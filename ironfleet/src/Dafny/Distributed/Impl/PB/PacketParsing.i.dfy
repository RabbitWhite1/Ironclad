include "../Common/GenericMarshalling.i.dfy"
include "../Common/NetClient.i.dfy"
include "Message.i.dfy"

module PacketParsing_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Logic__Option_i
import opened Environment_s
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened Types_i
import opened Message_i

predicate NetPacketBound(data:seq<byte>) 
{
    |data| < MaxPacketSize()
}

////////////////////////////////////////////////////////////////////
//    Grammars for the PB messages
////////////////////////////////////////////////////////////////////

function method CMessageUpdateGrammar() : G { GUint64 }

function method CMessageGrammar() : G 
{ 
    CMessageUpdateGrammar()
}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////

function method ParseCMessageUpdate(val:V) : CMessage
    requires ValInGrammar(val, CMessageUpdateGrammar());
{
    CUpdate(val.u)
}

function method ParseCMessage(val:V) : CMessage
    requires ValInGrammar(val, CMessageGrammar());
{
    ParseCMessageUpdate(val)
}

function DemarshallData(data:seq<byte>) : CMessage
{
    if Demarshallable(data, CMessageGrammar()) then
        var val := DemarshallFunc(data, CMessageGrammar());
        ParseCMessage(val)
    else
        CInvalid()
}

method DemarshallDataMethod(data:array<byte>) returns (msg:CMessage)
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  msg == DemarshallData(data[..]);
//    ensures  if Demarshallable(data[..], msg_grammar) then 
//                msg == PaxosDemarshallData(data[..]) 
//             else msg.CMessage_Invalid?;
//    ensures  CMessageIs64Bit(msg);
{
    var success, val := Demarshall(data, CMessageGrammar());
    if success {
        //assert ValInGrammar(val, msg_grammar);
        msg := ParseCMessage(val);
        assert !msg.CInvalid?;
    } else {
        msg := CInvalid();
    }
}



////////////////////////////////////////////////////////////////////
//    Marshalling
////////////////////////////////////////////////////////////////////

method MarshallMessageUpdate(c:CMessage) returns (val:V)
    requires c.CUpdate?;
    ensures  ValInGrammar(val, CMessageUpdateGrammar());
    ensures  ValidVal(val);
    ensures  ParseCMessageUpdate(val) == c;
    ensures  SizeOfV(val) < MaxPacketSize();
{
    val := VUint64(c.value);
}

method MarshallMessage(c:CMessage) returns (val:V)
    requires !c.CInvalid?;
    ensures  ValInGrammar(val, CMessageGrammar());
    ensures  ValidVal(val);
    ensures  ParseCMessage(val) == c;
    ensures  SizeOfV(val) < MaxPacketSize();
{
    if c.CUpdate? {
        var msg := MarshallMessageUpdate(c);
        val := msg;
    } else {
        assert false;       // Provably will not reach here
    }
}

method MarshallPBMessage(msg:CMessage) returns (data:array<byte>)
    requires !msg.CInvalid?;
    ensures fresh(data);
    ensures NetPacketBound(data[..]);
    ensures DemarshallData(data[..]) == msg;
{
    var val := MarshallMessage(msg);
    data := Marshall(val, CMessageGrammar());
}

////////////////////////////////////////////////////////////////////
//    Packet translation 
////////////////////////////////////////////////////////////////////

function AbstractifyNetPacket(net:NetPacket) : PBPacket
{
    LPacket(net.dst, net.src, AbstractifyCMessage(DemarshallData(net.msg)))
}

predicate CPBPacketValid(p:CPBPacket)
{
      EndPointIsValidPublicKey(p.src)
    && EndPointIsValidPublicKey(p.dst)
    && !p.msg.CInvalid?
}

predicate OptionCPBPacketValid(opt_packet:Option<CPBPacket>)
{
    opt_packet.Some? ==> CPBPacketValid(opt_packet.v)
}

}

