include "../../Protocol/PB/Node.i.dfy"
include "Message.i.dfy"
include "../Common/NetClient.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "PacketParsing.i.dfy"
include "../Common/SeqIsUniqueDef.i.dfy"

module Impl_Node_i {
import opened Native__NativeTypes_s
import opened Environment_s
import opened Protocol_Node_i
import opened Types_i
import opened Message_i
import opened Common__NetClient_i
import opened Logic__Option_i
import opened PacketParsing_i 
import opened Common__SeqIsUniqueDef_i

datatype CNode = CNode(is_primary:bool, value:uint64, my_index:uint64, config:Config)

predicate ValidConfig(c:Config)
{
    0 < |c| < 0x1_0000_0000_0000_0000
 && (forall e :: e in c ==> EndPointIsValidPublicKey(e))
 && SeqIsUnique(c)
}

predicate ValidConfigIndex(c:Config, index:uint64)
{
    0 <= index as int < |c|
}

predicate CNodeValid(c:CNode)
{
       ValidConfig(c.config)
    && ValidConfigIndex(c.config, c.my_index)
}

function AbstractifyCNode(n:CNode) : Node
{
    Node(n.is_primary, n.value as int, n.my_index as int, n.config)
}

method NodeInitImpl(my_index:uint64, config:Config) returns (node:CNode)
    requires 0 < |config| < 0x1_0000_0000_0000_0000;
    requires 0 <= my_index as int < |config|;
    requires ValidConfig(config);
    ensures CNodeValid(node);
    ensures NodeInit(AbstractifyCNode(node), my_index as int, config);
    ensures node.my_index == my_index;
    ensures node.config == config;
{
    node := CNode(my_index == 0, if my_index == 0 then 1 else 0, my_index, config);
    if node.is_primary {
        print "I am primary.\n";
    }
}

method NodeSendImpl(s:CNode) returns (s':CNode, packets:Option<seq<CPBPacket>>, ghost ios:seq<PBIo>)
    requires CNodeValid(s);
    // ensures  NodeSend(AbstractifyCNode(s), AbstractifyCNode(s'), ios);
    ensures  s'.my_index == s.my_index && s'.config == s.config;
    // TODO: modify for sequence of packets
    // ensures  packets.Some? ==> ios[0].LIoOpSend? 
    //                        && ios[0].s == AbstractifyCPBPacket(packets.v[0]);
    // ensures    OptionCPBPacketValid(packet) 
    //         && (packet.Some? ==> packet.v.src == s.config[s.my_index]); 
    // ensures  packet.None? ==> ios == [] && s' == s;
    ensures  CNodeValid(s');
{
    if s.is_primary {
        var ssss := CNode(s.is_primary, s.value, s.my_index, s.config);
        s' := ssss;
        var pkts := [];
        for index := 0 to |s.config| - 1 {
            if index as uint64 != s.my_index {
                var packet := LPacket(s.config[index], s.config[s.my_index], CUpdate(s.value));
                ios := [LIoOpSend(AbstractifyCPBPacket(packet))];
                pkts := pkts + [packet];
                print "I send Update to ", index, "\n";
            }
        }
        packets := Some(pkts);
    } else {
        s' := s;
        ios := [];
        packets := None();
    }
}

method NodeRecvImpl(s:CNode, packet:CPBPacket) 
    returns (s':CNode, ghost ios:seq<PBIo>)
    requires CNodeValid(s);
    // ensures  NodeRecv(AbstractifyCNode(s), AbstractifyCNode(s'), ios);
    ensures  s'.my_index == s.my_index && s'.config == s.config;
    ensures  |ios| >= 1
    ensures  CNodeValid(s');
{
    ios := [LIoOpReceive(AbstractifyCPBPacket(packet))];

    if    !s.is_primary 
       && packet.src in s.config
       && packet.msg.CUpdate? 
       && packet.msg.value >= s.value {
        var ssss := CNode(true, packet.msg.value, s.my_index, s.config);
        s' := ssss;
        print "I updated my value to", s'.value , "!\n";
    } else  {
        s' := s;
    }
}

}
