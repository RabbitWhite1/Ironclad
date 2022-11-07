include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "CTypes.i.dfy"

module Raft__PacketParsing_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened Raft__AppInterface_i
import opened Raft__Types_i
import opened Raft__CTypes_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
import opened Common__Util_i
import opened AppStateMachine_s
import opened Environment_s
import opened Math__mul_i
import opened Math__mul_nonlinear_i

////////////////////////////////////////////////////////////////////
//    Grammars for the Rafy types
////////////////////////////////////////////////////////////////////
function method EndPoint_grammar() : G { GByteArray }
function method CLogEntry_grammar() : G { GTuple([GUint64, GUint64, GByteArray, GUint64]) }
function method CLogEntrySeq_grammar() : G { GArray(CLogEntry_grammar()) }

////////////////////////////////////////////////////////////////////
//    Grammars for the Raft messages 
////////////////////////////////////////////////////////////////////
function method CMessage_RequestVote_grammar() : G { GTuple([GUint64, EndPoint_grammar(), GUint64, GUint64]) }
function method CMessage_RequestVoteReply_grammar() : G { GTuple([GUint64, GUint64]) }
function method CMessage_AppendEntries_grammar() : G { GTuple([GUint64, EndPoint_grammar(), GUint64, GUint64, CLogEntrySeq_grammar(), GUint64]) }
function method CMessage_AppendEntriesReply_grammar() : G { GTuple([GUint64, GUint64, GUint64]) }

function method CMessage_grammar() : G { 
  GTaggedUnion([
    CMessage_RequestVote_grammar(),
    CMessage_RequestVoteReply_grammar(),
    CMessage_AppendEntries_grammar(),
    CMessage_AppendEntriesReply_grammar()
  ]) 
}

predicate NetPacketBound(data:seq<byte>) 
{
  |data| < MaxPacketSize()
}

predicate CMessageIs64Bit(msg:CMessage)
{
  true
}


////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////
function method parse_EndPoint(val:V) : EndPoint
  requires ValInGrammar(val, EndPoint_grammar())
  ensures  EndPointIsAbstractable(parse_EndPoint(val))
{
  EndPoint(val.b)
}

function method parse_CLogEntry(val:V) : CLogEntry
  requires ValInGrammar(val, CLogEntry_grammar())
  ensures  CLogEntryIsAbstractable(parse_CLogEntry(val))
{
  CLogEntry(val.t[0].u, val.t[1].u, val.t[2].b, val.t[3].u)
}

function method parse_Message_RequestVote(val:V) : CMessage
  requires ValInGrammar(val, CMessage_RequestVote_grammar())
  ensures CMesssageIsAbstractable(parse_Message_RequestVote(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_RequestVote(val))
{
  CMessage_RequestVote(
    val.t[0].u,
    parse_EndPoint(val.t[1]),
    val.t[2].u,
    val.t[3].u
  )
}

function method parse_Message_RequestVoteReply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_RequestVoteReply_grammar())
  ensures CMesssageIsAbstractable(parse_Message_RequestVoteReply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_RequestVoteReply(val))
{
  CMessage_RequestVoteReply(
    val.t[0].u,
    val.t[1].u
  )
}

function parse_CLogEntrySeq(val:V) : seq<CLogEntry>
  requires ValInGrammar(val, CLogEntrySeq())
  ensures  |parse_CLogEntrySeq(val)| == |val.a|
  ensures  forall i :: 0 <= i < |parse_CLogEntrySeq(val)| ==> parse_CLogEntrySeq(val)[i] == parse_CLogEntry(val.a[i])
  ensures  CRequestBatchIsAbstractable(parse_CLogEntrySeq(val))
  ensures  ValidVal(val) ==> CRequestBatchIs64Bit(parse_CLogEntrySeq(val))
  decreases |val.a|
{
  if |val.a| == 0 then
    []
  else 
    var req := parse_CLogEntry(val.a[0]);
    var restVal:V := VArray(val.a[1..]);
    var rest := parse_CLogEntrySeq(restVal);
    [req] + rest
}

function method parse_Message_AppendEntries(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppendEntries_grammar())
  ensures CMesssageIsAbstractable(parse_Message_AppendEntries(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppendEntries(val))
{
  CMessage_AppendEntries(
    val.t[0].u,
    parse_EndPoint(val.t[1]),
    val.t[2].u,
    val.t[3].u,
    parse_CLogEntrySeq(val.t[4]),
    val.t[5].u
  )
}

function method parse_Message_AppendEntriesReply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppendEntriesReply_grammar())
  ensures CMesssageIsAbstractable(parse_Message_AppendEntriesReply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppendEntriesReply(val))
{
  CMessage_AppendEntriesReply(
    val.t[0].u,
    val.t[1].u,
    val.t[2].u
  )
}

method Parse_Message(val:V) returns (msg:CMessage)
	requires ValInGrammar(val, CMessage_grammar())
	requires ValidVal(val)
	// ensures	 msg == parse_Message(val)
	ensures	 !msg.CMessage_Invalid?
	ensures	 CMessageIsAbstractable(msg)
	ensures	 CMessageIs64Bit(msg)
{
  if val.c == 0 {
    msg := parse_Message_RequestVote(val.val);
  } else if val.c == 1 {
    msg := parse_Message_RequestVoteReply(val.val);
  } else if val.c == 2 {
    msg := parse_Message_AppendEntries(val.val);
  } else if val.c == 3 {
    msg := parse_Message_AppendEntriesReply(val.val);
  } else {
    assert false;
  }
}


////////////////////////////////////////////////////////////////////
//    Demarshall
////////////////////////////////////////////////////////////////////
function RaftDemarshallData(data:seq<byte>) : CMessage
  ensures  CMessageIsAbstractable(RaftDemarshallData(data))
{
  if Demarshallable(data, CMessage_grammar()) then
    var val := DemarshallFunc(data, CMessage_grammar());
    parse_Message(val)
  else
    CMessage_Invalid()
}

method RaftDemarshallDataMethod(data:array<byte>, msg_grammar:G) returns (msg:CMessage)
  requires data.Length < 0x1_0000_0000_0000_0000
  requires msg_grammar == CMessage_grammar()
  requires ValidGrammar(msg_grammar)
  ensures  CMessageIsAbstractable(msg)
  ensures  if Demarshallable(data[..], msg_grammar) then
             msg == RaftDemarshallData(data[..]) 
           else
             msg.CMessage_Invalid?
  ensures  CMessageIs64Bit(msg)
{
  var success, val := Demarshall(data, msg_grammar);
  if success {
    assert ValInGrammar(val, msg_grammar);
    msg := Parse_Message(val);
    assert !msg.CMessage_Invalid?;
  } else {
    msg := CMessage_Invalid();
  }
}

////////////////////////////////////////////////////////////////////
//    Can a value be marshalled?
////////////////////////////////////////////////////////////////////
function Marshallable(msg:CMessage) : bool
{
  // TODO: this is a hack
  && (!msg.CMessage_Invalid?)
  && (msg.CMessage_RequestVote? ==> true)
  && (msg.CMessage_RequestVoteReply? ==> true)
  && (msg.CMessage_AppendEntries? ==> true)
  && (msg.CMessage_AppendEntriesReply? ==> true)
}

function CMessageIsValid(msg:CMessage) : bool
{
  Marshallable(msg)
}

predicate CPacketsIsMarshallable(cps:set<CPacket>)
{
  forall cp :: cp in cps ==> Marshallable(cp.msg)
}

// TODO & DOING: finish this about determining if valid and DetermineIfMessageMarshallable


}