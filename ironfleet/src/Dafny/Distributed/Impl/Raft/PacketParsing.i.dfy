include "../../../Libraries/Math/mul.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
// include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../../Services/Raft/AppStateMachine.s.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NetClient.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "AppInterface.i.dfy"
include "CMessage.i.dfy"
include "CTypes.i.dfy"


module Raft__PacketParsing_i {

import opened Math__mul_i
import opened Environment_s
import opened Native__Io_s
import opened Native__NativeTypes_s
// import opened Collections__Maps_i
import opened Raft__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened Common__NodeIdentity_i
// import opened Common__Util_i
import opened AppStateMachine_s
import opened Raft__AppInterface_i
import opened Raft__CMessage_i
import opened Raft__CTypes_i

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
function method CMessage_Request_grammar() : G { GTuple([GUint64, GByteArray]) }
function method CMessage_Reply_grammar() : G { GTuple([GUint64, GUint64, GUint64, GByteArray]) }

function method CMessage_grammar() : G { 
  GTaggedUnion([
    CMessage_RequestVote_grammar(),
    CMessage_RequestVoteReply_grammar(),
    CMessage_AppendEntries_grammar(),
    CMessage_AppendEntriesReply_grammar(),
    CMessage_Request_grammar(),
    CMessage_Reply_grammar()
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

predicate CLogEntrySeqIs64Bit(entries:seq<CLogEntry>)
{
  true
}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////
function method parse_EndPoint(val:V) : EndPoint
  requires ValInGrammar(val, EndPoint_grammar())
  ensures EndPointIsAbstractable(parse_EndPoint(val))
{
  EndPoint(val.b)
}

function method parse_LogEntry(val:V) : CLogEntry
  requires ValInGrammar(val, CLogEntry_grammar())
  ensures CLogEntryIsAbstractable(parse_LogEntry(val))
{
  assert ValInGrammar(val, CLogEntry_grammar());
  CLogEntry(val.t[0].u, val.t[1].u, val.t[2].b, val.t[3].u)
}

function method parse_Message_RequestVote(val:V) : CMessage
  requires ValInGrammar(val, CMessage_RequestVote_grammar())
  ensures CMessageIsAbstractable(parse_Message_RequestVote(val))
{
  assert ValInGrammar(val, CMessage_RequestVote_grammar());
  CMessage_RequestVote(
    val.t[0].u,
    parse_EndPoint(val.t[1]),
    val.t[2].u,
    val.t[3].u
  )
}

function method parse_Message_RequestVoteReply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_RequestVoteReply_grammar())
  ensures CMessageIsAbstractable(parse_Message_RequestVoteReply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_RequestVoteReply(val))
{
  assert ValInGrammar(val, CMessage_RequestVoteReply_grammar());
  CMessage_RequestVoteReply(
    val.t[0].u,
    val.t[1].u
  )
}

function method parse_LogEntrySeq(val:V) : seq<CLogEntry>
  requires ValInGrammar(val, CLogEntrySeq_grammar())
  ensures  |parse_LogEntrySeq(val)| == |val.a|
  ensures  forall i :: 0 <= i < |parse_LogEntrySeq(val)| ==> parse_LogEntrySeq(val)[i] == parse_LogEntry(val.a[i])
  ensures  CLogEntrySeqIsAbstractable(parse_LogEntrySeq(val))
  ensures  ValidVal(val) ==> CLogEntrySeqIs64Bit(parse_LogEntrySeq(val))
  decreases |val.a|
{
  if |val.a| == 0 then
    []
  else 
    var req := parse_LogEntry(val.a[0]);
    var restVal:V := VArray(val.a[1..]);
    var rest := parse_LogEntrySeq(restVal);
    [req] + rest
}

function method parse_Message_AppendEntries(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppendEntries_grammar())
  ensures CMessageIsAbstractable(parse_Message_AppendEntries(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppendEntries(val))
{
  assert ValInGrammar(val, CMessage_AppendEntries_grammar());
  CMessage_AppendEntries(
    val.t[0].u,
    parse_EndPoint(val.t[1]),
    val.t[2].u,
    val.t[3].u,
    parse_LogEntrySeq(val.t[4]),
    val.t[5].u
  )
}

function method parse_Message_AppendEntriesReply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_AppendEntriesReply_grammar())
  ensures CMessageIsAbstractable(parse_Message_AppendEntriesReply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppendEntriesReply(val))
{
  assert ValInGrammar(val, CMessage_AppendEntriesReply_grammar());
  CMessage_AppendEntriesReply(
    val.t[0].u,
    val.t[1].u,
    val.t[2].u
  )
}

function method parse_Message_Request(val:V) : CMessage
  requires ValInGrammar(val, CMessage_Request_grammar())
  ensures CMessageIsAbstractable(parse_Message_Request(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Request(val))
{
  assert ValInGrammar(val, CMessage_Request_grammar());
  CMessage_Request(
    val.t[0].u,
    val.t[1].b
  )
}
function method parse_Message_Reply(val:V) : CMessage
  requires ValInGrammar(val, CMessage_Reply_grammar())
  ensures CMessageIsAbstractable(parse_Message_Reply(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Reply(val))
{
  assert ValInGrammar(val, CMessage_Reply_grammar());
  CMessage_Reply(
    val.t[0].u,
    val.t[1].u,
    val.t[2].u,
    val.t[3].b
  )
}

function parse_Message(val:V) : CMessage
  requires ValInGrammar(val, CMessage_grammar())
  ensures  CMessageIsAbstractable(parse_Message(val))
  ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message(val))
{
  if val.c == 0 then
    parse_Message_RequestVote(val.val)
  else if val.c == 1 then
    parse_Message_RequestVoteReply(val.val)
  else if val.c == 2 then
    parse_Message_AppendEntries(val.val)
  else if val.c == 3 then
    parse_Message_AppendEntriesReply(val.val)
  else if val.c == 4 then
    parse_Message_Request(val.val)
  else if val.c == 5 then
    parse_Message_Reply(val.val)
  else
    assert false;
    parse_Message_RequestVote(val.val)
}

method Parse_Message(val:V) returns (msg:CMessage)
	requires ValInGrammar(val, CMessage_grammar())
	requires ValidVal(val)
	ensures	 msg == parse_Message(val)
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
  } else if val.c == 4 {
    msg := parse_Message_Request(val.val);
  } else if val.c == 5 {
    msg := parse_Message_Reply(val.val);
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
function Marshallable(c:CMessage) : bool
{
  // TODO: this is a hack
  && (!c.CMessage_Invalid?)
  && (c.CMessage_RequestVote? ==> EndPointIsValidPublicKey(c.candidate_ep))
  && (c.CMessage_RequestVoteReply? ==> true)
  && (c.CMessage_AppendEntries? ==> ValidAppendEntries(c) && EndPointIsValidPublicKey(c.leader_ep))
  && (c.CMessage_Request? ==> CAppRequestMarshallable(c.req))
  && (c.CMessage_Reply? ==> CAppReplyMarshallable(c.reply))
}

function CMessageIsValid(msg:CMessage) : bool
{
  Marshallable(msg)
}

predicate CPacketsIsMarshallable(cps:set<CPacket>)
{
  forall cp :: cp in cps ==> Marshallable(cp.msg)
}

method DetermineIfMessageMarshallable(msg:CMessage) returns (b:bool)
  requires CMessageIsAbstractable(msg)
  requires CMessageIs64Bit(msg)
  ensures  b == Marshallable(msg)
{
  if msg.CMessage_Invalid? {
    b := false;
  }
  else if msg.CMessage_RequestVote? {
    b := EndPointIsValidPublicKey(msg.candidate_ep);
  }
  else if msg.CMessage_RequestVoteReply? {
    b := true;
  }
  else if msg.CMessage_AppendEntries? {
    b := ValidAppendEntries(msg) && EndPointIsValidPublicKey(msg.leader_ep);
  }
  else if msg.CMessage_AppendEntriesReply? {
    b := true;
  }
  else if msg.CMessage_Request? {
    b := CAppRequestMarshallable(msg.req);
  }
  else if msg.CMessage_Reply? {
    b := CAppReplyMarshallable(msg.reply);
  }
  else {
    assert false;
  }
}

////////////////////////////////////////////////////////////////////
//    Marshalling 
////////////////////////////////////////////////////////////////////
method MarshallEndPoint(c:EndPoint) returns (val:V)
  requires EndPointIsValidPublicKey(c)
  ensures  ValInGrammar(val, EndPoint_grammar())
  ensures  ValidVal(val)
  ensures  parse_EndPoint(val) == c
{
  val := VByteArray(c.public_key);
}

method MarshallLogEntry(c:CLogEntry) returns (val:V)
  requires ValidLogEntry(c)
  ensures ValInGrammar(val, CLogEntry_grammar())
  ensures ValidVal(val)
  ensures parse_LogEntry(val) == c
{
  var marshalled_app_req := MarshallCAppRequest(c.req);
  val := VTuple([VUint64(c.term), VUint64(c.index), marshalled_app_req, VUint64(c.is_commited)]);
  assert ValInGrammar(val, CLogEntry_grammar());
}

method MarshallLogEntrySeq(c:seq<CLogEntry>) returns (val:V)
  requires ValidLogEntrySeq(c)
  ensures ValInGrammar(val, CLogEntrySeq_grammar())
  ensures ValidVal(val)
  ensures parse_LogEntrySeq(val) == c
{
  var reqs := new V[|c| as uint64];

  var i:uint64 := 0;
  while i < |c| as uint64
    invariant 0 <= i as int <= |c|
    invariant forall j :: 0 <= j < i ==> ValInGrammar(reqs[j], CLogEntry_grammar())
    invariant forall j :: 0 <= j < i ==> ValidVal(reqs[j])
    invariant forall j :: 0 <= j < i ==> parse_LogEntry(reqs[j]) == c[j]
  {
    var single := MarshallLogEntry(c[i]);
    assert ValInGrammar(single, CLogEntry_grammar());
    reqs[i] := single;
    i := i + 1;
  }

  val := VArray(reqs[..]);
}

method MarshallMessage_RequestVote(c:CMessage) returns (val:V)
  requires c.CMessage_RequestVote?
  requires ValidRequestVote(c)
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_RequestVote_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_RequestVote(val) == c
{
  var marshalled_ep := MarshallEndPoint(c.candidate_ep);
  val := VTuple([VUint64(c.term), marshalled_ep, VUint64(c.last_log_index), VUint64(c.last_log_term)]);
  assert ValInGrammar(val, CMessage_RequestVote_grammar());
}

method MarshallMessage_RequestVoteReply(c:CMessage) returns (val:V)
  requires c.CMessage_RequestVoteReply?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_RequestVoteReply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_RequestVoteReply(val) == c
{
  val := VTuple([VUint64(c.term), VUint64(c.vote_granted)]);
  assert ValInGrammar(val, CMessage_RequestVoteReply_grammar());
}

method MarshallMessage_AppendEntries(c:CMessage) returns (val:V)
  requires c.CMessage_AppendEntries?
  requires ValidAppendEntries(c)
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_AppendEntries_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_AppendEntries(val) == c
{
  var marshalled_ep := MarshallEndPoint(c.leader_ep);
  var marshalled_entries := MarshallLogEntrySeq(c.entries);
  val := VTuple([
    VUint64(c.term), 
    marshalled_ep, 
    VUint64(c.prev_log_index), 
    VUint64(c.prev_log_term), 
    marshalled_entries, 
    VUint64(c.leader_commit)
  ]);
  assert ValInGrammar(val, CMessage_AppendEntries_grammar());
}

method MarshallMessage_AppendEntriesReply(c:CMessage) returns (val:V)
  requires c.CMessage_AppendEntriesReply?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_AppendEntriesReply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_AppendEntriesReply(val) == c
{
  val := VTuple([VUint64(c.term), VUint64(c.success), VUint64(c.match_index)]);
  assert ValInGrammar(val, CMessage_AppendEntriesReply_grammar());
}

method MarshallMessage_Request(c:CMessage) returns (val:V)
  requires c.CMessage_Request?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_Request_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_Request(val) == c
{
  val := VTuple([VUint64(c.seqno_req), VByteArray(c.req)]);
  assert ValInGrammar(val, CMessage_Request_grammar());
}

method MarshallMessage_Reply(c:CMessage) returns (val:V)
  requires c.CMessage_Reply?
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_Reply_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message_Reply(val) == c
{
  val := VTuple([VUint64(c.seqno_reply), VUint64(c.ok), VUint64(c.leader_id), VByteArray(c.reply)]);
  assert ValInGrammar(val, CMessage_Reply_grammar());
}

method MarshallMessage(c:CMessage) returns (val:V)
  requires Marshallable(c)
  ensures  ValInGrammar(val, CMessage_grammar())
  ensures  ValidVal(val)
  ensures  parse_Message(val) == c
{
  assert !c.CMessage_Invalid?;
  if c.CMessage_RequestVote? {
    assert EndPointIsValidPublicKey(c.candidate_ep);
    var msg := MarshallMessage_RequestVote(c);
    val := VCase(0, msg);
  } else if c.CMessage_RequestVoteReply? {
    var msg := MarshallMessage_RequestVoteReply(c);
    val := VCase(1, msg);
  } else if c.CMessage_AppendEntries? {
    var msg := MarshallMessage_AppendEntries(c);
    val := VCase(2, msg);
  } else if c.CMessage_AppendEntriesReply? {
    var msg := MarshallMessage_AppendEntriesReply(c);
    val := VCase(3, msg);
  } else if c.CMessage_Request? {
    var msg := MarshallMessage_Request(c);
    val := VCase(4, msg);
  } else if c.CMessage_Reply? {
    var msg := MarshallMessage_Reply(c);
    val := VCase(5, msg);
  } else {
    assert false;
  }
}

////////////////////////////////////////////////////////////////////////
// These functions need to be here, rather than CMessageRefinements.i.dfy,
// since they depend on RaftDemarshallData
////////////////////////////////////////////////////////////////////////

predicate NetPacketIsAbstractable(net:NetPacket)
{
  && EndPointIsValidPublicKey(net.src)
  && EndPointIsValidPublicKey(net.dst)
}

function AbstractifyBufferToRaftPacket(src:EndPoint, dst:EndPoint, data:seq<byte>) : RaftPacket
  requires EndPointIsValidPublicKey(src)
  requires EndPointIsValidPublicKey(dst)
{
  LPacket(AbstractifyEndPointToNodeIdentity(dst),
          AbstractifyEndPointToNodeIdentity(src),
          AbstractifyCMessageToRaftMessage(RaftDemarshallData(data)))
}

function AbstractifyNetPacketToRaftPacket(net:NetPacket) : RaftPacket
  requires NetPacketIsAbstractable(net)
{
  AbstractifyBufferToRaftPacket(net.src, net.dst, net.msg)
}

lemma lemma_CMessageGrammarValid()
  ensures ValidGrammar(CMessage_grammar())
{
  var g := CMessage_grammar();
  assert |g.cases| < 0x1_0000_0000_0000_0000;
  assert ValidGrammar(CMessage_RequestVote_grammar());
  assert ValidGrammar(CMessage_RequestVoteReply_grammar());
  assert ValidGrammar(CMessage_AppendEntries_grammar());
  assert ValidGrammar(CMessage_AppendEntriesReply_grammar());
}

predicate CBroadcastIsValid(broadcast:CBroadcast) 
{
  && CBroadcastIsAbstractable(broadcast)
  && (broadcast.CBroadcast? ==>
      && Marshallable(broadcast.msg)
      && 0 <= |broadcast.dsts| <= 0xFFFF_FFFF_FFFF_FFFF)
}

predicate BufferRefinementAgreesWithMessageRefinement(msg:CMessage, marshalled:seq<byte>)
  requires CMessageIsAbstractable(msg)
  requires CMessageIsAbstractable(msg)
{
  forall src, dst :: (EndPointIsValidPublicKey(src) && EndPointIsValidPublicKey(dst)) ==>

            (AbstractifyBufferToRaftPacket(src, dst, marshalled)
            == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRaftMessage(msg)))
}


lemma lemma_CLogEntryBound(c:CLogEntry, val:V)
  requires c.CLogEntry?
  requires ValInGrammar(val, CLogEntry_grammar())
  requires ValidLogEntry(c)
  requires parse_LogEntry(val) == c
  ensures SizeOfV(val) <= 32 + MaxAppRequestSize()
{
  assert ValInGrammar(val, CLogEntry_grammar());
  lemma_VSizeSeqSum4(val);
  assert SizeOfV(val.t[0]) == 8;
  assert SizeOfV(val.t[1]) == 8; 
  assert SizeOfV(val.t[2]) <= 8 + MaxAppRequestSize();
  assert SizeOfV(val.t[3]) == 8;
  assert SizeOfV(val) <= 32 + MaxAppRequestSize();
}


lemma lemma_CLogEntrySeqBound(c:seq<CLogEntry>, val:V)
  requires ValInGrammar(val, CLogEntrySeq_grammar())
  requires ValidLogEntrySeq(c)
  requires parse_LogEntrySeq(val) == c
  decreases |c|
  ensures SeqSum(val.a) <= (32 + MaxAppRequestSize())*|val.a|
{
  ghost var garray := GArray(CLogEntry_grammar());
  assert ValInGrammar(val, garray);
  reveal SeqSum();
  if |val.a| == 0 {
    assert SeqSum(val.a) <= (32 + MaxAppRequestSize())*|val.a|;
  } else {
    var req := parse_LogEntry(val.a[0]);
    var restVal:V := VArray(val.a[1..]);
    var rest := parse_LogEntrySeq(restVal);
    assert c == [req] + rest;
    var x := 32 + MaxAppRequestSize();
    var N := |val.a|;
    lemma_CLogEntrySeqBound(rest, restVal);
    assert SeqSum(val.a[1..]) <= x * (N-1);
    lemma_CLogEntryBound(req, val.a[0]);
    assert SizeOfV(val.a[0]) <= x;
    assert SeqSum(val.a) == SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
    assert |val.a| == |val.a[1..]| + 1;
    lemma_mul_is_distributive(x, N-1, 1);
    assert SeqSum(val.a) <= x * N;
  }
}

lemma lemma_MarshallableBound(c:CMessage, val:V)
  requires Marshallable(c)
  requires ValInGrammar(val, CMessage_grammar())
  requires ValidVal(val)
  requires parse_Message(val) == c
  ensures 0 <= SizeOfV(val) < MaxPacketSize()
{
  assert !c.CMessage_Invalid?;
  if c.CMessage_RequestVote? {
    assert ValInGrammar(val.val, CMessage_RequestVote_grammar());
    assert ValInGrammar(val.val.t[0], GUint64()) && SizeOfV(val.val.t[0]) == 8;
    assert ValInGrammar(val.val.t[1], GByteArray()) && SizeOfV(val.val.t[1]) <= 8 + MaxEndpointSize();
    assert ValInGrammar(val.val.t[2], GUint64()) && SizeOfV(val.val.t[2]) == 8;
    assert ValInGrammar(val.val.t[3], GUint64()) && SizeOfV(val.val.t[3]) == 8;
    assert |val.val.t| == 4;
    lemma_VSizeSeqSum4(val.val);
    assert SizeOfV(val) <= 40 + MaxEndpointSize();
  } else if c.CMessage_RequestVoteReply? {
    assert ValInGrammar(val.val, CMessage_RequestVoteReply_grammar());
    assert ValInGrammar(val.val.t[0], GUint64()) && SizeOfV(val.val.t[0]) == 8;
    assert ValInGrammar(val.val.t[1], GUint64()) && SizeOfV(val.val.t[1]) == 8;
    assert |val.val.t| == 2;
    lemma_VSizeSeqSum2(val.val);
    assert SizeOfV(val) == 24;
  } else if c.CMessage_AppendEntries? {
    assert ValInGrammar(val.val, CMessage_AppendEntries_grammar());
    assert SizeOfV(val.val.t[0]) == 8;
    assert SizeOfV(val.val.t[1]) <= 8 + MaxEndpointSize();
    assert SizeOfV(val.val.t[2]) <= 8;
    assert SizeOfV(val.val.t[3]) == 8;
    lemma_CLogEntrySeqBound(c.entries, val.val.t[4]);
    assert SizeOfV(val.val.t[4]) <= 8 + (32 + MaxAppRequestSize())*|val.val.t[4].a|;
    assert |val.val.t[4].a| <= LogEntrySeqSizeLimit();
    calc {
      SizeOfV(val.val.t[4]);
      8 + SeqSum(val.val.t[4].a);
      <=
      8 + (32 + MaxAppRequestSize())*|val.val.t[4].a|;
      <= { lemma_mul_is_commutative(|val.val.t[4].a|, LogEntrySeqSizeLimit());
          lemma_mul_is_commutative(|val.val.t[4].a|, 32 + MaxAppRequestSize());
          lemma_mul_inequality(|val.val.t[4].a|, LogEntrySeqSizeLimit(), 32 + MaxAppRequestSize());
        }
      8 + (32 + MaxAppRequestSize())*LogEntrySeqSizeLimit();
    }
    assert SizeOfV(val.val.t[4]) <= 8 + (32 + MaxAppRequestSize())*LogEntrySeqSizeLimit();
    assert SizeOfV(val.val.t[5]) == 8;
    lemma_VSizeSeqSum6(val.val);
    calc {
      SizeOfV(val);
      8 + SizeOfV(val.val);
      8 + SizeOfV(val.val.t[0]) + SizeOfV(val.val.t[1]) + SizeOfV(val.val.t[2]) + SizeOfV(val.val.t[3]) + SizeOfV(val.val.t[4]) + SizeOfV(val.val.t[5]);
      8 + 8 + SizeOfV(val.val.t[1]) + 8 + 8 + SizeOfV(val.val.t[4]) + 8;
      <=
      8 + 8 + 8 + MaxEndpointSize() + 8 + 8 + SizeOfV(val.val.t[4]) + 8;
      <=
      8 + 8 + 8 + MaxEndpointSize() + 8 + 8 + 8 + (32 + MaxAppRequestSize())*|val.val.t[4].a| + 8;
      ==
      56 + MaxEndpointSize() + (32 + MaxAppRequestSize())*|val.val.t[4].a|;
      <= {
        lemma_mul_is_commutative(|val.val.t[4].a|, LogEntrySeqSizeLimit());
        lemma_mul_is_commutative(|val.val.t[4].a|, 32 + MaxAppRequestSize());
        lemma_mul_inequality(|val.val.t[4].a|, LogEntrySeqSizeLimit(), 32 + MaxAppRequestSize());
      }
      56 + MaxEndpointSize() + (32 + MaxAppRequestSize())*LogEntrySeqSizeLimit();
    }
    assert SizeOfV(val) <= 56 + MaxEndpointSize() + (32 + MaxAppRequestSize())*|val.val.t[4].a|;
    assert SizeOfV(val) <= 56 + MaxEndpointSize() + (32 + MaxAppRequestSize())*LogEntrySeqSizeLimit();
  } else if c.CMessage_AppendEntriesReply? {
    assert ValInGrammar(val.val, CMessage_AppendEntriesReply_grammar());
    assert ValInGrammar(val.val.t[0], GUint64()) && SizeOfV(val.val.t[0]) == 8;
    assert ValInGrammar(val.val.t[1], GUint64()) && SizeOfV(val.val.t[1]) == 8;
    assert ValInGrammar(val.val.t[2], GUint64()) && SizeOfV(val.val.t[2]) == 8;
    assert |val.val.t| == 3;
    lemma_VSizeSeqSum3(val.val);
    assert SizeOfV(val) == 32;
  } else if c.CMessage_Request? {
    assert ValInGrammar(val.val, CMessage_Request_grammar());
    lemma_VSizeSeqSum2(val.val);
  } else if c.CMessage_Reply? {
    assert ValInGrammar(val.val, CMessage_Reply_grammar());
    lemma_VSizeSeqSum4(val.val);
  } else {
    assert false;
  }
}

method RaftMarshall(msg:CMessage) returns (data:array<byte>)
  requires CMessageIsAbstractable(msg)
  requires Marshallable(msg)
  ensures fresh(data)
  ensures NetPacketBound(data[..])
  ensures Marshallable(RaftDemarshallData(data[..]))
  ensures BufferRefinementAgreesWithMessageRefinement(msg, data[..])
{
  var val := MarshallMessage(msg);
  lemma_MarshallableBound(msg, val);
  lemma_CMessageGrammarValid();
  data := Marshall(val, CMessage_grammar());

  forall src, dst | EndPointIsValidPublicKey(src) && EndPointIsValidPublicKey(dst) 
    ensures AbstractifyBufferToRaftPacket(src, dst, data[..])
              == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRaftMessage(msg));
  {
    calc {
      AbstractifyBufferToRaftPacket(src, dst, data[..]);
      LPacket(AbstractifyEndPointToNodeIdentity(dst),
              AbstractifyEndPointToNodeIdentity(src),
              AbstractifyCMessageToRaftMessage(RaftDemarshallData(data[..])));
      LPacket(AbstractifyEndPointToNodeIdentity(dst),
              AbstractifyEndPointToNodeIdentity(src),
              AbstractifyCMessageToRaftMessage(RaftDemarshallData(data[..])));
      LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRaftMessage(msg));
    }
  }
}

//////////////////////////////////////////////////////////////////////////////
// Sendable predicates

predicate CPacketIsSendable(cpacket:CPacket)
{
  && CMessageIsValid(cpacket.msg) 
  && CPacketIsAbstractable(cpacket)
  && EndPointIsValidPublicKey(cpacket.src)
}

predicate OutboundPacketsIsValid(out:OutboundPackets)
{
  match out
    case Broadcast(broadcast) => CBroadcastIsValid(broadcast)
    case OutboundPacket(p) => p.Some? ==> CPacketIsSendable(p.v)
    case PacketSequence(s) => |s| < 0xFFFF_FFFF_FFFF_FFFF 
                              && (forall p :: p in s ==> CPacketIsSendable(p))
}

predicate IosReflectIgnoringUnsendable(ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  && |ios| == 1
  && ios[0].LIoOpReceive?
  && (|| !Demarshallable(ios[0].r.msg, CMessage_grammar())
     || !Marshallable(parse_Message(DemarshallFunc(ios[0].r.msg, CMessage_grammar()))))
}

}