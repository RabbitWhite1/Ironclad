// include "../../Services/Raft/AppStateMachine.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../Common/NetClient.i.dfy"
include "AppInterface.i.dfy"
include "CTypes.i.dfy"
include "Config.i.dfy"

module Raft__CMessage_i {

// import opened AppStateMachine_s
import opened Environment_s
import opened Logic__Option_i
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Raft__Types_i
import opened Common__NetClient_i
import opened Common__NodeIdentity_i
import opened Concrete_NodeIdentity_i
import opened Raft__AppInterface_i
import opened Raft__CTypes_i
import opened Raft__ConfigState_i

datatype CMessage =
    CMessage_Invalid()
  | CMessage_RequestVote(term:uint64, candidate_ep:EndPoint, last_log_index:uint64, last_log_term:uint64)
  | CMessage_RequestVoteReply(term:uint64, vote_granted:uint64)
  | CMessage_AppendEntries(term:uint64, leader_ep:EndPoint, prev_log_index:uint64, prev_log_term:uint64, entries:seq<CLogEntry>, leader_commit:uint64)
  | CMessage_AppendEntriesReply(term:uint64, success:uint64, match_index:uint64)
  | CMessage_Request(seqno_req:uint64, req:CAppRequest)
  | CMessage_Reply(seqno_reply:uint64, ok:uint64, leader_id:uint64, reply:CAppReply)

datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

datatype CBroadcast = CBroadcast(src:EndPoint, dsts:seq<EndPoint>, msg:CMessage) | CBroadcastNop

datatype OutboundPackets = Broadcast(broadcast:CBroadcast) | OutboundPacket(p:Option<CPacket>) | PacketSequence(s:seq<CPacket>)

predicate method ValidRequestVote(c:CMessage)
{
  c.CMessage_RequestVote? ==> EndPointIsValidPublicKey(c.candidate_ep)
}

predicate method ValidAppendEntries(c:CMessage)
{
  && c.CMessage_AppendEntries? ==> (
    && EndPointIsValidPublicKey(c.leader_ep)
    && ValidLogEntrySeq(c.entries)
    && ValidLogEntrySeq(c.entries)
    && (|c.entries| > 0 ==> (
        && LogEntrySeqIndexIncreasing(c.entries) 
        && c.entries[0].index as int == c.prev_log_index as int + 1
        && forall i :: 0 <= i < |c.entries| ==> i + c.prev_log_index as int + 1 == c.entries[i].index as int
        && |c.entries| + c.prev_log_index as int + 1 <= ServerMaxLogSize()
      )
    )
  )
}

// CMessage
predicate CMessageIsAbstractable(msg:CMessage) {
  // TODO: unlikely all are true
  match msg {
    case CMessage_Invalid() => true
    case CMessage_RequestVote(term, _, _, _) => (term as int <= 0xFFFF_FFFF_FFFF_FFFF)
    case CMessage_RequestVoteReply(term, _) => (term as int <= 0xFFFF_FFFF_FFFF_FFFF)
    case CMessage_AppendEntries(term, _, _, _, _, _) => (term as int <= 0xFFFF_FFFF_FFFF_FFFF)
    case CMessage_AppendEntriesReply(term, _, _) => (term as int <= 0xFFFF_FFFF_FFFF_FFFF)
    case CMessage_Request(_, _) => true
    case CMessage_Reply(_, _, _, _) => true
  }
}

function AbstractifyCMessageToRaftMessage(msg:CMessage) : RaftMessage
  requires CMessageIsAbstractable(msg)
{
  match msg
    case CMessage_Invalid => RaftMessage_Invalid()
    case CMessage_RequestVote(term, candidate_ep, last_log_index, last_log_term) => RaftMessage_RequestVote(term as int, candidate_ep, last_log_index as int, last_log_term as int)
    case CMessage_RequestVoteReply(term, vote_granted) => RaftMessage_RequestVoteReply(term as int, vote_granted == 1)
    case CMessage_AppendEntries(term, leader_ep, prev_log_index, prev_log_term, entries, leader_commit) => RaftMessage_AppendEntries(term as int, leader_ep, prev_log_index as int, prev_log_term as int, AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries), leader_commit as int)
    case CMessage_AppendEntriesReply(term, success, match_index) => RaftMessage_AppendEntriesReply(term as int, success == 1, match_index as int)
    case CMessage_Request(seqno_req, req) => RaftMessage_Request(seqno_req as int, AbstractifyCAppRequestToAppRequest(req))
    case CMessage_Reply(seqno_reply, ok, leader_id, reply) => RaftMessage_Reply(seqno_reply as int, AbstractifyCAppReplyToAppReply(reply), ok == 1, leader_id as int)
}

// CPacket
predicate CPacketIsAbstractable(cp:CPacket)
{
  && CMessageIsAbstractable(cp.msg)
  && EndPointIsValidPublicKey(cp.src)
  && EndPointIsValidPublicKey(cp.dst)
}

predicate CPacketSeqIsAbstractable(cps:seq<CPacket>)
{
  forall i :: 0 <= i < |cps| ==> CPacketIsAbstractable(cps[i])
}

function AbstractifyCPacketToRaftPacket(cp: CPacket): RaftPacket
  ensures CPacketIsAbstractable(cp) ==> AbstractifyCPacketToRaftPacket(cp) == LPacket(AbstractifyEndPointToNodeIdentity(cp.dst), AbstractifyEndPointToNodeIdentity(cp.src), AbstractifyCMessageToRaftMessage(cp.msg))
{
  if (CPacketIsAbstractable(cp)) then
    LPacket(AbstractifyEndPointToNodeIdentity(cp.dst), AbstractifyEndPointToNodeIdentity(cp.src), AbstractifyCMessageToRaftMessage(cp.msg))
  else
    var x:RaftPacket :| (true); x
}

function {:opaque} AbstractifySeqOfCPacketsToSeqOfRaftPackets(cps:seq<CPacket>) : seq<RaftPacket>
  requires CPacketSeqIsAbstractable(cps)
  ensures |cps| == |AbstractifySeqOfCPacketsToSeqOfRaftPackets(cps)|
  ensures forall i :: 0 <= i < |cps| ==> AbstractifySeqOfCPacketsToSeqOfRaftPackets(cps)[i] == AbstractifyCPacketToRaftPacket(cps[i])
{
  if |cps| == 0 then []
  else [AbstractifyCPacketToRaftPacket(cps[0])] + AbstractifySeqOfCPacketsToSeqOfRaftPackets(cps[1..])
}

predicate CBroadcastIsAbstractable(broadcast:CBroadcast) 
{
  || broadcast.CBroadcastNop?
  || (&& broadcast.CBroadcast? 
     && EndPointIsValidPublicKey(broadcast.src)
     && (forall i :: 0 <= i < |broadcast.dsts| ==> EndPointIsValidPublicKey(broadcast.dsts[i]))
     && CMessageIsAbstractable(broadcast.msg))
}

function {:opaque} BuildLBroadcast(src:NodeIdentity, dsts:seq<NodeIdentity>, m:RaftMessage):seq<RaftPacket>
  ensures |BuildLBroadcast(src, dsts, m)| == |dsts|
  ensures forall i :: 0 <= i < |dsts| ==> BuildLBroadcast(src, dsts, m)[i] == LPacket(dsts[i], src, m)
{
  if |dsts| == 0 then []
  else [LPacket(dsts[0], src, m)] + BuildLBroadcast(src, dsts[1..], m)
}

function AbstractifyCBroadcastToRaftPacketSeq(broadcast:CBroadcast) : seq<RaftPacket>
  requires CBroadcastIsAbstractable(broadcast)
{
  match broadcast
    case CBroadcast(_,_,_) => BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                              AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                              AbstractifyCMessageToRaftMessage(broadcast.msg))
    case CBroadcastNop => []
}

// OutboundPackets
predicate OutboundPacketsIsAbstractable(out:OutboundPackets)
{
  match out
    case Broadcast(broadcast) => CBroadcastIsAbstractable(broadcast)
    case OutboundPacket(Some(p)) => CPacketIsAbstractable(p)
    case OutboundPacket(None()) => true
    case PacketSequence(s) => CPacketSeqIsAbstractable(s)
} 

predicate OutboundPacketsHasCorrectSrc(out:OutboundPackets, me:EndPoint)
{
  match out
    case Broadcast(CBroadcast(src, _, _)) => src == me
    case Broadcast(CBroadcastNop()) => true
    case OutboundPacket(p) => p.Some? ==> p.v.src == me
    case PacketSequence(s) => (forall p :: p in s ==> p.src == me)
//    case OutboundPacket(Some(p)) => p.src == me
//    case OutboundPacket(None()) => true
}

function AbstractifyOutboundCPacketsToSeqOfRaftPackets(out:OutboundPackets) : seq<RaftPacket>
  requires OutboundPacketsIsAbstractable(out)
{
  match out
    case Broadcast(broadcast) => AbstractifyCBroadcastToRaftPacketSeq(broadcast)
    case OutboundPacket(Some(p)) => [AbstractifyCPacketToRaftPacket(p)]
    case OutboundPacket(None()) => [] 
    case PacketSequence(s) => AbstractifySeqOfCPacketsToSeqOfRaftPackets(s)
} 


}