include "../../Services/Raft/AppStateMachine.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "AppInterface.i.dfy"
include "CTypes.i.dfy"

module Raft__CMessage_i {

import opened Raft__AppInterface_i
import opened Raft__CTypes_i
import opened AppStateMachine_s
import opened Environment_s
import opened Native__Io_s

datatype CLogEntry = CLogEntry(term:uint64, index:uint64, req:CAppRequest, is_commited:bool)

predicate CLogEntryValid(entry:CLogEntry) {
  && entry.term > 0 && entry.index > 0
}

datatype CMessage =
    CMessage_RequestVote(term:uint64, candidate_ep:EndPoint, last_log_index:uint64, last_log_term:uint64)
  | CMessage_RequestVoteReply(term:uint64, vote_granted:bool)
  | CMessage_AppendEntries(term:uint64, leader_ep:EndPoint, prev_log_index:uint64, prev_log_term:uint64, entries:seq<CLogEntry>, leader_commit:uint64)
  | CMessage_AppendEntriesReply(term:uint64, success:bool, match_index:uint64)

datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

datatype CBroadcast = CBroadcast(src:EndPoint, dsts:seq<EndPoint>, msg:CMessage) | CBroadcastNop

datatype OutboundPackets = Broadcast(broadcast:CBroadcast) | OutboundPacket(p:Option<CPacket>) | PacketSequence(s:seq<CPacket>)

predicate CMessageIsAbstractable(msg:CMessage) {
  // TODO: unlikely all are true
  match msg {
    case CMessage_RequestVote(_, _, _, _) => true
    case CMessage_RequestVoteReply(_, _) => true
    case CMessage_AppendEntries(_, _, _, _, _, _) => true
    case CMessage_AppendEntriesReply(_, _, _) => true
  }
}

}