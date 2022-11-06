include "../../Services/Raft/AppStateMachine.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Raft__Types_i {

import opened AppStateMachine_s
import opened Environment_s
import opened Native__Io_s

type RaftEnvironment = LEnvironment<EndPoint, RaftMessage>
type RaftPacket = LPacket<EndPoint, RaftMessage>
type RaftIo = LIoOp<EndPoint, RaftMessage>

datatype LogEntry = LogEntry(term:int, index:int, req:AppRequest, is_commited:bool)

predicate LogEntryValid(entry:LogEntry) {
  && entry.term > 0 && entry.index > 0
}

datatype RaftMessage =
    RaftMessage_RequestVote(term:int, candidate_ep:EndPoint, last_log_index:int, last_log_term:int)
  | RaftMessage_RequestVoteReply(term:int, vote_granted:bool)
  | RaftMessage_AppendEntries(term:int, leader_ep:EndPoint, prev_log_index:int, prev_log_term:int, entries:seq<LogEntry>, leader_commit:int)
  | RaftMessage_AppendEntriesReply(term:int, success:bool, match_index:int)

datatype RaftRole = Follower | Candidate | Leader

datatype ClockReading = ClockReading(t:int)


}