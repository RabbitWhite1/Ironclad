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

datatype RaftMessage =
    RequestVote(term:int, candidate_id:int, last_log_index:int, last_log_term:int)
  | RequestVoteReply(term:int, vote_granted:bool)
  | AppendEntries(term:int, leader_id:int, prev_log_index:int, prev_log_term:int, entries:seq<AppRequest>, leader_commit:int)
  | AppendEntriesReply(term:int, success:bool)
}