/////////////////////////////////////////////////////////////////////////////
//
// This file defines behaviours of a server
//
/////////////////////////////////////////////////////////////////////////////
include "../../Common/Logic/Option.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Services/Raft/AppStateMachine.s.dfy"
include "../Common/UpperBound.s.dfy"
include "../Common/Utils.s.dfy"
include "Config.i.dfy"
include "Types.i.dfy"

module Raft__Server_i {

import opened Logic__Option_i
import opened Environment_s
import opened AppStateMachine_s
import opened Common__UpperBound_s
import opened Common__Utils_s
import opened Native__Io_s
import opened Raft__Config_i
import opened Raft__Types_i

datatype RaftServer = RaftServer(
  config:RaftServerConfig,
  role:RaftRole,
  // for timeout
  next_heartbeat_time:int,
  next_election_time:int,
  // persistent state
  current_leader:Option<int>,
  current_term:int,
  voted_for:Option<int>,
  log:seq<LogEntry>,
  // volatile state on all servers
  commit_index:int,
  last_applied:int,
  // volatile state on leaders
  next_index:map<EndPoint, int>,
  match_index:map<EndPoint, int>,
  num_replicated:seq<int>, // log index -> num of replicated
  // App
  app:AppState
)

predicate RaftServerInit(server:RaftServer, config:RaftServerConfig) {
  && server.config == config
  && server.current_term == 0
  && server.voted_for == None()
  && server.log == []
  && server.commit_index == 0
  && server.last_applied == 0
  && server.next_index == map []
  && server.match_index == map []
}

////////////////////////////////////////////////
// Clock-related
////////////////////////////////////////////////
predicate SpontaneousIos(ios:seq<RaftIo>, clocks:int)
  requires 0<=clocks<=1
{
  && clocks <= |ios|
  && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
  && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
}

function SpontaneousClock(ios:seq<RaftIo>) : ClockReading
{
  if SpontaneousIos(ios, 1) then ClockReading(ios[0].t) else ClockReading(0) // nonsense to avoid putting a precondition on this function
}

////////////////////////////////////////////////
// Utils
////////////////////////////////////////////////
function RaftLastLogIndex(s:RaftServer) : int
{
  if s.log == [] then 0 else s.log[|s.log|-1].index
}

function RaftLastLogTerm(s:RaftServer) : int
{
  if s.log == [] then 0 else s.log[|s.log|-1].term
}

function RaftGetLogEntry(s:RaftServer, index:int) : LogEntry
  requires 0 < index <= |s.log|
{
  s.log[index-1]
}

function {:opaque} ExtractSentPacketsFromIos(ios:seq<RaftIo>) : seq<RaftPacket>
  ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
{
  if |ios| == 0 then
    []
  else if ios[0].LIoOpSend? then
    [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
  else
    ExtractSentPacketsFromIos(ios[1..])
}

predicate WellFormedLRaftServer(s:RaftServer) {
  if s.role.Leader? then
    |s.log| == |s.num_replicated|
  else
    true
}

predicate RaftBroadcastToEveryone(config:RaftConfig, my_ep:EndPoint, m:RaftMessage, sent_packets:seq<RaftPacket>)
{
  && |sent_packets| == |config.server_eps|
  && my_ep in config.server_eps
  && forall idx {:trigger sent_packets[idx]}{:trigger config.server_eps[idx]}{:trigger LPacket(config.server_eps[idx], my_ep, m)} ::
      0 <= idx < |sent_packets| ==> sent_packets[idx] == LPacket(config.server_eps[idx], my_ep, m)
}

predicate RaftServerSentAppendEntries(s:RaftServer, dst:EndPoint, sent_packet:RaftPacket)
  requires sent_packet.msg.RaftMessage_AppendEntries?
{
  var msg := sent_packet.msg;
  && dst in s.next_index
  && var next_index := s.next_index[dst];
  && sent_packet.dst == dst
  && sent_packet.src == s.config.server_ep
  && |msg.entries| > 0
  && 0 < next_index <= |s.log|
  && |msg.entries| == |s.log| - next_index
  && forall i :: 0 <= i < |msg.entries| ==> msg.entries[i] == RaftGetLogEntry(s, s.next_index[dst] + i)
  && msg.leader_ep == s.config.server_ep
  && msg.prev_log_index == RaftLastLogIndex(s)
  && msg.prev_log_term == RaftLastLogTerm(s)
  && msg.leader_commit == s.commit_index
}

////////////////////////////////////////////////
// Handle received packets
////////////////////////////////////////////////
predicate RaftServerMaybeStepDown(s:RaftServer, s':RaftServer, term:int)
{
  if s.current_term < term then
    && s'.role == Follower
    && s'.voted_for == None()
    && s'.current_term == term
  else
    s'.role == s.role
    && s'.voted_for == s.voted_for
    && s'.current_term == s.current_term
}

predicate RaftServerMaybeResetElectionTimeout(s:RaftServer, s':RaftServer, clock:int, msg:RaftMessage)
  requires msg.RaftMessage_AppendEntries?
{
  // TOPROVE
  // var global_config := s.config.global_config;
  // s.current_leader.Some? && msg.leader_ep == s.current_leader.v ==> exists election_timeout :: (
  //   && global_config.params.min_election_timeout <= election_timeout <= global_config.params.max_election_timeout
  //   && s' == s.(next_election_time := UpperBoundedAddition(clock, election_timeout, global_config.params.max_integer_value))
  // )
  true
}

predicate RaftServerNextHandleAppendEntries(s:RaftServer, s':RaftServer, received_packet: RaftPacket, clock:int, sent_packages:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_AppendEntries?
{
  var received_msg := received_packet.msg;
  // maybe step down
  && RaftServerMaybeStepDown(s, s', received_packet.msg.term)
  // handle the entries
  && received_msg.prev_log_index >= 0
  && forall entry :: entry in received_packet.msg.entries ==> LogEntryValid(entry)
  // No matter when receiving this, a follower should reset its election timeout
  && RaftServerMaybeResetElectionTimeout(s, s', clock, received_msg)
  && (
    var entries := received_packet.msg.entries;
    if (
      || received_msg.prev_log_index == 0
      || (&& received_msg.prev_log_index <= |s.log| 
          && RaftGetLogEntry(s, received_msg.prev_log_index).term == received_msg.prev_log_term
          )
    ) then
      // entries should be appended
      && |s'.log| == |s.log| + |entries|
      && forall entry :: entry in entries ==> 0 < entry.index <= |s'.log| && RaftGetLogEntry(s', entry.index) == entry
      && |sent_packages| == 1
      && var sent_msg := sent_packages[0].msg;
        && sent_msg.RaftMessage_AppendEntriesReply?
        && sent_msg.term == s'.current_term
        && sent_msg.success == true
        && sent_msg.match_index == RaftLastLogIndex(s')
    else
      // or discarded
      && s'.log == s.log
      && |sent_packages| == 1
      && var sent_msg := sent_packages[0].msg;
        && sent_msg.RaftMessage_AppendEntriesReply?
        && sent_msg.term == s'.current_term
        && sent_msg.success == false
  )
}

predicate RaftServerNextHandleAppendEntriesReply(s:RaftServer, s':RaftServer, received_packet: RaftPacket, sent_packages:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_AppendEntriesReply?
{
  var received_msg := received_packet.msg;
  && WellFormedLRaftServer(s)
  && WellFormedLRaftServer(s')
  // maybe step down
  && RaftServerMaybeStepDown(s, s', received_packet.msg.term)
  // only leader handles this
  && (
    var sender := received_packet.src;
    var index := received_msg.match_index;
    if s.role.Leader? && s.current_term == received_msg.term then
      // handle this reply
      if received_msg.success == true then
        && s'.match_index == s.match_index[sender := index]
        && s'.next_index == s.next_index[sender := index + 1]
        // if quorum replicated, commit
        && s'.commit_index == max(s.commit_index, index)
        && forall i :: s.commit_index < i <= RaftLastLogIndex(s') ==> (
          && 0 <= i < |s'.log|
          && s'.log[i].is_commited == true
          && s'.num_replicated[i] >= RaftMinQuorumSize(s.config.global_config)
        )
        && s' == s.(match_index := s'.match_index, next_index := s'.next_index)
      else
        && sender in s.next_index
        && s' == s.(next_index := s.next_index[sender := s.next_index[sender] - 1])
        && |sent_packages| == 1
        && var sent_msg := sent_packages[0].msg;
          && sent_msg.RaftMessage_AppendEntries?
          && RaftServerSentAppendEntries(s, sender, sent_packages[0])
          && sent_msg.term == s'.current_term
          && sent_msg.prev_log_index == s.next_index[sender] - 1
          && 0 <= sent_msg.prev_log_index <= |s'.log|
          && (
            if sent_msg.prev_log_index == 0 then
              sent_msg.prev_log_term == 0
            else
              sent_msg.prev_log_term == RaftGetLogEntry(s, sent_msg.prev_log_index).term
          )
          && sent_msg.leader_commit == s'.commit_index
          && sent_msg.entries == []
    else
      s' == s.(role := s'.role, voted_for := s'.voted_for, current_term := s'.current_term)
  )
  // nothing needs to be sent
  && |sent_packages| == 0
  
}

predicate RaftServerNextHandleRequestVote(s:RaftServer, s':RaftServer, received_packet: RaftPacket, sent_packages:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_RequestVote?
{
  // maybe step down
  && RaftServerMaybeStepDown(s, s', received_packet.msg.term)
}

predicate RaftServerNextHandleRequestVoteReply(s:RaftServer, s':RaftServer, received_packet: RaftPacket, sent_packages:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_RequestVoteReply?
{
  // maybe step down
  && RaftServerMaybeStepDown(s, s', received_packet.msg.term)
}

predicate RaftServerNextReadClockAndProcessPacket(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
  requires ios[0].r.msg.RaftMessage_AppendEntries?
{
  && |ios| > 1
  && ios[1].LIoOpReadClock?
  && (forall io :: io in ios[2..] ==> io.LIoOpSend?)
  && forall entry :: entry in ios[0].r.msg.entries ==> LogEntryValid(entry)
  && RaftServerNextHandleAppendEntries(s, s', ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))
}

predicate RaftServerNextHandleRequest(s:RaftServer, s':RaftServer, received_packet:RaftPacket, sent_packets:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_Request?
{
  if |received_packet.msg.req| > MaxAppRequestSize() then
    && sent_packets == []
    && s' == s
  else
    // TODO
    && sent_packets == []
    && s' == s
}

predicate RaftServerNextHandleReply(s:RaftServer, s':RaftServer, received_packet:RaftPacket, sent_packets:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_Reply?
{
  && sent_packets == []
  && s' == s
}

predicate RaftServerNextProcessPacketWithoutReadingClock(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
  requires !ios[0].r.msg.RaftMessage_AppendEntries?
{
  && forall io :: io in ios[1..] ==> io.LIoOpSend?
  && var sent_packets := ExtractSentPacketsFromIos(ios);
    match ios[0].r.msg
      case RaftMessage_Invalid() => false
      case RaftMessage_RequestVote(_,_,_,_) => RaftServerNextHandleRequestVote(s, s', ios[0].r, sent_packets)
      case RaftMessage_RequestVoteReply(_,_) => RaftServerNextHandleRequestVoteReply(s, s', ios[0].r, sent_packets)
      case RaftMessage_AppendEntriesReply(_,_,_) => RaftServerNextHandleAppendEntriesReply(s, s', ios[0].r, sent_packets)
      case RaftMessage_Request(_,_) => RaftServerNextHandleRequest(s, s', ios[0].r, sent_packets)
      case RaftMessage_Reply(_,_,_,_) => RaftServerNextHandleReply(s, s', ios[0].r, sent_packets)
}

predicate RaftServerNextProcessPacket(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  && |ios| >= 1
  && if ios[0].LIoOpTimeoutReceive? then
      s' == s && |ios| == 1 // TODO: why? (maybe due to implmentation)
    else
      (
        && ios[0].LIoOpReceive?
        && if ios[0].r.msg.RaftMessage_AppendEntries? then
            RaftServerNextReadClockAndProcessPacket(s, s', ios)
          else
            RaftServerNextProcessPacketWithoutReadingClock(s, s', ios)
      )
}

////////////////////////////////////////////////
// Handle other events
////////////////////////////////////////////////
predicate RaftServerNextReadClockMaybeSendHeartbeat(s:RaftServer, s':RaftServer, clock:ClockReading, sent_packets:seq<RaftPacket>)
{
  && s.role.Leader?
  && (
    if clock.t < s.next_heartbeat_time then
      s' == s && sent_packets == []
    else
      && s'.next_heartbeat_time == UpperBoundedAddition(clock.t, s.config.global_config.params.heartbeat_timeout, s.config.global_config.params.max_integer_value)
      && RaftBroadcastToEveryone(
        s.config.global_config, s.config.server_ep, 
        RaftMessage_AppendEntries(
          s.current_term, s.config.server_ep, 
          RaftLastLogIndex(s), RaftLastLogTerm(s), 
          [], s.commit_index),
        sent_packets)
      && s' == s.(next_heartbeat_time := s'.next_heartbeat_time)
  )
}

predicate RaftServerNextReadClockMaybeStartElection(s:RaftServer, s':RaftServer, clock:ClockReading, sent_packets:seq<RaftPacket>)
{
  && (s.role.Follower? || s.role.Candidate?)
  && (
    if clock.t < s.next_election_time then
      s' == s && sent_packets == []
    else
      && s'.next_election_time == UpperBoundedAddition(clock.t, s.config.global_config.params.heartbeat_timeout, s.config.global_config.params.max_integer_value)
      && RaftBroadcastToEveryone(
        s.config.global_config, s.config.server_ep, 
        RaftMessage_RequestVote(
          s.current_term, s.config.server_id, 
          RaftLastLogIndex(s), RaftLastLogTerm(s)),
        sent_packets)
      && s' == s.(next_election_time := s'.next_election_time)
  )
}

predicate RaftServerNoReceiveNext(s:RaftServer, nextActionIndex:int, s':RaftServer, ios:seq<RaftIo>)
{
  var sent_packets := ExtractSentPacketsFromIos(ios);

  if nextActionIndex == 1 then
    if s.role.Leader? then
      // leader may timeout for heartbeat
      && SpontaneousIos(ios, 1)
      && RaftServerNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets)
    else if s.role.Follower? then
      // follower may timeout for election
      && SpontaneousIos(ios, 1)
      && RaftServerNextReadClockMaybeStartElection(s, s', SpontaneousClock(ios), sent_packets)
    else
      //candidate may timeout for election
      && s.role.Candidate?
      && SpontaneousIos(ios, 1)
      && RaftServerNextReadClockMaybeStartElection(s, s', SpontaneousClock(ios), sent_packets)
  else
    false
}

function method RaftServerNumActions() : int
{
  3
}

}