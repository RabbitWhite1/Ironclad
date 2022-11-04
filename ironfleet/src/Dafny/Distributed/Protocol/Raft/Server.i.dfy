/////////////////////////////////////////////////////////////////////////////
//
// This file defines behaviours of a server
//
/////////////////////////////////////////////////////////////////////////////
include "../../Common/Framework/Environment.s.dfy"
include "../../Services/Raft/AppStateMachine.s.dfy"
include "../Common/UpperBound.s.dfy"
include "Config.i.dfy"
include "Types.i.dfy"

module Raft__Server_i {

import opened Environment_s
import opened AppStateMachine_s
import opened Common__UpperBound_s
import opened Raft__Config_i
import opened Raft__Types_i

datatype RaftServer = RaftServer(
  config:RaftServerConfig,
  role:RaftRole,
  // for timeout
  next_heartbeat_time:int,
  next_election_time:int,
  // persistent state
  current_term:int,
  voted_for:int,
  log:seq<LogEntry>,
  // volatile state on all servers
  commit_index:int,
  last_applied:int,
  // volatile state on leaders
  next_index:map<int, int>,
  match_index:map<int, int>,
  // App
  app:AppState
)

predicate RaftServerInit(server:RaftServer, config:RaftServerConfig) {
  && server.config == config
  && server.current_term == 0
  && server.voted_for == -1
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
function RaftPrevLogIndex(s:RaftServer) : int
{
  if s.log == [] then 0 else s.log[|s.log|-1].index
}

function RaftPrevLogTerm(s:RaftServer) : int
{
  if s.log == [] then 0 else s.log[|s.log|-1].term
}

predicate RaftBroadcastToEveryone(config:RaftConfig, myidx:int, m:RaftMessage, sent_packets:seq<RaftPacket>)
{
  && |sent_packets| == |config.server_eps|
  && 0 <= myidx < |config.server_eps|
  && forall idx {:trigger sent_packets[idx]}{:trigger config.server_eps[idx]}{:trigger LPacket(config.server_eps[idx], config.server_eps[myidx], m)} ::
      0 <= idx < |sent_packets| ==> sent_packets[idx] == LPacket(config.server_eps[idx], config.server_eps[myidx], m)
}

////////////////////////////////////////////////
// Handle received packets
////////////////////////////////////////////////
predicate RaftServerNextHandleRequestVote(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  true
}

predicate RaftServerNextHandleRequestVoteReply(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  true
}

predicate RaftServerNextHandleAppendEntries(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  true
}

predicate RaftServerNextHandleAppendEntriesReply(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  true
}

predicate RaftServerNextProcessPacket(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  && |ios| >= 1
  && if ios[0].LIoOpTimeoutReceive? then
      s' == s && |ios| == 1 // TODO: why?
    else
      (
        && ios[0].LIoOpReceive?
        && if ios[0].r.msg.RaftMessage_RequestVote? then
            RaftServerNextHandleRequestVote(s, s', ios)
          else if ios[0].r.msg.RaftMessage_RequestVoteReply? then
            RaftServerNextHandleRequestVoteReply(s, s', ios)
          else if ios[0].r.msg.RaftMessage_AppendEntries? then
            // Note: this is the only one that may requires a election timeout reset
            RaftServerNextHandleAppendEntries(s, s', ios)
          else
            ios[0].r.msg.RaftMessage_AppendEntriesReply? && RaftServerNextHandleAppendEntriesReply(s, s', ios)
      )
}

////////////////////////////////////////////////
// Handle other events
////////////////////////////////////////////////
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

predicate RaftServerNextReadClockMaybeSendHeartbeat(s:RaftServer, s':RaftServer, clock:ClockReading, sent_packets:seq<RaftPacket>)
{
  && s.role.Leader?
  && (
    if clock.t < s.next_heartbeat_time then
      s' == s && sent_packets == []
    else
      && s'.next_heartbeat_time == UpperBoundedAddition(clock.t, s.config.global_config.heartbeat_timeout, s.config.global_config.max_integer_value)
      && RaftBroadcastToEveryone(
        s.config.global_config, s.config.server_id, 
        RaftMessage_AppendEntries(
          s.current_term, s.config.server_id, 
          RaftPrevLogIndex(s), RaftPrevLogTerm(s), 
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
      && s'.next_election_time == UpperBoundedAddition(clock.t, s.config.global_config.heartbeat_timeout, s.config.global_config.max_integer_value)
      && RaftBroadcastToEveryone(
        s.config.global_config, s.config.server_id, 
        RaftMessage_RequestVote(
          s.current_term, s.config.server_id, 
          RaftPrevLogIndex(s), RaftPrevLogTerm(s)),
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

function RaftServerNumActions() : int
{
  10
}

}