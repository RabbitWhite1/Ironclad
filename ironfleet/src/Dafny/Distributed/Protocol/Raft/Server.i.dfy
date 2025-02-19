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
  vote_granted:map<EndPoint, bool>, // server_id -> voted?(bool)
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
  && server.vote_granted == map []
}

function method RaftServerNumActions() : int
{
  3
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

function SpontaneousClock(ios:seq<RaftIo>) : int
{
  if SpontaneousIos(ios, 1) then ios[0].t else 0 // nonsense to avoid putting a precondition on this function
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
  ensures |ios| >= |ExtractSentPacketsFromIos(ios)|
{
  if |ios| == 0 then
    []
  else if ios[0].LIoOpSend? then
    [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
  else
    ExtractSentPacketsFromIos(ios[1..])
}

lemma {:opaque} lemma_NoSentPacketsExtraction(ios:seq<RaftIo>)
  requires forall i :: 0 <= i < |ios| ==> !ios[i].LIoOpSend?
  ensures ExtractSentPacketsFromIos(ios) == []
{
  reveal ExtractSentPacketsFromIos();
  for i := 0 to |ios|
    invariant forall i_ :: 0 <= i_ < i ==> !ios[i_].LIoOpSend?
    invariant ExtractSentPacketsFromIos(ios) == ExtractSentPacketsFromIos(ios[i..])
  {
    calc {
      ExtractSentPacketsFromIos(ios[i..]);
      ExtractSentPacketsFromIos([ios[i]] + ios[i+1..]);
      ExtractSentPacketsFromIos(ios[i+1..]);
    }
  }
  assert ExtractSentPacketsFromIos(ios) == [];
}

lemma {:opaque} lemma_OnlySentPacketsLeft(ios:seq<RaftIo>, sent_begin_index:int)
  requires 0 <= sent_begin_index < |ios|
  requires forall i :: 0 <= i < sent_begin_index ==> !ios[i].LIoOpSend?
  requires forall i :: sent_begin_index <= i < |ios| ==> ios[i].LIoOpSend?
  ensures ExtractSentPacketsFromIos(ios[sent_begin_index..]) == ExtractSentPacketsFromIos(ios)
{
  reveal ExtractSentPacketsFromIos();
  for i := 0 to sent_begin_index
    invariant forall i_ :: 0 <= i_ < i ==> !ios[i_].LIoOpSend?
    invariant ExtractSentPacketsFromIos(ios) == ExtractSentPacketsFromIos(ios[i..])
  {
    calc {
      ExtractSentPacketsFromIos(ios[i..]);
      ExtractSentPacketsFromIos([ios[i]] + ios[i+1..]);
      ExtractSentPacketsFromIos(ios[i+1..]);
    }
  }
  assert ExtractSentPacketsFromIos(ios[sent_begin_index..]) == ExtractSentPacketsFromIos(ios);
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

////////////////////////////////////////////////
// ReadClock action
////////////////////////////////////////////////
predicate RaftServerNextReadClock_Leader(s:RaftServer, s':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  var global_config := s.config.global_config;
  var params := global_config.params;
  
  && (
    if clock >= s.next_heartbeat_time then
      && UpperBoundedAddition(clock, params.heartbeat_timeout, params.max_integer_value) == s'.next_heartbeat_time
      && forall packet :: packet in sent_packets ==> packet.msg.RaftMessage_AppendEntries?
      && forall i :: (0 <= i < |global_config.server_eps| && i != s.config.server_id) 
          ==> (exists p :: p in sent_packets && p.dst == global_config.server_eps[i])
    else
      true
  )

}

predicate RaftServerNextReadClock_NonLeader(s:RaftServer, s':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  var global_config := s.config.global_config;
  var params := global_config.params;

  && (
    if clock >= s.next_election_time then
      // becomes candidate and starts election
      && s'.role == Candidate
      && UpperBoundedAddition(clock, params.min_election_timeout, params.max_integer_value) <= s'.next_election_time
      && s'.next_election_time <= UpperBoundedAddition(clock, params.max_election_timeout, params.max_integer_value)
      && forall packet :: packet in sent_packets ==> packet.msg.RaftMessage_RequestVote?
      && forall i :: (0 <= i < |global_config.server_eps| && i != s.config.server_id) 
          ==> (exists p :: p in sent_packets && p.dst == global_config.server_eps[i])
    else
      true
  )
}

predicate RaftServerNextReadClock(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  // for reseting timeout
  var sent_packets := ExtractSentPacketsFromIos(ios);

  // && true
  && SpontaneousIos(ios, 1)
  && (
    if (s.role == Leader) then
      && RaftServerNextReadClock_Leader(s, s', SpontaneousClock(ios), sent_packets)
    else
      && RaftServerNextReadClock_NonLeader(s, s', SpontaneousClock(ios), sent_packets)
  )
}


//////////////////////////////////////////////////////////
// Process AppendEntries
//////////////////////////////////////////////////////////
lemma lemma_MaybeOneMore_CountGreaterOrEqual(eps:seq<EndPoint>, end1:int, end2:int, numbers:map<EndPoint, int>, threshold:int)
  requires 0 <= end1 <= |eps|
  requires 0 <= end2 <= |eps|
  requires (forall ep :: ep in eps[..end1] ==> ep in numbers)
  requires (forall ep :: ep in eps[..end2] ==> ep in numbers)
  requires end2 == end1 + 1
  ensures (
    if numbers[eps[end1]] >= threshold then
      CountGreaterOrEqual(eps[..end1], numbers, threshold) + 1 == CountGreaterOrEqual(eps[..end2], numbers, threshold)
    else
      CountGreaterOrEqual(eps[..end1], numbers, threshold) == CountGreaterOrEqual(eps[..end2], numbers, threshold)
  )
{
    if numbers[eps[end1]] >= threshold {
      calc {
        CountGreaterOrEqual(eps[..end2], numbers, threshold);
        { assert eps[..end2] == eps[..end1] + [eps[end1]]; }
        CountGreaterOrEqual(eps[..end1] + [eps[end1]], numbers, threshold);
        { assert numbers[eps[end1]] >= threshold; }
        CountGreaterOrEqual(eps[..end1], numbers, threshold) + CountGreaterOrEqual([eps[end1]], numbers, threshold);
        CountGreaterOrEqual(eps[..end1], numbers, threshold) + 1;
      }
    } else {
      calc {
        CountGreaterOrEqual(eps[..end2], numbers, threshold);
        { assert eps[..end2] == eps[..end1] + [eps[end1]]; }
        CountGreaterOrEqual(eps[..end1] + [eps[end1]], numbers, threshold);
        { assert !(numbers[eps[end1]] >= threshold); }
        CountGreaterOrEqual(eps[..end1], numbers, threshold) + CountGreaterOrEqual([eps[end1]], numbers, threshold);
        CountGreaterOrEqual(eps[..end1], numbers, threshold);
      }
    }
}

function CountGreaterOrEqual(eps:seq<EndPoint>, numbers:map<EndPoint, int>, threshold:int) : int
  requires (forall ep :: ep in eps ==> ep in numbers)
{
  if |eps| == 0 then
    0
  else if numbers[eps[|eps|-1]] >= threshold then
    1 + CountGreaterOrEqual(eps[..|eps|-1], numbers, threshold)
  else
    CountGreaterOrEqual(eps[..|eps|-1], numbers, threshold)
}

predicate RaftServerNextProcessAppendEntries_GoodReply(s:RaftServer, s':RaftServer, received_packet:RaftPacket, sent_packet:RaftPacket)
  requires received_packet.msg.RaftMessage_AppendEntries?
  requires sent_packet.msg.RaftMessage_AppendEntriesReply?
  requires |s.log| >= 1
{
  var received_msg := received_packet.msg;
  var my_log_at_prev_log_index := if 0 <= received_msg.prev_log_index <= |s.log| - 1 then Some(s.log[received_msg.prev_log_index]) else None;
  var my_last_log := s.log[|s.log|-1];
  if (
    || received_msg.prev_log_index == 0 
    || (my_log_at_prev_log_index.Some? && received_msg.prev_log_term == my_log_at_prev_log_index.v.term)
  ) then
    && sent_packet.msg.success == true
    && sent_packet.msg.match_index == (if |received_msg.entries| == 0 then received_msg.prev_log_index else received_msg.entries[|received_msg.entries|-1].index)
    && s'.log == (if |received_msg.entries| == 0 then s.log else s.log[..received_msg.prev_log_index+1] + received_msg.entries)
    && s'.commit_index == if received_msg.leader_commit > s.commit_index then received_msg.leader_commit else s.commit_index
  else
    && sent_packet.msg.success == false
}

predicate RaftServerNextProcessAppendEntries(s:RaftServer, s':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>)
  requires raft_packet.msg.RaftMessage_AppendEntries?
{
  var received_packet := raft_packet;
  var received_msg := received_packet.msg;
  var ep := received_packet.src;

  && |s.log| >= 1
  && s.config == s'.config
  && (
    if (s.current_term < received_msg.term) then
      && s'.current_term == received_msg.term
      && s'.voted_for == None()
      && s'.role == Follower
    else
      true
  )
  && forall packet :: packet in sent_packets ==> packet.msg.RaftMessage_AppendEntriesReply?
  && |sent_packets| == 1
  && sent_packets[0].msg.RaftMessage_AppendEntriesReply?
  && (
    if (s'.current_term == received_msg.term) then
      var min_election_timeout := s'.config.global_config.params.min_election_timeout;
      var max_election_timeout := s'.config.global_config.params.max_election_timeout;
      var max_integer_value := s'.config.global_config.params.max_integer_value;
      // current_leader is updated
      && s'.role == Follower
      && s'.current_leader.Some?
      && 0 <= s'.current_leader.v < |s'.config.global_config.server_eps|
      && s'.config.global_config.server_eps[s'.current_leader.v] == received_packet.src
      // entry (if any) is appended
      && UpperBoundedAddition(clock, min_election_timeout, max_integer_value) <= s'.next_election_time <= UpperBoundedAddition(clock, max_election_timeout, max_integer_value)
      // proper reply is sent
      && RaftServerNextProcessAppendEntries_GoodReply(s, s', received_packet, sent_packets[0])
    else
      && sent_packets[0].msg.success == false
  )
}


//////////////////////////////////////////////////////////
// Process AppendEntriesReply
//////////////////////////////////////////////////////////
predicate RaftServer_GoodSentAppendEntries(s':RaftServer, ep:EndPoint, sent_packet:RaftPacket)
  requires |s'.log| >= 1
  requires WellFormedRaftServerConfig(s'.config)
  requires ep in s'.next_index
  requires ep in s'.match_index
  requires 1 <= s'.next_index[ep] <= |s'.log|
{
  var next_index := s'.next_index[ep];
  var log_index_end := if |s'.log| < next_index + LogEntrySeqSizeLimit() then |s'.log| else next_index + LogEntrySeqSizeLimit();

  && sent_packet.msg.RaftMessage_AppendEntries?
  && sent_packet.msg.term == s'.current_term
  && sent_packet.msg.leader_ep == s'.config.global_config.server_eps[s'.config.server_id]
  && sent_packet.msg.prev_log_index == next_index - 1
  && sent_packet.msg.prev_log_term == (if next_index == 0 then 0 else s'.log[next_index - 1].term)
  // && sent_packet.msg.entries == s'.log[next_index..log_index_end]
  && sent_packet.msg.leader_commit == s'.commit_index
  // && sent_packet.msg == RaftMessage_AppendEntries(
  //   s'.current_term,
  //   s'.config.global_config.server_eps[s'.config.server_id],
  //   next_index - 1,
  //   if next_index == 0 then 0 else s'.log[next_index - 1].term,
  //   s'.log[next_index..log_index_end],
  //   s'.commit_index
  // )
}

predicate RaftServerNextProcessAppendEntriesReply(s:RaftServer, s':RaftServer, received_packet:RaftPacket, sent_packets:seq<RaftPacket>)
  requires received_packet.msg.RaftMessage_AppendEntriesReply?
{
  var received_msg := received_packet.msg;
  var ep := received_packet.src;

  && (
    if (s.current_term < received_msg.term) then
      && s'.current_term == received_msg.term
      && s'.voted_for == None()
      && s'.role == Follower
    else
      true
  )
  && (
    if s'.role == Leader && s'.current_term == received_msg.term then
      if received_msg.success == true then
        // true
        && ep in s.match_index
        && (
          if received_msg.match_index > s.match_index[ep] then
            && s'.match_index == s.match_index[ep := received_msg.match_index]
          else
            && s'.match_index == s.match_index
        )
        && s'.next_index == s.next_index[ep := s'.match_index[ep] + 1]
        && (forall ep :: ep in s'.config.global_config.server_eps ==> ep in s'.match_index)
        && (forall i :: s.commit_index < i <= s'.commit_index ==> 
          CountGreaterOrEqual(s'.config.global_config.server_eps, s'.match_index, i) >= RaftMinQuorumSize(s'.config.global_config)
        )
      else
        && ep in s.next_index
        && ep in s.match_index
        && ep in s'.next_index
        && ep in s'.match_index
        && ep in s'.config.global_config.server_eps
        && s'.match_index == s'.match_index[ep := 0]
        && (s.next_index[ep] == 1 || s'.next_index[ep] <= s.next_index[ep])
        && s'.role == Leader
        && 1 <= s'.next_index[ep] <= |s'.log|
        && WellFormedRaftServerConfig(s'.config)
        && |sent_packets| == 1
        && RaftServer_GoodSentAppendEntries(s', ep, sent_packets[0])
    else
      true
  )
}


//////////////////////////////////////////////////////////
// Process RequestVote
//////////////////////////////////////////////////////////
predicate RaftServerNextProcessRequestVote(s:RaftServer, s':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>)
  requires raft_packet.msg.RaftMessage_RequestVote?
{
  true
}


//////////////////////////////////////////////////////////
// Process RequestVoteReply
//////////////////////////////////////////////////////////
function CountVoted(eps:seq<EndPoint>, vote_granted:map<EndPoint, bool>):int
  requires (forall ep :: ep in eps ==> ep in vote_granted)
{
  if |eps| == 0 then
    0
  else if vote_granted[eps[|eps|-1]] == true then
    1 + CountVoted(eps[..|eps|-1], vote_granted)
  else
    CountVoted(eps[..|eps|-1], vote_granted)
}

lemma lemma_MaybeOneMore_CountVoted(eps:seq<EndPoint>, end1:int, end2:int, vote_granted:map<EndPoint, bool>)
  requires 0 <= end1 <= |eps|
  requires 0 <= end2 <= |eps|
  requires (forall ep :: ep in eps[..end1] ==> ep in vote_granted)
  requires (forall ep :: ep in eps[..end2] ==> ep in vote_granted)
  requires end2 == end1 + 1
  ensures (
    if vote_granted[eps[end1]] == true then
      CountVoted(eps[..end1], vote_granted) + 1 == CountVoted(eps[..end2], vote_granted)
    else
      CountVoted(eps[..end1], vote_granted) == CountVoted(eps[..end2], vote_granted)
  )
{
    if vote_granted[eps[end1]] {
      calc {
        CountVoted(eps[..end2], vote_granted);
        { assert eps[..end2] == eps[..end1] + [eps[end1]]; }
        CountVoted(eps[..end1] + [eps[end1]], vote_granted);
        { assert vote_granted[eps[end1]]; }
        CountVoted(eps[..end1], vote_granted) + CountVoted([eps[end1]], vote_granted);
        CountVoted(eps[..end1], vote_granted) + 1;
      }
    } else {
      calc {
        CountVoted(eps[..end2], vote_granted);
        { assert eps[..end2] == eps[..end1] + [eps[end1]]; }
        CountVoted(eps[..end1] + [eps[end1]], vote_granted);
        { assert !(vote_granted[eps[end1]]); }
        CountVoted(eps[..end1], vote_granted) + CountVoted([eps[end1]], vote_granted);
        CountVoted(eps[..end1], vote_granted);
      }
    }
}

predicate RaftServerQuorumVoted(s':RaftServer)
{
  true
}

predicate RaftServerNextProcessRequestVoteReply(s:RaftServer, s':RaftServer, raft_packet:RaftPacket, sent_packets:seq<RaftPacket>)
  requires raft_packet.msg.RaftMessage_RequestVoteReply?
{
  var ep := raft_packet.src;
  var msg := raft_packet.msg;
  var eps := s'.config.global_config.server_eps;
  && (
    if s.role == Candidate && s.current_term == s'.current_term == msg.term then
      && (forall ep :: ep in eps ==> ep in s'.vote_granted)
      && (
        if CountVoted(eps, s'.vote_granted) >= RaftMinQuorumSize(s'.config.global_config) && sent_packets != [] then
          // true
          && s'.role == Leader
          && |s'.log| >= 1
          && WellFormedRaftServerConfig(s'.config)
          && (
            forall packet :: packet in sent_packets ==> (
              && packet.dst in s'.config.global_config.server_eps 
              && packet.dst in s'.next_index
              && packet.dst in s'.match_index
              && 1 <= s'.next_index[packet.dst] <= |s'.log|
              // TOPROVE
              // && RaftServer_GoodSentAppendEntries(s', packet.dst , packet)
              
            )
          )
        else
          && true
      )
    else
      && true
  )
}


predicate RaftServerNextProcessPacket(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  && |ios| >= 1
  && ios[0].LIoOpReceive?
  && (
    var sent_packets := ExtractSentPacketsFromIos(ios);
    var potential_clock := if |ios| >= 2 && ios[1].LIoOpReadClock? then ios[1].t else 0;

    match ios[0].r.msg
      case RaftMessage_Invalid() => (s == s' && sent_packets == [])
      case RaftMessage_RequestVote(_,_,_,_) => RaftServerNextProcessRequestVote(s, s', ios[0].r, potential_clock, sent_packets)
      case RaftMessage_RequestVoteReply(_,_) => RaftServerNextProcessRequestVoteReply(s, s', ios[0].r, sent_packets)
      case RaftMessage_AppendEntries(_,_,_,_,_,_) => RaftServerNextProcessAppendEntries(s, s', ios[0].r, potential_clock, sent_packets)
      case RaftMessage_AppendEntriesReply(_,_,_) => RaftServerNextProcessAppendEntriesReply(s, s', ios[0].r, sent_packets)
      case RaftMessage_Request(_,_) => (s == s' && sent_packets == [])
      case RaftMessage_Reply(_,_,_,_) => (s == s' && sent_packets == [])
  )
}


predicate RaftServerNextCommitAndApply(s:RaftServer, s':RaftServer, ios:seq<RaftIo>)
{
  var sent_packets := ExtractSentPacketsFromIos(ios);
  && |sent_packets| <= 1
  // && (
  //   if |sent_packets| > 0 then
  //     true
  //     // && |sent_packets| == 1
  //     // && s.last_applied < s.commit_index
  //     // && s'.last_applied == s.last_applied + 1
  //     // && sent_packets[0].msg.RaftMessage_Reply?
  //   else
  //     true
  // )
}


}