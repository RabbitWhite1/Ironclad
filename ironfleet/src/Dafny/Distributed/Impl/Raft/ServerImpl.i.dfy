include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Protocol/Raft/Config.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../../Services/Raft/AppStateMachine.s.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NetClient.i.dfy"
include "AppInterface.i.dfy"
include "CMessage.i.dfy"
include "Config.i.dfy"
include "CTypes.i.dfy"
include "PacketParsing.i.dfy"


module Raft__ServerImpl_i {

import opened Collections__Seqs_i
import opened Logic__Option_i
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Raft__Config_i
import opened Raft__Server_i
import opened Raft__ServerScheduler_i
import opened Raft__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened AppStateMachine_s
import opened Raft__AppInterface_i
import opened Raft__CMessage_i
import opened Raft__ConfigState_i
import opened Raft__CTypes_i
import opened Raft__PacketParsing_i

class ServerImpl
{
  var net_client:NetClient?;
  var local_addr:EndPoint;
  var nextActionIndex:uint64;

  var config:ServerConfigState;
  var role:RaftRole;
  // for timeout
  var next_heartbeat_time:uint64;
  var next_election_time:uint64;
  // persistent state
  var current_leader:Option<EndPoint>;
  var current_term:uint64;
  var voted_for:Option<EndPoint>;
  var log:seq<CLogEntry>;
  // volatile state on all servers
  var commit_index:uint64;
  var last_applied:uint64;
  // volatile state on leaders
  var next_index:map<EndPoint, uint64>;
  var match_index:map<EndPoint, uint64>;
  var num_replicated:seq<int>; // log index -> num of replicated

  var msg_grammar:G;

  var app_state:AppStateMachine;

  ghost var repr : set<object>;

  constructor() {
    net_client := null;
    role := Follower;
    next_heartbeat_time := 0;
    next_election_time := 0;
    current_leader := None();
    current_term := 0;
    voted_for := None();
    log := [];
    commit_index := 0;
    last_applied := 0;
    next_index := map[];
    match_index := map[];
    num_replicated := [];
    var app_s := AppStateMachine.Initialize();
    app_state := app_s;
  }

  predicate Valid()
    reads this
    reads this.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
  {
    && (0 <= nextActionIndex as int < RaftServerNumActions())
    && net_client != null
    && ServerConfigStateIsValid(config)
    && NetClientIsValid(net_client)
    && EndPoint(net_client.MyPublicKey()) == local_addr
    && EndPoint(net_client.MyPublicKey()) == config.server_ep
    && repr == { this } + NetClientRepr(net_client)
    && msg_grammar == CMessage_grammar()
    && (current_leader.None? || (current_leader.Some? && current_leader.v in config.global_config.server_eps))
    // Term
    && current_term as int <= MaxLogEntryTerm()
    // Log
    && 1 <= |log| <= ServerMaxLogSize() as int
    && log[0] == CLogEntry(0, 0, [], 0, 1)
    && (forall i :: 0 <= i < |log| ==> ValidLogEntry(log[i]))
    // TODO: this may not be true when truncating
    && (forall i :: 0 <= i < |log| ==> log[i].index as int == i)
    && LogEntrySeqIndexIncreasing(log)
    && (
      role.Leader? ==> (
        forall ep :: ep in config.global_config.server_eps ==> (
          && ep in next_index 
          && ep in match_index
          && 1 <= next_index[ep] <= |log| as uint64
          && 0 <= match_index[ep] < next_index[ep]
        )
      )
    )
    && |config.global_config.server_eps| >= 1
  }

  function MapUint64MapValueToInt<T>(m:map<T, uint64>) : map<T, int>
    requires true
    ensures forall k :: k in m ==> k in MapUint64MapValueToInt(m)
    ensures forall k, v :: k in m && v == m[k] ==> MapUint64MapValueToInt(m)[k] == v as int
  {
    map k:T | k in m :: m[k] as int
  }

  function AbstractifyToRaftServer() : RaftServer
    reads this
    reads this.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
    requires Valid()
    ensures Valid()
  {
    RaftServer(
      AbstractifyServerConfigStateToRaftServerConfig(config),
      role,
      next_heartbeat_time as int,
      next_election_time as int,
      current_leader,
      current_term as int,
      voted_for,
      AbstractifyCLogEntrySeqToRaftLogEntrySeq(log),
      commit_index as int,
      last_applied as int,
      MapUint64MapValueToInt(next_index),
      MapUint64MapValueToInt(match_index),
      num_replicated,
      app_state.Abstractify()
    )
  }

  function AbstractifyToRaftServerScheduler() : RaftServerScheduler
    requires Valid()
    reads this
    reads this.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
  {
    RaftServerScheduler(
      this.AbstractifyToRaftServer(),
      this.nextActionIndex as int
    )
  }

  method BecomeLeader() returns ()
    requires Valid()
    requires MaxLogEntryIndex() - LastLogEntryIndex() as int >= 1
    modifies this
    ensures this.role.Leader?
    ensures this.net_client == old(this.net_client)
    ensures Valid()
  {
    var i := 0;
    var last_log_entry := GetLastLogEntry();
    assert log[|log| - 1].index == last_log_entry.index;
    this.role := Candidate;
    while i < |config.global_config.server_eps|
      invariant 0 <= i <= |config.global_config.server_eps|
      decreases |config.global_config.server_eps| - i
      invariant !role.Leader?
      invariant 1 <= |log| <= ServerMaxLogSize() as int
      invariant log[|log| - 1] == old(log)[|old(log)| - 1]
      invariant log[|log| - 1].index == old(log)[|old(log)| - 1].index
      invariant forall i_ :: 0 <= i_ < i ==> (
        var ep_ := config.global_config.server_eps[i_]; 
        && ep_ in next_index 
        && ep_ in match_index
        && 1 <= next_index[ep_] <= |log| as uint64
        && 0 <= match_index[ep_] < next_index[ep_]
      )
      invariant Valid()
      invariant log == old(log)
      invariant this.net_client == old(this.net_client)
    {
      var ep := config.global_config.server_eps[i];
      next_index := next_index[ep := last_log_entry.index + 1];
      assert last_log_entry.index >= 0;
      assert next_index[ep] >= 1;
      if ep != local_addr {
        match_index := match_index[ep := 0];
      } else {
        match_index := match_index[ep := last_log_entry.index];
      }
      i := i + 1;
    }
    this.role := Leader;
    assert forall ep :: ep in config.global_config.server_eps ==> ep in next_index && ep in match_index;
  }

  method Init(
    config:ServerConfigState,
    nc:NetClient,
    ghost env:HostEnvironment
  ) returns (ok:bool)
    requires env.Valid() && env.ok.ok()
    requires nc.env == env
    requires NetClientIsValid(nc)
    requires ServerConfigStateIsValid(config)
    requires EndPoint(nc.MyPublicKey()) == config.server_ep
    requires WellFormedRaftServerConfig(AbstractifyServerConfigStateToRaftServerConfig(config))
    modifies this
    ensures ok ==> (
      && Valid()
      && Env() == nc.env
    )
  {
    this.config := config;
    this.net_client := nc;
    this.nextActionIndex := 0;
    this.local_addr := EndPoint(net_client.MyPublicKey());
    this.msg_grammar := CMessage_grammar();
    this.repr := { this } + NetClientRepr(net_client);
    this.current_leader := Some(this.config.global_config.server_eps[0]);
    this.log := [CLogEntry(0, 0, [], 0, 1)];
    this.role := Follower;
    // TODO: Remove this
    this.current_term := 1;
    assert LastLogEntryIndex() == 0;
    if this.current_leader.Some? && this.config.server_ep == this.current_leader.v {
      assert MaxLogEntryIndex() - LastLogEntryIndex() as int >= 1;
      this.BecomeLeader();
      assert net_client.env == nc.env;
    } else{
      this.role := Follower;
      this.current_term := 0;
    }
    assert net_client.env == nc.env;
    ok := true;
  }

  function Env() : HostEnvironment
    requires net_client != null
    reads this, NetClientIsValid.reads(net_client)
  {
    net_client.env
  }

  method GetMyIndex() returns(index:uint64)
    requires Valid()
    ensures 0 <= index as int < |config.global_config.server_eps|
    ensures config.global_config.server_eps[index] == config.server_ep
  {
    index := GetEndPointIndex(config.global_config, config.server_ep);
  }

  function method LastLogEntryIndex() : uint64
    requires Valid()
    reads this
    reads this.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
    requires 1 <= |log| <= ServerMaxLogSize()
    ensures LastLogEntryIndex() as int <= MaxLogEntryIndex()
    // TODO: this may not be true when truncating
    ensures LastLogEntryIndex() as int == |log| - 1
  {
    log[|log| - 1].index
  }

  method GetLastLogEntry() returns(log_entry:CLogEntry)
    requires Valid()
    requires |log| - 1 >= 0
    ensures log_entry in log
    ensures log_entry == log[|log| - 1]
    ensures Valid();
  {
    assert |log| - 1 >= 0;
    log_entry := log[|log| - 1];
  }

  method AddLogEntries(entries:seq<CLogEntry>) returns()
    requires Valid()
    requires forall entry :: entry in entries ==> ValidLogEntry(entry)
    requires |entries| <= ServerMaxLogSize() - |this.log|
    requires LogEntrySeqIndexIncreasing(entries)
    requires |entries| > 0 ==> (LastLogEntryIndex() + 1 == entries[0].index == |log| as uint64)
    requires (forall i :: 0 <= i < |entries| ==> entries[i].index as int == i+|log|)
    modifies this
    ensures Valid()
    ensures this.role == old(this.role)
    ensures log == old(log) + entries
    ensures this.Env() == old(this.Env())
    ensures this.nextActionIndex == old(this.nextActionIndex)
    ensures this.repr == old(this.repr)
  {
    this.log := this.log + entries;
  }

  method CreateLogEntry(seqno_req:uint64, req:CAppRequest) returns (ok:bool, entry:CLogEntry)
    requires this.Valid()
    requires 0 <= seqno_req as int <= MaxSeqno()
    requires CAppRequestMarshallable(req)
    ensures ok ==> (
      && this.Valid()
      && ValidLogEntry(entry)
    )
  {
    var last_log_entry := this.GetLastLogEntry();
    var last_log_index:uint64 := last_log_entry.index;
    var last_log_term:uint64 := last_log_entry.term;

    if last_log_index >= ServerMaxLogSize() as uint64 {
      ok := false;
      return;
    }

    entry := CLogEntry(this.current_term, last_log_index + 1, req, seqno_req, /*is_commited*/0);
    ok := true;
  }

  method PrepareAppendEntriesPacket(ep:EndPoint, is_heartbeat:bool) returns (ok:bool, packet:CPacket)
    requires this.role.Leader?
    requires Valid()
    requires ep in config.global_config.server_eps
    ensures ok ==> (
      && packet.msg.CMessage_AppendEntries?
      && packet.dst == ep
      && packet.src == this.config.server_ep == this.local_addr
      && CPacketIsSendable(packet)
      && CPacketIsAbstractable(packet)
      && this.nextActionIndex == old(this.nextActionIndex)
    )
  {
    ok := false;
    var next_index:uint64 := this.next_index[ep];
    var entries;
    if is_heartbeat {
      entries := [];
    } else {
      var log_index_end:uint64;
      if |this.log| < next_index as int + LogEntrySeqSizeLimit() {
        log_index_end := |this.log| as uint64;
      } else {
        log_index_end := next_index + LogEntrySeqSizeLimit() as uint64;
      }
      entries := this.log[next_index..log_index_end];
      assert |entries| <= LogEntrySeqSizeLimit();
    }
    var prev_log_index:uint64 := next_index - 1;
    assert prev_log_index >= 0;
    assert prev_log_index as int < |log|;
    var prev_log_term := log[prev_log_index].term;
    var leader_ep := this.config.server_ep;

    var last_log_entry := GetLastLogEntry();
    print "next_index=", next_index, ", last_log_entry.index=", last_log_entry.index, "\n";
    if next_index <= last_log_entry.index || is_heartbeat {
      ok := true;
      packet := CPacket(
        ep, 
        leader_ep, 
        CMessage_AppendEntries(
          this.current_term, leader_ep, prev_log_index, prev_log_term, entries, this.commit_index
        )
      );
    } else {
      ok := false;
    }
  }
}


method Server_CreateAppendEntriesForAll(server_impl:ServerImpl) returns (ok:bool, outbound_packets:seq<CPacket>)
  requires server_impl.Valid()
  requires server_impl.role.Leader?
  ensures server_impl.Valid()
  ensures server_impl.role.Leader?
  ensures |outbound_packets| <= |server_impl.config.global_config.server_eps|
  ensures (forall p :: p in outbound_packets ==> (
    CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.config.server_ep
  ))
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.nextActionIndex == old(server_impl.nextActionIndex)
  ensures server_impl.repr == old(server_impl.repr)
  ensures ok ==> (
    && OutboundPacketsIsValid(PacketSequence(outbound_packets))
  )
{
  outbound_packets := [];
  var i := 0;
  while i < |server_impl.config.global_config.server_eps|
    decreases |server_impl.config.global_config.server_eps| - i
    invariant server_impl.Valid()
    invariant 0 <= i <= |server_impl.config.global_config.server_eps|
    invariant server_impl.role.Leader?
    invariant |outbound_packets| <= i
    invariant |outbound_packets| <= |server_impl.config.global_config.server_eps|
    invariant (forall p :: p in outbound_packets ==> (
      CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.config.server_ep
    ))
    invariant server_impl.Env() == old(server_impl.Env())
    invariant server_impl.nextActionIndex == old(server_impl.nextActionIndex)
    invariant server_impl.repr == old(server_impl.repr)
  {
    var ep := server_impl.config.global_config.server_eps[i];
    if ep != server_impl.config.server_ep {
      var packet;
      ok, packet := server_impl.PrepareAppendEntriesPacket(ep, false);
      if (!ok) {
        break;
      }
      print "ready to send to ", i, " with AppendEntries(", |packet.msg.entries|, ")\n";
      assert CPacketIsSendable(packet);
      outbound_packets := outbound_packets + [packet];
    }
    i := i + 1;
    assert |outbound_packets| <= i;
  }
}

}