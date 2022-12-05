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
include "NetRaft.i.dfy"
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
import opened Raft__NetRaft_i
import opened Raft__PacketParsing_i


datatype ServerImplState = ServerImplState(
  config:ServerConfigState,
  role:RaftRole,
  // for timeout
  next_heartbeat_time:uint64,
  next_election_time:uint64,
  // persistent state
  current_leader:Option<uint64>,
  current_term:uint64,
  voted_for:Option<uint64>,
  log:seq<CLogEntry>,
  // volatile state on all servers
  commit_index:uint64,
  last_applied:uint64,
  // volatile state on leaders
  next_index:map<EndPoint, uint64>,
  match_index:map<EndPoint, uint64>,
  num_replicated:seq<int>, // log index -> num of replicated
  vote_granted:map<EndPoint, uint64>, // server_id -> voted?(bool)

  random_generator:RandomGenerator,

  app_state:AppStateMachine
)

class ServerImpl
{
  var state:ServerImplState;
  var net_client:NetClient?;
  var local_addr:EndPoint;
  var nextActionIndex:uint64;

  var msg_grammar:G;

  ghost var repr : set<object>;

  constructor() {
    net_client := null;
    config := ServerConfigState();
    state := ServerImplState(
      
    )
    
  }

  predicate Valid()
    reads this
    reads this.body.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
  {
    && (0 <= nextActionIndex as int < RaftServerNumActions())
    && net_client != null
    && ServerConfigStateIsValid(body.config)
    && NetClientIsValid(net_client)
    && EndPoint(net_client.MyPublicKey()) == local_addr
    && EndPoint(net_client.MyPublicKey()) == config.server_ep
    && repr == { this } + NetClientRepr(net_client)
    && msg_grammar == CMessage_grammar()
    && (current_leader.None? || (current_leader.Some? && current_leader.v as int < |config.global_config.server_eps|))
    // term
    && current_term as int <= MaxLogEntryTerm()
    // log
    && 1 <= |log| <= ServerMaxLogSize() as int
    && log[0] == CLogEntry(0, 0, [], 0, 1, config.global_config.server_eps[0])
    && (forall i :: 0 <= i < |log| ==> ValidLogEntry(log[i]))
    // TODO: this may not be true when truncating
    && (forall i :: 0 <= i < |log| ==> log[i].index as int == i)
    && LogEntrySeqIndexIncreasing(log)
    // commit_index & last_applied
    && 0 <= last_applied <= commit_index
    // next_index and match_index
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
    // vote_granted
    && (
      role.Candidate? ==> (
        forall ep :: ep in this.config.global_config.server_eps ==> ep in this.vote_granted
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
      if current_leader.Some? then Some(current_leader.v as int) else None(),
      current_term as int,
      if voted_for.Some? then Some(voted_for.v as int) else None(),
      AbstractifyCLogEntrySeqToRaftLogEntrySeq(log),
      commit_index as int,
      last_applied as int,
      MapUint64MapValueToInt(next_index),
      MapUint64MapValueToInt(match_index),
      num_replicated,
      MapUint64MapValueToInt(vote_granted),
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

  method BecomeCandidate() returns ()
    requires this.Valid()
    modifies this
    ensures this.role == Candidate
    ensures this.Valid()
    ensures this.net_client == old(this.net_client)
    ensures this.nextActionIndex == old(this.nextActionIndex)
  {
    var i := 0;

    while i < |config.global_config.server_eps|
      invariant 0 <= i <= |config.global_config.server_eps|
      decreases |config.global_config.server_eps| - i
      invariant Valid()
      invariant forall j :: 0 <= j < i ==> config.global_config.server_eps[j] in vote_granted
      invariant this.net_client == old(this.net_client)
      invariant this.nextActionIndex == old(this.nextActionIndex)
    {
      var ep := config.global_config.server_eps[i];
      if ep == this.config.server_ep {
        this.vote_granted := this.vote_granted[ep := 1];
      } else {
        this.vote_granted := this.vote_granted[ep := 0];
      }
      i := i + 1;
    }
    this.role := Candidate;
  }

  method BecomeLeader() returns ()
    requires Valid()
    requires MaxLogEntryIndex() - LastLogEntryIndex() as int >= 1
    requires this.role == Candidate
    modifies this
    ensures this.role.Leader?
    ensures this.net_client == old(this.net_client)
    ensures Valid()
    ensures this.nextActionIndex == old(this.nextActionIndex);
  {
    var i := 0;
    var last_log_entry := GetLastLogEntry();
    assert log[|log| - 1].index == last_log_entry.index;
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
      invariant this.nextActionIndex == old(this.nextActionIndex)
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
    var my_id := GetEndPointIndex(this.config.global_config, this.config.server_ep);
    this.current_leader := Some(my_id);
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
    this.current_leader := Some(0);
    this.log := [CLogEntry(0, 0, [], 0, 1, config.global_config.server_eps[0])];
    this.role := Follower;
    var my_id := GetEndPointIndex(this.config.global_config, this.config.server_ep);
    this.random_generator := new RandomGenerator(my_id);
    // TODO: Remove this
    this.current_term := 1;
    this.last_applied := 0;
    this.commit_index := 0;
    assert LastLogEntryIndex() == 0;
    // if this.current_leader.Some? && this.config.server_id == this.current_leader.v {
    //   assert MaxLogEntryIndex() - LastLogEntryIndex() as int >= 1;
    //   this.BecomeCandidate();
    //   assert net_client.env == nc.env;
    //   this.BecomeLeader();
    //   assert net_client.env == nc.env;
    // } else{
    //   this.role := Follower;
    //   this.current_term := 0;
    // }
    this.role := Follower;
    this.current_term := 0;
    assert net_client.env == nc.env;
    ok := true;
    app_state := AppStateMachine.Initialize();
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

  method GetLogEntry(index: uint64) returns (log_entry:Option<CLogEntry>)
    requires Valid()
    ensures log_entry.Some? ==> (
      && 0 <= index < |log| as uint64
      && 0 <= index <= |log| as uint64 - 1
      && log_entry.v in log
      && log_entry.v == log[index]
    )
    ensures Valid()
  {
    if 0 <= index < |log| as uint64 {
      log_entry := Some(log[index]);
    } else {
      log_entry := None;
    }
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

  method CreateLogEntry(client_ep:EndPoint, seqno_req:uint64, req:CAppRequest) returns (ok:bool, entry:CLogEntry)
    requires EndPointIsValidPublicKey(client_ep)
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

    entry := CLogEntry(this.current_term, last_log_index + 1, req, seqno_req, /*is_commited*/0, client_ep);
    ok := true;
  }

  method TryToIncreaseCommitIndexUntil(index:uint64) returns (ok:bool)
    requires this.role == Leader
    requires Valid()
    modifies this
    ensures Valid()
    ensures this.repr == old(this.repr)
    ensures this.nextActionIndex == old(this.nextActionIndex)
  {
    if (this.commit_index >= MaxLogEntryIndex() as uint64 
      || index >= MaxLogEntryIndex() as uint64
      || index >= |log| as uint64)
    {
      ok := false;
      return;
    } else if (this.commit_index >= index) {
      // already commit, but still ok.
      ok := true;
      return;
    } else {
      ok := true;
    }
    var i:uint64 := this.commit_index + 1;
    assert index < |log| as uint64;
    while i - 1 < index
      invariant this.commit_index <= i - 1 <= index
      decreases index - (i - 1)
      invariant i <= index + 1
      invariant |log| <= ServerMaxLogSize()
      invariant index < |log| as uint64
      invariant Valid()
      invariant this.role == Leader
      invariant this.repr == old(this.repr)
      invariant this.nextActionIndex == old(this.nextActionIndex)
    {
      var count:uint64 := 0;
      for ep_id:uint64 := 0 to |this.config.global_config.server_eps| as uint64
        invariant Valid()
        invariant this.role == Leader
        invariant i <= index + 1
        invariant |log| <= ServerMaxLogSize()
        invariant index < |log| as uint64
        invariant count <= ep_id
        invariant this.repr == old(this.repr)
        invariant this.nextActionIndex == old(this.nextActionIndex)
      {
        var ep := this.config.global_config.server_eps[ep_id];
        assert forall ep :: ep in config.global_config.server_eps ==> ep in match_index;
        if this.match_index[ep] >= i {
          count := count + 1;
        }
      }
      assert 0 <= commit_index < |log| as uint64;
      if (count >= CRaftMinQuorumSize(this.config.global_config)) {
        this.commit_index := i;
      } else {
        break;
      }
      assert 0 <= commit_index == i <= index + 1 <= |log| as uint64;
      i := i + 1;
    }
  }

  method PrepareAppendEntriesPacket(ep:EndPoint, is_heartbeat:bool) returns (packet:CPacket)
    requires this.role.Leader?
    requires Valid()
    requires ep in config.global_config.server_eps
    ensures packet.msg.CMessage_AppendEntries?
    ensures packet.dst == ep
    ensures packet.src == this.config.server_ep == this.local_addr
    ensures CPacketIsSendable(packet)
    ensures CPacketIsAbstractable(packet)
    ensures this.nextActionIndex == old(this.nextActionIndex)
  {
    var next_index:uint64 := this.next_index[ep];
    var entries;
    // if is_heartbeat {
    //   entries := [];
    // } else {
    //   var log_index_end:uint64;
    //   if |this.log| < next_index as int + LogEntrySeqSizeLimit() {
    //     log_index_end := |this.log| as uint64;
    //   } else {
    //     log_index_end := next_index + LogEntrySeqSizeLimit() as uint64;
    //   }
    //   entries := this.log[next_index..log_index_end];
    //   assert |entries| <= LogEntrySeqSizeLimit();
    // }

    // also send entries even it's heartbeat
    var log_index_end:uint64;
    if |this.log| < next_index as int + LogEntrySeqSizeLimit() {
      log_index_end := |this.log| as uint64;
    } else {
      log_index_end := next_index + LogEntrySeqSizeLimit() as uint64;
    }
    entries := this.log[next_index..log_index_end];
    assert |entries| <= LogEntrySeqSizeLimit();

    var prev_log_index:uint64 := next_index - 1;
    assert prev_log_index >= 0;
    assert prev_log_index as int < |log|;
    var prev_log_term := log[prev_log_index].term;
    var leader_ep := this.config.server_ep;

    var last_log_entry := GetLastLogEntry();
    var ep_id := GetEndPointIndex(this.config.global_config, ep);
    print "To ", ep_id, ": next_index=", next_index, ",last_log_entry.index=", last_log_entry.index, "\n";
    packet := CPacket(
      ep, 
      leader_ep, 
      CMessage_AppendEntries(
        this.current_term, leader_ep, prev_log_index, prev_log_term, entries, this.commit_index
      )
    );
    assert CPacketIsSendable(packet);
  }

  method VoteRequestPassed() returns (passed:bool)
    requires this.role == Candidate
    requires Valid()
    ensures Valid()
  {
    var count:uint64 := 0;
    for ep_id:uint64 := 0 to |this.config.global_config.server_eps| as uint64
      invariant Valid()
      invariant count <= ep_id <= 0xFFFF_FFFF_FFFF_FFFF
    {
      var ep := this.config.global_config.server_eps[ep_id];
      print "ep_id=", ep_id, ": ", this.vote_granted[ep], "\n";
      if this.vote_granted[ep] == 1 {
        count := count + 1;
      }
    }
    print "count=", count, "\n";
    passed := count >= CRaftMinQuorumSize(this.config.global_config);
  }

  predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:NetEvent, io0:RaftIo)
    reads this
    requires ServerConfigStateIsValid(config)
  {
    && CPacketIsSendable(cpacket)
    && EndPointIsValidPublicKey(cpacket.src)
    && io0.LIoOpReceive?
    && NetEventIsAbstractable(netEvent0)
    && io0 == AbstractifyNetEventToRaftIo(netEvent0)
    && netEvent0.LIoOpReceive? && AbstractifyCPacketToRaftPacket(cpacket) == AbstractifyNetPacketToRaftPacket(netEvent0.r)
  }

} // end of class ServerImpl


method Server_CreateAppendEntriesForAll(server_impl:ServerImpl, is_heartbeat:bool) returns (outbound_packets:seq<CPacket>)
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
  ensures OutboundPacketsIsValid(PacketSequence(outbound_packets))
  ensures server_impl.next_heartbeat_time == old(server_impl.next_heartbeat_time)
  ensures forall packet :: packet in outbound_packets ==> packet.msg.CMessage_AppendEntries?
  ensures forall i_ :: 0 <= i_ < |server_impl.config.global_config.server_eps| && server_impl.config.global_config.server_eps[i_] != server_impl.config.server_ep ==> 
      (exists packet :: packet in outbound_packets && packet.dst == server_impl.config.global_config.server_eps[i_])
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
    invariant forall packet_ :: packet_ in outbound_packets ==> packet_.msg.CMessage_AppendEntries?
    invariant forall i_ :: 0 <= i_ < i && server_impl.config.global_config.server_eps[i_] != server_impl.config.server_ep ==> 
      (exists packet :: packet in outbound_packets && packet.dst == server_impl.config.global_config.server_eps[i_])
  {
    var ep := server_impl.config.global_config.server_eps[i];
    if ep != server_impl.config.server_ep {
      var packet;
      packet := server_impl.PrepareAppendEntriesPacket(ep, is_heartbeat);
      print "ready to send to ", i, " with AppendEntries(", |packet.msg.entries|, ")\n";
      assert CPacketIsSendable(packet);
      outbound_packets := outbound_packets + [packet];
    }
    i := i + 1;
    assert |outbound_packets| <= i;
  }
}

method Server_CreateRequestVoteForAll(server_impl:ServerImpl) returns (ok:bool, outbound_packets:seq<CPacket>)
  requires server_impl.Valid()
  requires server_impl.role.Candidate?
  ensures server_impl.Valid()
  ensures server_impl.role.Candidate?
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
  var my_last_log := server_impl.GetLastLogEntry();
  while i < |server_impl.config.global_config.server_eps|
    decreases |server_impl.config.global_config.server_eps| - i
    invariant server_impl.Valid()
    invariant 0 <= i <= |server_impl.config.global_config.server_eps|
    invariant server_impl.role.Candidate?
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
      var msg := CMessage_RequestVote(
        server_impl.current_term, server_impl.config.server_id, my_last_log.index, my_last_log.term
      );
      var packet := CPacket(
        ep, server_impl.config.server_ep, msg
      );
      print "ready to send to ", i, " with RequestVote(", ")\n";
      assert CPacketIsSendable(packet);
      outbound_packets := outbound_packets + [packet];
    }
    i := i + 1;
    assert |outbound_packets| <= i;
  }
  ok := true;
}

}