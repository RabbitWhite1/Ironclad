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
  state.role:RaftRole,
  // for timeout
  next_heartbeat_time:uint64,
  next_election_time:uint64,
  // persistent state
  current_leader:Option<uint64>,
  current_term:uint64,
  voted_for:Option<uint64>,
  state.log:seq<CLogEntry>,
  // volatile state on all servers
  commit_index:uint64,
  last_applied:uint64,
  // volatile state on leaders
  next_index:map<EndPoint, uint64>,
  match_index:map<EndPoint, uint64>,
  num_replicated:seq<int>, // state.log index -> num of replicated
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
    var random_generator := new RandomGenerator(0);
    var appstate := AppStateMachine.Initialize();
    this.state := ServerImplState(
      /*config=*/ServerConfigState(0, ConfigState([], StaticParams())),
      /*state.role=*/Follower,
      /*next_heartbeat_time*/0,
      /*next_election_time*/0,
      /*current_leader=*/None,
      /*current_term=*/1,
      /*voted_for=*/None,
      /*state.log=*/[],
      /*commit_index=*/0,
      /*last_applied=*/0,
      /*next_index=*/map [],
      /*match_index=*/map [],
      /*num_replicated=*/[],
      /*vote_granted=*/map [],
      /*random_generator=*/random_generator,
      /*app_state=*/appstate
    );
    net_client := null;
    local_addr := EndPoint([]);
    nextActionIndex := 0;
  }

  predicate Valid()
    reads this
    reads this.state.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
  {
    && (0 <= nextActionIndex as int < RaftServerNumActions())
    && net_client != null
    && ServerConfigStateIsValid(state.config)
    && NetClientIsValid(net_client)
    && EndPoint(net_client.MyPublicKey()) == local_addr == GetMyEp()
    && repr == { this } + NetClientRepr(net_client)
    && msg_grammar == CMessage_grammar()
    && (state.current_leader.None? || (state.current_leader.Some? && state.current_leader.v as int < |state.config.global_config.server_eps|))
    // term
    && state.current_term as int <= MaxLogEntryTerm()
    // state.log
    && 1 <= |state.log| <= ServerMaxLogSize() as int
    && state.log[0] == CLogEntry(0, 0, [], 0, 1, state.config.global_config.server_eps[0])
    && (forall i :: 0 <= i < |state.log| ==> ValidLogEntry(state.log[i]))
    // TODO: this may not be true when truncating
    && (forall i :: 0 <= i < |state.log| ==> state.log[i].index as int == i)
    && LogEntrySeqIndexIncreasing(state.log)
    // commit_index & last_applied
    && 0 <= state.last_applied <= state.commit_index
    // next_index and match_index
    && (
      state.role.Leader? ==> (
        forall ep :: ep in state.config.global_config.server_eps ==> (
          && ep in state.next_index 
          && ep in state.match_index 
          && 1 <= state.next_index[ep] <= |state.log| as uint64
          && 0 <= state.match_index[ep] < state.next_index[ep]
        )
      )
    )
    // vote_granted
    && (
      state.role.Candidate? ==> (
        forall ep :: ep in this.state.config.global_config.server_eps ==> ep in this.state.vote_granted
      )
    )
    && |state.config.global_config.server_eps| >= 1
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
    reads this.state.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
    requires Valid()
    ensures Valid()
  {
    RaftServer(
      AbstractifyServerConfigStateToRaftServerConfig(state.config),
      state.role,
      state.next_heartbeat_time as int,
      state.next_election_time as int,
      if state.current_leader.Some? then Some(state.current_leader.v as int) else None(),
      state.current_term as int,
      if state.voted_for.Some? then Some(state.voted_for.v as int) else None(),
      AbstractifyCLogEntrySeqToRaftLogEntrySeq(state.log),
      state.commit_index as int,
      state.last_applied as int,
      MapUint64MapValueToInt(state.next_index),
      MapUint64MapValueToInt(state.match_index),
      state.num_replicated,
      MapUint64MapValueToInt(state.vote_granted),
      state.app_state.Abstractify()
    )
  }

  function AbstractifyToRaftServerScheduler() : RaftServerScheduler
    requires Valid()
    reads this
    reads this.state.app_state
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
    ensures this.state.role == Candidate
    ensures this.Valid()
    ensures this.state == old(this.state).(role := Candidate, vote_granted := this.state.vote_granted)
    ensures this.net_client == old(this.net_client)
    ensures this.nextActionIndex == old(this.nextActionIndex)
  {
    var i:uint64 := 0;
    var num_eps:uint64 := |state.config.global_config.server_eps| as uint64;

    while i < num_eps
      invariant 0 <= i <= num_eps
      invariant num_eps as int == |state.config.global_config.server_eps|
      decreases num_eps - i
      invariant Valid()
      invariant forall j :: 0 <= j < i ==> state.config.global_config.server_eps[j] in state.vote_granted
      invariant this.net_client == old(this.net_client)
      invariant this.nextActionIndex == old(this.nextActionIndex)
      invariant this.state == old(this.state).(vote_granted := this.state.vote_granted)
    {
      var ep := state.config.global_config.server_eps[i];
      if i == this.state.config.server_id {
        this.state := this.state.(vote_granted := this.state.vote_granted[ep := 1]);
      } else {
        this.state := this.state.(vote_granted := this.state.vote_granted[ep := 0]);
      }
      i := i + 1;
    }
    this.state := this.state.(role := Candidate);
  }

  method BecomeLeader() returns ()
    requires Valid()
    requires MaxLogEntryIndex() - LastLogEntryIndex() as int >= 1
    requires this.state.role == Candidate
    modifies this
    ensures this.state.role.Leader?
    ensures this.net_client == old(this.net_client)
    ensures Valid()
    ensures this.nextActionIndex == old(this.nextActionIndex);
  {
    var i := 0;
    var last_log_entry := GetLastLogEntry();
    assert state.log[|state.log| - 1].index == last_log_entry.index;
    while i < |state.config.global_config.server_eps|
      invariant 0 <= i <= |state.config.global_config.server_eps|
      decreases |state.config.global_config.server_eps| - i
      invariant !state.role.Leader?
      invariant 1 <= |state.log| <= ServerMaxLogSize() as int
      invariant state.log[|state.log| - 1] == old(state.log)[|old(state.log)| - 1]
      invariant state.log[|state.log| - 1].index == old(state.log)[|old(state.log)| - 1].index
      invariant forall i_ :: 0 <= i_ < i ==> (
        var ep_ := state.config.global_config.server_eps[i_]; 
        && ep_ in state.next_index 
        && ep_ in state.match_index
        && 1 <= state.next_index[ep_] <= |state.log| as uint64
        && 0 <= state.match_index[ep_] < state.next_index[ep_]
      )
      invariant Valid()
      invariant state.log == old(state.log)
      invariant this.net_client == old(this.net_client)
      invariant this.nextActionIndex == old(this.nextActionIndex)
    {
      var ep := state.config.global_config.server_eps[i];
      state := state.(next_index := state.next_index[ep := last_log_entry.index + 1]);
      assert last_log_entry.index >= 0;
      assert state.next_index[ep] >= 1;
      if ep != local_addr {
        state := state.(match_index := state.match_index[ep := 0]);
      } else {
        state := state.(match_index := state.match_index[ep := last_log_entry.index]);
      }
      i := i + 1;
    }
    state := state.(role := Leader);
    state := state.(current_leader := Some(this.state.config.server_id));
    assert forall ep :: ep in state.config.global_config.server_eps ==> ep in state.next_index && ep in state.match_index;
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
    requires EndPoint(nc.MyPublicKey()) == config.global_config.server_eps[config.server_id]
    requires WellFormedRaftServerConfig(AbstractifyServerConfigStateToRaftServerConfig(config))
    modifies this
    ensures ok ==> (
      && Valid()
      && Env() == nc.env
    )
  {
    var my_id := config.server_id;
    var random_generator := new RandomGenerator(my_id);
    var appstate := AppStateMachine.Initialize();
    this.state := ServerImplState(
      /*config=*/config,
      /*state.role=*/Follower,
      /*next_heartbeat_time*/0,
      /*next_election_time*/0,
      /*current_leader=*/None,
      /*current_term=*/1,
      /*voted_for=*/None,
      /*state.log=*/[CLogEntry(0, 0, [], 0, 1, config.global_config.server_eps[0])],
      /*commit_index=*/0,
      /*last_applied=*/0,
      /*next_index=*/map [],
      /*match_index=*/map [],
      /*num_replicated=*/[],
      /*vote_granted=*/map [],
      /*random_generator=*/random_generator,
      /*app_state=*/appstate
    );
    this.net_client := nc;
    this.nextActionIndex := 0;
    this.local_addr := EndPoint(net_client.MyPublicKey());
    this.msg_grammar := CMessage_grammar();
    this.repr := { this } + NetClientRepr(net_client);
    assert LastLogEntryIndex() == 0;
    assert net_client.env == nc.env;
    ok := true;
  }

  function Env() : HostEnvironment
    requires net_client != null
    reads this, NetClientIsValid.reads(net_client)
  {
    net_client.env
  }

  function method GetMyIndex() : uint64
    reads this
    requires ServerConfigStateIsValid(state.config)
    ensures 0 <= GetMyIndex() as int < |state.config.global_config.server_eps|
    ensures state.config.server_id == GetMyIndex()
  {
    state.config.server_id
  }

  function method GetMyEp() : EndPoint
    reads this
    requires ServerConfigStateIsValid(state.config)
    ensures GetMyEp() in state.config.global_config.server_eps
    ensures GetMyEp() == state.config.global_config.server_eps[state.config.server_id]
  {
    state.config.global_config.server_eps[state.config.server_id]
  }

  function method LastLogEntryIndex() : uint64
    requires Valid()
    reads this
    reads this.state.app_state
    reads if net_client != null then NetClientIsValid.reads(net_client) else {}
    requires 1 <= |state.log| <= ServerMaxLogSize()
    ensures LastLogEntryIndex() as int <= MaxLogEntryIndex()
    // TODO: this may not be true when truncating
    ensures LastLogEntryIndex() as int == |state.log| - 1
  {
    state.log[|state.log| - 1].index
  }

  method GetLogEntry(index: uint64) returns (log_entry:Option<CLogEntry>)
    requires Valid()
    ensures 0 <= index <= state.log[|state.log|-1].index ==> log_entry.Some?
    ensures log_entry.Some? ==> (
      && 0 <= index < |state.log| as uint64
      && 0 <= index <= |state.log| as uint64 - 1
      && log_entry.v in state.log
      && log_entry.v == state.log[index]
    )
    ensures Valid()
  {
    if 0 <= index < |state.log| as uint64 {
      log_entry := Some(state.log[index]);
    } else {
      log_entry := None;
    }
  }

  method GetLastLogEntry() returns(log_entry:CLogEntry)
    requires Valid()
    requires |state.log| - 1 >= 0
    ensures log_entry in state.log
    ensures log_entry == state.log[|state.log| - 1]
    ensures Valid();
  {
    assert |state.log| - 1 >= 0;
    log_entry := state.log[|state.log| - 1];
  }

  method AddLogEntries(entries:seq<CLogEntry>) returns()
    requires Valid()
    requires forall entry :: entry in entries ==> ValidLogEntry(entry)
    requires |entries| <= ServerMaxLogSize() - |this.state.log|
    requires LogEntrySeqIndexIncreasing(entries)
    requires |entries| > 0 ==> (LastLogEntryIndex() + 1 == entries[0].index == |state.log| as uint64)
    requires (forall i :: 0 <= i < |entries| ==> entries[i].index as int == i+|state.log|)
    modifies this
    ensures Valid()
    ensures this.state.role == old(this.state.role)
    ensures state.log == old(state.log) + entries
    ensures this.Env() == old(this.Env())
    ensures this.nextActionIndex == old(this.nextActionIndex)
    ensures this.repr == old(this.repr)
  {
    state := state.(log := state.log + entries);
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

    entry := CLogEntry(this.state.current_term, last_log_index + 1, req, seqno_req, /*is_commited*/0, client_ep);
    ok := true;
  }

  method TryToIncreaseCommitIndexUntil(index:uint64) returns (ok:bool)
    requires this.state.role == Leader
    requires Valid()
    modifies this
    ensures Valid()
    ensures this.repr == old(this.repr)
    ensures this.nextActionIndex == old(this.nextActionIndex)
  {
    if (this.state.commit_index >= MaxLogEntryIndex() as uint64 
      || index >= MaxLogEntryIndex() as uint64
      || index >= |state.log| as uint64)
    {
      ok := false;
      return;
    } else if (this.state.commit_index >= index) {
      // already commit, but still ok.
      ok := true;
      return;
    } else {
      ok := true;
    }
    var i:uint64 := this.state.commit_index + 1;
    assert index < |state.log| as uint64;
    while i - 1 < index
      invariant this.state.commit_index <= i - 1 <= index
      decreases index - (i - 1)
      invariant i <= index + 1
      invariant |state.log| <= ServerMaxLogSize()
      invariant index < |state.log| as uint64
      invariant Valid()
      invariant this.state.role == Leader
      invariant this.repr == old(this.repr)
      invariant this.nextActionIndex == old(this.nextActionIndex)
    {
      var count:uint64 := 0;
      for ep_id:uint64 := 0 to |this.state.config.global_config.server_eps| as uint64
        invariant Valid()
        invariant this.state.role == Leader
        invariant i <= index + 1
        invariant |state.log| <= ServerMaxLogSize()
        invariant index < |state.log| as uint64
        invariant count <= ep_id
        invariant this.repr == old(this.repr)
        invariant this.nextActionIndex == old(this.nextActionIndex)
      {
        var ep := this.state.config.global_config.server_eps[ep_id];
        assert forall ep :: ep in state.config.global_config.server_eps ==> ep in state.match_index;
        if this.state.match_index[ep] >= i {
          count := count + 1;
        }
      }
      assert 0 <= state.commit_index < |state.log| as uint64;
      if (count >= CRaftMinQuorumSize(this.state.config.global_config)) {
        state := state.(commit_index := i);
      } else {
        break;
      }
      assert 0 <= state.commit_index == i <= index + 1 <= |state.log| as uint64;
      i := i + 1;
    }
  }

  method PrepareAppendEntriesPacket(ep_id:uint64, is_heartbeat:bool) returns (packet:CPacket)
    requires this.state.role.Leader?
    requires Valid()
    requires 0 <= ep_id as int < |state.config.global_config.server_eps|
    ensures packet.msg.CMessage_AppendEntries?
    ensures packet.dst == state.config.global_config.server_eps[ep_id]
    ensures packet.src == GetMyEp() == this.local_addr == state.config.global_config.server_eps[GetMyIndex()]
    ensures CPacketIsSendable(packet)
    ensures CPacketIsAbstractable(packet)
    ensures this.nextActionIndex == old(this.nextActionIndex)
    ensures Valid()
  {
    var ep := state.config.global_config.server_eps[ep_id];
    var next_index:uint64 := this.state.next_index[ep];
    var entries;
    // if is_heartbeat {
    //   entries := [];
    // } else {
    //   var log_index_end:uint64;
    //   if |this.state.log| < next_index as int + LogEntrySeqSizeLimit() {
    //     log_index_end := |this.state.log| as uint64;
    //   } else {
    //     log_index_end := next_index + LogEntrySeqSizeLimit() as uint64;
    //   }
    //   entries := this.state.log[next_index..log_index_end];
    //   assert |entries| <= LogEntrySeqSizeLimit();
    // }

    // also send entries even it's heartbeat
    var log_index_end:uint64;
    if |this.state.log| < next_index as int + LogEntrySeqSizeLimit() {
      log_index_end := |this.state.log| as uint64;
    } else {
      log_index_end := next_index + LogEntrySeqSizeLimit() as uint64;
    }
    entries := this.state.log[next_index..log_index_end];
    assert |entries| <= LogEntrySeqSizeLimit();

    var prev_log_index:uint64 := next_index - 1;
    assert prev_log_index >= 0;
    assert prev_log_index as int < |state.log|;
    var prev_log_term := state.log[prev_log_index].term;
    var leader_ep := GetMyEp();

    var last_log_entry := GetLastLogEntry();
    var ep_id := GetEndPointIndex(this.state.config.global_config, ep);
    print "To ", ep_id, ": next_index=", next_index, ",last_log_entry.index=", last_log_entry.index, "\n";
    packet := CPacket(
      ep, 
      leader_ep, 
      CMessage_AppendEntries(
        state.current_term, leader_ep, prev_log_index, prev_log_term, entries, state.commit_index
      )
    );
    assert CPacketIsSendable(packet);
  }

  method VoteRequestPassed() returns (passed:bool)
    requires this.state.role == Candidate
    requires Valid()
    ensures Valid()
  {
    var count:uint64 := 0;
    for ep_id:uint64 := 0 to |this.state.config.global_config.server_eps| as uint64
      invariant Valid()
      invariant count <= ep_id <= 0xFFFF_FFFF_FFFF_FFFF
    {
      var ep := this.state.config.global_config.server_eps[ep_id];
      print "ep_id=", ep_id, ": ", this.state.vote_granted[ep], "\n";
      if this.state.vote_granted[ep] == 1 {
        count := count + 1;
      }
    }
    print "count=", count, "\n";
    passed := count >= CRaftMinQuorumSize(this.state.config.global_config);
  }

  predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:NetEvent, io0:RaftIo)
    reads this
    requires ServerConfigStateIsValid(state.config)
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
  requires server_impl.state.role.Leader?
  ensures server_impl.Valid()
  ensures server_impl.state.role.Leader?
  ensures |outbound_packets| <= |server_impl.state.config.global_config.server_eps|
  ensures (forall p :: p in outbound_packets ==> (
    CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.GetMyEp()
  ))
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.nextActionIndex == old(server_impl.nextActionIndex)
  ensures server_impl.repr == old(server_impl.repr)
  ensures OutboundPacketsIsValid(PacketSequence(outbound_packets))
  ensures server_impl.state.next_heartbeat_time == old(server_impl.state.next_heartbeat_time)
  ensures forall packet :: packet in outbound_packets ==> packet.msg.CMessage_AppendEntries?
  ensures forall i_ :: 0 <= i_ < |server_impl.state.config.global_config.server_eps| as uint64 && i_ != server_impl.GetMyIndex() ==> 
      (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_]);
{
  outbound_packets := [];
  var i:uint64 := 0;
  assert |server_impl.state.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
  while i < |server_impl.state.config.global_config.server_eps| as uint64
    decreases |server_impl.state.config.global_config.server_eps| - i as int
    invariant server_impl.Valid()
    invariant 0 <= i as int <= |server_impl.state.config.global_config.server_eps|
    invariant server_impl.state.role.Leader?
    invariant |outbound_packets| <= i as int
    invariant |outbound_packets| <= |server_impl.state.config.global_config.server_eps|
    invariant (forall p :: p in outbound_packets ==> (
      CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.GetMyEp()
    ))
    invariant server_impl.Env() == old(server_impl.Env())
    invariant server_impl.nextActionIndex == old(server_impl.nextActionIndex)
    invariant server_impl.repr == old(server_impl.repr)
    invariant forall packet_ :: packet_ in outbound_packets ==> packet_.msg.CMessage_AppendEntries?
    invariant forall i_ :: 0 <= i_ < i && i_ != server_impl.GetMyIndex() ==> 
      (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_])
  {
    if i != server_impl.GetMyIndex() {
      var packet;
      packet := server_impl.PrepareAppendEntriesPacket(i, is_heartbeat);
      print "ready to send to ", i, " with AppendEntries(", |packet.msg.entries|, ")\n";
      assert CPacketIsSendable(packet);
      outbound_packets := outbound_packets + [packet];
    }
    i := i + 1;
  }
  assert forall i_ :: 0 <= i_ < |server_impl.state.config.global_config.server_eps| as uint64 && i_ != server_impl.GetMyIndex() ==> 
      (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_]);
}

method Server_CreateRequestVoteForAll(server_impl:ServerImpl) returns (outbound_packets:seq<CPacket>)
  requires server_impl.Valid()
  requires server_impl.state.role.Candidate?
  ensures server_impl.Valid()
  ensures server_impl.state.role.Candidate?
  ensures |outbound_packets| <= |server_impl.state.config.global_config.server_eps|
  ensures (forall p :: p in outbound_packets ==> (
    CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.GetMyEp()
  ))
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.nextActionIndex == old(server_impl.nextActionIndex)
  ensures server_impl.repr == old(server_impl.repr)
  ensures OutboundPacketsIsValid(PacketSequence(outbound_packets))
  ensures forall packet :: packet in outbound_packets ==> packet.msg.CMessage_RequestVote? 
  ensures forall i_ :: 0 <= i_ < |server_impl.state.config.global_config.server_eps| as uint64 && i_ != server_impl.GetMyIndex() ==> 
            (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_])
{
  outbound_packets := [];
  var i:uint64 := 0;
  assert |server_impl.state.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
  var my_last_log := server_impl.GetLastLogEntry();
  while i < |server_impl.state.config.global_config.server_eps| as uint64
    decreases |server_impl.state.config.global_config.server_eps| - i as int
    invariant server_impl.Valid()
    invariant 0 <= i as int<= |server_impl.state.config.global_config.server_eps|
    invariant server_impl.state.role.Candidate?
    invariant |outbound_packets| <= i as int
    invariant |outbound_packets| <= |server_impl.state.config.global_config.server_eps|
    invariant (forall p :: p in outbound_packets ==> (
      CPacketIsSendable(p) && CPacketIsAbstractable(p) && p.src == server_impl.GetMyEp()
    ))
    invariant server_impl.Env() == old(server_impl.Env())
    invariant server_impl.nextActionIndex == old(server_impl.nextActionIndex)
    invariant server_impl.repr == old(server_impl.repr)
    invariant forall packet :: packet in outbound_packets ==> packet.msg.CMessage_RequestVote? 
    invariant forall i_ :: 0 <= i_ < i as uint64 && i_ != server_impl.GetMyIndex() ==> 
        (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_]);
  {
    if i != server_impl.GetMyIndex() {
      var ep := server_impl.state.config.global_config.server_eps[i];
      var msg := CMessage_RequestVote(
        server_impl.state.current_term, server_impl.GetMyIndex(), my_last_log.index, my_last_log.term
      );
      var packet := CPacket(ep, server_impl.GetMyEp(), msg);
      print "ready to send to ", i, " with RequestVote(", ")\n";
      assert CPacketIsSendable(packet);
      outbound_packets := outbound_packets + [packet];
    }
    i := i + 1;
  }
  assert forall i_ :: 0 <= i_ < |server_impl.state.config.global_config.server_eps| as uint64 && i_ != server_impl.GetMyIndex() ==> 
          (exists packet :: packet in outbound_packets && packet.dst == server_impl.state.config.global_config.server_eps[i_]);
}

}