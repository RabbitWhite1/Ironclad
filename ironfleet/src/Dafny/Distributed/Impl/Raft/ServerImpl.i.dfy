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
include "Config.i.dfy"
include "PacketParsing.i.dfy"

module Raft__ServerImpl_i {

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
import opened Raft__ConfigState_i
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
  var log:seq<LogEntry>;
  // volatile state on all servers
  var commit_index:uint64;
  var last_applied:uint64;
  // volatile state on leaders
  var next_index:map<EndPoint, int>;
  var match_index:map<EndPoint, int>;
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
  }

  function AbstractifyToRaftServer() : RaftServer
    reads this
  {
    RaftServer(
      AbstractifyServerConfigStateToRaftServerConfig(config),
      role,
      next_heartbeat_time as int,
      next_election_time as int,
      current_leader,
      current_term as int,
      voted_for,
      log,
      commit_index as int,
      last_applied as int,
      next_index,
      match_index,
      num_replicated,
      app_state.Abstractify()
    )
  }

  function AbstractifyToRaftServerScheduler() : RaftServerScheduler
    reads this
  {
    RaftServerScheduler(
      this.AbstractifyToRaftServer(),
      this.nextActionIndex as int
    )
  }

  method Init(
    config:ServerConfigState,
    nc:NetClient,
    ghost env:HostEnvironment
  ) returns (ok:bool)
    requires env.Valid() && env.ok.ok()
    requires NetClientIsValid(nc)
    requires ServerConfigStateIsValid(config)
    requires EndPoint(nc.MyPublicKey()) == config.server_ep
    requires WellFormedRaftServerConfig(AbstractifyServerConfigStateToRaftServerConfig(config))
    modifies this
    ensures Valid()
    ensures Env() == nc.env
  {
    this.config := config;
    this.net_client := nc;
    this.nextActionIndex := 0;
    this.local_addr := EndPoint(net_client.MyPublicKey());
    this.msg_grammar := CMessage_grammar();
    this.repr := { this } + NetClientRepr(net_client);
    this.current_leader := Some(this.config.global_config.server_eps[0]);
    if this.current_leader.Some? && this.config.server_ep == this.current_leader.v {
      this.role := Leader;
    } else{
      this.role := Follower;
    }
    ok := true;
  }

  function Env() : HostEnvironment
    requires net_client != null
    reads this, NetClientIsValid.reads(net_client)
  {
    net_client.env
  }
}
}