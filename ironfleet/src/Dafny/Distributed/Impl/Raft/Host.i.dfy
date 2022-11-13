include "CmdLineParser.i.dfy"
include "Config.i.dfy"
include "ServerImpl.i.dfy"
include "../../Common/Framework/Host.s.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"

module Host_i refines Host_s {
import opened RaftCmdLineParser_i
import opened Raft__ConfigState_i
import opened Collections__Sets_i
import opened Raft__ServerScheduler_i
import opened Raft__ServerImpl_i
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides HostState
    provides ConcreteConfiguration
    provides HostInit, HostNext, ConcreteConfigInit, HostStateInvariants
    provides ConcreteConfigToServers, ParseCommandLineConfiguration, ArbitraryObject
    provides HostInitImpl, HostNextImpl
export All reveals *

datatype CScheduler = CScheduler(ghost sched:RaftServerScheduler, server_impl:ServerImpl)

type HostState = CScheduler
type ConcreteConfiguration = ConfigState

predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
{
  id in config.server_eps
}
predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  && host_state' == host_state
  && |ios| == 0
}

predicate ConcreteConfigInit(config:ConcreteConfiguration)
{
  true
}

predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
{
  true
}

function ConcreteConfigToServers(config:ConcreteConfiguration) : set<EndPoint>
{
  MapSeqToSet(config.server_eps, x=>x)
}

function ParseCommandLineConfiguration(args:seq<seq<byte>>) : ConcreteConfiguration
{
  var server_eps := raft_config_parsing(args);
  var config := ConfigState(
    server_eps, // server_eps
    StaticParams()
  );
  config
}

method HostInitImpl(ghost env:HostEnvironment, netc:NetClient, args:seq<seq<byte>>) returns (
    ok:bool,
    host_state:HostState
)
{
  var my_index;
  var server_eps;
  var raft_sched:RaftServerScheduler;
  var server := new ServerImpl();
  host_state := CScheduler(raft_sched, server);

  var ep := EndPoint(netc.MyPublicKey());
  ok, server_eps, my_index := parse_cmd_line(ep, args);
  if !ok { return; }
  print "My ep is: ", ep, "\n";

  var server_config := InitServerConfigState(ep, server_eps);
  assert ep in server_config.global_config.server_eps;
  host_state := CScheduler(server.AbstractifyToRaftServerScheduler(), server);
}

method HostNextImpl(ghost env:HostEnvironment, host_state:HostState) 
  returns (
  ok:bool,
  host_state':HostState,
  ghost recvs:seq<NetEvent>,
  ghost clocks:seq<NetEvent>,
  ghost sends:seq<NetEvent>,
  ghost ios:seq<LIoOp<EndPoint, seq<byte>>>
)
{
  var raft_schedule:RaftServerScheduler;
  var server_impl:ServerImpl := new ServerImpl();
  host_state' := CScheduler(raft_schedule, server_impl);

  // var okay, netEventLog, abstract_ios := Server_Next_Main(host_state.server_impl);
}
}
