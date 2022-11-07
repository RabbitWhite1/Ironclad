include "CmdLineParser.i.dfy"
include "../../Common/Framework/Host.s.dfy"
include "../../Common/Collections/Sets.i.dfy"

module Host_i refines Host_s {
import opened SimplestCmdLineParser_i
import opened Collections__Sets_i
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides HostState
    provides ConcreteConfiguration
    provides HostInit, HostNext, ConcreteConfigInit, HostStateInvariants
    provides ConcreteConfigToServers, ParseCommandLineConfiguration, ArbitraryObject
    provides HostInitImpl, HostNextImpl
export All reveals *

type HostState = int
type ConcreteConfiguration = seq<EndPoint>

predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
{
  id in config
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
  MapSeqToSet(config, x=>x)
}

function ParseCommandLineConfiguration(args:seq<seq<byte>>) : ConcreteConfiguration
{
  simplest_config_parsing(args)
}

method HostInitImpl(ghost env:HostEnvironment, netc:NetClient, args:seq<seq<byte>>) returns (
    ok:bool,
    host_state:HostState
)
{
  var my_index;
  host_state := 0;

  var id := EndPoint(netc.MyPublicKey());
  print "My id is: ", id, "\n";
  var config;
  ok, config, my_index := parse_cmd_line(id, args);
  if !ok { return; }
  assert id in config;
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
  ok := true;
  host_state' := host_state;
  recvs := [];
  clocks := [];
  sends := [];
  ios := [];
}
}
