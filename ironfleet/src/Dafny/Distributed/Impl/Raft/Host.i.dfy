include "../../Common/Framework/Host.s.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/Raft/Config.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"
include "CmdLineParser.i.dfy"
include "Config.i.dfy"
include "QRelations.i.dfy"
include "ServerImpl.i.dfy"
include "ServerImplMain.i.dfy"

module Host_i refines Host_s {
import opened RaftCmdLineParser_i
import opened Raft__ConfigState_i
import opened Collections__Sets_i
import opened Raft__Config_i
import opened Raft__Types_i
import opened Raft__NetRaft_i
import opened Raft__QRelations_i
import opened Raft__ServerScheduler_i
import opened Raft__ServerImpl_i
import opened Raft__ServerImplMain_i
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
  true
}

predicate ConcreteConfigInit(config:ConcreteConfiguration)
{
  true
}

predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
{
  && host_state.server_impl.Valid() 
  && host_state.server_impl.Env() == env
  && host_state.sched == host_state.server_impl.AbstractifyToRaftServerScheduler()
  // true
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
  assert ep == server_eps[my_index];
  print "My ep is: ", ep, "\n";
  
  var server_config := InitServerConfigState(ep, server_eps);
  assert ep in server_config.global_config.server_eps;
  assert env.Valid() && env.ok.ok();
  assert ServerConfigStateIsValid(server_config);
  assert WellFormedRaftServerConfig(AbstractifyServerConfigStateToRaftServerConfig(server_config));

  ok := server.Init(server_config, netc, env);
  if !ok { return; }
  print "Server initialized\n";
  host_state := CScheduler(server.AbstractifyToRaftServerScheduler(), server);
}

predicate NetEventsReductionCompatible(events:seq<NetEvent>)
{
  forall i :: 0 <= i < |events| - 1 ==> events[i].LIoOpReceive? || events[i+1].LIoOpSend?
}

predicate EventsConsistent(recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>) 
{
  forall e :: && (e in recvs  ==> e.LIoOpReceive?) 
        && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
        && (e in sends  ==> e.LIoOpSend?)
}

ghost method RemoveRecvs(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, rest:seq<NetEvent>) 
  ensures forall e :: e in recvs ==> e.LIoOpReceive?
  ensures events == recvs + rest
  ensures rest != [] ==> !rest[0].LIoOpReceive?
  ensures NetEventsReductionCompatible(events) ==> NetEventsReductionCompatible(rest);
{
  recvs := [];
  rest := [];

  var i := 0;
  while i < |events| 
    invariant 0 <= i <= |events|
    invariant forall e :: e in recvs ==> e.LIoOpReceive?
    //invariant events == recvs + events[i..]
    invariant recvs == events[0..i]
  {
    if !events[i].LIoOpReceive? {
      rest := events[i..];
      return;
    }
    recvs := recvs + [events[i]];
    i := i + 1;
  }
}

lemma lemma_RemainingEventsAreSends(events:seq<NetEvent>)
  requires NetEventsReductionCompatible(events)
  requires |events| > 0
  requires !events[0].LIoOpReceive?
  ensures  forall e :: e in events[1..] ==> e.LIoOpSend?
{
  if |events| == 1 {
  } else {
    assert events[1].LIoOpSend?;
    lemma_RemainingEventsAreSends(events[1..]);
  }
}

ghost method PartitionEvents(events:seq<NetEvent>) returns (recvs:seq<NetEvent>, clocks:seq<NetEvent>, sends:seq<NetEvent>)
  requires NetEventsReductionCompatible(events)
  ensures  events == recvs + clocks + sends
  ensures  EventsConsistent(recvs, clocks, sends)
  ensures  |clocks| <= 1
{
  var rest;
  recvs, rest := RemoveRecvs(events);
  assert NetEventsReductionCompatible(rest);
  if |rest| > 0 && (rest[0].LIoOpReadClock? || rest[0].LIoOpTimeoutReceive?) {
    clocks := [rest[0]];
    sends := rest[1..];
    lemma_RemainingEventsAreSends(rest);
  } else {
    clocks := [];
    sends := rest;
    if |rest| > 0 {
      lemma_RemainingEventsAreSends(rest);
    }
  }
}

lemma lemma_ProtocolIosRespectReduction(s:RaftServerScheduler, s':RaftServerScheduler, ios:seq<RaftIo>)
  requires Q_RaftServerScheduler_Next(s, s', ios)
  ensures  LIoOpSeqCompatibleWithReduction(ios)
{
  reveal Q_RaftServerScheduler_Next();
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

  var okay, netEventLog, abstract_ios := Server_Next_main(host_state.server_impl);
  if okay {
    host_state' := CScheduler(host_state.server_impl.AbstractifyToRaftServerScheduler(), host_state.server_impl);
    calc { 
      Q_RaftServerScheduler_Next(host_state.sched, host_state.server_impl.AbstractifyToRaftServerScheduler(), abstract_ios);
        { reveal Q_RaftServerScheduler_Next(); }
      RaftServerSchedulerNext(host_state.sched, host_state.server_impl.AbstractifyToRaftServerScheduler(), abstract_ios);
    }

    assert AbstractifyRawLogToIos(netEventLog) == abstract_ios;
    if RaftServerSchedulerNext(host_state.sched, host_state.server_impl.AbstractifyToRaftServerScheduler(), abstract_ios)
    {
      lemma_ProtocolIosRespectReduction(host_state.sched, host_state.server_impl.AbstractifyToRaftServerScheduler(), abstract_ios);
    }
    recvs, clocks, sends := PartitionEvents(netEventLog);
    ios := recvs + clocks + sends; //abstract_ios;
    assert ios == netEventLog;
  } else {
    recvs := [];
    clocks := [];
    sends := [];
    ios := [];
  }
  ok := okay;
  reveal Q_RaftServerScheduler_Next();
  assert host_state.server_impl.Env() == env;
}
}
