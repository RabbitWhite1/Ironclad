/////////////////////////////////////////////////////////////////////////////
//
// This file defines prortocol of Raft
//
/////////////////////////////////////////////////////////////////////////////
include "../../Common/Native/Io.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "Config.i.dfy"
include "Server.i.dfy"
include "ServerScheduler.i.dfy"
include "Types.i.dfy"

module Raft__DistributedSystem_i {

import opened Environment_s
import opened Native__Io_s
import opened Raft__Config_i
import opened Raft__Server_i
import opened Raft__ServerScheduler_i
import opened Raft__Types_i


datatype RaftState = RaftState(
  config: RaftConfig,
  environment:LEnvironment<EndPoint, RaftMessage>,
  serverSchedulers:seq<RaftServerScheduler>
)

// Protocol-level init
predicate RaftInit(s:RaftState, c:RaftConfig)
{
  && s.config == c
  && WellFormedRaftConfig(c)
  && LEnvironment_Init(s.environment)
  && |s.serverSchedulers| == |c.server_eps|
  && (forall i :: 0 <= i < |s.serverSchedulers| ==>
      var sch := s.serverSchedulers[i];
      RaftServerScheduler_Init(sch, RaftServerConfig(sch.server.config.server_ep, i, c)))
}

// Protocol-level next
// Here a next step can be:
//  1. A host performing ios
//    1.1. RaftNextServer
//    1.2. RaftNextClient
//  2. The environment
//    2.1. deliver a packet
//    2.2. time advancing
//    2.3. do nothing
// And `RaftNextCommon` is commonly used by all circumstances
predicate RaftNextCommon(s:RaftState, s':RaftState)
{
  && |s.serverSchedulers| == |s.config.server_eps|
  && s.serverSchedulers == s'.serverSchedulers
  && s.config == s'.config
  && LEnvironment_Next(s.environment, s'.environment)
}

predicate RaftNextServer(s:RaftState, s':RaftState, idx:int, ios:seq<RaftIo>)
{
  && RaftNextCommon(s, s')
  && 0 <= idx < |s.serverSchedulers|
  && s.environment.nextStep == LEnvStepHostIos(s.config.server_eps[idx], ios)
  && s'.serverSchedulers == s.serverSchedulers[idx := s'.serverSchedulers[idx]]
  && RaftServerSchedulerNext(s.serverSchedulers[idx], s'.serverSchedulers[idx], ios)
}

predicate RaftNextClient(s:RaftState, s':RaftState, ep:EndPoint, ios:seq<RaftIo>)
{
  && RaftNextCommon(s, s')
  && s.environment.nextStep.LEnvStepHostIos?
}

predicate RaftNextEnvironment(s:RaftState, s':RaftState)
{
  // servers and config remain unchanged
  && RaftNextCommon(s, s')
  // only environment may change
  && !s.environment.nextStep.LEnvStepHostIos?
}

predicate RaftNext(s:RaftState, s':RaftState)
{
  || (exists idx, ios :: RaftNextServer(s, s', idx, ios))
  || (exists ep, ios :: RaftNextClient(s, s', ep, ios))
  || RaftNextEnvironment(s, s')
}





}