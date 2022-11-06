include "Config.i.dfy"
include "Server.i.dfy"
include "Types.i.dfy"

module Raft__ServerScheduler_i {

import opened Raft__Config_i
import opened Raft__Server_i
import opened Raft__Types_i

datatype RaftServerScheduler = RaftServerScheduler(
  server:RaftServer,
  nextActionIndex:int
)

predicate RaftServerSchedulerInit(sch:RaftServerScheduler, c:RaftServerConfig) 
{
  && WellFormedLRaftServerConfig(c)
  && RaftServerInit(sch.server, c)
  && sch.nextActionIndex == 0
}

predicate RaftServerSchedulerNext(sch:RaftServerScheduler, sch':RaftServerScheduler, ios:seq<RaftIo>) 
{
  && sch'.nextActionIndex == (sch.nextActionIndex + 1) % RaftServerNumActions()
  && if sch.nextActionIndex == 0 then
      RaftServerNextProcessPacket(sch.server, sch'.server, ios)
    else
      RaftServerNoReceiveNext(sch.server, sch.nextActionIndex, sch'.server, ios)

}
}