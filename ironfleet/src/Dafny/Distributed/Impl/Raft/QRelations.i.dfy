include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"

module Raft__QRelations_i {

import opened Raft__Types_i
import opened Raft__Server_i
import opened Raft__ServerScheduler_i


predicate {:opaque} Q_RaftServer_Next_ProcessPacket(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextProcessPacket(server, server', ios)
}

predicate {:opaque} Q_RaftScheduler_Next(sched:RaftServerScheduler, sched':RaftServerScheduler, ios:seq<RaftIo>)
{
  RaftServerSchedulerNext(sched, sched', ios)
}

predicate {:opaque} Q_RaftServer_NoReceive_Next(server:RaftServer, nextActionIndex:int, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNoReceiveNext(server, nextActionIndex, server', ios)
}

lemma lemma_EstablishQLSchedulerNext(server:RaftServer, server':RaftServer, ios:seq<RaftIo>, sched:RaftServerScheduler, sched':RaftServerScheduler)
  requires 0 <= sched.nextActionIndex < RaftServerNumActions()
  requires sched.nextActionIndex == 0 ==> Q_RaftServer_Next_ProcessPacket(server, server', ios)
  requires sched.nextActionIndex == 1 ==> Q_RaftServer_NoReceive_Next(server, sched.nextActionIndex, server', ios)
  requires sched.server == server
  requires sched'.server == server'
  requires sched'.nextActionIndex == (sched.nextActionIndex+1)%RaftServerNumActions()
  ensures Q_RaftScheduler_Next(sched, sched', ios)
{
  reveal Q_RaftServer_Next_ProcessPacket();
  reveal Q_RaftServer_NoReceive_Next();
  reveal Q_RaftScheduler_Next();
}

lemma lemma_EstablishQRaftServerNextProcessPacketFromTimeout(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
  requires |ios|==1
  requires ios[0].LIoOpTimeoutReceive?
  requires server==server'
  ensures Q_RaftServer_Next_ProcessPacket(server, server', ios)
{
  reveal Q_RaftServer_Next_ProcessPacket();
}

predicate {:opaque} Q_RaftServerScheduler_Next(s:RaftServerScheduler, s':RaftServerScheduler, ios:seq<RaftIo>)
{
  RaftServerSchedulerNext(s, s', ios)
}

}