include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"

module Raft__QRelations_i {

import opened Raft__Types_i
import opened Raft__Server_i
import opened Raft__ServerScheduler_i


predicate {:opaque} Q_RaftScheduler_Next(sched:RaftServerScheduler, sched':RaftServerScheduler, ios:seq<RaftIo>)
{
  RaftServerSchedulerNext(sched, sched', ios)
}

predicate {:opaque} Q_RaftServer_Next_ProcessPacket(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextProcessPacket(server, server', ios)
}

predicate Q_RaftServer_Next_ReadClock_Leader(server:RaftServer, server':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  RaftServerNextReadClock_Leader(server, server', clock, sent_packets)
}

predicate Q_RaftServer_Next_ReadClock_NonLeader(server:RaftServer, server':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  RaftServerNextReadClock_NonLeader(server, server', clock, sent_packets)
}

predicate {:opaque} Q_RaftServer_Next_ReadClock(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextReadClock(server, server', ios)
}

predicate {:opaque} Q_RaftServer_Next_CommitAndApply(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextCommitAndApply(server, server', ios)
}

// predicate {:opaque} Q_RaftServer_Next_Process_AppendEntries(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>)
// {
//   // raft_packet.msg.RaftMessage_AppendEntries? && RaftServerNextProcessAppendEntries(server, server', raft_packet, clock, sent_packets)
//   true
// }

// predicate Establish_Q_RaftServer_Next_ProcessPacket_preconditions(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>, ios:seq<RaftIo>)
// {
//   && sent_packets == ExtractSentPacketsFromIos(ios)
//   && clock == SpontaneousClock(ios)
//   // && raft_packet.msg.RaftMessage_AppendEntries?
//   // && Q_RaftServer_Next_Process_AppendEntries(server, server', raft_packet, clock, sent_packets)
//   && (
//     || (raft_packet.msg.RaftMessage_Invalid? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_AppendEntries? && Q_RaftServer_Next_Process_AppendEntries(server, server', raft_packet, clock, sent_packets))
//     // || (raft_packet.msg.RaftMessage_RequestVote? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_AppendEntriesReply? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_RequestVote? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_RequestVoteReply? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_Request? && (server == server' && sent_packets == []))
//     || (raft_packet.msg.RaftMessage_Reply? && (server == server' && sent_packets == []))
//   )
// }

// lemma lemma_EstablishQLReplicaNextProcessPacket(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>, ios:seq<RaftIo>)
//   requires |ios| >= 1
//   requires ios[0].LIoOpReceive?
//   requires |ios| >= 2 ==> (
//     || (ios[1].LIoOpReadClock? && AllIosAreSends(ios[2..]))
//     || (ios[1].LIoOpSend? && AllIosAreSends(ios[1..]))
//   )
//   requires sent_packets == ExtractSentPacketsFromIos(ios)
//   requires Establish_Q_RaftServer_Next_ProcessPacket_preconditions(server, server', raft_packet, clock, sent_packets, ios)
//   ensures Q_RaftServer_Next_ProcessPacket(server, server', ios)
// {
//   reveal Q_RaftServer_Next_Process_AppendEntries();

//   reveal Q_RaftServer_Next_ProcessPacket();
// }

// lemma lemma_EstablishQRaftServerSchedulerNext(server:RaftServer, server':RaftServer, ios:seq<RaftIo>, sched:RaftServerScheduler, sched':RaftServerScheduler)
//   requires 0 <= sched.nextActionIndex <= RaftServerNumActions() - 1
//   requires sched.nextActionIndex == 0 ==> Q_RaftServer_Next_ProcessPacket(server, server', ios)
//   requires sched.nextActionIndex == 1 ==> Q_RaftServer_Next_ReadClock(server, server', ios)
//   requires sched.nextActionIndex == 2 ==> Q_RaftServer_Next_CommitAndApply(server, server', ios)
//   requires sched.server == server
//   requires sched'.server == server'
//   requires sched'.nextActionIndex == (sched.nextActionIndex+1) % RaftServerNumActions()
//   // TOPROVE
//   ensures Q_RaftScheduler_Next(sched, sched', ios)
// {
//   reveal Q_RaftServer_Next_ProcessPacket();
//   reveal Q_RaftServer_Next_ReadClock();
//   reveal Q_RaftScheduler_Next();
//   assert sched'.nextActionIndex == (sched.nextActionIndex + 1) % RaftServerNumActions();
//   assert Q_RaftScheduler_Next(sched, sched', ios);
// }

// lemma lemma_EstablishQRaftServerNextProcessPacketFromTimeout(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
//   requires |ios|==1
//   requires ios[0].LIoOpTimeoutReceive?
//   requires server==server'
//   ensures Q_RaftServer_Next_ProcessPacket(server, server', ios)
// {
//   reveal Q_RaftServer_Next_ProcessPacket();
// }

predicate {:opaque} Q_RaftServerScheduler_Next(server:RaftServerScheduler, server':RaftServerScheduler, ios:seq<RaftIo>)
{
  RaftServerSchedulerNext(server, server', ios)
}

predicate AllIosAreSends(ios:seq<RaftIo>)
{
  forall i :: 0<=i<|ios| ==> ios[i].LIoOpSend?
}

}