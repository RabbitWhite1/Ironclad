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

//////////////////////////////////////////////////////////
// ProcessPacket
//////////////////////////////////////////////////////////
predicate {:opaque} Q_RaftServer_Next_ProcessPacket(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextProcessPacket(server, server', ios)
}

predicate {:opaque} Q_RaftServer_Next_ProcessAppendEntries_GoodReply(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, sent_packet:RaftPacket)
{
  && raft_packet.msg.RaftMessage_AppendEntries?
  && sent_packet.msg.RaftMessage_AppendEntriesReply?
  && |server.log| >= 1
  && RaftServerNextProcessAppendEntries_GoodReply(server, server', raft_packet, sent_packet)
}

predicate {:opaque} Q_RaftServer_Next_ProcessAppendEntries(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>)
{
  && raft_packet.msg.RaftMessage_AppendEntries?
  && RaftServerNextProcessAppendEntries(server, server', raft_packet, clock, sent_packets)
}

predicate {:opaque} Q_RaftServer_Next_ProcessAppendEntriesReply(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, sent_packets:seq<RaftPacket>)
{
  && raft_packet.msg.RaftMessage_AppendEntriesReply?
  && RaftServerNextProcessAppendEntriesReply(server, server', raft_packet, sent_packets)
}

predicate {:opaque} Q_RaftServer_Next_ProcessRequestVote(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, clock:int, sent_packets:seq<RaftPacket>)
{
  && raft_packet.msg.RaftMessage_RequestVote?
  && RaftServerNextProcessRequestVote(server, server', raft_packet, clock, sent_packets)
}

predicate {:opaque} Q_RaftServer_Next_ProcessRequestVoteReply(server:RaftServer, server':RaftServer, raft_packet:RaftPacket, sent_packets:seq<RaftPacket>)
{
  && raft_packet.msg.RaftMessage_RequestVoteReply?
  && RaftServerNextProcessRequestVoteReply(server, server', raft_packet, sent_packets)
}

//////////////////////////////////////////////////////////
// ReadClock
//////////////////////////////////////////////////////////
predicate {:opaque} Q_RaftServer_Next_ReadClock(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextReadClock(server, server', ios)
}

predicate {:opaque} Q_RaftServer_Next_ReadClock_Leader(server:RaftServer, server':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  RaftServerNextReadClock_Leader(server, server', clock, sent_packets)
}

predicate {:opaque} Q_RaftServer_Next_ReadClock_NonLeader(server:RaftServer, server':RaftServer, clock:int, sent_packets:seq<RaftPacket>)
{
  RaftServerNextReadClock_NonLeader(server, server', clock, sent_packets)
}

//////////////////////////////////////////////////////////
// CommitAndApply
//////////////////////////////////////////////////////////
predicate {:opaque} Q_RaftServer_Next_CommitAndApply(server:RaftServer, server':RaftServer, ios:seq<RaftIo>)
{
  RaftServerNextCommitAndApply(server, server', ios)
}

predicate {:opaque} Q_RaftServerScheduler_Next(server:RaftServerScheduler, server':RaftServerScheduler, ios:seq<RaftIo>)
{
  RaftServerSchedulerNext(server, server', ios)
}

predicate AllIosAreSends(ios:seq<RaftIo>)
{
  forall i :: 0<=i<|ios| ==> ios[i].LIoOpSend?
}

}