include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/ServerScheduler.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "NetRaft.i.dfy"
include "CTypes.i.dfy"
include "PacketParsing.i.dfy"
include "QRelations.i.dfy"
include "ServerImpl.i.dfy"
include "ServerImplNoReceiveCLock.i.dfy"
include "ServerImplProcessPacketX.i.dfy"

module Raft__ServerImplMain_i {

import opened Environment_s
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Raft__Server_i
import opened Raft__ServerScheduler_i
import opened Raft__Types_i
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened Raft__NetRaft_i
import opened Raft__CTypes_i
import opened Raft__PacketParsing_i
import opened Raft__QRelations_i
import opened Raft__ServerImpl_i
import opened Raft__ServerImplNoReceiveClock_i
import opened Raft__ServerImplProcessPacketX_i

method {:timeLimitMultiplier 2} rollActionIndex(a:uint64) returns (a':uint64)
  requires 0 <= a as int < RaftServerNumActions()
  ensures a' as int == ((a as int) + 1) % RaftServerNumActions()
{
  lemma_mod_auto(RaftServerNumActions());
  if (a >= 1) {
    a' := 0;
  } else {
    a' := (a + 1);
  }
}

predicate IosReflectIgnoringUnsendable(ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  && |ios| == 1
  && ios[0].LIoOpReceive?
  && (|| !Demarshallable(ios[0].r.msg, CMessage_grammar())
     || !Marshallable(parse_Message(DemarshallFunc(ios[0].r.msg, CMessage_grammar()))))
}
    
predicate HostNextIgnoreUnsendable(s:RaftServerScheduler, s':RaftServerScheduler, ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
  && s.nextActionIndex == 0
  && s' == s.(nextActionIndex := 1)
  && IosReflectIgnoringUnsendable(ios)
}


method {:timeLimitMultiplier 2} ServerNextMainProcessPacketX(server_impl:ServerImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires server_impl.nextActionIndex == 0
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==>
            && server_impl.Valid()
            // TOPROVE
            // && (|| Q_RaftScheduler_Next(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), ios)
            //    || HostNextIgnoreUnsendable(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), netEventLog))
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
            && forall i :: 0 <= i < |netEventLog| - 1 ==> netEventLog[i].LIoOpReceive? || netEventLog[i+1].LIoOpSend?
{
  ghost var server_old := old(server_impl.AbstractifyToRaftServer());
  ghost var scheduler_old := old(server_impl.AbstractifyToRaftServerScheduler());

  assert scheduler_old.nextActionIndex == 0;

  //print ("Replica_Next_main Enter\n");
  assert scheduler_old.server == server_old;
  ok, netEventLog, ios := Server_Next_ProcessPacketX(server_impl);
  if (!ok) { return; }

  assert server_impl.Valid();

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := server_impl.net_client;
  ghost var net_addr_old := server_impl.net_client.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  ghost var server := server_impl.AbstractifyToRaftServer();
  server_impl.nextActionIndex := 1;
  ghost var scheduler := server_impl.AbstractifyToRaftServerScheduler();

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == server_impl.net_client;
  assert NetClientIsValid(server_impl.net_client);
  assert net_addr_old == server_impl.net_client.MyPublicKey();

  assert server_impl.Valid();

  calc {
    scheduler.nextActionIndex;
    server_impl.nextActionIndex as int;
    1;
      { lemma_mod_auto(RaftServerNumActions()); }
    (1)%RaftServerNumActions();
    (scheduler_old.nextActionIndex+1)%RaftServerNumActions();
  }

  // TOPROVE
  // if Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios) {
  //   lemma_EstablishQLSchedulerNext(server_old, server, ios, scheduler_old, scheduler);
  //   assert Q_RaftScheduler_Next(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), ios);
  // }
  // else {
  //   assert IosReflectIgnoringUnsendable(netEventLog);
  //   assert old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer();
  //   assert HostNextIgnoreUnsendable(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), netEventLog);
  // }
}

method ServerNextMainReadClock(r:ServerImpl)
  returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires r.Valid()
  requires r.nextActionIndex == 1
  modifies r.repr
  ensures r.repr == old(r.repr)
  ensures r.net_client != null
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            // TOPROVE
            // && Q_RaftServerScheduler_Next(old(r.AbstractifyToRaftServerScheduler()), r.AbstractifyToRaftServerScheduler(), ios)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
            && forall i :: 0 <= i < |netEventLog| - 1 ==> netEventLog[i].LIoOpReceive? || netEventLog[i+1].LIoOpSend?
{
  var curActionIndex := r.nextActionIndex;

  ghost var server_old := old(r.AbstractifyToRaftServer());
  ghost var scheduler_old := old(r.AbstractifyToRaftServerScheduler());

  assert scheduler_old.server == server_old;
  ok, netEventLog, ios := Server_Next_NoReceive_ReadClock(r);
  if (!ok) { return; }

  assert r.Valid();

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.net_client;
  ghost var net_addr_old := r.net_client.MyPublicKey();
  assert NetClientIsValid(net_client_old);

  ghost var replica := r.AbstractifyToRaftServer();
  var nextActionIndex' := rollActionIndex(r.nextActionIndex);
  r.nextActionIndex := nextActionIndex';
  ghost var scheduler := r.AbstractifyToRaftServerScheduler();

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.net_client;
  assert NetClientIsValid(r.net_client);
  assert net_addr_old == r.net_client.MyPublicKey();

  assert r.Valid();
        
  calc {
    scheduler.nextActionIndex;
    r.nextActionIndex as int;
    nextActionIndex' as int;
    ((curActionIndex+1) as int)%RaftServerNumActions();
    (scheduler_old.nextActionIndex+1)%RaftServerNumActions();
  }

  // lemma_EstablishQLSchedulerNext(server_old, replica, ios, scheduler_old, scheduler);
  // assert Q_RaftServerScheduler_Next(old(r.AbstractifyToRaftServerScheduler()), r.AbstractifyToRaftServerScheduler(), ios);
}


method Server_Next_main(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  modifies server_impl.app_state, server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==>
            && server_impl.Valid()
            // TOPROVE
            // && (|| Q_RaftScheduler_Next(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), ios)
            //    || HostNextIgnoreUnsendable(old(server_impl.AbstractifyToRaftServerScheduler()), server_impl.AbstractifyToRaftServerScheduler(), net_event_log))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  //print ("Replica_Next_main Enter\n");
  if server_impl.nextActionIndex == 0 {
    ok, net_event_log, ios := ServerNextMainProcessPacketX(server_impl);
  }
  else if (server_impl.nextActionIndex == 1) {
    ok, net_event_log, ios := ServerNextMainReadClock(server_impl);
  } else {
    ok := true;
    ios := [];
    net_event_log := [];
    assert server_impl.Valid();
  }
  //print ("Replica_Next_main Exit\n");
}


}