include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/UpperBound.i.dfy"
include "CBroadcast.i.dfy"
include "CMessage.i.dfy"
include "Config.i.dfy"
include "CTypes.i.dfy"
include "NetRaft.i.dfy"
include "PacketParsing.i.dfy"
include "QRelations.i.dfy"
include "ServerImpl.i.dfy"
include "ServerImplDelivery.i.dfy"
// include "NetRSL.i.dfy"
// DEBUG
include "../../Protocol/Common/UpperBound.s.dfy"

module Raft__ServerImplNoReceiveClock_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Common__NetClient_i
import opened Common__UpperBound_i
import opened Environment_s
import opened Raft__CBroadcast_i
import opened Raft__ConfigState_i
import opened Raft__CTypes_i
import opened Raft__CMessage_i
import opened Raft__NetRaft_i
import opened Raft__PacketParsing_i
import opened Raft__QRelations_i
import opened Raft__ServerImpl_i
import opened Raft__ServerImplDelivery_i
import opened Raft__Types_i
import opened Common__UpperBound_s

method Server_Next_NoReceive_ReadClock(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.nextActionIndex == 1
  requires server_impl.Valid()
  modifies server_impl, server_impl.repr, server_impl.random_generator
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures ok ==>
            && server_impl.Valid()
            && server_impl.Env() == old(server_impl.Env())
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
            // && Q_RaftServer_Next_ReadClock(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            && OnlySentMarshallableData(net_event_log)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            // TODO: can I remove?
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ok := true;
  net_event_log := [];
  ios := [];

  var clock,clock_event := ReadClock(server_impl.net_client);
  ghost var clock_io := LIoOpReadClock(clock.t as int);
  ghost var ios_head := [clock_io];
  ghost var log_head := [clock_event];
  ghost var log_tail := [];
  ghost var ios_tail := [];
  net_event_log := log_head;
  ios := ios_head;
  ghost var preDeliveryHistory := server_impl.Env().net.history();
  // Default return
  net_event_log := log_head;
  ios := ios_head;
  ok := true;

  if (server_impl.role.Leader?) {
    if (clock.t >= server_impl.next_heartbeat_time) {
      var const_params := server_impl.config.global_config.params;
      // Create heartbeat packets
      var outbound_packets:seq<CPacket> := [];
      outbound_packets := Server_CreateAppendEntriesForAll(server_impl, true);
      assert |outbound_packets| <= |server_impl.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
      assert (forall p :: p in outbound_packets ==> CPacketIsSendable(p));
      ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, PacketSequence(outbound_packets));
      if (!ok) { return; }
      ios := ios_head + ios_tail;
      net_event_log := log_head + log_tail;
      // print "I broadcast heartbeat!\n";
      assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
      assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
      assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
      assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;

      // Update fields of server_impl after delivering packets
      var next_heartbeat_time := UpperBoundedAdditionImpl(clock.t, const_params.heartbeat_timeout, const_params.max_integer_value);
      server_impl.next_heartbeat_time := next_heartbeat_time;
      var raft_server := old(server_impl.AbstractifyToRaftServer());
      var raft_server' := server_impl.AbstractifyToRaftServer();
      assert Q_RaftServer_Next_ReadClock_Leader(raft_server, raft_server', clock.t as int, AbstractifyOutboundCPacketsToSeqOfRaftPackets(PacketSequence(outbound_packets)));
    } else {
      net_event_log := log_head;
      ios := ios_head;
    }
  } else {
    if (clock.t >= server_impl.next_election_time) {
      var const_params := server_impl.config.global_config.params;
      var next_election_delta := server_impl.random_generator.NextInt(
        const_params.min_election_timeout,
        const_params.max_election_timeout
      );
      print "My election timeout!!\n";
      ios := [clock_io];
      net_event_log := [clock_event];
      // TODO: need to increase my term
      if server_impl.current_term > 0xFFFF_FFFF_FFFF_FFFF - 1 {
        ok := true;
        return;
      }
      server_impl.current_term := server_impl.current_term + 1;
      server_impl.BecomeCandidate();
      var outbound_packets;
      ok, outbound_packets := Server_CreateRequestVoteForAll(server_impl);
      if (!ok) {
        ok := true;
        return;
      }
      assert |outbound_packets| <= |server_impl.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
      assert (forall p :: p in outbound_packets ==> CPacketIsSendable(p));

      var server_impl_before_deliver := server_impl;
      ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, PacketSequence(outbound_packets));
      if (!ok) { return; }
      ios := ios_head + ios_tail;
      net_event_log := log_head + log_tail;
      assert net_event_log[0].LIoOpReadClock?;
      assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
      assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
      assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
      assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;

      server_impl := server_impl_before_deliver;

      // Update fields of server_impl after delivering packets
      var next_election_time := UpperBoundedAdditionImpl(clock.t, next_election_delta, const_params.max_integer_value);
      server_impl.next_election_time := next_election_time;

      var raft_server := old(server_impl.AbstractifyToRaftServer());
      var raft_server' := server_impl.AbstractifyToRaftServer();
      // assert RaftServerNextReadClock_NonLeader(raft_server, raft_server', clock.t as int, AbstractifyOutboundCPacketsToSeqOfRaftPackets(PacketSequence(outbound_packets)));
    } else {
      net_event_log := log_head;
      ios := ios_head;
    }
  }
}

}