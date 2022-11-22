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

method Server_Next_NoReceive_ReadClock(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.nextActionIndex == 1
  requires server_impl.Valid()
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures ok ==>
            && server_impl.Valid()
            && server_impl.Env() == old(server_impl.Env())
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
            // && Q_RaftServer_NoReceive_Next(old(server_impl.AbstractifyToRaftServer()), server_impl.nextActionIndex as int, server_impl.AbstractifyToRaftServer(), ios)
            && OnlySentMarshallableData(net_event_log)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            // TODO: can I remove?
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ok := true;
  net_event_log := [];
  ios := [];

  if server_impl.nextActionIndex == 1 {
    var clock,netEvent0 := ReadClock(server_impl.net_client);
    ghost var io0 := LIoOpReadClock(clock.t as int);
    ghost var ios_head := [io0];
    ghost var log_head := [netEvent0];
    ghost var log_tail := [];
    ghost var ios_tail := [];
    ghost var preDeliveryHistory := server_impl.Env().net.history();
    // Default return
    net_event_log := log_head;
    ios := ios_head;
    ok := true;

    if (server_impl.role.Leader?) {
      if (clock.t >= server_impl.next_heartbeat_time) {
        var const_params := server_impl.config.global_config.params;
        var next_heartbeat_time := UpperBoundedAdditionImpl(clock.t, const_params.heartbeat_timeout, const_params.max_integer_value);
        server_impl.next_heartbeat_time := next_heartbeat_time;
        
        // Create packets
        var outbound_packets:seq<CPacket> := [];
        ok, outbound_packets := Server_CreateAppendEntriesForAll(server_impl);
        if (!ok) {
          ok := true;
          return;
        }
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
      } else {
        net_event_log := log_head;
        ios := ios_head;
      }
    } else {
      if (clock.t >= server_impl.next_election_time) {
        var const_params := server_impl.config.global_config.params;
        var next_election_delta := GenerateElectionTimeout(const_params);
        var next_election_time := UpperBoundedAdditionImpl(clock.t, next_election_delta, const_params.max_integer_value);
        server_impl.next_election_time := next_election_time;
        if (!ok) { return; }
        // print "My election timeout!!\n";
        ios := [io0];
        net_event_log := [netEvent0];
      } else {
        net_event_log := log_head;
        ios := ios_head;
      }
    }
  }
}

}