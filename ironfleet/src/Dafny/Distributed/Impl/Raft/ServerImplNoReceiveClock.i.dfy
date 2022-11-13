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
// include "NetRSL.i.dfy"

module Raft_ServerImplNoReceiveClock {

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
import opened Raft__Types_i

method Server_Next_NoReceive_ReadClock(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.nextActionIndex == 1
  requires server_impl.Valid()
  modifies server_impl.repr
  // ensures server_impl.Repr == old(server_impl.Repr)
  // ensures server_impl.netClient != null
  // ensures ok == NetClientOk(server_impl.netClient)
  // ensures server_impl.Env() == old(server_impl.Env())
  // ensures ok ==>
  //           && server_impl.Valid()
  //           && server_impl.Env() == old(server_impl.Env())
  //           && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
  //           && Q_LReplica_NoReceive_Next(old(server_impl.AbstractifyToLReplica()), server_impl.nextActionIndex as int, server_impl.AbstractifyToLReplica(), ios)
  //           && OnlySentMarshallableData(netEventLog)
  //           && RawIoConsistentWithSpecIO(netEventLog, ios)
  //           && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
{
  ok := true;
  net_event_log := [];
  ios := [];

  if server_impl.nextActionIndex == 1 {
    var clock,netEvent0 := ReadClock(server_impl.net_client);
    ghost var io0 := LIoOpReadClock(clock.t as int);

    if (server_impl.role.Leader?) {
      ok := true;
      if (clock.t >= server_impl.next_heartbeat_time) {
        var const_params := server_impl.config.global_config.params;
        var next_heartbeat_time := UpperBoundedAdditionImpl(clock.t, const_params.heartbeat_timeout, const_params.max_integer_value);
        server_impl.next_heartbeat_time := next_heartbeat_time;
        var msg := CMessage_AppendEntries(server_impl.current_term, server_impl.config.server_ep, 0, 0, [], 0);
        var packets := BuildBroadcastToEveryone(server_impl.config.global_config, server_impl.config.server_ep, msg);
        var packets_sent := Broadcast(packets);
        ghost var log_tail, ios_tail;
        ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, packets_sent);
        if (!ok) { return; }
        ghost var ios_head := [io0];
        ghost var log_head := [netEvent0];
        ios := ios_head + ios_tail;
        net_event_log := log_head + log_tail;

      } else {
        replica', packets_sent := ReplicaNextReadClockMaybeSendHeartbeatSkip(replica, clock);
      }
    }
  }
}

}