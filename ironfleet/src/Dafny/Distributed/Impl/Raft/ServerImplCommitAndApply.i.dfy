include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../../Services/Raft/AppStateMachine.s.dfy"
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

module Raft__ServerImplCommitAndApply_i {

import opened AppStateMachine_s
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Common__NetClient_i
import opened Common__UpperBound_i
import opened Environment_s
import opened Logic__Option_i
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

method Server_Next_CommitAndApply(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  modifies server_impl, server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==>
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
            // && Q_RaftServerScheduler_Next(old(r.AbstractifyToRaftServerScheduler()), r.AbstractifyToRaftServerScheduler(), ios)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ok := true;
  net_event_log := [];
  ios := [];
  ghost var log_tail := [];                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      
  ghost var ios_tail := [];
  var old_next_action_index := server_impl.nextActionIndex;
  var old_commit_index := server_impl.commit_index;
  var old_last_applied := server_impl.last_applied;

  if server_impl.last_applied >= server_impl.commit_index {
    // nothing to apply
    ok := true;
    return;
  }

  ok := false;

  assert server_impl.last_applied < server_impl.commit_index;
  assert old_last_applied < server_impl.commit_index;
  var i := server_impl.last_applied + 1;
  if i > |server_impl.log| as uint64 - 1 {
    // nothing to apply
    ok := true;
    return;
  }
  var log_entry := server_impl.log[i];
  var leader_id;
  if (server_impl.current_leader.Some?) {
    leader_id := server_impl.current_leader.v;
  } else {
    leader_id := GetEndPointIndex(server_impl.config.global_config, server_impl.config.server_ep);
  }
  assert server_impl.nextActionIndex == old(server_impl.nextActionIndex);
  var app_reply := server_impl.app_state.HandleRequest(log_entry.req);
  var msg := CMessage_Reply(log_entry.seqno, 1, leader_id, app_reply);
  var packet := CPacket(log_entry.client_ep, server_impl.config.server_ep , msg);
  var outbound_packets := OutboundPacket(Some(packet));
  assert server_impl.last_applied < |server_impl.log| as uint64;

  server_impl.last_applied := server_impl.last_applied  + 1;

  ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, outbound_packets);
  if (!ok) { return; }
  net_event_log := log_tail;
  ios := ios_tail;
  assert forall i::0<=i<|net_event_log| ==> AbstractifyNetEventToRaftIo(net_event_log[i]) == ios[i];
  assert forall i::0<=i<|net_event_log| ==> net_event_log[i].LIoOpSend? && ios[i].LIoOpSend?;
  assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
  assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;

}

}