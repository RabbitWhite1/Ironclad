include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/UpperBound.i.dfy"
include "AppInterface.i.dfy"
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

module Raft__ServerImplProcessPacketX_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Logic__Option_i
import opened Math__mod_auto_i
import opened Common__NetClient_i
import opened Common__UpperBound_i
import opened Environment_s
import opened Raft__AppInterface_i
import opened Raft__CBroadcast_i
import opened Raft__ConfigState_i
import opened Raft__CTypes_i
import opened Raft__CMessage_i
import opened Raft__NetRaft_i
import opened Raft__PacketParsing_i
import opened Raft__QRelations_i
import opened Raft__ServerImpl_i
import opened Raft__Types_i
import opened Raft__ServerImplDelivery_i

//////////////////////////////////////////////////////////
// Process request from client
//////////////////////////////////////////////////////////
method Server_Next_ProcessRequest(server_impl:ServerImpl, ghost old_net_history:seq<NetEvent>, rr:ReceiveResult, ghost receive_event:NetEvent)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires receive_event.LIoOpReceive?
  requires rr.RRPacket?
  requires NetPacketIsAbstractable(receive_event.r)
  requires rr.cpacket.msg.CMessage_Request?
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // PROVE
            // && (|| Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            //     || (&& IosReflectIgnoringUnsendable(net_event_log)
            //        && old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer()))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ok := true;
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var recved_msg := rr.cpacket.msg;
  ghost var ios_head := [receive_io];
  ghost var log_head := [receive_event];
  ghost var log_tail := [];                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      
  ghost var ios_tail := [];
  net_event_log := log_head;
  ios := ios_head;
  ok := true;
  
  if server_impl.role == Leader {
    var leader_ep := server_impl.config.server_ep;
    var leader_id := GetEndPointIndex(server_impl.config.global_config, leader_ep);
    // create entry
    var entry;
    print "trying to create log\n";
    ok, entry := server_impl.CreateLogEntry(rr.cpacket.src, recved_msg.seqno_req, recved_msg.req);
    print "created log: ", ok, "\n";
    if (!ok) {
      ok := true;
      return;
    }
    // Append entry to leader's log
    if (
      1 > ServerMaxLogSize() - |server_impl.log| 
      || !(server_impl.LastLogEntryIndex() + 1 == entry.index == |server_impl.log| as uint64)
    ) {
      print "append failed!!!",server_impl.LastLogEntryIndex() + 1, ",", entry.index, ",", |server_impl.log| as uint64, "\n";
      ok := true;
      return;
    }
    server_impl.AddLogEntries([entry]);
    server_impl.next_index := server_impl.next_index[leader_ep := entry.index + 1];
    server_impl.match_index := server_impl.match_index[leader_ep := entry.index];
    assert server_impl.role.Leader?;
    print "append success!!!\n";
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
    assert net_event_log[0].LIoOpReceive?;
    assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
    assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
    assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
    assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
  } else {
    var leader_id;
    if (server_impl.current_leader.Some?) {
      leader_id := GetEndPointIndex(server_impl.config.global_config, server_impl.current_leader.v);
    } else {
      leader_id := GetEndPointIndex(server_impl.config.global_config, server_impl.config.server_ep);
    }
    var msg := CMessage_Reply(recved_msg.seqno_req, 1, leader_id, []);
    var packet := CPacket(rr.cpacket.src, server_impl.config.server_ep , msg);
    var outbound_packets := OutboundPacket(Some(packet));
    ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, outbound_packets);
    if (!ok) { return; }
    ios := ios_head + ios_tail;
    net_event_log := log_head + log_tail;
    assert net_event_log[0].LIoOpReceive?;
    assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
    assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
    assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
    assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
  }
}

//////////////////////////////////////////////////////////
// Process AppendEntries
//////////////////////////////////////////////////////////
method Server_ResetNextElectionTime(server_impl:ServerImpl) returns (ghost clock_event:NetEvent, ghost clock_io:RaftIo)
  requires server_impl.role == Follower
  requires server_impl.Valid()
  // requires history_after_recv == server_impl.Env().net.history()
  modifies server_impl, NetClientRepr(server_impl.net_client)
  ensures clock_event.LIoOpReadClock? && clock_io.LIoOpReadClock?
  ensures server_impl.role == Follower
  ensures server_impl.Valid()
  // ensures io and event consistent
  ensures AbstractifyNetEventToRaftIo(clock_event) == clock_io
  // ensures history correctly changed
  ensures old(server_impl.Env().net.history()) + [clock_event] == server_impl.Env().net.history()
  // make sure some fields unchanged
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.nextActionIndex == old(server_impl.nextActionIndex)
  ensures RawIoConsistentWithSpecIO([clock_event], [clock_io])
  ensures server_impl.log == old(server_impl.log)
{
  var const_params := server_impl.config.global_config.params;
  var clock;
  clock, clock_event := ReadClock(server_impl.net_client);
  var election_timeout_delta := GenerateElectionTimeout(const_params);
  var next_election_time := UpperBoundedAdditionImpl(clock.t, election_timeout_delta, const_params.max_integer_value);
  server_impl.next_election_time := next_election_time;
  clock_io := LIoOpReadClock(clock.t as int);
}

method Server_HandleAppendEntries(server_impl:ServerImpl, ghost old_net_history:seq<NetEvent>, rr:ReceiveResult, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires receive_event.LIoOpReceive?
  requires rr.RRPacket?
  requires NetPacketIsAbstractable(receive_event.r)
  requires rr.cpacket.msg.CMessage_AppendEntries?
  // About server
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // PROVE
            // && (|| Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            //     || (&& IosReflectIgnoringUnsendable(net_event_log)
            //        && old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer()))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var msg := rr.cpacket.msg;

  var success := 0;
  var match_index := 0;
  if (server_impl.current_term < msg.term) {
    server_impl.current_term := msg.term;
    server_impl.voted_for := None;
    server_impl.role := Follower;
  }
  var my_last_log := server_impl.GetLastLogEntry();
  assert server_impl.Valid();
  if (server_impl.current_term == msg.term) {
    print "Trying to append #of entries=", |msg.entries|, "\n";
    // Reset role to follower;
    server_impl.role := Follower;
    // And reset Election Timeout
    ghost var clock_event, clock_io := Server_ResetNextElectionTime(server_impl);
    assert my_last_log.index as int == |server_impl.log| - 1;
    assert server_impl.Valid();
    net_event_log := [receive_event, clock_event];
    ios := [receive_io, clock_io];
    assert net_event_log[0].LIoOpReceive?;
    assert net_event_log[1].LIoOpReadClock?;
    // check whether we can put the entries
    if msg.prev_log_index > 0xFFFF_FFFF_FFFF_FFFE 
      && (msg.prev_log_index as int + 1 + |msg.entries| > ServerMaxLogSize()
    ){
      ok := true;
      print "[Error] msg.prev_log_index too large";
      return;
    }
    if (msg.prev_log_index == 0 
      || (msg.prev_log_index <= my_last_log.index && msg.prev_log_term == my_last_log.term)
    ) {
      success := 1;
      assert |msg.entries| > 0 ==> server_impl.log[msg.prev_log_index].index as int + 1 == msg.entries[0].index as int;
      server_impl.log := server_impl.log[..msg.prev_log_index+1] + msg.entries;
      if |msg.entries| == 0 {
        match_index := msg.prev_log_index;
      } else {
        match_index := my_last_log.index;
      }
      if (msg.leader_commit > server_impl.commit_index) {
        server_impl.commit_index := msg.leader_commit;
      }
      print "After appending, |log|=", |server_impl.log|, "\n";
    } else {
      print "Not yet uptodate, cannot append\n";
    }
    var send_msg := CMessage_AppendEntriesReply(server_impl.current_term, success, match_index);
    var send_packet := CPacket(rr.cpacket.src, server_impl.config.server_ep, send_msg);
    ghost var log_tail, ios_tail;
    ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, OutboundPacket(Some(send_packet)));
    if (!ok) { return; }
    net_event_log := net_event_log + log_tail;
    ios := ios + ios_tail;
    assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
    assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
    assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
  } else {
    net_event_log := [receive_event];
    ios := [receive_io];
    ok := true;
  }
}

//////////////////////////////////////////////////////////
// Process AppendEntriesReply
//////////////////////////////////////////////////////////
method Server_HandleAppendEntriesReply(server_impl:ServerImpl, ghost old_net_history:seq<NetEvent>, rr:ReceiveResult, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires receive_event.LIoOpReceive?
  requires rr.RRPacket?
  requires NetPacketIsAbstractable(receive_event.r)
  requires rr.cpacket.msg.CMessage_AppendEntriesReply?
  // About server
  requires server_impl.role == Leader
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // PROVE
            // && (|| Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            //     || (&& IosReflectIgnoringUnsendable(net_event_log)
            //        && old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer()))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var msg := rr.cpacket.msg;
  // setup default return values
  net_event_log := [receive_event];
  ios := [receive_io];
  ok := true;

  // Check and update term
  if (server_impl.current_term < msg.term) {
    server_impl.current_term := msg.term;
    server_impl.voted_for := None;
    server_impl.role := Follower;
    return;
  }
  
  var ep := rr.cpacket.src;
  if (ep !in server_impl.config.global_config.server_eps) {
    print "[Error] src of the packet not in cluster\n";
    return;
  }

  if (server_impl.role == Leader && server_impl.current_term == msg.term) {
    if (msg.success == 1) {
      assert forall ep :: ep in server_impl.config.global_config.server_eps ==> (
        && ep in server_impl.next_index 
        && ep in server_impl.match_index
        && 1 <= server_impl.next_index[ep] <= |server_impl.log| as uint64
        && 0 <= server_impl.match_index[ep] < server_impl.next_index[ep]
      );
      if (msg.match_index > MaxLogEntryIndex() as uint64 - 1) {
        print "[Error] match_index too large\n";
        return;
      }
      if (msg.match_index + 1 > |server_impl.log| as uint64) {
        print "[Error] should not be\n";
        return;
      }
      if (msg.match_index > server_impl.match_index[ep]) {
        server_impl.match_index := server_impl.match_index[ep := msg.match_index];
      }
      server_impl.next_index := server_impl.next_index[ep := server_impl.match_index[ep] + 1];
      // Update commit_index
      ok := server_impl.TryToIncreaseCommitIndexUntil(server_impl.match_index[ep]);
      if (!ok) { 
        print "[Error] TryToIncreaseCommitIndexUntil failed, ", server_impl.commit_index, "\n";
        ok := true;
        return;
      } else {
        print "[Info] Committed up to ", server_impl.commit_index, "\n";
      }
    } else {
      var decreased_index;
      if server_impl.next_index[ep] > 1 {
        decreased_index := server_impl.next_index[ep];
      } else {
        decreased_index := 1;
      }
      server_impl.next_index := server_impl.next_index[ep := decreased_index];
    }
  }

}

//////////////////////////////////////////////////////////
// Process All Packet.
//////////////////////////////////////////////////////////
method Server_Next_ProcessPacketX(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires ConfigStateIsValid(server_impl.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // PROVE
            // && (|| Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            //     || (&& IosReflectIgnoringUnsendable(net_event_log)
            //        && old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer()))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ghost var old_net_history := server_impl.Env().net.history();

  var rr, receive_event := Receive(server_impl.net_client, server_impl.config.server_ep, server_impl.config.global_config, server_impl.msg_grammar);
  
  assert server_impl.Env()==old(server_impl.Env());

  if (rr.RRFail?) {
    ok := false;
    net_event_log := [];
    ios := [];
    return;
  } else if (rr.RRTimeout?) {
    ok := true;
    net_event_log := [receive_event];
    ios := [LIoOpTimeoutReceive()];
  } else {
    var marshallable := DetermineIfMessageMarshallable(rr.cpacket.msg);
    ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
    // setup default return
    net_event_log := [receive_event];
    ios := [receive_io];
    ok := true;
    if !marshallable {
      return;
    }
    var my_idx := server_impl.GetMyIndex();
    var msg := rr.cpacket.msg;
    if (msg.CMessage_Request? || msg.CMessage_Reply?) {
      if (msg.CMessage_Request?) {
        print "server ", my_idx, "(is_leader=", server_impl.role.Leader?, ") received a request(", msg.seqno_req, ", ", msg.req, ")\n";
        ok, net_event_log, ios := Server_Next_ProcessRequest(server_impl, old_net_history, rr, receive_event);
      } else {
        return;
      }
    } else {
      assert msg.CMessage_AppendEntries? || msg.CMessage_AppendEntriesReply? || msg.CMessage_RequestVote? || msg.CMessage_RequestVoteReply?;
      // ignore outside packets for inside operations
      if (rr.cpacket.src !in server_impl.config.global_config.server_eps) {
        return;
      }
      var src_id := GetEndPointIndex(server_impl.config.global_config, rr.cpacket.src);
      if (msg.CMessage_AppendEntries?) {
        // ignore packet from self
        if (rr.cpacket.src == server_impl.config.server_ep) {
          return;
        }
        print "server ", my_idx, "(is_leader=", server_impl.role.Leader?, 
          ") received AppendEntries(|entries|=", |msg.entries|, ",prev_log_index=", msg.prev_log_index, ")\n";
        ok, net_event_log, ios := Server_HandleAppendEntries(server_impl, old_net_history, rr, receive_event);
      } else if (msg.CMessage_AppendEntriesReply?) {
        if (server_impl.role != Leader) {
          return;
        }
        print "server ", my_idx, "(is_leader=", server_impl.role.Leader?, 
          ") received from ", src_id, " AppendEntriesReply(term=", msg.term, ",success=", msg.success, "match_index=", msg.match_index, ")\n";
        ok, net_event_log, ios := Server_HandleAppendEntriesReply(server_impl, old_net_history, rr, receive_event);
      } else {
        return;
      }
    }
  }
}

}
