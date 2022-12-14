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

// DEBUG
include "../../Protocol/Common/UpperBound.s.dfy"

module Raft__ServerImplProcessPacketX1_i {

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
import opened Raft__Server_i
import opened Raft__ServerImpl_i
import opened Raft__Types_i
import opened Raft__ServerImplDelivery_i
import opened Common__UpperBound_s

//////////////////////////////////////////////////////////
// Process AppendEntries
//////////////////////////////////////////////////////////
method Server_ResetNextElectionTime(server_impl:ServerImpl) returns (ghost clock_event:NetEvent, ghost clock_io:RaftIo)
  requires server_impl.state.role == Follower || server_impl.state.role == Candidate
  requires server_impl.Valid()
  // requires history_after_recv == server_impl.Env().net.history()
  modifies server_impl, NetClientRepr(server_impl.net_client), server_impl.state.random_generator
  ensures clock_event.LIoOpReadClock? && clock_io.LIoOpReadClock?
  ensures server_impl.state.role == old(server_impl.state.role)
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
  ensures server_impl.state == old(server_impl.state).(next_election_time := server_impl.state.next_election_time)
  ensures server_impl.state.next_election_time as int >= UpperBoundedAddition(clock_io.t, server_impl.state.config.global_config.params.min_election_timeout as int, UpperBoundFinite(server_impl.state.config.global_config.params.max_integer_value as int))
  ensures server_impl.state.next_election_time as int <= UpperBoundedAddition(clock_io.t, server_impl.state.config.global_config.params.max_election_timeout as int, UpperBoundFinite(server_impl.state.config.global_config.params.max_integer_value as int))
{
  var const_params := server_impl.state.config.global_config.params;
  var clock;
  clock, clock_event := ReadClock(server_impl.net_client);
  var next_election_delta := server_impl.state.random_generator.NextInt(
    const_params.min_election_timeout,
    const_params.max_election_timeout
  );
  var next_election_time := UpperBoundedAdditionImpl(clock.t, next_election_delta, const_params.max_integer_value);
  server_impl.state := server_impl.state.(next_election_time := next_election_time);
  clock_io := LIoOpReadClock(clock.t as int);
}

method {:timeLimitMultiplier 2} Server_HandleAppendEntries_TryToAppendAndSend(server_impl:ServerImpl, ghost old_net_history:seq<NetEvent>, rr:ReceiveResult, tmp_server_impl:ServerImpl) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires rr.RRPacket?
  requires rr.cpacket.msg.CMessage_AppendEntries?
  // About server
  requires server_impl.state.role == Follower
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  requires tmp_server_impl == server_impl
  modifies server_impl, server_impl.repr, server_impl.net_client
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env() == old(server_impl.Env());
  ensures server_impl.state == old(server_impl.state).(log := server_impl.state.log, commit_index := server_impl.state.commit_index)
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            && AllIosAreSends(ios)
            && (forall i :: 0 <= i < |ios| ==> ios[i].LIoOpSend? && ios[i].s.msg.RaftMessage_AppendEntriesReply?)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && (forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?)
            && |net_event_log| == |ios| == 1
            && Q_RaftServer_Next_ProcessAppendEntries_GoodReply(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), AbstractifyCPacketToRaftPacket(rr.cpacket), ios[0].s)
            && Q_RaftServer_Next_ProcessAppendEntries_GoodReply(tmp_server_impl.AbstractifyToRaftServer(), server_impl.AbstractifyToRaftServer(), AbstractifyCPacketToRaftPacket(rr.cpacket), ios[0].s)
{
  var msg := rr.cpacket.msg;
  var my_last_log := server_impl.GetLastLogEntry();
  var success := 0;
  var match_index := 0;
  net_event_log := [];
  ios := [];
  
  // check whether we can put the entries
  if msg.prev_log_index > 0xFFFF_FFFF_FFFF_FFFE 
    && (msg.prev_log_index as int + 1 + |msg.entries| > ServerMaxLogSize())
  {
    ok := false;
    print "[Error] msg.prev_log_index too large";
    return;
  }

  var my_log_at_prev_log_index := None;
  if (0 <= msg.prev_log_index <= my_last_log.index) {
    my_log_at_prev_log_index := server_impl.GetLogEntry(msg.prev_log_index);
  }
  if (msg.prev_log_index == 0 
    || (my_log_at_prev_log_index.Some? && msg.prev_log_term == my_log_at_prev_log_index.v.term)
  ) {
    success := 1;
    assert |msg.entries| > 0 ==> server_impl.state.log[msg.prev_log_index].index as int + 1 == msg.entries[0].index as int;
    if |msg.entries| == 0 {
      match_index := msg.prev_log_index;
    } else {
      server_impl.state := server_impl.state.(log := server_impl.state.log[..msg.prev_log_index+1] + msg.entries);
      match_index := msg.entries[|msg.entries|-1].index;
    }
    if (msg.leader_commit > server_impl.state.commit_index) {
      server_impl.state := server_impl.state.(commit_index := msg.leader_commit);
    }
    print "After appending, |log|=", |server_impl.state.log|, "\n";
  } else {
    print "Not yet uptodate, cannot append\n";
  }
  var send_msg := CMessage_AppendEntriesReply(server_impl.state.current_term, success, match_index);
  var send_packet := CPacket(rr.cpacket.src, server_impl.GetMyEp(), send_msg);
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, OutboundPacket(Some(send_packet)));
  if (!ok) { return; }
  net_event_log := net_event_log + log_tail;
  ios := ios + ios_tail;
  assert forall i :: 0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
  assert forall i :: 0<=i<|log_tail| ==> (
    && log_tail[i].LIoOpSend? 
    && ios_tail[i].LIoOpSend?
    && ios_tail[i].s.msg.RaftMessage_AppendEntriesReply?
  );
  assert forall i :: 0<=i<|net_event_log|-1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
  var raft_server := old(server_impl.AbstractifyToRaftServer());
  var raft_server' := server_impl.AbstractifyToRaftServer();
  var raft_recv_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
  var raft_sent_packet := ios[0].s;
  assert raft_recv_packet.msg.RaftMessage_AppendEntries?;
  assert raft_sent_packet.msg.RaftMessage_AppendEntriesReply?;
  assert |raft_server.log| >= 1;

  reveal Q_RaftServer_Next_ProcessAppendEntries_GoodReply();
  assert Q_RaftServer_Next_ProcessAppendEntries_GoodReply(raft_server, raft_server', raft_recv_packet, raft_sent_packet);
}

method {:timeLimitMultiplier 8} Server_HandleAppendEntries(server_impl:ServerImpl, rr:ReceiveResult, ghost old_net_history:seq<NetEvent>, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires receive_event.LIoOpReceive?
  requires rr.RRPacket?
  requires NetPacketIsAbstractable(receive_event.r)
  requires rr.cpacket.msg.CMessage_AppendEntries?
  requires AbstractifyCPacketToRaftPacket(rr.cpacket) == AbstractifyNetPacketToRaftPacket(receive_event.r)
  // About server
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client, server_impl.state.random_generator
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            && (
              || rr.cpacket.msg.term < server_impl.state.current_term
              || Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            )
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && (forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?)
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var msg := rr.cpacket.msg;
  net_event_log := [receive_event];
  ios := [receive_io];

  var success := 0;
  var match_index := 0;
  if (server_impl.state.current_term < msg.term) {
    server_impl.state := server_impl.state.(
      current_term := msg.term, voted_for := None, role := Follower
    );
  }
  var my_last_log := server_impl.GetLastLogEntry();
  assert server_impl.Valid();
  // update my leader
  if (server_impl.state.current_term == msg.term) {
    if rr.cpacket.src !in server_impl.state.config.global_config.server_eps {
      print "[Error] src not in server_eps\n";
      ok := false;
      return;
    }
    var src_id := GetEndPointIndex(server_impl.state.config.global_config, rr.cpacket.src);
    server_impl.state := server_impl.state.(current_leader := Some(src_id));
  }
  if (server_impl.state.current_term == msg.term) {
    print "Trying to append #of entries=", |msg.entries|, "\n";
    // Reset role to follower;
    server_impl.state := server_impl.state.(role := Follower);
    // And reset Election Timeout
    ghost var clock_event, clock_io := Server_ResetNextElectionTime(server_impl);
    assert my_last_log.index as int == |server_impl.state.log| - 1;
    assert server_impl.Valid();
    assert |ios| == 1;
    net_event_log := net_event_log + [clock_event];
    ios := ios + [clock_io];
    assert net_event_log[0].LIoOpReceive?;
    assert net_event_log[1].LIoOpReadClock?;
    assert server_impl.state.config == old(server_impl.state.config);
    var old_net_history2 := server_impl.Env().net.history();
    ghost var net_event_log2, ios2;
    assert server_impl.state.log == old(server_impl.state.log);
    assert old(server_impl.AbstractifyToRaftServer().log) == server_impl.AbstractifyToRaftServer().log;
    var tmp_server_impl := server_impl;
    ok, net_event_log2, ios2 := Server_HandleAppendEntries_TryToAppendAndSend(server_impl, old_net_history2, rr, tmp_server_impl);
    if (!ok) { return; }
    reveal Q_RaftServer_Next_ProcessAppendEntries_GoodReply();
    assert Q_RaftServer_Next_ProcessAppendEntries_GoodReply(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), AbstractifyCPacketToRaftPacket(rr.cpacket), ios2[0].s);

    net_event_log := net_event_log + net_event_log2;
    ios := ios + ios2;
    assert forall i :: 0<=i<|net_event_log2| ==> AbstractifyNetEventToRaftIo(net_event_log2[i]) == ios2[i];
    assert forall i :: 0<=i<|net_event_log2| ==> (
      && net_event_log2[i].LIoOpSend?
      && ios2[i].LIoOpSend?
      && ios2[i].s.msg.RaftMessage_AppendEntriesReply?
    );
    assert forall i :: 0<=i<|net_event_log|-1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;

    var raft_server := old(server_impl.AbstractifyToRaftServer());
    var raft_server' := server_impl.AbstractifyToRaftServer();
    var raft_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
    assert raft_packet.msg.RaftMessage_AppendEntries?;

    assert AbstractifyCPacketToRaftPacket(rr.cpacket) == ios[0].r;
    assert clock_io.t == ios[1].t;
    lemma_OnlySentPacketsLeft(ios, 2);
    assert ExtractSentPacketsFromIos(ios) == ExtractSentPacketsFromIos(ios[2..]) == ExtractSentPacketsFromIos(ios2);

    reveal Q_RaftServer_Next_ProcessAppendEntries();
    assert Q_RaftServer_Next_ProcessAppendEntries(raft_server, raft_server', raft_packet, clock_io.t, ExtractSentPacketsFromIos(ios));

    reveal Q_RaftServer_Next_ProcessPacket();
    assert Q_RaftServer_Next_ProcessPacket(raft_server, raft_server', ios);
  } else {
    net_event_log := [receive_event];
    ios := [receive_io];
    ok := true;
    reveal Q_RaftServer_Next_ProcessPacket();
  }
}

}
