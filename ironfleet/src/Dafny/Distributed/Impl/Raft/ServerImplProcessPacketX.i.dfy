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
include "ServerImplProcessPacketX1.i.dfy"

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
import opened Raft__Server_i
import opened Raft__ServerImpl_i
import opened Raft__Types_i
import opened Raft__ServerImplDelivery_i
import opened Raft__ServerImplProcessPacketX1_i

//////////////////////////////////////////////////////////
// Process request from client
//////////////////////////////////////////////////////////
method {:timeLimitMultiplier 2} Server_Next_ProcessRequest(server_impl:ServerImpl, rr:ReceiveResult, ghost old_net_history:seq<NetEvent>, ghost receive_event:NetEvent)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // recved things
  requires rr.RRPacket?
  requires rr.cpacket.msg.CMessage_Request?
  requires receive_event.LIoOpReceive?
  requires NetPacketIsAbstractable(receive_event.r)
  requires AbstractifyNetPacketToRaftPacket(receive_event.r) == AbstractifyCPacketToRaftPacket(rr.cpacket)
  // server
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
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
  
  if server_impl.state.role == Leader {
    var leader_id := server_impl.state.config.server_id;
    var leader_ep := server_impl.GetMyEp();
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
      1 > ServerMaxLogSize() - |server_impl.state.log| 
      || !(server_impl.LastLogEntryIndex() + 1 == entry.index == |server_impl.state.log| as uint64)
    ) {
      print "append failed!!!",server_impl.LastLogEntryIndex() + 1, ",", entry.index, ",", |server_impl.state.log| as uint64, "\n";
      ok := true;
      return;
    }
    server_impl.AddLogEntries([entry]);
    server_impl.state := server_impl.state.(next_index := server_impl.state.next_index[leader_ep := entry.index + 1]);
    server_impl.state := server_impl.state.(match_index := server_impl.state.match_index[leader_ep := entry.index]);
    assert server_impl.state.role.Leader?;
    print "append success!!!\n";
    // Create packets
    var outbound_packets:seq<CPacket> := [];
    outbound_packets := Server_CreateAppendEntriesForAll(server_impl, false);
    assert |outbound_packets| <= |server_impl.state.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
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
    if (server_impl.state.current_leader.Some?) {
      leader_id := server_impl.state.current_leader.v;
    } else {
      leader_id := GetEndPointIndex(server_impl.state.config.global_config, server_impl.GetMyEp());
    }
    var msg := CMessage_Reply(recved_msg.seqno_req, 0, leader_id, []);
    var packet := CPacket(rr.cpacket.src, server_impl.GetMyEp() , msg);
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
  ensures server_impl.state.log == old(server_impl.state.log)
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

//////////////////////////////////////////////////////////
// Process AppendEntriesReply
//////////////////////////////////////////////////////////
method {:timeLimitMultiplier 8} Server_HandleAppendEntriesReply(server_impl:ServerImpl, rr:ReceiveResult, ghost old_net_history:seq<NetEvent>, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires rr.RRPacket?
  requires rr.cpacket.msg.CMessage_AppendEntriesReply?
  requires receive_event.LIoOpReceive?
  requires NetPacketIsAbstractable(receive_event.r)
  requires AbstractifyNetPacketToRaftPacket(receive_event.r) == AbstractifyCPacketToRaftPacket(rr.cpacket)
  // About server
  requires server_impl.state.role == Leader
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  // ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            && Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && (forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?)
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var msg := rr.cpacket.msg;
  // setup default return values
  net_event_log := [receive_event];
  ios := [receive_io];
  ok := true;

  // Check and update term
  if (server_impl.state.current_term < msg.term) {
    server_impl.state := server_impl.state.(
      current_term := msg.term, voted_for := None, role := Follower
    );
    reveal Q_RaftServer_Next_ProcessPacket();
      
    return;
  }
  
  var ep := rr.cpacket.src;
  if (ep !in server_impl.state.config.global_config.server_eps) {
    print "[Error] src of the packet not in cluster\n";
    ok := false;
    return;
  }

  if (server_impl.state.role == Leader && server_impl.state.current_term == msg.term) {
    if (msg.success == 1) {
      if (msg.match_index > MaxLogEntryIndex() as uint64 - 1) {
        print "[Error] match_index too large\n";
        ok := false;
        return;
      }
      if (msg.match_index + 1 > |server_impl.state.log| as uint64) {
        print "[Error] should not be\n";
        ok := false;
        return;
      }
      if (msg.match_index > server_impl.state.match_index[ep]) {
        server_impl.state := server_impl.state.(match_index := server_impl.state.match_index[ep := msg.match_index]);
      }
      server_impl.state := server_impl.state.(next_index := server_impl.state.next_index[ep := server_impl.state.match_index[ep] + 1]);
      // Update commit_index
      ok := server_impl.TryToIncreaseCommitIndexUntil(server_impl.state.match_index[ep]);
      if (!ok) { 
        print "[Error] TryToIncreaseCommitIndexUntil failed, ", server_impl.state.commit_index, "\n";
        ok := false;
        return;
      } else {
        print "[Info] Committed up to ", server_impl.state.commit_index, "\n";
      }
      assert (
        if msg.match_index > old(server_impl.state.match_index[ep]) then
          && server_impl.state.match_index == old(server_impl.state.match_index[ep := msg.match_index])
        else
          && server_impl.state.match_index == old(server_impl.state.match_index)
      );
      
      ghost var raft_server := old(server_impl.AbstractifyToRaftServer());
      ghost var raft_server' := server_impl.AbstractifyToRaftServer();
      ghost var raft_received_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
      ghost var raft_sent_packets := ExtractSentPacketsFromIos(ios);
      
      reveal ExtractSentPacketsFromIos();
      assert raft_sent_packets == [];

      reveal Q_RaftServer_Next_ProcessAppendEntriesReply();
      assert Q_RaftServer_Next_ProcessAppendEntriesReply(raft_server, raft_server', raft_received_packet, raft_sent_packets);
      reveal Q_RaftServer_Next_ProcessPacket();
      assert Q_RaftServer_Next_ProcessPacket(raft_server, raft_server', ios);
    } else {
      var decreased_index;
      if server_impl.state.next_index[ep] > LogEntrySeqSizeLimit() as uint64 {
        decreased_index := server_impl.state.next_index[ep] - LogEntrySeqSizeLimit() as uint64;
      } else {
        decreased_index := 1;
      }
      server_impl.state := server_impl.state.(
        match_index := server_impl.state.match_index[ep := 0], 
        next_index := server_impl.state.next_index[ep := decreased_index]
      );

      var ep_id := GetEndPointIndex(server_impl.state.config.global_config, ep);
      var packet := server_impl.PrepareAppendEntriesPacket(ep_id, false);
      var outbound_packet := OutboundPacket(Some(packet));
      ghost var log_tail, ios_tail;
      ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, outbound_packet);
      if (!ok) { return; }
      ios := ios + ios_tail;
      net_event_log := net_event_log + log_tail;
      assert net_event_log[0].LIoOpReceive?;
      assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
      assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
      assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
      assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;


      ghost var raft_server := old(server_impl.AbstractifyToRaftServer());
      ghost var raft_server' := server_impl.AbstractifyToRaftServer();
      ghost var raft_received_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
      ghost var raft_sent_packets := ExtractSentPacketsFromIos(ios);

      lemma_OnlySentPacketsLeft(ios, 1);
      assert ExtractSentPacketsFromIos(ios) == ExtractSentPacketsFromIos(ios_tail);

      reveal ExtractSentPacketsFromIos();
      assert |raft_sent_packets| == 1;
      assert raft_sent_packets[0].msg.RaftMessage_AppendEntries?;
      reveal Q_RaftServer_Next_ProcessAppendEntriesReply();
      assert Q_RaftServer_Next_ProcessAppendEntriesReply(raft_server, raft_server', raft_received_packet, raft_sent_packets);
      reveal Q_RaftServer_Next_ProcessPacket();
      assert Q_RaftServer_Next_ProcessPacket(raft_server, raft_server', ios);
    }
    reveal Q_RaftServer_Next_ProcessPacket();
    assert Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios);
  } else {
    reveal Q_RaftServer_Next_ProcessPacket();
    assert Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios);
  }
  reveal Q_RaftServer_Next_ProcessPacket();
  assert Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios);
}

//////////////////////////////////////////////////////////
// Process RequestVote
//////////////////////////////////////////////////////////
method {:timeLimitMultiplier 2} Server_HandleReqeustVote(server_impl:ServerImpl, rr:ReceiveResult, ghost old_net_history:seq<NetEvent>, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires rr.RRPacket?
  requires rr.cpacket.msg.CMessage_RequestVote?
  requires receive_event.LIoOpReceive?
  requires NetPacketIsAbstractable(receive_event.r)
  requires AbstractifyNetPacketToRaftPacket(receive_event.r) == AbstractifyCPacketToRaftPacket(rr.cpacket)
  // About server
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client, server_impl.state.random_generator
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
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

  var granted := 0;
  if (server_impl.state.current_term < msg.term) {
    server_impl.state := server_impl.state.(current_term := msg.term, voted_for := None, role := Follower);
  }

  if (server_impl.state.role == Leader || server_impl.state.role == Candidate) {
    return;
  }

  var my_last_log := server_impl.GetLastLogEntry();
  if (
    server_impl.state.current_term == msg.term
    && (server_impl.state.voted_for == None || server_impl.state.voted_for == Some(msg.candidate_id))
    && (msg.last_log_term > my_last_log.term || (msg.last_log_term == my_last_log.term && msg.last_log_index >= my_last_log.index))
  ){
    granted := 1;
    // reset election timeout before we do any change to server (to avoid proof)
    ghost var clock_event, clock_io := Server_ResetNextElectionTime(server_impl);
    assert my_last_log.index as int == |server_impl.state.log| - 1;
    assert server_impl.Valid();
    net_event_log := [receive_event, clock_event];
    ios := [receive_io, clock_io];
    assert net_event_log[0].LIoOpReceive?;
    assert net_event_log[1].LIoOpReadClock?;
    // update voted_for
    if (msg.candidate_id >= |server_impl.state.config.global_config.server_eps| as uint64) {
      if |server_impl.state.config.global_config.server_eps| == 3 {
        print server_impl.state.config.global_config.server_eps[0], "\n";
        print server_impl.state.config.global_config.server_eps[1], "\n";
        print server_impl.state.config.global_config.server_eps[2], "\n";
      }
      print "[Error] candidate_id(", msg.candidate_id, ") not in cluster\n";
      return;
    }
    server_impl.state := server_impl.state.(voted_for := Some(msg.candidate_id));
    server_impl.state := server_impl.state.(current_leader := Some(msg.candidate_id));
  }
  // send reply
  var reply_msg := CMessage_RequestVoteReply(server_impl.state.current_term, granted);
  var reply_packet := CPacket(rr.cpacket.src, server_impl.GetMyEp(), reply_msg);
  ghost var log_tail, ios_tail;
  ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, OutboundPacket(Some(reply_packet)));
  if (!ok) { return; }
  net_event_log := net_event_log + log_tail;
  ios := ios + ios_tail;
  assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
  assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
  assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
}

//////////////////////////////////////////////////////////
// Process RequestVoteReply
//////////////////////////////////////////////////////////
method {:timeLimitMultiplier 8} Server_HandleReqeustVoteReply(server_impl:ServerImpl, rr:ReceiveResult, ghost old_net_history:seq<NetEvent>, ghost receive_event:NetEvent) 
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  // About recved things
  requires receive_event.LIoOpReceive?
  requires rr.RRPacket?
  requires NetPacketIsAbstractable(receive_event.r)
  requires rr.cpacket.msg.CMessage_RequestVoteReply?
  requires AbstractifyCPacketToRaftPacket(rr.cpacket) == AbstractifyNetPacketToRaftPacket(receive_event.r)
  // About server
  requires server_impl.Valid()
  requires server_impl.Env().net.history() == old_net_history + [receive_event]
  requires CPacketIsSendable(rr.cpacket)
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env());
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
            && (
              || Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            )
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
  var msg := rr.cpacket.msg;
  // setup default return values
  ghost var ios_tail := [];
  ghost var log_tail := [];
  net_event_log := [receive_event];
  ios := [receive_io];
  ok := true;

  if (server_impl.state.current_term < msg.term) {
    server_impl.state := server_impl.state.(current_term := msg.term, voted_for := None, role := Follower);
  }

  var ep := rr.cpacket.src;
  
  if (server_impl.state.role == Candidate && server_impl.state.current_term == msg.term) {
    // Record the vote
    server_impl.state := server_impl.state.(vote_granted := server_impl.state.vote_granted[rr.cpacket.src := msg.vote_granted]);
    // Check for step up
    var passed:bool := server_impl.VoteRequestPassed();
    print "passed=", passed, "\n";
    if (passed) {
      print "election passed, become leader\n";
      server_impl.BecomeLeader();
      // Create packets
      var outbound_packets:seq<CPacket> := [];
      outbound_packets := Server_CreateAppendEntriesForAll(server_impl, true);
      assert |outbound_packets| <= |server_impl.state.config.global_config.server_eps| <= 0xFFFF_FFFF_FFFF_FFFF;
      assert (forall p :: p in outbound_packets ==> CPacketIsSendable(p));
      ok, log_tail, ios_tail := DeliverOutboundPackets(server_impl, PacketSequence(outbound_packets));
      if (!ok) { return; }
      ios := ios + ios_tail;
      net_event_log := net_event_log + log_tail;
      // print "I broadcast heartbeat!\n";
      assert forall i::0<=i<|log_tail| ==> AbstractifyNetEventToRaftIo(log_tail[i]) == ios_tail[i];
      assert forall i::0<=i<|log_tail| ==> log_tail[i].LIoOpSend? && ios_tail[i].LIoOpSend?;
      assert forall i :: 1 <= i < |net_event_log| ==> net_event_log[i].LIoOpSend?;
      assert forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?;
      assert server_impl.state.role == Leader;

      ghost var raft_server := old(server_impl.AbstractifyToRaftServer());
      ghost var raft_server' := server_impl.AbstractifyToRaftServer();
      ghost var raft_received_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
      ghost var raft_sent_packets := ExtractSentPacketsFromIos(ios);
      
      assert raft_received_packet.msg.RaftMessage_RequestVoteReply?;
      assert ios[0].r.msg.RaftMessage_RequestVoteReply?;

      reveal Q_RaftServer_Next_ProcessRequestVoteReply();
      assert Q_RaftServer_Next_ProcessRequestVoteReply(raft_server, raft_server', raft_received_packet, raft_sent_packets);
    } else {
    }
  }
  ghost var raft_server := old(server_impl.AbstractifyToRaftServer());
  ghost var raft_server' := server_impl.AbstractifyToRaftServer();
  ghost var raft_received_packet := AbstractifyCPacketToRaftPacket(rr.cpacket);
  ghost var raft_sent_packets := ExtractSentPacketsFromIos(ios);

  reveal Q_RaftServer_Next_ProcessRequestVoteReply();
  assert Q_RaftServer_Next_ProcessRequestVoteReply(raft_server, raft_server', raft_received_packet, raft_sent_packets);

  reveal Q_RaftServer_Next_ProcessPacket();
  assert Q_RaftServer_Next_ProcessPacket(raft_server, raft_server', ios);
}


//////////////////////////////////////////////////////////
// Process All Packet.
//////////////////////////////////////////////////////////
method Server_Next_ProcessPacketX(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires ConfigStateIsValid(server_impl.state.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client, server_impl.state.random_generator
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  // ensures server_impl.Env().Valid() && server_impl.Env().ok.ok() ==> ok
  ensures server_impl.Env() == old(server_impl.Env())
  ensures ok ==> 
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            // TOPROVE
            // && (|| Q_RaftServer_Next_ProcessPacket(old(server_impl.AbstractifyToRaftServer()), server_impl.AbstractifyToRaftServer(), ios)
            //     || (&& IosReflectIgnoringUnsendable(net_event_log)
            //        && old(server_impl.AbstractifyToRaftServer()) == server_impl.AbstractifyToRaftServer()))
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old(server_impl.Env().net.history()) + net_event_log == server_impl.Env().net.history()
            && forall i :: 0 <= i < |net_event_log| - 1 ==> net_event_log[i].LIoOpReceive? || net_event_log[i+1].LIoOpSend?
{
  ghost var old_net_history := server_impl.Env().net.history();

  var rr, receive_event := Receive(server_impl.net_client, server_impl.GetMyEp(), server_impl.state.config.global_config, server_impl.msg_grammar);
  
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
        print "server ", my_idx, "(", server_impl.state.current_term, ",is_leader=", server_impl.state.role.Leader?, ") received a request(", msg.seqno_req, ", ", msg.req, ")\n";
        ok, net_event_log, ios := Server_Next_ProcessRequest(server_impl, rr, old_net_history, receive_event);
      } else {
        return;
      }
    } else {
      assert msg.CMessage_AppendEntries? || msg.CMessage_AppendEntriesReply? || msg.CMessage_RequestVote? || msg.CMessage_RequestVoteReply?;
      // ignore outside packets for inside operations
      if (rr.cpacket.src !in server_impl.state.config.global_config.server_eps) {
        return;
      }
      var src_id := GetEndPointIndex(server_impl.state.config.global_config, rr.cpacket.src);
      // process the message
      if (msg.CMessage_AppendEntries?) {
        // ignore packet from self
        if (rr.cpacket.src == server_impl.GetMyEp()) {
          ok := true;
          return;
        }
        print "server ", my_idx, "(", server_impl.state.current_term, ",is_leader=", server_impl.state.role.Leader?, ",leader=", if server_impl.state.current_leader.Some? then server_impl.state.current_leader.v else 0xFFFF_FFFF_FFFF_FFFF, 
          ") received from ", src_id, "AppendEntries(|entries|=", |msg.entries|, ",prev_log_index=", msg.prev_log_index, ")\n";
        ok, net_event_log, ios := Server_HandleAppendEntries(server_impl, rr, old_net_history, receive_event);
      } else if (msg.CMessage_AppendEntriesReply?) {
        if (server_impl.state.role != Leader) {
          return;
        }
        print "server ", my_idx, "(", server_impl.state.current_term, ",is_leader=", server_impl.state.role.Leader?, ",leader=", if server_impl.state.current_leader.Some? then server_impl.state.current_leader.v else 0xFFFF_FFFF_FFFF_FFFF, 
          ") received from ", src_id, " AppendEntriesReply(term=", msg.term, ",success=", msg.success, ",match_index=", msg.match_index, ",commit=", server_impl.state.commit_index, ")\n";
        ok, net_event_log, ios := Server_HandleAppendEntriesReply(server_impl, rr, old_net_history, receive_event);
      } else if (msg.CMessage_RequestVote?) {
        print "server ", my_idx, "(", server_impl.state.current_term, ",is_leader=", server_impl.state.role.Leader?, ",leader=", if server_impl.state.current_leader.Some? then server_impl.state.current_leader.v else 0xFFFF_FFFF_FFFF_FFFF, ",commit=", server_impl.state.commit_index, ") received from ", src_id, " RequestVote(term=", msg.term, ")\n";
        ok, net_event_log, ios := Server_HandleReqeustVote(server_impl, rr, old_net_history, receive_event); 
      } else {
        assert msg.CMessage_RequestVoteReply?;
        print "server ", my_idx, "(", server_impl.state.current_term, ",is_leader=", server_impl.state.role.Leader?, ",leader=", if server_impl.state.current_leader.Some? then server_impl.state.current_leader.v else 0xFFFF_FFFF_FFFF_FFFF, ") received from ", src_id, " RequestVoteReply(term=", msg.term, ",granted=", msg.vote_granted, ")\n";
        ok, net_event_log, ios := Server_HandleReqeustVoteReply(server_impl, rr, old_net_history, receive_event);
        return;
      }
    }
  }
}

}
