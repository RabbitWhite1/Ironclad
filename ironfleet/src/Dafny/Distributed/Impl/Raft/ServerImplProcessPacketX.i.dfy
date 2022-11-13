include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/UpperBound.i.dfy"
include "CMessage.i.dfy"
include "Config.i.dfy"
include "CTypes.i.dfy"
include "NetRaft.i.dfy"
include "PacketParsing.i.dfy"
include "QRelations.i.dfy"
include "ServerImpl.i.dfy"
// include "NetRSL.i.dfy"

module Raft__ServerImplProcessPacketX_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Common__NetClient_i
import opened Common__UpperBound_i
import opened Environment_s
import opened Raft__ConfigState_i
import opened Raft__CTypes_i
import opened Raft__CMessage_i
import opened Raft__NetRaft_i
import opened Raft__PacketParsing_i
import opened Raft__QRelations_i
import opened Raft__ServerImpl_i
import opened Raft__Types_i

method Server_Next_ProcessPacketX(server_impl:ServerImpl)
  returns (ok:bool, ghost net_event_log:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires ConfigStateIsValid(server_impl.config.global_config)
  modifies server_impl, server_impl.repr, server_impl.net_client;
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
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
    if !marshallable {
      ok := true;
      ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
      net_event_log := [receive_event];
      ios := [receive_io];
    } else if (rr.cpacket.msg.CMessage_AppendEntries?) {
      ok := true;
      var const_params := server_impl.config.global_config.params;
      var clock, clock_event := ReadClock(server_impl.net_client);
      var election_timeout_delta := GenerateElectionTimeout(const_params);
      var next_election_time := UpperBoundedAdditionImpl(clock.t, election_timeout_delta, const_params.max_integer_value);
      server_impl.next_election_time := next_election_time;
      ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
      ghost var clock_io := LIoOpReadClock(clock.t as int);
      net_event_log := [receive_event, clock_event];
      ios := [receive_io, clock_io];
      assert net_event_log[0].LIoOpReceive?;
      assert net_event_log[1].LIoOpReadClock?;
    } else {
      ok := true;
      ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRaftPacket(receive_event.r));
      net_event_log := [receive_event];
      ios := [receive_io];
    }
  }
}

}
