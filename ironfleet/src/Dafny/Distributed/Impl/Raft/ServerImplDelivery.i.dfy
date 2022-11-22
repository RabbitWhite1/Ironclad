include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "CMessage.i.dfy"
include "CBroadcast.i.dfy"
include "ServerImpl.i.dfy"
include "NetRaft.i.dfy"
include "CTypes.i.dfy"
include "QRelations.i.dfy"
include "PacketParsing.i.dfy"
include "ServerImplLemmas.i.dfy"

module Raft__ServerImplDelivery_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Raft__CMessage_i
import opened Raft__Server_i
import opened Raft__NetRaft_i
import opened Raft__CTypes_i
import opened Raft__Types_i
import opened Raft__ServerImpl_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
import opened Common__Util_i
import opened Environment_s
import opened Raft__CBroadcast_i
import opened Raft__QRelations_i
import opened Raft__PacketParsing_i
import opened Raft__ServerImplLemmas_i

method DeliverPacket(r:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires r.Valid()
  requires packets.OutboundPacket?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.config.server_ep)
  modifies r.repr
  ensures r.repr == old(r.repr)
  ensures r.net_client != null
  ensures ok == NetClientOk(r.net_client)
  ensures r.Env() == old(r.Env())
  // TOPROVE
  // ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
          && forall i::0<=i<|netEventLog| ==> AbstractifyNetEventToRaftIo(netEventLog[i]) == ios[i]
          && forall i::0<=i<|netEventLog| ==> netEventLog[i].LIoOpSend? && ios[i].LIoOpSend?;
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacket(r.net_client, packets, r.local_addr);
  if (!ok) { return; }

  ios := MapSentPacketToIos(packets.p);
  lemma_MapSentPacketToIosExtractSentPacketsFromIosEquivalence(packets.p, ios);
  var end_time := Time.GetDebugTimeTicks();
  if packets.p.None? {
    RecordTimingSeq("DeliverPacketEmpty", start_time, end_time);
  } else {
    RecordTimingSeq("DeliverPacketSingleton", start_time, end_time);
  } 
}

method {:timeLimitMultiplier 2} DeliverPacketSequence(r:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires r.Valid()
  requires packets.PacketSequence?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.config.server_ep)
  modifies r.repr
  ensures r.repr == old(r.repr)
  ensures r.net_client != null
  ensures ok == NetClientOk(r.net_client)
  ensures r.Env() == old(r.Env())
  // TOPROVE
  // ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacketSequence(r.net_client, packets, r.local_addr);
  if (!ok) { return; }

  ios := MapSentPacketSeqToIos(packets.s);
  lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(packets, ios);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("DeliverPacketSequence", start_time, end_time);
}

method{:timeLimitMultiplier 2} DeliverBroadcast(r:ServerImpl, broadcast:CBroadcast) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires r.Valid()
  requires CBroadcastIsValid(broadcast)
  requires broadcast.CBroadcast? ==> broadcast.src == r.config.server_ep;
  modifies r.repr
  ensures r.repr == old(r.repr)
  ensures r.net_client != null
  ensures ok == NetClientOk(r.net_client)
  ensures r.Env() == old(r.Env())
  // TOPROVE
  // ensures r.replica == old(r.replica)
  ensures ok ==>
          && r.Valid()
          && r.nextActionIndex == old(r.nextActionIndex)
          && AllIosAreSends(ios)
          // && AbstractifyCBroadcastToRaftPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendBroadcast(r.net_client, broadcast, r.local_addr);
  if (!ok) { return; }

  ios := MapBroadcastToIos(broadcast);
  // lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast, ios);
    
  lemma_NetEventLogToBroadcastRefinable(netEventLog, broadcast);
  assert NetEventLogIsAbstractable(netEventLog);
  if broadcast.CBroadcastNop? {
    assert RawIoConsistentWithSpecIO(netEventLog, ios);
  } else {
    ghost var broadcast_ios := BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                 AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                 AbstractifyCMessageToRaftMessage(broadcast.msg));
    calc {
      AbstractifyRawLogToIos(netEventLog);
      {
        forall i | 0 <= i < |AbstractifyRawLogToIos(netEventLog)|
          ensures AbstractifyRawLogToIos(netEventLog)[i] == 
                    LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                                      AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                      AbstractifyCMessageToRaftMessage(broadcast.msg)))
        {
          calc {
            AbstractifyRawLogToIos(netEventLog)[i];
            AbstractifyNetEventToRaftIo(netEventLog[i]);
              { lemma_NetEventLogToBroadcast(netEventLog, broadcast, i); }
            LIoOpSend(AbstractifyCBroadcastToRaftPacketSeq(broadcast)[i]);
            LIoOpSend(BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                      AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                      AbstractifyCMessageToRaftMessage(broadcast.msg))[i]);
            LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                              AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyCMessageToRaftMessage(broadcast.msg)));
          }
        }
        forall i | 0 <= i < |broadcast_ios|
          ensures broadcast_ios[i] == LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                                                        AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                        AbstractifyCMessageToRaftMessage(broadcast.msg)))
        {
          calc {
            LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                              AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyCMessageToRaftMessage(broadcast.msg)));
            BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                              AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                              AbstractifyCMessageToRaftMessage(broadcast.msg))[i];
            broadcast_ios[i];
          }
          }
      }
      broadcast_ios;
      BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                        AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                        AbstractifyCMessageToRaftMessage(broadcast.msg));
      MapBroadcastToIos(broadcast);
      ios;
    }
    assert RawIoConsistentWithSpecIO(netEventLog, ios);
  }

  var end_time := Time.GetDebugTimeTicks();
  if broadcast.CBroadcastNop? || (broadcast.CBroadcast? && |broadcast.dsts| as uint64 == 0) {
    RecordTimingSeq("DeliverBroadcastEmpty", start_time, end_time);
  } else if broadcast.CBroadcast? && |broadcast.dsts| as uint64 == 1 {
    RecordTimingSeq("DeliverBroadcastSingleton", start_time, end_time);
  } else {
    RecordTimingSeq("DeliverBroadcastMany", start_time, end_time);
  }
}

method DeliverOutboundPackets(r:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires r.Valid()
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, r.config.server_ep);
  modifies r.repr
  ensures r.repr == old(r.repr)
  ensures r.net_client != null
  ensures ok == NetClientOk(r.net_client)
  ensures r.Env() == old(r.Env())
  // ensures r.replica == old(r.replica)
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && AllIosAreSends(ios)
            // && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
            && OnlySentMarshallableData(netEventLog)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(r.Env().net.history()) + netEventLog == r.Env().net.history()
{
  match packets {
    case Broadcast(broadcast) => ok, netEventLog, ios := DeliverBroadcast(r, broadcast);
    case OutboundPacket(p) => ok, netEventLog, ios := DeliverPacket(r, packets);
    case PacketSequence(s) => ok, netEventLog, ios := DeliverPacketSequence(r, packets);
  }
}

}
