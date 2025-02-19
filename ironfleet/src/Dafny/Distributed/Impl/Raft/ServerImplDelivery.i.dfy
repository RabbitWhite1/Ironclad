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

method DeliverPacket(server_impl:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires packets.OutboundPacket?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsHasCorrectSrc(packets, server_impl.GetMyEp())
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.state == old(server_impl.state)
  ensures ok ==>
          && server_impl.Valid()
          && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
          && (forall i::0<=i<|netEventLog| ==> AbstractifyNetEventToRaftIo(netEventLog[i]) == ios[i])
          && (forall i::0<=i<|netEventLog| ==> netEventLog[i].LIoOpSend? && ios[i].LIoOpSend?)
          && (packets.p.Some? ==> |netEventLog| == 1 && |ios| == 1)
          && (packets.p.None? ==> |netEventLog| == 0 && |ios| == 0)
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacket(server_impl.net_client, packets, server_impl.local_addr);
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

method {:timeLimitMultiplier 2} DeliverPacketSequence(server_impl:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires packets.PacketSequence?
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, server_impl.GetMyEp())
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.state == old(server_impl.state)
  ensures ok ==>
          && server_impl.Valid()
          && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
{
  var start_time := Time.GetDebugTimeTicks();
  ok, netEventLog := SendPacketSequence(server_impl.net_client, packets, server_impl.local_addr);
  if (!ok) { return; }

  ios := MapSentPacketSeqToIos(packets.s);
  lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(packets, ios);
  var end_time := Time.GetDebugTimeTicks();
  RecordTimingSeq("DeliverPacketSequence", start_time, end_time);
}

lemma lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast:CBroadcast, ios:seq<RaftIo>)
  requires CBroadcastIsAbstractable(broadcast)
  requires ios == MapBroadcastToIos(broadcast)
  requires AllIosAreSends(ios)
  ensures  AbstractifyCBroadcastToRaftPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
{
  // reveal ExtractSentPacketsFromIos();

  if broadcast.CBroadcastNop? {

  } else {
    calc {
      |AbstractifyCBroadcastToRaftPacketSeq(broadcast)|;
      |broadcast.dsts|;
      |ios|;
        { lemma_ExtractSentPacketsFromIos(ios); }
      |ExtractSentPacketsFromIos(ios)|;
    }

    forall i | 0 <= i < |broadcast.dsts|
      ensures AbstractifyCBroadcastToRaftPacketSeq(broadcast)[i] == ExtractSentPacketsFromIos(ios)[i]
    {
      calc {
        AbstractifyCBroadcastToRaftPacketSeq(broadcast)[i];
        BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                        AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                        AbstractifyCMessageToRaftMessage(broadcast.msg))[i];
        LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                AbstractifyEndPointToNodeIdentity(broadcast.src), 
                AbstractifyCMessageToRaftMessage(broadcast.msg));

        calc {
          LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
                            AbstractifyEndPointToNodeIdentity(broadcast.src),
                            AbstractifyCMessageToRaftMessage(broadcast.msg)));
          BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                            AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                            AbstractifyCMessageToRaftMessage(broadcast.msg))[i];
        }
          { lemma_ExtractSentPacketsFromIos(ios); }
        ExtractSentPacketsFromIos(BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                    AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                    AbstractifyCMessageToRaftMessage(broadcast.msg)))[i];
        ExtractSentPacketsFromIos(ios)[i];
      }
    }
  }
}

method{:timeLimitMultiplier 2} DeliverBroadcast(server_impl:ServerImpl, broadcast:CBroadcast) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires CBroadcastIsValid(broadcast)
  requires broadcast.CBroadcast? ==> broadcast.src == server_impl.GetMyEp();
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.state == old(server_impl.state)
  ensures ok ==>
          && server_impl.Valid()
          && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
          && AllIosAreSends(ios)
          && AbstractifyCBroadcastToRaftPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
          && OnlySentMarshallableData(netEventLog)
          && RawIoConsistentWithSpecIO(netEventLog, ios)
          && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
{
  ok, netEventLog := SendBroadcast(server_impl.net_client, broadcast, server_impl.local_addr);
  if (!ok) { return; }

  ios := MapBroadcastToIos(broadcast);
  lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast, ios);
    
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
}

method DeliverOutboundPackets(server_impl:ServerImpl, packets:OutboundPackets) returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<RaftIo>)
  requires server_impl.Valid()
  requires OutboundPacketsIsValid(packets)
  requires OutboundPacketsIsAbstractable(packets)
  requires OutboundPacketsHasCorrectSrc(packets, server_impl.GetMyEp());
  modifies server_impl.repr
  ensures server_impl.repr == old(server_impl.repr)
  ensures server_impl.net_client != null
  ensures ok == NetClientOk(server_impl.net_client)
  ensures server_impl.Env() == old(server_impl.Env())
  ensures server_impl.state == old(server_impl.state)
  ensures ok ==>
            && server_impl.Valid()
            && server_impl.nextActionIndex == old(server_impl.nextActionIndex)
            && AllIosAreSends(ios)
            && AbstractifyOutboundCPacketsToSeqOfRaftPackets(packets) == ExtractSentPacketsFromIos(ios)
            && OnlySentMarshallableData(netEventLog)
            && RawIoConsistentWithSpecIO(netEventLog, ios)
            && OnlySentMarshallableData(netEventLog)
            && old(server_impl.Env().net.history()) + netEventLog == server_impl.Env().net.history()
            && (packets.OutboundPacket? ==> if packets.p.Some? then |netEventLog| == |ios| == 1 else |netEventLog| == |ios| == 0)
{
  match packets {
    case Broadcast(broadcast) => ok, netEventLog, ios := DeliverBroadcast(server_impl, broadcast);
    case OutboundPacket(p) => ok, netEventLog, ios := DeliverPacket(server_impl, packets);
    case PacketSequence(s) => ok, netEventLog, ios := DeliverPacketSequence(server_impl, packets);
  }
}

}
