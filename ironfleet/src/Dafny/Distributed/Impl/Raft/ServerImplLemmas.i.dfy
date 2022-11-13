include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "ServerImpl.i.dfy"
include "NetRaft.i.dfy"
include "CTypes.i.dfy"
include "CBroadcast.i.dfy"
include "QRelations.i.dfy"
include "CMessage.i.dfy"
include "PacketParsing.i.dfy"

module Raft__ServerImplLemmas_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Raft__CTypes_i
import opened Raft__CBroadcast_i
import opened Raft__CMessage_i
import opened Raft__Types_i
import opened Raft__PacketParsing_i
import opened Raft__ServerImpl_i
import opened Raft__Server_i
import opened Raft__NetRaft_i
import opened Raft__QRelations_i
import opened Common__NodeIdentity_i
import opened Concrete_NodeIdentity_i
import opened Logic__Option_i
import opened Environment_s


function MapSentPacketToIos(sent_packet:Option<CPacket>) : seq<RaftIo>
  requires OutboundPacketsIsValid(OutboundPacket(sent_packet))
{
  match sent_packet {
    case Some(p) => [LIoOpSend(AbstractifyCPacketToRaftPacket(p))]
    case None => []
  }
}

lemma lemma_MapSentPacketToIosExtractSentPacketsFromIosEquivalence(sent_packet:Option<CPacket>, ios:seq<RaftIo>)
  requires OutboundPacketsIsValid(OutboundPacket(sent_packet))
  requires ios == MapSentPacketToIos(sent_packet)
  ensures AbstractifyOutboundCPacketsToSeqOfRaftPackets(OutboundPacket(sent_packet)) == ExtractSentPacketsFromIos(ios)
{
  reveal ExtractSentPacketsFromIos();
}

function {:opaque} BuildBroadcastIos(src:NodeIdentity, dsts:seq<NodeIdentity>, msg:RaftMessage) : seq<RaftIo>
  ensures |BuildBroadcastIos(src, dsts, msg)| == |dsts|
  ensures forall i :: 0<=i<|dsts| ==> BuildBroadcastIos(src, dsts, msg)[i] == LIoOpSend(LPacket(dsts[i], src, msg))
{
  if |dsts| == 0 then []
  else [ LIoOpSend(LPacket(dsts[0], src, msg)) ] + BuildBroadcastIos(src, dsts[1..], msg)
}

function MapBroadcastToIos(broadcast:CBroadcast) : seq<RaftIo>
  requires CBroadcastIsAbstractable(broadcast)
{
  match broadcast
    case CBroadcast(_,_,_) => BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
                                                AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
                                                AbstractifyCMessageToRaftMessage(broadcast.msg))
    case CBroadcastNop => []
}

lemma lemma_NetEventLogToBroadcast(netEventLog:seq<NetEvent>, broadcast:CBroadcast, index:int)
  requires CBroadcastIsValid(broadcast)
  requires broadcast.CBroadcast?
  requires 0 <= index < |netEventLog|
  requires SendLogReflectsBroadcast(netEventLog, broadcast)
  ensures  netEventLog[index].LIoOpSend?
  ensures  NetPacketIsAbstractable(netEventLog[index].s)
  ensures  AbstractifyNetPacketToRaftPacket(netEventLog[index].s) == AbstractifyCBroadcastToRaftPacketSeq(broadcast)[index]
{
  calc ==> {
    true;
    SendLogReflectsBroadcast(netEventLog, broadcast);
    SendLogReflectsBroadcastPrefix(netEventLog, broadcast);
    SendLogMatchesRefinement(netEventLog, broadcast, index);
    netEventLog[index].LIoOpSend? && NetPacketIsAbstractable(netEventLog[index].s)
      && AbstractifyCBroadcastToRaftPacketSeq(broadcast)[index] == AbstractifyNetPacketToRaftPacket(netEventLog[index].s);
  }
}

lemma lemma_NetEventLogToBroadcastRefinable(netEventLog:seq<NetEvent>, broadcast:CBroadcast)
  requires CBroadcastIsValid(broadcast)
  requires SendLogReflectsBroadcast(netEventLog, broadcast)
  ensures  NetEventLogIsAbstractable(netEventLog)
{
  if broadcast.CBroadcastNop? {
    assert netEventLog == [];
  } else {
    forall i | 0 <= i < |netEventLog|
      ensures NetEventIsAbstractable(netEventLog[i])
    {
      lemma_NetEventLogToBroadcast(netEventLog, broadcast, i);
    }
  }
}

lemma lemma_ExtractSentPacketsFromIos(ios:seq<RaftIo>)
  requires AllIosAreSends(ios)
  ensures  |ExtractSentPacketsFromIos(ios)| == |ios|
  ensures  forall i {:auto_trigger} :: 0 <= i < |ios| ==> ExtractSentPacketsFromIos(ios)[i] == ios[i].s
{
  reveal ExtractSentPacketsFromIos();
}

lemma lemma_MapBroadcastToIosExtractSentPacketsFromIosEquivalence(broadcast:CBroadcast, ios:seq<RaftIo>)
  requires CBroadcastIsAbstractable(broadcast)
  requires ios == MapBroadcastToIos(broadcast)
  requires AllIosAreSends(ios)
  // ensures  AbstractifyCBroadcastToRaftPacketSeq(broadcast) == ExtractSentPacketsFromIos(ios)
{
  reveal ExtractSentPacketsFromIos();

  if broadcast.CBroadcastNop? {

  } else {
    // TOPROVE
    // forall i | 0 <= i < |broadcast.dsts|
    //   ensures AbstractifyCBroadcastToRaftPacketSeq(broadcast)[i] == ExtractSentPacketsFromIos(ios)[i]
    // {
    //   calc {
    //     AbstractifyCBroadcastToRaftPacketSeq(broadcast)[i];
    //     BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src), 
    //                     AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
    //                     AbstractifyCMessageToRaftMessage(broadcast.msg))[i];
    //     LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
    //             AbstractifyEndPointToNodeIdentity(broadcast.src), 
    //             AbstractifyCMessageToRaftMessage(broadcast.msg));

    //     calc {
    //       LIoOpSend(LPacket(AbstractifyEndPointsToNodeIdentities(broadcast.dsts)[i], 
    //                         AbstractifyEndPointToNodeIdentity(broadcast.src),
    //                         AbstractifyCMessageToRaftMessage(broadcast.msg)));
    //       BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
    //                         AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
    //                         AbstractifyCMessageToRaftMessage(broadcast.msg))[i];
    //     }
    //       { lemma_ExtractSentPacketsFromIos(ios); }
    //     ExtractSentPacketsFromIos(BuildBroadcastIos(AbstractifyEndPointToNodeIdentity(broadcast.src), 
    //                                                 AbstractifyEndPointsToNodeIdentities(broadcast.dsts), 
    //                                                 AbstractifyCMessageToRaftMessage(broadcast.msg)))[i];
    //     ExtractSentPacketsFromIos(ios)[i];
    //   }
    // }

    calc {
      |AbstractifyCBroadcastToRaftPacketSeq(broadcast)|;
      |broadcast.dsts|;
      |ios|;
        { lemma_ExtractSentPacketsFromIos(ios); }
      |ExtractSentPacketsFromIos(ios)|;
    }
  }
}
    
function {:opaque} MapSentPacketSeqToIos(sent_packets:seq<CPacket>) : seq<RaftIo>
  requires OutboundPacketsIsValid(PacketSequence(sent_packets))
  requires OutboundPacketsIsAbstractable(PacketSequence(sent_packets))
  ensures |MapSentPacketSeqToIos(sent_packets)| == |sent_packets|
  ensures forall i :: 0 <= i < |sent_packets| ==> MapSentPacketSeqToIos(sent_packets)[i] == LIoOpSend(AbstractifyCPacketToRaftPacket(sent_packets[i]))
{
  //lemma_MapSentPacketSeqToIos(sent_packets);
  if |sent_packets| == 0 then
  []
  else if |sent_packets| == 1 then
    [LIoOpSend(AbstractifyCPacketToRaftPacket(sent_packets[0]))]
  else
    [LIoOpSend(AbstractifyCPacketToRaftPacket(sent_packets[0]))] + MapSentPacketSeqToIos(sent_packets[1..])
}
lemma {:timeLimitMultiplier 3} lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(sent_packets:OutboundPackets, ios:seq<RaftIo>)
  requires sent_packets.PacketSequence?
  requires OutboundPacketsIsValid(sent_packets)
  requires OutboundPacketsIsAbstractable(sent_packets)
  requires ios == MapSentPacketSeqToIos(sent_packets.s)
  requires forall i :: 0 <= i < |sent_packets.s| ==> CPacketIsSendable(sent_packets.s[i])
  ensures AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios)
  decreases |ios|
{
  assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == AbstractifySeqOfCPacketsToSeqOfRaftPackets(sent_packets.s);
  reveal ExtractSentPacketsFromIos();
  //assert |AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets)| == |ExtractSentPacketsFromIos(ios)|;
  reveal MapSentPacketSeqToIos();
  if (|ios| == 0) {
    assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  } else if (|ios| == 1) {
    assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  } else {
    if (ios[0].LIoOpSend?) {
      var one := ios[0];
      var rest := PacketSequence(sent_packets.s[1..]);
      assert ExtractSentPacketsFromIos(ios) == [ios[0].s] + ExtractSentPacketsFromIos(ios[1..]);
            
      lemma_MapSentPacketSeqToIosExtractSentPacketsFromIosEquivalence(rest, ios[1..]);
      reveal AbstractifySeqOfCPacketsToSeqOfRaftPackets();
      assert {:split_here} true;
      calc {
        AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets);
        AbstractifySeqOfCPacketsToSeqOfRaftPackets(sent_packets.s);
        [ios[0].s] + AbstractifyOutboundCPacketsToSeqOfRaftPackets(rest);
        [ios[0].s] + ExtractSentPacketsFromIos(ios[1..]);
        ExtractSentPacketsFromIos(ios);
      }

    } else {
      assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    }
    assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
  }
  //forall i | 0 <= i < |AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets)|
  //    ensures AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets)[i] == ExtractSentPacketsFromIos(ios)[i];
  //{
  //}
  assert AbstractifyOutboundCPacketsToSeqOfRaftPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
}

}