include "../../Common/Native/Io.s.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../../Protocol/Raft/Server.i.dfy"
include "../Common/NetClient.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "Config.i.dfy"
include "CMessage.i.dfy"
include "PacketParsing.i.dfy"

module Raft__CBroadcast_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Common__NetClient_i
import opened Common__NodeIdentity_i
import opened Raft__Types_i
import opened Raft__ConfigState_i
import opened Raft__CMessage_i
import opened Raft__PacketParsing_i
import opened Raft__Server_i

// CBroadcast
method BuildBroadcastToEveryone(config:ConfigState, my_ep:EndPoint, msg:CMessage) returns (broadcast:CBroadcast)
  requires ConfigStateIsValid(config)
  requires my_ep in config.server_eps
  requires CMessageIsAbstractable(msg)
  requires Marshallable(msg)
  ensures CBroadcastIsValid(broadcast)
  ensures OutboundPacketsHasCorrectSrc(Broadcast(broadcast), my_ep)
  ensures RaftBroadcastToEveryone(AbstractifyConfigStateToRaftConfig(config), my_ep, AbstractifyCMessageToRaftMessage(msg), AbstractifyCBroadcastToRaftPacketSeq(broadcast))
{
  broadcast := CBroadcast(my_ep, config.server_eps, msg);
}

}