/////////////////////////////////////////////////////////////////////////////
// The high-level specification is basically the same as IronRSL. Thus, we
// copied the useful infomation here.
//
// This is the specification for an abstract service that implements an
// application-defined state machine.  It provides linearizability of
// state-machine operations requested by clients.  That is, each operation
// the service executes appears to occur atomically, at a point after it
// was submitted by the client and before the service sent its response.
//
// Note that the specification does not require exactly-once semantics.
// If one needs exactly-once semantics, one should enforce that in the
// application state machine.  For instance, the state machine could keep
// track of the highest request sequence number seen from each client, and
// treat requests with older sequence numbers as no-ops.
//
/////////////////////////////////////////////////////////////////////////////

include "../../Common/Framework/AbstractService.s.dfy"
include "../../Common/Collections/Seqs.s.dfy"
include "AppStateMachine.s.dfy"

module AbstractServiceRaft_s refines AbstractService_s {
import opened AppStateMachine_s
import opened Collections__Seqs_s

datatype AppRequestMessage = AppRequestMessage(client:EndPoint, seqno:int, request:AppRequest)
datatype AppReplyMessage   = AppReplyMessage(client:EndPoint, seqno:int, reply:AppReply)

datatype ServiceState' = ServiceState'(
  serverAddresses:set<EndPoint>,
  app:AppState,
  requests:set<AppRequestMessage>,
  replies:set<AppReplyMessage>
  )

type ServiceState = ServiceState'

// Service Init
predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
  && s.serverAddresses == serverAddresses
  && s.app == AppInitialize()
  && s.requests == {}
  && s.replies == {}
}

// Service Next

predicate ServiceExecutesAppRequest(s:ServiceState, s':ServiceState, req:AppRequestMessage)
{
  && |req.request| <= MaxAppRequestSize()
  && s'.serverAddresses == s.serverAddresses
  && s'.requests == s.requests + { req }
  && s'.app == AppHandleRequest(s.app, req.request).0
  && s'.replies == s.replies + { AppReplyMessage(req.client, req.seqno, AppHandleRequest(s.app, req.request).1) }
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
  exists req:AppRequestMessage :: ServiceExecutesAppRequest(s, s', req)
}

// Marshalling
function Uint64ToBytes(u:uint64) : seq<byte>
{
  [( u/0x1000000_00000000)        as byte,
   ((u/  0x10000_00000000)%0x100) as byte,
   ((u/    0x100_00000000)%0x100) as byte,
   ((u/      0x1_00000000)%0x100) as byte,
   ((u/         0x1000000)%0x100) as byte,
   ((u/           0x10000)%0x100) as byte,
   ((u/             0x100)%0x100) as byte,
   ( u                    %0x100) as byte]
}

function MarshallServiceRequest(seqno:int, request:AppRequest) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 && |request| <= MaxAppRequestSize() then
    [0, 0, 0, 0, 0, 0, 0, 0]
    + Uint64ToBytes(seqno as uint64)
    + Uint64ToBytes(|request| as uint64)
    + request
  else
    [1]
}

function MarshallServiceReply(seqno:int, reply:AppReply) : seq<byte>
{
  if 0 <= seqno < 0x1_0000_0000_0000_0000 && |reply| <= MaxAppReplySize() then
    [0, 0, 0, 0, 0, 0, 0, 6 ]
    + Uint64ToBytes(seqno as uint64)
    + Uint64ToBytes(|reply| as uint64)
    + reply
  else
    [1]
}

// Note: this indicates how each packet(in concretePkts) can affect serviceState
predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState)
{
  // every reply should be recorded in serviceState.replies
  && forall packet, seqno, reply :: 
    packet in concretePkts 
    && packet.src in serviceState.serverAddresses 
    && packet.msg == MarshallServiceReply(seqno, reply) 
    ==>
    AppReplyMessage(packet.dst, seqno, reply) in serviceState.replies
  // every request in serviceState.requests should be a packet sent to service
  && forall request :: request in serviceState.requests ==>
    exists packet :: 
      packet in concretePkts 
      && packet.src in serviceState.serverAddresses 
      && packet.dst == request.client 
      && packet.msg == MarshallServiceRequest(request.seqno, request.request)


    
}
}