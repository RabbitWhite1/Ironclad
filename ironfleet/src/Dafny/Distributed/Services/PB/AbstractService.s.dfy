include "../../Common/Framework/AbstractService.s.dfy"

module AbstractServiceLock_s refines AbstractService_s {
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides ServiceState 
    provides Service_Init, Service_Next, Service_Correspondence
export All reveals *

datatype ServiceState' = ServiceState'(
    hosts:set<EndPoint>,
    value:int
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.hosts == serverAddresses
    && s.value == 0

}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
       s'.hosts == s.hosts
    && s'.value == s.value + 1
}

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

function MarshallPBMsg(value:int) : seq<byte>
{
  if 0 <= value < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 1] // MarshallMesssage_Request magic number
      + Uint64ToBytes(value as uint64)        
  else 
      [ 1 ]
}

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
    // TODO
    true
}

}
