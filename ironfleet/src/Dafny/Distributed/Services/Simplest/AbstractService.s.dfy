include "../../Common/Framework/AbstractService.s.dfy"

module AbstractServiceSimplest_s refines AbstractService_s {
export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s
    provides ServiceState 
    provides Service_Init, Service_Next, Service_Correspondence
export All reveals *

datatype ServiceState' = ServiceState'(
    hosts:set<EndPoint>
)

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
  s.hosts == serverAddresses
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
  s'.hosts == s.hosts
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

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
  true
}

}
