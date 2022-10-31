include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Types_i {
import opened Environment_s
import opened Native__Io_s

datatype PBMessage = Update(value:int) | Invalid

type PBEnvironment = LEnvironment<EndPoint, PBMessage>
type PBPacket = LPacket<EndPoint, PBMessage>
type PBIo = LIoOp<EndPoint, PBMessage>

}
