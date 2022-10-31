include "../../Protocol/PB/Types.i.dfy"

module Message_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened Types_i

datatype CMessage = CUpdate(value:uint64) | CInvalid

function AbstractifyCMessage(cmsg:CMessage) : PBMessage
{
    match cmsg {
        case CUpdate(value) => Update(value as int)
        case CInvalid         => Invalid()
    }
}

type CPBPacket = LPacket<EndPoint, CMessage>

function AbstractifyCPBPacket(p:CPBPacket) : PBPacket
{
    LPacket(p.dst, p.src, AbstractifyCMessage(p.msg))
}

}
