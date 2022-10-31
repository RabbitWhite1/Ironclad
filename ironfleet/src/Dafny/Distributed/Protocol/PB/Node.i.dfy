include "Types.i.dfy"

module Protocol_Node_i {
import opened Types_i
import opened Native__Io_s

type Config = seq<EndPoint>

datatype Node = Node(is_primary:bool, value:int, my_index:int, config:Config)

predicate NodeInit(s:Node, my_index:int, config:Config)
{
 && 0 <= my_index < |config|
 && s.my_index == my_index // change
 && s.is_primary == (my_index == 0)
 && s.config == config
}

predicate NodeSend(s:Node, s':Node, ios:seq<PBIo>)
{
    s.my_index == s'.my_index
    &&  if s.is_primary then
            |ios| == |s.config| - 1 
            && |s.config| > 0
            && s'.config == s.config
            && s'.value == s.value
            && forall index :: 0 <= index < |s.config| && index != s.my_index ==> (
                exists packet ::
                    packet in ios && packet.LIoOpSend?
                && packet.s.dst == s.config[index]
                && packet.s.msg.Update?
                && packet.s.msg.value == s.value)
        else
            s == s' && ios == []
}

predicate NodeRecv(s:Node, s':Node, ios:seq<PBIo>)
{
    s.my_index == s'.my_index
    && |ios| >= 1
    && if s.is_primary then
        if ios[0].LIoOpTimeoutReceive? then
            s == s' && |ios| == 1 // why?
        else
            ios[0].LIoOpReceive?
            && ios[0].r.src in s.config
            && ios[0].r.msg.Update?
            && ios[0].r.msg.value >= s.value
    else
        s == s' && |ios| >= 1
}

predicate NodeNext(s:Node, s':Node, ios:seq<PBIo>)
{
    NodeRecv(s, s', ios) || NodeSend(s, s', ios)
}

}
