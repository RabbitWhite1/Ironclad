include "Node.i.dfy"
include "NetPB.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module NodeImpl_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Environment_s
import opened Types_i
import opened Message_i
import opened Impl_Node_i
import opened NetPB_i
import opened Protocol_Node_i
import opened Common__Util_i
import opened Common__NetClient_i
import opened Logic__Option_i

class NodeImpl
{
    var node:CNode;
    var netClient:NetClient?;
    var localAddr:EndPoint;

    ghost var Repr : set<object>;

    constructor () {
        netClient := null;
    }

    predicate Valid()
        reads this;
        reads NetClientIsValid.reads(netClient);
    {
           CNodeValid(node)
        && NetClientIsValid(netClient)
        && EndPoint(netClient.MyPublicKey()) == localAddr
        && localAddr == node.config[node.my_index]
        && Repr == { this } + NetClientRepr(netClient)
    }
        
    function Env() : HostEnvironment?
        reads this, NetClientIsValid.reads(netClient);
    {
        if netClient!=null then netClient.env else null
    }

    method InitNode(config:Config, my_index:uint64, nc:NetClient, ghost env_:HostEnvironment) returns (ok:bool)
        requires env_.Valid() && env_.ok.ok()
        requires ValidConfig(config) && ValidConfigIndex(config, my_index)
        requires NetClientIsValid(nc)
        requires EndPoint(nc.MyPublicKey()) == config[my_index]
        requires nc.env == env_
        modifies this
        ensures ok ==>
               Valid()
            && Env() == env_
            && NodeInit(AbstractifyCNode(node), my_index as int, config)
            && node.config == config 
            && node.my_index == my_index
    {
        netClient := nc;
        node := NodeInitImpl(my_index, config);
        assert node.my_index == my_index;
        localAddr := node.config[my_index];
        Repr := { this } + NetClientRepr(netClient);
        ok := true;
    }

    method NodeNextSend() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<PBIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeSend(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(netEventLog) == ios
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var packets;
        node, packets, ios := NodeSendImpl(node);
        ok := true;

        netEventLog := [];
        if packets.Some? {
            ghost var sendEventLog;
            for i := 0 to |packets| - 1 {
                ok, sendEventLog := SendPacket(netClient, Some(packets[i]), localAddr); 
                netEventLog := netEventLog + sendEventLog;
            }
        } else {
            netEventLog := [];
            assert AbstractifyRawLogToIos(netEventLog) == ios;
        }
    }

    method NodeNextRecv() returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<PBIo>)
        requires Valid();
        modifies Repr;
        ensures Repr == old(Repr);
        ensures ok == NetClientOk(netClient);
        ensures Env() == old(Env());
        ensures ok ==> (
               Valid()
            && NodeRecv(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
            && AbstractifyRawLogToIos(netEventLog) == ios
            && OnlySentMarshallableData(netEventLog)
            && old(Env().net.history()) + netEventLog == Env().net.history());
    {
        var rr;
        ghost var receiveEvent;
        rr, receiveEvent := Receive(netClient, localAddr);

        netEventLog := [ receiveEvent ];
        if (rr.RRFail?) {
            ok := false;
            return;
        } else if (rr.RRTimeout?) {
            ok := true;
            ios := [ LIoOpTimeoutReceive() ];
            return;
        } else {
            ok := true;
            node, ios := NodeRecvImpl(node, rr.cpacket);
        }
    }


    method HostNextMain()
        returns (ok:bool, ghost netEventLog:seq<NetEvent>, ghost ios:seq<PBIo>)
        requires Valid();
        modifies Repr;
        ensures  Repr == old(Repr);
        ensures  ok <==> Env() != null && Env().Valid() && Env().ok.ok();
        ensures  Env() == old(Env());
        ensures  ok ==> (
                   Valid()
                && NodeNext(old(AbstractifyCNode(node)), AbstractifyCNode(node), ios)
                && AbstractifyRawLogToIos(netEventLog) == ios
                && OnlySentMarshallableData(netEventLog)
                && old(Env().net.history()) + netEventLog == Env().net.history()
                );
    {
        if node.is_primary {
            ok, netEventLog, ios := NodeNextSend();
        } else {
            ok, netEventLog, ios := NodeNextRecv();
        }
    }
}

} 
