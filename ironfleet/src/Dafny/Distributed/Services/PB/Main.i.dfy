include "../../Common/Framework/Main.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "PBDistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/PB/PacketParsing.i.dfy"
include "../../Impl/PB/NetPB.i.dfy"
include "../../Impl/PB/Host.i.dfy"
include "AbstractService.s.dfy"
include "../../Protocol/PB/RefinementProof/Refinement.i.dfy"
include "../../Protocol/PB/RefinementProof/RefinementProof.i.dfy"
include "Marshall.i.dfy"

module Main_i refines Main_s {
    import opened DS_s = PB_DistributedSystem_i
    import opened Environment_s

    lemma RefinementProof(config:DS_s.H_s.ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
        /*
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
        */
    {
        // TODO
    }
    
}
