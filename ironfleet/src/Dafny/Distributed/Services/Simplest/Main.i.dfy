include "AbstractService.s.dfy"
include "SimplestDistributedSystem.i.dfy"
include "../../Common/Framework/Main.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.s.dfy"

module Main_i refines Main_s {
import opened AS_s = AbstractServiceSimplest_s`All
import opened DS_s = Simplest_DistributedSystem_i
import opened Environment_s
import opened Concrete_NodeIdentity_i
import opened Collections__Sets_i
export
    provides DS_s, Native__Io_s, Native__NativeTypes_s
    provides IronfleetMain

lemma {:timeLimitMultiplier 2} RefinementToServiceState(config:DS_s.H_s.ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
  requires |db| > 0
  ensures |sb| == |db|;
  ensures Service_Init(sb[0], MapSeqToSet(config, x=>x));
  ensures forall i :: 0 <= i < |sb| ==> sb[i] == sb[0];
  ensures forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
{
  if |db| == 1 {
    sb := [ServiceState'(MapSeqToSet(config, x=>x))];
  } else {
    var rest := RefinementToServiceState(config, all_but_last(db));
    var last := last(db);
    sb := rest + [ServiceState'(MapSeqToSet(config, x=>x))];
  }
}

lemma RefinementProof(config:DS_s.H_s.ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
{
  sb := RefinementToServiceState(config, db);
  forall i | 0 <= i < |db|
    ensures Service_Correspondence(db[i].environment.sentPackets, sb[i]);
  {}
}

}
