include "../../Impl/Raft/Host.i.dfy"
include "../../Common/Framework/DistributedSystem.s.dfy"

module Raft_DistributedSystem_i refines DistributedSystem_s {

    import H_s = Host_i`All

}
