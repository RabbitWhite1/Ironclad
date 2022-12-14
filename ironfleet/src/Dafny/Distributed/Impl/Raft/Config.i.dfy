include "../../Common/Native/Io.s.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Collections/Maps2.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../Common/SeqIsUniqueDef.i.dfy"
include "../Common/UpperBound.i.dfy"
include "../Common/NetClient.i.dfy"
include "../../Protocol/Raft/Config.i.dfy"

module Raft__ConfigState_i {

import opened Common__UpperBound_s
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Sets_i
import opened Collections__Seqs_i
import opened Collections__Maps2_s
import opened Common__SeqIsUniqueDef_i
import opened Common__NetClient_i
import opened Raft__Config_i

datatype ParamState = ParamState(
  min_election_timeout:uint64,
  max_election_timeout:uint64,
  heartbeat_timeout:uint64,
  max_integer_value:uint64
)

predicate ParamStateIsValid(params:ParamState)
{
  && 0 < params.min_election_timeout < params.max_election_timeout
  && params.heartbeat_timeout > 0
  && params.max_integer_value > 0
}

method GenerateElectionTimeout(params:ParamState) returns (t:uint64)
  requires ParamStateIsValid(params)
  ensures params.min_election_timeout <= t <= params.max_election_timeout
{
  t := params.min_election_timeout;
}

class RandomGenerator {
  var next:uint64
  constructor (seed:uint64)
    ensures this.next == seed
  {
    this.next := seed;
  }
  method Next() returns (n:uint64)
    modifies this
    ensures n == this.next
  {
    if (this.next > 0xFFFF_FFFF_FFFF_FFFF / 1103515245) {
      this.next := this.next % (0xFFFF_FFFF_FFFF_FFFF / 1103515245);
    }
    this.next := this.next * 1103515245 + 123456;
    n := this.next;
  }
  method NextInt(min:uint64, max:uint64) returns (n:uint64)
    requires 0 <= min <= max
    modifies this
    ensures min <= n <= max
  {
    if (min == max) {
      return min;
    } else {
      var tmp_next := this.Next();
      n := tmp_next % (max-min) + min;
    }
  }
}

function AbstractifyParamStateToRaftParam(params:ParamState) : RaftParam
{
  RaftParam(
    params.min_election_timeout as int,
    params.max_election_timeout as int,
    params.heartbeat_timeout as int,
    UpperBoundFinite(params.max_integer_value as int)
  )       
}

function method StaticParams():ParamState
{
  ParamState(
    2000, // min_election_timeout
    5000, // max_election_timeout
    100, // heartbeat_timeout
    0x8000_0000_0000_0000 - 1 // max_integer_value
  )
}

datatype ConfigState = ConfigState(
  // client_eps:set<EndPoint>,
  server_eps:seq<EndPoint>,
  params:ParamState
)

function method CRaftMinQuorumSize(c:ConfigState) : uint64
  requires ConfigStateIsValid(c)
{
  (|c.server_eps| as uint64)/2+1
}

predicate ConfigStateIsAbstractable(config:ConfigState)
{
  && (forall e :: e in config.server_eps ==> EndPointIsValidPublicKey(e))
  && SeqIsUnique(config.server_eps)
}

predicate ConfigStateIsValid(config:ConfigState)
  ensures ConfigStateIsValid(config) ==> SeqIsUnique(config.server_eps)
{
  && 0 < |config.server_eps| < 0x1_0000_0000_0000_0000
  && ConfigStateIsAbstractable(config)
  && ParamStateIsValid(config.params)
  && RaftMinQuorumSize(AbstractifyConfigStateToRaftConfig(config)) <= |config.server_eps|
  && SeqIsUnique(config.server_eps)
}

method GetEndPointIndex(global_config:ConfigState, ep:EndPoint) returns(index:uint64)
  requires ep in global_config.server_eps
  requires ConfigStateIsValid(global_config)
  ensures 0 <= index as int < |global_config.server_eps|
  ensures global_config.server_eps[index] == ep
{
  index := |global_config.server_eps| as uint64;
  var i := 0;
  while i < |global_config.server_eps|
    invariant 0 <= i as int <= |global_config.server_eps|
    decreases |global_config.server_eps| - i 
    invariant exists idx :: i <= idx as int < |global_config.server_eps| && global_config.server_eps[idx] == ep;
  {
    if global_config.server_eps[i] == ep {
      index := i as uint64;
      break;
    }
    i := i + 1;
  }
}

function AbstractifyConfigStateToRaftConfig(config:ConfigState) : RaftConfig
{
  RaftConfig(
    config.server_eps,
    AbstractifyParamStateToRaftParam(config.params)
  )
}

datatype ServerConfigState = ServerConfigState(
  server_id:uint64,
  global_config:ConfigState
)

predicate ServerConfigStateIsValid(sconfig:ServerConfigState)
{
  && 0 <= sconfig.server_id as int < |sconfig.global_config.server_eps|
  && ConfigStateIsValid(sconfig.global_config)
}

function AbstractifyServerConfigStateToRaftServerConfig(server_config:ServerConfigState) : RaftServerConfig
{
  RaftServerConfig(
    server_config.server_id as int,
    AbstractifyConfigStateToRaftConfig(server_config.global_config)
  )
}

method InitServerConfigState(my_ep:EndPoint, eps:seq<EndPoint>) returns (sc:ServerConfigState)
  requires my_ep in eps
  requires 0 < |eps| < 0x1_0000_0000_0000_0000
  requires forall ep :: ep in eps ==> EndPointIsValidPublicKey(ep)
  requires SeqIsUnique(eps)
  ensures 0 <= sc.server_id as int < |eps|
  ensures eps[sc.server_id] == my_ep
  ensures sc.global_config.server_eps == eps
  ensures sc.global_config.params == StaticParams()
  ensures ParamStateIsValid(sc.global_config.params)
  ensures ServerConfigStateIsValid(sc)
  ensures WellFormedRaftConfig(AbstractifyConfigStateToRaftConfig(sc.global_config))
{
  var params := StaticParams(); 
  var global_config := ConfigState(eps, params);
  var ep_id := GetEndPointIndex(global_config, my_ep);
  sc := ServerConfigState(ep_id, global_config);
}

function method RaftEndPointIsValid(endPoint:EndPoint, config:ConfigState) : bool
  requires ConfigStateIsValid(config)
{
  EndPointIsValidPublicKey(endPoint)
}

}