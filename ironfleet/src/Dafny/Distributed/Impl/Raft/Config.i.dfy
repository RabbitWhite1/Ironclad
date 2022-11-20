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
  && params.min_election_timeout <= params.max_election_timeout
  && params.heartbeat_timeout > 0
  && params.max_integer_value > 0
}

method GenerateElectionTimeout(params:ParamState) returns (t:uint64)
  requires ParamStateIsValid(params)
  ensures params.min_election_timeout <= t <= params.max_election_timeout
{
  t := params.min_election_timeout;
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
    1000, // min_election_timeout
    2000, // max_election_timeout
    100, // heartbeat_timeout
    0x8000_0000_0000_0000 - 1 // max_integer_value
  )
}

datatype ConfigState = ConfigState(
  // client_eps:set<EndPoint>,
  server_eps:seq<EndPoint>,
  params:ParamState
)

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
  server_ep:EndPoint,
  global_config:ConfigState
)

predicate ServerConfigStateIsValid(sconfig:ServerConfigState)
{
  && EndPointIsValidPublicKey(sconfig.server_ep)
  && ConfigStateIsValid(sconfig.global_config)
  && sconfig.server_ep in sconfig.global_config.server_eps
}

function AbstractifyServerConfigStateToRaftServerConfig(server_config:ServerConfigState) : RaftServerConfig
{
  RaftServerConfig(
    server_config.server_ep,
    AbstractifyConfigStateToRaftConfig(server_config.global_config)
  )
}

method InitServerConfigState(my_ep:EndPoint, eps:seq<EndPoint>) returns (sc:ServerConfigState)
  requires my_ep in eps
  requires 0 < |eps| < 0x1_0000_0000_0000_0000
  requires forall ep :: ep in eps ==> EndPointIsValidPublicKey(ep)
  requires SeqIsUnique(eps)
  ensures sc.server_ep == my_ep
  ensures sc.global_config.server_eps == eps
  ensures sc.global_config.params == StaticParams()
  ensures ParamStateIsValid(sc.global_config.params)
  ensures ServerConfigStateIsValid(sc)
  ensures WellFormedRaftConfig(AbstractifyConfigStateToRaftConfig(sc.global_config))
{
  var params := StaticParams(); 
  var global_config := ConfigState(eps, params);
  sc := ServerConfigState(my_ep, global_config);
}

function method RaftEndPointIsValid(endPoint:EndPoint, config:ConfigState) : bool
  requires ConfigStateIsValid(config)
{
  EndPointIsValidPublicKey(endPoint)
}

}