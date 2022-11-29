include "../../Impl/Common/SeqIsUniqueDef.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../../Common/Collections/Maps2.s.dfy"
include "../Common/UpperBound.s.dfy"
include "Types.i.dfy"

module Raft__Config_i {
import opened Raft__Types_i
import opened Common__UpperBound_s
import opened Native__Io_s
import opened Collections__Sets_i
import opened Collections__Seqs_i
import opened Collections__Maps2_s

import opened Common__SeqIsUniqueDef_i

datatype RaftParam = RaftParam(
  min_election_timeout:int,
  max_election_timeout:int,
  heartbeat_timeout:int,
  max_integer_value:UpperBound
)

datatype RaftConfig = RaftConfig(
  // client_eps:set<EndPoint>,
  server_eps:seq<EndPoint>,
  params:RaftParam
)

datatype RaftServerConfig = RaftServerConfig(
  server_ep:EndPoint,
  server_id:int,
  global_config:RaftConfig
)

function RandInt(min:int, max:int):int
  requires min <= max
{
  (min + max) / 2
}

function RaftMinQuorumSize(c:RaftConfig) : int
{
  |c.server_eps|/2+1
}

predicate ServersDistinct<X>(server_eps:seq<X>)
{
  forall i, j :: 0 <= i < |server_eps| && 0 <= j < |server_eps| && server_eps[i] == server_eps[j] ==> i == j
}

function WellFormedRaftConfig(c:RaftConfig) : bool
{
  && |c.server_eps| > 0
  && c.params.min_election_timeout > 0
  && c.params.max_election_timeout > 0
  && c.params.min_election_timeout < c.params.max_election_timeout
  && c.params.heartbeat_timeout > 0
  && SeqIsUnique(c.server_eps)
}

function WellFormedRaftServerConfig(c:RaftServerConfig) : bool
{
  && WellFormedRaftConfig(c.global_config)
  && c.server_ep in c.global_config.server_eps
}

} 
