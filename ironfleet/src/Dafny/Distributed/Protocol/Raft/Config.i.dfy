include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "../Common/UpperBound.s.dfy"
include "Types.i.dfy"

module Raft__Config_i {
import opened Raft__Types_i
import opened Common__UpperBound_s
import opened Native__Io_s
import opened Collections__Sets_i
import opened Collections__Seqs_i

datatype RaftConfig = RaftConfig(
  client_eps:set<EndPoint>,
  server_eps:seq<EndPoint>,
  min_election_timeout:int,
  max_election_timeout:int,
  heartbeat_timeout:int,
  max_integer_value:UpperBound
  )

datatype RaftServerConfig = RaftServerConfig(
  server_id:int,
  global_config:RaftConfig
)

function RaftMinQuorumSize(c:RaftConfig) : int
{
  |c.server_eps|/2+1
}

predicate ReplicasDistinct(server_eps:seq<EndPoint>, i:int, j:int)
{
  0 <= i < |server_eps| && 0 <= j < |server_eps| && server_eps[i] == server_eps[j] ==> i == j
}

function WellFormedLRaftConfig(c:RaftConfig) : bool
{
  && |c.server_eps| > 0
  && c.min_election_timeout > 0
  && c.max_election_timeout > 0
  && c.min_election_timeout < c.max_election_timeout
  && c.heartbeat_timeout > 0
  && forall i,j :: ReplicasDistinct(c.server_eps, i, j)
}

function WellFormedLRaftServerConfig(c:RaftServerConfig) : bool
{
  && WellFormedLRaftConfig(c.global_config)
  && 0 <= c.server_id
}

} 
