include "../Common/CmdLineParser.i.dfy"

module SimplestCmdLineParser_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened CmdLineParser_i
import opened Common__NetClient_i
import opened Common__SeqIsUniqueDef_i

function simplest_config_parsing(args:seq<seq<byte>>) : seq<EndPoint>
{
  var (_, endpoints) := parse_end_points(args);
  endpoints
}

method parse_cmd_line(id:EndPoint, args:seq<seq<byte>>) returns (ok:bool, host_ids:seq<EndPoint>, my_index:uint64)
  requires EndPointIsValidPublicKey(id)
  ensures ok ==> 0 <= my_index as int < |host_ids| < 0x1_0000_0000_0000_0000
                && host_ids == simplest_config_parsing(args)
                && host_ids[my_index] == id
                && SeqIsUnique(host_ids)
                && (forall h :: h in host_ids ==> EndPointIsValidPublicKey(h))
{
  var tuple1 := parse_end_points(args);
  ok := tuple1.0;
  if !ok {
    return;
  }
  host_ids := tuple1.1;
  if |host_ids| == 0 || |host_ids| >= 0x1_0000_0000_0000_0000 {
    ok := false;
    return;
  }

  var unique := test_unique(host_ids);
  if !unique {
    ok := false;
    return;
  }

  ok, my_index := GetHostIndex(id, host_ids);
  if !ok {
    return;
  }

  ghost var ghost_host_ids := simplest_config_parsing(args);
  assert host_ids == ghost_host_ids;
}

}
