include "../../Services/Raft/AppStateMachine.s.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "AppInterface.i.dfy"

module Raft__CTypes_i {

import opened Raft__AppInterface_i
import opened AppStateMachine_s
import opened Environment_s
import opened Native__Io_s

datatype CLogEntry = CLogEntry(term:uint64, index:uint64, req:CAppRequest, is_commited:bool)

predicate CLogEntryValid(entry:CLogEntry) {
  && entry.term > 0 && entry.index > 0
}

}