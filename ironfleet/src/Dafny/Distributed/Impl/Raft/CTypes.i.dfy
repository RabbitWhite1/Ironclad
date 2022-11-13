include "../../Common/Native/Io.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "AppInterface.i.dfy"

module Raft__CTypes_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Raft__AppInterface_i
import opened Raft__Types_i

datatype CClockReading = CClockReading(t:uint64)

function AbstractifyCClockReadingToClockReading(cclock:CClockReading) : ClockReading
{
  ClockReading(cclock.t as int)
}

datatype CLogEntry = CLogEntry(term:uint64, index:uint64, req:CAppRequest, is_commited:uint64)

predicate method ValidLogEntry(entry:CLogEntry) {
  && 0 < entry.term <= 0xFFFF_FFFF_FFFF_FFFF
  && 0 < entry.index <= 0xFFFF_FFFF_FFFF_FFFF
  && (entry.is_commited == 0 || entry.is_commited == 1)
  && CAppRequestMarshallable(entry.req)
}

function method LogEntrySeqSizeLimit() : int { 100 }

predicate method ValidLogEntrySeq(entries:seq<CLogEntry>) {
  && (forall entry :: entry in entries ==> ValidLogEntry(entry))
  && |entries| <= LogEntrySeqSizeLimit()
}

predicate CLogEntryIsAbstractable(entry:CLogEntry) {
  true
}

predicate CLogEntrySeqIsAbstractable(log_entries:seq<CLogEntry>) {
  true
}

function AbstractifyCLogEntryToRaftLogEntry(entry:CLogEntry) : LogEntry
{
  LogEntry(entry.term as int, entry.index as int, AbstractifyCAppRequestToAppRequest(entry.req), entry.is_commited == 1)
}

function AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries:seq<CLogEntry>) : seq<LogEntry>
{
  if |entries| == 0 then []
  else [AbstractifyCLogEntryToRaftLogEntry(entries[0])] + AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries[1..])
}

}