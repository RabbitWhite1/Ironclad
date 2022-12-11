include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Raft/Types.i.dfy"
include "../Common/NetClient.i.dfy"
include "AppInterface.i.dfy"

module Raft__CTypes_i {

import opened Environment_s
import opened Common__NetClient_i
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Raft__AppInterface_i
import opened Raft__Types_i

datatype CClockReading = CClockReading(t:uint64)

function AbstractifyCClockReadingToClockReading(cclock:CClockReading) : ClockReading
{
  ClockReading(cclock.t as int)
}

datatype CLogEntry = CLogEntry(term:uint64, index:uint64, req:CAppRequest, seqno:uint64, is_commited:uint64, client_ep:EndPoint)

// for `log` in server_impl
function method ServerMaxLogSize() : int
{
  0xFFFF_FFFF_FFFF_FFFF
}

function method MaxLogEntryTerm() : int {
  0xFFFF_FFFF_FFFF_FFFF
}

function method MaxLogEntryIndex() : int {
  0xFFFF_FFFF_FFFF_FFFF
}

function method MaxSeqno() : int {
  0xFFFF_FFFF_FFFF_FFFF
}

predicate method ValidLogEntry(entry:CLogEntry) {
  && 0 <= entry.term <= MaxLogEntryTerm() as uint64
  && 0 <= entry.index <= MaxLogEntryIndex() as uint64
  && 0 <= entry.seqno <= MaxSeqno() as uint64
  && (entry.is_commited == 0 || entry.is_commited == 1)
  && CAppRequestMarshallable(entry.req)
  && EndPointIsValidPublicKey(entry.client_ep)
}

function method LogEntrySeqSizeLimit() : int { 100 }

predicate method LogEntrySeqIndexIncreasing(log:seq<CLogEntry>) 
  requires forall i :: 0 <= i < |log| ==> ValidLogEntry(log[i])
{
  (forall i :: 0 <= i < |log|-1 && log[i].index > 0 ==> log[i].index as int + 1 == log[i+1].index as int)
}

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
  LogEntry(entry.term as int, entry.index as int, AbstractifyCAppRequestToAppRequest(entry.req), entry.seqno as int, entry.is_commited == 1)
}

function AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries:seq<CLogEntry>) : seq<LogEntry>
  ensures |entries| == |AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries)|
  ensures forall i :: 0 <= i < |entries| ==> AbstractifyCLogEntryToRaftLogEntry(entries[i]) == AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries)[i]
{
  if |entries| == 0 then []
  else [AbstractifyCLogEntryToRaftLogEntry(entries[0])] + AbstractifyCLogEntrySeqToRaftLogEntrySeq(entries[1..])
}

}