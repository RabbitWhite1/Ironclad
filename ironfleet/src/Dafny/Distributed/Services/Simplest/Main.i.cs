// Dafny program Main.i.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.9.0.41003
// Command Line Options: /compile:0 /spillTargetCode:3 /noVerify src/Dafny/Distributed/Services/Simplest/Main.i.dfy
// Main.i.dfy


module Main_i refines Main_s {

  import opened AS_s = AbstractServiceSimplest_s`All

  import opened DS_s = Simplest_DistributedSystem_i

  import opened Environment_s

  import opened Concrete_NodeIdentity_i

  import opened Collections__Sets_i

  export
    provides DS_s, Native__Io_s, Native__NativeTypes_s, IronfleetMain

  lemma {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ RefinementToServiceState(config: DS_s.H_s.ConcreteConfiguration, db: seq<DS_State>) returns (sb: seq<ServiceState>)
    requires |db| > 0
    ensures |sb| == |db|
    ensures Service_Init(sb[0], MapSeqToSet(config, (x: EndPoint) => x))
    ensures forall i: int :: 0 <= i < |sb| ==> sb[i] == sb[0]
    ensures forall i: int {:trigger Service_Next(sb[i], sb[i + 1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i + 1] || Service_Next(sb[i], sb[i + 1])
    decreases config, db
  {
    if |db| == 1 {
      sb := [ServiceState'(MapSeqToSet(config, (x: EndPoint) => x))];
    } else {
      ghost var rest := RefinementToServiceState(config, all_but_last(db));
      ghost var last := last(db);
      sb := rest + [ServiceState'(MapSeqToSet(config, (x: EndPoint) => x))];
    }
  }

  lemma RefinementProof(config: DS_s.H_s.ConcreteConfiguration, db: seq<DS_State>) returns (sb: seq<ServiceState>)
    requires |db| > 0
    requires DS_Init(db[0], config)
    requires forall i: int {:trigger DS_Next(db[i], db[i + 1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i + 1])
    ensures |db| == |sb|
    ensures Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers))
    ensures forall i: int {:trigger Service_Next(sb[i], sb[i + 1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i + 1] || Service_Next(sb[i], sb[i + 1])
    ensures forall i: int :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i])
    decreases config, db
  {
    sb := RefinementToServiceState(config, db);
    forall i: int | 0 <= i < |db|
      ensures Service_Correspondence(db[i].environment.sentPackets, sb[i])
    {
    }
  }

  method IronfleetMain(ghost env: HostEnvironment, netc: NetClient, args: seq<seq<byte>>)
    requires env.Valid() && env.ok.ok()
    requires env.net.history() == []
    requires netc.IsOpen()
    requires netc.env == env
    requires ValidPhysicalAddress(EndPoint(netc.MyPublicKey()))
    modifies set x: object {:trigger DS_s.H_s.ArbitraryObject(x)} | DS_s.H_s.ArbitraryObject(x)
    decreases *
  {
    var ok, host_state := DS_s.H_s.HostInitImpl(env, netc, args);
    ghost var config := DS_s.H_s.ParseCommandLineConfiguration(args);
    var id := EndPoint(netc.MyPublicKey());
    assert ok ==> DS_s.H_s.HostInit(host_state, config, id);
    while ok
      invariant ok ==> DS_s.H_s.HostStateInvariants(host_state, env)
      invariant ok ==> env.Valid() && env.ok.ok()
      decreases *
    {
      ghost var old_net_history := env.net.history();
      ghost var old_state := host_state;
      ghost var recvs, clocks, sends, ios;
      ok, host_state, recvs, clocks, sends, ios := DS_s.H_s.HostNextImpl(env, host_state);
      if ok {
        assert DS_s.H_s.HostNext(old_state, host_state, ios);
        assert recvs + clocks + sends == ios;
        assert env.net.history() == old_net_history + recvs + clocks + sends;
        assert forall e: LIoOp<EndPoint, seq<byte>> :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?);
        assert |clocks| <= 1;
      }
    }
  }

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Collections__Seqs_s
}

module AbstractServiceSimplest_s refines AbstractService_s {

  export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s, ServiceState, Service_Init, Service_Next, Service_Correspondence


  export All
    reveals *
    reveals ServiceState', ServiceState, Service_Init, Service_Next, Uint64ToBytes, Service_Correspondence
    provides Native__Io_s, Environment_s, Native__NativeTypes_s

  datatype ServiceState' = ServiceState'(hosts: set<EndPoint>)

  type /*{:_provided}*/ ServiceState = ServiceState'

  predicate Service_Init(s: ServiceState, serverAddresses: set<EndPoint>)
    decreases s, serverAddresses
  {
    s.hosts == serverAddresses
  }

  predicate Service_Next(s: ServiceState, s': ServiceState)
    decreases s, s'
  {
    s'.hosts == s.hosts
  }

  function Uint64ToBytes(u: uint64): seq<byte>
    decreases u
  {
    [(u / 72057594037927936) as byte, (u / 281474976710656 % 256) as byte, (u / 1099511627776 % 256) as byte, (u / 4294967296 % 256) as byte, (u / 16777216 % 256) as byte, (u / 65536 % 256) as byte, (u / 256 % 256) as byte, (u % 256) as byte]
  }

  predicate Service_Correspondence(concretePkts: set<LPacket<EndPoint, seq<byte>>>, serviceState: ServiceState)
    decreases concretePkts, serviceState
  {
    true
  }

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
}

abstract module AbstractService_s {

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  type ServiceState

  predicate Service_Init(s: ServiceState, serverAddresses: set<EndPoint>)
    decreases serverAddresses

  predicate Service_Next(s: ServiceState, s': ServiceState)

  predicate Service_Correspondence(concretePkts: set<LPacket<EndPoint, seq<byte>>>, serviceState: ServiceState)
    decreases concretePkts
}

module Native__Io_s {

  import opened Native__NativeTypes_s

  import opened Environment_s
  class HostEnvironment {
    ghost var ok: OkState
    ghost var now: NowState
    ghost var net: NetState
    ghost var files: FileSystemState

    constructor {:axiom} ()
      requires false

    predicate Valid()
      reads this
      decreases {this}
    {
      true
    }
  }

  class OkState {
    constructor {:axiom} ()
      requires false

    function {:axiom} ok(): bool
      reads this
      decreases {this}
  }

  class PrintParams {
    constructor {:axiom} ()
      requires false

    static function method {:axiom} ShouldPrintProfilingInfo(): bool

    static function method {:axiom} ShouldPrintProgress(): bool
  }

  class NowState {
    constructor {:axiom} ()
      requires false

    function {:axiom} now(): int
      reads this
      decreases {this}
  }

  class Time {
    static method {:axiom} GetTime(ghost env: HostEnvironment) returns (t: uint64)
      requires env.Valid()
      modifies env.now, env.net
      ensures t as int == env.now.now()
      ensures AdvanceTime(old(env.now.now()), env.now.now(), 0)
      ensures env.net.history() == old(env.net.history()) + [LIoOpReadClock(t as int)]
      decreases env

    static method {:axiom} GetDebugTimeTicks() returns (t: uint64)

    static method {:axiom} RecordTiming(name: array<char>, time: uint64)
      decreases name, time
  }

  datatype EndPoint = EndPoint(public_key: seq<byte>)

  type NetPacket = LPacket<EndPoint, seq<byte>>

  type NetEvent = LIoOp<EndPoint, seq<byte>>

  class NetState {
    constructor {:axiom} ()
      requires false

    function {:axiom} history(): seq<NetEvent>
      reads this
      decreases {this}
  }

  class NetClient {
    ghost var env: HostEnvironment

    function method {:axiom} MyPublicKey(): seq<byte>
      reads this
      decreases {this}

    function {:axiom} IsOpen(): bool
      reads this
      decreases {this}

    constructor {:axiom} ()
      requires false

    method {:axiom} Close() returns (ok: bool)
      requires env.Valid()
      requires env.ok.ok()
      requires this.IsOpen()
      modifies this, env.ok
      ensures env == old(env)
      ensures env.ok.ok() == ok

    method {:axiom} Receive(timeLimit: int32)
        returns (ok: bool, timedOut: bool, remote: seq<byte>, buffer: array<byte>)
      requires env.Valid()
      requires env.ok.ok()
      requires IsOpen()
      requires timeLimit >= 0
      requires timeLimit as int * 1000 < 2147483648
      modifies this, env.ok, env.now, env.net
      ensures env == old(env)
      ensures env.ok.ok() == ok
      ensures AdvanceTime(old(env.now.now()), env.now.now(), timeLimit as int)
      ensures MyPublicKey() == old(MyPublicKey())
      ensures ok ==> IsOpen()
      ensures ok ==> timedOut ==> env.net.history() == old(env.net.history()) + [LIoOpTimeoutReceive()]
      ensures ok ==> !timedOut ==> fresh(buffer) && env.net.history() == old(env.net.history()) + [LIoOpReceive(LPacket(EndPoint(MyPublicKey()), EndPoint(remote), buffer[..]))] && ValidPhysicalAddress(EndPoint(remote)) && buffer.Length <= MaxPacketSize()
      decreases timeLimit

    method {:axiom} Send(remote: seq<byte>, buffer: array<byte>) returns (ok: bool)
      requires env.Valid()
      requires env.ok.ok()
      requires IsOpen()
      requires buffer.Length <= MaxPacketSize()
      modifies this, env.ok, env.net
      ensures env == old(env)
      ensures env.ok.ok() == ok
      ensures MyPublicKey() == old(MyPublicKey())
      ensures ok ==> IsOpen()
      ensures ok ==> env.net.history() == old(env.net.history()) + [LIoOpSend(LPacket(EndPoint(remote), EndPoint(MyPublicKey()), buffer[..]))]
      decreases remote, buffer
  }

  class FileSystemState { }

  class MutableSet<T(==,0,!new)> {
    static function method {:axiom} SetOf(s: MutableSet<T>): set<T>
      reads s
      decreases {s}, s

    static method {:axiom} EmptySet() returns (s: MutableSet<T>)
      ensures SetOf(s) == {}
      ensures fresh(s)

    constructor {:axiom} ()
      requires false

    method {:axiom} Size() returns (size: int)
      ensures size == |SetOf(this)|

    method {:axiom} SizeModest() returns (size: uint64)
      requires |SetOf(this)| < 18446744073709551616
      ensures size as int == |SetOf(this)|

    method {:axiom} Contains(x: T) returns (contains: bool)
      ensures contains == (x in SetOf(this))

    method {:axiom} Add(x: T)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) + {x}

    method {:axiom} AddSet(s: MutableSet<T>)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) + old(SetOf(s))
      decreases s

    method {:axiom} TransferSet(s: MutableSet<T>)
      modifies this, s
      ensures SetOf(this) == old(SetOf(s))
      ensures SetOf(s) == {}
      decreases s

    method {:axiom} Remove(x: T)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) - {x}

    method {:axiom} RemoveAll()
      modifies this
      ensures SetOf(this) == {}
  }

  class MutableMap<K(==), V> {
    static function method {:axiom} MapOf(m: MutableMap<K, V>): map<K, V>
      reads m
      decreases {m}, m

    static method {:axiom} EmptyMap() returns (m: MutableMap<K, V>)
      ensures MapOf(m) == map[]
      ensures fresh(m)

    static method {:axiom} FromMap(dafny_map: map<K, V>) returns (m: MutableMap<K, V>)
      ensures MapOf(m) == dafny_map
      ensures fresh(m)
      decreases dafny_map

    static method {:axiom} FromKVTuples(kvs: seq<(K, V)>) returns (m: MutableMap<K, V>)
      ensures MapOf(m) == KVTupleSeqToMap(kvs)
      decreases kvs

    constructor {:axiom} ()
      requires false

    function method {:axiom} Size(): int
      reads this
      ensures this.Size() == |MapOf(this)|
      decreases {this}

    method {:axiom} SizeModest() returns (size: uint64)
      requires |MapOf(this)| < 18446744073709551616
      ensures size as int == |MapOf(this)|

    method {:axiom} Contains(key: K) returns (contains: bool)
      ensures contains == (key in MapOf(this))

    method {:axiom} TryGetValue(key: K) returns (contains: bool, val: V)
      ensures contains == (key in MapOf(this))
      ensures contains ==> val == MapOf(this)[key]

    method {:axiom} Set(key: K, val: V)
      modifies this
      ensures MapOf(this) == old(MapOf(this))[key := val]

    method {:axiom} Remove(key: K)
      modifies this
      ensures MapOf(this) == old(MapOf(this)) - {key}

    method {:axiom} AsKVTuples() returns (kvs: seq<(K, V)>)
      ensures |kvs| == |MapOf(this).Keys|
      ensures forall k: K :: k in MapOf(this) ==> (k, MapOf(this)[k]) in kvs
      ensures forall k: K, v: V :: (k, v) in kvs ==> k in MapOf(this) && MapOf(this)[k] == v
  }

  class Arrays {
    static method {:axiom} CopySeqIntoArray<A>(src: seq<A>, srcIndex: uint64, dst: array<A>, dstIndex: uint64, len: uint64)
      requires srcIndex as int + len as int <= |src|
      requires dstIndex as int + len as int <= dst.Length
      modifies dst
      ensures forall i: int :: 0 <= i < dst.Length ==> dst[i] == if dstIndex as int <= i < dstIndex as int + len as int then src[i - dstIndex as int + srcIndex as int] else old(dst[..])[i]
      ensures forall i: int :: srcIndex as int <= i < srcIndex as int + len as int ==> src[i] == dst[i - srcIndex as int + dstIndex as int]
      decreases src, srcIndex, dst, dstIndex, len
  }

  function {:axiom} realTimeBound(): int

  predicate AdvanceTime(oldTime: int, newTime: int, delay: int)
    decreases oldTime, newTime, delay
  {
    oldTime <= newTime < oldTime + delay + realTimeBound()
  }

  function MaxPacketSize(): int
  {
    18446744073709551615
  }

  predicate ValidPhysicalAddress(endPoint: EndPoint)
    decreases endPoint
  {
    |endPoint.public_key| < 1048576
  }

  predicate ValidPhysicalPacket(p: LPacket<EndPoint, seq<byte>>)
    decreases p
  {
    ValidPhysicalAddress(p.src) &&
    ValidPhysicalAddress(p.dst) &&
    |p.msg| <= MaxPacketSize()
  }

  predicate ValidPhysicalIo(io: LIoOp<EndPoint, seq<byte>>)
    decreases io
  {
    (io.LIoOpReceive? ==>
      ValidPhysicalPacket(io.r)) &&
    (io.LIoOpSend? ==>
      ValidPhysicalPacket(io.s))
  }

  function KVTupleSeqToMap<K(!new), V(!new)>(kvs: seq<(K, V)>): (m: map<K, V>)
    ensures forall k: K, v: V :: (k, v) in kvs ==> k in m
    ensures forall k: K :: k in m ==> (k, m[k]) in kvs
    decreases kvs
  {
    if |kvs| == 0 then
      map[]
    else
      ghost var kvs_prefix: seq<(K, V)> := kvs[..|kvs| - 1]; ghost var m_prefix: map<K, V> := KVTupleSeqToMap(kvs_prefix); ghost var kv_last: (K, V) := kvs[|kvs| - 1]; m_prefix[kv_last.0 := kv_last.1]
  }
}

module Native__NativeTypes_s {
  newtype {:nativeType ""sbyte""} sbyte = i: int
    | -128 <= i < 128

  newtype {:nativeType ""byte""} byte = i: int
    | 0 <= i < 256

  newtype {:nativeType ""short""} int16 = i: int
    | -32768 <= i < 32768

  newtype {:nativeType ""ushort""} uint16 = i: int
    | 0 <= i < 65536

  newtype {:nativeType ""int""} int32 = i: int
    | -2147483648 <= i < 2147483648

  newtype {:nativeType ""uint""} uint32 = i: int
    | 0 <= i < 4294967296

  newtype {:nativeType ""long""} int64 = i: int
    | -9223372036854775808 <= i < 9223372036854775808

  newtype {:nativeType ""ulong""} uint64 = i: int
    | 0 <= i < 18446744073709551616

  newtype {:nativeType ""sbyte""} nat8 = i: int
    | 0 <= i < 128

  newtype {:nativeType ""short""} nat16 = i: int
    | 0 <= i < 32768

  newtype {:nativeType ""int""} nat32 = i: int
    | 0 <= i < 2147483648

  newtype {:nativeType ""long""} nat64 = i: int
    | 0 <= i < 9223372036854775808
}

module Environment_s {

  import opened Collections__Maps2_s

  import opened Temporal__Temporal_s
  datatype LPacket<IdType, MessageType(==)> = LPacket(dst: IdType, src: IdType, msg: MessageType)

  datatype LIoOp<IdType, MessageType(==)> = LIoOpSend(s: LPacket<IdType, MessageType>) | LIoOpReceive(r: LPacket<IdType, MessageType>) | LIoOpTimeoutReceive | LIoOpReadClock(t: int)

  datatype LEnvStep<IdType, MessageType(==)> = LEnvStepHostIos(actor: IdType, ios: seq<LIoOp<IdType, MessageType>>) | LEnvStepDeliverPacket(p: LPacket<IdType, MessageType>) | LEnvStepAdvanceTime | LEnvStepStutter

  datatype LHostInfo<IdType, MessageType(==)> = LHostInfo(queue: seq<LPacket<IdType, MessageType>>)

  datatype LEnvironment<IdType, MessageType(==)> = LEnvironment(time: int, sentPackets: set<LPacket<IdType, MessageType>>, hostInfo: map<IdType, LHostInfo<IdType, MessageType>>, nextStep: LEnvStep<IdType, MessageType>)

  predicate IsValidLIoOp<IdType, MessageType>(io: LIoOp<IdType, MessageType>, actor: IdType, e: LEnvironment<IdType, MessageType>)
    decreases io, e
  {
    match io
    case LIoOpSend(s) =>
      s.src == actor
    case LIoOpReceive(r) =>
      r.dst == actor
    case LIoOpTimeoutReceive() =>
      true
    case LIoOpReadClock(t) =>
      true
  }

  predicate LIoOpOrderingOKForAction<IdType, MessageType>(io1: LIoOp<IdType, MessageType>, io2: LIoOp<IdType, MessageType>)
    decreases io1, io2
  {
    io1.LIoOpReceive? || io2.LIoOpSend?
  }

  predicate LIoOpSeqCompatibleWithReduction<IdType, MessageType>(ios: seq<LIoOp<IdType, MessageType>>)
    decreases ios
  {
    forall i: int {:trigger ios[i], ios[i + 1]} :: 
      0 <= i < |ios| - 1 ==>
        LIoOpOrderingOKForAction(ios[i], ios[i + 1])
  }

  predicate IsValidLEnvStep<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, step: LEnvStep<IdType, MessageType>)
    decreases e, step
  {
    match step
    case LEnvStepHostIos(actor, ios) =>
      (forall io :: 
        io in ios ==>
          IsValidLIoOp(io, actor, e)) &&
      LIoOpSeqCompatibleWithReduction(ios)
    case LEnvStepDeliverPacket(p) =>
      p in e.sentPackets
    case LEnvStepAdvanceTime() =>
      true
    case LEnvStepStutter() =>
      true
  }

  predicate LEnvironment_Init<IdType, MessageType>(e: LEnvironment<IdType, MessageType>)
    decreases e
  {
    |e.sentPackets| == 0 &&
    e.time >= 0
  }

  predicate LEnvironment_PerformIos<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>, actor: IdType, ios: seq<LIoOp<IdType, MessageType>>)
    decreases e, e', ios
  {
    e'.sentPackets == e.sentPackets + (set io: LIoOp<IdType, MessageType> {:trigger io.s} {:trigger io.LIoOpSend?} {:trigger io in ios} | io in ios && io.LIoOpSend? :: io.s) &&
    (forall io: LIoOp<IdType, MessageType> :: 
      io in ios &&
      io.LIoOpReceive? ==>
        io.r in e.sentPackets) &&
    e'.time == e.time
  }

  predicate LEnvironment_AdvanceTime<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    e'.time > e.time &&
    e'.sentPackets == e.sentPackets
  }

  predicate LEnvironment_Stutter<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    e'.time == e.time &&
    e'.sentPackets == e.sentPackets
  }

  predicate LEnvironment_Next<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    IsValidLEnvStep(e, e.nextStep) &&
    match e.nextStep { case LEnvStepHostIos(_mcc#0: IdType, _mcc#1: seq<LIoOp<IdType, MessageType>>) => (var ios := _mcc#1; var actor := _mcc#0; LEnvironment_PerformIos(e, e', actor, ios)) case LEnvStepDeliverPacket(_mcc#2: LPacket<IdType, MessageType>) => (var p := _mcc#2; LEnvironment_Stutter(e, e')) case LEnvStepAdvanceTime => LEnvironment_AdvanceTime(e, e') case LEnvStepStutter => LEnvironment_Stutter(e, e') }
  }

  function {:opaque} {:fuel 0, 0} EnvironmentNextTemporal<IdType, MessageType>(b: Behavior<LEnvironment<IdType, MessageType>>): temporal
    requires imaptotal(b)
    ensures forall i: int {:trigger sat(i, EnvironmentNextTemporal(b))} :: sat(i, EnvironmentNextTemporal(b)) <==> LEnvironment_Next(b[i], b[nextstep(i)])
  {
    stepmap(imap i: int {:trigger nextstep(i)} | true :: LEnvironment_Next(b[i], b[nextstep(i)]))
  }

  predicate LEnvironment_BehaviorSatisfiesSpec<IdType, MessageType>(b: Behavior<LEnvironment<IdType, MessageType>>)
  {
    imaptotal(b) &&
    LEnvironment_Init(b[0]) &&
    sat(0, always(EnvironmentNextTemporal(b)))
  }
}

module Collections__Maps2_s {
  function mapdomain<KT, VT>(m: map<KT, VT>): set<KT>
    decreases m
  {
    set k: KT {:trigger k in m} | k in m :: k
  }

  function mapremove<KT, VT>(m: map<KT, VT>, k: KT): map<KT, VT>
    decreases m
  {
    map ki: KT {:trigger m[ki]} {:trigger ki in m} | ki in m && ki != k :: m[ki]
  }

  predicate imaptotal<KT(!new), VT>(m: imap<KT, VT>)
  {
    forall k: KT {:trigger m[k]} {:trigger k in m} :: 
      k in m
  }
}

module Temporal__Temporal_s {

  import opened Collections__Maps2_s
  type temporal = imap<int, bool>

  type Behavior<S> = imap<int, S>

  function stepmap(f: imap<int, bool>): temporal
    ensures forall i: int :: i in f ==> sat(i, stepmap(f)) == f[i]
  {
    f
  }

  predicate sat(s: int, t: temporal)
    decreases s
  {
    s in t &&
    t[s]
  }

  function {:opaque} {:fuel 0, 0} and(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, and(x, y))} :: sat(i, and(x, y)) == (sat(i, x) && sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) && sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} or(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, or(x, y))} :: sat(i, or(x, y)) == (sat(i, x) || sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) || sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} imply(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, imply(x, y))} :: sat(i, imply(x, y)) == (sat(i, x) ==> sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) ==> sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} equiv(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, equiv(x, y))} :: sat(i, equiv(x, y)) == (sat(i, x) <==> sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) <==> sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} not(x: temporal): temporal
    ensures forall i: int {:trigger sat(i, not(x))} :: sat(i, not(x)) == !sat(i, x)
  {
    stepmap(imap i: int {:trigger sat(i, x)} | true :: !sat(i, x))
  }

  function nextstep(i: int): int
    decreases i
  {
    i + 1
  }

  function {:opaque} {:fuel 0, 0} next(x: temporal): temporal
    ensures forall i: int {:trigger sat(i, next(x))} :: sat(i, next(x)) == sat(nextstep(i), x)
  {
    stepmap(imap i: int {:trigger nextstep(i)} | true :: sat(nextstep(i), x))
  }

  function {:opaque} {:fuel 0, 0} always(x: temporal): temporal
  {
    stepmap(imap i: int {:trigger sat(i, always(x))} | true :: forall j: int {:trigger sat(j, x)} :: i <= j ==> sat(j, x))
  }

  function {:opaque} {:fuel 0, 0} eventual(x: temporal): temporal
  {
    stepmap(imap i: int {:trigger sat(i, eventual(x))} | true :: exists j: int :: i <= j && sat(j, x))
  }
}

module Simplest_DistributedSystem_i refines DistributedSystem_s {

  import H_s = Host_i`All
  predicate ValidPhysicalEnvironmentStep(step: LEnvStep<EndPoint, seq<byte>>)
    decreases step
  {
    step.LEnvStepHostIos? ==>
      forall io: LIoOp<EndPoint, seq<byte>> {:trigger io in step.ios} {:trigger ValidPhysicalIo(io)} :: 
        io in step.ios ==>
          ValidPhysicalIo(io)
  }

  predicate DS_Init(s: DS_State, config: H_s.ConcreteConfiguration)
    reads *
    decreases {}, s, config
  {
    s.config == config &&
    H_s.ConcreteConfigToServers(s.config) == mapdomain(s.servers) &&
    H_s.ConcreteConfigInit(s.config) &&
    LEnvironment_Init(s.environment) &&
    forall id: EndPoint :: 
      id in s.servers ==>
        H_s.HostInit(s.servers[id], config, id)
  }

  predicate DS_NextOneServer(s: DS_State, s': DS_State, id: EndPoint, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires id in s.servers
    reads *
    decreases {}, s, s', id, ios
  {
    id in s'.servers &&
    H_s.HostNext(s.servers[id], s'.servers[id], ios) &&
    s'.servers == s.servers[id := s'.servers[id]]
  }

  predicate DS_Next(s: DS_State, s': DS_State)
    reads *
    decreases {}, s, s'
  {
    s'.config == s.config &&
    LEnvironment_Next(s.environment, s'.environment) &&
    ValidPhysicalEnvironmentStep(s.environment.nextStep) &&
    if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then DS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios) else s'.servers == s.servers
  }

  import opened Collections__Maps2_s

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s

  datatype DS_State = DS_State(config: H_s.ConcreteConfiguration, environment: LEnvironment<EndPoint, seq<byte>>, servers: map<EndPoint, H_s.HostState>)
}

module Host_i refines Host_s {

  import opened SimplestCmdLineParser_i

  import opened Collections__Sets_i

  export Spec
    provides Native__Io_s, Environment_s, Native__NativeTypes_s, HostState, ConcreteConfiguration, HostInit, HostNext, ConcreteConfigInit, HostStateInvariants, ConcreteConfigToServers, ParseCommandLineConfiguration, ArbitraryObject, HostInitImpl, HostNextImpl


  export All
    reveals *
    provides SimplestCmdLineParser_i, Collections__Sets_i
    reveals HostState, ConcreteConfiguration, HostInit, HostNext, ConcreteConfigInit, HostStateInvariants, ConcreteConfigToServers, ParseCommandLineConfiguration
    provides HostInitImpl, HostNextImpl
    reveals ArbitraryObject
    provides Native__Io_s, Environment_s, Native__NativeTypes_s

  type /*{:_provided}*/ HostState = int

  type /*{:_provided}*/ ConcreteConfiguration = seq<EndPoint>

  predicate HostInit(host_state: HostState, config: ConcreteConfiguration, id: EndPoint)
    reads *
    decreases {}, host_state, config, id
  {
    id in config
  }

  predicate HostNext(host_state: HostState, host_state': HostState, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    reads *
    decreases {}, host_state, host_state', ios
  {
    host_state' == host_state &&
    |ios| == 0
  }

  predicate ConcreteConfigInit(config: ConcreteConfiguration)
    decreases config
  {
    true
  }

  predicate HostStateInvariants(host_state: HostState, env: HostEnvironment)
    reads *
    decreases {}, host_state, env
  {
    true
  }

  function ConcreteConfigToServers(config: ConcreteConfiguration): set<EndPoint>
    decreases config
  {
    MapSeqToSet(config, (x: EndPoint) => x)
  }

  function ParseCommandLineConfiguration(args: seq<seq<byte>>): ConcreteConfiguration
    decreases args
  {
    simplest_config_parsing(args)
  }

  method HostInitImpl(ghost env: HostEnvironment, netc: NetClient, args: seq<seq<byte>>)
      returns (ok: bool, host_state: HostState)
    requires env.Valid()
    requires env.ok.ok()
    requires netc.IsOpen()
    requires netc.env == env
    requires ValidPhysicalAddress(EndPoint(netc.MyPublicKey()))
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok ==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state, env)
    ensures ok ==> var id: EndPoint := EndPoint(netc.MyPublicKey()); var config: ConcreteConfiguration := ParseCommandLineConfiguration(args); id in ConcreteConfigToServers(config) && ConcreteConfigInit(config) && HostInit(host_state, config, id)
    ensures env.net.history() == old(env.net.history())
    decreases env, netc, args
  {
    var my_index;
    host_state := 0;
    var id := EndPoint(netc.MyPublicKey());
    print ""My id is: "", id, ""\n"";
    var config;
    ok, config, my_index := parse_cmd_line(id, args);
    if !ok {
      return;
    }
    assert id in config;
  }

  method HostNextImpl(ghost env: HostEnvironment, host_state: HostState)
      returns (ok: bool, host_state': HostState, ghost recvs: seq<NetEvent>, ghost clocks: seq<NetEvent>, ghost sends: seq<NetEvent>, ghost ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires env.Valid() && env.ok.ok()
    requires HostStateInvariants(host_state, env)
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok <==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state', env)
    ensures ok ==> HostNext(host_state, host_state', ios)
    ensures ok ==> recvs + clocks + sends == ios
    ensures ok || |sends| > 0 ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
    ensures forall e: LIoOp<EndPoint, seq<byte>> :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1
    decreases env, host_state
  {
    ok := true;
    host_state' := host_state;
    recvs := [];
    clocks := [];
    sends := [];
    ios := [];
  }

  predicate ArbitraryObject(o: object)
    decreases o
  {
    true
  }

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
}

module SimplestCmdLineParser_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened CmdLineParser_i

  import opened Common__NetClient_i

  import opened Common__SeqIsUniqueDef_i
  function simplest_config_parsing(args: seq<seq<byte>>): seq<EndPoint>
    decreases args
  {
    var (_: bool, endpoints: seq<EndPoint>) := parse_end_points(args);
    endpoints
  }

  method parse_cmd_line(id: EndPoint, args: seq<seq<byte>>)
      returns (ok: bool, host_ids: seq<EndPoint>, my_index: uint64)
    requires EndPointIsValidPublicKey(id)
    ensures ok ==> 0 <= my_index as int < |host_ids| < 18446744073709551616 && host_ids == simplest_config_parsing(args) && host_ids[my_index] == id && SeqIsUnique(host_ids) && forall h: EndPoint :: h in host_ids ==> EndPointIsValidPublicKey(h)
    decreases id, args
  {
    var tuple1 := parse_end_points(args);
    ok := tuple1.0;
    if !ok {
      return;
    }
    host_ids := tuple1.1;
    if |host_ids| == 0 || |host_ids| >= 18446744073709551616 {
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

module CmdLineParser_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Math__power_s

  import opened Common__SeqIsUniqueDef_i

  import opened Common__NetClient_i
  function method parse_end_point(public_key: seq<byte>): (bool, EndPoint)
    ensures var tuple: (bool, EndPoint) := parse_end_point(public_key); var ok: bool, ep: EndPoint := tuple.0, tuple.1; ok ==> EndPointIsValidPublicKey(ep)
    decreases public_key
  {
    if |public_key| < 1048576 then
      (true, EndPoint(public_key))
    else
      (false, EndPoint(public_key))
  }

  method test_unique(endpoints: seq<EndPoint>) returns (unique: bool)
    ensures unique <==> SeqIsUnique(endpoints)
    decreases endpoints
  {
    unique := true;
    var i := 0;
    while i < |endpoints|
      invariant 0 <= i <= |endpoints|
      invariant forall j: int, k: int :: 0 <= j < |endpoints| && 0 <= k < i && j != k ==> endpoints[j] != endpoints[k]
      decreases |endpoints| - i
    {
      var j := 0;
      while j < |endpoints|
        invariant 0 <= j <= |endpoints|
        invariant forall k: int :: 0 <= k < j && k != i ==> endpoints[i] != endpoints[k]
        decreases |endpoints| - j
      {
        if i != j && endpoints[i] == endpoints[j] {
          unique := false;
          reveal_SeqIsUnique();
          return;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    reveal SeqIsUnique();
  }

  function method parse_end_points(args: seq<seq<byte>>): (bool, seq<EndPoint>)
    ensures var (ok: bool, endpoints: seq<EndPoint>) := parse_end_points(args); ok ==> forall e: EndPoint :: e in endpoints ==> EndPointIsValidPublicKey(e)
    decreases args
  {
    if |args| == 0 then
      (true, [])
    else
      var (ok1: bool, ep: EndPoint) := parse_end_point(args[0]); var (ok2: bool, rest: seq<EndPoint>) := parse_end_points(args[1..]); if !(ok1 && ok2) then (false, []) else (true, [ep] + rest)
  }

  method GetHostIndex(host: EndPoint, hosts: seq<EndPoint>)
      returns (found: bool, index: uint64)
    requires EndPointIsValidPublicKey(host)
    requires SeqIsUnique(hosts)
    requires |hosts| < 18446744073709551616
    requires forall h: EndPoint :: h in hosts ==> EndPointIsValidPublicKey(h)
    ensures found ==> 0 <= index as int < |hosts| && hosts[index] == host
    ensures !found ==> !(host in hosts)
    decreases host, hosts
  {
    var i: uint64 := 0;
    while i < |hosts| as uint64
      invariant i as int <= |hosts|
      invariant forall j: uint64 :: 0 <= j < i ==> hosts[j] != host
      decreases |hosts| as uint64 as int - i as int
    {
      if host == hosts[i] {
        found := true;
        index := i;
        calc ==> {
          true;
          {
            reveal_SeqIsUnique();
          }
          forall j: int :: 
            0 <= j < |hosts| &&
            j != i as int ==>
              hosts[j] != host;
        }
        return;
      }
      if i == |hosts| as uint64 - 1 {
        found := false;
        return;
      }
      i := i + 1;
    }
    found := false;
  }
}

module Math__power_i {

  import opened Math__power_s

  import opened Math__mul_i

  import opened Math__mul_auto_i
  lemma /*{:_induction b}*/ lemma_power_0(b: int)
    ensures power(b, 0) == 1
    decreases b
  {
  }

  lemma /*{:_induction b}*/ lemma_power_1(b: int)
    ensures power(b, 1) == b
    decreases b
  {
  }

  lemma /*{:_induction e}*/ lemma_0_power(e: nat)
    requires e > 0
    ensures power(0, e) == 0
    decreases e
  {
  }

  lemma /*{:_induction e}*/ lemma_1_power(e: nat)
    ensures power(1, e) == 1
    decreases e
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_adds(b: int, e1: nat, e2: nat)
    ensures power(b, e1) * power(b, e2) == power(b, e1 + e2)
    decreases e1
  {
  }

  lemma /*{:_induction a, b, c}*/ lemma_power_multiplies(a: int, b: nat, c: nat)
    ensures 0 <= b * c
    ensures power(a, b * c) == power(power(a, b), c)
    decreases c
  {
  }

  lemma /*{:_induction a, b, e}*/ lemma_power_distributes(a: int, b: int, e: nat)
    ensures power(a * b, e) == power(a, e) * power(b, e)
    decreases e
  {
  }

  lemma lemma_power_auto()
    ensures forall x: int {:trigger power(x, 0)} :: power(x, 0) == 1
    ensures forall x: int {:trigger power(x, 1)} :: power(x, 1) == x
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 0 ==> power(x, y) == 1
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 1 ==> power(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y + z)} :: power(x, y + z) == power(x, y) * power(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y - z)} :: y >= z ==> power(x, y - z) * power(x, z) == power(x, y)
    ensures forall x: int, y: int, z: nat {:trigger power(x * y, z)} :: power(x * y, z) == power(x, z) * power(y, z)
  {
  }

  lemma /*{:_induction b, e}*/ lemma_power_positive(b: int, e: nat)
    requires 0 < b
    ensures 0 < power(b, e)
    decreases b, e
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_increases(b: nat, e1: nat, e2: nat)
    requires 0 < b
    requires e1 <= e2
    ensures power(b, e1) <= power(b, e2)
    decreases b, e1, e2
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_strictly_increases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures power(b, e1) < power(b, e2)
    decreases b, e1, e2
  {
  }

  lemma /*{:_induction x}*/ lemma_square_is_power_2(x: nat)
    ensures power(x, 2) == x * x
    decreases x
  {
  }
}

module Math__power_s {
  function {:opaque} {:fuel 0, 0} power(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * power(b, e - 1)
  }
}

module Math__mul_i {

  import opened Math__mul_nonlinear_i

  import opened Math__mul_auto_i
  function mul(x: int, y: int): int
    decreases x, y
  {
    x * y
  }

  function mul_recursive(x: int, y: int): int
    decreases x, y
  {
    if x >= 0 then
      mul_pos(x, y)
    else
      -1 * mul_pos(-1 * x, y)
  }

  function {:opaque} {:fuel 0, 0} mul_pos(x: int, y: int): int
    requires x >= 0
    decreases x, y
  {
    if x == 0 then
      0
    else
      y + mul_pos(x - 1, y)
  }

  lemma lemma_mul_is_mul_recursive(x: int, y: int)
    ensures x * y == mul_recursive(x, y)
    decreases x, y
  {
  }

  lemma /*{:_induction x, y}*/ lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
    decreases x, y
  {
  }

  lemma lemma_mul_basics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
    decreases x
  {
  }

  lemma lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
    decreases x, y
  {
  }

  lemma lemma_mul_ordering_general()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
  {
  }

  lemma lemma_mul_is_mul_boogie(x: int, y: int)
    decreases x, y
  {
  }

  lemma lemma_mul_inequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures x * z <= y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x <= x_bound
    requires y <= y_bound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= x_bound * y_bound
    decreases x, x_bound, y, y_bound
  {
  }

  lemma lemma_mul_strict_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x < x_bound
    requires y < y_bound
    requires 0 <= x
    requires 0 <= y
    ensures x * y < x_bound * y_bound
    decreases x, x_bound, y, y_bound
  {
  }

  lemma lemma_mul_left_inequality(x: int, y: int, z: int)
    requires x > 0
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures x < y
    decreases x, y, z
  {
  }

  lemma lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures x <= y
    decreases x, y, z
  {
  }

  lemma lemma_mul_equality_converse(x: int, y: int, z: int)
    requires x * z == y * z
    requires 0 < z
    ensures x == y
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
    decreases x, y, z
  {
  }

  lemma lemma_mul_strictly_increases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
    decreases x, y
  {
  }

  lemma lemma_mul_increases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_nonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures 0 <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_unary_negation(x: int, y: int)
    ensures -x * y == -(x * y) == x * -y
    decreases x, y
  {
  }

  lemma lemma_mul_one_to_one_pos(m: int, x: int, y: int)
    requires 0 < m
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma lemma_mul_one_to_one(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma lemma_mul_is_mul_recursive_forall()
    ensures forall x: int, y: int :: x * y == mul_recursive(x, y)
  {
  }

  lemma lemma_mul_basics_forall()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  lemma lemma_mul_is_commutative_forall()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma lemma_mul_ordering_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
  {
  }

  lemma lemma_mul_strict_inequality_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
  }

  lemma lemma_mul_inequality_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
  }

  lemma lemma_mul_strict_inequality_converse_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
  }

  lemma lemma_mul_inequality_converse_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
  }

  lemma lemma_mul_is_distributive_add_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
  }

  lemma lemma_mul_is_distributive_sub_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
  }

  lemma lemma_mul_is_distributive_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
  }

  lemma lemma_mul_is_associative_forall()
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
  {
  }

  lemma lemma_mul_nonzero_forall()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
  }

  lemma lemma_mul_nonnegative_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
  }

  lemma lemma_mul_unary_negation_forall()
    ensures forall x: int, y: int {:trigger -x * y} {:trigger x * -y} :: -x * y == -(x * y) == x * -y
  {
  }

  lemma lemma_mul_strictly_increases_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
  {
  }

  lemma lemma_mul_increases_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
  {
  }

  lemma lemma_mul_strictly_positive_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  lemma lemma_mul_one_to_one_forall()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: m != 0 && m * x == m * y ==> x == y
  {
  }

  lemma lemma_mul_by_zero_is_zero_forall()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
  }

  lemma lemma_mul_properties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1} {:trigger 1 * x} :: x * 1 == 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  function INTERNAL_mul_recursive(x: int, y: int): int
    decreases x, y
  {
    mul_recursive(x, y)
  }
}

module Math__mul_nonlinear_i {
  lemma lemma_mul_strictly_positive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_ordering(x: int, y: int)
    requires 0 < x
    requires 0 < y
    requires 0 <= x * y
    ensures x <= x * y && y <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_by_zero_is_zero(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    decreases x
  {
  }
}

module Math__mul_auto_i {

  import opened Math__mul_auto_proofs_i
  predicate MulAuto()
  {
    (forall x: int, y: int {:trigger x * y} :: 
      x * y == y * x) &&
    (forall x: int, y: int, z: int {:trigger (x + y) * z} :: 
      (x + y) * z == x * z + y * z) &&
    forall x: int, y: int, z: int {:trigger (x - y) * z} :: 
      (x - y) * z == x * z - y * z
  }

  lemma lemma_mul_auto()
    ensures MulAuto()
  {
  }

  predicate TMulAutoLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma lemma_mul_auto_induction(x: int, f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger TMulAutoLe(0, i)} :: TMulAutoLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger TMulAutoLe(i, 0)} :: TMulAutoLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures f(x)
    decreases x
  {
  }

  lemma lemma_mul_auto_induction_forall(f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger TMulAutoLe(0, i)} :: TMulAutoLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger TMulAutoLe(i, 0)} :: TMulAutoLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }
}

module Math__mul_auto_proofs_i {

  import opened Math__mul_nonlinear_i
  lemma lemma_mul_induction_helper(f: int -> bool, x: int)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures f(x)
    decreases if x >= 0 then x else -x
  {
  }

  lemma lemma_mul_induction_forall(f: int -> bool)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures forall i: int :: f(i)
  {
  }

  lemma lemma_mul_auto_commutes()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma lemma_mul_auto_succ()
    ensures forall x: int, y: int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x: int, y: int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
  }

  lemma lemma_mul_auto_distributes()
    ensures forall x: int, y: int, z: int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x: int, y: int, z: int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
  }
}

module Common__SeqIsUniqueDef_i {
  predicate {:opaque} {:fuel 0, 0} SeqIsUnique<X>(xs: seq<X>)
    decreases xs
  {
    forall i: int, j: int :: 
      0 <= i < |xs| &&
      0 <= j < |xs| &&
      xs[i] == xs[j] ==>
        i == j
  }
}

module Common__NetClient_i {

  import opened Native__Io_s
  function Workaround_CastHostEnvironmentToObject(env: HostEnvironment): object
    decreases env
  {
    env
  }

  function Workaround_CastOkStateToObject(okState: OkState): object
    decreases okState
  {
    okState
  }

  function Workaround_CastNowStateToObject(nowState: NowState): object
    decreases nowState
  {
    nowState
  }

  function Workaround_CastNetStateToObject(netState: NetState): object
    decreases netState
  {
    netState
  }

  function Workaround_CastNetClientToObject(netc: NetClient?): object?
    decreases netc
  {
    netc
  }

  function HostEnvironmentDefaultFrame(env: HostEnvironment): set<object>
    reads env, {env.now}, {env.ok}, {env.net}, {env}
    decreases {env.now} + {env.ok} + {env.net} + {env} + {env}, env
  {
    {Workaround_CastOkStateToObject(env.ok), Workaround_CastNowStateToObject(env.now), Workaround_CastNetStateToObject(env.net)}
  }

  function NetClientRepr(netc: NetClient?): set<object?>
    reads netc, if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}
    decreases (if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}) + {netc}, netc
  {
    {Workaround_CastNetClientToObject(netc)} + if netc != null then HostEnvironmentDefaultFrame(netc.env) else {}
  }

  predicate HostEnvironmentIsValid(env: HostEnvironment)
    reads env, env.Valid.reads(), env.ok.ok.reads()
    decreases env.Valid.reads() + env.ok.ok.reads() + {env}, env
  {
    env.Valid() &&
    env.ok.ok()
  }

  predicate NetClientOk(netc: NetClient?)
    reads netc, if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}
    decreases (if netc != null then HostEnvironmentDefaultFrame.reads(netc.env) else {}) + {netc}, netc
  {
    netc != null &&
    netc.env.ok.ok()
  }

  function method EndPointIsValidPublicKey(endPoint: EndPoint): bool
    decreases endPoint
  {
    true &&
    |endPoint.public_key| < 1048576
  }

  predicate NetClientIsValid(netc: NetClient?)
    reads NetClientRepr(netc), if netc != null then HostEnvironmentIsValid.reads(netc.env) else {}
    decreases NetClientRepr(netc) + if netc != null then HostEnvironmentIsValid.reads(netc.env) else {}, netc
  {
    netc != null &&
    netc.IsOpen() &&
    HostEnvironmentIsValid(netc.env) &&
    EndPointIsValidPublicKey(EndPoint(netc.MyPublicKey()))
  }

  predicate EndPointsAreValidPublicKeys(eps: seq<EndPoint>)
    decreases eps
  {
    forall i: int :: 
      0 <= i < |eps| ==>
        EndPointIsValidPublicKey(eps[i])
  }
}

abstract module Host_s {

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  type HostState

  type ConcreteConfiguration

  predicate HostInit(host_state: HostState, config: ConcreteConfiguration, id: EndPoint)
    reads *
    decreases {}, id

  predicate HostNext(host_state: HostState, host_state': HostState, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    reads *
    decreases {}, ios

  predicate ConcreteConfigInit(config: ConcreteConfiguration)

  function ConcreteConfigToServers(config: ConcreteConfiguration): set<EndPoint>

  predicate HostStateInvariants(host_state: HostState, env: HostEnvironment)
    reads *
    decreases {}, env

  function ParseCommandLineConfiguration(args: seq<seq<byte>>): ConcreteConfiguration
    decreases args

  predicate ArbitraryObject(o: object)
    decreases o
  {
    true
  }

  method HostInitImpl(ghost env: HostEnvironment, netc: NetClient, args: seq<seq<byte>>)
      returns (ok: bool, host_state: HostState)
    requires env.Valid()
    requires env.ok.ok()
    requires netc.IsOpen()
    requires netc.env == env
    requires ValidPhysicalAddress(EndPoint(netc.MyPublicKey()))
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok ==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state, env)
    ensures ok ==> var id: EndPoint := EndPoint(netc.MyPublicKey()); var config: ConcreteConfiguration := ParseCommandLineConfiguration(args); id in ConcreteConfigToServers(config) && ConcreteConfigInit(config) && HostInit(host_state, config, id)
    ensures env.net.history() == old(env.net.history())
    decreases env, netc, args

  method HostNextImpl(ghost env: HostEnvironment, host_state: HostState)
      returns (ok: bool, host_state': HostState, ghost recvs: seq<NetEvent>, ghost clocks: seq<NetEvent>, ghost sends: seq<NetEvent>, ghost ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires env.Valid() && env.ok.ok()
    requires HostStateInvariants(host_state, env)
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok <==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state', env)
    ensures ok ==> HostNext(host_state, host_state', ios)
    ensures ok ==> recvs + clocks + sends == ios
    ensures ok || |sends| > 0 ==> env.net.history() == old(env.net.history()) + (recvs + clocks + sends)
    ensures forall e: LIoOp<EndPoint, seq<byte>> :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1
    decreases env
}

module Collections__Sets_i {
  lemma ThingsIKnowAboutSubset<T>(x: set<T>, y: set<T>)
    requires x < y
    ensures |x| < |y|
    decreases x, y
  {
  }

  lemma SubsetCardinality<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
    decreases x, y
  {
  }

  lemma ItIsASingletonSet<T>(foo: set<T>, x: T)
    requires foo == {x}
    ensures |foo| == 1
    decreases foo
  {
  }

  lemma ThingsIKnowAboutASingletonSet<T>(foo: set<T>, x: T, y: T)
    requires |foo| == 1
    requires x in foo
    requires y in foo
    ensures x == y
    decreases foo
  {
  }

  predicate Injective<X(!new), Y>(f: X --> Y)
    requires forall x: X :: f.requires(x)
    reads f.reads
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0
  {
    forall x1: X, x2: X :: 
      f(x1) == f(x2) ==>
        x1 == x2
  }

  predicate InjectiveOver<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: x in xs ==> f.requires(x)
    reads f.reads
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs, ys
  {
    forall x1: X, x2: X :: 
      x1 in xs &&
      x2 in xs &&
      f(x1) in ys &&
      f(x2) in ys &&
      f(x1) == f(x2) ==>
        x1 == x2
  }

  predicate InjectiveOverSeq<X, Y>(xs: seq<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: x in xs ==> f.requires(x)
    reads f.reads
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs, ys
  {
    forall x1: X, x2: X :: 
      x1 in xs &&
      x2 in xs &&
      f(x1) in ys &&
      f(x2) in ys &&
      f(x1) == f(x2) ==>
        x1 == x2
  }

  lemma lemma_MapSetCardinality<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: f.requires(x)
    requires Injective(f)
    requires forall x: X :: x in xs <==> f(x) in ys
    requires forall y: Y :: y in ys ==> exists x: X :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSetCardinalityOver<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, ys, f)
    requires forall x: X :: x in xs ==> f(x) in ys
    requires forall y: Y :: y in ys ==> exists x: X :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSubsetCardinalityOver<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, ys, f)
    requires forall x: X :: x in xs ==> f(x) in ys
    ensures |xs| <= |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSubseqCardinalityOver<X, Y>(xs: seq<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X :: x in xs ==> f.requires(x)
    requires forall i: int, j: int :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
    requires InjectiveOverSeq(xs, ys, f)
    requires forall x: X :: x in xs ==> f(x) in ys
    ensures |xs| <= |ys|
    decreases xs, ys
  {
  }

  function MapSetToSet<X(!new), Y>(xs: set<X>, f: X --> Y): set<Y>
    requires forall x: X :: f.requires(x)
    requires Injective(f)
    reads f.reads
    ensures forall x: X :: x in xs <==> f(x) in MapSetToSet(xs, f)
    ensures |xs| == |MapSetToSet(xs, f)|
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    ghost var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    lemma_MapSetCardinality(xs, ys, f);
    ys
  }

  function MapSetToSetOver<X, Y>(xs: set<X>, f: X --> Y): set<Y>
    requires forall x: X :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x), f)
    reads f.reads
    ensures forall x: X :: x in xs ==> f(x) in MapSetToSetOver(xs, f)
    ensures |xs| == |MapSetToSetOver(xs, f)|
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    ghost var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    lemma_MapSetCardinalityOver(xs, ys, f);
    ys
  }

  function MapSeqToSet<X(!new), Y>(xs: seq<X>, f: X --> Y): set<Y>
    requires forall x: X :: f.requires(x)
    requires Injective(f)
    reads f.reads
    ensures forall x: X :: x in xs <==> f(x) in MapSeqToSet(xs, f)
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x)
  }

  function SeqToSet<X(!new)>(xs: seq<X>): set<X>
    decreases xs
  {
    set x: X {:trigger x in xs} | x in xs
  }

  lemma lemma_SubsetCardinality<X>(xs: set<X>, ys: set<X>, f: X --> bool)
    requires forall x: X :: x in xs ==> f.requires(x)
    requires forall x: X :: x in ys ==> x in xs && f(x)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
  }

  function MakeSubset<X(!new)>(xs: set<X>, f: X -> bool): set<X>
    requires forall x: X :: x in xs ==> f.requires(x)
    reads f.reads
    ensures forall x: X :: x in MakeSubset(xs, f) <==> x in xs && f(x)
    ensures |MakeSubset(xs, f)| <= |xs|
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    ghost var ys: set<X> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    lemma_SubsetCardinality(xs, ys, f);
    ys
  }

  lemma lemma_UnionCardinality<X>(xs: set<X>, ys: set<X>, us: set<X>)
    requires us == xs + ys
    ensures |us| >= |xs|
    decreases ys
  {
  }

  function SetOfNumbersInRightExclusiveRange(a: int, b: int): set<int>
    requires a <= b
    ensures forall opn: int :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b)
    ensures forall opn: int :: opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn < b
    ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b - a
    decreases b - a
  {
    if a == b then
      {}
    else
      {a} + SetOfNumbersInRightExclusiveRange(a + 1, b)
  }

  lemma lemma_CardinalityOfBoundedSet(s: set<int>, a: int, b: int)
    requires forall opn: int :: opn in s ==> a <= opn < b
    requires a <= b
    ensures |s| <= b - a
    decreases s, a, b
  {
  }

  function intsetmax(s: set<int>): int
    requires |s| > 0
    ensures ghost var m: int := intsetmax(s); m in s && forall i: int :: i in s ==> m >= i
    decreases s
  {
    ghost var x: int :| x in s;
    if |s| == 1 then
      assert |s - {x}| == 0;
      x
    else
      ghost var sy: set<int> := s - {x}; ghost var y: int := intsetmax(sy); assert forall i: int :: i in s ==> i in sy || i == x; if x > y then x else y
  }
}

abstract module DistributedSystem_s {

  import H_s : Host_s

  import opened Collections__Maps2_s

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  datatype DS_State = DS_State(config: H_s.ConcreteConfiguration, environment: LEnvironment<EndPoint, seq<byte>>, servers: map<EndPoint, H_s.HostState>)

  predicate ValidPhysicalEnvironmentStep(step: LEnvStep<EndPoint, seq<byte>>)
    decreases step
  {
    step.LEnvStepHostIos? ==>
      forall io: LIoOp<EndPoint, seq<byte>> {:trigger io in step.ios} {:trigger ValidPhysicalIo(io)} :: 
        io in step.ios ==>
          ValidPhysicalIo(io)
  }

  predicate DS_Init(s: DS_State, config: H_s.ConcreteConfiguration)
    reads *
    decreases {}, s
  {
    s.config == config &&
    H_s.ConcreteConfigToServers(s.config) == mapdomain(s.servers) &&
    H_s.ConcreteConfigInit(s.config) &&
    LEnvironment_Init(s.environment) &&
    forall id: EndPoint :: 
      id in s.servers ==>
        H_s.HostInit(s.servers[id], config, id)
  }

  predicate DS_NextOneServer(s: DS_State, s': DS_State, id: EndPoint, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires id in s.servers
    reads *
    decreases {}, s, s', id, ios
  {
    id in s'.servers &&
    H_s.HostNext(s.servers[id], s'.servers[id], ios) &&
    s'.servers == s.servers[id := s'.servers[id]]
  }

  predicate DS_Next(s: DS_State, s': DS_State)
    reads *
    decreases {}, s, s'
  {
    s'.config == s.config &&
    LEnvironment_Next(s.environment, s'.environment) &&
    ValidPhysicalEnvironmentStep(s.environment.nextStep) &&
    if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then DS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios) else s'.servers == s.servers
  }
}

abstract module Main_s {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened DS_s : DistributedSystem_s

  import opened AS_s : AbstractService_s

  import opened Collections__Seqs_s
  method IronfleetMain(ghost env: HostEnvironment, netc: NetClient, args: seq<seq<byte>>)
    requires env.Valid() && env.ok.ok()
    requires env.net.history() == []
    requires netc.IsOpen()
    requires netc.env == env
    requires ValidPhysicalAddress(EndPoint(netc.MyPublicKey()))
    modifies set x: object {:trigger DS_s.H_s.ArbitraryObject(x)} | DS_s.H_s.ArbitraryObject(x)
    decreases *
  {
    var ok, host_state := DS_s.H_s.HostInitImpl(env, netc, args);
    ghost var config := DS_s.H_s.ParseCommandLineConfiguration(args);
    var id := EndPoint(netc.MyPublicKey());
    assert ok ==> DS_s.H_s.HostInit(host_state, config, id);
    while ok
      invariant ok ==> DS_s.H_s.HostStateInvariants(host_state, env)
      invariant ok ==> env.Valid() && env.ok.ok()
      decreases *
    {
      ghost var old_net_history := env.net.history();
      ghost var old_state := host_state;
      ghost var recvs, clocks, sends, ios;
      ok, host_state, recvs, clocks, sends, ios := DS_s.H_s.HostNextImpl(env, host_state);
      if ok {
        assert DS_s.H_s.HostNext(old_state, host_state, ios);
        assert recvs + clocks + sends == ios;
        assert env.net.history() == old_net_history + recvs + clocks + sends;
        assert forall e: LIoOp<EndPoint, seq<byte>> :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?);
        assert |clocks| <= 1;
      }
    }
  }

  lemma RefinementProof(config: DS_s.H_s.ConcreteConfiguration, db: seq<DS_State>) returns (sb: seq<ServiceState>)
    requires |db| > 0
    requires DS_Init(db[0], config)
    requires forall i: int {:trigger DS_Next(db[i], db[i + 1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i + 1])
    ensures |db| == |sb|
    ensures Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers))
    ensures forall i: int {:trigger Service_Next(sb[i], sb[i + 1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i + 1] || Service_Next(sb[i], sb[i + 1])
    ensures forall i: int :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i])
    decreases db
}

module Collections__Seqs_s {
  function last<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[|s| - 1]
  }

  function all_but_last<T>(s: seq<T>): seq<T>
    requires |s| > 0
    ensures |all_but_last(s)| == |s| - 1
    decreases s
  {
    s[..|s| - 1]
  }
}

module Concrete_NodeIdentity_i refines Common__NodeIdentity_s {

  import opened Native__Io_s

  export Spec
    provides NodeIdentity


  export
    reveals *
    provides Native__Io_s
    reveals NodeIdentity

  type /*{:_provided}*/ NodeIdentity = EndPoint
}

abstract module Common__NodeIdentity_s {
  type NodeIdentity(==)
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(Array.Empty<T>());

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += ")";
      return s;
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
  }

  public interface _ITuple1<out T1> {
    T1 dtor__0 { get; }
    _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0);
  }
  public class Tuple1<T1> : _ITuple1<T1> {
    public readonly T1 _0;
    public Tuple1(T1 _0) {
      this._0 = _0;
    }
    public _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0) {
      if (this is _ITuple1<__T1> dt) { return dt; }
      return new Tuple1<__T1>(converter0(_0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T1>;
      return oth != null && object.Equals(this._0, oth._0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ")";
      return s;
    }
    public static _ITuple1<T1> Default(T1 _default_T1) {
      return create(_default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T1>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T1>>(_System.Tuple1<T1>.Default(_td_T1.Default()));
    }
    public static _ITuple1<T1> create(T1 _0) {
      return new Tuple1<T1>(_0);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(_0), converter1(_1), converter2(_2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ")";
      return s;
    }
    public static _ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(_0), converter1(_1), converter2(_2), converter3(_3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ")";
      return s;
    }
    public static _ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ")";
      return s;
    }
    public static _ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ")";
      return s;
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ")";
      return s;
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ")";
      return s;
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ")";
      return s;
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ")";
      return s;
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ")";
      return s;
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ")";
      return s;
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ")";
      return s;
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ")";
      return s;
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ")";
      return s;
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ")";
      return s;
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ")";
      return s;
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ")";
      return s;
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ")";
      return s;
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public readonly T19 _19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
      this._19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18), converter19(_19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18) && object.Equals(this._19, oth._19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._19));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ", ";
      s += Dafny.Helpers.ToString(this._19);
      s += ")";
      return s;
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
    public T19 dtor__19 {
      get {
        return this._19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Native____NativeTypes__s_Compile {

  public partial class @sbyte {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace Native____NativeTypes__s_Compile
namespace Collections____Maps2__s_Compile {

} // end of namespace Collections____Maps2__s_Compile
namespace Temporal____Temporal__s_Compile {

} // end of namespace Temporal____Temporal__s_Compile
namespace Environment__s_Compile {

  public interface _ILPacket<IdType, MessageType> {
    bool is_LPacket { get; }
    IdType dtor_dst { get; }
    IdType dtor_src { get; }
    MessageType dtor_msg { get; }
    _ILPacket<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LPacket<IdType, MessageType> : _ILPacket<IdType, MessageType> {
    public readonly IdType _dst;
    public readonly IdType _src;
    public readonly MessageType _msg;
    public LPacket(IdType dst, IdType src, MessageType msg) {
      this._dst = dst;
      this._src = src;
      this._msg = msg;
    }
    public _ILPacket<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILPacket<__IdType, __MessageType> dt) { return dt; }
      return new LPacket<__IdType, __MessageType>(converter0(_dst), converter0(_src), converter1(_msg));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LPacket<IdType, MessageType>;
      return oth != null && object.Equals(this._dst, oth._dst) && object.Equals(this._src, oth._src) && object.Equals(this._msg, oth._msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dst));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._src));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._msg));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LPacket.LPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._dst);
      s += ", ";
      s += Dafny.Helpers.ToString(this._src);
      s += ", ";
      s += Dafny.Helpers.ToString(this._msg);
      s += ")";
      return s;
    }
    public static _ILPacket<IdType, MessageType> Default(IdType _default_IdType, MessageType _default_MessageType) {
      return create(_default_IdType, _default_IdType, _default_MessageType);
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILPacket<IdType, MessageType>> _TypeDescriptor(Dafny.TypeDescriptor<IdType> _td_IdType, Dafny.TypeDescriptor<MessageType> _td_MessageType) {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILPacket<IdType, MessageType>>(Environment__s_Compile.LPacket<IdType, MessageType>.Default(_td_IdType.Default(), _td_MessageType.Default()));
    }
    public static _ILPacket<IdType, MessageType> create(IdType dst, IdType src, MessageType msg) {
      return new LPacket<IdType, MessageType>(dst, src, msg);
    }
    public bool is_LPacket { get { return true; } }
    public IdType dtor_dst {
      get {
        return this._dst;
      }
    }
    public IdType dtor_src {
      get {
        return this._src;
      }
    }
    public MessageType dtor_msg {
      get {
        return this._msg;
      }
    }
  }

  public interface _ILIoOp<IdType, MessageType> {
    bool is_LIoOpSend { get; }
    bool is_LIoOpReceive { get; }
    bool is_LIoOpTimeoutReceive { get; }
    bool is_LIoOpReadClock { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_s { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_r { get; }
    BigInteger dtor_t { get; }
    _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public abstract class LIoOp<IdType, MessageType> : _ILIoOp<IdType, MessageType> {
    public LIoOp() { }
    public static _ILIoOp<IdType, MessageType> Default() {
      return create_LIoOpTimeoutReceive();
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILIoOp<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILIoOp<IdType, MessageType>>(Environment__s_Compile.LIoOp<IdType, MessageType>.Default());
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpSend(Environment__s_Compile._ILPacket<IdType, MessageType> s) {
      return new LIoOp_LIoOpSend<IdType, MessageType>(s);
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpReceive(Environment__s_Compile._ILPacket<IdType, MessageType> r) {
      return new LIoOp_LIoOpReceive<IdType, MessageType>(r);
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpTimeoutReceive() {
      return new LIoOp_LIoOpTimeoutReceive<IdType, MessageType>();
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpReadClock(BigInteger t) {
      return new LIoOp_LIoOpReadClock<IdType, MessageType>(t);
    }
    public bool is_LIoOpSend { get { return this is LIoOp_LIoOpSend<IdType, MessageType>; } }
    public bool is_LIoOpReceive { get { return this is LIoOp_LIoOpReceive<IdType, MessageType>; } }
    public bool is_LIoOpTimeoutReceive { get { return this is LIoOp_LIoOpTimeoutReceive<IdType, MessageType>; } }
    public bool is_LIoOpReadClock { get { return this is LIoOp_LIoOpReadClock<IdType, MessageType>; } }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_s {
      get {
        var d = this;
        return ((LIoOp_LIoOpSend<IdType, MessageType>)d)._s;
      }
    }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_r {
      get {
        var d = this;
        return ((LIoOp_LIoOpReceive<IdType, MessageType>)d)._r;
      }
    }
    public BigInteger dtor_t {
      get {
        var d = this;
        return ((LIoOp_LIoOpReadClock<IdType, MessageType>)d)._t;
      }
    }
    public abstract _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LIoOp_LIoOpSend<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _s;
    public LIoOp_LIoOpSend(Environment__s_Compile._ILPacket<IdType, MessageType> s) {
      this._s = s;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpSend<__IdType, __MessageType>((_s).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpSend<IdType, MessageType>;
      return oth != null && object.Equals(this._s, oth._s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Environment__s_Compile.LIoOp.LIoOpSend";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ")";
      return ss;
    }
  }
  public class LIoOp_LIoOpReceive<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _r;
    public LIoOp_LIoOpReceive(Environment__s_Compile._ILPacket<IdType, MessageType> r) {
      this._r = r;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpReceive<__IdType, __MessageType>((_r).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpReceive<IdType, MessageType>;
      return oth != null && object.Equals(this._r, oth._r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpReceive";
      s += "(";
      s += Dafny.Helpers.ToString(this._r);
      s += ")";
      return s;
    }
  }
  public class LIoOp_LIoOpTimeoutReceive<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public LIoOp_LIoOpTimeoutReceive() {
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpTimeoutReceive<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpTimeoutReceive<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpTimeoutReceive";
      return s;
    }
  }
  public class LIoOp_LIoOpReadClock<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly BigInteger _t;
    public LIoOp_LIoOpReadClock(BigInteger t) {
      this._t = t;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpReadClock<__IdType, __MessageType>(_t);
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpReadClock<IdType, MessageType>;
      return oth != null && this._t == oth._t;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpReadClock";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }

  public interface _ILEnvStep<IdType, MessageType> {
    bool is_LEnvStepHostIos { get; }
    bool is_LEnvStepDeliverPacket { get; }
    bool is_LEnvStepAdvanceTime { get; }
    bool is_LEnvStepStutter { get; }
    IdType dtor_actor { get; }
    Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> dtor_ios { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_p { get; }
    _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public abstract class LEnvStep<IdType, MessageType> : _ILEnvStep<IdType, MessageType> {
    public LEnvStep() { }
    public static _ILEnvStep<IdType, MessageType> Default() {
      return create_LEnvStepAdvanceTime();
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILEnvStep<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILEnvStep<IdType, MessageType>>(Environment__s_Compile.LEnvStep<IdType, MessageType>.Default());
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepHostIos(IdType actor, Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> ios) {
      return new LEnvStep_LEnvStepHostIos<IdType, MessageType>(actor, ios);
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepDeliverPacket(Environment__s_Compile._ILPacket<IdType, MessageType> p) {
      return new LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>(p);
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepAdvanceTime() {
      return new LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>();
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepStutter() {
      return new LEnvStep_LEnvStepStutter<IdType, MessageType>();
    }
    public bool is_LEnvStepHostIos { get { return this is LEnvStep_LEnvStepHostIos<IdType, MessageType>; } }
    public bool is_LEnvStepDeliverPacket { get { return this is LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>; } }
    public bool is_LEnvStepAdvanceTime { get { return this is LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>; } }
    public bool is_LEnvStepStutter { get { return this is LEnvStep_LEnvStepStutter<IdType, MessageType>; } }
    public IdType dtor_actor {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepHostIos<IdType, MessageType>)d)._actor;
      }
    }
    public Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> dtor_ios {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepHostIos<IdType, MessageType>)d)._ios;
      }
    }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_p {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>)d)._p;
      }
    }
    public abstract _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LEnvStep_LEnvStepHostIos<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public readonly IdType _actor;
    public readonly Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> _ios;
    public LEnvStep_LEnvStepHostIos(IdType actor, Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> ios) {
      this._actor = actor;
      this._ios = ios;
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepHostIos<__IdType, __MessageType>(converter0(_actor), (_ios).DowncastClone<Environment__s_Compile._ILIoOp<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILIoOp<IdType, MessageType>, Environment__s_Compile._ILIoOp<__IdType, __MessageType>>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepHostIos<IdType, MessageType>;
      return oth != null && object.Equals(this._actor, oth._actor) && object.Equals(this._ios, oth._ios);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._actor));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ios));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepHostIos";
      s += "(";
      s += Dafny.Helpers.ToString(this._actor);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ios);
      s += ")";
      return s;
    }
  }
  public class LEnvStep_LEnvStepDeliverPacket<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _p;
    public LEnvStep_LEnvStepDeliverPacket(Environment__s_Compile._ILPacket<IdType, MessageType> p) {
      this._p = p;
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepDeliverPacket<__IdType, __MessageType>((_p).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>;
      return oth != null && object.Equals(this._p, oth._p);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._p));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepDeliverPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._p);
      s += ")";
      return s;
    }
  }
  public class LEnvStep_LEnvStepAdvanceTime<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public LEnvStep_LEnvStepAdvanceTime() {
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepAdvanceTime<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepAdvanceTime";
      return s;
    }
  }
  public class LEnvStep_LEnvStepStutter<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public LEnvStep_LEnvStepStutter() {
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepStutter<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepStutter<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepStutter";
      return s;
    }
  }

  public interface _ILHostInfo<IdType, MessageType> {
    bool is_LHostInfo { get; }
    Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_queue { get; }
    _ILHostInfo<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LHostInfo<IdType, MessageType> : _ILHostInfo<IdType, MessageType> {
    public readonly Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> _queue;
    public LHostInfo(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> queue) {
      this._queue = queue;
    }
    public _ILHostInfo<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILHostInfo<__IdType, __MessageType> dt) { return dt; }
      return new LHostInfo<__IdType, __MessageType>((_queue).DowncastClone<Environment__s_Compile._ILPacket<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILPacket<IdType, MessageType>, Environment__s_Compile._ILPacket<__IdType, __MessageType>>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LHostInfo<IdType, MessageType>;
      return oth != null && object.Equals(this._queue, oth._queue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LHostInfo.LHostInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._queue);
      s += ")";
      return s;
    }
    public static _ILHostInfo<IdType, MessageType> Default() {
      return create(Dafny.Sequence<Environment__s_Compile._ILPacket<IdType, MessageType>>.Empty);
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILHostInfo<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILHostInfo<IdType, MessageType>>(Environment__s_Compile.LHostInfo<IdType, MessageType>.Default());
    }
    public static _ILHostInfo<IdType, MessageType> create(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> queue) {
      return new LHostInfo<IdType, MessageType>(queue);
    }
    public bool is_LHostInfo { get { return true; } }
    public Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_queue {
      get {
        return this._queue;
      }
    }
  }

  public interface _ILEnvironment<IdType, MessageType> {
    bool is_LEnvironment { get; }
    BigInteger dtor_time { get; }
    Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_sentPackets { get; }
    Dafny.IMap<IdType,Environment__s_Compile._ILHostInfo<IdType, MessageType>> dtor_hostInfo { get; }
    Environment__s_Compile._ILEnvStep<IdType, MessageType> dtor_nextStep { get; }
    _ILEnvironment<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LEnvironment<IdType, MessageType> : _ILEnvironment<IdType, MessageType> {
    public readonly BigInteger _time;
    public readonly Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> _sentPackets;
    public readonly Dafny.IMap<IdType,Environment__s_Compile._ILHostInfo<IdType, MessageType>> _hostInfo;
    public readonly Environment__s_Compile._ILEnvStep<IdType, MessageType> _nextStep;
    public LEnvironment(BigInteger time, Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> sentPackets, Dafny.IMap<IdType,Environment__s_Compile._ILHostInfo<IdType, MessageType>> hostInfo, Environment__s_Compile._ILEnvStep<IdType, MessageType> nextStep) {
      this._time = time;
      this._sentPackets = sentPackets;
      this._hostInfo = hostInfo;
      this._nextStep = nextStep;
    }
    public _ILEnvironment<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvironment<__IdType, __MessageType> dt) { return dt; }
      return new LEnvironment<__IdType, __MessageType>(_time, (_sentPackets).DowncastClone<Environment__s_Compile._ILPacket<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILPacket<IdType, MessageType>, Environment__s_Compile._ILPacket<__IdType, __MessageType>>), (_hostInfo).DowncastClone<__IdType, Environment__s_Compile._ILHostInfo<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<Environment__s_Compile._ILHostInfo<IdType, MessageType>, Environment__s_Compile._ILHostInfo<__IdType, __MessageType>>), (_nextStep).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvironment<IdType, MessageType>;
      return oth != null && this._time == oth._time && object.Equals(this._sentPackets, oth._sentPackets) && object.Equals(this._hostInfo, oth._hostInfo) && object.Equals(this._nextStep, oth._nextStep);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._time));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sentPackets));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hostInfo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nextStep));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvironment.LEnvironment";
      s += "(";
      s += Dafny.Helpers.ToString(this._time);
      s += ", ";
      s += Dafny.Helpers.ToString(this._sentPackets);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hostInfo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nextStep);
      s += ")";
      return s;
    }
    public static _ILEnvironment<IdType, MessageType> Default() {
      return create(BigInteger.Zero, Dafny.Set<Environment__s_Compile._ILPacket<IdType, MessageType>>.Empty, Dafny.Map<IdType, Environment__s_Compile._ILHostInfo<IdType, MessageType>>.Empty, Environment__s_Compile.LEnvStep<IdType, MessageType>.Default());
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILEnvironment<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILEnvironment<IdType, MessageType>>(Environment__s_Compile.LEnvironment<IdType, MessageType>.Default());
    }
    public static _ILEnvironment<IdType, MessageType> create(BigInteger time, Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> sentPackets, Dafny.IMap<IdType,Environment__s_Compile._ILHostInfo<IdType, MessageType>> hostInfo, Environment__s_Compile._ILEnvStep<IdType, MessageType> nextStep) {
      return new LEnvironment<IdType, MessageType>(time, sentPackets, hostInfo, nextStep);
    }
    public bool is_LEnvironment { get { return true; } }
    public BigInteger dtor_time {
      get {
        return this._time;
      }
    }
    public Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_sentPackets {
      get {
        return this._sentPackets;
      }
    }
    public Dafny.IMap<IdType,Environment__s_Compile._ILHostInfo<IdType, MessageType>> dtor_hostInfo {
      get {
        return this._hostInfo;
      }
    }
    public Environment__s_Compile._ILEnvStep<IdType, MessageType> dtor_nextStep {
      get {
        return this._nextStep;
      }
    }
  }

} // end of namespace Environment__s_Compile
namespace Native____Io__s_Compile {

  public partial class HostEnvironment {
    public HostEnvironment() {
    }
  }

  public partial class OkState {
    public OkState() {
    }
  }

  public partial class PrintParams {
    public PrintParams() {
    }
  }

  public partial class NowState {
    public NowState() {
    }
  }

  public partial class Time {
    public Time() {
    }
  }

  public interface _IEndPoint {
    bool is_EndPoint { get; }
    Dafny.ISequence<byte> dtor_public__key { get; }
    _IEndPoint DowncastClone();
  }
  public class EndPoint : _IEndPoint {
    public readonly Dafny.ISequence<byte> _public__key;
    public EndPoint(Dafny.ISequence<byte> public__key) {
      this._public__key = public__key;
    }
    public _IEndPoint DowncastClone() {
      if (this is _IEndPoint dt) { return dt; }
      return new EndPoint(_public__key);
    }
    public override bool Equals(object other) {
      var oth = other as Native____Io__s_Compile.EndPoint;
      return oth != null && object.Equals(this._public__key, oth._public__key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._public__key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Native____Io__s_Compile.EndPoint.EndPoint";
      s += "(";
      s += Dafny.Helpers.ToString(this._public__key);
      s += ")";
      return s;
    }
    private static readonly _IEndPoint theDefault = create(Dafny.Sequence<byte>.Empty);
    public static _IEndPoint Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint> _TYPE = new Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint>(Native____Io__s_Compile.EndPoint.Default());
    public static Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEndPoint create(Dafny.ISequence<byte> public__key) {
      return new EndPoint(public__key);
    }
    public bool is_EndPoint { get { return true; } }
    public Dafny.ISequence<byte> dtor_public__key {
      get {
        return this._public__key;
      }
    }
  }

  public partial class NetState {
    public NetState() {
    }
  }

  public partial class NetClient {
    public NetClient() {
    }
  }

  public partial class FileSystemState {
    public FileSystemState() {
    }
  }

  public partial class MutableSet<T> {
    private Dafny.TypeDescriptor<T> _td_T;
    public MutableSet(Dafny.TypeDescriptor<T> _td_T) {
      this._td_T = _td_T;
    }
  }

  public partial class MutableMap<K, V> {
    public MutableMap() {
    }
  }

  public partial class Arrays {
    public Arrays() {
    }
  }

} // end of namespace Native____Io__s_Compile
namespace Collections____Seqs__s_Compile {

} // end of namespace Collections____Seqs__s_Compile
namespace AbstractServiceSimplest__s_Compile {

  public interface _IServiceState_k {
    bool is_ServiceState_k { get; }
    Dafny.ISet<Native____Io__s_Compile._IEndPoint> dtor_hosts { get; }
    _IServiceState_k DowncastClone();
  }
  public class ServiceState_k : _IServiceState_k {
    public readonly Dafny.ISet<Native____Io__s_Compile._IEndPoint> _hosts;
    public ServiceState_k(Dafny.ISet<Native____Io__s_Compile._IEndPoint> hosts) {
      this._hosts = hosts;
    }
    public _IServiceState_k DowncastClone() {
      if (this is _IServiceState_k dt) { return dt; }
      return new ServiceState_k(_hosts);
    }
    public override bool Equals(object other) {
      var oth = other as AbstractServiceSimplest__s_Compile.ServiceState_k;
      return oth != null && object.Equals(this._hosts, oth._hosts);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hosts));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AbstractServiceSimplest__s_Compile.ServiceState'.ServiceState'";
      s += "(";
      s += Dafny.Helpers.ToString(this._hosts);
      s += ")";
      return s;
    }
    private static readonly _IServiceState_k theDefault = create(Dafny.Set<Native____Io__s_Compile._IEndPoint>.Empty);
    public static _IServiceState_k Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AbstractServiceSimplest__s_Compile._IServiceState_k> _TYPE = new Dafny.TypeDescriptor<AbstractServiceSimplest__s_Compile._IServiceState_k>(AbstractServiceSimplest__s_Compile.ServiceState_k.Default());
    public static Dafny.TypeDescriptor<AbstractServiceSimplest__s_Compile._IServiceState_k> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IServiceState_k create(Dafny.ISet<Native____Io__s_Compile._IEndPoint> hosts) {
      return new ServiceState_k(hosts);
    }
    public bool is_ServiceState_k { get { return true; } }
    public Dafny.ISet<Native____Io__s_Compile._IEndPoint> dtor_hosts {
      get {
        return this._hosts;
      }
    }
  }

} // end of namespace AbstractServiceSimplest__s_Compile
namespace Math____power__s_Compile {

} // end of namespace Math____power__s_Compile
namespace Common____SeqIsUniqueDef__i_Compile {

} // end of namespace Common____SeqIsUniqueDef__i_Compile
namespace Common____NetClient__i_Compile {

  public partial class __default {
    public static bool EndPointIsValidPublicKey(Native____Io__s_Compile._IEndPoint endPoint) {
      return (true) && ((new BigInteger(((endPoint).dtor_public__key).Count)) < (new BigInteger(1048576)));
    }
  }
} // end of namespace Common____NetClient__i_Compile
namespace CmdLineParser__i_Compile {

  public partial class __default {
    public static _System._ITuple2<bool, Native____Io__s_Compile._IEndPoint> parse__end__point(Dafny.ISequence<byte> public__key) {
      if ((new BigInteger((public__key).Count)) < (new BigInteger(1048576))) {
        return _System.Tuple2<bool, Native____Io__s_Compile._IEndPoint>.create(true, Native____Io__s_Compile.EndPoint.create(public__key));
      } else {
        return _System.Tuple2<bool, Native____Io__s_Compile._IEndPoint>.create(false, Native____Io__s_Compile.EndPoint.create(public__key));
      }
    }
    public static bool test__unique(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> endpoints)
    {
      bool unique = false;
      unique = true;
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((endpoints).Count))) {
        BigInteger _1_j;
        _1_j = BigInteger.Zero;
        while ((_1_j) < (new BigInteger((endpoints).Count))) {
          if (((_0_i) != (_1_j)) && (object.Equals((endpoints).Select(_0_i), (endpoints).Select(_1_j)))) {
            unique = false;
            return unique;
          }
          _1_j = (_1_j) + (BigInteger.One);
        }
        _0_i = (_0_i) + (BigInteger.One);
      }
      return unique;
    }
    public static _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> parse__end__points(Dafny.ISequence<Dafny.ISequence<byte>> args) {
      if ((new BigInteger((args).Count)).Sign == 0) {
        return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(true, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements());
      } else {
        _System._ITuple2<bool, Native____Io__s_Compile._IEndPoint> _let_tmp_rhs0 = CmdLineParser__i_Compile.__default.parse__end__point((args).Select(BigInteger.Zero));
        bool _2_ok1 = _let_tmp_rhs0.dtor__0;
        Native____Io__s_Compile._IEndPoint _3_ep = _let_tmp_rhs0.dtor__1;
        _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> _let_tmp_rhs1 = CmdLineParser__i_Compile.__default.parse__end__points((args).Drop(BigInteger.One));
        bool _4_ok2 = _let_tmp_rhs1.dtor__0;
        Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _5_rest = _let_tmp_rhs1.dtor__1;
        if (!((_2_ok1) && (_4_ok2))) {
          return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(false, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements());
        } else {
          return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(true, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Concat(Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements(_3_ep), _5_rest));
        }
      }
    }
    public static void GetHostIndex(Native____Io__s_Compile._IEndPoint host, Dafny.ISequence<Native____Io__s_Compile._IEndPoint> hosts, out bool found, out ulong index)
    {
      found = false;
      index = 0;
      ulong _6_i;
      _6_i = 0UL;
      while ((_6_i) < ((ulong)(hosts).LongCount)) {
        if (object.Equals(host, (hosts).Select(_6_i))) {
          found = true;
          index = _6_i;
          return ;
        }
        if ((_6_i) == (((ulong)(hosts).LongCount) - (1UL))) {
          found = false;
          return ;
        }
        _6_i = (_6_i) + (1UL);
      }
      found = false;
    }
  }
} // end of namespace CmdLineParser__i_Compile
namespace SimplestCmdLineParser__i_Compile {

  public partial class __default {
    public static void parse__cmd__line(Native____Io__s_Compile._IEndPoint id, Dafny.ISequence<Dafny.ISequence<byte>> args, out bool ok, out Dafny.ISequence<Native____Io__s_Compile._IEndPoint> host__ids, out ulong my__index)
    {
      ok = false;
      host__ids = Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty;
      my__index = 0;
      _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> _7_tuple1;
      _7_tuple1 = CmdLineParser__i_Compile.__default.parse__end__points(args);
      ok = (_7_tuple1).dtor__0;
      if (!(ok)) {
        return ;
      }
      host__ids = (_7_tuple1).dtor__1;
      if (((new BigInteger((host__ids).Count)).Sign == 0) || ((new BigInteger((host__ids).Count)) >= (BigInteger.Parse("18446744073709551616")))) {
        ok = false;
        return ;
      }
      bool _8_unique;
      bool _out0;
      _out0 = CmdLineParser__i_Compile.__default.test__unique(host__ids);
      _8_unique = _out0;
      if (!(_8_unique)) {
        ok = false;
        return ;
      }
      bool _out1;
      ulong _out2;
      CmdLineParser__i_Compile.__default.GetHostIndex(id, host__ids, out _out1, out _out2);
      ok = _out1;
      my__index = _out2;
      if (!(ok)) {
        return ;
      }
    }
  }
} // end of namespace SimplestCmdLineParser__i_Compile
namespace Collections____Sets__i_Compile {

} // end of namespace Collections____Sets__i_Compile
namespace Host__i_Compile {

  public partial class __default {
    public static void HostInitImpl(Native____Io__s_Compile.NetClient netc, Dafny.ISequence<Dafny.ISequence<byte>> args, out bool ok, out BigInteger host__state)
    {
      ok = false;
      host__state = BigInteger.Zero;
      ulong _9_my__index = 0;
      host__state = BigInteger.Zero;
      Native____Io__s_Compile._IEndPoint _10_id;
      _10_id = Native____Io__s_Compile.EndPoint.create((netc).MyPublicKey());
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("My id is: "));
      Dafny.Helpers.Print(_10_id);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _11_config = Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty;
      bool _out3;
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _out4;
      ulong _out5;
      SimplestCmdLineParser__i_Compile.__default.parse__cmd__line(_10_id, args, out _out3, out _out4, out _out5);
      ok = _out3;
      _11_config = _out4;
      _9_my__index = _out5;
      if (!(ok)) {
        return ;
      }
    }
    public static void HostNextImpl(BigInteger host__state, out bool ok, out BigInteger host__state_k)
    {
      ok = false;
      host__state_k = BigInteger.Zero;
      ok = true;
      host__state_k = host__state;
    }
  }
} // end of namespace Host__i_Compile
namespace Simplest__DistributedSystem__i_Compile {


  public interface _IDS__State {
    bool is_DS__State { get; }
    Dafny.ISequence<Native____Io__s_Compile._IEndPoint> dtor_config { get; }
    Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> dtor_environment { get; }
    Dafny.IMap<Native____Io__s_Compile._IEndPoint,BigInteger> dtor_servers { get; }
    _IDS__State DowncastClone();
  }
  public class DS__State : _IDS__State {
    public readonly Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _config;
    public readonly Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> _environment;
    public readonly Dafny.IMap<Native____Io__s_Compile._IEndPoint,BigInteger> _servers;
    public DS__State(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> environment, Dafny.IMap<Native____Io__s_Compile._IEndPoint,BigInteger> servers) {
      this._config = config;
      this._environment = environment;
      this._servers = servers;
    }
    public _IDS__State DowncastClone() {
      if (this is _IDS__State dt) { return dt; }
      return new DS__State(_config, _environment, _servers);
    }
    public override bool Equals(object other) {
      var oth = other as Simplest__DistributedSystem__i_Compile.DS__State;
      return oth != null && object.Equals(this._config, oth._config) && object.Equals(this._environment, oth._environment) && object.Equals(this._servers, oth._servers);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._config));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._environment));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._servers));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Simplest__DistributedSystem__i_Compile.DS_State.DS_State";
      s += "(";
      s += Dafny.Helpers.ToString(this._config);
      s += ", ";
      s += Dafny.Helpers.ToString(this._environment);
      s += ", ";
      s += Dafny.Helpers.ToString(this._servers);
      s += ")";
      return s;
    }
    private static readonly _IDS__State theDefault = create(Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty, Environment__s_Compile.LEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>>.Default(), Dafny.Map<Native____Io__s_Compile._IEndPoint, BigInteger>.Empty);
    public static _IDS__State Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Simplest__DistributedSystem__i_Compile._IDS__State> _TYPE = new Dafny.TypeDescriptor<Simplest__DistributedSystem__i_Compile._IDS__State>(Simplest__DistributedSystem__i_Compile.DS__State.Default());
    public static Dafny.TypeDescriptor<Simplest__DistributedSystem__i_Compile._IDS__State> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDS__State create(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> environment, Dafny.IMap<Native____Io__s_Compile._IEndPoint,BigInteger> servers) {
      return new DS__State(config, environment, servers);
    }
    public bool is_DS__State { get { return true; } }
    public Dafny.ISequence<Native____Io__s_Compile._IEndPoint> dtor_config {
      get {
        return this._config;
      }
    }
    public Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> dtor_environment {
      get {
        return this._environment;
      }
    }
    public Dafny.IMap<Native____Io__s_Compile._IEndPoint,BigInteger> dtor_servers {
      get {
        return this._servers;
      }
    }
  }
} // end of namespace Simplest__DistributedSystem__i_Compile
namespace Concrete__NodeIdentity__i_Compile {

} // end of namespace Concrete__NodeIdentity__i_Compile
namespace Main__i_Compile {

  public partial class __default {
    public static void IronfleetMain(Native____Io__s_Compile.NetClient netc, Dafny.ISequence<Dafny.ISequence<byte>> args)
    {
      bool _12_ok;
      BigInteger _13_host__state;
      bool _out6;
      BigInteger _out7;
      Host__i_Compile.__default.HostInitImpl(netc, args, out _out6, out _out7);
      _12_ok = _out6;
      _13_host__state = _out7;
      Native____Io__s_Compile._IEndPoint _14_id;
      _14_id = Native____Io__s_Compile.EndPoint.create((netc).MyPublicKey());
      while (_12_ok) {
        bool _out8;
        BigInteger _out9;
        Host__i_Compile.__default.HostNextImpl(_13_host__state, out _out8, out _out9);
        _12_ok = _out8;
        _13_host__state = _out9;
      }
    }
  }
} // end of namespace Main__i_Compile
namespace Math____mul__nonlinear__i_Compile {

} // end of namespace Math____mul__nonlinear__i_Compile
namespace Math____mul__auto__proofs__i_Compile {

} // end of namespace Math____mul__auto__proofs__i_Compile
namespace Math____mul__auto__i_Compile {

} // end of namespace Math____mul__auto__i_Compile
namespace Math____mul__i_Compile {

} // end of namespace Math____mul__i_Compile
namespace Math____power__i_Compile {

} // end of namespace Math____power__i_Compile
namespace _module {

} // end of namespace _module
