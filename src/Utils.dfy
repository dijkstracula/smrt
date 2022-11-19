include "Types.dfy"

module Utils {
    import opened NativeTypes

    // what's polymorphism, precious?

    function method MinUInt64(a: uint64, b: uint64): uint64
        ensures MaxUInt64(a, b) == a || MaxUInt64(a, b) == b
    {
        if a < b then a else b
    }

    function method MaxUInt64(a: uint64, b: uint64): uint64
        ensures MaxUInt64(a, b) == a || MaxUInt64(a, b) == b
    {
        if a > b then a else b
    }

    // what's monads, precious?
    // also what's a standard library, precious? >:(

    function method Flatten<A>(ss: seq<seq<A>>) : seq<A>
    {
        if |ss| == 0 then [] else
        ss[0] + Flatten(ss[1..])
    }

    function method Map<T,U>(f: (T ~> U), s: seq<T>) : seq<U>
        reads f.reads
        requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
        ensures |s| == |Map(f, s)|
    {
        if |s| == 0 then [] else
        [f(s[0])] + Map(f, s[1..])
    }

    function method Filter<T>(f: (T ~> bool), s: seq<T>) : seq<T>
        reads f.reads
        requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
        ensures |Filter(f, s)| <= |s|
    {
        if |s| == 0 then [] else
        (if f(s[0]) then [s[0]] else []) + Filter(f, s[1..])
    }
}