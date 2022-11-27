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

    // Needed for CowZonedDiskRefinesBlockDisk::I
    lemma FlattenedContentsUnchanged<T>(ss: seq<seq<T>>, s: seq<T>)
        requires Flatten(ss) == s
        ensures forall i, j :: 
            0 <= i < |ss| ==> 0 <= j < |ss[i]| ==>
                exists k :: 0 <= k < |s| && s[k] == ss[i][j]
    {
        if |ss| == 0 {}
        else {
            var hd: seq<T> := ss[0];
            var hdlen := |ss[0]|;
            var tl: seq<seq<T>> := ss[1..];

            assert forall i :: 0 <= i < hdlen ==> hd[i] in s;
            FlattenedContentsUnchanged(tl, s[hdlen..]);
        }
    }


    /*
    lemma FlattenedContentsUnchanged<T>(ss: seq<seq<T>>, s: seq<T>)
        requires Flatten(ss) == s
        ensures (set x | x in Flatten(ss)) == (set i, j | 0 <= i < |ss| && 0 <= j < |ss[i]| :: ss[i][j])
    {

    }
    */

    function method Map<T,U>(f: (T ~> U), s: seq<T>) : seq<U>
        reads f.reads
        requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
        ensures |s| == |Map(f, s)|
    {
        if |s| == 0 then [] else
        [f(s[0])] + Map(f, s[1..])
    }

    function method FlatMapSeq<T, U>(f: T ~> seq<U>, s: seq<T>) : seq<U>
        reads f.reads
        requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    {
        Flatten(Map(f, s))
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