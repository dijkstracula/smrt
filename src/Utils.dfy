include "Types.dfy"

module Utils {
    import opened NativeTypes

    // what's polymorphism, precious?

    function method MinUInt64(a: uint64, b: uint64): uint64
    {
        if a < b then a else b
    }

    function method MaxUInt64(a: uint64, b: uint64): uint64
    {
        if a > b then a else b
    }

    // what's monads, precious?

    function method Flatten<A>(ss: seq<seq<A>>) : seq<A>
    {
        if |ss| == 0 then [] else
        ss[0] + Flatten(ss[1..])
    }
}