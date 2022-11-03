include "./BlockDisk.dfy"
include "../Types.dfy"

// A read-anywhere, append-only datatype.
module Zone {
    import opened NativeTypes
    import Block

    datatype State = State(
        write_ptr: uint64,
        blocks: seq<Block.State>
    )

    function method Init(blocks: uint64) : State
        requires 0 < blocks as int < UINT64_MAX
        ensures Valid(Init(blocks))
    {
        State(
            write_ptr := 0,
            blocks := seq(blocks, i => Block.Init()))
    }

    function Valid(s: State) : bool 
    {
        && 0 < |s.blocks|
        && 0 <= s.write_ptr as int <= |s.blocks|
        && forall i :: 0 <= i < s.write_ptr ==> Block.Valid(s.blocks[i])
    }

    function method Read(s: State, block_offset: uint64) : Block.State
        requires Valid(s)
        requires 0 <= block_offset < s.write_ptr
        ensures Valid(s)
    {
        s.blocks[block_offset]
    }

    predicate Write(s: State, s': State, b: Block.State)
        requires Valid(s)
        requires Valid(s')
        requires Block.Valid(b)
    {
        && !Full(s)
        && !Empty(s')
        && s.write_ptr == s'.write_ptr - 1
        && s.blocks[0..s.write_ptr] == s'.blocks[0..s.write_ptr]
        && s'.blocks[s.write_ptr] == b
    }

    predicate Reset(s: State)
        requires Valid(s)
    {
        s.write_ptr == 0
    }

    predicate Empty(s: State)
        requires Valid(s)
    {
        s.write_ptr == 0
    }

    predicate Full(s: State)
        requires Valid(s)
    {
        s.write_ptr as int == |s.blocks|
    }
}

module ZonedDisk /* refines Disk */ {
    import opened NativeTypes
    import opened Types
    import opened Zone

    datatype Constants = Constants(
        n_blocks: uint64,
        zone_map: seq<(uint64, uint64)> // [b, e)
    )

    datatype State = State(
        zones: seq<Zone.State>
    )

    function method Init(c: Constants) : State
        requires ConstantsValid(c)
    {
        State.State(
            seq(|c.zone_map|, i => Zone.Init(c.zone_map[i].1 - c.zone_map[i].0))
        )
    }

    predicate ConstantsValid(c: Constants)
    {
        zone_map_well_formed(c.n_blocks, c.zone_map)
    }

    predicate Valid(c: Constants, s: State) 
    {
        && ConstantsValid(c)
        && |s.zones| == |c.zone_map|
    }


    // Defining a function just to have something for Z3 to trigger on.
    predicate contiguous_interval(z: seq<(uint64, uint64)>, i: int)
        requires 0 < i < |z|
    {
        && z[i-1].1 == z[i].0
    }

    predicate zone_map_well_formed(n_blocks: uint64, zone_map: seq<(uint64, uint64)>)
    {
        n_blocks > 0
        && 0 < |zone_map| as int
        && zone_map[0].0 == 0
        && zone_map[|zone_map| - 1].1 == n_blocks
        && forall i :: 0 <= i < |zone_map| ==> 0 < zone_map[i].1 < zone_map[i].1
        && forall i :: 0 <= i < |zone_map| ==> 0 < (zone_map[i].1 - zone_map[i].0) < UINT64_MAX as uint64
        && forall i :: 0 <  i < |zone_map| ==> contiguous_interval(zone_map, i)
    }

    method resolve_lba(c: Constants, lba: uint64) returns (zone: int, offset: uint64) 
        requires 0 <= lba < c.n_blocks
        requires zone_map_well_formed(c.n_blocks, c.zone_map)

        ensures 0 <= zone < |c.zone_map|
        ensures 0 <= c.zone_map[zone].0 < c.n_blocks
        ensures c.zone_map[zone].0 <= lba < c.zone_map[zone].1;
        ensures offset == lba - c.zone_map[zone].0;
    {
        var i := 0;

        while i < |c.zone_map|
            invariant 0 <= i <= |c.zone_map| 
            invariant i > 0 ==> lba >= c.zone_map[i-1].1
            invariant i > 0 ==> contiguous_interval(c.zone_map, i)
        {
            if lba >= c.zone_map[i].0 && lba < c.zone_map[i].1 {
                zone := i;
                offset := lba - c.zone_map[i].0;
                return;
            }
            i := i + 1;
        }
    }

    datatype Step =
    | ReadBlock(block: uint32, contents: seq<uint8>)
    | WriteBlock(tid: uint32, contents: seq<uint8>)
}