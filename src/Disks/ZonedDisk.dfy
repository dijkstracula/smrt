include "./BlockDisk.dfy"
include "../Types.dfy"

// A read-anywhere, append-only datatype.
module Zone {
    import opened NativeTypes
    import Block

    // XXX: should Constants be the zone size, and
    // then the ZonedDisk zonemap be a seq of Zone.Constants?

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
        && (forall i :: 0 <= i < s.write_ptr ==> Block.Valid(s.blocks[i]))
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
        requires Block.Valid(b)
    {
        && !Full(s)
        && !Empty(s')
        && s.write_ptr == s'.write_ptr - 1
        && |s.blocks| == |s'.blocks|
        && s.blocks[0..s.write_ptr] == s'.blocks[0..s.write_ptr]
        && s'.blocks[s.write_ptr] == b
    }

    function method Reset(s: State) : State
        requires Valid(s)
        ensures Valid(Reset(s))
    {
        var blocks := |s.blocks|;

        State(
            write_ptr := 0,
            blocks := seq(blocks, i => Block.Init()))
    }

    predicate Empty(s: State)
    {
        s.write_ptr == 0
    }

    predicate Full(s: State)
    {
        s.write_ptr as int == |s.blocks|
    }
}

module ZonedDisk refines Disk {
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
    {
        State.State(
            seq(|c.zone_map|, i requires 0 <= i < |c.zone_map| => Zone.Init(c.zone_map[i].1 - c.zone_map[i].0))
        )
    }

    function method Read(c: Constants, s: State, zone: uint64, block: uint64) : Block.State
        requires Valid(c, s)
        requires 0 <= zone as int < |c.zone_map|
        requires 0 <= block < s.zones[zone].write_ptr
        ensures Block.Valid(Read(c, s, zone, block))
    {
        s.zones[zone].blocks[block]
    }

    predicate Append(c: Constants, s: State, s': State, zone_id: uint64, block: Block.State)
        requires Valid(c, s)
        requires 0 <= zone_id as int < |c.zone_map|
        requires !Full(s.zones[zone_id])
        requires Block.Valid(block)
    {
        var write_ptr := s.zones[zone_id].write_ptr;

        // Only zone_id is touched in an append operation; the rest stay the same...
        && |s.zones| == |s'.zones|
        && (forall z :: 0 <= z < |s.zones| 
            ==> z != zone_id as int 
            ==> s.zones[z] == s'.zones[z])

        // ...and the new and old zones are identical except for...
        && |s.zones[zone_id].blocks| == |s'.zones[zone_id].blocks|
        && (forall b :: 0 <= b < write_ptr ==> s.zones[zone_id].blocks[b] == s'.zones[zone_id].blocks[b])

        // ...the single additional element.
        && Zone.Write(s.zones[zone_id], s'.zones[zone_id], block)
        && s'.zones[zone_id].write_ptr == write_ptr + 1
        && s'.zones[zone_id].blocks[write_ptr] == block
    }

    predicate Reset(c: Constants, s: State, s': State, zone_id: uint64)
        requires Valid(c, s)
        requires 0 <= zone_id as int < |c.zone_map|
    {
        && |s.zones| == |s'.zones|
        && (forall z :: 0 <= z < |c.zone_map| 
            ==> z != zone_id as int 
            ==> s.zones[z] == s'.zones[z])
        && (s'.zones[zone_id] == Zone.Reset(s.zones[zone_id]))
    }

    // Invariants

    predicate ConstantsValid(c: Constants)
    {
        zone_map_well_formed(c.n_blocks, c.zone_map)
    }

    predicate Valid(c: Constants, s: State) 
    {
        && ConstantsValid(c)
        && |s.zones| == |c.zone_map|
        && (forall i :: 0 <= i < |c.zone_map| ==> Zone.Valid(s.zones[i]))
        && (forall i :: 0 <= i < |c.zone_map|
            ==> |s.zones[i].blocks| == (c.zone_map[i].1 - c.zone_map[i].0) as int)
    }


    // Defining a function just to have something for Z3 to trigger on.
    predicate contiguous_interval(z: seq<(uint64, uint64)>, j: int)
        requires 0 < j < |z|
    {
        && z[j-1].1 == z[j].0
        && (forall i :: 0 <= i < j < |z| ==> z[i].1 < z[j].0)
    }

    predicate zone_map_well_formed(n_blocks: uint64, zone_map: seq<(uint64, uint64)>)
    {
        && 0 < |zone_map| as int
        && zone_map[0].0 == 0
        && zone_map[|zone_map| - 1].1 == n_blocks
        && (forall i :: 0 <= i < |zone_map| ==> zone_map[i].0 < zone_map[i].1)
        && (forall i :: 0 <= i < |zone_map| ==> (zone_map[i].1 as int - zone_map[i].0 as int) < UINT64_MAX)
        && (forall i :: 0 <  i < |zone_map| ==> contiguous_interval(zone_map, i))
    }

    predicate lba_in_range(c: Constants, lba: uint64)
        requires ConstantsValid(c)
    {
        c.zone_map[0].0 <= lba < c.zone_map[|c.zone_map| - 1].1
    }

    predicate resolve_lba(c: Constants, lba: uint64, zone_off: (int, uint64))
        requires zone_map_well_formed(c.n_blocks, c.zone_map)
    {
        var zone := zone_off.0;
        var off := zone_off.1;

        && lba_in_range(c, lba)
        && 0 <= zone < |c.zone_map|
        && c.zone_map[zone].0 <= lba < c.zone_map[zone].1
        && off == lba - c.zone_map[zone].0
    }

    // XXX: I don't think I'll ever be in a position to call a method; oops..???
    method ResolveLBA(c: Constants, lba: uint64) returns (zone: int, offset: uint64) 
        requires 0 <= lba < c.n_blocks
        requires zone_map_well_formed(c.n_blocks, c.zone_map)
        ensures resolve_lba(c, lba, (zone, offset))
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

    // Steps and step relations

    datatype Step =
    | ReadFromZone(zone: uint64, block: uint64, val: Block.State)
    | AppendToZone(zone_idx: uint64, val: Block.State)
    | ResetZone(zone_idx: uint64)

    predicate NextStep(c: Constants, s: State, s': State, step: Step)
    {
        Valid(c, s) && match step
        {
            case ReadFromZone(zone, block, val) =>
                && 0 <= zone as int < |s.zones|
                && 0 <= block < s.zones[zone].write_ptr
                && Read(c, s, zone, block) == val
                && s == s'

            case AppendToZone(zone, val) => 
                && 0 <= zone as int < |s.zones| == |s'.zones|
                && !Full(s.zones[zone])
                && Block.Valid(val)
                && Append(c, s, s', zone, val)

            case ResetZone(zone) => 
                && 0 <= zone as int < |s.zones|
                && Reset(c, s, s', zone)
        }
    }

    predicate Next(c: Constants, s: State, s': State)
    {
        exists step :: NextStep(c, s, s', step)
    }

    // Invariant preservation

    lemma InitImpliesValid(c: Constants)
        {}

/*
    lemma NextPreservesValid(c: Constants, s: State, s': State)
        requires Valid(c, s)
        requires Next(c, s, s')
        ensures Valid(c, s')
    {
        var step :| NextStep(c, s, s', step);
        match step {
            case ReadFromZone(z, b, val) => {
            }
            case AppendToZone(z, b) => {

            }
            case ResetZone(z) => {}
        }
    } */
}