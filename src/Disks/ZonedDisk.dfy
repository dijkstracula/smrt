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
        && 0 < |s.blocks| < UINT64_MAX
        && 0 <= s.write_ptr as int <= |s.blocks|
        && (forall i :: 0 <= i < |s.blocks| ==> Block.Valid(s.blocks[i]))
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
        ensures Valid(s)
    {
        && !Full(s)
        && !Empty(s')
        && s.write_ptr == s'.write_ptr - 1
        && s'.blocks == s.blocks[s.write_ptr := b]
    }

    function method Reset(s: State) : State
        requires Valid(s)
        ensures Valid(Reset(s))
        ensures Empty(Reset(s))
    {
        Init(|s.blocks| as uint64)
    }

    predicate Empty(s: State)
    {
        s.write_ptr == 0
    }

    predicate Full(s: State)
    {
        s.write_ptr as int == |s.blocks|
    }

    predicate Zeroed(s: State)
    {
        Full(s) && (forall i :: 0 <= i < |s.blocks| ==> 
            s.blocks[i] == seq(Block.block_sz, i => 0))
    }

    lemma WriteImpliesValid(s: State, s': State, b: Block.State)
        requires Valid(s)
        requires Block.Valid(b)
        requires Write(s, s', b)
        ensures Valid(s')
    {}

    lemma ResetImpliesValid(s: State)
        requires Valid(s)
        ensures Valid(Reset(s))
    {}

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
        && s'.zones == s.zones[zone_id := Zone.Reset(s.zones[zone_id])]
        /*
        && (forall z :: 0 <= z < |s.zones| 
            ==> z != zone_id as int 
            ==> s.zones[z] == s'.zones[z])
        && (s'.zones[zone_id] == Zone.Reset(s.zones[zone_id]))
        */
    }

    // Invariants

    predicate ConstantsValid(c: Constants)
    {
        && c.n_blocks > 0 
        && zone_map_well_formed(c.n_blocks, c.zone_map)
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
    }

    predicate zone_map_well_formed(n_blocks: uint64, zone_map: seq<(uint64, uint64)>)
    {
        && 0 < |zone_map| as int
        && zone_map[0].0 == 0
        && zone_map[|zone_map| - 1].1 == n_blocks
        && zone_map_ordered_total(zone_map)
    }

    predicate zone_map_ordered_total(zone_map: seq<(uint64, uint64)>)
    {
        && 0 < |zone_map| as int
        && (forall i :: 0 <  i < |zone_map| ==> contiguous_interval(zone_map, i))
        && (forall i :: 0 <= i < |zone_map| ==> zone_map[i].0 < zone_map[i].1)
        && (forall i :: 0 <= i < |zone_map| ==> (zone_map[i].1 - zone_map[i].0) as int < UINT64_MAX)

        // XXX: seems weird that these can't be figured out.
        && (forall i,j :: 0 <= i < j < |zone_map| ==> zone_map[i].0 < zone_map[j].0)
        && (forall i,j :: 0 <= i < j < |zone_map| ==> zone_map[i].0 < zone_map[j].1)
        && (forall i,j :: 0 <= i < j < |zone_map| ==> zone_map[i].1 < zone_map[j].1)
    }

    predicate lba_in_range(c: Constants, lba: uint64)
        requires ConstantsValid(c)
    {
        c.zone_map[0].0 <= lba < c.zone_map[|c.zone_map| - 1].1
    }

    predicate resolve_lba(c: Constants, lba: uint64, zone: int)
        requires zone_map_well_formed(c.n_blocks, c.zone_map)
    {
        && lba_in_range(c, lba)
        && 0 <= zone < |c.zone_map|
        && c.zone_map[zone].0 <= lba < c.zone_map[zone].1
    }

    function resolve_zone_offset(c: Constants, lba: uint64): uint64
        requires ConstantsValid(c)
        requires lba_in_range(c, lba)
        ensures exists z :: 
            && resolve_lba(c, lba, z) 
            // XXX: newtype constraints are a PITA
            && c.zone_map[z].0 as int + resolve_zone_offset(c, lba) as int == lba as int
    {
        resolve_lba_functional(c, lba);
        var lzone: int :| resolve_lba(c, lba, lzone);
        lba - c.zone_map[lzone].0
    }

    lemma resolve_lba_functional(c: Constants, lba: uint64)
        requires zone_map_well_formed(c.n_blocks, c.zone_map)
        requires lba_in_range(c, lba)
        ensures exists z :: 0 <= z < |c.zone_map| && resolve_lba(c, lba, z)
    {
        var i := 0;

        while i < |c.zone_map|
            invariant 0 <= i <= |c.zone_map| 
            invariant i > 0 ==> lba >= c.zone_map[i-1].1
            invariant i > 0 ==> contiguous_interval(c.zone_map, i)
        {
            if c.zone_map[i].0 <= lba < c.zone_map[i].1 {
                var zone := i;
                var offset := lba - c.zone_map[i].0;
                assert resolve_lba(c, lba, zone);
                return;
            }
            i := i + 1;
        }

        assert false; /* This must be unreachable! */
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

    lemma ResetPreservesValid(c: Constants, s: State, s': State)
        requires Valid(c,s)
        ensures forall s', i: uint64 :: 
            0 <= i as int < |c.zone_map| 
            ==> Reset(c, s, s', i) 
            ==> Valid(c, s')
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