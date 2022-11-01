include "./BlockDisk.dfy"
include "../Types.dfy"

// A read-anywhere, append-only datatype.
module Zone {
    import opened NativeTypes
    import Block

    const block_sz := 1024;
    
    class State
    {
        var write_ptr: usize
        var blocks: seq<Block.State>

        function Valid() : bool 
            reads this
        {
            0 < |blocks| < USIZE_MAX
            && 0 <= write_ptr as int < |blocks|
        }

        constructor New(blocks: usize)
            // XXX: email Robin about why we have to bound USIZE_MAX given the argument to Init
            requires 0 < blocks as int < USIZE_MAX
            ensures Valid()
        {
            this.write_ptr := 0;
            this.blocks := seq(blocks, i => Block.Init());
        }

        function method Read(offset: usize) : Block.State
            reads this
            requires Valid()
            requires 0 <= offset < write_ptr
        {
            blocks[offset]
        }

        method Write(data: Block.State)
            modifies this
            requires Valid()
            requires |data| % block_sz == 0
            requires write_ptr as int < |blocks| - 1
            ensures Valid()
        {
            blocks := blocks[write_ptr := data];
            write_ptr := write_ptr + 1;
        }

        method Reset()
            modifies this
            requires Valid()
            ensures Valid()
        {
            write_ptr := 0;
        }
    }
}

module ZonedDisk /* refines TrackedDisk */ {
    import opened NativeTypes
    import opened Types
    import opened Zone

    datatype Constants = Constants(
        n_blocks: uint64,
        zone_map: seq<(uint64, uint64)> // [b, e)
    )

    // TODO: for crash consistency, we ought to distinguish between persistent state
    // and in-memory state (and show, presuamably, that at all steps the latter can be
    // reconstructed from the former?)
    datatype State = State(
        zones: seq<Zone.State>
    )

    predicate zone_map_well_formed(n_blocks: uint64, zone_map: seq<(uint64, uint64)>)
    {
        n_blocks > 0
        && 0 < |zone_map| as int
        && zone_map[0].0 == 0
        && zone_map[|zone_map| - 1].1 == n_blocks
        && forall i :: 0 <= i < |zone_map| ==> zone_map[i].0 < zone_map[i].1
        && forall i :: 0 <= i < |zone_map| - 1 ==> zone_map[i].1 == zone_map[i+1].0
        // TODO: email Robin about triggering with the following uncommented...
        //&& forall i :: 0 <= i < |zone_map| ==> forall j :: 0 <= j < i ==> zone_map[j].0 < zone_map[i].0
        //&& forall i :: 0 <= i < |zone_map| ==> forall j :: 0 <= j < i ==> zone_map[j].1 < zone_map[i].1
    }

    method resolve_lba(c: Constants, lba: uint64) returns (zone: int, offset: uint64) 
        requires 0 <= lba < c.n_blocks
        requires zone_map_well_formed(c.n_blocks, c.zone_map)

        ensures 0 <= zone < |c.zone_map|
        ensures 0 <= c.zone_map[zone].0 < c.n_blocks
        ensures 0 <= offset < c.zone_map[zone].1
        ensures c.zone_map[zone].0 <= lba;
        ensures offset == lba - c.zone_map[zone].0;
    {
        var i := 0;
        while i < |c.zone_map|
            invariant 0 <= i < |c.zone_map| 
            invariant i > 0 ==> lba >= c.zone_map[i-1].0
            invariant i > 0 ==> lba >= c.zone_map[i-1].1
        {
            if lba >= c.zone_map[i].0 && lba < c.zone_map[i].1 {
                zone := i;
                offset := lba - c.zone_map[i].0;
                return;
            }
            i := i + 1;
        }
    }

    predicate Valid(c: Constants, s: State) 
        requires zone_map_well_formed(c.n_blocks, c.zone_map)
        reads s.zones
    {
        |s.zones| == |c.zone_map|
    }

    datatype Step =
    | ReadBlock(block: uint32, contents: seq<uint8>)
    | WriteBlock(tid: uint32, contents: seq<uint8>)
}