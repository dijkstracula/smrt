/* A terrible but "straightforward" block-addressible translation layer: All
 * zones are of a fixed size, and (n-1) zones are available for user use, with
 * one reserved as a buffer.  A random access write to a particular zone
 * necessitates a full copy of that zone to the buffer zone, applying the
 * destructive update in place.
 *
 * When the final block is written to the disk, a zone map is updated in order
 * to make the copy "durable".
 *
 * Yeah, this sucks!  Nobody should build a drive this way, but the intention
 * here is to get a trivial remapping system working and show refinement, before
 * we show something more interesting.
 */

include "ZonedDisk.dfy"

include "../Disk.dfy"
include "../Types.dfy"
include "../Utils.dfy"


module CowZonedDisk refines Disk {
    import opened NativeTypes
    import opened Types
    import opened Utils

    import Block
    import Zone
    import ZonedDisk

    datatype Constants = Constants(
        zd: ZonedDisk.Constants
    )

    datatype State = State(
        /* The underlying zoned disk */
        zd: ZonedDisk.State,

        /* Which buffer will we fault the next write's zone over into? */
        buffer_zone: int,

        /* Logical zone -> physical zone remapping (to account for the
         * buffer zone, which will float around as writes happen) */
        buffer_map: seq<int>
    )

    function method Init(c: Constants) : State
    {
        State(
            ZonedDisk.Init(c.zd),

            /* Begin with the identity mapping for the first (n-1) zones,
             * leaving the final zone for our initial buffer.  */
            |c.zd.zone_map| as int - 1,
            seq(|c.zd.zone_map| - 1, i => i)
        )
    }

    predicate ConstantsValid(c: Constants)
    {
        && ZonedDisk.ConstantsValid(c.zd)
        && (forall i,j :: 0 <= i < j < |c.zd.zone_map| ==> 
            c.zd.zone_map[i].1 - c.zd.zone_map[i].0 ==
            c.zd.zone_map[j].1 - c.zd.zone_map[j].0)
    }

    predicate Valid(c: Constants, s: State)
    {
        && ConstantsValid(c)
        && ZonedDisk.Valid(c.zd, s.zd)
        && (0 <= s.buffer_zone as int < |s.zd.zones|)
        && buffer_map_well_formed(c, s)
    }

    predicate buffer_map_well_formed(c: Constants, s: State)
    {
        var map_max := |c.zd.zone_map| - 1;
        var bmap := s.buffer_map;

        // the buffer map needs to be a permutation of [0..|c.zd.zone_map|)
        // with exactly one element missing, namely buffer_zone.
        && (|s.buffer_map| == |c.zd.zone_map| - 1)
        && (forall i :: 0 <= i       < |bmap| ==> 0 <= bmap[i] <= map_max)
        && (forall i,j :: 0 <= i < j < |bmap| ==> bmap[i] != bmap[j])
        && (forall i :: 0 <= i       < |bmap| ==> bmap[i] != s.buffer_zone)

        // The buffer zone needs to be in range, and it has to be empty.
        && (0 <= s.buffer_zone < |s.zd.zones|)
        && Zone.Empty(s.zd.zones[s.buffer_zone])
    }

    function Read(c: Constants, s: State, lba: uint64) : Block.State
        requires Valid(c, s)
        requires 0 <= lba < c.zd.n_blocks
        //ensures Block.Valid(Read(c, s, lba))
    {
        var p :| ZonedDisk.resolve_lba(c.zd, lba, p);
        var (lzone, off) := p;
        var pzone := s.buffer_map[lzone];

        s.zd.zones[pzone].blocks[off]
    }

    // XXX: This will do a full zone copy.  Where should the fact that this involves
    // multiple atomic operaitons live?  That could be at the refinement layer, but
    // maybe it needs to be here?
    predicate Write(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires 0 <= lba < c.zd.n_blocks
    {
        true
        /*
        var p :| ZonedDisk.resolve_lba(c.zd, lba, p);
        var (lzone, off) := p;
        var pzone := s.buffer_map[lzone];

        var src_zone := s.zd.zones[pzone];
        var dst_zone := Zone.State(
            MaxUInt64(src_zone.write_ptr + 1, off) as uint64,
            src_zone.blocks[ off := val ]
        );

        assert Zone.Valid(dst_zone);

        && |s.zd.zones| == |s'.zd.zones|

        // The zone containing the block we want to destructively write
        // is now the new buffer zone
        && Zone.Empty(s'.zd.zones[pzone])

        // Our former buffer zone now contains the zone with the
        // destructive update
        && Zone.Empty(s.zd.zones[s.buffer_zone])
        && s'.zd.zones[s.buffer_zone] == dst_zone

        // No other zones are touched
        && (forall i :: 0 <= i < |s'.zd.zones| ==>
            (i != pzone && i != s.buffer_zone ==> s.zd.zones[i] == s'.zd.zones[i]))
            */
    }


    // Steps and step relations

    datatype Step =
    | ReadBlock(lba: uint64, val: Block.State)
    | WriteBlock(lba: uint64, val: Block.State)

    predicate NextStep(c: Constants, s: State, s': State, step: Step)
    {
        Valid(c, s) 
        && (match step {
            case ReadBlock(off, val) => 
                && ZonedDisk.lba_in_range(c.zd, off) ==>
                && Read(c, s, off) == val
            case WriteBlock(off, val) => 
                && ZonedDisk.lba_in_range(c.zd, off) ==>
                && Write(c, s, s', off, val)
        })    
    }

    predicate Next(c: Constants, s: State, s': State)
    {
        exists step :: NextStep(c, s, s', step)
    }

    // Invariant preservation
    
    lemma InitImpliesValid(c: Constants) 
    {}

    lemma NextPreservesValid(c: Constants, s: State, s': State)
        requires Valid(c, s)
        requires Next(c, s, s')
     //   ensures Valid(c, s')
    {
        /*
        var step :| NextStep(c, s, s', step);
        match step {
            case ReadBlock(off, val) => ReadPreservesValid(c, s, s', off, val);
            case WriteBlock(off, val) => WritePreservesValid(c, s, s', off, val);
        }
        */
    }

    lemma ReadPreservesValid(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires ZonedDisk.lba_in_range(c.zd, lba)
        requires s == s'
        requires Read(c, s, lba) == val
        ensures Valid(c, s')
    {}
    
    lemma WritePreservesValid(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires Write(c, s, s', lba, val);
        ensures Valid(c, s')
    {}

}