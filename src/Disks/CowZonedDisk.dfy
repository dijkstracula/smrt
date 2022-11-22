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
 *
 * "I send a the COW Zones into space!! I don't pay a the taxes!! Ohhhhhh!!!"
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
        && |c.zd.zone_map| >= 2
        && (forall i,j :: 0 <= i < j < |c.zd.zone_map| ==> 
            c.zd.zone_map[i].1 - c.zd.zone_map[i].0 ==
            c.zd.zone_map[j].1 - c.zd.zone_map[j].0)
    }

    predicate Valid(c: Constants, s: State)
    {
        && ConstantsValid(c)
        && AllZonesAreEquallySized(c)
        && ZonedDisk.Valid(c.zd, s.zd)
        && (0 <= s.buffer_zone as int < |s.zd.zones|)
        && buffer_map_well_formed(c, s)

        // The buffer zone is "zeroed out"
        && Zone.Empty(s.zd.zones[s.buffer_zone])
    }

    function BlocksPerZone(c: Constants): uint64
        requires ConstantsValid(c)
        // XXX: This postcondition is already part of ConstantsValid; I don't
        // know why I have to state it here for CowZonedRefinement to pass??
        ensures AllZonesAreEquallySized(c)
    {
        c.zd.zone_map[0].1 - c.zd.zone_map[0].0
    }

    predicate AllZonesAreEquallySized(c: Constants)
        requires ConstantsValid(c)
    {
        forall i,j :: 0 <= i < j < |c.zd.zone_map| ==>
            (c.zd.zone_map[i].1 - c.zd.zone_map[i].0) ==
            (c.zd.zone_map[j].1 - c.zd.zone_map[j].0)
    }


    predicate lba_in_range(c: Constants, lba: uint64)
        requires ConstantsValid(c)
    {
        // Similar to ZonedDisk.lba_in_range, but because we lose the
        // final zone for the buffer zone, no lbas can reside in that one.
        && ZonedDisk.lba_in_range(c.zd, lba)
        && lba < c.zd.zone_map[|c.zd.zone_map| - 1].0
    }

    predicate buffer_map_well_formed(c: Constants, s: State)
    {
        var bmap := s.buffer_map;

        // Any logical zone needs to be a valid index into the buffer zone.
        && (|bmap| == |c.zd.zone_map| - 1)

        // Every logical -> physical zone mapping must be well-defined.
        && (forall i :: 0 <= i < |bmap| ==> 0 <= bmap[i] < |c.zd.zone_map|)

        // The buffer map needs hold all but one physical zone - the one that's
        // missing is the buffer zone.
        //&& (forall i,j :: 0 <= i < j < |bmap| ==> 
         //   bmap[i] == bmap[j] ==> bmap[i] == s.buffer_zone)

        // The buffer zone needs to be empty, and not present in the buffer map.
        && (0 <= s.buffer_zone < |s.zd.zones|)
        && Zone.Empty(s.zd.zones[s.buffer_zone])
    }

    // Resolves a logical zone into a physical one.
    function buffer_resolve(c: Constants, s: State, lzone: int): int
        requires Valid(c, s)
        requires 0 <= lzone                       < |s.buffer_map|
        ensures  0 <= buffer_resolve(c, s, lzone) < |s.zd.zones|
    {
        s.buffer_map[lzone]
    }

    function Read(c: Constants, s: State, lba: uint64) : Block.State
        requires Valid(c, s)
        requires lba_in_range(c, lba)
        ensures Block.Valid(Read(c, s, lba))
    {
        ZonedDisk.resolve_lba_functional(c.zd, lba);
        var lzone: int :| ZonedDisk.resolve_lba(c.zd, lba, lzone);
        var pzone := buffer_resolve(c, s, lzone);

        var off := lba - c.zd.zone_map[lzone].0;

        s.zd.zones[pzone].blocks[off]
    }

    // XXX: This will do a full zone copy.  Where should the fact that this involves
    // multiple atomic operaitons live?  That could be at the refinement layer, but
    // maybe it needs to be here?
    predicate Write(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires Block.Valid(val)
        requires lba_in_range(c, lba)
    {
        ZonedDisk.resolve_lba_functional(c.zd, lba);
        var lzone: int :| ZonedDisk.resolve_lba(c.zd, lba, lzone);
        assert 0 <= lzone < |s.zd.zones| - 1;
        var off := lba - c.zd.zone_map[lzone].0;

        var pzone := buffer_resolve(c, s, lzone);
        assert 0 <= pzone < |s.zd.zones|;

        var src_zone := s.zd.zones[pzone];
        var dst_zone := Zone.State(
            /* XXX: why does this break when we don't increment
             * the write_ptr?? */
            MaxUInt64(src_zone.write_ptr, off) /*+ 1*/,
            src_zone.blocks[ off := val ]
        );

        var reset_zone := Zone.Reset(s.zd.zones[pzone]);
        Zone.ResetImpliesValid(reset_zone);

        // XXX: Right now we have a hole in the logic: we need to be able to
        // say that there's no chance that the buffer zone is also where 
        // assert pzone != s.buffer_zone;

        // All future resolutions to the logical zone we destructively
        // updated need to go to the zone we just copied everything over
        // into (i.e. the old buffer zone)
        && s'.buffer_zone == pzone
        && s'.buffer_map == s.buffer_map
        [
            lzone := s.buffer_zone
        ]

        // ...we haven't modified the disk, except for two zones:
        && s'.zd.zones == s.zd.zones
        [
            // Our former buffer zone now contains the zone with the destructive update
            s.buffer_zone := dst_zone
        ]
        [
            // The old zone location is now the new buffer zone
            s'.buffer_zone := reset_zone
        ]
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
                && lba_in_range(c, off)
                && Block.Valid(val)
                && s == s'
                && Read(c, s, off) == val
            case WriteBlock(off, val) => 
                && lba_in_range(c, off)
                && Block.Valid(val)
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
        ensures Valid(c, s')
    {
        var step :| NextStep(c, s, s', step);
        match step {
            case ReadBlock(off, val) => ReadPreservesValid(c, s, s', off, val);
            case WriteBlock(off, val) => WritePreservesValid(c, s, s', off, val);
        }
    }

    lemma ReadPreservesValid(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires lba_in_range(c, lba)
        requires s == s'
        requires Read(c, s, lba) == val
        ensures Valid(c, s')
    {}

    lemma WritePreservesValid(c: Constants, s: State, s': State, lba: uint64, val: Block.State)
        requires Valid(c, s)
        requires lba_in_range(c, lba)
        requires Block.Valid(val)
        requires Write(c, s, s', lba, val);
        ensures Valid(c, s')
    {
    }

}