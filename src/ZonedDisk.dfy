include "Types.dfy"

module ZonedDisk /* refines TrackedDisk */ {
    import opened NativeTypes
    import opened Types

    datatype Constants = Constants(
        drive_sz: uint64,
        zone_map: seq<(uint64, uint64)> // [b, e)
    )

    predicate zone_map_well_formed(drive_sz: uint64, zone_map: seq<(uint64, uint64)>)
    {
        drive_sz > 0
        && 0 < |zone_map| < drive_sz as int
        && zone_map[0].0 == 0
        && zone_map[|zone_map| - 1].1 == drive_sz
        && forall i :: 0 <= i < |zone_map| ==> zone_map[i].0 < zone_map[i].1
        && forall i :: 0 <= i < |zone_map| - 1 ==> zone_map[i].1 == zone_map[i+1].0
        // TODO: email Robin about triggering with the following uncommented...
        //&& forall i :: 0 <= i < |zone_map| ==> forall j :: 0 <= j < i ==> zone_map[j].0 < zone_map[i].0
        //&& forall i :: 0 <= i < |zone_map| ==> forall j :: 0 <= j < i ==> zone_map[j].1 < zone_map[i].1
    }

    method resolve_lba(c: Constants, lba: uint64) returns (zone: int, offset: uint64) 
        requires 0 <= lba < c.drive_sz
        requires zone_map_well_formed(c.drive_sz, c.zone_map)

        ensures 0 <= zone < |c.zone_map|
        ensures 0 <= c.zone_map[zone].0 < c.drive_sz
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

    datatype State = State(validTracks: set<uint32>)
    datatype Step =
    | ReadBlock(block: uint32, contents: seq<uint8>)
    | WriteBlock(tid: uint32, contents: seq<uint8>)
}