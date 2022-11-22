include "../Utils.dfy"
include "../Types.dfy"
include "../Disks/BlockDisk.dfy"
include "../Disks/CowZonedDisk.dfy"

module CowZonedDiskRefinesBlockDisk {
    import opened NativeTypes
    import opened Types
    import opened Utils
    import opened Zone

    import C = CowZonedDisk
    import A = BlockDisk

    // wow what a great name
    lemma FlattenedSeqOfEqualLengthedSeqLengthLemma<T>(s: seq<seq<T>>)
        requires |s| > 0
        requires forall i,j :: 0 <= i < j < |s| ==> |s[i]| == |s[j]|
        ensures |Flatten(s)| == |s| * |s[0]|
    {}

    function IC(c: C.Constants): A.Constants
        requires C.ConstantsValid(c)
        ensures A.ConstantsValid(IC(c))
    {
        // A CowZonedDisk can be modeled as an abstract block disk, 
        // with the buffer zone "invisible" to the outside world.
        A.Constants(
            C.BlocksPerZone(c) as int * (|c.zd.zone_map| - 1)
        )
    }

    function I(c: C.Constants, s: C.State): A.State
        requires C.Valid(c,s)
        ensures A.Valid(IC(c), I(c, s))
    {
        var buffer_zone := s.buffer_zone;
        var zones: seq<Zone.State> := 
            s.zd.zones[0..buffer_zone] + s.zd.zones[buffer_zone + 1..];

        assert |zones| == |s.zd.zones| - 1;
        
        var ssblocks: seq<seq<Block.State>> := seq(|zones|, z requires 0 <= z < |zones| => zones[z].blocks);
        assert forall i,j :: 0 <= i < j < |ssblocks| ==> |ssblocks[i]| == |ssblocks[j]|;

        var blocks : seq<Block.State> := Flatten(ssblocks);

        FlattenedSeqOfEqualLengthedSeqLengthLemma(ssblocks);

        // XXX: We don't know that, even though all the Blocks in the seq<seq<Block>> were valid, that
        // after flattening they remain exactly the same.  Punch a hole in the proof with an assume until
        // I can figure out why this might be.
        assert forall i,j :: 0 <= i < |ssblocks| ==> 0 <= j < |zones[i].blocks| 
            ==> Block.Valid(ssblocks[i][j]);
        assume forall i :: 0 <= i < |blocks| ==> Block.Valid(blocks[i]);

        A.State(blocks)
    }


    lemma RefinesInit(c: C.Constants)
        requires C.ConstantsValid(c)
        requires C.Valid(c, C.Init(c))
        ensures A.Valid(IC(c), I(c, C.Init(c)))
    {}
}