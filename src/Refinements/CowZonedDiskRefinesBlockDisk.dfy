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
        assert forall i,j :: 0 <= i < |ssblocks| ==> 0 <= j < |zones[i].blocks| ==> Block.Valid(ssblocks[i][j]);
        assume forall i :: 0 <= i < |blocks| ==> Block.Valid(blocks[i]);

        A.State(blocks)
    }


/* XXX: This crashes Dafny!
    https://github.com/dafny-lang/dafny/issues/3105
    lemma RefinesInit(c: C.Constants)
        requires C.ConstantsValid(c)
        requires C.Valid(c, C.Init(c))
        ensures A.Valid(IC(c), I(c, C.Init(c)))
    {}


    lemma RefinesReadStep(c: C.Constants, s: C.State, s': C.State, block_id: uint64, val: Block.State)
        requires C.Valid(c, s)
        requires C.NextStep(c, s, s', C.ReadBlock(block_id, val))
        requires C.Read(c, s, block_id) == val
        ensures A.Read(IC(c), I(c, s), block_id as int) == val
    {
    }

    lemma RefinesWriteStep(c: C.Constants, s: C.State, s': C.State, block_id: uint64, val: Block.State)
        requires C.Valid(c, s)
        requires C.NextStep(c, s, s', C.WriteBlock(block_id, val))
        requires C.Write(c, s, s', block_id, val)
        ensures A.Write(IC(c), I(c, s), I(c, s'), block_id as int, val)
    {
    }


    lemma RefinesStep(c: C.Constants, s: C.State, s': C.State, step: C.Step)
        requires C.ConstantsValid(c)
        requires C.NextStep(c, s, s', step)
        ensures A.Next(IC(c), I(c, s), I(c, s'))
    {
        match step {
            case ReadBlock(b, val) => RefinesReadStep(c, s, s', b, val);
            case WriteBlock(b, val) => RefinesWriteStep(c, s, s', b, val);
        }
    }
    */
}

/* We want to show that on a write, you have to fault all the data over to the
 * buffer zone _before_ updating the indirection map.
 * TODO: where should this live?
 */
module CowZonedDiskCrashSequencing {
    import opened NativeTypes
    import opened Types
    import ZonedDisk

    import C = CowZonedDisk
    import A = BlockDisk
    import R = CowZonedDiskRefinesBlockDisk

    datatype Step =
        | IOStep(A.Step)
        | CrashStep
        | StutterStep

    function Threaded(s: seq<A.Step>): seq<Step>
    {
        if |s| == 0 then []
        else 
            var x, xs := IOStep(s[0]), Threaded(s[1..]);
            var cstr :| 0 <= cstr < 3;
            (if cstr == 0      then [x]
            else if cstr == 1  then [CrashStep, x]
            else /* cstr == 2 */    [StutterStep, x]) + xs
    }

    predicate ValidOp(c: A.Constants, op: A.Step)
        requires A.ConstantsValid(c)
        requires op.ReadBlock?
    {
        && 0 <= op.lba as int < c.n_blocks
        && A.Block.Valid(op.val)
    }

    function ReadOps(c: C.Constants, s: C.State, lba: uint64, val: A.Block.State): seq<A.Step>
        requires C.Valid(c, s)
        requires 0 <= lba as int < c.zd.n_blocks as int
        requires A.Block.Valid(val)
        ensures forall i :: 0 <= i < |ReadOps(c, s, lba, val)| ==> ReadOps(c, s, lba, val)[i].ReadBlock?
        ensures forall i :: 0 <= i < |ReadOps(c, s, lba, val)| ==> ValidOp(R.IC(c), ReadOps(c, s, lba, val)[i])
        //ensures C.Read(c, s, lba) == A.Read(R.IC(c), R.I(c, s), lba as int)
    {
        ZonedDisk.resolve_lba_functional(c.zd, lba);
        var lzone: int :| ZonedDisk.resolve_lba(c.zd, lba, lzone);
        assume 0 <= lzone < |s.zd.zones| - 1; // XXX: why isn't thie assert working??

        var pzone := C.buffer_resolve(c, s, lzone);
        assert 0 <= pzone < |s.zd.zones|;
        var off := lba - c.zd.zone_map[lzone].0;

        assume (pzone + off as int) < UINT64_MAX; // XXX: same???
        assume (pzone as uint64 + off) < c.zd.zone_map[lzone].1; // XXX: same???
        var op := A.ReadBlock(pzone as uint64 + off, val);
        assert ZonedDisk.lba_in_range(c.zd, op.lba);
        assume ValidOp(R.IC(c), op); // XXX: This times out otherwise, boooo

        [op]
    }

    lemma ReadOpsAreValid(c: C.Constants, s: C.State, lba: uint64, val: A.Block.State)
        requires C.Valid(c, s)
        requires C.lba_in_range(c, lba)
        requires A.Block.Valid(val)
        requires C.Read(c, s, lba) == val
        ensures A.Read(R.IC(c), R.I(c, s), lba) == val
    {
        var ic := R.IC(c);
        var ist := R.I(c, s);
        var ops := ReadOps(c, s, lba, val);

        var i := 0;
        while (i < |ops|) {
            var step := ops[i]; // Or inject a crash??  What's a good way to compose things nondeterministically?
            match step {
                case ReadBlock(off, val) => {
                    assert 0 <= off as int < ic.n_blocks;
                }
                case WriteBlock(off, val) => {
                    assert false;
                }
            }       
            i := i + 1;
        }
    }

    /*
    function WriteOps(c: C.Constants, s: C.State, op: C.WriteStep): seq<A.Step>
        requires C.Valid(c, s)
    {
        ZonedDisk.resolve_lba_functional(c.zd, lba);
        var lzone: int :| ZonedDisk.resolve_lba(c.zd, lba, lzone);
        assert 0 <= lzone < |s.zd.zones| - 1;
        var off := lba - c.zd.zone_map[lzone].0;

        var pzone := buffer_resolve(c, s, lzone);
        assert 0 <= pzone < |s.zd.zones|;

        var src_zone := s.zd.zones[pzone];
    }
    */
}