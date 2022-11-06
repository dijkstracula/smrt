include "../Types.dfy"
include "../Disk.dfy"

module Block {
    import opened NativeTypes

    // XXX: Can I parameterise this "module parameter"?
    const block_sz := 1024;

    type State = seq<uint8>

    predicate Valid(s: State) {
        |s| == block_sz
    }

    function method Init() : State
        ensures Valid(Init())
    {
        seq(block_sz, i => 0)
    }
}

module BlockDisk refines Disk {
    import opened NativeTypes
    import opened Types
    import opened Block

    datatype Constants = Constants(
        n_blocks: uint32
    )
    datatype State = State(
        // XXX: should this be seq<option<Block>> ?
        blocks: seq<Block.State>
    )
    
    function method Init(c: Constants) : State 
    {
        State(seq(c.n_blocks, i => Block.Init()))
    }

    function method Read(c: Constants, s: State, block_id: int) : Block.State
        requires 0 <= block_id < |s.blocks|
    {
        s.blocks[block_id]
    }

    predicate Write(c: Constants, s: State, s': State, block_id: int, val: Block.State)
    {
        && Block.Valid(val)
        && 0 <= block_id < |s.blocks| == |s'.blocks|
        && s'.blocks == s.blocks[block_id := val]
    }

    // Invariant preservation


    predicate ConstantsValid(c: Constants) {
        && c.n_blocks > 0
    }

    predicate Valid(c: Constants, s: State) 
    {
        && ConstantsValid(c)
        && |s.blocks| == c.n_blocks as int
        && forall i :: 0 <= i < |s.blocks| ==> Block.Valid(s.blocks[i])
    }


    // Step relations

    datatype Step =
    | ReadBlock(lba: int, val: Block.State)
    | WriteBlock(lba: int, val: Block.State)

    predicate NextStep(c: Constants, s: State, s': State, step: Step)
    {
        Valid(c, s) 
        && match step {
            case ReadBlock(off, val) => 
                && 0 <= off < |s.blocks| as int
                && Read(c, s, off) == val
                && s == s'
            case WriteBlock(off, val) => 
                && 0 <= off < |s.blocks| as int
                && Write(c, s, s', off, val)
        }       
    }

    predicate Next(c: Constants, s: State, s': State)
    {
        exists step :: NextStep(c, s, s', step)
    }

    // Invariant nonsense
    
    lemma InitImpliesValid(c: Constants) 
    {}

    lemma NextPreservesValid(c: Constants, s: State, s': State)
        requires Valid(c, s)
        requires Next(c, s, s')
        ensures Valid(c, s')
    {
        var step :| NextStep(c, s, s', step);
        match step {
            case ReadBlock(off, val) => {}
            case WriteBlock(off, val) => {
                assert |s.blocks| == |s'.blocks|;
            }
        }
    }

    lemma ReadPreservesValid(c: Constants, s: State, s': State, lba: int, val: Block.State)
        requires Valid(c, s)
        requires 0 <= lba < c.n_blocks as int
        requires s == s'
        requires Read(c, s, lba) == val
        ensures Valid(c, s')
    {}
    
    lemma WritePreservesValid(c: Constants, s: State, s': State, lba: int, val: Block.State)
        requires Valid(c, s)
        requires Write(c, s, s', lba, val);
        ensures Valid(c, s')
    {}
}
