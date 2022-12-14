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
        n_blocks: int
    )
    datatype State = State(
        // XXX: should this be seq<option<Block>> ?
        blocks: seq<Block.State>
    )
    
    function method Init(c: Constants) : State 
    {
        State(seq(c.n_blocks, i => Block.Init()))
    }

    function method Read(c: Constants, s: State, lba: uint64) : Block.State
        requires 0 <= lba as int < |s.blocks| {
        s.blocks[lba]
    }

    predicate Write(c: Constants, s: State, s': State, lba: uint64, val: Block.State) {
        && Block.Valid(val)                   // A block is well-formed...
        && 0 <= lba as int < |s.blocks|       // ...and the lba is within range...
        && s'.blocks == s.blocks[lba := val]  // ...and the before and after states only
                                              // differ in the block that was mutated.
    }

    // Invariant preservation


    predicate ConstantsValid(c: Constants) {
        && c.n_blocks > 0
    }

    predicate Valid(c: Constants, s: State) 
    {
        && ConstantsValid(c)
        && |s.blocks| == c.n_blocks as int
        && (forall i :: 0 <= i < |s.blocks| ==> Block.Valid(s.blocks[i]))
    }


    // Step relations

    datatype Step =
    | ReadBlock(lba: uint64, val: Block.State)  // `val` is the block at block address `lba`
    | WriteBlock(lba: uint64, val: Block.State) // `val` is updated to be the block at `lba`

    predicate NextStep(c: Constants, s: State, s': State, step: Step)
    {
        Valid(c, s) 
        && match step {
            case ReadBlock(off, val) => 
                && 0 <= off as int < |s.blocks| as int
                && Read(c, s, off) == val
                && s == s'
            case WriteBlock(off, val) => 
                && 0 <= off as int < |s.blocks| as int
                && Write(c, s, s', off, val)
        }       
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
        requires 0 <= lba as int < c.n_blocks as int
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
