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

    predicate ConstantsValid(c: Constants) {
        && c.n_blocks > 0
    }

    predicate Valid(c: Constants, s: State) 
    {
        && ConstantsValid(c)
        && |s.blocks| == c.n_blocks as int
        && forall i :: 0 <= i < |s.blocks| ==> Block.Valid(s.blocks[i])
    }

    // Invariant preservation

    lemma InitImpliesValid(c: Constants, s: State) 
        ensures Valid(c, s)
    {}

    lemma ReadPreservesValid(c: Constants, s: State, s': State, block_id: int, val: Block.State)
        requires Valid(c, s)
        requires s == s'
        requires 0 <= block_id as int < |s.blocks|
        requires Read(c, s, block_id) == val
        ensures Valid(c, s')
    {
    }
    
    lemma WritePreservesValid(c: Constants, s: State, s': State, block_id: int, val: Block.State)
        requires Valid(c, s)
        requires 0 <= block_id as int < |s.blocks|
        requires Write(c, s, s', block_id, val)
        ensures Valid(c, s')
    {
    }

    // Step relations

    datatype Step =
    | ReadBlock(id: int, val: Block.State)
    | WriteBlock(b: int, val: Block.State)

    predicate StepImpliesValid(c: Constants, s: State, s': State, step: Step)
    {
        match step {
            case ReadBlock(off, val) => && 0 <= off as int < |s.blocks| 
                                      && Valid(c, s)
                                      && s == s'
                                      && s.blocks[off] == val
                                      && Valid(c, s')
            case WriteBlock(off, val) => && 0 <= off as int < |s.blocks|
                                       && Valid(c, s)
                                       && Block.Valid(val)
                                       && s'.blocks == s.blocks[off := val]
                                       && Valid(c, s')
        }       
    }

    predicate Next(c: Constants, s: State, s': State)
    {
        exists step :: StepImpliesValid(c, s, s', step)
    }

    //

    function method Read(c: Constants, s: State, block_id: int) : Block.State
        requires Valid(c, s)
        requires 0 <= block_id < |s.blocks|
        ensures Block.Valid(Read(c, s, block_id))
    {
        s.blocks[block_id]
    }

    predicate Write(c: Constants, s: State, s': State, block_id: int, val: Block.State)
        requires Valid(c, s)
    {
        && 0 <= block_id < |s.blocks|
        && Block.Valid(val)
        && s'.blocks == s.blocks[block_id := val]
    }

}
