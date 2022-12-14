include "../Types.dfy"
include "../Disks/BlockDisk.dfy"

module BlockDiskRefinesItself {
import opened NativeTypes

import C = BlockDisk
import A = BlockDisk
import opened Block

function IC(c: C.Constants): A.Constants
    requires C.ConstantsValid(c)
    ensures A.ConstantsValid(IC(c))
{
    c
}

function I(c: C.Constants, s: C.State): A.State
    requires C.ConstantsValid(c)
    requires C.Valid(c,s)
    ensures A.Valid(IC(c), I(c, s))
{
    s
}

lemma RefinesInit(c: C.Constants)
    requires C.ConstantsValid(c)
    requires C.Valid(c, C.Init(c))
    ensures A.Valid(IC(c), I(c, C.Init(c)))
{}

lemma RefinesReadStep(c: C.Constants, s: C.State, s': C.State, block_id: uint64, val: Block.State)
    requires C.NextStep(c, s, s', C.ReadBlock(block_id, val))
    requires C.Read(c, s, block_id) == val
    ensures A.Read(IC(c), I(c, s), block_id) == val
{
}

lemma RefinesWriteStep(c: C.Constants, s: C.State, s': C.State, block_id: uint64, val: Block.State)
    requires C.NextStep(c, s, s', C.WriteBlock(block_id, val))
    requires C.Write(c, s, s', block_id, val)
    ensures A.Write(IC(c), I(c, s), I(c, s'), block_id, val)
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
}