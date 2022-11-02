include "Types.dfy"

abstract module Disk {
    /* Our disk depends on two datatypes: 
     * - Constants, which are immutable properties of the disk;
     * - State, which can change as the Disk steps between states.
     * TODO: We should probably also distinguish between peristent state and
     * volatile state (the latter being zapped out during a Crash transition).
     */
    type Constants
    type State

    /* Encodes all the things a Disk can do (Read a block, write a block, append
     * to a zone, crash, etc) */
    type Step

    /* Given Disk contents, give us an initial drive state. */
    function method Init(c: Constants) : State 
        requires ConstantsValid(c)
        ensures Valid(c, Init(c))

    /* Correspondingly, we'll need to assert whether our state variables
     * are valid. */
    predicate ConstantsValid(c: Constants)
    predicate Valid(c: Constants, s: State)

    /* A disk must begin in a valid state. */
    lemma InitImpliesValid(c: Constants, s: State) 
        requires ConstantsValid(c)
        requires s == Init(c)
        ensures Valid(c, s)

    /* Whatever our step relation is, we need to maintain validity. */
    predicate StepImpliesValid(c: Constants, s: State, s': State, step: Step)

    // XXX: I'd like to have a concrete Next() predicate at this point, stating
    // exists step :: StepImpliesValid(c, s, s', step); but, I'm getting an
    // error saying "an exists in a predicate def'n is not allowed to depend on
    // the set of allcoated references, but values of step may contain
    // references".  This isn't a problem when StepImpliesValid is concretised
    // (i.e. in BlockDisk).  It'd be nice to figure out why, because I don't think
    // it's realistic to make Step a !new type.
}