## Abstract

This project implements a collection of primitives for decomposing and refining
models of stateful transition systems in Dafny[@Leino10], and to apply those
models against a concrete use-case: building a random block-addressable
indirection layer atop a shingled magnetic recording disk[@SMROverview] as part
of a hypothetical HDD controller.  As a side effect of this work, several
patches were submitted and accepted to the open-source Dafny compiler.  We
discuss the current state of the SMR disk modeling effort, _SMRT_, in a broader
modeling philosophy inspired by mixins and traits in OOP languages, and propose
several avenues for future work that we suspect to be fruitful.

As a side-effect of working on SMRT, several issues in Dafny (
[#2943](https://github.com/dafny-lang/dafny/issues/2943),
[#3048](https://github.com/dafny-lang/dafny/issues/3048),
[#3089](https://github.com/dafny-lang/dafny/issues/3089),
[#3105](https://github.com/dafny-lang/dafny/issues/3105))
were uncovered, and several PRs were put out to address many of them (
Compiler:
[#3044](https://github.com/dafny-lang/dafny/pull/3044),
[#3093](https://github.com/dafny-lang/dafny/pull/3093),
[#3130](https://github.com/dafny-lang/dafny/pull/3130);
Language server:
[#290](https://github.com/dafny-lang/ide-vscode/issues/290)
).

## Introduction

Uncovering software defects becomes all the more critical the farther down the
stack it resides, the more stateful it is, and the more opaque its internals
are.  Storage device controllers reside in the unfortunate intersection of all
three: most software developers need never know of its existence, those who do
have no choice but to treat it as an inscrutable black box, and what is more
stateful than a hard disk?  Any bugs that manifest in storage firmware would be
nontrivial to diagnose and have a significant blast radius.  Hardware vendors,
therefore, are justifiably conservative around firmware feature development and
user-facing interfaces and abstractions.

This conservatism is seen in each major shift in storage technology: flash
controllers are complex out of necessity, since wear levelling and write
buffering, inherent to the technology itself, need to be hidden behind firmware
in order to maintain the veneer of a block-addressable, non-degradable storage
medium.

Shingled magnetic recording (SMR) hard disks, which trade direct modification
of disk sectors for increased storage capacity [@SMROverview], are another
advancement whose complexity is papered over at the controller level.
So-called _drive-managed SMR_ disks, similar to flash devices, expose the
one-size-fits-all block-addressable interface to software at the expense of
highly variable throughput if the drive's indirection mechanism cannot keep up
with host I/O.  By contrast, _host-managed SMR_ exposes a series of append-only
regions called _zones_ that avoid expensive indirection mechanisms and data
corruption on random writes, but require significant re-architecture to the
software that sits above it[@Ext4].  Proposals for so-called "caveat
scriptor"[@CaveatScriptor] disks permit physical block writes anywhere on the
disk, but an off-by-one bug in the software stack could have disastrous data
integrity consequences.  It's unsurprising, then, that such drives do not
actually exist in the wild.

This work began as a thought experiment inspired by the
exokernelian[@Exokernel] view that mediating access to raw physical devices
lets applications best choose how to manage their use, as an attempt to
reconcile control and safety.  In particular, Exokernel's _Application-Specific
Safe Handlers_ (ASHs) permit application-specific optimisations to be executed
in kernelspace by mechanisms like sandboxing and static analysis.  

We propose a similar methodology one layer down the stack: a hypothetical disk
controller could consume verified and signed policy code that conforms to a
baseline formal specification; said signed code implements desired
storage-level properties from the perspective of some high-performance
application like a filesystem or database.  Equivalently: a software
stack, formally checked against a model of an underlying _caveat scriptor_
storage device, could peek and poke bits on such a disk in a safer manner.

We use Dafny as a modelling language to explore these ideas; such models form
the bedrock for a verified SMR storage stack called SMRT[@SMRT], comprised so
far of about 1150 lines of Dafny code.  Alternatives to Dafny abound; Alloy has
seen adoption for reasoning about storage systems [@AlloyFFS], and a pure
type-theoretic approach that joins specification and a satisfying
implementation has been enjoyed in a similar domain elsewhere [@BilbyFS]
[@FSCQ].  That said, verification of large-scale systems through Dafny has
found success in recent work [@IronFleet] [@VeriBetrKV]; in terms of Dafny
language idioms, we drew particular inspiration from [@VeriBetrKV].

## Disk drives as a modelling problem

Rather than working about a particular workload or application, this project
takes a formal modeling approach as the first cut.  In particular, our goal was
to model a hypothetical SMR disk, implement a random-access indirection layer
atop it, and show refinement against a standard block-addressable drive; in
other words, verify that a simple drive-managed SMR disk controller externally
behaves indistinguishably from a non-SMR disk.

At present, there are four disk models implemented in SMRT: the three of
interest to us are a block-addressable disk, mimicking a CMR disk, a zoned disk
with an append-only interface similar to host-managed SMR, and a zoned disk
with a block-addressable indirection layer, similar to drive-managed SMR (The
fourth disk, which models drive tracks, was intended to reason about
corruption adjacent singled tracks on write operations, but proved not to be
useful and so is considered vestigial for the moment.)

We make no claims that our drive-managed disk's indirection layer is novel or
even remotely desirable.  Actual SMR indirection systems involve layers of
careful set-associative caching or new "shingled" block primitives
[@SMRIndirection]; by contrast, ours instead was optimised for ease of
invariant writing.  At all times, one SMR zone is sacrificed as a "buffer" zone;
on a random write to some LBA, an indirection system computes the actual PBA
and zone offset, and faults _the entire PBA's zone_ to the buffer zone with the
destructive update applied.  After all blocks are copied, the PBA's former zone
becomes the new buffer zone.  As a result, only `(n-1)/n` blocks are actually
usable by application code.  Despite terrible write amplification, inductive
invariants for this drive are straightforward to express.

```

                    ┌─ Operation:             │
                    │  Overwrite block 2      │
                    ▼                         │
                 ┌────────┬────────┐          │ ┌────────┬────────┐
 Logical "zones" │ABCD    │EFGHIJ  │          │ │AB*D    │EFGHIJ  │
                 └───┬────┴────┬───┘          │ └───┬────┴────┬───┘
                     │         │              │     │         │    Zone map:
  Zone map:          │         │              │     │         │    {0:0, 1:1}
  {0:2, 1:1}         └─────────┼────────┐     │     │         │    Buf zone: 2
  Buf zone: 0                  │        │     │     │         │
                 ┌────────┬────▼───┬────▼───┐ │ ┌───▼────┬────▼───┬────────┐
  Physical zones │        │EFGHIJ  │ABCD    │ │ │AB*Z    │EFGHIJ  │        │
                 └────────┴────────┴────────┘ │ └────────┴────────┴────────┘

 Figure 0: A logical random-access write requires faulting every block in the
 target zone over to the buffer zone.
```

### Modelling a drive with SMRT

We take a "domain-first" approach to modelling in SMRT.  A disk model called `D`
is comprised of up to three state datatypes:

- `D.Constants`: immutable attributes of the drive. Examples of Constant data
  include the size of a given device in blocks, or the number of and size of
  each zone in a zoned disk.

- `D.Persistant`: generally refers to durable data stored on the disk itself:
  this could be random-accessible block data, append-only zones, or perhaps
  some combination of the two.

- `D.Volatile`: attributes of the drive that are ephemeral, such as
  in-disk-controller memory copies of drive constants and metadata.  By
  convention, in contrast to durable state, this data would be undefined
  following a crash.

Not every disk necessarily requires all three: for instance, an abstract
block-addressable disk has no volatile state to keep track of, and for
simplicity our SMR drive only stores its indirection mapping on disk.  To
simplify the presentation and to align with the interface currently
implemented, we will refer to a `State` value as either a composition of
`Persistent` as well as a `Volatile` value, or simply the former if no volatile
state is defined on the disk.

For each of the drives currently implemented in SMRT, we have some variation on
a `Read` and a `Write` (see Fig. 1).  The specifics may vary: block-addressable
disks' write steps will refer to a block address, and a zoned disk will refer
instead to the zone to append.  Critically: at this level we are only concerned
with "user interface"-level steps, leaving orthogonal concerns like asynchrony
and failures to refinement layers.

```
datatype Step =
| ReadBlock(lba: uint64, val: Block.State)
| WriteBlock(lba: uint64, val: Block.State)

datatype Constants = Constants(n_blocks: int)
datatype State = State(blocks: seq<Block.State>)

Figure 1: Modelling datatypes for a block-addressable storage device.
```

Each possible `Step` is operated on via a relation between `State`s.  Per
VeriBetrKV's convention, non-mutating steps are implemented as Dafny functions
(since no `State` changes because of taking the step), whereas mutating steps
are written in a relational style, consuming before and after `State`s.  For
instance, a step relation for a write would enforce that the arguments to the
`WriteBlock` structure are well-formed, and that the before and after states
only differ in the written-to block.

```
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

Figure 2: Step relations on a block-addressable storage device.
```

### Verifying a drive with SMRT

Each piece of state data has a notion of validity: for instance, a `Persistent`
state datatype must never spuriously change the number of blocks on the disk,
an immutable value defined in the corresponding `Constant` state datatype.
This, in turn, would have its own notion of validity, perhaps encoding the
requirement that the number of blocks is non-negative.  Anecdotally: a well
defined `Valid` function helps reduce the amount of uninterpretable
counterexamples produced by Dafny, and in cases where counterexample values
seem contradictory, often the first step in debugging it was to place further
constraints in `Valid`.  `Step`s also have their own notion of validity: for
instance, the `lba` values in Figure 1's datatypes must be nonzero and bounded
by the size of the drive.


Verification happens inductively, in the straightforward manner.  A nascent
`State` variable is shown to satisfy its `Valid` predicate, and that no valid
`Step` can ever result in a `State` stepping from a valid state to an invalid
one.  For the simpler of the drive models, these were proven as Dafny lemmas,
and the verifier was able to conclude their correctness without writing any
statements in the lemmas' bodies!

```
    /* Given drive constants, give us the state of a fresh drive. */
    function method Init(c: Constants) : State
        requires ConstantsValid(c)
        ensures Valid(c, Init(c))

    /* We'll need to specify whether our datatypes are valid. */
    predicate ConstantsValid(c: Constants)
    predicate Valid(c: Constants, s: State)
    predicate ValidStep(c: Constants, s: State, s': State, step: Step);
    predicate Next(c: Constants, s: State, s': State) {
        exists step :: ValidStep(c, s, s', step)
    }

    /* A disk must begin in a valid state. */
    lemma InitImpliesValid(c: Constants)
        requires ConstantsValid(c)
        ensures Valid(c, Init(c))

    /* Whatever our step relation is, we need to maintain validity. */
    lemma StepImpliesValid(c: Constants, s: State, s': State, step: Step)
        requires Valid(c, s)
        ensures Valid(c, s')
    
Figure 3: Abstract inductive validity interface
```

### Refining SMRT models

Recall that our goal was to show that our shingled indirection layer is
functionally equivalent to a standard block-addressable disk.  In order to do
so, SMRT needs a notion of _refinement_ [@RefinementBook].  (Note that our
notion of refinement refers to relating two automata or transition systems,
_not_ Dafny's inheritance-like notion of module refinement.).  We begin by
writing refinement functions that take concrete model datatypes to their
corresponding abstract one.  For instance, an SMR drive's number of available
blocks needs to be reduced when refining to an abstract block-addressable disk,
since one zone is used for the buffer and is not "externally visible".

```
    type C = CowZonedDisk
    type A = BlockDisk

    function IC(c: C.Constants): A.Constants
        requires C.ConstantsValid(c)
        ensures A.ConstantsValid(IC(c))
    
    function I(c: C.Constants, s: C.State): A.State
        requires C.ConstantsValid(c)
        requires C.Valid(c,s)
        ensures A.Valid(IC(c), I(c, s))

Figure 4: Refinement mapping between disk models
```

Refinement is shown in the usual forward simulation sense.  In order to ensure
our basic mechanism is well-formed, we started with a straightforward but
limited notion of module refinement: simple simulation.  Concretely, simple
simulation ensures that irrespective of what step the concrete model would like
to take, there still exists exactly one step for the abstract model to take
[@RefinementBook].  For example, an indirect SMR write to a zoned block is
simulated by abstracting away the entire indirection layer and zone copying,
and simply applying the write to the given block directly.

Of course, this is not entirely sufficient: in cases like our indirect SMR
disk, a write operation is actually made up of many individual zone append
operations.  Treating them as "a single atomic block" only demonstrates
correctness in the absence of possible intermediary operations - thus, each
transition in the concrete model must conform to _one or more_ transitions in
the abstract model with the same effects.

```
    /* The refinement module, containing IC(), I(), etc... */
    import R = CowZonedDiskRefinesBlockDisk

    function ReadOps(c: C.Constants, s: C.State, lba: uint64, val: A.Block.State): seq<A.Step>
        requires C.Valid(c, s)
        requires 0 <= lba as int < c.zd.n_blocks as int
        requires A.Block.Valid(val)
        ensures forall i :: 0 <= i < |ReadOps(c, s, lba, val)| ==>
            ValidStep(R.IC(c), ReadOps(c, s, lba, val)[i])
    {
        var lzone :| ZonedDisk.resolve_lba(c.zd, lba, lzone); // 1) Find which logical zone the LBA refers to...
        var off := lba - c.zd.zone_map[lzone].0;              // ...and the index into that zone...
        var pzone := C.buffer_resolve(c, s, lzone);           // ...and the corresponding physical zone.
        [A.ReadBlock(pzone + off, val)]                       // 2) In this case, one read is sufficient.
    }

Figure 5: Implementation of a step relation (simplified): here, a read operation is a one-to-one relation;
a write operation involves a full zone copy, comprising many block writes, and thus would return a sequence of
length greater than one.  
```

Abstract steps are applied by "folding over" the sequence, applying each step
in turn to the refined state until the sequence is exhausted and a final
stepped states is derived.

Non-injective forward simulation is currently in a state of "partial
correctness": introducing the refinement functions `I()` and `IC()` into these
simulations' lemmas induces Dafny verification timeouts, even if their use is
not more involved than in the injective simple forward simulation case.

## Towards "trait-forward" modelling

SMRT's drive models differ from other work in that we do not encode internal,
invisible mechanisms like operation reordering and other forms of asynchrony
directly in the model, nor externalities like crashes. This is by design; as
discussed in the refinement subsection, SMRT is an exercise in trait-like
_compositional modeling_, which we attempt to maintain external concerns as
distinct from the core disk models.  In so doing, modellers can fault in
independent concerns by "mixing in" additional actions external to the model
itself, even ones imagined after the initial disk implementation.  Drawing from
the economic meaning of the word, we refer to such concerns as _externalities_.
Previous work like Yggdrasil [@Yggdrasil] models disks inherently as an
asynchronous, crashable "concept", by contrast.  We took this opportunity
to explore an alternate approach.

Externality modelling in SMRT extends the space of possible steps that the
system can take.  For instance, in-progress work on crash refinement
non-deterministically weaves in crash steps into an operations sequence.  An
asynchronous refinement module could perhaps permute such a sequence.

```
    datatype Step =
        | IOStep(A.Step)
        | CrashStep

    function Weave(s: seq<A.Step>): seq<Step>
    {
        if |s| == 0 then [] else
            var cstr :| 0 <= cstr <= 1;
            if cstr == 0 then [IOStep(s[0])] + Weave(s[1..])
                         else [CrashStep]
    }

Figure 6: Extending a sequence of disk operations by inserting crash steps in arbitrary points.  Notice
that a crash step drops all subsequent disk operations, preventing the operation from fully completing.
```

Trait-forward modelling was not a total success here thus far.  In particular,
the inherent indirection between concerns seemed to trip Dafny's resolver up,
leading almost immediately to verification timeouts that obstructed feature
work.  Whether verification times exploding is inherent in this style of Dafny
programming or simply a matter of operator error is still yet to be determined.
Also, arguably, separating ephemeral from durable state is a layering violation
if we also expect crash refinement to be separate from the model, so there is
likely work that should be done to meditate on how this should be best
composed.

## Future directions

Clearly, resolving verifier timeouts is a top priority - it's hard to make
forward progress without those issues being resolved.  It is conceivable that
walking back the "trait-forward" methodology might be necessary in order to do
so.  Once the general refinement mechanism is in place, it makes sense to
explore a more reasonable and realistic indirection mechanism than the trivial
"fault over the entire zone on a random write" one demonstrated here.

We have obliquely discussed drive performance in terms of our indirection
mechanism's terrible write amplification - it is interesting to think about how
we might more rigorously quantify and compare translation layer performance
given their abstract models.

More generally, SMRT is comprised only of ghost code - there is no actual
implementation to extract.  While a _caveat scriptor_ disk or one with a
programmable translation layer remains a fantasy, this work -- particularly
with a performance analysis bent -- could form the basis of an interpretable
hardware layer to build SMR-optimised code like a database storage engine or
file system atop.
