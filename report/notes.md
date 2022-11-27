# Top-down denotational modeling with SMRT

## Introduction

Modeling stuff is good!  Modeling complex things is unduly complex because of
compounding complexity from orthgonal issues like crash safety and asynchrony.

Modeling involves relating the behaviour of software concerns.  The simplest
distillation of this is a "is-a" relationship: a distributed KV store "is a"
hash table, a file is composed of inodes, which are composed of disk blocks.
(TODO: I like the second one less.)

This feels a lot like OOP modeling with inheritance.  Yggdrasil uses "a long
single inheritance tree".  VeriBetrKV uses "Transposition" which you can squint
at as a form of polymorphism.  What else could we imagine?

(There's something interesting in that we're strictly not targeting executable
code here.)

Modern developers have come to favour composition and trait-like mixins when
needed rather than inheritance.  (Something here that introduces "design the
top-level thing first, versus "begin with an asynchronous device" first?  Can
we think of this as factoring out domain models from separating concerns,
aspect-style?  Aspect-oriented whatever might make for good "future work"
stuff.) Can we apply these lessons to state machine modeling?

We'd like to be able to specify objects to model in a straightforward way, and
then mix in additional complexity in an ad-hoc, pay-as-you-go way, in a manner
similar to the flexibilty that traits/mixins gives developers writing
application code.

Towards this: this project designs primitives for state machine modeling and
refinement in the Dafny programming language.  We have used these primitives in
the development of SMRT, the beginning of a verified storage stack that takes
advantage of SMR hard disks.

## Dafny

Dafny is cool!

Prior work making use of Dafny (VeriBetr, IronFleet) approach modeling from an
"environment-first" perspective: one begins with properties of the world such
as asynchrony or the possibility of a system crash, and models the domain atop
those.

As a side-effect of this work, several bugs in the Dafny compiler and language
server were filed, and PRs were put out to address some of them, totaling X
lines of code contributed.

## Denotational modeling

"denotational" after denotational design
(http://conal.net/talks/denotational-design-lambdajam-2015.pdf).

## SMR disks

SMR: blah blah, append-only zones.

Host versus disk managed SMR is a false dichotomy!  We believe that an
end-to-end modeled SMR stack can obviate the need for restrictive software
abstractions in order to improve software correctness and mechatronic safety.

## Modeling a drive with SMRT

We begin with a "domain-first" approach.  Inspired by the denotational design
axiom that "the instance’s meaning is the meaning’s instance", a disk model
module called `D` is defined in terms of up to three pieces of data:

- `D.Constants`: attributes of the drive that do not change as operations
  execute on the disk.  Examples of Constant data include the size of a given
  device in blocks, or the number of and size of each zone in a zoned disk.  We
  do not consider cases where drive constants could ever change; however, there
  do exist situations that we do not consider, such as repartioning operations,
  where they conceivably could.  

- `D.Persistant`: generally refers to durable data stored on the disk
  itself: this could be random-accessable block data, append-only zones, or
  some combination of the two.

- `D.Volatile`: attributes of the drive that are ephemeral, such as in-disk
  controller memory copies of drive constants and metadata.  By convention, in
  contrast to durable state, this data is undefined following a crash.

Not every disk necessarily requires all three: for instance, an abstract
block-addressable disk has no volatile state to keep track of.  To simplify the
presentation, we will refer to a `State` value as containing either a
`Persistant` as well as a `Volatile` value, or simply the former.

The fundamental modeling primitive here is big-step semantics written in a
relational form: for instance, for a random-access block device, `predicate
Write(c: Constants, s: State, s': State, step: WriteOp)` is
true if `s'` matches `s` after applying the given `WriteOp` operation (a
tuple containing a block address and a block value).  Unsurprisingly, the
`Read` predicate would consume an equivalent `ReadOp` value.

Critially: at this layer we do not encode internal mechanisms like operation
reordering and other forms of asynchrony, nor extermal mechanisms like
crashes.

### Verifying an SMRT model

Validity of a model is shown in the standard inductive transition relation
manner: the validity of the model's state is shown to be shown in an initial,
at-construction time state, and also that any action taken on a valid state
leaves the model in a valid state.

### Refining SMRT models

SMRT can also show forward simulation between two models.  As a demonstration,
we implemented a simple random block abstraction over a zoned SMR disk model,
and then proceeded to show forward simulation to an abstract block device.

Random access on a zoned disk is implemented terribly!  But that wasn't really
the point.  Here's how it works.

Here's how the refinement works!

Now here's how we decomposed one COW zone operation into many abstract block
operations, and we did refinement on that one too.  Yikes, I better get started
on this one!

## Showing crash refinement

Yikes, I better get started on this one!

## Lessons learned

- Counterexamples are hard to reason about.  Test case minimization would be
  nice!

- Refinement in Dafny (modular specialization) seems underused: a few bugs
  found, especially w/r/t the IDE plugin that related to refinement.

- Be dogmatic about clean abstractions at your peril.  
