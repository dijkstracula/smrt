# Top-down denotational disk controller modeling with SMRT

The goal for this project was to implement a collection of primitives for
decomposing and refining models of stateful transition systems in Dafny[@Leino10],
and to apply those primitives against a concrete use-case: building a random
block-addressable indirection layer atop a shingled magnetic recording
disk[@SMROverview] as part of a hypothetical HDD controller.  As a side effect
of this work, several patches were submitted and accepted to the open-source
Dafny compiler.  We discuss the current state of the SMR disk modeling effort,
called _SMRT_ in a broader modeling philosophy that we are calling _denotational
modeling_, and propose several avenues for future work that we suspect to be
fruitful.

## Introduction

Uncovering software defects becomes all the more critical the farther down the
stack it resides, the more stateful it is, and the more opaque its internals
are. 


