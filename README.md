# Compiling a Fifty Year Journey [![Build Status](https://travis-ci.org/pa-ba/McCarthy-Painter.svg?branch=master)](https://travis-ci.org/pa-ba/McCarthy-Painter)

This repository contains the supplementary material for the paper
["Compiling a Fifty Year Journey"](docs/paper.pdf)
by Graham Hutton and Patrick Bahr.  The material includes Coq
formalisations of the calculations in the paper.


## File Structure


Below we list the relevant Coq files for the calculations in the
paper:

 - [Arith.v](Arith.v): the calculations from the paper (arithmetic expressions)
 - [Vars.v](Vars.v): the calculations for the language from McCarthy &
   Painter paper (arithmetic expressions + variables)
 - [Memory.v](Memory.v): the abstract memory model
 - [LinearMemory.v](LinearMemory.v): simple instantiation of the memory model
 - [Tactics.v](Tactics.v): tactics library

## Paper vs. Coq Proofs


The Coq proofs proceed as the calculations in the paper. There are,
however, two minor technical difference due to the nature of the Coq
system.

  1. In the paper the derived VMs are tail recursive, first-order
     functions. The Coq system must be able to prove termination of
     all recursive function definitions. Since Coq's termination
     checker is not powerful enough to prove termination for some of
     the VMs (VMs from sections 3.1, 4.1, 5) or the VMs are not
     expected to terminate in general (VMs for lambda calculi / for
     language with loops), we had to define the VMs as relations
     instead. In particular, all VMs are defined as a small-step
     semantics. Each tail recursive function of a VM corresponds to a
     configuration constructor in the small-step semantics. As a
     consequence, the calculations do not prove equations, but rather
     instances of the relation `=>>`, which is the transitive,
     reflexive closure of the relation `==>` that defines the VM.

  2. The Coq files contain the final result of the calculation, and
     thus do not reflect the *process* of discovering the definition
     of the compiler and the VM. That is, the files already contain
     the full definitions of the compiler and the virtual machine. But
     we used the same methodology as described in the paper to
     *develop* the Coq proofs. This is achieved by initially defining
     the `Code` data type as an empty type, defining the `==>`
     relation as an empty relation (i.e. with no rules), and defining
     the compiler function using the term `Admit` (which corresponds
     to Haskell's "undefined"). This setup then allows us to calculate
     the definition of the `Code` data type, the VM, and the compiler
     as described in the paper.


## Technical Details

### Dependencies

- To check the proofs: Coq 8.5pl3
- To step through the proofs: GNU Emacs 24.5.1, Proof General 4.4

### Proof Checking

The complete Coq development in this repository is proof-checked
automatically. The current status is:
[![Build Status](https://travis-ci.org/pa-ba/McCarthy-Painter.svg?branch=master)](https://travis-ci.org/pa-ba/McCarthy-Painter)

To check and compile the complete Coq development yourself, you can
use the `Makefile`:

```shell
> make
