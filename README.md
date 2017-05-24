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
