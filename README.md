HipSpec - the Haskell Inductive Prover meets QuickSpec
======================================================

[![Build Status](https://travis-ci.org/danr/hipspec.png?branch=master)](https://travis-ci.org/danr/hipspec)

HipSpec is only supported on GHC 7.4.1 and GHC 7.6.1. Patches
for other versions are more than welcome.

## Installation instructions

    cabal install

You need to have the development version of QuickSpec. It can be obtained by
cloning that repository:

    git clone https://github.com/nick8325/quickspec

Assuming your directory structure looks like this:

    $CWD/
        hipspec/
            ...
        quickspec/
            ...

You current directory is $CWD. You can then install quickspec and hipspec in
one go, which makes the dependency analysis better:

    cabal install hipspec quickspec

### Supported theorem provers

You will need to install at least a theorem prover. Currently, we only support z3:

  * [z3](http://research.microsoft.com/en-us/um/redmond/projects/z3/),

## Tutorial

In HipSpec, QuickSpec will generate a background theory, which
then Hip will try to prove as much as possible from.
This little tutorial will try to explain how to use HipSpec
as a theory exploration system.

An example is given in [`testsuite/examples/Nat.hs`](https://github.com/danr/hipspec/blob/master/testsuite/examples/Nat.hs).

You need to import `HipSpec.Prelude`. The data types you will put in the
signature needs to be an instance of `Eq`, `Ord`, `Data.Typeable`, and
`Test.QuickCheck.Arbitrary`. Example:

    {-# LANGUAGE DeriveDataTypeable #-}

    import HipSpec.Prelude

    data Nat = S Nat | Z
        deriving (Eq,Ord,Typeable)

    instance Arbitrary Nat where
        arbitrary = ...

Hipspec will look for a QuickSpec signature in a top level declaration called
`sig`.  The signature explains what variables and constants QuickSpec should
use when generating terms.

  * Make variables with `vars`, then string representations and
    something of the type of the variable.

  * Use `fun0`, `fun1`, `fun2`, and so on, and a string representation,
    for Haskell functions and constructors.

Example:

    sig = [ vars ["x", "y", "z"] (error "Nat type" :: Nat)
          , fun0 "Z" Z
          , fun1 "S" S
          , fun2 "+" (+)
          , fun2 "*" (*)
          ]

You need to give concrete, monoromorphic signatures to polymorphic functions
(and variables). QuickSpec gives you one which is called `A`. You can see it as
a skolem type. In fact, as you might have guessed, it's a newtype wrapper
around `Int`. To be able to translate from QuickSpec's internal representation
to HipSpec's, the string of functions and data constructors needs to match up
exactly as they are named in the source code.

Now, we are good to go!

    $ hipspec Nat

### Bottoms (domain theoretic ones, that is)

If you wish to prove properties with bottoms, add the `--bottoms` flag. Voila!

### Theory Exploration mode

To make HipSpec print a small, pruned theory of everything that is proved
to be correct, run the compiled binary with `--explore-theory`, or `-e` for
short.

## Options and flags

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hipspec` executable.

### QuickSpec flags

  * `--swap-repr` (`-s`): Swap equations with their representative
  * `--prepend-pruned` (`-r`): Prepend nice, pruned, equations from QuickSpec
    before attacking all equations.
  * `--quadratic` (`-q`): Add all pairs of equations from every equivalence
    class instead of picking a representative.
  * `--interesting-cands` (`-i`): Consider properties that imply newly
    found theorems.
  * `--assoc-important` (`-a`): Consider associativity as most important
    and try to prove it first.


### Induction flags

  * `--inddepth=INT` (`-d`): Induction depth, default 1.
  * `--indvars=INT` (`-v`): Variables to do induction on simultaneously,
    default 2.
  * `--indhyps=INT` (`-H`): For some data types, and with many variables and
    depths, the number of hypotheses become very large. This flag
    gives the upper bound, and just cuts of if it gets too
    big (compromising completeness). Default is 200.
  * `--indobligs=INT` (`-O`): If the number of parts (bases and steps) gets
    over this threshold, this combination of variables and depths is
    skipped. Default is 25.


### Specifying theorem prover

The `--provers` flag, or `-p` for short, takes a one character
description for the theorem prover:

   * **`z`**: z3
   * **`Z`**: z3 with unsatisfiable cores, solver prints used lemmas

You can specify many at the same time, i.e. `--provers=zZ`, which indeed looks
a bit silly.

### Processors and parallel proving

As you probably have a multi-core machine, you might just as well use
some more processor core. While theorem provers are still usually
single-core, you can run many of them in parallel. The `--processes`
or `-N` flag will let you specify this. The default is 2, but if you
have, say, 8 cores and you want to use all of them, use `-N=8`. Also
give `+RTS -N8` to the executable then.

### Timeout

The default timeout is one second. It can be specified with the `-t` or
`--timeout` flag. With `-t=5`, each theorem prover invocation will be 5 seconds
long. The timeout can be issued as a double, so -t=0.1 can be used to get
100 ms timeout.

### Output theories

Should you wish to inspect the generated theory, you can use `--output` (or
`-o`) and make a `proving/` directory. Then all relevant files will be put
there for you to view.

### Consistency

HipSpec will try to prove `True =:= False` if given the `--consistency` flag,
or `-c` for short. It will add any proven lemmas to the theory, and the
definitions of functions used in those lemmas.

## Authors and contact

The HipSpec group consists of:

  * Dan Rosén, [danr@chalmers.se](mailto:danr@chalmers.se),

  * Koen Claessen

  * Moa Johansson

  * Nicholas Smallbone

