HipSpec - the Haskell Inductive Prover meets QuickSpec
======================================================

[![Build Status](https://travis-ci.org/danr/hipspec.png?branch=master)](https://travis-ci.org/danr/hipspec)

## Installation instructions

HipSpec is only supported on GHC 7.4.1 and GHC 7.6.1. Patches
for other versions are more than welcome.

Make sure you have `quickspec` installed. It isn't yet on hackage,
so the easiest way is to get it from github:

    git clone https://github.com/nick8325/quickspec

Follow its instructions, but it all boils down to `cabal install`.

Have you already cloned this repo? Then get the submodules:

    git submodule update --init

Not cloned yet? Then you can clone hipspec and submodules in one go with this flag:

    git clone https://github.com/danr/hipspec.git --recursive

If you now have hipspec and its submodules, install the library thusly:

    cabal install

### Supported theorem provers

You will need to install at least one or more of the following theorem provers:

  * [E
    prover](http://www4.informatik.tu-muenchen.de/~schulz/E/E.html),
    recommended, precompiled binaries [here](http://www4.informatik.tu-muenchen.de/~schulz/E/Download.html)

  * [z3](http://research.microsoft.com/en-us/um/redmond/projects/z3/),
    recommended, precompiled binaries [here](http://research.microsoft.com/en-us/um/redmond/projects/z3/download.html)

    NOTE: You will need an old version of z3 (3.2 or older), because later z3s
    do not support TPTP format. Or send a patch which makes HipSpec print
    in a native z3 format. (Much of the code is already in halo)

  * [vampire](http://www.vprover.org/)

  * [SPASS](http://www.spass-prover.org/)

  * [equinox](https://github.com/nick8325/equinox)

## Tutorial

In HipSpec, QuickSpec will generate a background theory, which
then Hip will try to prove as much as possible from.
This little tutorial will try to explain how to use HipSpec
as a theory exploration system.

An example is given in [`testsuite/examples/Nat.hs`](https://github.com/danr/hipspec/blob/master/testsuite/examples/Nat.hs).

Two important imports:

    import HipSpec
    import HipSpec.Prelude

Make a `main` function which calls `hipSpec`. This function takes
three parameters: the file name and a QuickSpec signature. Example:

    main = hipSpec "Trees.hs" sig
      where sig = ...

If you think it's crazy that you have to write your filename,
GHC can do it for you with Template Haskell. Slap this on the
top of your file:

    {-# LANUGAGE TemplateHaskell -#}

Now the HipSpec import gives you the fileName function which
is appropriately used like this:

    main = hipSpec $(fileName) sig
      where sig = ...

The signature explains what variables and constants QuickSpec
should use when generating terms.

  * Make variables with `vars`, then string representations and
    something of the type of the variable.

  * Use `fun0`, `fun1`, `fun2`, and so on, and a string representation,
    for Haskell functions and constructors.

We continue the example above:

    main = hipSpec "Trees.hs" sig
      where
        sig = [ vars ["t","u"] (undefined :: Tree A)
              , vars ["x","y"] (undefined :: A)
              , fun0 "Leaf"    (Leaf :: A -> Tree A)
              , fun0 "Fork"    (Fork :: Tree A -> Tree A -> Tree A)
              , fun1 "mirror"  (mirror :: Tree A -> Tree A)
              ]

You need to give concrete, monoromorphic signatures to polymorphic functions
(and variables). QuickSpec gives you one which is called A. You can see it as a
skolem type. In fact, as you might have guessed, it's a newtype wrapper around
`Int`. To be able to translate from QuickSpec's internal representation to
HipSpec's, the string of functions and data constructors needs to match up
exactly as they are named in the source code. This sometimes does not work.
If this happens you can raise an [issue](https://github.com/danr/hipspec/issues).

Now, we are good to go. Compile this and run:

    $ ghc Trees.hs
    ...
    $ ./Trees
    ...

### Theory Exploration mode

To make HipSpec print a small, pruned theory of everything that is proved
to be correct, run the compiled binary with `--explore-theory`, or `-e` for
short.

### Other options

To make things run a bit faster, use optimisation and parallelism by
passing the flags `-O2 -threaded -rtsopts` to `ghc`. Then run the
executable with `+RTS -N2`, where `2` is the number of cores on your
machine.

If we import modules of whose definitions we want to prove properties about we
need to compile with these flags:

   ghc --make Trees.hs -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

There is a makefile that does this, namely
[`testsuite/Makefile.common`](https://github.com/danr/hipspec/blob/master/testsuite/Makefile.common)
As an example, goto the testsuite/examples directory. Now you
can compile the Nat.hs file by issuing:

    make Nat

If you also want to run this, you write:

    make Nat_runs

You can also specify some flags here. For instance, to use up to three
induction variables on depth two, and E as the theorem prover, using
8 cores on your machine:

    make Nat_runs provers=e indvars=3 inddepth=2 processes=8

To use the theory exploration mode, you can use the `HIP_FLAGS`
variable:

    make Nat_runs HIP_FLAGS=-e

## Options and flags

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hipspec` executable, or executables compiled
with the HipSpec library.

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

  * `--inddepth=INT` (`-D`): Induction depth, default 1.
  * `--indvars=INT` (`-S`): Variables to do induction on simultaneously,
    default 1.
  * `--indhyps=INT`: For some data types, and with many variables and
    depths, the number of hypotheses become very large. This flag
    gives the upper bound, and just cuts of if it gets too
    big (compromising completeness). Default is 200.
  * `--indparts=INT`: If the number of parts (bases and steps) gets
    over this threshold, this combination of variables and depths is
    skipped. Default is 10.


### Specifying theorem prover

The `--provers` flag, or `-p` for short, takes a one character
description for the theorem prover:

   * **`e`**: E prover
   * **`z`**: z3
   * **`v`**: vampire
   * **`s`**: SPASS
   * **`x`**: equinox
   * **`f`**: E-proof: prints which lemmas were used for each proof.

To print which lemmas were used in each proof, run with `-p=f`.

You can specify many at the same time, i.e. `--provers=zevs`, which
will run z3, E prover, vampire 32-bit and SPASS, in that order, on
each problem.

### Processors and parallel proving

As you probably have a multi-core machine, you might just as well use
some more processor core. While theorem provers are still usually
single-core, you can run many of them in parallel. The `--processes`
or `-N` flag will let you specify this. The default is 2, but if you
have, say, 8 cores and you want to use all of them, use `-N=8`:

### Timeout

The default timeout is one second. It can be specified with the `-t` or
`--timeout` flag. With `-t=5`, each theorem prover invocation will be 5 seconds
long.

### Output TPTP

Should you wish to inspect the generated tptp theory, you can use
`--output` (or `-o`) and make a `proving/` directory. Then all
relevant `.tptp` files will be put there for you to view.

A good combination is to also use the `--readable-tptp` flag (or `-R`).
Without this flag, all tptp identifiers get short, cryptic names that
are quick to otput. With the flag, the identifiers should have a
strong resemblence from their origin in the Haskell Source (or at
least, their Core representation).

### Consistency

HipSpec will try to prove `True =:= False` if given the `--consistency` flag,
or `-c` for short.

## Authors and contact

The HipSpec group consists of:

  * Dan Rosén, [danr@chalmers.se](mailto:danr@chalmers.se),

  * Koen Claessen

  * Moa Johansson

  * Nicholas Smallbone

