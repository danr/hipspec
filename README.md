HipSpec - the Haskell Inductive Prover meets QuickSpec
======================================================

Automatically prove properties about Haskell programs by using
induction or coinduction. The approach taken is to compile Haskell
programs to first order theories. Induction is applied on the meta
level, and proof search is carried out by automated theorem provers
for first order logic with equality.

This version uses HALO to translate from GHC Core to First Order
Logic.  There is an old version is in the `src-exts` branch, using
Haskell Source Extensions.

Installation instructions
=========================

Make sure you have `quickspec` installed. It isn't yet on hackage,
so the easiest way is to get it from github:

    git clone https://github.com/nick8325/quickspec

Follow its instructions, but it all boils down to `cabal install`.

Clone this repo, if you haven't already:

    git clone https://github.com/danr/hipspec.git

Then, you need to pull `HALO`, the HAskell to LOgic Translator:

    git submodule update --init

Then, in the main directory, run

    cabal install

This should install the HipSpec library.

If you later update the repository with `git pull`, you will probably
need to update `HALO` as well. Do the same as before, but without `--init`:

    git submodule update

If you want to install the HipSpec executable, run cabal like this:

    cabal install -fexecutable

Supported theorem provers
-------------------------

You will need to install at least one or more of the following theorem provers:

  * [E
    prover](http://www4.informatik.tu-muenchen.de/~schulz/E/E.html),
    recommended, precompiled binaries [here](http://www4.informatik.tu-muenchen.de/~schulz/E/Download.html)

  * [z3](http://research.microsoft.com/en-us/um/redmond/projects/z3/),
    recommended, precompiled binaries [here](http://research.microsoft.com/en-us/um/redmond/projects/z3/download.html)

  * [vampire](http://www.vprover.org/)

  * [SPASS](http://www.spass-prover.org/)

  * [equinox](https://github.com/nick8325/equinox)

Only user stated properties mode
================================

To prove properties using structural induction without generating a
background theory with QuickSpec, use the `hipspec` executable
installed with the `cabal` file. Import `Hip.Prelude` to get access
to the `=:=`, `oops` and `Prop` functions, and now you can enter
properties in a fashion like this:

    import Hip.Prelude

    prop_mirror_involutive :: Tree a -> Prop (Tree a)
    prop_mirror_involutive t = mirror (mirror t) =:= t

    prop_mirror_idempotent :: Tree a -> Prop (Tree a)
    prop_mirror_idempotent t = oops (mirror (mirror t) =:= mirror t)

Type signatures on properties are optional, unlike the old version
based on `haskell-src-exts`.

The `oops` function exists mainly for the reason to check that HipSpec
is not lying and proves whatever you give it.

Theory exploration mode
=======================

The interesting mode is when you use QuickSpec to generate a theory.
A few steps needs to be carried out. An example is given in `testsuite/Nat.hs`.

Import the `Hip.HipSpec` library. This gives you the `hipSpec` function.

Make a `main` function which calls `hipSpec`. This function takes
three parameters: the file name, a configuration and the maximum depth
of generated terms. Example:

    main = hipSpec "Trees.hs" conf 3
      where conf = ...

The configuration explains what variables and constants QuickSpec
should use when generating terms.

  * Make variables with `vars`, then string representations and
    something of the type of the variable.

  * Use `fun0`, `fun1`, `fun2`, and so on, and a string representation,
    for Haskell functions and constructors.

We continue the example above:

    main = hipSpec "Trees.hs" conf 3
      where
        conf = [ vars ["t","u"] (undefined :: Tree Int)
               , vars ["x","y"] (undefined :: Int)
               , fun0 "Leaf" Leaf
               , fun0 "Fork" Fork
               , fun1 "mirror" mirror
               ]

For polymorphic functions, just enter some concrete and rich data type
as `Int`. To be able to translate from QuickSpec's internal representation
to HipSpec's, the string of functions and data constructors needs to match
up exactly as they are named in the source code.

Now, we are good to go. Compile this and run:

    $ ghc Trees.hs
    ...
    $ ./Trees
    ...

To make things run a bit faster, use optimisation and parallelism by
passing the flags `-O2 -threaded -rtsopts` to `ghc`. Then run the
executable with `+RTS -N2`, where `2` is the number of cores on your
machine.

Options and flags
=================

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hipspec` executable, or executables compiled
with the HipSpec library.

QuickSpec flags
---------------

  * `--swap-repr` (`-s`): Swap equations with their representative
  * `--prepend-pruned` (`-r`): Prepend nice, pruned, equations from QuickSpec
    before attacking all equations.
  * `--quadratic` (`-q`): Add all pairs of equations from every equivalence
    class instead of picking a representative.
  * `--interesting-cands` (`-i`): Consider properties that imply newly
    found theorems.
  * `--assoc-important` (`-a`): Consider associativity as most important
    and try to prove it first.


Induction flags
---------------

  * `--inddepth=INT`: Induction depth, default 1.
  * `--indvars=INT`: Variables to do induction on simultaneously,
    default 1.
  * `--indhyps=INT`: For some data types, and with many variables and
    depths, the number of hypotheses become very large. This flag
    gives the upper bound, and just cuts of if it gets too
    big (compromising completeness). Default is 200.
  * `--indparts=INT`: If the number of parts (bases and steps) gets
    over this threshold, this combination of variables and depths is
    skipped. Default is 10.


Specifying theorem prover
-------------------------

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

Processors and parallel proving
-------------------------------

As you probably have a multi-core machine, you might just as well use
some more processor core. While theorem provers are still usually
single-core, you can run many of them in parallel. The `--processes`
or `-N` flag will let you specify this. The default is 2, but if you
have, say, 8 cores and you want to use all of them:

    hipspec testsuite/hip/Nat.hs -N=8

Timeout
-------

The default timeout is one second. It can be specified with the `-t`
or `--timeout` flag:

    hipspec testsuite/hip/Nat.hs -t=5

Now, each theorem prover invocation will be 5 seconds long.

Output TPTP
-----------

Should you wish to inspect the generated tptp theory, you can use
`--output` (or `-o`) and make a `proving/` directory. Then all
relevant `.tptp` files will be put there for you to view.

A good combination is to also use the `--readable-tptp` flag (or `-R`).
Without this flag, all tptp identifiers get short, cryptic names that
are quick to otput. With the flag, the identifiers should have a
strong resemblence from their origin in the Haskell Source (or at
least, their Core representation).

Consistency
-----------

Doubting the consistency of the theories that are generated? Run with
the `--consistency` flag (for short, `-c`), which will let the theorem
provers try to find a contradiction without any properties.

Authors and contact
===================

The HipSpec group consists of:

  * Dan Rosén, main developer
    [danr at student dot chalmers dot se](mailto:danr-student-chalmers-se),

  * Koen Claessen

  * Moa Johansson

  * Nicholas Smallbone


