HipSpec - the Haskell Inductive Prover meets QuickSpec
======================================================

Automatically prove properties about Haskell programs by using
induction or coinduction. The approach taken is to compile Haskell
programs to first order theories. Induction is applied on the meta
level, and proof search is carried out by automated theorem provers
for first order logic with equality.

Exprimental version
===================

The `master` branch of this repository is still experimental. The old
version is in the `src-exts` branch.

Installation instructions
=========================

First, you need to pull `halt`, the Haskell to Logic Translator:

    git submodule update --init

Then, in the main directory, run

    cabal install

This should install the HipSpec library and the hipspec executable.

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

Options and flags
=================

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hipspec` executable, or executables compiled
with the HipSpec library.

Specifying theorem prover
-------------------------

The `--provers` flag takes a one character description for the theorem
prover:

   * **`e`**: E prover
   * **`z`**: z3
   * **`v`**: vampire 32 bit
   * **`V`**: vampire 64 bit
   * **`s`**: SPASS
   * **`x`**: equinox

You can specify many at the same time, i.e. `--provers=zevs`, which
will run z3, E prover, vampire 32-bit and SPASS, in that order, on
each problem.

Processors and parallel proving
-------------------------------

As you probably have a multi-core machine, you might just as well use
some more processor core. While theorem provers are still usually
single-core, you can run many of them in parallel. The `--processes`
or `-p` flag will let you specify this. The default is 2, but if you
have, say, 8 cores and you want to use all of them:

    hipspec testsuite/Nat.hs -p=8

Timeout
-------

The default timeout is one second. It can be specified with the `-t`
or `--timeout` flag:

    hipspec testsuite/PatternMatching.hs -t=5

Now, each theorem prover invocation will be 5 seconds long.

Consistency
-----------

Doubting the consistency of the theories that are generated? Run with
the `--consistency` flag (for short, `-c`), which will let the theorem
provers try to find a contradiction without any properties.

Output TPTP
-----------

Should you wish to inspect the generated tptp theory, you can use
`--output` and make a `proving/` directory. Then all relevant `.tptp`
files will be put there for you to view.

Authors and contact
===================

The HipSpec group consists of:

  * Dan Rosén, main developer
    [danr at student dot gu dot se](mailto:danr-student-gu-se),

  * Koen Claessen

  * Moa Johansson

  * Nicholas Smallbone


