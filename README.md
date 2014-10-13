HipSpec - the Haskell Inductive Prover meets QuickSpec
======================================================

[![Build Status](https://travis-ci.org/danr/hipspec.png?branch=master)](https://travis-ci.org/danr/hipspec)

HipSpec is an inductive theorem prover for Haskell programs.  It will (try to)
conjecture essential lemmas to prove tricky properties.  It supports all
algebraic Haskell 98 data types and polymorphism.  We assume that functions
terminate on finite input and produce finite output.  All quantification is
only over total and finite values.

## Example

In the `examples/Rotate.hs` file we see the following definitions:

    rotate :: Nat -> [a] -> [a]
    rotate Z     xs     = xs
    rotate _     []     = []
    rotate (S n) (x:xs) = rotate n (xs ++ [x])

    prop_rotate :: [a] -> Prop [a]
    prop_rotate xs = rotate (length xs) xs =:= xs

The second definition defines a property in the HipSpec property language that
we would like to prove. The `=:=` operator simply means equals.

Let's run HipSpec on this file:

    $ hipspec Rotate.hs --auto --cg --verbosity=30
    Depth 1: 11 terms, 5 tests, 29 evaluations, 11 classes, 0 raw equations.
    Depth 2: 63 terms, 100 tests, 2151 evaluations, 48 classes, 15 raw equations.
    Depth 3: 1688 terms, 100 tests, 63851 evaluations, 1303 classes, 385 raw equations.
    Proved xs++[] == xs by induction on xs using Z3
    Proved (xs++ys)++zs == xs++(ys++zs) by induction on xs using Z3
    Proved length (xs++ys) == length (ys++xs) by induction on ys,xs using Z3
    Proved rotate m [] == [] without induction using Z3
    Proved rotate m (rotate n xs) == rotate n (rotate m xs) by induction on n,m using Z3
    Proved rotate (S m) (rotate n xs) == rotate (S n) (rotate m xs) by induction on xs using Z3
    Proved rotate m (x:[]) == x:[] by induction on m using Z3
    Proved rotate m xs++rotate m xs == rotate m (xs++xs) by induction on m using Z3
    Proved length (rotate m xs) == length xs by induction on m using Z3
    Proved rotate (length xs) (xs++ys) == ys++xs by induction on xs using Z3
    Proved prop_rotate {- rotate (length xs) xs == xs -} without induction using Z3
    Proved:
        xs++[] == xs
        (xs++ys)++zs == xs++(ys++zs)
        length (xs++ys) == length (ys++xs)
        rotate m (rotate n xs) == rotate n (rotate m xs)
        rotate (S m) (rotate n xs) == rotate (S n) (rotate m xs)
        rotate m (x:[]) == x:[]
        rotate m xs++rotate m xs == rotate m (xs++xs)
        length (rotate m xs) == length xs
        rotate (length xs) (xs++ys) == ys++xs
        prop_rotate {- rotate (length xs) xs == xs -}

The property and some lemmas conjectured by QuickSpec have been proved! Success!

## Installation instructions

HipSpec is maintained for GHC 7.4.1, 7.6.3 and 7.8.3.

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

    cabal install hipspec/ quickspec/

#### Note for Mac users using `homebrew`

The `homebrew` program sometimes messes up the package `ghc-paths`. If you get
the error that `hipspec` cannot find the `HipSpec` module, try to reinstall
this package with:

    cabal install ghc-paths --reinstall

### Supported theorem provers

We support:

* [Z3](https://z3.codeplex.com/). The default.
* [CVC4](http://cvc4.cs.nyu.edu/web/).
* [Alt Ergo](http://alt-ergo.lri.fr/), in particular versions 0.94 and 0.95.
  It exists in the
  [ubuntu repositories](https://launchpad.net/ubuntu/precise/+source/alt-ergo/0.94-1),
  and in Arch Linux' [AUR](https://aur.archlinux.org/packages/alt-ergo/).
* [vampire](http://www.vprover.org/), but your executable should be called `vampire-rel`
  (or change `src/HipSpec/ATP/Provers.hs`).
* [E](http://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html)
* [SPASS](http://www.spass-prover.org/)

See `--help` to see the flags to select theorem provers.

### Automatically Generated Signatures

HipSpec can generate a signature for you with the `--auto` flag. If you want to
see what signature it generated for you, use the `--print-auto-sig` flag.
Unfortunately, the monomorphiser is not very clever yet: say you have lists
in your program, then `(:)` will only get the type `A -> [A] -> [A]` and not
other presumably desireable instances such as `[A] -> [[A]] -> [[A]]` and
`Nat -> [Nat] -> [Nat]`.

### Theory Exploration mode

To make HipSpec print a small, pruned theory of everything that is proved
to be correct, run the compiled binary with `--explore-theory`, or `-e` for
short.

## Options and flags

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hipspec` executable.

### QuickSpec flags

  * `--call-graph` (`--cg`): Order equations according to the call graph in the
    program.
  * `--swap-repr` (`-s`): Swap equations with their representative
  * `--prepend-pruned` (`-r`): Prepend nice, pruned, equations from QuickSpec
    before attacking all equations.
  * `--quadratic` (`-q`): Add all pairs of equations from every equivalence
    class instead of picking a representative.
  * `--interesting-cands` (`-i`): Consider properties that imply newly
    found theorems.

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

### Processors and parallel proving

While theorem provers are still usually single-core, you can run many
of them in parallel. The `--processes` or `-N` flag will let you
specify this. The default is 2, but if you to use eight cores: `-N=8`.

### Timeout

The default timeout is one second. It can be specified with the `-t` or
`--timeout` flag. With `-t=5`, each theorem prover invocation will be 5 seconds
long. The timeout can be issued as a double, so `-t=0.25` can be used to get
250 ms timeout.

### Output theories

Should you wish to inspect the generated theory, you can use `--output` (or
`-o`) to make a `proving/` directory. Then all relevant files will be put
there for you to view.

## Authors and contact

The HipSpec group consists of:

  * Dan Rosén, [danr@chalmers.se](mailto:danr@chalmers.se),

  * Koen Claessen

  * Moa Johansson

  * Nicholas Smallbone

