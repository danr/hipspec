TODO
====

  * Add type predicates/guards for finite types.

  * Follow type predicates.

  * Perform eta-expansion of properties.

  * Make a switch to ignore eta-reduced properties from QuickSpec.

  * Either enforce a default branch or add infinite domain axioms.

  * Print which axioms were used to prove a lemma.
    E-proof and other provers supports the TSTP format.

Bugs
====

  * There seems to be some bug when the theorem provers report
    CounterSatisfiable. At one occasion I think a problem got
    registered as theorem when it actually was counter-satisfiable.
    Regardless, Satisfiable is interesting information for instance
    in conjuction with `oops`.

