TODO
====

  * Add type predicates/guards for finite types.

  * Follow type predicates.

  * Perform eta-expansion of properties.

  * Make a switch to ignore eta-reduced properties from QuickSpec.

  * Either enforce a default branch or add infinite domain axioms.

  * Only add necessary data types to generated theories;
    don't only restrict to tuples of size two.

  * Add function pointer axioms to the theory.

Bugs
====

  * There seems to be some bug when the theorem provers report
    CounterSatisfiable. At one occasion I think a problem got
    registered as theorem when it actually was counter-satisfiable.
    Regardless, Satisfiable is interesting information for instance
    in conjuction with `oops`.

