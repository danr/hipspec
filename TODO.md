TODO
====

  * Add type predicates/guards for finite types.

  * Follow type predicates.

  * Perform eta-expansion of properties.

  * Add infinite domain axioms.

  * Besides E-proof, Vampire also print which axioms were used to
    prove a lemma. This is not supported.

  * Use `TcGblRdrEnv` to get rid of the `ANN` pragmas. SPJ wrote down
    this list of useful functions:

         Linker.getHValue :: HscEnv -> Name -> IO HValue

         Look at TcSplice.runMeta

         Convert.thRdrName

         RdrName.lookupGlobalRdrEnv
              String -->  Name
         This Name is the Name of the Id in the CoreBinds.

         Behave like ghc –c, called “OneShot” mode.



