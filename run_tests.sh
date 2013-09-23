#!/bin/sh

PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON='--cg --verbosity=40 +RTS -N2 -RTS'

cd examples
hipspec Properties.hs                                   --success=NothingUnproved  $COMMON &&
hipspec $PR         --auto --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON &&
hipspec $PR         --auto --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON &&
hipspec Nat.hs      --auto --extra-trans=*              --success=NothingUnproved  $COMMON &&
hipspec List.hs                                         --success=NothingUnproved  $COMMON &&
hipspec Reverse.hs  --auto --only-user-stated           --success=ProvesUserStated $COMMON &&
hipspec Join.hs                                         --success=NothingUnproved  $COMMON &&
hipspec BinLists.hs --auto                              --success=NothingUnproved  $COMMON
# hipspec Rotate.hs   --auto --only-user-stated           --success=ProvesUserStated $COMMON &&
# does not work on travis

