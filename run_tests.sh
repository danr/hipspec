#!/bin/sh

PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON='--cg --verbosity=40  --lint-poly-fol +RTS -N2 -RTS'

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

cd examples
hipspec HOF.hs         --mono-alt-ergo                                     --success=NothingUnproved  $COMMON &&
hipspec Properties.hs  --mono-alt-ergo                                     --success=NothingUnproved  $COMMON &&
hipspec $PR            --mono-alt-ergo --auto --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON &&
hipspec $PR            --mono-alt-ergo --auto --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON &&
hipspec Nat.hs         --mono-alt-ergo --auto --extra-trans=*              --success=NothingUnproved  $COMMON &&
hipspec List.hs        --mono-alt-ergo                                     --success=NothingUnproved  $COMMON &&
hipspec Reverse.hs     --mono-alt-ergo --auto --only-user-stated           --success=ProvesUserStated $COMMON &&
hipspec Join.hs        --mono-alt-ergo                                     --success=NothingUnproved  $COMMON
# hipspec BinLists.hs --auto                              --success=NothingUnproved  $COMMON &&
# hipspec Rotate.hs   --auto --only-user-stated           --success=ProvesUserStated $COMMON &&
# these do not work on travis

