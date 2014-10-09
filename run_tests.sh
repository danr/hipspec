#!/bin/sh

PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON='--verbosity=40  --lint-poly-fol +RTS -N2 -RTS'

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

cd examples
hipspec HOF.hs         --cvc4 --auto=False                              --success=NothingUnproved  $COMMON &&
hipspec Properties.hs  --cvc4 --auto=False                              --success=NothingUnproved  $COMMON &&
hipspec $PR            --cvc4              --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON &&
hipspec $PR            --cvc4              --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON &&
hipspec Nat.hs         --cvc4              --extra-trans=*              --success=NothingUnproved  $COMMON &&
hipspec List.hs        --cvc4 --auto=False                              --success=NothingUnproved  $COMMON &&
hipspec Reverse.hs     --cvc4              --only-user-stated           --success=ProvesUserStated $COMMON &&
hipspec Join.hs        --cvc4 --auto=False                              --success=NothingUnproved  $COMMON &&
hipspec BinLists.hs    --cvc4                                           --success=NothingUnproved  $COMMON &&
hipspec Rotate.hs      --cvc4              --only-user-stated           --success=ProvesUserStated $COMMON

