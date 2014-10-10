#!/bin/sh

PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON='--verbosity=40  --lint-poly-fol +RTS -N2 -RTS'

cd examples
hipspec HOF.hs         --cvc4 --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec Properties.hs  --cvc4 --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec $PR            --cvc4              --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON || exit $?
hipspec $PR            --cvc4              --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON || exit $?
hipspec Nat.hs         --cvc4              --extra-trans=*              --success=NothingUnproved  $COMMON || exit $?
hipspec List.hs        --cvc4 --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec Reverse.hs     --cvc4              --only-user-stated           --success=ProvesUserStated $COMMON || exit $?
hipspec Join.hs        --cvc4 --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec BinLists.hs    --cvc4                                           --success=NothingUnproved  $COMMON || exit $?
hipspec Rotate.hs      --cvc4              --only-user-stated           --success=ProvesUserStated $COMMON || exit $?
cd ..

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

