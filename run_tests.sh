#!/bin/sh

PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON='--cg --verbosity=40  --lint-poly-fol +RTS -N2 -RTS'

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

cd examples
hipspec Properties.hs                                        --success=NothingUnproved  $COMMON &&
hipspec $PR         --auto --extra-trans=++,foldl,foldr      --success=NothingUnproved  $COMMON &&
hipspec $PR         --auto --extra-trans=++,map,reverse      --success=NothingUnproved  $COMMON &&
hipspec Nat.hs      --auto --prop "\ x y -> x * y =:= y * x" --success=NothingUnproved  $COMMON &&
hipspec List.hs                                              --success=NothingUnproved  $COMMON &&
hipspec Reverse.hs  --auto --only-user-stated                --success=ProvesUserStated $COMMON &&
hipspec Join.hs                                              --success=NothingUnproved  $COMMON
