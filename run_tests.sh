#!/bin/sh

N=$(cat /proc/cpuinfo | grep processor | wc -l)
echo "Using $N threads."
PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON="--cvc4 --alt-ergo --spass --verbosity=40  --lint-poly-fol -N$N +RTS -N4 -RTS"

cd examples
hipspec HOF.hs         --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec Properties.hs  --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec $PR                         --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON || exit $?
hipspec $PR                         --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON || exit $?
hipspec Nat.hs         -i           --extra-trans=*              --success=NothingUnproved  $COMMON || exit $?
hipspec List.hs        --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec Reverse.hs                  --only-user-stated           --success=ProvesUserStated $COMMON || exit $?
hipspec Concat.hs      --auto=False                              --success=NothingUnproved  $COMMON || exit $?
hipspec BinLists.hs                                              --success=NothingUnproved  $COMMON || exit $?
hipspec Rotate.hs                   --only-user-stated           --success=ProvesUserStated $COMMON || exit $?
cd ..

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

