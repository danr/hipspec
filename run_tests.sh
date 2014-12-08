#!/bin/sh

N=$(cat /proc/cpuinfo | grep processor | wc -l)
echo "Using $N threads."
PR=../testsuite/precision-recall/PrecisionRecall.hs
COMMON="--cvc4 --alt-ergo --spass --verbosity=40  --lint-poly-fol -N$N +RTS -N4 -RTS"
COMMON_INT="--cvc4 --verbosity=40 -N$N +RTS -N4 -RTS"

cd examples

hipspec Collapse.hs --only-user-stated --success=ProvesUserStated --auto=False --plain $COMMON_INT || exit $?

hipspec Int.hs --only-user-stated --success=ProvesUserStated $COMMON_INT || exit $?
hipspec Int.hs --only= --extra-trans=plus,minus,eq,ne,lt,le,gt,ge --success=NothingUnproved --termsize=3 $COMMON_INT || exit $?

hipspec Integer.hs --only-user-stated --success=ProvesUserStated $COMMON_INT || exit $?
hipspec Integer.hs --only= --extra-trans=plus,minus,eq,ne,lt,le,gt,ge --success=NothingUnproved --termsize=3 $COMMON_INT || exit $?

hipspec Char.hs --only-user-stated --success=ProvesUserStated $COMMON_INT || exit $?
hipspec Char.hs --only= --extra-trans=eq,ne,lt,le,gt,ge --success=NothingUnproved --termsize=3 $COMMON_INT || exit $?

hipspec HOF.hs         --auto=False                         --success=NothingUnproved  $COMMON || exit $?
hipspec Properties.hs  --auto=False                         --success=NothingUnproved  $COMMON || exit $?
hipspec Nat.hs    --extra-trans=*                           --success=NothingUnproved  $COMMON || exit $?
hipspec Rotate.hs --only-user-stated                        --success=ProvesUserStated $COMMON || exit $?
hipspec List.hs        --extra-trans=++,length,map,filter,. --success=NothingUnproved  $COMMON || exit $?
hipspec Reverse.hs                  --only-user-stated      --success=ProvesUserStated $COMMON || exit $?
hipspec ZipRev.hs --auto=False      --only-user-stated      --success=ProvesUserStated $COMMON || exit $?
hipspec Concat.hs --extra-trans=+,++,length,map,sum,concat  --success=NothingUnproved  $COMMON || exit $?
hipspec BinLists.hs                                         --success=ProvesUserStated $COMMON || exit $?
# hipspec $PR                         --extra-trans=++,foldl,foldr --success=NothingUnproved  $COMMON || exit $?
# hipspec $PR                         --extra-trans=++,map,reverse --success=NothingUnproved  $COMMON || exit $?
cd ..

for i in $(ls tfp1/tests/*.hs); do
    echo $i
    hipspec --tr-mod --translate-only --lint-poly-fol $i || exit $?
done

