#!/bin/bash

ok=true

function run {
    echo $1
    ERROR=$($1 2>&1 > /dev/null)
    if [ -n "$ERROR" ]
    then
        echo $ERROR
        ok=false
    fi
}

for i in `ls *.hs`
do
    run "tfp1 -t $i"
    run "tfp1 -t -O $i"
done

if $ok
then
    exit 0
else
    exit -1
fi

