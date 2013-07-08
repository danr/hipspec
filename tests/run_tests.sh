#!/bin/bash

for i in `ls *.hs`
do
    echo $i
    tfp1 -t $i > /dev/null
done
