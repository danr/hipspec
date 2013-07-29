#!/bin/bash

PREFIX=Lang

for i in `ls *.hs`
do
    m=$(basename $i .hs)
    sed -i "s/import $m/import $PREFIX.$m/g" *.hs
    sed -i "s/import qualified $m/import qualified $PREFIX.$m/g" *.hs
    sed -i "s/module $m/module $PREFIX.$m/g" *.hs
done

sed -i "s/import \"ghc\"/import/g" *.hs
sed -i "s/{-# LANGUAGE PackageImports #-}//" *.hs
sed -i "s/,PackageImports//" *.hs

mkdir $PREFIX
git add *.hs
git mv *.hs $PREFIX
