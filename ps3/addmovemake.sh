#!/bin/bash

FILES="test/*"
function runall {
  mkdir -p compiled
  i=0
  for f in $FILES
  do
    i=$(($i+1))
    out=`./ps3 $f > compiled/$i.asm`
    out2=`sed -i 's/j _sdej_mainepilogue/move\t$4, $2\n\tj _sdej_mainepilogue/g' compiled/$i.asm`
  done
}

runall
