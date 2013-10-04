#!/bin/bash

FILES="test/*"
function runall {
  mkdir -p compiled
  i=0
  for f in $FILES
  do
    i=$(($i+1))
    out=`./ps2 $f > compiled/$i.asm`
    out2=`sed -i 's/jr\t$31/move\t$4, $2\n\tjr\t$31/g' compiled/$i.asm`
  done
}

runall
