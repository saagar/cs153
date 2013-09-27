#!/bin/bash

FILES="test/*"
function runall {
  i=0
  for f in $FILES
  do
    i=$(($i+1))
    out=`./ps1yacc $f`
    a=( $out )
    if [[ ${a[0]} = "Fatal" ]]; then
      echo "boom"
    else
      ans=`head -$i solutions | tail -1`
      if [[ $ans = ${a[2]} ]]; then
        echo Test $i passed! answer: ${a[2]}, expected: $ans
      else
        echo FAILED: test $i answer: ${a[2]}, expected: $ans
      fi
    fi
  done
}

runall
