#!/bin/bash

FILES="test/*"

function runall {
  for f in $FILES
  do
    echo "== $f =="
    NAME=${f%.*}
    SOLN=${NAME##*/}
    ANSWER=$(./ps5_mlish "$f")
    EXPECTED=$(cat soln/$SOLN.soln)
    if [ "$ANSWER" != "answer = $EXPECTED" ]; then
      echo -n -e "\e[91m[ FAILED! ] "
      tput sgr0
      echo "$SOLN: answer: $ANSWER, expected: $EXPECTED"
    else
      echo -n -e "\e[92m[ SUCCESS ] "
      tput sgr0
      echo "$SOLN: answer: $ANSWER, expected: $EXPECTED"
    fi
  done
}

runall

