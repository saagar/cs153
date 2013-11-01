#!/bin/bash

FILES="test/*"

function trim {
  local var=$@
  var="${var#"${var%%[![:space:]]*}"}"   # remove leading whitespace characters
  var="${var%"${var##*[![:space:]]}"}"   # remove trailing whitespace characters
  echo -n "$var"

}

function runall {
  for f in $FILES
  do
    NAME=${f%.*}
    SOLN=${NAME##*/}
    echo -e "\e[94m|=== $NAME ===|"
    tput sgr0
    ANSWER=$(./ps5_mlish "$f")
    EXPECTED=$(cat soln/$SOLN.soln)
    if [ "$ANSWER" != "answer = $EXPECTED" ]; then
      # test failed, check error messages
      if [ "$ANSWER" != "$EXPECTED" ]; then
      
        echo -n -e "\e[95m[ SUCCESS ] "
        tput sgr0
        echo "$SOLN: answer: $ANSWER, expected: $EXPECTED"
      else
        echo -n -e "\e[91m[ FAILED! ] "
        tput sgr0
        echo "$SOLN: answer: $ANSWER, expected: $EXPECTED"
      fi

    else
      echo -n -e "\e[92m[ SUCCESS ] "
      tput sgr0
      echo "$SOLN: answer: $ANSWER, expected: $EXPECTED"
    fi
  done
}

runall

