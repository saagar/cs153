#!/bin/bash

FILES="ps*.grade"
function runall {
  FILE="total.grade"
  num=0
  den=0
  `grep "Part" ps*.grade | cut -d : -f 3 | cut -d ' ' -f 2 > numbers.txt`
  `cat numbers.txt | cut -d / -f 1 > top.txt`
  `cat numbers.txt | cut -d / -f 2 > bot.txt`
  while read line;
  do
    num=$(echo $num + $line | bc)
  done < top.txt
  #echo $num

  while read line1;
  do
    den=$(echo $den + $line1 | bc)
  done < bot.txt
  #echo $den

  text=`grep "Part" ps*.grade`
  echo "$text" > $FILE
  echo "" >> $FILE
  echo "TOTAL POINTS" >> $FILE
  echo "$num/$den" >> $FILE
  `rm numbers.txt top.txt bot.txt`
  cat $FILE
  bc -l <<< $num/$den
}

runall
