#!/bin/bash

FILES="ps*.grade"
function runall {
  FILE="total.grade"
  num=0
  den=0
  # get all the grade lines from .grade files
  `grep "Part" ps*.grade | cut -d : -f 3 | cut -d ' ' -f 2 > numbers.txt`
  `cat numbers.txt | cut -d / -f 1 > top.txt`
  `cat numbers.txt | cut -d / -f 2 > bot.txt`
  # get all numerators
  while read line;
  do
    num=$(echo $num + $line | bc)
  done < top.txt

  # get all denominators
  while read line1;
  do
    den=$(echo $den + $line1 | bc)
  done < bot.txt
  # get the grades and the parts so we can track each pset
  text=`grep "Part" ps*.grade`
  # store into temp file. such noob. we will output it all at the end
  echo "" > $FILE # this overwrites the entire file, plus puts a newline...
  echo "===== GRADE REPORT =====" >> $FILE
  echo "$text" >> $FILE
  echo "" >> $FILE
  echo "TOTAL POINTS (Weighted 80%)" >> $FILE
  # output the numbers.
  echo "$num/$den" >> $FILE
  `rm numbers.txt top.txt bot.txt`
  cat $FILE
  # use bc to calculate float division, then use printf to limit precision
  printf "%.2f %%\n" $(bc -l <<< $num/$den*100)
  echo "" 
}

runall
