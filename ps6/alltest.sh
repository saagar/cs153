#!/bin/bash -x
mkdir testout
for f in $(ls test*.ml); do
  ./monadic $f > "testout/$f.out"
done
