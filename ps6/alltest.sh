#!/bin/bash -x
for f in $(ls test*.ml); do
  ./monadic $f > "$f.out"
done
