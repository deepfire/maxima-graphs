#!/bin/sh

for f in *.lisp
do
    sed -i 's/$//' $f
    sed -i 's/_/-/' $f
done
