#/bin/bash
a=$(~/z3/build/z3 $*)
echo $a
if [ "$a" = "sat" ]
then exit 0 
fi
exit 1
