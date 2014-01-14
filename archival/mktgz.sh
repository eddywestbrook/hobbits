#!/bin/bash

DIR=`mktemp -d /tmp/build-hobbit-XXXXX`
ORIG=$PWD
(cd $DIR
mkdir -p hobbits/code/Bench
cp $ORIG/*.hs hobbits/code
cp $ORIG/bench.sh hobbits/code
cp $ORIG/Bench/*.hs hobbits/code/Bench
cp $ORIG/paper/paper.pdf hobbits/hobbits.pdf
tar cvzf hobbits.tgz hobbits
cp hobbits.tgz $ORIG)
rm -rf $DIR
