#!/bin/sh

RESDIR=Bench/results2
OPTIMS=("" "-O" "-O2")

mkdir -p $RESDIR

# run -O2 version of tests
ghc -DHOBBIT --make -O2 -fno-cse -fno-full-laziness -fforce-recomp Bench/BenchNormalizer
echo running -O2 tests
./Bench/BenchNormalizer > $RESDIR/O2.txt

# run -O version of tests
ghc -DHOBBIT --make -O -fno-cse -fno-full-laziness -fforce-recomp Bench/BenchNormalizer
echo running -O tests
./Bench/BenchNormalizer > $RESDIR/O.txt

# run tests with no optimizations
ghc -DHOBBIT --make -fno-cse -fno-full-laziness -fforce-recomp Bench/BenchNormalizer
echo running tests with no optimization
./Bench/BenchNormalizer > $RESDIR/no-O.txt
