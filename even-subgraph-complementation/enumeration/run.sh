#!/bin/bash
# Reproduces the computations of Section 4 of the paper. Requirements: gcc, python3 with networkx.
# About seven minutes.
set -eu
cd "$(dirname "$0")"
mkdir -p logs work
gcc -O2 -o work/rank4_branch_dp src/rank4_branch_dp.c
gcc -O2 -o work/c2_small_graphs src/c2_small_graphs.c
gcc -O2 -DPRINT -DFAST -o work/enum_k4 src/enum_k4.c

# All graphs with adjacency rank 4 over F_2 on at most 15 vertices: minimal forbidden graphs for c_2 <= 4.
./work/rank4_branch_dp 15 | grep '^n=' > logs/rank4_branch_dp.log

# All graphs on at most 7 vertices: minimal forbidden graphs for c_2 <= 1, 2, 3.
./work/c2_small_graphs | grep '^n=' > logs/c2_small_graphs.log

# Isomorphism classes for n = 7, ..., 11 (orbits under Sp(4, 2)) and for the triplings at n = 12.
for n in 7 8 9 10 11; do ./work/enum_k4 $n | grep -v '^n=' > work/min_n$n.txt; done
( cd work && python3 ../src/orbits.py ) > logs/orbits.log

# Optional cross-check of the first program for n <= 11 by a second program that keeps no table:
#   gcc -O2 -o work/rank4_branch_exhaustive src/rank4_branch_exhaustive.c
#   for n in 4 5 6 7 8 9 10 11; do ./work/rank4_branch_exhaustive $n 4 | grep '^n='; done
