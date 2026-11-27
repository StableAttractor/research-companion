#!/bin/bash
# Reproduces the exhaustive search reported in the paper (Section 7; Section 4 of the short version).
# Requirements: gcc, python3 with networkx. Running time: a few minutes.
set -eu
cd "$(dirname "$0")"
mkdir -p logs
gcc -O2 -o forbidden_graphs_f2 src/forbidden_graphs_f2.c

# E. All minimal forbidden induced subgraphs for mr(F_2, G) <= k, k = 1, 2, 3, among all graphs on at most 8 vertices.
./forbidden_graphs_f2 > logs/E_forbidden_graphs_f2.txt 2> logs/E_forbidden_graphs_f2.stderr.txt

# F. Graph-by-graph comparison with the published lists.
python3 src/compare_published_lists.py > logs/F_comparison_with_published_lists.txt
tail -1 logs/F_comparison_with_published_lists.txt
