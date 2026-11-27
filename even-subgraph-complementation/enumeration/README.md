# Computations of Section 4

Section 4 of the paper reports exhaustive computations over F_2. This folder holds the programs and
their output. Run `./run.sh` (requirements: `gcc`, `python3` with `networkx`; about seven minutes)
to regenerate `logs/`; scratch files go to `work/`.

| Program | What it does | Result |
|---|---|---|
| `src/rank4_branch_dp.c` | Enumerates every graph whose adjacency matrix has rank 4 over F_2 on n ≤ 15 vertices, as a spanning multiset of n vectors of F_2^4, and counts the minimal forbidden graphs for c_2 ≤ 4 among them | 120, 7,560, 25,200, 15,960, 5,040 and 840 multisets for n = 7, …, 12; none for n ≤ 6 or n = 13, 14, 15; the 840 at n = 12 are all triplings (`logs/rank4_branch_dp.log`) |
| `src/enum_k4.c`, `src/orbits.py` | An independent enumeration of the same minimal forbidden multisets for n ≤ 11, and their classes up to graph isomorphism (orbits under Sp(4, 2), checked pairwise with networkx) | 1, 18, 48, 31 and 11 graphs for n = 7, …, 11; the triplings at n = 12 form 4 classes (`logs/orbits.log`) |
| `src/c2_small_graphs.c` | Computes c_2 of every labelled graph on n ≤ 7 vertices from its matrix form and counts the minimal forbidden graphs for c_2 ≤ 1, 2, 3 | for c_2 ≤ 2: none on 7 vertices, largest on 6 (`logs/c2_small_graphs.log`) |
| `src/rank4_branch_exhaustive.c` | Cross-check of the first program for n ≤ 11 by a program that keeps no table | the same counts (`logs/rank4_branch_exhaustive_summary.log`) |

In `logs/rank4_branch_dp.log`, `minimal` counts multisets giving a minimal forbidden graph,
`tripled` those that are triplings, and `minimal_not_tripled` the rest.

## Limits

- The enumeration covers the graphs with adjacency rank exactly 4 over F_2; graphs with minimum rank
  above 4 are covered by the bound 2k + 2 of the companion paper, as Section 4 says.
- It stops at 15 vertices; Theorem 1 is what excludes larger minimal forbidden graphs.
- The programs were written by an AI system (Claude, Anthropic).
