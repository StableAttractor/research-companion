# Exhaustive search for minimal forbidden subgraphs over F_2

Section 4 of the paper states that an exhaustive search over all graphs on at most 8 vertices
reproduces the published lists of minimal forbidden induced subgraphs for mr(F_2, G) <= k,
k = 2 and 3. This folder holds that search. Everything is exact computation over F_2.

Run `./run.sh` (requirements: `gcc`, `python3` with `networkx`; a few minutes). It regenerates the
files in `logs/`, which are included as produced by the run of 22 November 2026.

| Step | Program | What it does | Result |
|---|---|---|---|
| E | `src/forbidden_graphs_f2.c` | Lists every minimal forbidden induced subgraph for mr(F_2, G) <= k, k = 1, 2, 3, among ALL graphs on at most 8 vertices | 2, 7 and 62 graphs; largest on 4, 6 and 8 vertices |
| F | `src/compare_published_lists.py` | Compares E with the published lists graph by graph, by isomorphism testing, and recomputes independently the minimum rank of every published graph and of its vertex-deleted subgraphs | k = 1: 2 of 2; k = 2: 7 of 7 (Barrett, van der Holst, Loewy 2005, Theorem 16); k = 3: 62 of 62 (Barrett, Grout, Loewy 2009, Theorem 49). Lists identical |

`data/BGL_2009_Theorem49_graph6.txt` holds the 62 graph6 codes of Barrett, Grout and Loewy,
extracted from the source of arXiv:math/0612331v3.

## Limits

- The search is exhaustive only up to 8 vertices. It confirms the bound 2k + 2 of Corollary 3 for
  k <= 3 among graphs on at most 8 vertices; that no minimal forbidden subgraph has 9 or more
  vertices is Theorem 48 of Barrett, Grout and Loewy for k = 3, and Corollary 3 of the paper in
  general.
- `forbidden_graphs_f2.c` also contains code for a second invariant, which the paper does not use.
- The programs were written by the same AI system that produced the proofs.
