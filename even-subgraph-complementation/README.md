# The Sharp 3k Obstruction Bound for Subgraph Complementation at Even k

Formalization and computation for this paper. The Lean project is in [`../lean/`](../lean/); every
name below is in the namespace `FreeDiagonal.EvenComplementation.Paper` and is stated in
`lean/FreeDiagonal/EvenComplementation/Paper.lean`, named after the paper's numbering.

## Contents

- [`paper/`](paper/): the paper ([PDF](paper/even-subgraph-complementation.pdf)), with its LaTeX source.
- [`enumeration/`](enumeration/): the computations of Section 4, with their logs.
- The formalization: the table below, and the Lean project in [`../lean/`](../lean/).

## Statements

| Statement in the paper | Lean name |
|---|---|
| Fact (a): c₂ is the least f(M) over completions M | `fact_a` |
| Fact (b): c₂ does not increase on induced subgraphs | `fact_b` |
| Fact (c): a symmetric matrix over F₂ with zero diagonal has even rank | `fact_c` |
| Fact (d): the bound 2k + 2 for minimum rank over F₂ | `fact_d` |
| k-rigid (definition) | `IsRigid` |
| Lemma 1 | `lemma1` |
| Lemma 2 (rank formula), over any field; for any factorisation A = USUᵀ | `lemma2`, `lemma2_of_factor` |
| Remark after Lemma 2 | `lemma2_remark` |
| Lemma 3 (witness), over any field: the construction as printed, and the existence form | `lemma3`, `lemma3_exists` |
| Theorem 1 | `theorem1` |
| Theorem 2 | `theorem2` |
| Corollary 3, odd and even k | `corollary3` |

Triplings are taken up to graph isomorphism. The rank of a bilinear form restricted to a subspace is
`formRankOn`, shown equal to the rank of its Gram matrix in any basis (`formRankOn_eq_rank_gram`).
The formal proofs of Theorem 1 and of the rigidity part of Lemma 3 follow a different route from the
printed ones, as Section 6 of the paper says.

## Hypotheses and axioms

None of these theorems takes a hypothesis beyond those displayed in its statement. Each depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. To build and to print
the axioms, see [`../lean/README.md`](../lean/README.md).
