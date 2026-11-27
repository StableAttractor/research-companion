# The Sharp 2k+2 Obstruction Bound for Minimum-Rank Completion with a Free Diagonal

Formalization for this paper (full and short versions). The Lean project is in
[`../lean/`](../lean/); every name below is in the namespace `FreeDiagonal.Results`, is stated in
`lean/FreeDiagonal/Results.lean`, and is the name printed in the paper's formalization table.
The proof is in the library file given.

## Contents

- [`paper/`](paper/): the paper, full version ([PDF](paper/minimum-rank-free-diagonal.pdf)) and short version ([PDF](paper/minimum-rank-free-diagonal-short.pdf)), with LaTeX sources.
- [`forbidden-subgraph-search/`](forbidden-subgraph-search/): the exhaustive search over graphs on at most 8 vertices reported in the paper (Section 7; Section 4 of the short version), with its logs.
- The formalization: the table below, and the Lean project in [`../lean/`](../lean/).

## Statements

| Statement in the paper | Lean name | Proof in `lean/FreeDiagonal/` |
|---|---|---|
| Facts (a), (b), (c) of Section 2 | `note_fact_a`, `note_fact_b`, `note_fact_c` | `Witness/Basic.lean` |
| Lemma 1, in the Frobenius form (take P, Q the row and column selections of A and C) | `frobenius` | `Foundations/Rank.lean` |
| Matroid union inequality used in Section 4, for any two submodular functions | `union_minmax` | `Foundations/Union.lean` |
| Theorem 1, any completion G: \|T\| ≤ rank G + j | `note_theorem_2_any_completion` | `Witness/Unconditional.lean` |
| Theorem 1, optimal completion, and \|T\| ≤ 2c | `note_theorem_2`, `note_theorem_2_two_mul` | `Witness/Unconditional.lean` |
| Section 4, first remark: every completion of x_T is matched by one of x | `note_theorem_2_construction` | `Witness/Restricted.lean` |
| Section 4, restricted diagonals: Theorem 1, the bound n ≤ 2k+2, facts (a), (b), (c) | `note_remark_restricted_witness`, `note_remark_restricted_bound`, `note_remark_restricted_fact_a`, `note_remark_restricted_fact_b`, `note_remark_restricted_fact_c` | `Witness/Restricted.lean` |
| Theorem 2: minimal obstructions, the equivalence, sharpness | `note_theorem_3_minimal`, `note_theorem_3`, `note_theorem_3_sharp` | `Witness/Unconditional.lean`, `Witness/Threshold.lean` |
| Corollary 3 | `note_corollary_4_minimal`, `note_corollary_4_threshold`, `note_corollary_4_witness`, `note_corollary_4_sharp` | `Graphs/MinRankF2.lean` |
| Section 6: c₂ in matrix form; mr ≤ c₂ ≤ mr + 1; c₂ = mr + 1 exactly when every minimum-rank completion has zero diagonal (mr ≥ 1); the odd classes coincide | `note_c2_matrix_form`, `note_mr_le_c2_le_mr_add_one`, `note_c2_eq_mr_add_one_iff`, `note_odd_classes_coincide` | `Graphs/Complementation.lean` (Lempel's facts in `Graphs/Lempel.lean`) |
| Theorem 4 (1) | `note_corollary_5`, `note_corollary_5_odd` | `Graphs/Complementation.lean` |
| Theorem 4 (2): m K₃,₃ for every m ≥ 2 | `note_remark_even_k` | `Graphs/EvenK.lean` |

Theorem 2 is proved for every k ≥ 0 (the paper states k ≥ 1). The facts from [L75] and [BPR22] used
in Section 6 are proved, not assumed. Statements quoted from the literature, such as the case k = 2
of the conjecture of [BPR22], are not formalized.

## Hypotheses and axioms

None of these theorems takes a hypothesis beyond those displayed in its statement. Each depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. To build and to print
the axioms, see [`../lean/README.md`](../lean/README.md).
