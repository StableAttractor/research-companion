# The Sharp Quadratic Threshold for Finiteness in Statistical Factor Analysis

Formalization for this paper. The Lean project is in [`../lean/`](../lean/); every name below is in
the namespace `FreeDiagonal.StatisticalFactorAnalysis.Paper` and is stated in
`lean/FreeDiagonal/StatisticalFactorAnalysis/Paper.lean`, named after the paper's numbering. The
paper reports no computation beyond its exact arithmetic.

## Contents

- [`paper/`](paper/): the paper ([PDF](paper/statistical-factor-analysis.pdf)), with its LaTeX source.
- The formalization: the table below, and the Lean project in [`../lean/`](../lean/).

## Statements

| Statement in the paper | Lean name |
|---|---|
| Section 1: the model F, the weak model, fits, references, test sizes | `InModel`, `InWeakModel`, `IsFit`, `IsWeakFit`, `IsReference`, `IsWeakReference`, `IsTestSize`, `IsWeakTestSize` |
| Section 1: Σ is in the model if and only if it has a fit (and the weak form) | `setting_fit`, `setting_weakFit` |
| Lemma 1, and its weak form | `lemma1`, `lemma1_weak` |
| Theorem 1 | `theorem1` |
| Theorem 2 (all four statements), and its weak form | `theorem2`, `theorem2_weak` |
| Theorem 3 (both directions) | `theorem3` |
| Theorem 4 | `theorem4` |
| Lemma 2 | `lemma2` |
| Remark after the proof of Theorem 2: the part that holds, and the example where every set is {0} | `remark_theorem2`, `remark_theorem2_last_fails` (with `hasFitIn_zero_iff`) |
| Lemma 3 | `lemma3` |
| Section 6: q(m+3−q) > 2m+2 exactly when 3 ≤ q ≤ m | `section6_ineq` |
| Section 6: ⌊(m+3)²/4⌋ − 2(m+1) = ⌊(m−1)²/4⌋ | `section6_gap` |

The formal proofs of Theorems 3 and 4 and of parts of Lemmas 2 and 3 follow shorter routes than the
printed ones, as Section 7 of the paper says.

## Hypotheses and axioms

None of these theorems takes a hypothesis beyond those displayed in its statement. Each depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. To build and to print
the axioms, see [`../lean/README.md`](../lean/README.md).
