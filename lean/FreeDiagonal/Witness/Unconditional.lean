import FreeDiagonal.Foundations.Union
import FreeDiagonal.Witness.Threshold

/-!
# Theorems 2 and 3, unconditional

The Stage A theorems with the hypothesis `UnionRankFormula F` discharged by `unionRankFormula`
(Stage B). Nothing is assumed.
-/

open Matrix Finset

universe u v

namespace FreeDiagonal

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- **Theorem 2, any completion** (first remark of Section 4; Part 51-b). -/
theorem thm2_any_completion (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) (d0 : n → F) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRank (subPattern x T) = minCompRank x :=
  witness_of_completion (unionRankFormula F) x j hcut d0

/-- **Theorem 2 (witness theorem).** -/
theorem thm2_witness (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ minCompRank x + j ∧
      minCompRank (subPattern x T) = minCompRank x :=
  witness (unionRankFormula F) x j hcut

/-- **Theorem 2, "in particular `|T| ≤ 2c`".** -/
theorem thm2_two_mul (x : Matrix n n F) :
    ∃ T : Finset n, T.card ≤ 2 * minCompRank x ∧
      minCompRank (subPattern x T) = minCompRank x :=
  witness_two_mul (unionRankFormula F) x

/-- **Theorem 3, minimal obstructions have at most `2k + 2` indices.** -/
theorem thm3_minimal (k : ℕ) (x : Matrix n n F) (hk : k + 1 ≤ minCompRank x)
    (hmin : ∀ T : Finset n, T ≠ univ → minCompRank (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 :=
  card_le_of_minimal (unionRankFormula F) k x hk hmin

/-- **Theorem 3, the threshold equivalence.** -/
theorem thm3_threshold (k : ℕ) (x : Matrix n n F) :
    minCompRank x ≤ k ↔
      ∀ T : Finset n, T.card ≤ 2 * k + 2 → minCompRank (subPattern x T) ≤ k :=
  threshold (unionRankFormula F) k x

end FreeDiagonal
