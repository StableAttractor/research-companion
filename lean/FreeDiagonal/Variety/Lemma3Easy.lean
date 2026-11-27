import FreeDiagonal.Variety.Zariski

/-!
# Lemma 3, direction "ρ(x) ≤ k implies membership"

If `ρ(x) ≤ k`, pick `D` and a completion `B` of `x_{E∖D}` with `|D| + rank B ≤ k`. For `t ≠ 0`
the matrix

  `M_t = B (extended by zero) + Σ_{i ∈ D} (e_i + t c_i)(t⁻¹ e_i + r_i)ᵀ`

has rank `≤ rank B + |D| ≤ k`, and its off-diagonal part is `x + t y` with `y = Σ_{i∈D} c_i r_iᵀ`,
for a suitable choice of the vectors `c_i, r_i`. So the line `x + t y` lies in `{c ≤ k}` for
every `t ≠ 0`, and over an infinite field `x` lies in the Zariski closure.

* General patterns: `r_i` = row `i` of `x`, `c_i` = column `i` of `x` with the entries in `D`
  set to zero.
* Symmetric patterns (`n` linearly ordered): `c_i = r_i` = row `i` of `x` with the entries at
  `i` and at the elements of `D` below `i` set to zero; then `M_t` is symmetric.
-/

open Matrix Finset

namespace FreeDiagonal

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

variable (K) in
/-- The `n × T` matrix of the inclusion `T ⊆ n`. -/
def incMat (T : Finset n) : Matrix n T K := fun a j => if (j : n) = a then 1 else 0

lemma sum_incl (T : Finset n) (a : n) (f : T → K) :
    ∑ j : T, (if (j : n) = a then f j else 0) = if h : a ∈ T then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro j _ hj
      rw [if_neg]; intro e; exact hj (Subtype.ext e)
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]; intro e; exact h (e ▸ j.2)

lemma incMat_mul_apply {m : Type*} (T : Finset n) (N : Matrix T m K) (a : n) (b : m) :
    (incMat K T * N) a b = if h : a ∈ T then N ⟨a, h⟩ b else 0 := by
  rw [Matrix.mul_apply, ← sum_incl T a (fun j => N j b)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [incMat]; split_ifs <;> simp

lemma mul_incMat_transpose_apply {m : Type*} (T : Finset n) (N : Matrix m T K) (a : m) (b : n) :
    (N * (incMat K T)ᵀ) a b = if h : b ∈ T then N a ⟨b, h⟩ else 0 := by
  rw [Matrix.mul_apply, ← sum_incl T b (fun j => N a j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [incMat, transpose_apply]; split_ifs <;> simp

/-- **The matrix on the line.** Given `D`, a completion `B = x_{Dᶜ} + diag g` of the sub-pattern
on `Dᶜ`, and matrices `C : n × D`, `R : D × n` that split the off-diagonal entries of `x` as in
`hcomb`, for every `t ≠ 0` there is a matrix of rank `≤ rank B + |D|` whose off-diagonal entries
are `x + t (C R)`. -/
theorem exists_line_matrix (x : Matrix n n K) (D : Finset n) (g : (Dᶜ : Finset n) → K)
    (C : Matrix n D K) (R : Matrix D n K)
    (hcomb : ∀ a b, a ≠ b → x a b = (if a ∈ Dᶜ ∧ b ∈ Dᶜ then x a b else 0)
      + (if h : a ∈ D then R ⟨a, h⟩ b else 0) + (if h : b ∈ D then C a ⟨b, h⟩ else 0))
    (t : K) (ht : t ≠ 0) :
    ∃ M : Matrix n n K, M.rank ≤ (subPattern x Dᶜ + diagonal g).rank + D.card ∧
      ∀ a b, a ≠ b → M a b = x a b + t * (C * R) a b := by
  set B := subPattern x Dᶜ + diagonal g
  refine ⟨incMat K Dᶜ * B * (incMat K Dᶜ)ᵀ + (incMat K D + t • C) * (t⁻¹ • (incMat K D)ᵀ + R), ?_, ?_⟩
  · refine (rank_add_le' _ _).trans (Nat.add_le_add ?_ ?_)
    · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    · refine (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans ?_)
      simp
  · intro a b hab
    have e : (incMat K D + t • C) * (t⁻¹ • (incMat K D)ᵀ + R)
        = t⁻¹ • (incMat K D * (incMat K D)ᵀ) + incMat K D * R + C * (incMat K D)ᵀ + t • (C * R) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        mul_inv_cancel₀ ht, inv_mul_cancel₀ ht, one_smul]
      abel
    have hB : (incMat K Dᶜ * B * (incMat K Dᶜ)ᵀ) a b = if a ∈ Dᶜ ∧ b ∈ Dᶜ then x a b else 0 := by
      rw [mul_incMat_transpose_apply]
      by_cases hb : b ∈ Dᶜ
      · rw [dif_pos hb, incMat_mul_apply]
        by_cases ha : a ∈ Dᶜ
        · rw [dif_pos ha, if_pos ⟨ha, hb⟩]
          simp [B, subPattern, diagonal, hab]
        · rw [dif_neg ha, if_neg (fun h => ha h.1)]
      · rw [dif_neg hb, if_neg (fun h => hb h.2)]
    have hE : (incMat K D * (incMat K D)ᵀ) a b = 0 := by
      rw [mul_incMat_transpose_apply]
      split_ifs <;> simp [incMat, Ne.symm hab]
    rw [Matrix.add_apply, e, hB]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hE, mul_zero, zero_add,
      incMat_mul_apply, mul_incMat_transpose_apply]
    linear_combination -(hcomb a b hab)

/-- The off-diagonal coordinates of a matrix. -/
def offCoords (N : Matrix n n K) : OffIdx n → K := fun p => N p.1.1 p.1.2

lemma minCompRank_le_of_offDiag (x M : Matrix n n K) (hx : ∀ a, x a a = 0)
    (hM : ∀ a b, a ≠ b → M a b = x a b) : minCompRank x ≤ M.rank := by
  have : M = x + diagonal (fun a => M a a) := by
    ext a b
    by_cases h : a = b
    · subst h; simp [hx]
    · simp [diagonal, h, hM a b h]
  rw [this]; exact minCompRank_le _ _

/-- **Lemma 3, easy direction, general patterns.** Over an infinite field, a pattern with
`ρ(x) ≤ k` lies in `D_{n,k}`, the Zariski closure of `{x : c(x) ≤ k}`. -/
theorem mem_Dvar_of_closRank_le [Infinite K] (k : ℕ) (p : OffIdx n → K)
    (h : closRank (toMat p) ≤ k) : p ∈ Dvar n k := by
  set x := toMat p
  obtain ⟨D, hD⟩ := exists_closRank x
  obtain ⟨g, hg⟩ := exists_minCompRank (subPattern x Dᶜ)
  let C : Matrix n D K := fun a i => if a ∈ D then 0 else x a i
  let R : Matrix D n K := fun i b => x i b
  have hcomb : ∀ a b, a ≠ b → x a b = (if a ∈ Dᶜ ∧ b ∈ Dᶜ then x a b else 0)
      + (if h : a ∈ D then R ⟨a, h⟩ b else 0) + (if h : b ∈ D then C a ⟨b, h⟩ else 0) := by
    intro a b _
    by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;> simp [ha, hb, C, R]
  refine mem_zariskiClosure_of_line _ p (offCoords (C * R)) (fun t ht => ?_)
  obtain ⟨M, hMr, hM⟩ := exists_line_matrix x D g C R hcomb t ht
  show minCompRank (toMat (p + t • offCoords (C * R))) ≤ k
  refine (minCompRank_le_of_offDiag _ M (toMat_apply_self _) (fun a b hab => ?_)).trans ?_
  · rw [hM a b hab, toMat_apply_ne _ hab]
    simp [x, toMat_apply_ne _ hab, offCoords]
  · rw [hg] at hMr; omega

/-! ### Symmetric patterns -/

section Symmetric

variable {m : Type*} [Fintype m] [LinearOrder m]

lemma toMatSym_apply_lt (p : SymIdx m → K) {i j : m} (h : i < j) :
    toMatSym p i j = p ⟨(i, j), h⟩ := by
  simp [toMatSym, h]

lemma toMatSym_apply_gt (p : SymIdx m → K) {i j : m} (h : j < i) :
    toMatSym p i j = p ⟨(j, i), h⟩ := by
  simp [toMatSym, h, not_lt_of_gt h]

/-- **Lemma 3, easy direction, symmetric patterns.** Over an infinite field, a symmetric pattern
with `ρ(x) ≤ k` lies in `X_{n,k}`, the Zariski closure (in the space of symmetric patterns) of the
symmetric patterns with `c(x) ≤ k`. -/
theorem mem_Xvar_of_closRank_le [Infinite K] (k : ℕ) (p : SymIdx m → K)
    (h : closRank (toMatSym p) ≤ k) : p ∈ Xvar m k := by
  set x := toMatSym p
  obtain ⟨D, hD⟩ := exists_closRank x
  obtain ⟨g, hg⟩ := exists_minCompRank (subPattern x Dᶜ)
  let C : Matrix m D K := fun a i => if a ∈ D ∧ a ≤ (i : m) then 0 else x a i
  let R : Matrix D m K := fun i b => if b ∈ D ∧ b ≤ (i : m) then 0 else x i b
  have hRC : ∀ i b, R i b = C b i := by
    intro i b; simp only [R, C, x, toMatSym_symm p (i : m) b]
  have hCR : ∀ a b, (C * R) a b = (C * R) b a := by
    intro a b
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hRC, hRC]; ring
  have hcomb : ∀ a b, a ≠ b → x a b = (if a ∈ Dᶜ ∧ b ∈ Dᶜ then x a b else 0)
      + (if h : a ∈ D then R ⟨a, h⟩ b else 0) + (if h : b ∈ D then C a ⟨b, h⟩ else 0) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with hlt | hlt <;>
      by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;>
      simp [ha, hb, C, R, hlt.le, not_le.mpr hlt]
  refine mem_zariskiClosure_of_line _ p (fun q => (C * R) q.1.1 q.1.2) (fun t ht => ?_)
  obtain ⟨M, hMr, hM⟩ := exists_line_matrix x D g C R hcomb t ht
  show minCompRank (toMatSym (p + t • fun q : SymIdx m => (C * R) q.1.1 q.1.2)) ≤ k
  refine (minCompRank_le_of_offDiag _ M (toMatSym_apply_self _) (fun a b hab => ?_)).trans ?_
  · rw [hM a b hab]
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · rw [toMatSym_apply_lt _ hlt]; simp [x, toMatSym_apply_lt _ hlt]
    · rw [toMatSym_apply_gt _ hlt]; simp [x, toMatSym_apply_gt _ hlt, hCR a b]
  · rw [hg] at hMr; omega

/-! ### `X_{3,1}` is the whole space -/

lemma closRank_le_card_of_zero {N : Type*} [Fintype N] [DecidableEq N] (x : Matrix N N K)
    (D : Finset N) (h : ∀ i ∈ Dᶜ, ∀ j ∈ Dᶜ, x i j = 0) : closRank x ≤ D.card := by
  have h0 : subPattern x Dᶜ = 0 := by
    ext i j; exact h i i.2 j j.2
  have := closRank_le x D
  have h1 : minCompRank (subPattern x Dᶜ) ≤ 0 := by
    have := minCompRank_le (subPattern x Dᶜ) 0
    simpa [h0] using this
  omega

/-- Every symmetric pattern on three indices has `ρ ≤ 1`. -/
theorem closRank_le_one_fin3 (p : SymIdx (Fin 3) → K) : closRank (toMatSym p) ≤ 1 := by
  obtain ⟨a, ea⟩ : ∃ a, p ⟨(0, 1), by decide⟩ = a := ⟨_, rfl⟩
  obtain ⟨b, eb⟩ : ∃ b, p ⟨(0, 2), by decide⟩ = b := ⟨_, rfl⟩
  obtain ⟨c, ec⟩ : ∃ c, p ⟨(1, 2), by decide⟩ = c := ⟨_, rfl⟩
  by_cases ha : a = 0
  · refine closRank_le_card_of_zero _ {2} (fun i hi j hj => ?_)
    simp only [mem_compl, mem_singleton] at hi hj
    fin_cases i <;> fin_cases j <;> simp_all [toMatSym]
  by_cases hb : b = 0
  · refine closRank_le_card_of_zero _ {1} (fun i hi j hj => ?_)
    simp only [mem_compl, mem_singleton] at hi hj
    fin_cases i <;> fin_cases j <;> simp_all [toMatSym]
  by_cases hc : c = 0
  · refine closRank_le_card_of_zero _ {0} (fun i hi j hj => ?_)
    simp only [mem_compl, mem_singleton] at hi hj
    fin_cases i <;> fin_cases j <;> simp_all [toMatSym]
  -- all three entries are nonzero: a rank-one completion
  refine (closRank_le_minCompRank _).trans ?_
  set l := a * b / c
  set v : Fin 3 → K := ![1, c / b, c / a]
  have hM : toMatSym p + diagonal (fun i => l * v i * v i) = vecMulVec (l • v) v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatSym, vecMulVec, diagonal, l, v, ea, eb, ec] <;>
      field_simp
  refine (minCompRank_le _ (fun i => l * v i * v i)).trans ?_
  rw [hM]; exact rank_vecMulVec_le _ _

/-- **`X_{3,1}` is the whole space** (infinite field). -/
theorem Xvar_fin3_one [Infinite K] : Xvar (K := K) (Fin 3) 1 = Set.univ :=
  Set.eq_univ_of_forall (fun p => mem_Xvar_of_closRank_le 1 p (closRank_le_one_fin3 p))

end Symmetric

end FreeDiagonal
