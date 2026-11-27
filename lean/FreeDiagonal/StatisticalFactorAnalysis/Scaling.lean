import FreeDiagonal.StatisticalFactorAnalysis.TestSize

/-!
# Schur complements as minima, invertibility from the other hypotheses of Lemma 3, and
invariance of the model under rescaling of the variables
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section Schur

variable {q : ℕ}

/-- `xᵀ S x = x_j² s_j + 2 x_j (r_j ⬝ y) + yᵀ S[-j] y`, `y` the restriction of `x`. -/
lemma quad_split (S : Matrix (Fin q) (Fin q) ℝ) (hS : S.IsSymm) (j : Fin q) (x : Fin q → ℝ) :
    x ⬝ᵥ (S *ᵥ x) = x j ^ 2 * S j j + 2 * x j * (offRow S j ⬝ᵥ (fun k : {k // k ≠ j} => x k)) +
      (fun k : {k // k ≠ j} => x k) ⬝ᵥ (offPrinc S j *ᵥ fun k : {k // k ≠ j} => x k) := by
  have hs : ∀ k, S k j = S j k := fun k => symm_apply hS k j
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have e1 : ∀ k, ∑ l, S k l * x l = S k j * x j + ∑ l : {l // l ≠ j}, S k l * x l :=
    fun k => Fintype.sum_eq_add_sum_subtype_ne _ j
  simp_rw [e1]
  simp only [offRow, offPrinc, submatrix_apply, mul_add, Finset.sum_add_distrib]
  have e2 : ∑ k : {k // k ≠ j}, x k * (S k j * x j) = x j * ∑ k : {k // k ≠ j}, S j k * x k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hs]; ring
  rw [e2]; ring

/-- `-g_j` is the least value of `xᵀ S x` over `x` with `x_j = 1` (attained). -/
lemma schur_min (S : Matrix (Fin q) (Fin q) ℝ) (hS : S.IsSymm) (j : Fin q)
    (hP : (offPrinc S j).PosDef) :
    (∀ x : Fin q → ℝ, x j = 1 → -schurG S j ≤ x ⬝ᵥ (S *ᵥ x)) ∧
      ∃ x : Fin q → ℝ, x j = 1 ∧ x ⬝ᵥ (S *ᵥ x) = -schurG S j := by
  classical
  set Sj := offPrinc S j
  set r := offRow S j
  set c := Sj⁻¹ *ᵥ r with hc
  have hSc : Sj *ᵥ c = r := by
    rw [hc, mulVec_mulVec, mul_nonsing_inv _ ((hP.isUnit).map Matrix.detMonoidHom), one_mulVec]
  have hSjs : Sj.IsSymm := by
    ext a b; exact symm_apply hS b a
  have hcSy : ∀ y, c ⬝ᵥ (Sj *ᵥ y) = r ⬝ᵥ y := by
    intro y
    rw [dotProduct_mulVec, ← mulVec_transpose, hSjs.eq, hSc]
  have hySc : ∀ y, y ⬝ᵥ (Sj *ᵥ c) = r ⬝ᵥ y := by
    intro y; rw [hSc, dotProduct_comm]
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [quad_split S hS j x, hx]
    set y := fun k : {k // k ≠ j} => x k
    have h0 := hP.posSemidef.dotProduct_mulVec_nonneg (y + c)
    simp only [star_trivial] at h0
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add] at h0
    have k1 : y ⬝ᵥ (Sj *ᵥ c) = r ⬝ᵥ y := hySc y
    have k2 : c ⬝ᵥ (Sj *ᵥ y) = r ⬝ᵥ y := hcSy y
    have k3 : c ⬝ᵥ (Sj *ᵥ c) = r ⬝ᵥ c := hcSy c
    rw [k1, k2, k3] at h0
    have : -schurG S j = S j j - r ⬝ᵥ c := by rw [schurG]; ring
    rw [this]
    simp only [one_pow, one_mul, mul_one]
    change S j j - r ⬝ᵥ c ≤ S j j + 2 * (r ⬝ᵥ y) + y ⬝ᵥ (Sj *ᵥ y)
    linarith
  · refine ⟨fun k => if h : k = j then 1 else -c ⟨k, h⟩, by simp, ?_⟩
    rw [quad_split S hS j]
    have hy : (fun k : {k // k ≠ j} => (fun k => if h : k = j then (1 : ℝ) else -c ⟨k, h⟩) k.1)
        = -c := by
      funext k; simp [k.2]
    simp only [dite_true]
    have k3 : c ⬝ᵥ (offPrinc S j *ᵥ c) = offRow S j ⬝ᵥ c := hcSy c
    rw [hy, mulVec_neg, neg_dotProduct, dotProduct_neg, dotProduct_neg, neg_neg, k3, schurG]
    ring

/-- A real symmetric matrix that is not positive semidefinite and has a positive definite
principal submatrix of size `q - 1` is invertible: the hypothesis "invertible" of Lemma 3
follows from its other hypotheses. -/
lemma det_ne_zero_of_princ (S : Matrix (Fin q) (Fin q) ℝ) (hS : S.IsSymm) (j : Fin q)
    (hP : (offPrinc S j).PosDef) (hn : ¬ S.PosSemidef) : S.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  apply hn
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hS
  · simp only [star_trivial]
    -- `v_j ≠ 0`
    have hvj : v j ≠ 0 := by
      intro hj
      have hq := quad_split S hS j v
      rw [hv, dotProduct_zero, hj] at hq
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
        zero_add] at hq
      have hy0 : (fun k : {k // k ≠ j} => v k) ≠ 0 := by
        intro h0; apply hv0; funext k
        by_cases hk : k = j
        · rw [hk, hj]; rfl
        · exact congrFun h0 ⟨k, hk⟩
      have := hP.dotProduct_mulVec_pos hy0
      simp only [star_trivial] at this
      linarith
    set y := x - (x j / v j) • v
    have hyj : y j = 0 := by simp [y, hvj]
    have e : x ⬝ᵥ (S *ᵥ x) = y ⬝ᵥ (S *ᵥ y) := by
      have hx : x = y + (x j / v j) • v := by simp [y]
      have hvSy : v ⬝ᵥ (S *ᵥ y) = 0 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, hv, zero_dotProduct]
      rw [hx, mulVec_add, mulVec_smul, hv, smul_zero, add_zero, add_dotProduct, smul_dotProduct,
        hvSy, smul_zero, add_zero]
    rw [e, quad_split S hS j y, hyj]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      zero_add]
    exact hP.posSemidef.dotProduct_mulVec_nonneg _

end Schur

section Scaling

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Rescaling the variables.** For `p_i ≠ 0`, `Σ ∈ F` iff `(p_i Σ_il p_l) ∈ F`. -/
lemma InModel.scale {m : ℕ} {Sig : Matrix n n ℝ} (h : InModel m Sig) (p : n → ℝ)
    (hp : ∀ i, p i ≠ 0) : InModel m (diagonal p * Sig * diagonal p) := by
  rw [inModel_iff_exists_fit] at h ⊢
  obtain ⟨G, hG, hr, ho, hd⟩ := h
  refine ⟨diagonal p * G * diagonal p, ?_, ?_, ?_, ?_⟩
  · have := hG.mul_mul_conjTranspose_same (diagonal p)
    rwa [conjTranspose_eq_transpose_of_trivial, diagonal_transpose] at this
  · exact (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans hr)
  · intro i l hil; simp only [diagonal_mul, mul_diagonal]; rw [ho i l hil]
  · intro i
    simp only [diagonal_mul, mul_diagonal]
    have := mul_lt_mul_of_pos_left (hd i) (mul_self_pos.2 (hp i))
    nlinarith [this]

lemma InWeakModel.scale {m : ℕ} {Sig : Matrix n n ℝ} (h : InWeakModel m Sig) (p : n → ℝ) :
    InWeakModel m (diagonal p * Sig * diagonal p) := by
  rw [inWeakModel_iff_exists_weakFit] at h ⊢
  obtain ⟨G, hG, hr, ho, hd⟩ := h
  refine ⟨diagonal p * G * diagonal p, ?_, ?_, ?_, ?_⟩
  · have := hG.mul_mul_conjTranspose_same (diagonal p)
    rwa [conjTranspose_eq_transpose_of_trivial, diagonal_transpose] at this
  · exact (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans hr)
  · intro i l hil; simp only [diagonal_mul, mul_diagonal]; rw [ho i l hil]
  · intro i
    simp only [diagonal_mul, mul_diagonal]
    have := mul_le_mul_of_nonneg_left (hd i) (mul_self_nonneg (p i))
    nlinarith [this]

lemma inModel_scale_iff {m : ℕ} (Sig : Matrix n n ℝ) (p : n → ℝ) (hp : ∀ i, p i ≠ 0) :
    InModel m (diagonal p * Sig * diagonal p) ↔ InModel m Sig := by
  refine ⟨fun h => ?_, fun h => h.scale p hp⟩
  have := h.scale (fun i => (p i)⁻¹) (fun i => inv_ne_zero (hp i))
  have e : diagonal (fun i => (p i)⁻¹) * (diagonal p * Sig * diagonal p) *
      diagonal (fun i => (p i)⁻¹) = Sig := by
    ext i l; simp only [diagonal_mul, mul_diagonal]; field_simp [hp i, hp l]
  rwa [e] at this

lemma inWeakModel_scale_iff {m : ℕ} (Sig : Matrix n n ℝ) (p : n → ℝ) (hp : ∀ i, p i ≠ 0) :
    InWeakModel m (diagonal p * Sig * diagonal p) ↔ InWeakModel m Sig := by
  refine ⟨fun h => ?_, fun h => h.scale p⟩
  have := h.scale (fun i => (p i)⁻¹)
  have e : diagonal (fun i => (p i)⁻¹) * (diagonal p * Sig * diagonal p) *
      diagonal (fun i => (p i)⁻¹) = Sig := by
    ext i l; simp only [diagonal_mul, mul_diagonal]; field_simp [hp i, hp l]
  rwa [e] at this

lemma subPattern_scale (Sig : Matrix n n ℝ) (p : n → ℝ) (T : Finset n) :
    subPattern (diagonal p * Sig * diagonal p) T =
      diagonal (fun a : T => p a) * subPattern Sig T * diagonal (fun a : T => p a) := by
  ext a b; simp [subPattern, diagonal_mul, mul_diagonal]

end Scaling

end FreeDiagonal.StatisticalFactorAnalysis
