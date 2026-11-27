import FreeDiagonal.StatisticalFactorAnalysis.Gram

/-! # Matrix helpers for the factor analysis proofs -/

open Matrix Module Submodule

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

section Rank

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma rank_add_le' (A B : Matrix n n ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [mulVecLin_add]
  calc finrank ℝ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank ℝ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A cross Gram matrix `(⟪v_i, w_j⟫)` has rank at most the dimension of the space. -/
lemma rank_cross_le {ι : Type*} [Fintype ι] (v w : ι → E) :
    (Matrix.of fun i j => inner ℝ (v i) (w j)).rank ≤ finrank ℝ E := by
  set L1 : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ w
  set L2 : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i => innerₗ E (v i)
  have e : (Matrix.of fun i j => inner ℝ (v i) (w j)).mulVecLin = L2 ∘ₗ L1 := by
    ext c i
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, Function.comp_apply, L1, L2,
      LinearMap.pi_apply, innerₗ_apply_apply, Fintype.linearCombination_apply, inner_sum,
      real_inner_smul_right, mulVec, dotProduct, of_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold Matrix.rank
  rw [e, LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_le (LinearMap.range L1))

/-- The bilinear form `(α, β) ↦ (Mᵀ α) ⬝ β`, i.e. `α ⬝ M β`, as a map into the dual. -/
noncomputable def formOf {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ :=
  (Matrix.toLinearMap₂' ℝ (1 : Matrix ι ι ℝ)) ∘ₗ (Mᵀ).mulVecLin

lemma formOf_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (α β : ι → ℝ) :
    formOf M α β = α ⬝ᵥ (M *ᵥ β) := by
  simp only [formOf, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
    Matrix.toLinearMap₂'_apply', Matrix.one_mulVec]
  rw [mulVec_transpose, ← dotProduct_mulVec]

lemma finrank_range_formOf {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    finrank ℝ (LinearMap.range (formOf M)) = M.rank := by
  have hinj : Function.Injective
      (Matrix.toLinearMap₂' ℝ (1 : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ) := by
    intro u u' h
    funext i
    have := congrArg (fun f : (ι → ℝ) →ₗ[ℝ] ℝ => f (Pi.single i 1)) h
    simpa only [Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, dotProduct_single, mul_one]
      using this
  rw [formOf, LinearMap.range_comp]
  rw [(Submodule.equivMapOfInjective _ hinj _).symm.finrank_eq]
  rw [← Matrix.rank, Matrix.rank_transpose]

/-- A symmetric real matrix with non-negative quadratic form is positive semidefinite. -/
lemma posSemidef_of_form {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} (hM : M.IsSymm)
    (h : ∀ α, 0 ≤ α ⬝ᵥ (M *ᵥ α)) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => by simpa using h x)
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hM

end Rank

section RankOne

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real symmetric matrix of rank at most one with non-negative diagonal is positive
semidefinite. -/
lemma posSemidef_of_rank_le_one {G : Matrix n n ℝ} (hG : G.IsSymm) (hr : G.rank ≤ 1)
    (hd : ∀ i, 0 ≤ G i i) : G.PosSemidef := by
  classical
  by_cases h0 : G = 0
  · subst h0; exact PosSemidef.zero
  obtain ⟨i0, hi0⟩ : ∃ i0, G.row i0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (by ext i j; exact congrFun (hc i) j)
  -- every row is a multiple of row `i0`
  have hspan : ∀ j, ∃ c : ℝ, G.row j = c • G.row i0 := by
    intro j
    have hle : span ℝ {G.row i0} ≤ span ℝ (Set.range G.row) :=
      span_mono (Set.singleton_subset_iff.2 ⟨i0, rfl⟩)
    have h1 : finrank ℝ (span ℝ {G.row i0}) = 1 := finrank_span_singleton hi0
    have h2 : finrank ℝ (span ℝ (Set.range G.row)) ≤ 1 := by
      rw [← Matrix.rank_eq_finrank_span_row]; exact hr
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hj : G.row j ∈ span ℝ {G.row i0} := by rw [heq]; exact subset_span ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := mem_span_singleton.1 hj
    exact ⟨c, hc.symm⟩
  choose c hc using hspan
  have hent : ∀ j k, G j k = c j * G i0 k := fun j k => by
    have := congrFun (hc j) k; simpa using this
  have hsym : ∀ j k, G j k = G k j := fun j k => by
    have := congrFun (congrFun hG j) k; simpa using this.symm
  -- `G j k = c_j c_k G_{i0 i0}`
  obtain ⟨g, hgdef⟩ : ∃ g, g = G i0 i0 := ⟨_, rfl⟩
  have hent2 : ∀ j k, G j k = c j * c k * g := by
    intro j k
    rw [hent j k, hsym i0 k, hent k i0, hgdef]; ring
  have hg : 0 ≤ g := hgdef ▸ hd i0
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hG
  · have : star x ⬝ᵥ (G *ᵥ x) = g * ((∑ j, c j * x j) * (∑ k, c k * x k)) := by
      simp only [star_trivial, dotProduct, mulVec]
      simp_rw [hent2]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact mul_nonneg hg (mul_self_nonneg _)

end RankOne

end FreeDiagonal.StatisticalFactorAnalysis
