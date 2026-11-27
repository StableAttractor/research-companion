import Mathlib

/-!
# Gram matrices over the reals

A real symmetric matrix is positive semidefinite of rank at most `m` iff it is the Gram matrix of
vectors in a Euclidean space of dimension at most `m`, iff it is `Λ Λᵀ` with `Λ` of width `m`.
-/

open Matrix Module Submodule

namespace FreeDiagonal.StatisticalFactorAnalysis

section Gram

variable {n : Type*} [Fintype n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_mulVec (v : n → E) (c : n → ℝ) (i : n) :
    (gram ℝ v *ᵥ c) i = inner ℝ (v i) (Fintype.linearCombination ℝ v c) := by
  simp only [mulVec, dotProduct, gram_apply, Fintype.linearCombination_apply, inner_sum,
    inner_smul_right, mul_comm]

lemma dotProduct_gram_mulVec (v : n → E) (c : n → ℝ) :
    c ⬝ᵥ (gram ℝ v *ᵥ c) =
      inner ℝ (Fintype.linearCombination ℝ v c) (Fintype.linearCombination ℝ v c) := by
  simp only [dotProduct, gram_mulVec]
  conv_rhs => rw [Fintype.linearCombination_apply, sum_inner]
  simp only [inner_smul_left, Fintype.linearCombination_apply]
  simp

lemma ker_gram (v : n → E) :
    LinearMap.ker (gram ℝ v).mulVecLin = LinearMap.ker (Fintype.linearCombination ℝ v) := by
  ext c
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    have h2 := dotProduct_gram_mulVec v c
    rw [h, dotProduct_zero] at h2
    exact inner_self_eq_zero.1 h2.symm
  · intro h
    funext i
    rw [gram_mulVec, h, inner_zero_right]
    rfl

/-- The rank of a Gram matrix is the dimension of the span of the vectors. -/
theorem rank_gram (v : n → E) :
    (gram ℝ v).rank = finrank ℝ (span ℝ (Set.range v)) := by
  rw [Matrix.rank, ← Fintype.range_linearCombination]
  have h1 := LinearMap.finrank_range_add_finrank_ker (gram ℝ v).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination ℝ v)
  rw [ker_gram] at h1
  omega

lemma rank_gram_le [FiniteDimensional ℝ E] (v : n → E) : (gram ℝ v).rank ≤ finrank ℝ E := by
  rw [rank_gram]; exact Submodule.finrank_le _

end Gram

section PSD

variable {n : Type*} [Fintype n]

/-- A positive semidefinite real matrix is a Gram matrix. -/
theorem exists_gram_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∃ (k : ℕ) (v : n → EuclideanSpace ℝ (Fin k)), gram ℝ v = A := by
  obtain ⟨k, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hA
  refine ⟨k, fun a => WithLp.toLp 2 (fun i => w i a), ?_⟩
  ext a b
  rw [hw]
  simp [gram_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, vecMulVec_apply,
    Matrix.sum_apply, mul_comm]

end PSD

end FreeDiagonal.StatisticalFactorAnalysis
