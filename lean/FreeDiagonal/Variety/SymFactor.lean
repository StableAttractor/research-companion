import FreeDiagonal.Variety.Theorem3
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Symmetric matrices of rank `≤ m` are `Λ Λᵀ`

Over an algebraically closed field of characteristic other than 2, every symmetric matrix of rank
at most `m` is `Λ Λᵀ` for some `Λ` with `m` columns. Proof: an orthogonal basis for the bilinear
form `uᵀ M w` (Mathlib, `LinearMap.BilinForm.exists_orthogonal_basis`) writes
`M = Σ_i a_i y_i y_iᵀ`; at most `rank M` of the `a_i` are nonzero; take square roots.
-/

open Matrix Finset

namespace FreeDiagonal

variable {K : Type*} [Field K]

/-- **Symmetric factorization.** `K` algebraically closed, `2 ≠ 0` in `K`, `M` symmetric of rank
`≤ m`: then `M = Λ Λᵀ` for some `Λ : ι × m`. -/
theorem exists_mul_transpose_eq [IsAlgClosed K] (h2 : (2 : K) ≠ 0) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι K) (hM : Mᵀ = M) (m : ℕ) (hr : M.rank ≤ m) :
    ∃ Λ : Matrix ι (Fin m) K, Λ * Λᵀ = M := by
  classical
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  let B : LinearMap.BilinForm K (ι → K) := Matrix.toBilin' M
  have hBs : ∀ u w, B u w = B w u := by
    intro u w
    simp only [B, Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) ⟨hBs⟩
  let a : Fin (Module.finrank K (ι → K)) → K := fun i => B (v i) (v i)
  have hortho : ∀ i j, i ≠ j → B (v i) (v j) = 0 := fun i j hij => hv hij
  -- `B u w = Σ a_i c_i(u) c_i(w)`
  have key : ∀ u w, B u w = ∑ i, a i * v.repr u i * v.repr w i := by
    intro u w
    conv_lhs => rw [← v.sum_repr u, ← v.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hortho i j (Ne.symm hji), hortho j i hji])
      (by simp)]
    simp only [a]; ring
  -- at most `rank M` of the `a_i` are nonzero
  let S := {i : Fin (Module.finrank K (ι → K)) // a i ≠ 0}
  have hcard : Fintype.card S ≤ m := by
    let f : S → LinearMap.range M.mulVecLin := fun i => ⟨M *ᵥ v i, ⟨v i, rfl⟩⟩
    have hli : LinearIndependent K f := by
      rw [linearIndependent_iff']
      intro s g hg i hi
      have h0 := congrArg (fun z : LinearMap.range M.mulVecLin => v i ⬝ᵥ (z : ι → K)) hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, f, dotProduct_sum, dotProduct_smul,
        smul_eq_mul, ZeroMemClass.coe_zero, dotProduct_zero] at h0
      rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd hi h)] at h0
      · have : v i ⬝ᵥ M *ᵥ v i = a i := by simp [a, B, Matrix.toBilin'_apply']
        rw [this] at h0
        exact (mul_eq_zero.1 h0).resolve_right i.2
      · have : v i ⬝ᵥ M *ᵥ v j = 0 := by
          have := hortho i j (fun e => hji (Subtype.ext e.symm))
          simpa [B, Matrix.toBilin'_apply'] using this
        rw [this, mul_zero]
    have := hli.fintype_card_le_finrank
    exact this.trans hr
  -- square roots
  choose s hs using fun i : S => IsAlgClosed.exists_pow_nat_eq (a i) two_pos
  let Λ0 : Matrix ι S K := Matrix.of fun x i => s i * v.repr (Pi.single x 1) i
  have hΛ0 : Λ0 * Λ0ᵀ = M := by
    ext x y
    rw [← Matrix.toBilin'_single M x y, key]
    simp only [Matrix.mul_apply, transpose_apply, Λ0, of_apply]
    have e1 : ∀ i : S, s i * v.repr (Pi.single x 1) i * (s i * v.repr (Pi.single y 1) i) =
        a i * v.repr (Pi.single x 1) i * v.repr (Pi.single y 1) i := by
      intro i; rw [← hs i]; ring
    simp only [e1]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => a i ≠ 0)
      (fun i => a i * v.repr (Pi.single x 1) i * v.repr (Pi.single y 1) i)]
    have e2 : ∑ i : {i // ¬ a i ≠ 0}, a i * v.repr (Pi.single x 1) i * v.repr (Pi.single y 1) i
        = 0 := Finset.sum_eq_zero (fun i _ => by rw [not_not.1 i.2]; ring)
    rw [e2, add_zero]
  -- pad to `m` columns
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le (by simpa using hcard :
    Fintype.card S ≤ Fintype.card (Fin m))
  let E : Matrix S (Fin m) K := Matrix.of fun i l => if φ i = l then 1 else 0
  have hE : E * Eᵀ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, transpose_apply, E, of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, φ.injective.eq_iff]
    rw [Matrix.one_apply]
  refine ⟨Λ0 * E, ?_⟩
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc E, hE, Matrix.one_mul, hΛ0]

end FreeDiagonal
