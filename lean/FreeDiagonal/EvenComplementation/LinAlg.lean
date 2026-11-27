import FreeDiagonal.Witness.RankFormula

/-!
# Part 54-g in Lean: linear-algebra tools for the classification

* `mulVec_eq_zero_of_span`: if the rows indexed by `B` span all rows of `A`, a vector `A y`
  vanishing on `B` is zero (`B` is an information set of the column space).
* `rank_le_of_ker_le`: kernel inclusion gives the reverse rank inequality.
* `frk_comp_injective`: `frk` is unchanged by an injective linear map.
* `exists_coeff`: rows as combinations of the rows indexed by `B`.
* `factor_symm`: a symmetric `A` whose rows indexed by `B` span all rows, with `|B| = rank A`,
  is `C Θ Cᵀ` with `Θ = A[B, B]` invertible and `C` of width `|B|`; and `frk` of rows of `C`
  equals `frk` of rows of `A` (`frk_C_eq`).
-/

open Matrix Module Submodule Finset

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {F : Type*} [Field F] {V : Type*} [Fintype V] [DecidableEq V]

/-- `r ↦ r ⬝ᵥ y` as a linear functional. -/
def dotL (y : V → F) : (V → F) →ₗ[F] F where
  toFun r := r ⬝ᵥ y
  map_add' a b := add_dotProduct a b y
  map_smul' c a := by simp [smul_dotProduct]

lemma mulVec_eq_zero_of_span (A : Matrix V V F) (B : Finset V)
    (hB : ∀ i, A.row i ∈ span F (A.row '' (B : Set V))) (y : V → F)
    (h : ∀ b ∈ B, (A *ᵥ y) b = 0) : A *ᵥ y = 0 := by
  funext i
  have hle : span F (A.row '' (B : Set V)) ≤ LinearMap.ker (dotL y) := by
    rw [span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have := hle (hB i)
  simpa [dotL, mulVec, Matrix.row] using this

omit [DecidableEq V] in
lemma rank_add_finrank_ker {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n F) :
    M.rank + finrank F (LinearMap.ker M.mulVecLin) = Fintype.card n := by
  unfold Matrix.rank
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

omit [DecidableEq V] in
lemma rank_le_of_ker_le {m m' n : Type*} [Fintype m] [Fintype m'] [Fintype n]
    (M1 : Matrix m n F) (M2 : Matrix m' n F) (h : ∀ y, M1 *ᵥ y = 0 → M2 *ᵥ y = 0) :
    M2.rank ≤ M1.rank := by
  have hle : LinearMap.ker M1.mulVecLin ≤ LinearMap.ker M2.mulVecLin := by
    intro y hy
    rw [LinearMap.mem_ker, mulVecLin_apply] at hy ⊢
    exact h y hy
  have h1 := rank_add_finrank_ker M1
  have h2 := rank_add_finrank_ker M2
  have h3 := Submodule.finrank_mono hle
  omega

lemma frk_comp_injective {ι M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
    [Module F N] (f : M →ₗ[F] N) (hf : Function.Injective f) (u : ι → M) (S : Finset ι) :
    frk F (f ∘ u) S = frk F u S := by
  unfold frk
  rw [Set.image_comp, ← Submodule.map_span]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf _)).symm

omit [DecidableEq V] in
lemma exists_coeff (A : Matrix V V F) (B : Finset V)
    (hB : ∀ i, A.row i ∈ span F (A.row '' (B : Set V))) :
    ∃ C : Matrix V B F, A = C * A.submatrix (fun b : B => (b : V)) id := by
  have h : ∀ i, ∃ c : B → F, ∑ b, c b • A.row b = A.row i := by
    intro i
    have hi := hB i
    have e : A.row '' (B : Set V) = Set.range (fun b : B => A.row b) := by
      ext x; constructor
      · rintro ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
      · rintro ⟨b, rfl⟩; exact ⟨b, b.2, rfl⟩
    rw [e] at hi
    exact (Submodule.mem_span_range_iff_exists_fun F).1 hi
  choose C hC using h
  refine ⟨Matrix.of fun i b => C i b, ?_⟩
  ext i j
  have := congrFun (hC i) j
  rw [Matrix.mul_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] at this
  simp [← this]

/-- **Factorisation.** `A` symmetric, the rows indexed by `B` span all rows, `|B| = rank A`.
Then `A = C * Θ * Cᵀ` with `Θ = A[B, B]` invertible. -/
theorem factor_symm (A : Matrix V V F) (hA : A.IsSymm) (B : Finset V)
    (hB : ∀ i, A.row i ∈ span F (A.row '' (B : Set V))) (hcard : B.card = A.rank) :
    ∃ C : Matrix V B F, A = C * A.submatrix (fun b : B => (b : V)) (fun b : B => (b : V)) * Cᵀ ∧
      A = C * A.submatrix (fun b : B => (b : V)) id ∧
      IsUnit (A.submatrix (fun b : B => (b : V)) (fun b : B => (b : V))).det := by
  obtain ⟨C, hC⟩ := exists_coeff A B hB
  set Θ := A.submatrix (fun b : B => (b : V)) (fun b : B => (b : V)) with hΘ
  have hcol : A.submatrix id (fun b : B => (b : V)) = C * Θ := by
    conv_lhs => rw [hC]
    ext i b
    simp [Matrix.mul_apply, hΘ]
  have hrow : A.submatrix (fun b : B => (b : V)) id = Θ * Cᵀ := by
    have h1 : A.submatrix (fun b : B => (b : V)) id = (A.submatrix id (fun b : B => (b : V)))ᵀ := by
      ext b j
      simp only [submatrix_apply, transpose_apply, id]
      have := congrFun (congrFun hA b) j
      simp only [transpose_apply] at this
      exact this.symm
    have hΘs : Θᵀ = Θ := by
      ext a b; simp only [hΘ, transpose_apply, submatrix_apply]
      exact congrFun (congrFun hA _) _
    rw [h1, hcol, transpose_mul, hΘs]
  have hfac : A = C * Θ * Cᵀ := by
    conv_lhs => rw [hC]
    rw [hrow, Matrix.mul_assoc]
  refine ⟨C, hfac, hC, ?_⟩
  have hr : A.rank ≤ Θ.rank := by
    calc A.rank = (C * Θ * Cᵀ).rank := by rw [← hfac]
      _ ≤ (C * Θ).rank := rank_mul_le_left _ _
      _ ≤ Θ.rank := rank_mul_le_right _ _
  have hr2 : Θ.rank ≤ Fintype.card B := rank_le_card_width _
  have hrk : Θ.rank = Fintype.card B := by
    rw [Fintype.card_coe] at hr2 ⊢; omega
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit,
    Matrix.mulVec_surjective_iff_rank_eq_card]
  exact hrk

/-- With `A = C * A[B, ·]` and the rows indexed by `B` independent, `frk` of rows of `C` equals
`frk` of rows of `A`. -/
theorem frk_C_eq (A : Matrix V V F) (B : Finset V) (C : Matrix V B F)
    (hC : A = C * A.submatrix (fun b : B => (b : V)) id) (hind : frk F A.row B = B.card)
    (S : Finset V) : frk F C.row S = frk F A.row S := by
  set R1 := A.submatrix (fun b : B => (b : V)) id
  have hset : Set.range (fun b : B => R1 b) = A.row '' (B : Set V) := by
    ext x; constructor
    · rintro ⟨b, rfl⟩; exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
  have hli : LinearIndependent F (fun b : B => R1 b) := by
    rw [linearIndependent_iff_card_eq_finrank_span, hset, Fintype.card_coe]
    exact hind.symm
  have hinj : Function.Injective R1.vecMul := Matrix.vecMul_injective_iff.2 hli
  let f : (B → F) →ₗ[F] (V → F) :=
    { toFun := fun c => c ᵥ* R1
      map_add' := fun a b => Matrix.add_vecMul R1 a b
      map_smul' := fun c a => Matrix.smul_vecMul c a R1 }
  have e : A.row = f ∘ C.row := by
    funext i
    ext j
    simp only [Function.comp_apply, f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.row]
    conv_lhs => rw [hC]
    rfl
  rw [e, frk_comp_injective f hinj]

end FreeDiagonal.EvenComplementation
