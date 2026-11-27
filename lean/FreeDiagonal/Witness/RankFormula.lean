import FreeDiagonal.Foundations.Rank

/-!
# Theorem 1 of the note: the rank formula

`U, V : m × q`, `Θ` invertible `q × q`, `G = U Θ⁻¹ Vᵀ`, `D = diag d`, `Z = {i : d i = 0}`:

  rank (G - D) = (m - q) - |Z| + rk_U(Z) + rk_V(Z) + rank β_D,

with `β_D (ψ, φ) = ψᵀ (Θ - Σ_{i ∉ Z} d_i⁻¹ v_iᵀ u_i) φ` on
`{ψ : v_i ψ = 0, i ∈ Z} × {φ : u_i φ = 0, i ∈ Z}`. Stated without subtraction:
`rank (G - D) + q + |Z| = m + rk_U(Z) + rk_V(Z) + rank β_D`.

The rank of `β_D` is the rank of the linear map `Φ → Ψ*`, `φ ↦ β_D(·, φ)`.
Not used by the proofs of Theorems 2 and 3 (they follow Part 51); formalized because the note states it.
-/

open Matrix Module Finset

namespace FreeDiagonal

variable {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

private lemma rk_add_ker' {m k : Type*} [Fintype k] (M : Matrix m k F) [Fintype m] :
    M.rank + finrank F (LinearMap.ker M.mulVecLin) = Fintype.card k := by
  unfold Matrix.rank
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- The rows of `U` indexed by `Z`. -/
def rowsOn (U : Matrix ι κ F) (Z : Finset ι) : Matrix Z κ F :=
  U.submatrix (fun z : Z => (z : ι)) id

/-- `{φ : u_i φ = 0 for all i ∈ Z}`. -/
def annSub (U : Matrix ι κ F) (Z : Finset ι) : Submodule F (κ → F) :=
  LinearMap.ker (rowsOn U Z).mulVecLin

lemma mem_annSub (U : Matrix ι κ F) (Z : Finset ι) (φ : κ → F) :
    φ ∈ annSub U Z ↔ ∀ i ∈ Z, U i ⬝ᵥ φ = 0 := by
  rw [annSub, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext z; exact h z z.2

/-- `Θ - Σ_{i ∉ Z} d_i⁻¹ v_iᵀ u_i`. -/
noncomputable def betaMat (U V : Matrix ι κ F) (Θ : Matrix κ κ F) (d : ι → F) (Z : Finset ι) :
    Matrix κ κ F :=
  Θ - ∑ i ∈ Zᶜ, (d i)⁻¹ • vecMulVec (V i) (U i)

/-- The bilinear form `(ψ, φ) ↦ ψᵀ M φ` on `Ψ × Φ`, as a linear map `Φ → Ψ*`. -/
noncomputable def betaForm (M : Matrix κ κ F) (Ψ Φ : Submodule F (κ → F)) :
    Φ →ₗ[F] Module.Dual F Ψ :=
  LinearMap.mk₂ F (fun (φ : Φ) (ψ : Ψ) => (ψ : κ → F) ⬝ᵥ (M *ᵥ (φ : κ → F)))
    (by intro a b c; simp [mulVec_add, dotProduct_add])
    (by intro r a b; simp [mulVec_smul, dotProduct_smul])
    (by intro a b c; simp [add_dotProduct])
    (by intro r a b; simp [smul_dotProduct])

/-- `range Aᵀ` is the set of vectors orthogonal (for the dot product) to `ker A`. -/
lemma mem_range_transpose_iff {ρ : Type*} [Fintype ρ] (A : Matrix ρ κ F) (y : κ → F) :
    y ∈ LinearMap.range Aᵀ.mulVecLin ↔ ∀ ψ, A *ᵥ ψ = 0 → ψ ⬝ᵥ y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩ ψ hψ
    rw [mulVecLin_apply, dotProduct_mulVec, vecMul_transpose, hψ, zero_dotProduct]
  · intro h
    set K := LinearMap.ker A.mulVecLin with hK
    let W' : Submodule F (κ → F) :=
      { carrier := {y | ∀ ψ ∈ K, ψ ⬝ᵥ y = 0}
        add_mem' := by
          intro a b ha hb ψ hψ; rw [dotProduct_add, ha ψ hψ, hb ψ hψ, add_zero]
        zero_mem' := by intro ψ _; exact dotProduct_zero ψ
        smul_mem' := by intro c a ha ψ hψ; rw [dotProduct_smul, ha ψ hψ, smul_zero] }
    have hle : LinearMap.range Aᵀ.mulVecLin ≤ W' := by
      rintro _ ⟨c, rfl⟩ ψ hψ
      rw [LinearMap.mem_ker, mulVecLin_apply] at hψ
      show ψ ⬝ᵥ (Aᵀ.mulVecLin c) = 0
      rw [mulVecLin_apply, dotProduct_mulVec, vecMul_transpose, hψ, zero_dotProduct]
    let b := Module.finBasis F K
    let B : Matrix (Fin (finrank F K)) κ F := fun j => (b j : κ → F)
    have hW' : W' = LinearMap.ker B.mulVecLin := by
      ext z; constructor
      · intro hz; rw [LinearMap.mem_ker]; funext j
        have := hz (b j) (b j).2
        show (b j : κ → F) ⬝ᵥ z = 0
        exact this
      · intro hz ψ hψ
        rw [LinearMap.mem_ker, mulVecLin_apply] at hz
        have hsum : ψ = ∑ j, (b.repr ⟨ψ, hψ⟩ j) • (b j : κ → F) := by
          have := congrArg Subtype.val (b.sum_repr ⟨ψ, hψ⟩)
          rw [Submodule.coe_sum] at this
          simp only [Submodule.coe_smul] at this
          exact this.symm
        rw [hsum, sum_dotProduct]
        apply Finset.sum_eq_zero; intro j _
        have h' : (b j : κ → F) ⬝ᵥ z = 0 := congrFun hz j
        rw [smul_dotProduct, h', smul_zero]
    have hBr : B.rank = finrank F K := by
      rw [rank_eq_finrank_span_row]
      have hli : LinearIndependent F (fun j => (b j : κ → F)) :=
        b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
      show finrank F (Submodule.span F (Set.range fun j => (b j : κ → F))) = _
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have h1 : A.rank + finrank F K = Fintype.card κ := rk_add_ker' A
    have h2 := rk_add_ker' B
    have hT : Aᵀ.rank = A.rank := rank_transpose A
    have heq : LinearMap.range Aᵀ.mulVecLin = W' := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [hW']
      have : finrank F (LinearMap.range Aᵀ.mulVecLin) = Aᵀ.rank := rfl
      omega
    rw [heq]
    intro ψ hψ
    exact h ψ (by rwa [hK, LinearMap.mem_ker, mulVecLin_apply] at hψ)

lemma betaMat_mulVec (U V : Matrix ι κ F) (Θ : Matrix κ κ F) (d : ι → F) (Z : Finset ι)
    (φ : κ → F) :
    betaMat U V Θ d Z *ᵥ φ = Θ *ᵥ φ - ∑ i ∈ Zᶜ, ((d i)⁻¹ * (U i ⬝ᵥ φ)) • V i := by
  rw [betaMat, sub_mulVec]
  congr 1
  funext a
  simp only [mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma transpose_mulVec_split (V : Matrix ι κ F) (Z : Finset ι) (w : ι → F) :
    Vᵀ *ᵥ w = (rowsOn V Z)ᵀ *ᵥ (fun z : Z => w z) + ∑ i ∈ Zᶜ, w i • V i := by
  funext a
  simp only [mulVec, dotProduct, transpose_apply, rowsOn, submatrix_apply, id, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_sum_compl Z, Finset.sum_coe_sort Z (fun i => V i a * w i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Theorem 1 of the note (rank formula).** -/
theorem rank_formula (U V : Matrix ι κ F) (Θ : Matrix κ κ F) (hΘ : IsUnit Θ.det) (d : ι → F)
    (Z : Finset ι) (hZ : ∀ i, i ∈ Z ↔ d i = 0) :
    (U * Θ⁻¹ * Vᵀ - diagonal d).rank + Fintype.card κ + Z.card =
      Fintype.card ι + frk F U.row Z + frk F V.row Z +
        finrank F (LinearMap.range (betaForm (betaMat U V Θ d Z) (annSub V Z) (annSub U Z))) := by
  set G := U * Θ⁻¹ * Vᵀ - diagonal d with hG
  set M := betaMat U V Θ d Z with hM
  set Ψ := annSub V Z with hΨ
  set Φ := annSub U Z with hΦ
  set Vz := rowsOn V Z with hVz
  have hinv : Θ⁻¹ * Θ = 1 := nonsing_inv_mul Θ hΘ
  have hinv' : Θ * Θ⁻¹ = 1 := mul_nonsing_inv Θ hΘ
  have hGw : ∀ w, G *ᵥ w = U *ᵥ (Θ⁻¹ *ᵥ (Vᵀ *ᵥ w)) - fun i => d i * w i := by
    intro w; funext i
    simp [hG, sub_mulVec, ← mulVec_mulVec, mulVec_diagonal]
  have hUi : ∀ (φ : κ → F) i, (U *ᵥ φ) i = U i ⬝ᵥ φ := fun _ _ => rfl
  -- the space S of pairs (c, φ)
  let S : Submodule F ((Z → F) × (κ → F)) :=
    { carrier := {p | p.2 ∈ Φ ∧ M *ᵥ p.2 = Vzᵀ *ᵥ p.1}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨Φ.add_mem ha1 hb1, by simp [mulVec_add, ha2, hb2]⟩
      zero_mem' := ⟨Φ.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨Φ.smul_mem c ha1, by simp [mulVec_smul, ha2]⟩ }
  have hmemS : ∀ p, p ∈ S ↔ p.2 ∈ Φ ∧ M *ᵥ p.2 = Vzᵀ *ᵥ p.1 := fun _ => Iff.rfl
  -- Step 1: S ≅ ker (G - D)
  let wOf : (Z → F) × (κ → F) →ₗ[F] (ι → F) :=
    { toFun := fun p i => if h : i ∈ Z then p.1 ⟨i, h⟩ else (d i)⁻¹ * (U i ⬝ᵥ p.2)
      map_add' := by
        intro a b; funext i; by_cases h : i ∈ Z <;> simp [h, dotProduct_add, mul_add]
      map_smul' := by
        intro c a; funext i; by_cases h : i ∈ Z <;> simp [h, dotProduct_smul] <;> ring }
  have hwOf : ∀ p i, wOf p i = if h : i ∈ Z then p.1 ⟨i, h⟩ else (d i)⁻¹ * (U i ⬝ᵥ p.2) :=
    fun _ _ => rfl
  have hVw : ∀ p ∈ S, Vᵀ *ᵥ wOf p = Θ *ᵥ p.2 := by
    rintro p ⟨_, h2⟩
    rw [transpose_mulVec_split V Z]
    have e1 : (fun z : Z => wOf p z) = p.1 := by
      funext z; rw [hwOf, dif_pos z.2]
    have e2 : ∑ i ∈ Zᶜ, wOf p i • V i = ∑ i ∈ Zᶜ, ((d i)⁻¹ * (U i ⬝ᵥ p.2)) • V i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hwOf, dif_neg (Finset.mem_compl.1 hi)]
    rw [e1, e2, ← hVz, ← h2, hM, betaMat_mulVec, sub_add_cancel]
  have hTmem : ∀ p : S, wOf p ∈ LinearMap.ker G.mulVecLin := by
    rintro ⟨p, hp⟩
    have hΘΘ : Θ⁻¹ *ᵥ (Θ *ᵥ p.2) = p.2 := by rw [mulVec_mulVec, hinv, one_mulVec]
    rw [LinearMap.mem_ker, mulVecLin_apply, hGw, hVw p hp, hΘΘ]
    have hp1 := (mem_annSub U Z p.2).1 hp.1
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply, hUi]
    by_cases h : i ∈ Z
    · rw [hp1 i h, (hZ i).1 h, zero_mul, sub_zero]
    · have hd : d i ≠ 0 := fun h' => h ((hZ i).2 h')
      rw [hwOf, dif_neg h, ← mul_assoc, mul_inv_cancel₀ hd, one_mul, sub_self]
  let T : S →ₗ[F] LinearMap.ker G.mulVecLin :=
    LinearMap.codRestrict _ (wOf.comp S.subtype) hTmem
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨c, φ⟩, hp1, hp2⟩ h0
    have hw : wOf (c, φ) = 0 := congrArg Subtype.val h0
    have hc : c = 0 := by
      funext z; have := congrFun hw z; rwa [hwOf, dif_pos z.2] at this
    have hUφ : ∀ i, U i ⬝ᵥ φ = 0 := by
      intro i
      by_cases h : i ∈ Z
      · exact (mem_annSub U Z φ).1 hp1 i h
      · have hd : d i ≠ 0 := fun h' => h ((hZ i).2 h')
        have := congrFun hw i
        rw [hwOf, dif_neg h] at this
        simpa [hd] using this
    have hΘφ : Θ *ᵥ φ = 0 := by
      have := hp2
      simp only at this
      rw [hM, betaMat_mulVec, hc, mulVec_zero] at this
      simpa [hUφ] using this
    have hφ : φ = 0 := by
      rw [← one_mulVec φ, ← hinv, ← mulVec_mulVec, hΘφ, mulVec_zero]
    subst hc; subst hφ; rfl
  have hTsurj : Function.Surjective T := by
    rintro ⟨w, hw⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, hGw, sub_eq_zero] at hw
    set φ := Θ⁻¹ *ᵥ (Vᵀ *ᵥ w) with hφdef
    have hUφ : ∀ i, U i ⬝ᵥ φ = d i * w i := fun i => congrFun hw i
    have hφΦ : φ ∈ Φ := (mem_annSub U Z φ).2 fun i hi => by rw [hUφ, (hZ i).1 hi, zero_mul]
    have hcomp : ∑ i ∈ Zᶜ, ((d i)⁻¹ * (U i ⬝ᵥ φ)) • V i = ∑ i ∈ Zᶜ, w i • V i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hd : d i ≠ 0 := fun h' => (Finset.mem_compl.1 hi) ((hZ i).2 h')
      rw [hUφ, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    have hMφ : M *ᵥ φ = Vzᵀ *ᵥ (fun z : Z => w z) := by
      rw [hM, betaMat_mulVec, hcomp, hφdef, mulVec_mulVec, hinv', one_mulVec,
        transpose_mulVec_split V Z, add_sub_cancel_right]
    refine ⟨⟨(fun z : Z => w z, φ), hφΦ, hMφ⟩, ?_⟩
    apply Subtype.ext
    show wOf (fun z : Z => w z, φ) = w
    funext i
    rw [hwOf]
    by_cases h : i ∈ Z
    · rw [dif_pos h]
    · have hd : d i ≠ 0 := fun h' => h ((hZ i).2 h')
      rw [dif_neg h, hUφ, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have hS1 : finrank F S = finrank F (LinearMap.ker G.mulVecLin) :=
    (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩).finrank_eq
  -- Step 2: dim S = dim ker Vzᵀ + dim ker β
  let p2 : S →ₗ[F] (κ → F) := (LinearMap.snd F (Z → F) (κ → F)).comp S.subtype
  have hrange : LinearMap.range p2 = (LinearMap.ker (betaForm M Ψ Φ)).map Φ.subtype := by
    ext φ; constructor
    · rintro ⟨⟨⟨c, φ'⟩, h1, h2⟩, rfl⟩
      refine ⟨⟨φ', h1⟩, LinearMap.mem_ker.2 ?_, rfl⟩
      ext ψ
      show (ψ : κ → F) ⬝ᵥ (M *ᵥ φ') = 0
      have hψ : Vz *ᵥ (ψ : κ → F) = 0 := ψ.2
      simp only at h2
      rw [h2, dotProduct_mulVec, vecMul_transpose, hψ, zero_dotProduct]
    · rintro ⟨⟨φ', h1⟩, hk, rfl⟩
      have hr : M *ᵥ φ' ∈ LinearMap.range Vzᵀ.mulVecLin := by
        rw [mem_range_transpose_iff]
        intro ψ hψ
        have := LinearMap.congr_fun (LinearMap.mem_ker.1 hk) ⟨ψ, hψ⟩
        exact this
      obtain ⟨c, hc⟩ := hr
      exact ⟨⟨(c, φ'), h1, hc.symm⟩, rfl⟩
  have hrk : finrank F (LinearMap.range p2) = finrank F (LinearMap.ker (betaForm M Ψ Φ)) := by
    rw [hrange]
    exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype Φ) _).finrank_eq.symm
  have hgmem : ∀ c : LinearMap.ker Vzᵀ.mulVecLin, ((c : Z → F), (0 : κ → F)) ∈ S := by
    rintro ⟨c, hc⟩
    refine ⟨Φ.zero_mem, ?_⟩
    simp only [mulVec_zero]
    exact (LinearMap.mem_ker.1 hc).symm
  let g0 : LinearMap.ker Vzᵀ.mulVecLin →ₗ[F] S :=
    LinearMap.codRestrict S ((LinearMap.inl F (Z → F) (κ → F)).comp (Submodule.subtype _))
      hgmem
  have hg0 : ∀ c, g0 c ∈ LinearMap.ker p2 := fun c => by
    rw [LinearMap.mem_ker]; rfl
  let g : LinearMap.ker Vzᵀ.mulVecLin →ₗ[F] LinearMap.ker p2 :=
    LinearMap.codRestrict _ g0 hg0
  have hginj : Function.Injective g := by
    intro a b h
    have := congrArg (fun x : LinearMap.ker p2 => ((x : S) : (Z → F) × (κ → F)).1) h
    exact Subtype.ext this
  have hgsurj : Function.Surjective g := by
    rintro ⟨⟨⟨c, φ⟩, h1, h2⟩, hp⟩
    have hφ : φ = 0 := hp
    subst hφ
    simp only [mulVec_zero] at h2
    refine ⟨⟨c, LinearMap.mem_ker.2 h2.symm⟩, ?_⟩
    rfl
  have hk : finrank F (LinearMap.ker p2) = finrank F (LinearMap.ker Vzᵀ.mulVecLin) :=
    (LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩).finrank_eq.symm
  have hp := LinearMap.finrank_range_add_finrank_ker p2
  have hβ := LinearMap.finrank_range_add_finrank_ker (betaForm M Ψ Φ)
  -- Step 3: the other dimensions
  have h1 := rk_add_ker' G
  have hΦd := rk_add_ker' (rowsOn U Z)
  have hUr : (rowsOn U Z).rank = frk F U.row Z := rank_submatrix_rows_eq_frk U Z
  have hVd := rk_add_ker' Vzᵀ
  have hVr : Vzᵀ.rank = frk F V.row Z := by
    rw [rank_transpose]; exact rank_submatrix_rows_eq_frk V Z
  have hZc : Fintype.card Z = Z.card := Fintype.card_coe Z
  have hΦe : finrank F (LinearMap.ker (rowsOn U Z).mulVecLin) = finrank F Φ := rfl
  omega

end FreeDiagonal
