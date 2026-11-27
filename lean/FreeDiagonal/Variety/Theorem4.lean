import FreeDiagonal.Variety.SymFactor
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Theorem 4: the radical part of Question 29 of Drton, Sturmfels and Sullivant

The factor analysis model with index set `ι` (observed variables) and `m` factors is the set of
real matrices `Λ Λᵀ + Δ` with `Λ : ι × m` real and `Δ` diagonal with positive entries.
`FAideal ι m ⊆ ℝ[ψ_ij : i < j]` is the ideal of polynomials in the off-diagonal entries that
vanish on the model, and `FAidealOn A m` is the same ideal in the variables indexed by `A`,
renamed into `ℝ[ψ_ij : i < j ∈ ι]`. The proof does not use [DSS07, Theorem 7]:

1. `zeroLocus_FAideal`: the complex zero locus of `FAideal ι m` is `X_{ι,m}` over `ℂ`. Steps:
   real points and complex points (`vanishingIdeal_ofReal`), real and imaginary parts of a
   complex polynomial (`zeroLocus_real_eq_closure`), density of real `Λ` in complex `Λ`
   (`dense_real_factors`), and `{c ≤ m} = {Λ Λᵀ}` over `ℂ` (`exists_mul_transpose_eq`).
2. `zeroLocus_sumIdeal`: the zero locus of `Σ_{|A| = t} FAidealOn A m` is
   `{x : x_A ∈ X_{A,m} for all |A| = t}`.
3. `radical_eq_iff_zeroLocus_eq`: two ideals of `ℝ[ψ]` have the same radical iff their complex
   zero loci agree (Nullstellensatz, `vanishingIdeal_zeroLocus_eq_radical` with `ℝ → ℂ`).
4. Theorem 3 (under `ClosedRhoSym ℂ`) and its sharpness finish the proof.
-/

open Matrix Finset MvPolynomial Complex

namespace FreeDiagonal

/-! ### Zero loci of sums and renamings -/

section ZeroLocus

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {σ τ : Type*}

lemma mem_zeroLocus_iff_le_ker (I : Ideal (MvPolynomial σ k)) (z : σ → K) :
    z ∈ zeroLocus K I ↔ I ≤ RingHom.ker (aeval z : MvPolynomial σ k →ₐ[k] K) :=
  ⟨fun h p hp => (RingHom.mem_ker).2 (h p hp), fun h p hp => (RingHom.mem_ker).1 (h hp)⟩

lemma mem_zeroLocus_iSup {ι : Type*} (I : ι → Ideal (MvPolynomial σ k)) (z : σ → K) :
    z ∈ zeroLocus K (⨆ i, I i) ↔ ∀ i, z ∈ zeroLocus K (I i) := by
  simp only [mem_zeroLocus_iff_le_ker, iSup_le_iff]

lemma mem_zeroLocus_map_rename (e : τ → σ) (J : Ideal (MvPolynomial τ k)) (z : σ → K) :
    z ∈ zeroLocus K (Ideal.map (rename e) J) ↔ z ∘ e ∈ zeroLocus K J := by
  rw [mem_zeroLocus_iff_le_ker, Ideal.map_le_iff_le_comap]
  constructor
  · intro h p hp
    have := h hp
    rw [Ideal.mem_comap, RingHom.mem_ker] at this
    simpa [aeval_rename] using this
  · intro h p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa [aeval_rename] using h p hp

lemma zeroLocus_radical (I : Ideal (MvPolynomial σ k)) :
    zeroLocus K I.radical = zeroLocus K I := by
  apply Set.Subset.antisymm (zeroLocus_anti_mono Ideal.le_radical)
  intro z hz p ⟨n, hn⟩
  have := hz _ hn
  rw [map_pow] at this
  exact pow_eq_zero_iff'.1 this |>.1

/-- **The Nullstellensatz step.** Over `k ⊆ K` with `K` algebraically closed and finitely many
variables, two ideals of `k[σ]` have the same radical iff their zero loci in `K^σ` agree. -/
theorem radical_eq_iff_zeroLocus_eq [IsAlgClosed K] [Finite σ] (I J : Ideal (MvPolynomial σ k)) :
    I.radical = J.radical ↔ zeroLocus K I = zeroLocus K J := by
  constructor
  · intro h
    rw [← zeroLocus_radical (K := K) I, h, zeroLocus_radical]
  · intro h
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), h, vanishingIdeal_zeroLocus_eq_radical]

end ZeroLocus

/-! ### Real points in complex space -/

section Real

variable {σ : Type*}

/-- A real point as a complex point. -/
def ofRealPt (x : σ → ℝ) : σ → ℂ := fun s => (x s : ℂ)

lemma aeval_ofRealPt (x : σ → ℝ) (f : MvPolynomial σ ℝ) :
    aeval (ofRealPt x) f = ((aeval x f : ℝ) : ℂ) :=
  aeval_algebraMap_apply (B := ℂ) x f

/-- Real points: vanishing at `x` or at `x` seen in `ℂ^σ` is the same. -/
lemma vanishingIdeal_ofReal (V : Set (σ → ℝ)) :
    vanishingIdeal ℝ V = vanishingIdeal ℝ (ofRealPt '' V) := by
  ext f
  simp only [mem_vanishingIdeal_iff, Set.forall_mem_image, aeval_ofRealPt, ofReal_eq_zero]

/-- The real part of a complex polynomial, coefficient by coefficient. -/
noncomputable def rePart (g : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ s ∈ g.support, monomial s (g.coeff s).re

/-- The imaginary part of a complex polynomial, coefficient by coefficient. -/
noncomputable def imPart (g : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ s ∈ g.support, monomial s (g.coeff s).im

lemma coeff_rePart (g : MvPolynomial σ ℂ) (t : σ →₀ ℕ) : (rePart g).coeff t = (g.coeff t).re := by
  classical
  rw [rePart, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, zero_re]

lemma coeff_imPart (g : MvPolynomial σ ℂ) (t : σ →₀ ℕ) : (imPart g).coeff t = (g.coeff t).im := by
  classical
  rw [imPart, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, zero_im]

lemma eq_rePart_add_imPart (g : MvPolynomial σ ℂ) :
    g = map (algebraMap ℝ ℂ) (rePart g) + C I * map (algebraMap ℝ ℂ) (imPart g) := by
  ext t
  simp only [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_rePart, coeff_imPart, coe_algebraMap]
  rw [mul_comm, re_add_im]

lemma aeval_eq_re_add_im (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    aeval z g = aeval z (rePart g) + I * aeval z (imPart g) := by
  conv_lhs => rw [eq_rePart_add_imPart g]
  rw [map_add, map_mul, aeval_map_algebraMap, aeval_map_algebraMap, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- For a set of real points, the closure with real polynomials equals the Zariski closure. -/
lemma zeroLocus_real_eq_closure (V : Set (σ → ℝ)) :
    zeroLocus ℂ (vanishingIdeal ℝ (ofRealPt '' V)) = zariskiClosure (ofRealPt '' V) := by
  apply Set.Subset.antisymm
  · intro z hz g hg
    rw [mem_vanishingIdeal_iff] at hg
    have hre : ∀ x ∈ V, aeval x (rePart g) = 0 ∧ aeval x (imPart g) = 0 := by
      intro x hx
      have h0 := hg _ ⟨x, hx, rfl⟩
      rw [aeval_eq_re_add_im, aeval_ofRealPt, aeval_ofRealPt] at h0
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp at h1 h2
      exact ⟨h1, h2⟩
    have hr : rePart g ∈ vanishingIdeal ℝ (ofRealPt '' V) := by
      rw [← vanishingIdeal_ofReal, mem_vanishingIdeal_iff]; exact fun x hx => (hre x hx).1
    have hi : imPart g ∈ vanishingIdeal ℝ (ofRealPt '' V) := by
      rw [← vanishingIdeal_ofReal, mem_vanishingIdeal_iff]; exact fun x hx => (hre x hx).2
    rw [aeval_eq_re_add_im, hz _ hr, hz _ hi]; simp
  · intro z hz f hf
    rw [mem_vanishingIdeal_iff] at hf
    have h := hz (map (algebraMap ℝ ℂ) f) (by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [aeval_map_algebraMap]; exact hf x hx)
    rwa [aeval_map_algebraMap] at h

end Real

/-! ### The factor analysis model -/

section Model

variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- The off-diagonal coordinates `ψ_ij`, `i < j`, of a matrix. -/
def symCoords {R : Type*} (S : Matrix ι ι R) : SymIdx ι → R := fun q => S q.1.1 q.1.2

/-- **The factor analysis model** with observed variables `ι` and `m` factors: the real matrices
`Λ Λᵀ + Δ` with `Λ : ι × m` and `Δ` diagonal with positive entries. -/
def FAmodel (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) : Set (Matrix ι ι ℝ) :=
  {S | ∃ (Λ : Matrix ι (Fin m) ℝ) (δ : ι → ℝ), (∀ i, 0 < δ i) ∧ S = Λ * Λᵀ + diagonal δ}

variable (ι) in
/-- **`I_{p,m}`**: the polynomials in the off-diagonal entries `ψ_ij` (`i < j`) that vanish on the
covariance matrices of the factor analysis model. -/
noncomputable def FAideal (m : ℕ) : Ideal (MvPolynomial (SymIdx ι) ℝ) :=
  vanishingIdeal ℝ (symCoords '' FAmodel ι m)

/-- The variables indexed by `A` among those indexed by `ι`. -/
def symEmb (A : Finset ι) : SymIdx A → SymIdx ι := fun q => ⟨((q.1.1 : ι), (q.1.2 : ι)), q.2⟩

/-- **`I_{A,m}`**: the ideal `I_{|A|,m}` in the variables indexed by `A`. -/
noncomputable def FAidealOn (A : Finset ι) (m : ℕ) : Ideal (MvPolynomial (SymIdx ι) ℝ) :=
  Ideal.map (rename (symEmb A)) (FAideal A m)

variable (ι) in
/-- `Σ_{|A| = t} I_{A,m}`. -/
noncomputable def sumIdeal (m t : ℕ) : Ideal (MvPolynomial (SymIdx ι) ℝ) :=
  ⨆ A : {A : Finset ι // A.card = t}, FAidealOn A.1 m

lemma symCoords_diagonal_add {R : Type*} [AddZeroClass R] (S : Matrix ι ι R) (δ : ι → R) :
    symCoords (S + diagonal δ) = symCoords S := by
  ext q; simp [symCoords, diagonal, ne_of_lt q.2]

/-- The model's off-diagonal entries are those of `Λ Λᵀ`, `Λ` real. -/
lemma symCoords_FAmodel (m : ℕ) :
    symCoords '' FAmodel ι m = Set.range (fun Λ : Matrix ι (Fin m) ℝ => symCoords (Λ * Λᵀ)) := by
  ext y; constructor
  · rintro ⟨S, ⟨Λ, δ, -, rfl⟩, rfl⟩; exact ⟨Λ, (symCoords_diagonal_add _ _).symm⟩
  · rintro ⟨Λ, rfl⟩
    exact ⟨Λ * Λᵀ + diagonal 1, ⟨Λ, 1, fun _ => one_pos, rfl⟩, symCoords_diagonal_add _ _⟩

lemma mul_transpose_symm {R : Type*} [CommSemiring R] {m : Type*} [Fintype m]
    (Λ : Matrix ι m R) (a b : ι) : (Λ * Λᵀ) a b = (Λ * Λᵀ) b a := by
  simp only [Matrix.mul_apply, transpose_apply, mul_comm]

/-- **`{c ≤ m}` is the set of patterns of `Λ Λᵀ`** over an algebraically closed field of
characteristic other than 2; hence `X_{ι,m}` is the closure of these patterns. -/
lemma minCompRank_le_iff_factor' {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (m : ℕ) : {p : SymIdx ι → K | minCompRank (toMatSym p) ≤ m} =
      Set.range (fun Λ : Matrix ι (Fin m) K => symCoords (Λ * Λᵀ)) := by
  ext p; constructor
  · intro hp
    obtain ⟨d, hd⟩ := exists_minCompRank (toMatSym p)
    set M := toMatSym p + diagonal d
    have hMs : Mᵀ = M := by
      ext a b
      rw [transpose_apply]
      simp only [M, Matrix.add_apply]
      rw [toMatSym_symm p b a]
      by_cases h : a = b
      · subst h; rfl
      · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
    obtain ⟨Λ, hΛ⟩ := exists_mul_transpose_eq h2 M hMs m (hd ▸ hp)
    refine ⟨Λ, ?_⟩
    ext q
    simp only [symCoords, hΛ, M]
    rw [Matrix.add_apply, diagonal_apply_ne _ (ne_of_lt q.2), add_zero, toMatSym_apply_lt _ q.2]
  · rintro ⟨Λ, rfl⟩
    show minCompRank (toMatSym (symCoords (Λ * Λᵀ))) ≤ m
    refine (minCompRank_le_of_offDiag _ (Λ * Λᵀ) (toMatSym_apply_self _) (fun a b hab => ?_)).trans
      ((rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp)))
    rcases lt_or_gt_of_ne hab with h | h
    · rw [toMatSym_apply_lt _ h]; rfl
    · rw [toMatSym_apply_gt _ h]; exact mul_transpose_symm Λ a b

lemma minCompRank_le_iff_factor (m : ℕ) :
    {p : SymIdx ι → ℂ | minCompRank (toMatSym p) ≤ m} =
      Set.range (fun Λ : Matrix ι (Fin m) ℂ => symCoords (Λ * Λᵀ)) :=
  minCompRank_le_iff_factor' two_ne_zero m

/-- `X_{ι,m}` is the Zariski closure of the patterns of `Λ Λᵀ` (`K` algebraically closed,
characteristic other than 2). -/
theorem Xvar_eq_closure_factors {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (m : ℕ) : Xvar (K := K) ι m =
      zariskiClosure (Set.range (fun Λ : Matrix ι (Fin m) K => symCoords (Λ * Λᵀ))) := by
  rw [Xvar, minCompRank_le_iff_factor' h2]

/-- Evaluation of a substituted polynomial. -/
lemma eval_aeval_subst {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ)
    (y : τ → ℂ) : eval y (aeval g f) = aeval (fun s => eval y (g s)) f := by
  rw [aeval_eq_bind₁]
  exact aeval_bind₁ y g f

/-- **Density of real `Λ`**: a polynomial vanishing on the patterns of `Λ Λᵀ` for real `Λ`
vanishes on them for complex `Λ`. -/
lemma dense_real_factors (m : ℕ) :
    Set.range (fun Λ : Matrix ι (Fin m) ℂ => symCoords (Λ * Λᵀ)) ⊆
      zariskiClosure (ofRealPt '' (symCoords '' FAmodel ι m)) := by
  rintro _ ⟨Λ, rfl⟩ f hf
  rw [mem_vanishingIdeal_iff] at hf
  set g : SymIdx ι → MvPolynomial (ι × Fin m) ℂ :=
    fun q => ∑ l, X (q.1.1, l) * X (q.1.2, l)
  have hg : ∀ L : ι × Fin m → ℂ, aeval (fun s => eval L (g s)) f =
      aeval (symCoords (Matrix.of (fun a l => L (a, l)) * (Matrix.of (fun a l => L (a, l)))ᵀ)) f := by
    intro L; congr 1; ext q; simp [g, symCoords, Matrix.mul_apply]
  have hF : aeval g f = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective ofReal_injective)
    intro L hL
    rw [eval_aeval_subst, hg, map_zero]
    choose r hr using fun i => (hL i (Set.mem_univ _))
    apply hf
    rw [symCoords_FAmodel]
    refine ⟨symCoords (Matrix.of (fun a l => r (a, l)) * (Matrix.of (fun a l => r (a, l)))ᵀ),
      ⟨_, rfl⟩, ?_⟩
    ext q
    simp [ofRealPt, symCoords, Matrix.mul_apply, hr]
  have := congrArg (eval (fun p : ι × Fin m => Λ p.1 p.2)) hF
  rw [eval_aeval_subst, hg, map_zero] at this
  exact this

lemma zariskiClosure_idem {σ : Type*} {K : Type*} [Field K] (S : Set (σ → K)) :
    zariskiClosure (zariskiClosure S) = zariskiClosure S :=
  Set.Subset.antisymm (zariskiClosure_subset_of_closed subset_rfl ⟨_, rfl⟩)
    (subset_zariskiClosure _)

/-- **The complex variety of `I_{p,m}` is `X_{p,m}` over `ℂ`.** -/
theorem zeroLocus_FAideal (m : ℕ) : zeroLocus ℂ (FAideal ι m) = Xvar (K := ℂ) ι m := by
  rw [FAideal, vanishingIdeal_ofReal, zeroLocus_real_eq_closure, Xvar,
    minCompRank_le_iff_factor]
  apply Set.Subset.antisymm
  · apply zariskiClosure_mono
    rintro _ ⟨y, hy, rfl⟩
    rw [symCoords_FAmodel] at hy
    obtain ⟨Λ, rfl⟩ := hy
    refine ⟨Matrix.of (fun a l => (Λ a l : ℂ)), ?_⟩
    ext q; simp [ofRealPt, symCoords, Matrix.mul_apply]
  · calc zariskiClosure _ ⊆ zariskiClosure (zariskiClosure (ofRealPt '' (symCoords '' FAmodel ι m))) :=
          zariskiClosure_mono (dense_real_factors m)
      _ = _ := zariskiClosure_idem _

/-- **The complex variety of `Σ_{|A| = t} I_{A,m}`**: the symmetric patterns `x` with
`x_A ∈ X_{A,m}` for every `|A| = t`. -/
theorem zeroLocus_sumIdeal (m t : ℕ) :
    zeroLocus ℂ (sumIdeal ι m t) =
      {z | ∀ A : Finset ι, A.card = t → restrictSym z A ∈ Xvar (K := ℂ) A m} := by
  ext z
  simp only [sumIdeal, FAidealOn, mem_zeroLocus_iSup, mem_zeroLocus_map_rename,
    zeroLocus_FAideal, Subtype.forall, Set.mem_setOf_eq]
  rfl

end Model

/-! ### Theorem 4 -/

/-- **Theorem 4** (under `ClosedRhoSym ℂ`): for every `m` and every `p ≥ 2m + 2`, the ideals
`I_{p,m}` and `Σ_{|A| = 2m+2} I_{A,m}` of `ℝ[ψ_ij : i < j]` have the same radical. -/
theorem theorem_4 (hC : ClosedRhoSym.{0, 0} ℂ) (m p : ℕ) (hp : 2 * m + 2 ≤ p) :
    (FAideal (Fin p) m).radical = (sumIdeal (Fin p) m (2 * m + 2)).radical := by
  rw [radical_eq_iff_zeroLocus_eq (K := ℂ), zeroLocus_FAideal, zeroLocus_sumIdeal]
  ext z
  exact theorem_3_sym hC m (by simpa using hp) z

/-- **Theorem 4, sharpness** (under `ClosedRhoSym ℂ`): for every `t ≤ 2m + 1`, the radicals of
`I_{2m+2,m}` and `Σ_{|A| = t} I_{A,m}` differ. So no number smaller than `2m + 2` works for
all larger `p`. -/
theorem theorem_4_sharp (hC : ClosedRhoSym.{0, 0} ℂ) (m t : ℕ) (ht : t ≤ 2 * m + 1) :
    (FAideal (Fin (2 * m + 2)) m).radical ≠ (sumIdeal (Fin (2 * m + 2)) m t).radical := by
  rw [Ne, radical_eq_iff_zeroLocus_eq (K := ℂ), zeroLocus_FAideal, zeroLocus_sumIdeal]
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sym_sharp hC m
  apply hnot
  rw [h]
  exact fun A hA => hsub A (hA ▸ ht)

end FreeDiagonal
