import FreeDiagonal.StatisticalFactorAnalysis.Gram
import FreeDiagonal.Witness.Restricted

/-!
# The factor analysis model, fits and references

* `InModel m Sig` (`Σ ∈ F_{n,m}`): `Σ = D + Λ Λᵀ` with `D` diagonal with positive entries and `Λ`
  a real `n × m` matrix (the model of Drton and Xiao); `InWeakModel`: `D ≥ 0`.
* `IsFit m Sig G`: `G` positive semidefinite of rank `≤ m`, `G_ij = Σ_ij` (`i ≠ j`),
  `G_ii < Σ_ii`; `IsWeakFit`: `G_ii ≤ Σ_ii`.
* `IsReference Sig G`: `G` real symmetric, `G_ij = Σ_ij` (`i ≠ j`), `0 ≤ G_ii < Σ_ii`;
  `IsWeakReference`: `0 ≤ G_ii ≤ Σ_ii`.
* `IsCompletionIn A Sig G`: `G` symmetric, `G_ij = Σ_ij` (`i ≠ j`), `G_ii ∈ A i` (admissible sets).
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The `m`-factor model** `F_{n,m}`: `Σ = D + Λ Λᵀ` with `D` a diagonal matrix with positive
diagonal entries and `Λ` a real `n × m` matrix. -/
def InModel (m : ℕ) (Sig : Matrix n n ℝ) : Prop :=
  ∃ (D : n → ℝ) (Λ : Matrix n (Fin m) ℝ), (∀ i, 0 < D i) ∧ Sig = diagonal D + Λ * Λᵀ

/-- **The weak `m`-factor model** `F̄_{n,m}`: as `InModel` with `D ≥ 0`. -/
def InWeakModel (m : ℕ) (Sig : Matrix n n ℝ) : Prop :=
  ∃ (D : n → ℝ) (Λ : Matrix n (Fin m) ℝ), (∀ i, 0 ≤ D i) ∧ Sig = diagonal D + Λ * Λᵀ

/-- **Fit**: `G` positive semidefinite of rank at most `m`, with the off-diagonal entries of `Σ`
and `G_ii < Σ_ii` for all `i`. -/
def IsFit (m : ℕ) (Sig G : Matrix n n ℝ) : Prop :=
  G.PosSemidef ∧ G.rank ≤ m ∧ (∀ i j, i ≠ j → G i j = Sig i j) ∧ ∀ i, G i i < Sig i i

/-- **Weak fit**: as `IsFit` with `G_ii ≤ Σ_ii`. -/
def IsWeakFit (m : ℕ) (Sig G : Matrix n n ℝ) : Prop :=
  G.PosSemidef ∧ G.rank ≤ m ∧ (∀ i j, i ≠ j → G i j = Sig i j) ∧ ∀ i, G i i ≤ Sig i i

/-- **Reference**: `G` real symmetric (not necessarily positive semidefinite), with the
off-diagonal entries of `Σ` and `0 ≤ G_ii < Σ_ii` for all `i`. -/
def IsReference (Sig G : Matrix n n ℝ) : Prop :=
  G.IsSymm ∧ (∀ i j, i ≠ j → G i j = Sig i j) ∧ ∀ i, 0 ≤ G i i ∧ G i i < Sig i i

/-- **Weak reference**: as `IsReference` with `0 ≤ G_ii ≤ Σ_ii`. -/
def IsWeakReference (Sig G : Matrix n n ℝ) : Prop :=
  G.IsSymm ∧ (∀ i j, i ≠ j → G i j = Sig i j) ∧ ∀ i, 0 ≤ G i i ∧ G i i ≤ Sig i i

/-- A symmetric completion of the off-diagonal entries of `Σ` with each diagonal entry `G_ii` in
a prescribed set `A i`. -/
def IsCompletionIn (A : n → Set ℝ) (Sig G : Matrix n n ℝ) : Prop :=
  G.IsSymm ∧ (∀ i j, i ≠ j → G i j = Sig i j) ∧ ∀ i, G i i ∈ A i

/-- `Σ` has a positive semidefinite completion of rank at most `m` with diagonal in `A`. -/
def HasFitIn (m : ℕ) (A : n → Set ℝ) (Sig : Matrix n n ℝ) : Prop :=
  ∃ G, IsCompletionIn A Sig G ∧ G.PosSemidef ∧ G.rank ≤ m

/-- The admissible sets of references, `[0, Σ_ii)`. -/
def refSets (Sig : Matrix n n ℝ) : n → Set ℝ := fun i => Set.Ico 0 (Sig i i)

/-- The admissible sets of weak references, `[0, Σ_ii]`. -/
def weakRefSets (Sig : Matrix n n ℝ) : n → Set ℝ := fun i => Set.Icc 0 (Sig i i)

omit [Fintype n] [DecidableEq n] in
lemma isReference_iff (Sig G : Matrix n n ℝ) :
    IsReference Sig G ↔ IsCompletionIn (refSets Sig) Sig G := by
  simp [IsReference, IsCompletionIn, refSets, Set.mem_Ico]

omit [Fintype n] [DecidableEq n] in
lemma isWeakReference_iff (Sig G : Matrix n n ℝ) :
    IsWeakReference Sig G ↔ IsCompletionIn (weakRefSets Sig) Sig G := by
  simp [IsWeakReference, IsCompletionIn, weakRefSets, Set.mem_Icc]

omit [Fintype n] [DecidableEq n] in
lemma PosSemidef.isSymm' {G : Matrix n n ℝ} (h : G.PosSemidef) : G.IsSymm := by
  have := h.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

/-- A fit is a reference of rank at most `m`. -/
lemma isFit_iff (m : ℕ) (Sig G : Matrix n n ℝ) :
    IsFit m Sig G ↔ IsReference Sig G ∧ G.PosSemidef ∧ G.rank ≤ m := by
  constructor
  · rintro ⟨hp, hr, ho, hd⟩
    exact ⟨⟨PosSemidef.isSymm' hp, ho, fun i => ⟨hp.diag_nonneg, hd i⟩⟩, hp, hr⟩
  · rintro ⟨⟨-, ho, hd⟩, hp, hr⟩
    exact ⟨hp, hr, ho, fun i => (hd i).2⟩

lemma isWeakFit_iff (m : ℕ) (Sig G : Matrix n n ℝ) :
    IsWeakFit m Sig G ↔ IsWeakReference Sig G ∧ G.PosSemidef ∧ G.rank ≤ m := by
  constructor
  · rintro ⟨hp, hr, ho, hd⟩
    exact ⟨⟨PosSemidef.isSymm' hp, ho, fun i => ⟨hp.diag_nonneg, hd i⟩⟩, hp, hr⟩
  · rintro ⟨⟨-, ho, hd⟩, hp, hr⟩
    exact ⟨hp, hr, ho, fun i => (hd i).2⟩

lemma exists_fit_iff_hasFitIn (m : ℕ) (Sig : Matrix n n ℝ) :
    (∃ G, IsFit m Sig G) ↔ HasFitIn m (refSets Sig) Sig := by
  simp only [isFit_iff, isReference_iff, HasFitIn]

lemma exists_weakFit_iff_hasFitIn (m : ℕ) (Sig : Matrix n n ℝ) :
    (∃ G, IsWeakFit m Sig G) ↔ HasFitIn m (weakRefSets Sig) Sig := by
  simp only [isWeakFit_iff, isWeakReference_iff, HasFitIn]

end Defs

section Factor

variable {n : Type*} [Fintype n]

/-- A positive semidefinite real matrix of rank at most `m` is `Λ Λᵀ` with `Λ` of width `m`. -/
theorem exists_eq_mul_transpose {G : Matrix n n ℝ} (hG : G.PosSemidef) {m : ℕ} (hm : G.rank ≤ m) :
    ∃ Λ : Matrix n (Fin m) ℝ, G = Λ * Λᵀ := by
  classical
  obtain ⟨k, v, hv⟩ := exists_gram_of_posSemidef hG
  set W := span ℝ (Set.range v) with hW
  set v' : n → W := fun a => ⟨v a, subset_span ⟨a, rfl⟩⟩ with hv'
  have hgram : gram ℝ v' = G := by
    rw [← hv]; ext a b; simp [gram_apply, v']
  have hr : finrank ℝ W ≤ m := by
    have := rank_gram v; rw [hv] at this
    change finrank ℝ (span ℝ (Set.range v)) ≤ m; omega
  set b := stdOrthonormalBasis ℝ W
  set M : Matrix (Fin (finrank ℝ W)) n ℝ := of fun j a => b.repr (v' a) j with hM
  have hGM : G = Mᵀ * M := by
    rw [← hgram, gram_eq_conjTranspose_mul b v', conjTranspose_eq_transpose_of_trivial]
  set P : Matrix (Fin (finrank ℝ W)) (Fin m) ℝ :=
    of fun j k => if k = Fin.castLE hr j then 1 else 0 with hP
  have hPP : P * Pᵀ = 1 := by
    ext j j'
    simp only [hP, Matrix.mul_apply, transpose_apply, of_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
    by_cases h : j = j'
    · subst h; simp
    · have : Fin.castLE hr j' ≠ Fin.castLE hr j := fun e => h (Fin.castLE_injective hr e).symm
      simp [h, this]
  refine ⟨Mᵀ * P, ?_⟩
  rw [Matrix.transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc P,
    hPP, Matrix.one_mul, hGM]

omit [Fintype n] in
lemma posSemidef_mul_transpose {k : Type*} [Fintype k] (Λ : Matrix n k ℝ) :
    (Λ * Λᵀ).PosSemidef := by
  have := posSemidef_self_mul_conjTranspose Λ
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma rank_mul_transpose_le {m : ℕ} (Λ : Matrix n (Fin m) ℝ) : (Λ * Λᵀ).rank ≤ m :=
  (rank_mul_le_left _ _).trans ((rank_le_card_width Λ).trans (by simp))

end Factor

section Equiv

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`Σ ∈ F_{n,m}` iff `Σ` has a fit.** -/
theorem inModel_iff_exists_fit (m : ℕ) (Sig : Matrix n n ℝ) :
    InModel m Sig ↔ ∃ G, IsFit m Sig G := by
  constructor
  · rintro ⟨D, Λ, hD, rfl⟩
    refine ⟨Λ * Λᵀ, posSemidef_mul_transpose Λ, rank_mul_transpose_le Λ, ?_, ?_⟩
    · intro i j hij; simp [diagonal_apply_ne _ hij]
    · intro i; simp [hD i]
  · rintro ⟨G, hp, hr, ho, hd⟩
    obtain ⟨Λ, hΛ⟩ := exists_eq_mul_transpose hp hr
    refine ⟨fun i => Sig i i - G i i, Λ, fun i => by linarith [hd i], ?_⟩
    rw [← hΛ]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, ho i j h]

/-- **`Σ ∈ F̄_{n,m}` iff `Σ` has a weak fit.** -/
theorem inWeakModel_iff_exists_weakFit (m : ℕ) (Sig : Matrix n n ℝ) :
    InWeakModel m Sig ↔ ∃ G, IsWeakFit m Sig G := by
  constructor
  · rintro ⟨D, Λ, hD, rfl⟩
    refine ⟨Λ * Λᵀ, posSemidef_mul_transpose Λ, rank_mul_transpose_le Λ, ?_, ?_⟩
    · intro i j hij; simp [diagonal_apply_ne _ hij]
    · intro i; simp [hD i]
  · rintro ⟨G, hp, hr, ho, hd⟩
    obtain ⟨Λ, hΛ⟩ := exists_eq_mul_transpose hp hr
    refine ⟨fun i => Sig i i - G i i, Λ, fun i => by linarith [hd i], ?_⟩
    rw [← hΛ]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, ho i j h]

lemma InModel.inWeakModel {m : ℕ} {Sig : Matrix n n ℝ} (h : InModel m Sig) :
    InWeakModel m Sig := by
  obtain ⟨D, Λ, hD, e⟩ := h
  exact ⟨D, Λ, fun i => (hD i).le, e⟩

/-- Members of the model are positive definite. -/
lemma InModel.posDef {m : ℕ} {Sig : Matrix n n ℝ} (h : InModel m Sig) : Sig.PosDef := by
  obtain ⟨D, Λ, hD, rfl⟩ := h
  exact (PosDef.diagonal hD).add_posSemidef (posSemidef_mul_transpose Λ)

/-- **Principal submatrices of members are members.** -/
lemma InModel.sub {m : ℕ} {Sig : Matrix n n ℝ} (h : InModel m Sig) (T : Finset n) :
    InModel m (FreeDiagonal.subPattern Sig T) := by
  rw [inModel_iff_exists_fit] at h ⊢
  obtain ⟨G, hp, hr, ho, hd⟩ := h
  refine ⟨FreeDiagonal.subPattern G T, hp.submatrix _, (rank_submatrix_le _ _ _).trans hr, ?_, fun a => hd a⟩
  intro a b hab
  exact ho a b (fun e => hab (Subtype.ext e))

lemma InWeakModel.sub {m : ℕ} {Sig : Matrix n n ℝ} (h : InWeakModel m Sig)
    (T : Finset n) : InWeakModel m (FreeDiagonal.subPattern Sig T) := by
  rw [inWeakModel_iff_exists_weakFit] at h ⊢
  obtain ⟨G, hp, hr, ho, hd⟩ := h
  refine ⟨FreeDiagonal.subPattern G T, hp.submatrix _, (rank_submatrix_le _ _ _).trans hr, ?_, fun a => hd a⟩
  intro a b hab
  exact ho a b (fun e => hab (Subtype.ext e))

end Equiv

section TestSize

/-- `b` is a **valid test size** for the `m`-factor model: for every `N`, a symmetric `N × N`
real matrix `Σ` lies in `F_{N,m}` iff `Σ_T ∈ F_{|T|,m}` for every `T` with `|T| ≤ b`. The test
size `b_m` of the paper is the least valid `b` (`IsLeast {b | IsTestSize m b} b_m`). -/
def IsTestSize (m b : ℕ) : Prop :=
  ∀ (N : ℕ) (Sig : Matrix (Fin N) (Fin N) ℝ), Sig.IsSymm →
    (InModel m Sig ↔ ∀ T : Finset (Fin N), T.card ≤ b → InModel m (FreeDiagonal.subPattern Sig T))

/-- `b` is a valid test size for the weak `m`-factor model. -/
def IsWeakTestSize (m b : ℕ) : Prop :=
  ∀ (N : ℕ) (Sig : Matrix (Fin N) (Fin N) ℝ), Sig.IsSymm →
    (InWeakModel m Sig ↔
      ∀ T : Finset (Fin N), T.card ≤ b → InWeakModel m (FreeDiagonal.subPattern Sig T))

end TestSize

end FreeDiagonal.StatisticalFactorAnalysis
