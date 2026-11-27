import FreeDiagonal.Variety.Lemma3Easy

/-!
# Lemma 3 in full, Theorem 3 and Corollary 5 (variety form), under `ClosedRho`

The converse direction of Lemma 3 needs that `{x : ρ(x) ≤ k}` is Zariski closed. The paper proves
this by projecting along `(ℙ¹)ⁿ`. Here it is the named hypothesis `ClosedRho K` (general
patterns) and `ClosedRhoSym K` (symmetric patterns), taken as explicit arguments.

* `Dvar_eq` / `Xvar_eq`: Lemma 3, `D_{n,k} = {ρ ≤ k}` and `X_{n,k} = {x symmetric : ρ ≤ k}`.
* `theorem_3` / `theorem_3_sym`: membership is decided by the sub-patterns on `2k + 2` indices
  (`n ≥ 2k + 2`), and `theorem_3_sharp` / `theorem_3_sym_sharp`: no smaller number works.
* `cutRankLE_iff_minorsVanish`: all cut ranks `≤ k` iff every `(k+1) × (k+1)` minor
  `det x[R, C]` with `R ∩ C = ∅` vanishes (any field).
* `corollary_5` / `corollary_5_sym`: Corollary 5 in variety form.
-/

open Matrix Finset MvPolynomial

universe u v

namespace FreeDiagonal

variable {K : Type u} [Field K]

/-! ### Zariski-closed sets -/

/-- A set of points is Zariski closed if it is the zero locus of an ideal. -/
def IsZariskiClosed {σ : Type*} (S : Set (σ → K)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ K), zeroLocus K I = S

lemma zariskiClosure_mono {σ : Type*} {S T : Set (σ → K)} (h : S ⊆ T) :
    zariskiClosure S ⊆ zariskiClosure T :=
  zeroLocus_anti_mono (vanishingIdeal_anti_mono h)

lemma zariskiClosure_subset_of_closed {σ : Type*} {S C : Set (σ → K)} (hSC : S ⊆ C)
    (hC : IsZariskiClosed C) : zariskiClosure S ⊆ C := by
  obtain ⟨I, rfl⟩ := hC
  exact (zariskiClosure_mono hSC).trans (zeroLocus_anti_mono (le_vanishingIdeal_zeroLocus I))

variable (K) in
/-- **The named hypothesis `ClosedRho` (general patterns).** For every finite index type `n` and
every `k`, the set of patterns with `ρ(x) ≤ k` is Zariski closed in `K^{OffIdx n}`. The paper
proves this for `K` algebraically closed, by projection along `(ℙ¹)ⁿ` (proof of Lemma 3). -/
def ClosedRho : Prop :=
  ∀ (n : Type v) [Fintype n] [DecidableEq n] (k : ℕ),
    IsZariskiClosed {p : OffIdx n → K | closRank (toMat p) ≤ k}

variable (K) in
/-- **The named hypothesis `ClosedRhoSym` (symmetric patterns).** For every finite linearly
ordered index type `n` and every `k`, the set of symmetric patterns with `ρ(x) ≤ k` is Zariski
closed in `K^{SymIdx n}`. -/
def ClosedRhoSym : Prop :=
  ∀ (n : Type v) [Fintype n] [LinearOrder n] (k : ℕ),
    IsZariskiClosed {p : SymIdx n → K | closRank (toMatSym p) ≤ k}

/-! ### Lemma 3 -/

/-- **Lemma 3, general patterns**: `D_{n,k} = {x : ρ(x) ≤ k}`. -/
theorem Dvar_eq [Infinite K] (hC : ClosedRho.{u, v} K) (n : Type v) [Fintype n] [DecidableEq n]
    (k : ℕ) : Dvar n k = {p : OffIdx n → K | closRank (toMat p) ≤ k} := by
  apply Set.Subset.antisymm
  · exact zariskiClosure_subset_of_closed
      (fun p (hp : minCompRank (toMat p) ≤ k) => (closRank_le_minCompRank _).trans hp) (hC n k)
  · exact fun p hp => mem_Dvar_of_closRank_le k p hp

/-- **Lemma 3, symmetric patterns**: `X_{n,k} = {x symmetric : ρ(x) ≤ k}`. -/
theorem Xvar_eq [Infinite K] (hC : ClosedRhoSym.{u, v} K) (n : Type v) [Fintype n] [LinearOrder n]
    (k : ℕ) : Xvar n k = {p : SymIdx n → K | closRank (toMatSym p) ≤ k} := by
  apply Set.Subset.antisymm
  · exact zariskiClosure_subset_of_closed
      (fun p (hp : minCompRank (toMatSym p) ≤ k) => (closRank_le_minCompRank _).trans hp) (hC n k)
  · exact fun p hp => mem_Xvar_of_closRank_le k p hp

/-! ### Restriction to a set of indices -/

section Restrict

variable {n : Type v} [Fintype n]

/-- The sub-pattern `x_T` in coordinates. -/
def restrictOff [DecidableEq n] (p : OffIdx n → K) (T : Finset n) : OffIdx T → K :=
  fun q => p ⟨((q.1.1 : n), (q.1.2 : n)), fun h => q.2 (Subtype.ext h)⟩

lemma toMat_restrictOff [DecidableEq n] (p : OffIdx n → K) (T : Finset n) :
    toMat (restrictOff p T) = subPattern (toMat p) T := by
  ext a b
  by_cases h : a = b
  · subst h; simp [toMat_apply_self, subPattern]
  · have h' : (a : n) ≠ b := fun e => h (Subtype.ext e)
    simp [subPattern, toMat_apply_ne _ h, toMat_apply_ne _ h', restrictOff]

/-- The symmetric sub-pattern `x_T` in coordinates. -/
def restrictSym [LinearOrder n] (p : SymIdx n → K) (T : Finset n) : SymIdx T → K :=
  fun q => p ⟨((q.1.1 : n), (q.1.2 : n)), q.2⟩

lemma toMatSym_restrictSym [LinearOrder n] (p : SymIdx n → K) (T : Finset n) :
    toMatSym (restrictSym p T) = subPattern (toMatSym p) T := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · have h' : (a : n) < b := h
    simp only [subPattern, submatrix_apply, toMatSym_apply_lt _ h, toMatSym_apply_lt _ h',
      restrictSym]
  · subst h; simp [toMatSym_apply_self, subPattern]
  · have h' : (b : n) < a := h
    simp only [subPattern, submatrix_apply, toMatSym_apply_gt _ h, toMatSym_apply_gt _ h',
      restrictSym]

end Restrict

/-! ### Theorem 3 -/

lemma closRank_iff_card_eq {n : Type v} [Fintype n] [DecidableEq n] (x : Matrix n n K) (k N : ℕ)
    (hN : N ≤ Fintype.card n) (hthr : closRank x ≤ k ↔
      ∀ T : Finset n, T.card ≤ N → closRank (subPattern x T) ≤ k) :
    closRank x ≤ k ↔ ∀ T : Finset n, T.card = N → closRank (subPattern x T) ≤ k := by
  rw [hthr]
  constructor
  · exact fun h T hT => h T hT.le
  · intro h T hT
    obtain ⟨T', hTT', hT'⟩ := Finset.exists_superset_card_eq hT hN
    exact (closRank_subPattern_mono x hTT').trans (h T' hT')

/-- **Theorem 3, general patterns** (under `ClosedRho`): for `n ≥ 2k + 2`, `x ∈ D_{n,k}` iff
`x_T ∈ D_{T,k}` for every `T` with `|T| = 2k + 2`. -/
theorem theorem_3 [Infinite K] (hC : ClosedRho.{u, v} K) {n : Type v} [Fintype n] [DecidableEq n]
    (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) (p : OffIdx n → K) :
    p ∈ Dvar n k ↔ ∀ T : Finset n, T.card = 2 * k + 2 → restrictOff p T ∈ Dvar T k := by
  rw [Dvar_eq hC]
  simp only [Dvar_eq hC, Set.mem_setOf_eq, toMat_restrictOff]
  exact closRank_iff_card_eq _ k _ hn (closure_threshold _ k)

/-- **Theorem 3, symmetric patterns** (under `ClosedRhoSym`): for `n ≥ 2k + 2`, `x ∈ X_{n,k}` iff
`x_T ∈ X_{T,k}` for every `T` with `|T| = 2k + 2`. -/
theorem theorem_3_sym [Infinite K] (hC : ClosedRhoSym.{u, v} K) {n : Type v} [Fintype n]
    [LinearOrder n] (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) (p : SymIdx n → K) :
    p ∈ Xvar n k ↔ ∀ T : Finset n, T.card = 2 * k + 2 → restrictSym p T ∈ Xvar T k := by
  rw [Xvar_eq hC]
  simp only [Xvar_eq hC, Set.mem_setOf_eq, toMatSym_restrictSym]
  convert closRank_iff_card_eq (toMatSym p) k _ hn (closure_threshold _ k)

/-! ### Sharpness -/

/-- `ρ` does not depend on the decidable-equality instance. -/
lemma closRank_inst_eq {m : Type*} [Fintype m] (i j : DecidableEq m) (x : Matrix m m K) :
    (letI := i; closRank x) = (letI := j; closRank x) := by
  obtain rfl := Subsingleton.elim i j; rfl

/-- The coordinates of a matrix with zero diagonal. -/
lemma toMat_offCoords {n : Type v} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (hM : ∀ a, M a a = 0) : toMat (offCoords M) = M := by
  ext a b
  by_cases h : a = b
  · subst h; simp [toMat_apply_self, hM]
  · simp [toMat_apply_ne _ h, offCoords]

lemma matching_diag (k : ℕ) (a : Fin (k + 1) × Bool) : matching K k a a = 0 := by
  simp [matching]

lemma matching_symm (k : ℕ) (a b : Fin (k + 1) × Bool) : matching K k a b = matching K k b a := by
  simp only [matching, eq_comm, ne_comm]

/-- **Theorem 3, sharpness, general patterns**: the perfect matching on `2k + 2` indices is not in
`D_{2k+2,k}` (under `ClosedRho`), while all its sub-patterns on at most `2k + 1` indices are in
their varieties (no hypothesis). -/
theorem theorem_3_sharp [Infinite K] (hC : ClosedRho.{u, 0} K) (k : ℕ) :
    offCoords (matching K k) ∉ Dvar (Fin (k + 1) × Bool) k ∧
      ∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        restrictOff (offCoords (matching K k)) T ∈ Dvar T k := by
  have hm := toMat_offCoords (matching K k) (matching_diag k)
  obtain ⟨-, hnot, -, hsub⟩ := closure_threshold_sharp K k
  refine ⟨fun h => hnot ?_, fun T hT => mem_Dvar_of_closRank_le k _ ?_⟩
  · rw [Dvar_eq hC] at h; simpa [hm] using h
  · rw [toMat_restrictOff, hm]; exact hsub T hT

/-- The matching on `2k + 2` indices, transported to `Fin (2k + 2)`. -/
noncomputable def matchEquiv (k : ℕ) : Fin (k + 1) × Bool ≃ Fin (2 * k + 2) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_prod]; ring)

/-- The perfect matching as a symmetric pattern on `Fin (2k + 2)`. -/
noncomputable def matchSym (k : ℕ) : SymIdx (Fin (2 * k + 2)) → K :=
  fun q => matching K k ((matchEquiv k).symm q.1.1) ((matchEquiv k).symm q.1.2)

lemma toMatSym_matchSym (k : ℕ) (a b : Fin (2 * k + 2)) :
    toMatSym (matchSym (K := K) k) a b =
      matching K k ((matchEquiv k).symm a) ((matchEquiv k).symm b) := by
  rcases lt_trichotomy a b with h | h | h
  · rw [toMatSym_apply_lt _ h]; rfl
  · subst h; rw [toMatSym_apply_self, matching_diag]
  · rw [toMatSym_apply_gt _ h, matchSym, matching_symm]

/-- **Theorem 3, sharpness, symmetric patterns**: the perfect matching on `2k + 2` indices is not
in `X_{2k+2,k}` (under `ClosedRhoSym`), while all its sub-patterns on at most `2k + 1` indices are
in their varieties (no hypothesis). -/
theorem theorem_3_sym_sharp [Infinite K] (hC : ClosedRhoSym.{u, 0} K) (k : ℕ) :
    matchSym (K := K) k ∉ Xvar (Fin (2 * k + 2)) k ∧
      ∀ T : Finset (Fin (2 * k + 2)), T.card ≤ 2 * k + 1 →
        restrictSym (matchSym (K := K) k) T ∈ Xvar T k := by
  obtain ⟨-, hnot, -, hsub⟩ := closure_threshold_sharp K k
  set e := matchEquiv k
  refine ⟨fun h => hnot ?_, fun T hT => mem_Xvar_of_closRank_le k _ ?_⟩
  · rw [Xvar_eq hC] at h
    refine le_trans (closRank_le_of_embedding (toMatSym (matchSym (K := K) k)) (matching K k) e
      e.injective (fun a b _ => ?_)) h
    rw [toMatSym_matchSym, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rw [toMatSym_restrictSym]
    set T' : Finset (Fin (k + 1) × Bool) := T.map e.symm.toEmbedding
    have hT' : T'.card ≤ 2 * k + 1 := by simpa [T'] using hT
    have key := le_trans (closRank_le_of_embedding (subPattern (matching K k) T')
      (subPattern (toMatSym (matchSym (K := K) k)) T)
      (fun a : T => (⟨e.symm a, by simp [T']⟩ : T')) (fun a b hab => ?_) (fun a b _ => ?_))
      (hsub T' hT')
    · convert key using 1
      exact closRank_inst_eq _ _ _
    · apply Subtype.ext
      have := congrArg (fun z : T' => e (z : Fin (k + 1) × Bool)) hab
      simpa using this
    · simp [subPattern, toMatSym_matchSym]; rfl

/-- "`2k + 2` cannot be replaced by a smaller number", symmetric form: for `N ≤ 2k + 1` the
criterion "all sub-patterns on `N` indices lie in their varieties" does not imply membership. -/
theorem theorem_3_sym_not_smaller [Infinite K] (hC : ClosedRhoSym.{u, 0} K) (k N : ℕ)
    (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : SymIdx (Fin (2 * k + 2)) → K,
      (∀ T : Finset (Fin (2 * k + 2)), T.card = N → restrictSym p T ∈ Xvar T k) →
        p ∈ Xvar (Fin (2 * k + 2)) k := by
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sym_sharp hC k
  exact hnot (h _ (fun T hT => hsub T (hT ▸ hN)))

/-- "`2k + 2` cannot be replaced by a smaller number", general form. -/
theorem theorem_3_not_smaller [Infinite K] (hC : ClosedRho.{u, 0} K) (k N : ℕ)
    (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : OffIdx (Fin (k + 1) × Bool) → K,
      (∀ T : Finset (Fin (k + 1) × Bool), T.card = N → restrictOff p T ∈ Dvar T k) →
        p ∈ Dvar (Fin (k + 1) × Bool) k := by
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sharp hC k
  exact hnot (h _ (fun T hT => hsub T (hT ▸ hN)))

/-! ### Minors and cut ranks -/

/-- Every `(k+1) × (k+1)` minor `det x[R, C]` with disjoint row and column sets vanishes. Rows and
columns are given by injective maps from `Fin (k + 1)`. -/
def MinorsVanish {n : Type*} (x : Matrix n n K) (k : ℕ) : Prop :=
  ∀ r c : Fin (k + 1) → n, Function.Injective r → Function.Injective c → (∀ i j, r i ≠ c j) →
    (x.submatrix r c).det = 0

lemma det_ne_zero_of_rank {m : Type*} [Fintype m] [DecidableEq m] (S : Matrix m m K)
    (h : Fintype.card m ≤ S.rank) : S.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hker : 0 < Module.finrank K (LinearMap.ker S.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, by simpa using hv⟩, by simpa using hv0⟩
  have := rank_add_finrank_ker S
  omega

/-- **All cut ranks `≤ k` iff all off-diagonal `(k+1)`-minors vanish** (any field). -/
theorem cutRankLE_iff_minorsVanish {n : Type*} [Fintype n] [DecidableEq n] (x : Matrix n n K)
    (k : ℕ) : CutRankLE x k ↔ MinorsVanish x k := by
  constructor
  · intro h r c _ _ hrc
    by_contra hdet
    set A : Finset n := univ.image r
    have hcA : ∀ j, c j ∈ Aᶜ := by
      intro j; simp only [A, mem_compl, mem_image, mem_univ, true_and, not_exists]
      exact fun i => hrc i j
    have heq : x.submatrix r c =
        (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).submatrix
          (fun i => ⟨r i, by simp [A]⟩) (fun j => ⟨c j, hcA j⟩) := rfl
    have h1 := rank_of_det_ne_zero hdet
    have h2 : (x.submatrix r c).rank ≤ k := by
      rw [heq]; exact (rank_submatrix_le _ _ _).trans (h A)
    simp at h1; omega
  · intro h A
    by_contra hlt
    rw [not_le] at hlt
    set M := x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))
    obtain ⟨R, C, hR, hC, hRC⟩ := exists_small_submatrix M (k + 1) hlt
    set N := M.submatrix (fun a : R => (a : A)) (fun b : C => (b : ↥(Aᶜ)))
    have hNR : N.rank ≤ R.card := by simpa using rank_le_card_height N
    have hNC : N.rank ≤ C.card := by simpa using rank_le_card_width N
    have eR : Fintype.card R = k + 1 := by simp; omega
    have eC : Fintype.card C = k + 1 := by simp; omega
    set fR := Fintype.equivFinOfCardEq eR
    set fC := Fintype.equivFinOfCardEq eC
    have hdet := h (fun i => (((fR.symm i : R) : A) : n)) (fun j => (((fC.symm j : C) : ↥(Aᶜ)) : n))
      (fun i i' e => fR.symm.injective (Subtype.ext (Subtype.ext e)))
      (fun j j' e => fC.symm.injective (Subtype.ext (Subtype.ext e)))
      (fun i j e => by
        have h1 := ((fR.symm i : R) : A).2
        have h2 := ((fC.symm j : C) : ↥(Aᶜ)).2
        rw [mem_compl] at h2; exact h2 (e ▸ h1))
    have hS : (N.submatrix fR.symm fC.symm).rank = N.rank := rank_submatrix N fR.symm fC.symm
    exact det_ne_zero_of_rank (N.submatrix fR.symm fC.symm) (by simp; omega) hdet

/-! ### Corollary 5, variety form -/

/-- **Corollary 5, general patterns** (under `ClosedRho`): for `n ≥ 2k + 1`, `x ∈ D_{n,k}` iff
every off-diagonal `(k+1)`-minor vanishes and `x_T ∈ D_{T,k}` for every `T` with `|T| = 2k + 1`. -/
theorem corollary_5 [Infinite K] (hC : ClosedRho.{u, v} K) {n : Type v} [Fintype n] [DecidableEq n]
    (k : ℕ) (hn : 2 * k + 1 ≤ Fintype.card n) (p : OffIdx n → K) :
    p ∈ Dvar n k ↔ MinorsVanish (toMat p) k ∧
      ∀ T : Finset n, T.card = 2 * k + 1 → restrictOff p T ∈ Dvar T k := by
  rw [Dvar_eq hC, ← cutRankLE_iff_minorsVanish]
  simp only [Dvar_eq hC, Set.mem_setOf_eq, toMat_restrictOff]
  exact closure_corC _ k hn

/-- **Corollary 5, symmetric patterns** (under `ClosedRhoSym`). -/
theorem corollary_5_sym [Infinite K] (hC : ClosedRhoSym.{u, v} K) {n : Type v} [Fintype n]
    [LinearOrder n] (k : ℕ) (hn : 2 * k + 1 ≤ Fintype.card n) (p : SymIdx n → K) :
    p ∈ Xvar n k ↔ MinorsVanish (toMatSym p) k ∧
      ∀ T : Finset n, T.card = 2 * k + 1 → restrictSym p T ∈ Xvar T k := by
  rw [Xvar_eq hC, ← cutRankLE_iff_minorsVanish]
  simp only [Xvar_eq hC, Set.mem_setOf_eq, toMatSym_restrictSym]
  convert closure_corC (toMatSym p) k hn

end FreeDiagonal
