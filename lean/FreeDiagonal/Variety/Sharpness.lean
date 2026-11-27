import FreeDiagonal.Variety.Theorem4

/-!
# Sharpness of Theorems 3 and 4 with no hypothesis, and for every `n ≥ 2k + 2`

The sharpness halves of Theorems 3 and 4 of the closure-threshold paper were stated under
`ClosedRho` / `ClosedRhoSym` / `ProjClosed` (`theorem_3_sharp`, `theorem_3_sym_sharp`,
`theorem_4_sharp` and the `paper_*` front doors). They need no hypothesis. The reason is one
fact over any field:

* `cutRankLE_of_mem_Dvar`, `cutRankLE_of_mem_Xvar`: every point of `D_{n,k}` or `X_{n,k}` has all
  cut ranks `≤ k`. The off-diagonal `(k+1)`-minors are polynomials in the coordinates that vanish
  on `{c ≤ k}`, hence on its Zariski closure.
* `not_mem_Dvar_of_det_ne_zero`, `not_mem_Xvar_of_det_ne_zero`: so one non-zero off-diagonal
  `(k+1)`-minor keeps a pattern out of the variety.

This file proves, with no hypothesis beyond `K` infinite:

1. at `n = 2k + 2`, the statements of `theorem_3_sharp`, `theorem_3_sym_sharp` and
   `theorem_4_sharp` (`theorem_3_sharp_noHyp`, `theorem_3_sym_sharp_noHyp`,
   `theorem_4_sharp_noHyp`); the proofs adapt those of the audit of 25 Nov 2026
   (`audit_2026-11-25_blind/minimal_project/Audit/Reconcile3.lean`, `Reconcile4.lean`);
2. for EVERY index set with `n ≥ 2k + 2` indices ("reading 2" of the sentence "2k+2 cannot be
   replaced by a smaller number"): the padded matching `padMatching k f` (the perfect matching on
   `2k + 2` of the indices, all other off-diagonal entries zero) lies in neither variety, while
   all its sub-patterns on at most `2k + 1` indices lie in their varieties
   (`theorem_3_sharp_every_n`, `theorem_3_sym_sharp_every_n`, `theorem_3_sharp_every_n_both`,
   and the "no smaller subset size decides membership" forms `theorem_3_not_smaller_every_n`,
   `theorem_3_sym_not_smaller_every_n`);
3. as a by-product, Theorem 4's sharpness at every `p ≥ 2m + 2` (`theorem_4_sharp_every_p`).

The sub-pattern bound in 2 is direct, not via a padding lemma: on `T` with `|T| ≤ 2k + 1` at most
`k` matched pairs lie inside `T`; deleting one endpoint of each leaves a pattern with zero
off-diagonal entries, so `ρ(x_T) ≤ k` (`closRank_subPattern_padMatching_le`).
-/

open Matrix Finset MvPolynomial

namespace FreeDiagonal

variable {K : Type*} [Field K]

/-! ### Points of the varieties have all cut ranks `≤ k` (any field, no hypothesis) -/

section CutRanks

/-- A polynomial vanishing on `S` vanishes on the Zariski closure of `S`. -/
lemma aeval_eq_zero_of_mem_zariskiClosure {σ : Type*} {S : Set (σ → K)} {p : σ → K}
    (hp : p ∈ zariskiClosure S) (f : MvPolynomial σ K) (hf : ∀ q ∈ S, aeval q f = 0) :
    aeval p f = 0 :=
  (mem_zeroLocus_iff.1 hp) f (mem_vanishingIdeal_iff.2 hf)

/-- Patterns with `c ≤ k` have all cut ranks `≤ k`. -/
lemma cutRankLE_of_minCompRank_le {n : Type*} [Fintype n] [DecidableEq n] (x : Matrix n n K)
    (k : ℕ) (h : minCompRank x ≤ k) : CutRankLE x k := fun A =>
  (cutRank_le_closRank x A).trans ((closRank_le_minCompRank x).trans h)

/-- The minor `det x[r, c]` (`r`, `c` with disjoint images) as a polynomial in the coordinates
of a pattern. -/
noncomputable def offMinorPoly {n : Type*} {k : ℕ} (r c : Fin (k + 1) → n) (h : ∀ i j, r i ≠ c j) :
    MvPolynomial (OffIdx n) K :=
  (Matrix.of fun a b => (X ⟨(r a, c b), h a b⟩ : MvPolynomial (OffIdx n) K)).det

lemma aeval_offMinorPoly {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (r c : Fin (k + 1) → n)
    (h : ∀ i j, r i ≠ c j) (p : OffIdx n → K) :
    aeval p (offMinorPoly (K := K) r c h) = ((toMat p).submatrix r c).det := by
  rw [offMinorPoly, ← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  rw [submatrix_apply, toMat_apply_ne _ (h a b)]
  simp [RingHom.mapMatrix_apply]

/-- **Every point of `D_{n,k}` has all cut ranks `≤ k`** (any field, no hypothesis). -/
theorem cutRankLE_of_mem_Dvar {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (p : OffIdx n → K) (hp : p ∈ Dvar n k) : CutRankLE (toMat p) k := by
  rw [cutRankLE_iff_minorsVanish]
  intro r c hr hc hrc
  rw [← aeval_offMinorPoly r c hrc]
  refine aeval_eq_zero_of_mem_zariskiClosure hp _ (fun q hq => ?_)
  rw [aeval_offMinorPoly]
  exact (cutRankLE_iff_minorsVanish _ k).1 (cutRankLE_of_minCompRank_le _ k hq) r c hr hc hrc

/-- The entries of a symmetric pattern as polynomials in its coordinates `i < j`. -/
noncomputable def symEntryPoly {m : Type*} [LinearOrder m] (i j : m) : MvPolynomial (SymIdx m) K :=
  if h : i < j then X ⟨(i, j), h⟩ else if h' : j < i then X ⟨(j, i), h'⟩ else 0

lemma aeval_symEntryPoly {m : Type*} [LinearOrder m] (p : SymIdx m → K) (i j : m) :
    aeval p (symEntryPoly (K := K) i j) = toMatSym p i j := by
  unfold symEntryPoly toMatSym
  split_ifs <;> simp

/-- **Every point of `X_{n,k}` has all cut ranks `≤ k`** (any field, no hypothesis). -/
theorem cutRankLE_of_mem_Xvar {m : Type*} [Fintype m] [LinearOrder m] (k : ℕ)
    (p : SymIdx m → K) (hp : p ∈ Xvar m k) : CutRankLE (toMatSym p) k := by
  rw [cutRankLE_iff_minorsVanish]
  intro r c hr hc hrc
  have key : ∀ q : SymIdx m → K,
      aeval q (Matrix.of fun a b => symEntryPoly (K := K) (r a) (c b)).det =
        ((toMatSym q).submatrix r c).det := by
    intro q
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]
    congr 1
    ext a b
    rw [submatrix_apply, ← aeval_symEntryPoly]
    simp [RingHom.mapMatrix_apply]
  rw [← key]
  refine aeval_eq_zero_of_mem_zariskiClosure hp _ (fun q hq => ?_)
  rw [key]
  exact (cutRankLE_iff_minorsVanish _ k).1 (cutRankLE_of_minCompRank_le _ k hq) r c hr hc hrc

/-- One non-zero off-diagonal `(k+1)`-minor keeps a pattern out of `D_{n,k}`. -/
theorem not_mem_Dvar_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (p : OffIdx n → K) (r c : Fin (k + 1) → n) (hr : Function.Injective r)
    (hc : Function.Injective c) (hrc : ∀ i j, r i ≠ c j)
    (hdet : ((toMat p).submatrix r c).det ≠ 0) : p ∉ Dvar n k := fun h =>
  hdet (((cutRankLE_iff_minorsVanish _ k).1 (cutRankLE_of_mem_Dvar k p h)) r c hr hc hrc)

/-- One non-zero off-diagonal `(k+1)`-minor keeps a symmetric pattern out of `X_{n,k}`. -/
theorem not_mem_Xvar_of_det_ne_zero {m : Type*} [Fintype m] [LinearOrder m] (k : ℕ)
    (p : SymIdx m → K) (r c : Fin (k + 1) → m) (hr : Function.Injective r)
    (hc : Function.Injective c) (hrc : ∀ i j, r i ≠ c j)
    (hdet : ((toMatSym p).submatrix r c).det ≠ 0) : p ∉ Xvar m k := fun h =>
  hdet (((cutRankLE_iff_minorsVanish _ k).1 (cutRankLE_of_mem_Xvar k p h)) r c hr hc hrc)

end CutRanks

/-! ### Sharpness at `n = 2k + 2`, no hypothesis (the statements of `theorem_3_sharp`,
`theorem_3_sym_sharp`, `theorem_4_sharp` without `ClosedRho`, `ClosedRhoSym`) -/

section AtTwoKPlusTwo

/-- All sub-patterns of the symmetric matching on at most `2k+1` indices lie in their varieties
(the second half of `theorem_3_sym_sharp`, whose proof never used its hypothesis). -/
theorem restrictSym_matchSym_mem [Infinite K] (k : ℕ) (T : Finset (Fin (2 * k + 2)))
    (hT : T.card ≤ 2 * k + 1) : restrictSym (matchSym (K := K) k) T ∈ Xvar T k := by
  obtain ⟨-, -, -, hsub⟩ := closure_threshold_sharp K k
  set e := matchEquiv k
  apply mem_Xvar_of_closRank_le
  rw [toMatSym_restrictSym]
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

/-- **Theorem 3, sharpness, symmetric, no hypothesis**: the statement of `theorem_3_sym_sharp`
without `ClosedRhoSym`. -/
theorem theorem_3_sym_sharp_noHyp [Infinite K] (k : ℕ) :
    matchSym (K := K) k ∉ Xvar (Fin (2 * k + 2)) k ∧
      ∀ T : Finset (Fin (2 * k + 2)), T.card ≤ 2 * k + 1 →
        restrictSym (matchSym (K := K) k) T ∈ Xvar T k := by
  refine ⟨not_mem_Xvar_of_det_ne_zero k _ (fun a => matchEquiv k (a, false))
    (fun a => matchEquiv k (a, true))
    (fun a b e => by simpa using (matchEquiv k).injective e)
    (fun a b e => by simpa using (matchEquiv k).injective e)
    (fun a b e => by simpa using (matchEquiv k).injective e) ?_, restrictSym_matchSym_mem k⟩
  have hid : (toMatSym (matchSym (K := K) k)).submatrix
      (fun a : Fin (k + 1) => matchEquiv k (a, false)) (fun a => matchEquiv k (a, true)) = 1 := by
    ext a b
    simp [toMatSym_matchSym, matching, Matrix.one_apply]
  rw [hid, det_one]
  exact one_ne_zero

/-- **Theorem 3, sharpness, arbitrary patterns, no hypothesis**: the statement of
`theorem_3_sharp` without `ClosedRho`. -/
theorem theorem_3_sharp_noHyp [Infinite K] (k : ℕ) :
    offCoords (matching K k) ∉ Dvar (Fin (k + 1) × Bool) k ∧
      ∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        restrictOff (offCoords (matching K k)) T ∈ Dvar T k := by
  have hm := toMat_offCoords (matching K k) (matching_diag k)
  obtain ⟨-, -, -, hsub⟩ := closure_threshold_sharp K k
  refine ⟨not_mem_Dvar_of_det_ne_zero k _ (fun a : Fin (k + 1) => (a, false)) (fun a => (a, true))
    (fun a b e => by simpa using e) (fun a b e => by simpa using e) (fun a b e => by simp at e) ?_,
    fun T hT => mem_Dvar_of_closRank_le k _ ?_⟩
  · have hid : (matching K k).submatrix (fun a : Fin (k + 1) => (a, false)) (fun a => (a, true))
        = 1 := by
      ext a b; simp [matching, Matrix.one_apply]
    rw [hm, hid, det_one]
    exact one_ne_zero
  · rw [toMat_restrictOff, hm]; exact hsub T hT

/-- "`2k + 2` cannot be replaced by a smaller number" at `n = 2k + 2`, symmetric, no hypothesis. -/
theorem theorem_3_sym_not_smaller_noHyp [Infinite K] (k N : ℕ) (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : SymIdx (Fin (2 * k + 2)) → K,
      (∀ T : Finset (Fin (2 * k + 2)), T.card = N → restrictSym p T ∈ Xvar T k) →
        p ∈ Xvar (Fin (2 * k + 2)) k := by
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sym_sharp_noHyp (K := K) k
  exact hnot (h _ (fun T hT => hsub T (hT ▸ hN)))

/-- "`2k + 2` cannot be replaced by a smaller number" at `n = 2k + 2`, general, no hypothesis. -/
theorem theorem_3_not_smaller_noHyp [Infinite K] (k N : ℕ) (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : OffIdx (Fin (k + 1) × Bool) → K,
      (∀ T : Finset (Fin (k + 1) × Bool), T.card = N → restrictOff p T ∈ Dvar T k) →
        p ∈ Dvar (Fin (k + 1) × Bool) k := by
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sharp_noHyp (K := K) k
  exact hnot (h _ (fun T hT => hsub T (hT ▸ hN)))

/-- **Theorem 4, sharpness, no hypothesis**: the statement of `theorem_4_sharp` without
`ClosedRhoSym ℂ`. For `t ≤ 2m + 1` the radicals of `I_{2m+2,m}` and `Σ_{|A|=t} I_{A,m}` differ. -/
theorem theorem_4_sharp_noHyp (m t : ℕ) (ht : t ≤ 2 * m + 1) :
    (FAideal (Fin (2 * m + 2)) m).radical ≠ (sumIdeal (Fin (2 * m + 2)) m t).radical := by
  rw [Ne, radical_eq_iff_zeroLocus_eq (K := ℂ), zeroLocus_FAideal, zeroLocus_sumIdeal]
  intro h
  obtain ⟨hnot, hsub⟩ := theorem_3_sym_sharp_noHyp (K := ℂ) m
  apply hnot
  rw [h]
  exact fun A hA => hsub A (hA ▸ ht)

end AtTwoKPlusTwo

/-! ### The padded matching: sharpness for every `n ≥ 2k + 2` -/

section Padded

variable {n : Type*} [DecidableEq n]

variable (K) in
/-- The perfect matching on the `2k + 2` indices `f (i, b)`: `f (i, false)` and `f (i, true)` are
matched, and every other off-diagonal entry (in particular every entry in a row or column outside
the image of `f`) is zero. -/
def padMatching (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) : Matrix n n K := fun a b =>
  if ∃ i, (a = f (i, false) ∧ b = f (i, true)) ∨ (a = f (i, true) ∧ b = f (i, false)) then 1
  else 0

lemma padMatching_symm (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (a b : n) :
    padMatching K k f a b = padMatching K k f b a := by
  have swap : ∀ a b : n,
      (∃ i, (a = f (i, false) ∧ b = f (i, true)) ∨ (a = f (i, true) ∧ b = f (i, false))) →
      (∃ i, (b = f (i, false) ∧ a = f (i, true)) ∨ (b = f (i, true) ∧ a = f (i, false))) :=
    fun a b ⟨i, h⟩ => ⟨i, by tauto⟩
  unfold padMatching
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (swap a b h1) h2
  · exact absurd (swap b a h2) h1
  · rfl

lemma padMatching_transpose (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) :
    (padMatching K k f)ᵀ = padMatching K k f := by
  ext a b; exact padMatching_symm k f b a

lemma padMatching_diag (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (a : n) :
    padMatching K k f a a = 0 := by
  unfold padMatching
  split_ifs with h
  · exfalso
    obtain ⟨i, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := h
    · have := f.injective (e1.symm.trans e2); simp at this
    · have := f.injective (e1.symm.trans e2); simp at this
  · rfl

/-- On the matched block the padded matching is the identity. -/
lemma padMatching_apply_emb (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (i j : Fin (k + 1)) :
    padMatching K k f (f (i, false)) (f (j, true)) = if i = j then 1 else 0 := by
  unfold padMatching
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    obtain ⟨l, ⟨e1, e2⟩ | ⟨e1, -⟩⟩ := h1
    · have h3 := f.injective e1
      have h4 := f.injective e2
      simp only [Prod.mk.injEq, and_true] at h3 h4
      exact h2 (h3.trans h4.symm)
    · have h3 := f.injective e1
      simp at h3
  · exact absurd ⟨i, Or.inl ⟨rfl, by rw [h2]⟩⟩ h1
  · rfl

lemma padMatching_block (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) :
    (padMatching K k f).submatrix (fun i => f (i, false)) (fun j => f (j, true)) = 1 := by
  ext i j
  rw [submatrix_apply, padMatching_apply_emb, Matrix.one_apply]

omit [DecidableEq n] in
lemma padMatching_rows_injective (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (b : Bool) :
    Function.Injective (fun i : Fin (k + 1) => f (i, b)) := fun i j e => by
  simpa using f.injective e

omit [DecidableEq n] in
lemma padMatching_rows_disjoint (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (i j : Fin (k + 1)) :
    f (i, false) ≠ f (j, true) := fun e => by
  simpa using f.injective e

/-- **The sub-patterns of the padded matching on at most `2k + 1` indices have `ρ ≤ k`** (any
field). At most `k` matched pairs lie inside `T`; delete one endpoint of each. -/
theorem closRank_subPattern_padMatching_le (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) (T : Finset n)
    (hT : T.card ≤ 2 * k + 1) : closRank (subPattern (padMatching K k f) T) ≤ k := by
  set I : Finset (Fin (k + 1)) := univ.filter (fun i => f (i, false) ∈ T ∧ f (i, true) ∈ T)
  have hI : I.card * 2 ≤ T.card := by
    have hsub : (I ×ˢ (univ : Finset Bool)).map f ⊆ T := by
      intro x hx
      rw [mem_map] at hx
      obtain ⟨⟨i, b⟩, hib, rfl⟩ := hx
      rw [mem_product] at hib
      have hi := (mem_filter.1 hib.1).2
      cases b
      · exact hi.1
      · exact hi.2
    have := card_le_card hsub
    rwa [card_map, card_product, card_univ, Fintype.card_bool] at this
  have hIk : I.card ≤ k := by omega
  set D : Finset T := univ.filter (fun a => ∃ i ∈ I, (a : n) = f (i, false))
  have hD : D.card ≤ I.card := by
    calc D.card ≤ (I.image (fun i => f (i, false))).card :=
          card_le_card_of_injOn (fun a : T => (a : n)) (fun a ha => by
            obtain ⟨i, hi, e⟩ := (mem_filter.1 ha).2
            exact mem_image.2 ⟨i, hi, e.symm⟩) Subtype.val_injective.injOn
      _ ≤ I.card := card_image_le
  refine (closRank_le_card_of_zero _ D ?_).trans (hD.trans hIk)
  intro a ha b hb
  simp only [subPattern, submatrix_apply, padMatching]
  split_ifs with h
  swap
  · rfl
  exfalso
  obtain ⟨i, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := h
  · have hi : i ∈ I := mem_filter.2 ⟨mem_univ _, by rw [← e1]; exact a.2, by rw [← e2]; exact b.2⟩
    exact (mem_compl.1 ha) (mem_filter.2 ⟨mem_univ _, i, hi, e1⟩)
  · have hi : i ∈ I := mem_filter.2 ⟨mem_univ _, by rw [← e2]; exact b.2, by rw [← e1]; exact a.2⟩
    exact (mem_compl.1 hb) (mem_filter.2 ⟨mem_univ _, i, hi, e2⟩)

/-- The padded matching has a cut of rank `k + 1`, so it lies outside `D_{n,k}` (no hypothesis). -/
theorem offCoords_padMatching_not_mem [Fintype n] (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) :
    offCoords (padMatching K k f) ∉ Dvar n k := by
  refine not_mem_Dvar_of_det_ne_zero k _ (fun i => f (i, false)) (fun j => f (j, true))
    (padMatching_rows_injective k f false) (padMatching_rows_injective k f true)
    (padMatching_rows_disjoint k f) ?_
  rw [toMat_offCoords _ (padMatching_diag k f), padMatching_block, det_one]
  exact one_ne_zero

/-- The sub-patterns of the padded matching on at most `2k + 1` indices lie in their varieties. -/
theorem restrictOff_padMatching_mem [Infinite K] [Fintype n] (k : ℕ) (f : Fin (k + 1) × Bool ↪ n)
    (T : Finset n) (hT : T.card ≤ 2 * k + 1) :
    restrictOff (offCoords (padMatching K k f)) T ∈ Dvar T k := by
  apply mem_Dvar_of_closRank_le
  rw [toMat_restrictOff, toMat_offCoords _ (padMatching_diag k f)]
  exact closRank_subPattern_padMatching_le k f T hT

omit [DecidableEq n] in
/-- An embedding of the `2k + 2` matching indices into any index set with at least `2k + 2`
elements. -/
lemma exists_matchEmb [Fintype n] (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) :
    Nonempty (Fin (k + 1) × Bool ↪ n) :=
  Function.Embedding.nonempty_of_card_le (by rw [card_matching_index]; exact hn)

/-- **Theorem 3, sharpness, arbitrary patterns, for every `n ≥ 2k + 2`** (no hypothesis): there is
a pattern on `n` indices outside `D_{n,k}` all of whose sub-patterns on at most `2k + 1` indices
lie in their varieties. -/
theorem theorem_3_sharp_every_n [Infinite K] [Fintype n] (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) :
    ∃ p : OffIdx n → K, p ∉ Dvar n k ∧
      ∀ T : Finset n, T.card ≤ 2 * k + 1 → restrictOff p T ∈ Dvar T k := by
  obtain ⟨f⟩ := exists_matchEmb k hn
  exact ⟨_, offCoords_padMatching_not_mem k f, restrictOff_padMatching_mem k f⟩

/-- **"`2k + 2` cannot be replaced by a smaller number", arbitrary patterns, every `n ≥ 2k + 2`**
(no hypothesis): for no `N ≤ 2k + 1` do the sub-patterns on `N` indices decide membership in
`D_{n,k}`. -/
theorem theorem_3_not_smaller_every_n [Infinite K] [Fintype n] (k N : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n)
    (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : OffIdx n → K,
      (∀ T : Finset n, T.card = N → restrictOff p T ∈ Dvar T k) → p ∈ Dvar n k := by
  intro h
  obtain ⟨p, hnot, hsub⟩ := theorem_3_sharp_every_n (K := K) k hn
  exact hnot (h p (fun T hT => hsub T (hT ▸ hN)))

end Padded

section PaddedSym

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The coordinates `i < j` of a matrix. -/
def upperCoords (M : Matrix n n K) : SymIdx n → K := fun q => M q.1.1 q.1.2

lemma toMatSym_upperCoords (M : Matrix n n K) (hM : ∀ a b, M a b = M b a)
    (hd : ∀ a, M a a = 0) : toMatSym (upperCoords M) = M := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [toMatSym_apply_lt _ h]; rfl
  · subst h; rw [toMatSym_apply_self, hd]
  · rw [toMatSym_apply_gt _ h]; exact hM b a

/-- The padded matching, as a symmetric pattern, lies outside `X_{n,k}` (no hypothesis). -/
theorem upperCoords_padMatching_not_mem (k : ℕ) (f : Fin (k + 1) × Bool ↪ n) :
    upperCoords (padMatching K k f) ∉ Xvar n k := by
  refine not_mem_Xvar_of_det_ne_zero k _ (fun i => f (i, false)) (fun j => f (j, true))
    (padMatching_rows_injective k f false) (padMatching_rows_injective k f true)
    (padMatching_rows_disjoint k f) ?_
  rw [toMatSym_upperCoords _ (padMatching_symm k f) (padMatching_diag k f), padMatching_block,
    det_one]
  exact one_ne_zero

/-- Its symmetric sub-patterns on at most `2k + 1` indices lie in their varieties. -/
theorem restrictSym_padMatching_mem [Infinite K] (k : ℕ) (f : Fin (k + 1) × Bool ↪ n)
    (T : Finset n) (hT : T.card ≤ 2 * k + 1) :
    restrictSym (upperCoords (padMatching K k f)) T ∈ Xvar T k := by
  apply mem_Xvar_of_closRank_le
  rw [toMatSym_restrictSym, toMatSym_upperCoords _ (padMatching_symm k f) (padMatching_diag k f)]
  convert closRank_subPattern_padMatching_le (K := K) k f T hT using 1
  exact closRank_inst_eq _ _ _

/-- **Theorem 3, sharpness, symmetric patterns, for every `n ≥ 2k + 2`** (no hypothesis). -/
theorem theorem_3_sym_sharp_every_n [Infinite K] (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) :
    ∃ p : SymIdx n → K, p ∉ Xvar n k ∧
      ∀ T : Finset n, T.card ≤ 2 * k + 1 → restrictSym p T ∈ Xvar T k := by
  obtain ⟨f⟩ := exists_matchEmb k hn
  exact ⟨_, upperCoords_padMatching_not_mem k f, restrictSym_padMatching_mem k f⟩

/-- **"`2k + 2` cannot be replaced by a smaller number", symmetric patterns, every
`n ≥ 2k + 2`** (no hypothesis). -/
theorem theorem_3_sym_not_smaller_every_n [Infinite K] (k N : ℕ)
    (hn : 2 * k + 2 ≤ Fintype.card n) (hN : N ≤ 2 * k + 1) :
    ¬ ∀ p : SymIdx n → K,
      (∀ T : Finset n, T.card = N → restrictSym p T ∈ Xvar T k) → p ∈ Xvar n k := by
  intro h
  obtain ⟨p, hnot, hsub⟩ := theorem_3_sym_sharp_every_n (K := K) k hn
  exact hnot (h p (fun T hT => hsub T (hT ▸ hN)))

/-- **Both statements at once, one witness** (no hypothesis): for every `n ≥ 2k + 2` there is a
symmetric matrix `M` with zero diagonal whose pattern lies in neither `D_{n,k}` nor `X_{n,k}`,
while for every `T` with `|T| ≤ 2k + 1` its sub-pattern lies in both `D_{T,k}` and `X_{T,k}`. -/
theorem theorem_3_sharp_every_n_both [Infinite K] (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) :
    ∃ M : Matrix n n K, Mᵀ = M ∧ (∀ a, M a a = 0) ∧
      offCoords M ∉ Dvar n k ∧ upperCoords M ∉ Xvar n k ∧
      ∀ T : Finset n, T.card ≤ 2 * k + 1 →
        restrictOff (offCoords M) T ∈ Dvar T k ∧ restrictSym (upperCoords M) T ∈ Xvar T k := by
  obtain ⟨f⟩ := exists_matchEmb k hn
  exact ⟨padMatching K k f, padMatching_transpose k f, padMatching_diag k f,
    offCoords_padMatching_not_mem k f, upperCoords_padMatching_not_mem k f,
    fun T hT => ⟨restrictOff_padMatching_mem k f T hT, restrictSym_padMatching_mem k f T hT⟩⟩

end PaddedSym

/-! ### Theorem 4, sharpness at every `p ≥ 2m + 2` (a by-product) -/

/-- For every `p ≥ 2m + 2` and `t ≤ 2m + 1` the radicals of `I_{p,m}` and `Σ_{|A|=t} I_{A,m}`
differ (no hypothesis). -/
theorem theorem_4_sharp_every_p (m p t : ℕ) (hp : 2 * m + 2 ≤ p) (ht : t ≤ 2 * m + 1) :
    (FAideal (Fin p) m).radical ≠ (sumIdeal (Fin p) m t).radical := by
  rw [Ne, radical_eq_iff_zeroLocus_eq (K := ℂ), zeroLocus_FAideal, zeroLocus_sumIdeal]
  intro h
  obtain ⟨q, hnot, hsub⟩ := theorem_3_sym_sharp_every_n (K := ℂ) (n := Fin p) m (by simpa using hp)
  apply hnot
  rw [h]
  exact fun A hA => hsub A (hA ▸ ht)

end FreeDiagonal
