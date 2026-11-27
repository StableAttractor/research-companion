import FreeDiagonal.StatisticalFactorAnalysis.ExtremalGroups

/-!
# Theorem 3 (extremal matrices)

From the groups (`ExtremalGroups.lean`): with `μ_l` the multiplier of row `l` and
`S0'_{KK'} = G_{rep K, rep K'}`, `G_{ll'} = μ_l μ_l' S0'_{K(l) K(l')}`. Then `S0'` is not
positive semidefinite (else `G` would be a fit), its principal submatrices without one group are
positive definite (`PSDon` and the independence of the representatives), and dividing each
variable by `μ_l` makes `Σ` replicated from `S0'`.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Ctx

variable {G : Matrix n n ℝ} {q t : ℕ} {Xf : n → Finset n}

/-- The multiplier of row `l`. -/
noncomputable def lam (c : Ctx G q t Xf) (l : n) : ℝ := (c.exists_lam l).choose

lemma lam_ne (c : Ctx G q t Xf) (l : n) : c.lam l ≠ 0 := (c.exists_lam l).choose_spec.1

lemma lam_spec (c : Ctx G q t Xf) (l : n) :
    G.row l = c.lam l • G.row (rep Xf (grp Xf l)) := (c.exists_lam l).choose_spec.2

/-- `S0'_{KK'} = G_{rep K, rep K'}`. -/
noncomputable def S0' (G : Matrix n n ℝ) (Xf : n → Finset n) : Matrix (grps Xf) (grps Xf) ℝ :=
  Matrix.of fun K K' => G (rep Xf K) (rep Xf K')

lemma entry (c : Ctx G q t Xf) (l l' : n) :
    G l l' = c.lam l * c.lam l' * S0' G Xf (grp Xf l) (grp Xf l') := by
  have hs : ∀ a b, G a b = G b a := fun a b => symm_apply c.symm a b
  have h1 : ∀ a b, G a b = c.lam a * G (rep Xf (grp Xf a)) b := fun a b => by
    have := congrFun (c.lam_spec a) b
    simpa using this
  rw [h1 l l', hs _ l', h1 l' _, S0', of_apply, hs (rep Xf (grp Xf l')) _]
  ring

lemma S0'_symm (c : Ctx G q t Xf) : (S0' G Xf).IsSymm := by
  ext K K'; simp [S0', symm_apply c.symm (rep Xf K') (rep Xf K)]

lemma G_eq (c : Ctx G q t Xf) :
    G = (Matrix.of fun l K => if grp Xf l = K then c.lam l else 0) * S0' G Xf *
      (Matrix.of fun l K => if grp Xf l = K then c.lam l else 0)ᵀ := by
  refine Matrix.ext fun l l' => ?_
  simp only [Matrix.mul_apply, of_apply, transpose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, mem_univ, ite_true]
  rw [c.entry]; ring

lemma S0'_not_psd (c : Ctx G q t Xf) (hnpsd : ¬ G.PosSemidef) : ¬ (S0' G Xf).PosSemidef := by
  intro h
  apply hnpsd
  rw [c.G_eq]
  have := h.mul_mul_conjTranspose_same
    (Matrix.of fun l K => if grp Xf l = K then c.lam l else 0)
  simpa [conjTranspose_eq_transpose_of_trivial] using this

lemma S0'_princ (c : Ctx G q t Xf) (K0 : grps Xf) :
    ((S0' G Xf).submatrix (fun K : {K // K ≠ K0} => K.1) (fun K : {K // K ≠ K0} => K.1)).PosDef := by
  classical
  refine PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext a b; simp [S0', symm_apply c.symm (rep Xf b.1) (rep Xf a.1)]
  · simp only [star_trivial]
    have hf : ∀ a : {K // K ≠ K0}, rep Xf a.1 ∈ Xf (rep Xf K0) := fun a => by
      rw [rep_spec (Xf := Xf) K0]
      exact c.mem_other (by rw [grp_rep]; exact a.2)
    obtain ⟨hnn, hz⟩ := c.psd (rep Xf K0) {K // K ≠ K0} (fun a => rep Xf a.1) hf x
    have hQ : x ⬝ᵥ ((S0' G Xf).submatrix (fun K : {K // K ≠ K0} => K.1)
        (fun K : {K // K ≠ K0} => K.1)) *ᵥ x =
        ∑ a, ∑ b, x a * x b * G (rep Xf a.1) (rep Xf b.1) := by
      simp only [dotProduct, mulVec, submatrix_apply, S0', of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hQ]
    refine lt_of_le_of_ne hnn (fun h0 => hx ?_)
    have hli := c.linIndep.comp (fun a : {K // K ≠ K0} => a.1) Subtype.val_injective
    funext a
    exact Fintype.linearIndependent_iff.1 hli x (hz h0.symm) a

lemma card_fiber (c : Ctx G q t Xf) (K : grps Xf) : Fintype.card {l // grp Xf l = K} = t := by
  classical
  rw [Fintype.card_subtype]
  have e : univ.filter (fun l => grp Xf l = K) = univ.filter (fun l => Xf l = Xf (rep Xf K)) := by
    ext l; simp only [mem_filter, mem_univ, true_and, rep_spec (Xf := Xf) K, grp, Subtype.ext_iff]
  rw [e, c.fiber_eq, c.card_compl]

/-- Labels of the groups. -/
noncomputable def eK (c : Ctx G q t Xf) : grps Xf ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact c.card_grps)

/-- The variables as `Fin q × Fin t` (group, member). -/
noncomputable def equiv (c : Ctx G q t Xf) : n ≃ Fin q × Fin t :=
  (Equiv.sigmaFiberEquiv (grp Xf)).symm.trans
    ((Equiv.sigmaCongrRight fun K => Fintype.equivFinOfCardEq (c.card_fiber K)).trans
      ((Equiv.sigmaEquivProd (grps Xf) (Fin t)).trans (Equiv.prodCongr c.eK (Equiv.refl _))))

lemma equiv_fst (c : Ctx G q t Xf) (l : n) : (c.equiv l).1 = c.eK (grp Xf l) := rfl

lemma grp_equiv_symm (c : Ctx G q t Xf) (x : Fin q × Fin t) :
    grp Xf (c.equiv.symm x) = c.eK.symm x.1 := by
  rw [Equiv.eq_symm_apply, ← equiv_fst, Equiv.apply_symm_apply]

/-- `S0 = S0'` relabelled by `Fin q`. -/
noncomputable def S0 (c : Ctx G q t Xf) : Matrix (Fin q) (Fin q) ℝ :=
  (S0' G Xf).submatrix c.eK.symm c.eK.symm

lemma S0_lemma3 (c : Ctx G q t Xf) (hnpsd : ¬ G.PosSemidef) : IsLemma3Matrix c.S0 := by
  have hsymm : c.S0.IsSymm := by
    ext a b; simp [S0, symm_apply c.S0'_symm (c.eK.symm b) (c.eK.symm a)]
  have hnot : ¬ c.S0.PosSemidef := fun h =>
    c.S0'_not_psd hnpsd ((posSemidef_submatrix_equiv c.eK.symm).1 h)
  have hprinc : ∀ j, (offPrinc c.S0 j).PosDef := by
    intro j
    set φ : {k // k ≠ j} → {K // K ≠ c.eK.symm j} :=
      fun k => ⟨c.eK.symm k.1, fun h => k.2 (c.eK.symm.injective h)⟩ with hφ
    have hinj : Function.Injective φ := fun a b h => Subtype.ext (c.eK.symm.injective
      (congrArg Subtype.val h))
    have := (c.S0'_princ (c.eK.symm j)).submatrix hinj
    exact this
  have hq := c.hq
  exact ⟨hsymm, det_ne_zero_of_princ _ hsymm ⟨0, by omega⟩ (hprinc _) hnot, hnot, hprinc⟩

/-- **The replicated structure.** Dividing variable `l` by `μ_l` and labelling the variables
by (group, member) makes `Σ` replicated from `S0`. -/
theorem replicated (c : Ctx G q t Xf) {Sig : Matrix n n ℝ}
    (hoffG : ∀ i j, i ≠ j → G i j = Sig i j) (hnpsd : ¬ G.PosSemidef) :
    IsLemma3Matrix c.S0 ∧
      IsReplicated c.S0 ((diagonal (fun l => (c.lam l)⁻¹) * Sig * diagonal (fun l => (c.lam l)⁻¹)).submatrix
        c.equiv.symm c.equiv.symm) := by
  refine ⟨c.S0_lemma3 hnpsd, ?_, fun x y hxy => ?_⟩
  · ext x y
    simp only [transpose_apply, submatrix_apply, diagonal_mul, mul_diagonal]
    by_cases h : c.equiv.symm x = c.equiv.symm y
    · rw [h]
    · rw [← hoffG _ _ h, ← hoffG _ _ (Ne.symm h), symm_apply c.symm]; ring
  · have h : c.equiv.symm x ≠ c.equiv.symm y := fun e => hxy (c.equiv.symm.injective e)
    simp only [submatrix_apply, diagonal_mul, mul_diagonal]
    rw [← hoffG _ _ h, c.entry, c.grp_equiv_symm, c.grp_equiv_symm, S0, submatrix_apply]
    field_simp [c.lam_ne (c.equiv.symm x), c.lam_ne (c.equiv.symm y)]

end Ctx

lemma three_le_of_balanced (m q t : ℕ) (hm : 3 ≤ m) (hqt : q + t = m + 3)
    (h : q * t = (m + 3) ^ 2 / 4) : 3 ≤ t ∧ 3 ≤ q := by
  have h1 : (m + 3) ^ 2 < 4 * ((m + 3) ^ 2 / 4) + 4 := by
    have := Nat.lt_mul_div_succ ((m + 3) ^ 2) (show 0 < 4 by norm_num); linarith
  rw [← h, ← hqt] at h1
  constructor
  · by_contra hc; push Not at hc
    have hq : 4 ≤ q := by omega
    interval_cases t <;> nlinarith
  · by_contra hc; push Not at hc
    have ht : 4 ≤ t := by omega
    interval_cases q <;> nlinarith

/-- **Theorem 3, forward direction** (any finite index type with `⌊(m+3)²/4⌋` elements; positive
definiteness is not needed). If `m ≥ 3` and `Σ ∉ F_{n,m}` while all its proper principal
submatrices are in the model, then there are `q, t` with `q + t = m + 3`, `q t = ⌊(m+3)²/4⌋`, a
labelling of the variables by (group, member) and non-zero multipliers `p` such that
`(p_i Σ_il p_l)` is replicated from a matrix `S0` satisfying the hypotheses of Lemma 3, and
satisfies condition (1). -/
theorem theorem3_forward (m : ℕ) (hm : 3 ≤ m) (Sig : Matrix n n ℝ)
    (hN : Fintype.card n = (m + 3) ^ 2 / 4) (hnot : ¬ InModel m Sig)
    (hprop : ∀ T : Finset n, T ≠ univ → InModel m (subPattern Sig T)) :
    ∃ q t : ℕ, 2 ≤ q ∧ 3 ≤ t ∧ q + t = m + 3 ∧ q * t = (m + 3) ^ 2 / 4 ∧
      ∃ (e : n ≃ Fin q × Fin t) (p : n → ℝ), (∀ i, p i ≠ 0) ∧
        ∃ S0 : Matrix (Fin q) (Fin q) ℝ, IsLemma3Matrix S0 ∧
          IsReplicated S0 ((diagonal p * Sig * diagonal p).submatrix e.symm e.symm) ∧
          Cond1 S0 ((diagonal p * Sig * diagonal p).submatrix e.symm e.symm) := by
  classical
  -- `n > 2m + 2`
  have hgap := section6_gap m
  have hm1 : 1 ≤ (m - 1) ^ 2 / 4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 ≤ m - 1 := by omega
    nlinarith
  have hbig : 2 * m + 2 < Fintype.card n := by omega
  -- a reference of rank at most `m` (Lemma 1)
  obtain ⟨G0, hG0, hG0r⟩ := lemma1 m Sig (fun T hT => by
    have hT' : T ≠ univ := fun e => by
      rw [e, card_univ] at hT; omega
    obtain ⟨H, hH⟩ := (inModel_iff_exists_fit m _).1 (hprop T hT')
    exact ⟨H, ⟨PosSemidef.isSymm' hH.1, hH.2.2.1, fun i => ⟨hH.1.diag_nonneg, hH.2.2.2 i⟩⟩,
      hH.2.1⟩)
  have hex : ∃ r, ∃ G, IsReference Sig G ∧ G.rank = r := ⟨_, G0, hG0, rfl⟩
  set q := Nat.find hex with hqdef
  have hqL : IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q :=
    ⟨Nat.find_spec hex, fun r hr => Nat.find_min' hex hr⟩
  obtain ⟨G, hG, hGr⟩ := Nat.find_spec hex
  rw [← hqdef] at hGr
  have hqm : q ≤ m := (Nat.find_min' hex ⟨G0, hG0, rfl⟩).trans hG0r
  have hGc : IsCompletionIn (refSets Sig) Sig G := (isReference_iff Sig G).1 hG
  have hmin : ∀ G', IsCompletionIn (refSets Sig) Sig G' → G.rank ≤ G'.rank := fun G' hG' => by
    rw [hGr]; exact hqL.2 ⟨G', (isReference_iff Sig G').2 hG', rfl⟩
  -- `q ≥ 2` (Theorem 2)
  have hq2 : 2 ≤ q := by
    by_contra hc; push Not at hc
    exact hnot ((theorem2_first m Sig q hqL).2.1 (by omega) m hqm)
  set t := m + 3 - q with htdef
  -- the set `T` of Theorem 2 is everything, whence `|Z| ≤ t ρ(Z)`
  obtain ⟨T, hTb, hTfit⟩ := theorem2_sets_iii' (refSets Sig) m Sig G hGc hmin (by omega)
  have hTu : T = univ := by
    by_contra hT
    have h1 := (inModel_iff_hasFitIn m _).1 (hprop T hT)
    exact hnot ((inModel_iff_hasFitIn m Sig).2 (hTfit h1))
  rw [hTu, hGr] at hTb
  have h3 : ∀ Z : Finset n, Z.card ≤ t * frk ℝ G.row Z := by
    intro Z
    have h1 := hTb Z
    have h2 := card_sdiff_eq' (subset_univ Z)
    rw [card_univ] at h1 h2
    have : (Z.card : ℤ) ≤ (t : ℤ) * frk ℝ G.row Z := by linarith
    exact_mod_cast this
  have hfu : frk ℝ G.row univ = q := by rw [← rank_eq_frk_univ, hGr]
  have hcard : Fintype.card n = t * q := by
    have h1 := h3 univ
    rw [card_univ, hfu] at h1
    have h2 := mul_sub_le_sq_div m q (by omega)
    rw [← htdef] at h2
    have : q * t = t * q := Nat.mul_comm _ _
    omega
  have hqt : q * t = (m + 3) ^ 2 / 4 := by rw [← hN, hcard, Nat.mul_comm]
  obtain ⟨ht3, -⟩ := three_le_of_balanced m q t hm (by omega) hqt
  have hmq : q + t - 3 = m := by omega
  -- `G` is not positive semidefinite
  have hnpsd : ¬ G.PosSemidef := fun hp =>
    hnot ((inModel_iff_exists_fit m Sig).2 ⟨G, hp, by omega, hG.2.1, fun i => (hG.2.2 i).2⟩)
  -- a fit without each variable, and its hyperplane
  have hX : ∀ i : n, ∃ X : Finset n, i ∉ X ∧ frk ℝ G.row X = q - 1 ∧ X.card = t * (q - 1) ∧
      (∀ l, G.row l ∈ span ℝ (G.row '' (X : Set n)) → l ∈ X) ∧ PSDon G X := by
    intro i
    have hne : (univ.erase i : Finset n) ≠ univ := fun e => by
      have : i ∈ univ.erase i := by rw [e]; exact mem_univ _
      simp at this
    obtain ⟨H, hH⟩ := (inModel_iff_exists_fit m _).1 (hprop _ hne)
    rw [← hmq] at hH
    exact hyperplane hG.1 hG.2.1 hGr hcard h3 ht3 hq2 hnpsd i H hH
  choose Xf hXn hXf hXc hXcl hXp using hX
  have c : Ctx G q t Xf := ⟨hG.1, hGr, hcard, h3, ht3, hq2, hXn, hXf, hXc, hXcl, hXp⟩
  obtain ⟨hL3, hR⟩ := c.replicated hG.2.1 hnpsd
  set p : n → ℝ := fun l => (c.lam l)⁻¹ with hp
  have hp0 : ∀ i, p i ≠ 0 := fun i => inv_ne_zero (c.lam_ne i)
  refine ⟨q, t, hq2, ht3, by omega, hqt, c.equiv, p, hp0, c.S0, hL3, hR,
    lemma3_converse hL3 hq2 ht3 hR (fun T hT => ?_)⟩
  rw [hmq]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ T := by
    by_contra hc; push Not at hc; exact hT (eq_univ_of_forall hc)
  have hne : (univ.erase (c.equiv.symm x) : Finset n) ≠ univ := fun e => by
    have : c.equiv.symm x ∈ univ.erase (c.equiv.symm x) := by rw [e]; exact mem_univ _
    simp at this
  have h1 := (hprop _ hne).scale (fun a : (univ.erase (c.equiv.symm x) : Finset n) => p a)
    (fun a => hp0 a)
  rw [← subPattern_scale] at h1
  have := h1.comp_inj (fun a : T => (⟨c.equiv.symm a, mem_erase.2 ⟨fun h => hx
      (by rw [← c.equiv.symm.injective h]; exact a.2), mem_univ _⟩⟩ :
      (univ.erase (c.equiv.symm x) : Finset _)))
    (fun a b hab => Subtype.ext (c.equiv.symm.injective (by simpa using congrArg Subtype.val hab)))
  exact this

/-- **Theorem 3, converse.** A positive definite replicated matrix from a matrix `S0` as in
Lemma 3, with `q + t = m + 3`, satisfying condition (1), is not in the model (not even in the weak
model), while all its proper principal submatrices are. -/
theorem theorem3_converse {q t : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t) (m : ℕ) (hm : q + t = m + 3)
    {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0)
    {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hR : IsReplicated S0 Sig) (hC : Cond1 S0 Sig) :
    ¬ InWeakModel m Sig ∧ ¬ InModel m Sig ∧
      ∀ T : Finset (Fin q × Fin t), T ≠ univ → InModel m (subPattern Sig T) := by
  have hmq : q + t - 3 = m := by omega
  have hnw : ¬ InWeakModel m Sig := by
    rw [inWeakModel_iff_exists_weakFit]
    rintro ⟨G, hp, hr, ho, -⟩
    have := lemma3_no_psd hS0 hq ht hR G hp ho
    omega
  refine ⟨hnw, fun h => hnw h.inWeakModel, fun T hT => ?_⟩
  have := lemma3_proper hS0 hq ht hR hC T hT
  rwa [hmq] at this

end FreeDiagonal.StatisticalFactorAnalysis
