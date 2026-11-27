import FreeDiagonal.StatisticalFactorAnalysis.Extremal

/-!
# Theorem 3: the groups

Given, for every variable `i`, a closed set `X_i ∌ i` of rank `q - 1` with `t (q - 1)`
elements (`hyperplane`), two such sets are equal or cover `E` (`Ctx.dich`, from
`|Z| ≤ t ρ(Z)` applied to `X_i ∩ X_{i'}`). The complements `E \ X_i` are the `q` groups of
`t`; one representative per group gives linearly independent rows spanning all rows, and
every row of group `K` is a non-zero multiple of the representative's row.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The situation reached in the proof of Theorem 3. -/
structure Ctx (G : Matrix n n ℝ) (q t : ℕ) (Xf : n → Finset n) : Prop where
  symm : G.IsSymm
  rank : G.rank = q
  card : Fintype.card n = t * q
  h3 : ∀ Z : Finset n, Z.card ≤ t * frk ℝ G.row Z
  ht : 3 ≤ t
  hq : 2 ≤ q
  notin : ∀ i, i ∉ Xf i
  frkX : ∀ i, frk ℝ G.row (Xf i) = q - 1
  cardX : ∀ i, (Xf i).card = t * (q - 1)
  closed : ∀ i l, G.row l ∈ span ℝ (G.row '' (Xf i : Set n)) → l ∈ Xf i
  psd : ∀ i, PSDon G (Xf i)

namespace Ctx

variable {G : Matrix n n ℝ} {q t : ℕ} {Xf : n → Finset n}

lemma frk_univ (c : Ctx G q t Xf) : frk ℝ G.row univ = q := by
  rw [← rank_eq_frk_univ, c.rank]

lemma mem_iff (c : Ctx G q t Xf) (i l : n) :
    l ∈ Xf i ↔ G.row l ∈ span ℝ (G.row '' (Xf i : Set n)) :=
  ⟨fun h => subset_span ⟨l, h, rfl⟩, c.closed i l⟩

/-- Two of the sets are equal or cover `E`. -/
lemma dich (c : Ctx G q t Xf) (i i' : n) : Xf i = Xf i' ∨ Xf i ∪ Xf i' = univ := by
  classical
  set P := span ℝ (G.row '' (Xf i : Set n)) with hP
  set P' := span ℝ (G.row '' (Xf i' : Set n)) with hP'
  by_cases hPP : P = P'
  · left
    ext l
    rw [c.mem_iff i l, c.mem_iff i' l, ← hP, ← hP', hPP]
  · right
    have hfP : finrank ℝ P = q - 1 := c.frkX i
    have hfP' : finrank ℝ P' = q - 1 := c.frkX i'
    have hW : finrank ℝ ((P ⊔ P' : Submodule ℝ (n → ℝ))) ≤ q := by
      have : P ⊔ P' ≤ span ℝ (G.row '' ((univ : Finset n) : Set n)) :=
        sup_le (span_mono (Set.image_mono (by simp))) (span_mono (Set.image_mono (by simp)))
      have h := Submodule.finrank_mono this
      have hu := c.frk_univ
      unfold frk at hu
      omega
    have hsup : q ≤ finrank ℝ ((P ⊔ P' : Submodule ℝ (n → ℝ))) := by
      by_contra hlt
      push Not at hlt
      have h1 : finrank ℝ P ≤ finrank ℝ ((P ⊔ P' : Submodule ℝ (n → ℝ))) := Submodule.finrank_mono le_sup_left
      have e1 : P = P ⊔ P' := Submodule.eq_of_le_of_finrank_eq le_sup_left (by omega)
      have e2 : P' = P ⊔ P' := Submodule.eq_of_le_of_finrank_eq le_sup_right (by
        have := Submodule.finrank_mono (le_sup_right : P' ≤ P ⊔ P'); omega)
      exact hPP (e1.trans e2.symm)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq P P'
    have hinf : finrank ℝ (P ⊓ P' : Submodule ℝ (n → ℝ)) ≤ q - 2 := by omega
    set Z := Xf i ∩ Xf i' with hZ
    have hZf : frk ℝ G.row Z ≤ q - 2 := by
      refine le_trans (Submodule.finrank_mono ?_) hinf
      exact le_inf (span_mono (Set.image_mono (by simp [hZ])))
        (span_mono (Set.image_mono (by simp [hZ])))
    have hZc : Z.card ≤ t * (q - 2) := (c.h3 Z).trans (Nat.mul_le_mul_left _ hZf)
    have hU := card_union_add_card_inter (Xf i) (Xf i')
    rw [c.cardX i, c.cardX i'] at hU
    have hq := c.hq
    have hq1 : q - 1 = (q - 2) + 1 := by omega
    have hq0 : q = (q - 2) + 2 := by omega
    have e1 : t * (q - 1) = t * (q - 2) + t := by rw [hq1]; ring
    have e2 : t * q = t * (q - 2) + 2 * t := by
      calc t * q = t * ((q - 2) + 2) := by rw [← hq0]
        _ = t * (q - 2) + 2 * t := by ring
    have hcard : (Xf i ∪ Xf i').card ≥ Fintype.card n := by
      rw [← hZ, e1] at hU
      rw [c.card, e2]
      generalize t * (q - 2) = w at hU hZc ⊢
      omega
    exact eq_univ_of_card _ (le_antisymm (card_le_univ _) hcard)

/-- A variable outside `X_i` has the same set as `i`. -/
lemma eq_of_notMem (c : Ctx G q t Xf) {i l : n} (h : l ∉ Xf i) : Xf l = Xf i := by
  rcases c.dich l i with e | e
  · exact e
  · exfalso
    have : l ∈ Xf l ∪ Xf i := e ▸ mem_univ l
    rcases mem_union.1 this with h1 | h1
    · exact c.notin l h1
    · exact h h1

lemma fiber_eq (c : Ctx G q t Xf) (i : n) : univ.filter (fun l => Xf l = Xf i) = univ \ Xf i := by
  ext l
  simp only [mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · intro h hl; rw [← h] at hl; exact c.notin l hl
  · exact c.eq_of_notMem

lemma card_compl (c : Ctx G q t Xf) (i : n) : (univ \ Xf i).card = t := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, c.card, c.cardX i]
  have hq := c.hq
  rw [show q = (q - 1) + 1 by omega]
  simp [Nat.mul_add]

/-- The groups, labelled by their sets `X`. -/
noncomputable abbrev grps (Xf : n → Finset n) : Finset (Finset n) := univ.image Xf

lemma card_grps (c : Ctx G q t Xf) : (grps Xf).card = q := by
  have h := Finset.card_eq_sum_card_image Xf (univ : Finset n)
  have h2 : ∀ K ∈ grps Xf, (univ.filter (fun l => Xf l = K)).card = t := by
    intro K hK
    obtain ⟨i, -, rfl⟩ := mem_image.1 hK
    rw [c.fiber_eq i, c.card_compl i]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, card_univ, c.card] at h
  have ht := c.ht
  have : t * q = t * (grps Xf).card := by rw [h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm

/-- A representative of each group. -/
noncomputable def rep (Xf : n → Finset n) (K : grps Xf) : n :=
  (mem_image.1 K.2).choose

lemma rep_spec (K : grps Xf) : Xf (rep Xf K) = K.1 := (mem_image.1 K.2).choose_spec.2

/-- The group of a variable. -/
def grp (Xf : n → Finset n) (l : n) : grps Xf := ⟨Xf l, mem_image_of_mem _ (mem_univ l)⟩

lemma grp_rep (K : grps Xf) : grp Xf (rep Xf K) = K := Subtype.ext (rep_spec K)

lemma mem_other (c : Ctx G q t Xf) {l : n} {K : grps Xf} (h : grp Xf l ≠ K) : l ∈ K.1 := by
  by_contra hl
  rw [← rep_spec (Xf := Xf) K] at hl
  apply h
  apply Subtype.ext
  change Xf l = K.1
  rw [c.eq_of_notMem hl, rep_spec (Xf := Xf) K]

lemma coord_zero (c : Ctx G q t Xf) (K0 : grps Xf) (w : n → ℝ)
    (hw : w ∈ span ℝ (G.row '' (K0.1 : Set n))) (a : grps Xf → ℝ)
    (ha : ∑ K, a K • G.row (rep Xf K) = w) : a K0 = 0 := by
  classical
  by_contra hne
  set P := span ℝ (G.row '' (K0.1 : Set n))
  have hrest : ∑ K ∈ univ.erase K0, a K • G.row (rep Xf K) ∈ P := by
    refine sum_mem fun K hK => smul_mem _ _ (subset_span ⟨rep Xf K, ?_, rfl⟩)
    exact c.mem_other (by rw [grp_rep]; exact (mem_erase.1 hK).1)
  have hsplit := Finset.add_sum_erase univ (fun K => a K • G.row (rep Xf K)) (mem_univ K0)
  rw [ha] at hsplit
  have h1 : a K0 • G.row (rep Xf K0) ∈ P := by
    have : a K0 • G.row (rep Xf K0) = w - ∑ K ∈ univ.erase K0, a K • G.row (rep Xf K) := by
      rw [← hsplit]; abel
    rw [this]; exact sub_mem hw hrest
  have h2 : G.row (rep Xf K0) ∈ P := by
    have := smul_mem P (a K0)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have h3 : rep Xf K0 ∈ Xf (rep Xf K0) := c.closed _ _ (by rw [rep_spec (Xf := Xf) K0]; exact h2)
  exact c.notin _ h3

lemma linIndep (c : Ctx G q t Xf) : LinearIndependent ℝ (fun K : grps Xf => G.row (rep Xf K)) :=
  Fintype.linearIndependent_iff.2 fun a h K0 => c.coord_zero K0 0 (zero_mem _) a h

lemma span_reps (c : Ctx G q t Xf) :
    span ℝ (Set.range fun K : grps Xf => G.row (rep Xf K)) =
      span ℝ (G.row '' ((univ : Finset n) : Set n)) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [span_le]; rintro _ ⟨K, rfl⟩; exact subset_span ⟨rep Xf K, by simp, rfl⟩
  · rw [finrank_span_eq_card c.linIndep, Fintype.card_coe, c.card_grps]
    have := c.frk_univ; unfold frk at this; omega

/-- Every row is a non-zero multiple of its representative's row. -/
lemma exists_lam (c : Ctx G q t Xf) (l : n) :
    ∃ μ : ℝ, μ ≠ 0 ∧ G.row l = μ • G.row (rep Xf (grp Xf l)) := by
  classical
  have hmem : G.row l ∈ span ℝ (Set.range fun K : grps Xf => G.row (rep Xf K)) := by
    rw [c.span_reps]; exact subset_span ⟨l, by simp, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hz : ∀ K, K ≠ grp Xf l → a K = 0 := fun K hK =>
    c.coord_zero K (G.row l) (subset_span ⟨l, c.mem_other (Ne.symm hK), rfl⟩) a ha
  have hsum : ∑ K, a K • G.row (rep Xf K) = a (grp Xf l) • G.row (rep Xf (grp Xf l)) :=
    Fintype.sum_eq_single _ fun K hK => by rw [hz K hK, zero_smul]
  refine ⟨a (grp Xf l), fun h0 => ?_, by rw [← ha, hsum]⟩
  have : G.row l = 0 := by rw [← ha, hsum, h0, zero_smul]
  exact c.notin l (c.closed l l (by rw [this]; exact zero_mem _))

end Ctx

end FreeDiagonal.StatisticalFactorAnalysis
