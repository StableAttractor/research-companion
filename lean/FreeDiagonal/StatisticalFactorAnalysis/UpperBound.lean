import FreeDiagonal.StatisticalFactorAnalysis.References
import FreeDiagonal.StatisticalFactorAnalysis.Packing
import FreeDiagonal.StatisticalFactorAnalysis.Extension

/-!
# Theorem 2 except its last sentence, and the upper bound of Theorem 1

Proved for arbitrary admissible sets `A i ⊆ [0, ∞)` (the remark after the proof of Theorem 2),
then specialised to references (`[0, Σ_ii)`) and weak references (`[0, Σ_ii]`).
The third statement does not even need `A i ⊆ [0, ∞)` (`theorem2_sets_iii`).
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma HasFitIn.restrict {m : ℕ} {A : n → Set ℝ} {Sig : Matrix n n ℝ} (h : HasFitIn m A Sig)
    (T : Finset n) : HasFitIn m (fun a : T => A a) (subPattern Sig T) := by
  obtain ⟨G, ⟨hs, ho, hd⟩, hp, hr⟩ := h
  refine ⟨subPattern G T, ⟨?_, ?_, fun a => hd a⟩, hp.submatrix _,
    (rank_submatrix_le _ _ _).trans hr⟩
  · ext a b; exact congrFun (congrFun hs a) b
  · intro a b hab; exact ho a b (fun e => hab (Subtype.ext e))

/-- `q (m + 3 - q) ≤ ⌊(m+3)²/4⌋`. -/
lemma mul_sub_le_sq_div (m q : ℕ) (hq : q ≤ m + 3) : q * (m + 3 - q) ≤ (m + 3) ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨s, hs⟩ : ∃ s, m + 3 = q + s := ⟨m + 3 - q, by omega⟩
  rw [hs, Nat.add_sub_cancel_left]
  have : ((q : ℤ) - s) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : ((q : ℤ) * s * 4) ≤ ((q : ℤ) + s) ^ 2 := by nlinarith
  exact_mod_cast h2

/-- `2m + 2 ≤ ⌊(m+3)²/4⌋`. -/
lemma two_mul_add_two_le (m : ℕ) : 2 * m + 2 ≤ (m + 3) ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have : ((m : ℤ) - 1) ^ 2 ≥ 0 := sq_nonneg _
  have : (((2 * m + 2) * 4 : ℕ) : ℤ) ≤ (((m + 3) ^ 2 : ℕ) : ℤ) := by push_cast; nlinarith
  exact_mod_cast this

/-- **Theorem 2, third statement, for arbitrary admissible sets.** If `G` is a completion of
least rank `q ≤ m`, there is `T` with `|T| ≤ q (m + 3 - q)` such that a fit on `T` gives a fit
of `Σ`. (The paper assumes `2 ≤ q`; the argument does not use it.) -/
theorem theorem2_sets_iii (A : n → Set ℝ) (m : ℕ) (Sig G : Matrix n n ℝ)
    (hG : IsCompletionIn A Sig G) (hmin : ∀ G', IsCompletionIn A Sig G' → G.rank ≤ G'.rank)
    (hqm : G.rank ≤ m) :
    ∃ T : Finset n, T.card ≤ G.rank * (m + 3 - G.rank) ∧
      (HasFitIn m (fun a : T => A a) (subPattern Sig T) → HasFitIn m A Sig) := by
  classical
  set q := G.rank with hq
  set t := m + 3 - q with ht
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset n).powerset
    (fun X => ((univ \ X).card : ℤ) + (t : ℤ) * frk ℝ G.row X)
    ⟨univ, mem_powerset.2 (Subset.refl _)⟩
  have hpack : ∀ Z ⊆ X, (t : ℤ) * frk ℝ G.row X ≤ (X \ Z).card + (t : ℤ) * frk ℝ G.row Z := by
    intro Z hZ
    have h1 := hXmin Z (mem_powerset.2 (subset_univ Z))
    have e1 := card_sdiff_eq' (subset_univ X)
    have e2 := card_sdiff_eq' (subset_univ Z)
    have e3 := card_sdiff_eq' hZ
    linarith
  obtain ⟨B, hBX, hBd, hBc, hBs⟩ := spanning_bases (F := ℝ) G.row t X hpack
  set T := (univ \ X) ∪ univ.biUnion B with hT
  have hTcard : T.card ≤ q * (m + 3 - q) := by
    have h1 : T.card ≤ (univ \ X).card + ∑ a, (B a).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
    have h2 : ∑ a : Fin t, (B a).card = t * frk ℝ G.row X := by simp [hBc]
    have h3 := hXmin univ (mem_powerset.2 (Subset.refl _))
    simp only [sdiff_self, bot_eq_empty, card_empty, Nat.cast_zero, zero_add] at h3
    have h4 : frk ℝ G.row univ = q := (rank_eq_frk_univ G).symm
    rw [h4] at h3
    rw [h2] at h1
    have h5 : (T.card : ℤ) ≤ t * q := by
      have : (T.card : ℤ) ≤ (univ \ X).card + (t : ℤ) * frk ℝ G.row X := by exact_mod_cast h1
      linarith
    have h6 : T.card ≤ t * q := by exact_mod_cast h5
    rw [mul_comm] at h6
    exact h6
  refine ⟨T, hTcard, ?_⟩
  rintro ⟨H, hHc, hHpsd, hHr⟩
  obtain ⟨k, v, hv⟩ := exists_gram_of_posSemidef hHpsd
  set Esp := span ℝ (Set.range v) with hEspdef
  set w : T → Esp := fun a => ⟨v a, subset_span ⟨a, rfl⟩⟩ with hwdef
  have hw : ∀ a b, inner ℝ (w a) (w b) = H a b := by
    intro a b; rw [← hv]; simp [w, gram_apply]
  have hEsp : finrank ℝ Esp ≤ m := by
    have := rank_gram v
    rw [hv] at this
    change finrank ℝ (span ℝ (Set.range v)) ≤ m
    omega
  set hn : n → Esp := fun i => if hi : i ∈ T then w ⟨i, hi⟩ else 0 with hndef
  have hnT : ∀ i (hi : i ∈ T) j (hj : j ∈ T), inner ℝ (hn i) (hn j) = H ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i hi j hj; simp [hn, hi, hj, hw]
  obtain ⟨G', hG'c, hG'p, hG'r⟩ := extend_fit A Sig G hG hmin X t (by omega) B hBX hBd hBs hn
    (fun i j hi hj hij => by
      rw [hnT i hi j hj]
      exact hHc.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (fun e => hij (congrArg Subtype.val e)))
    (fun i hi => by
      have hiT : i ∈ T := mem_union_left _ (by simp [hi])
      rw [hnT i hiT i hiT]; exact hHc.2.2 ⟨i, hiT⟩)
    (by omega)
  exact ⟨G', hG'c, hG'p, hG'r.trans hEsp⟩

/-- **Theorem 2 (except its last sentence), for arbitrary admissible sets `A i ⊆ [0, ∞)`.** Let
`q` be the least rank of a symmetric completion of `Σ` with diagonal in the sets `A i`. If
`q > m`, some `Σ_T` with `|T| ≤ 2m + 2` has no positive semidefinite admissible completion of
rank `≤ m`. If `q ≤ 1`, `Σ` has one for every `m ≥ q`. If `2 ≤ q ≤ m`, there is `T` with
`|T| ≤ q (m + 3 - q)` such that `Σ` has one iff `Σ_T` has one. -/
theorem theorem2_sets (A : n → Set ℝ) (hA : ∀ i, A i ⊆ Set.Ici 0) (m : ℕ) (Sig : Matrix n n ℝ)
    (q : ℕ) (hq : IsLeast {r | ∃ G, IsCompletionIn A Sig G ∧ G.rank = r} q) :
    (m < q → ∃ T : Finset n, T.card ≤ 2 * m + 2 ∧
        ¬ HasFitIn m (fun a : T => A a) (subPattern Sig T)) ∧
    (q ≤ 1 → ∀ m', q ≤ m' → HasFitIn m' A Sig) ∧
    (2 ≤ q → q ≤ m → ∃ T : Finset n, T.card ≤ q * (m + 3 - q) ∧
      (HasFitIn m A Sig ↔ HasFitIn m (fun a : T => A a) (subPattern Sig T))) := by
  obtain ⟨⟨G, hG, hGq⟩, hmin'⟩ := hq
  have hmin : ∀ G', IsCompletionIn A Sig G' → G.rank ≤ G'.rank := fun G' hG' => by
    rw [hGq]; exact hmin' ⟨G', hG', rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hmq
    by_contra hcon
    push Not at hcon
    obtain ⟨G', hG', hr'⟩ := lemma1_sets m A Sig (fun T hT => by
      obtain ⟨H, hH, -, hHr⟩ := hcon T hT
      exact ⟨H, hH, hHr⟩)
    have := hmin G' hG'
    omega
  · intro hq1 m' hm'
    refine ⟨G, hG, posSemidef_of_rank_le_one hG.1 (by omega) (fun i => hA i (hG.2.2 i)), by omega⟩
  · intro hq2 hqm
    obtain ⟨T, hT, hfit⟩ := theorem2_sets_iii A m Sig G hG hmin (by omega)
    rw [hGq] at hT
    exact ⟨T, hT, ⟨fun h => h.restrict T, hfit⟩⟩

/-- **Upper bound of Theorem 1, for arbitrary admissible sets `A i ⊆ [0, ∞)`.** If every
`Σ_T` with `|T| ≤ ⌊(m+3)²/4⌋` has a positive semidefinite admissible completion of rank
`≤ m`, so has `Σ`. -/
theorem upper_bound_sets (A : n → Set ℝ) (hA : ∀ i, A i ⊆ Set.Ici 0) (m : ℕ)
    (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ (m + 3) ^ 2 / 4 →
      HasFitIn m (fun a : T => A a) (subPattern Sig T)) :
    HasFitIn m A Sig := by
  classical
  obtain ⟨G0, hG0, hG0r⟩ := lemma1_sets m A Sig (fun T hT => by
    obtain ⟨H, hH, -, hHr⟩ := h T (hT.trans (two_mul_add_two_le m))
    exact ⟨H, hH, hHr⟩)
  have hex : ∃ r, ∃ G, IsCompletionIn A Sig G ∧ G.rank = r := ⟨_, G0, hG0, rfl⟩
  set q := Nat.find hex with hqdef
  have hq : IsLeast {r | ∃ G, IsCompletionIn A Sig G ∧ G.rank = r} q :=
    ⟨Nat.find_spec hex, fun r hr => Nat.find_min' hex hr⟩
  have hqm : q ≤ m := (Nat.find_min' hex ⟨G0, hG0, rfl⟩).trans hG0r
  obtain ⟨-, h2, h3⟩ := theorem2_sets A hA m Sig q hq
  by_cases hq1 : q ≤ 1
  · exact h2 hq1 m hqm
  · obtain ⟨T, hT, hiff⟩ := h3 (by omega) hqm
    exact hiff.2 (h T (hT.trans (mul_sub_le_sq_div m q (by omega))))

section Paper

lemma refSets_nonneg (Sig : Matrix n n ℝ) : ∀ i, refSets Sig i ⊆ Set.Ici 0 :=
  fun _ _ hx => hx.1

lemma weakRefSets_nonneg (Sig : Matrix n n ℝ) : ∀ i, weakRefSets Sig i ⊆ Set.Ici 0 :=
  fun _ _ hx => hx.1

lemma inModel_iff_hasFitIn (m : ℕ) (Sig : Matrix n n ℝ) :
    InModel m Sig ↔ HasFitIn m (refSets Sig) Sig :=
  (inModel_iff_exists_fit m Sig).trans (exists_fit_iff_hasFitIn m Sig)

lemma inWeakModel_iff_hasFitIn (m : ℕ) (Sig : Matrix n n ℝ) :
    InWeakModel m Sig ↔ HasFitIn m (weakRefSets Sig) Sig :=
  (inWeakModel_iff_exists_weakFit m Sig).trans (exists_weakFit_iff_hasFitIn m Sig)

/-- **Theorem 2, first three statements** (the paper's form). Let `q` be the least rank of a
reference of `Σ`. If `q > m`, then `Σ_T ∉ F_{|T|,m}` for some `T` with `|T| ≤ 2m + 2`. If
`q ≤ 1`, then `Σ ∈ F_{n,m}` for every `m ≥ q`. If `2 ≤ q ≤ m`, there is a set `T` of at most
`q (m + 3 - q)` variables with `Σ ∈ F_{n,m} ↔ Σ_T ∈ F_{|T|,m}`. -/
theorem theorem2_first (m : ℕ) (Sig : Matrix n n ℝ) (q : ℕ)
    (hq : IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q) :
    (m < q → ∃ T : Finset n, T.card ≤ 2 * m + 2 ∧ ¬ InModel m (subPattern Sig T)) ∧
    (q ≤ 1 → ∀ m', q ≤ m' → InModel m' Sig) ∧
    (2 ≤ q → q ≤ m → ∃ T : Finset n, T.card ≤ q * (m + 3 - q) ∧
      (InModel m Sig ↔ InModel m (subPattern Sig T))) := by
  simp only [isReference_iff] at hq
  simp only [inModel_iff_hasFitIn]
  exact theorem2_sets (refSets Sig) (refSets_nonneg Sig) m Sig q hq

/-- **Theorem 2, first three statements, weak model** (weak references and `F̄`). -/
theorem theorem2_first_weak (m : ℕ) (Sig : Matrix n n ℝ) (q : ℕ)
    (hq : IsLeast {r | ∃ G, IsWeakReference Sig G ∧ G.rank = r} q) :
    (m < q → ∃ T : Finset n, T.card ≤ 2 * m + 2 ∧ ¬ InWeakModel m (subPattern Sig T)) ∧
    (q ≤ 1 → ∀ m', q ≤ m' → InWeakModel m' Sig) ∧
    (2 ≤ q → q ≤ m → ∃ T : Finset n, T.card ≤ q * (m + 3 - q) ∧
      (InWeakModel m Sig ↔ InWeakModel m (subPattern Sig T))) := by
  simp only [isWeakReference_iff] at hq
  simp only [inWeakModel_iff_hasFitIn]
  exact theorem2_sets (weakRefSets Sig) (weakRefSets_nonneg Sig) m Sig q hq

/-- **Upper bound of Theorem 1.** If `Σ_T ∈ F_{|T|,m}` for every `T` with
`|T| ≤ ⌊(m+3)²/4⌋`, then `Σ ∈ F_{n,m}`. -/
theorem upper_bound (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ (m + 3) ^ 2 / 4 → InModel m (subPattern Sig T)) :
    InModel m Sig := by
  simp only [inModel_iff_hasFitIn] at h ⊢
  exact upper_bound_sets (refSets Sig) (refSets_nonneg Sig) m Sig h

/-- **Upper bound of Theorem 1, weak model.** -/
theorem upper_bound_weak (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ (m + 3) ^ 2 / 4 → InWeakModel m (subPattern Sig T)) :
    InWeakModel m Sig := by
  simp only [inWeakModel_iff_hasFitIn] at h ⊢
  exact upper_bound_sets (weakRefSets Sig) (weakRefSets_nonneg Sig) m Sig h

end Paper

end FreeDiagonal.StatisticalFactorAnalysis
