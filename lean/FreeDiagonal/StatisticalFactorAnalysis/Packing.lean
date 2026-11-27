import FreeDiagonal.Foundations.Union

/-!
# Base packing for `t` copies of a linear matroid, every `t`

For a family of vectors `u : ι → V` and a finite set `X`, if
`t rk(X) ≤ |X \ Z| + t rk(Z)` for every `Z ⊆ X`, then `X` contains `t` pairwise disjoint sets,
each of size `rk X` and spanning the span of `X` (`spanning_bases`).

Route: `rk_t(Y) = min_{W ⊆ Y} |Y \ W| + t rk(W)` is submodular (`rkt_submod`); the project's
min-max inequality `union_minmax_submodular` (Foundations/Union.lean) applied to `(rk, rk_t)`
splits off one full-rank part and leaves a set satisfying the hypothesis for `t`; induction on
`t`. (For `t = 3` this is the argument of `EvenComplementation/Packing.lean`.)
-/

open Finset Submodule Module

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {F : Type*} [Field F] {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module F V]

/-- `rk_t(Y) = min_{W ⊆ Y} (|Y \ W| + t rk(W))`. -/
noncomputable def rkt (t : ℕ) (u : ι → V) (Y : Finset ι) : ℤ :=
  Y.powerset.inf' ⟨∅, empty_mem_powerset Y⟩
    (fun W => ((Y \ W).card : ℤ) + (t : ℤ) * (frk F u W : ℤ))

lemma rkt_le (t : ℕ) (u : ι → V) {Y W : Finset ι} (h : W ⊆ Y) :
    rkt (F := F) t u Y ≤ ((Y \ W).card : ℤ) + (t : ℤ) * (frk F u W : ℤ) :=
  Finset.inf'_le _ (mem_powerset.2 h)

lemma exists_rkt (t : ℕ) (u : ι → V) (Y : Finset ι) :
    ∃ W ⊆ Y, rkt (F := F) t u Y = ((Y \ W).card : ℤ) + (t : ℤ) * (frk F u W : ℤ) := by
  obtain ⟨W, hW, h⟩ := Finset.exists_mem_eq_inf' (s := Y.powerset) ⟨∅, empty_mem_powerset Y⟩
    (fun W => ((Y \ W).card : ℤ) + (t : ℤ) * (frk F u W : ℤ))
  exact ⟨W, mem_powerset.1 hW, h⟩

lemma card_sdiff_eq' {A B : Finset ι} (h : B ⊆ A) : ((A \ B).card : ℤ) = A.card - B.card := by
  have := card_sdiff_add_card_eq_card h
  omega

lemma rkt_submod (t : ℕ) (u : ι → V) : Submod (rkt (F := F) t u) := by
  intro P Q
  obtain ⟨W1, hW1, e1⟩ := exists_rkt (F := F) t u P
  obtain ⟨W2, hW2, e2⟩ := exists_rkt (F := F) t u Q
  have hU : W1 ∪ W2 ⊆ P ∪ Q := union_subset_union hW1 hW2
  have hI : W1 ∩ W2 ⊆ P ∩ Q := inter_subset_inter hW1 hW2
  have h1 := rkt_le (F := F) t u hU
  have h2 := rkt_le (F := F) t u hI
  have hs := frk_submod (F := F) u W1 W2
  simp only at hs
  rw [card_sdiff_eq' hU] at h1
  rw [card_sdiff_eq' hI] at h2
  rw [e1, e2, card_sdiff_eq' hW1, card_sdiff_eq' hW2]
  have c1 := card_union_add_card_inter P Q
  have c2 := card_union_add_card_inter W1 W2
  have ht : (0 : ℤ) ≤ t := by positivity
  nlinarith

/-- **`t` disjoint full-rank parts.** If `t rk(X) ≤ |X \ Z| + t rk(Z)` for every `Z ⊆ X`, then
`X` contains `t` pairwise disjoint sets, each of rank `rk(X)`. -/
theorem full_rank_parts (u : ι → V) : ∀ (t : ℕ) (X : Finset ι),
    (∀ Z ⊆ X, (t : ℤ) * frk F u X ≤ (X \ Z).card + (t : ℤ) * frk F u Z) →
    ∃ A : Fin t → Finset ι, (∀ a, A a ⊆ X) ∧ (∀ a b, a ≠ b → Disjoint (A a) (A b)) ∧
      ∀ a, frk F u (A a) = frk F u X := by
  intro t
  induction t with
  | zero =>
    intro X _
    exact ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ t ih =>
    intro X h
    obtain ⟨A0, hA0, Z, hZ, h1⟩ := union_minmax_submodular X (fun Y => (frk F u Y : ℤ))
      (rkt (F := F) t u) (frk_submod (F := F) u) (rkt_submod t u)
    obtain ⟨W, hW, eW⟩ := exists_rkt (F := F) t u Z
    have hWX : W ⊆ X := hW.trans hZ
    have hmW := frk_mono (F := F) u hW
    have hWh := h W hWX
    have cXZ := card_sdiff_eq' hZ
    have cZW := card_sdiff_eq' hW
    have cXW := card_sdiff_eq' hWX
    rw [eW] at h1
    set X' := X \ A0 with hX'
    have hX'X : X' ⊆ X := sdiff_subset
    have m1 := frk_mono (F := F) u hA0
    have m2 := frk_mono (F := F) u hX'X
    have h3 := rkt_le (F := F) t u (Subset.refl X')
    simp only [sdiff_self, Finset.bot_eq_empty, card_empty, Nat.cast_zero, zero_add] at h3
    push_cast at hWh h1
    have ht : (0 : ℤ) ≤ t := by positivity
    -- key inequality: `t rk X ≤ rk_t(X')`
    have m1' : (frk F u A0 : ℤ) ≤ frk F u X := by exact_mod_cast m1
    have hmW' : (frk F u W : ℤ) ≤ frk F u Z := by exact_mod_cast hmW
    have hbig : (t : ℤ) * frk F u X + frk F u X ≤ frk F u A0 + rkt (F := F) t u X' := by
      linarith
    have hkey : (t : ℤ) * frk F u X ≤ rkt (F := F) t u X' := by linarith
    have hA0r : frk F u A0 = frk F u X := by
      have : (frk F u X : ℤ) ≤ frk F u A0 := by
        have := rkt_le (F := F) t u (Subset.refl X')
        have hm2 : (t : ℤ) * frk F u X' ≤ (t : ℤ) * frk F u X :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast m2) ht
        simp only [sdiff_self, Finset.bot_eq_empty, card_empty, Nat.cast_zero, zero_add] at this
        linarith [hbig, this, hm2]
      omega
    have hX'h : ∀ Z' ⊆ X', (t : ℤ) * frk F u X' ≤ (X' \ Z').card + (t : ℤ) * frk F u Z' := by
      intro Z' hZ'
      have := rkt_le (F := F) t u hZ'
      have : (t : ℤ) * frk F u X' ≤ (t : ℤ) * frk F u X :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast m2) ht
      linarith
    obtain ⟨A, hA, hAd, hAr⟩ := ih X' hX'h
    refine ⟨Fin.cons A0 A, ?_, ?_, ?_⟩
    · intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hA0
      · simpa using (hA a).trans hX'X
    · intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd rfl hab
        | succ b =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact disjoint_of_subset_right (hA b) disjoint_sdiff
      | succ a =>
        induction b using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact disjoint_of_subset_left (hA a) sdiff_disjoint
        | succ b =>
          simp only [Fin.cons_succ]
          exact hAd a b (fun e => hab (by rw [e]))
    · intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hA0r
      · simp only [Fin.cons_succ]
        rw [hAr a]
        -- `t ≥ 1` here, so `rk X' = rk X`
        have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast a.pos
        have : (t : ℤ) * frk F u X ≤ (t : ℤ) * frk F u X' := by linarith
        have := le_of_mul_le_mul_left this (by linarith)
        omega

/-- **`t` disjoint bases.** Under the hypothesis of `full_rank_parts`, `X` contains `t` pairwise
disjoint sets `B_a`, each of size `rk(X)` and each spanning the span of `X`. -/
theorem spanning_bases (u : ι → V) (t : ℕ) (X : Finset ι)
    (h : ∀ Z ⊆ X, (t : ℤ) * frk F u X ≤ (X \ Z).card + (t : ℤ) * frk F u Z) :
    ∃ B : Fin t → Finset ι, (∀ a, B a ⊆ X) ∧ (∀ a b, a ≠ b → Disjoint (B a) (B b)) ∧
      (∀ a, (B a).card = frk F u X) ∧
      ∀ a, span F (u '' (B a : Set ι)) = span F (u '' (X : Set ι)) := by
  obtain ⟨A, hA, hAd, hAr⟩ := full_rank_parts u t X h
  have sp : ∀ a, ∃ B ⊆ A a, B.card = frk F u X ∧
      span F (u '' (B : Set ι)) = span F (u '' (X : Set ι)) := by
    intro a
    obtain ⟨B, hB, hc, hs⟩ := exists_basis_subset (F := F) u (A a)
    refine ⟨B, hB, hc.trans (hAr a), hs.trans ?_⟩
    exact Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (coe_subset.2 (hA a))))
      (hAr a)
  choose B hB hc hs using sp
  exact ⟨B, fun a => (hB a).trans (hA a),
    fun a b hab => disjoint_of_subset_left (hB a) (disjoint_of_subset_right (hB b) (hAd a b hab)),
    hc, hs⟩

end FreeDiagonal.StatisticalFactorAnalysis
