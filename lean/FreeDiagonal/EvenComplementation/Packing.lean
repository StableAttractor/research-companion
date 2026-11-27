import FreeDiagonal.Foundations.Union

/-!
# Part 54, Lean: three disjoint bases (base packing for three copies of a linear matroid)

For a family of vectors `u : ι → V` and a finite set `X`, if
`3 rk(X) ≤ |X \ Z| + 3 rk(Z)` for every `Z ⊆ X`, then `X` contains three pairwise disjoint
subsets, each spanning the same subspace as `X` (`three_spanning_bases`, with the subsets
independent of size `rk X`).

Route: `rk₂(Y) = min_{W ⊆ Y} |Y \ W| + 2 rk(W)` (the rank of the union of two copies) is
submodular (`rk2_submod`, a direct computation, no matroid axioms needed); the project's
min-max inequality `union_minmax_submodular` (Foundations/Union.lean), applied once to
`(rk, rk₂)` and once to `(rk, rk)`, splits `X` into three parts of full rank.
-/

open Finset Submodule Module

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable (F : Type*) [Field F] {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module F V]

/-- `rk₂(Y) = min_{W ⊆ Y} (|Y \ W| + 2 rk(W))`. -/
noncomputable def rk2 (u : ι → V) (Y : Finset ι) : ℤ :=
  Y.powerset.inf' ⟨∅, empty_mem_powerset Y⟩ (fun W => ((Y \ W).card : ℤ) + 2 * (frk F u W : ℤ))

variable {F}

lemma rk2_le (u : ι → V) {Y W : Finset ι} (h : W ⊆ Y) :
    rk2 F u Y ≤ ((Y \ W).card : ℤ) + 2 * (frk F u W : ℤ) :=
  Finset.inf'_le _ (mem_powerset.2 h)

lemma exists_rk2 (u : ι → V) (Y : Finset ι) :
    ∃ W ⊆ Y, rk2 F u Y = ((Y \ W).card : ℤ) + 2 * (frk F u W : ℤ) := by
  obtain ⟨W, hW, h⟩ := Finset.exists_mem_eq_inf' (s := Y.powerset) ⟨∅, empty_mem_powerset Y⟩
    (fun W => ((Y \ W).card : ℤ) + 2 * (frk F u W : ℤ))
  exact ⟨W, mem_powerset.1 hW, h⟩

lemma card_sdiff_eq {A B : Finset ι} (h : B ⊆ A) : ((A \ B).card : ℤ) = A.card - B.card := by
  have := card_sdiff_add_card_eq_card h
  omega

lemma rk2_submod (u : ι → V) : Submod (rk2 F u) := by
  intro P Q
  obtain ⟨W1, hW1, e1⟩ := exists_rk2 (F := F) u P
  obtain ⟨W2, hW2, e2⟩ := exists_rk2 (F := F) u Q
  have hU : W1 ∪ W2 ⊆ P ∪ Q := union_subset_union hW1 hW2
  have hI : W1 ∩ W2 ⊆ P ∩ Q := inter_subset_inter hW1 hW2
  have h1 := rk2_le (F := F) u hU
  have h2 := rk2_le (F := F) u hI
  have hs := frk_submod (F := F) u W1 W2
  simp only at hs
  rw [card_sdiff_eq hU] at h1
  rw [card_sdiff_eq hI] at h2
  rw [e1, e2, card_sdiff_eq hW1, card_sdiff_eq hW2]
  have c1 := card_union_add_card_inter P Q
  have c2 := card_union_add_card_inter W1 W2

  linarith

/-- **Three disjoint full-rank parts.** If `3 rk(X) ≤ |X \ Z| + 3 rk(Z)` for every `Z ⊆ X`, then
`X` splits into three pairwise disjoint parts, each of rank `rk(X)`. -/
theorem three_full_rank_parts (u : ι → V) (X : Finset ι)
    (h : ∀ Z ⊆ X, 3 * frk F u X ≤ (X \ Z).card + 3 * frk F u Z) :
    ∃ A1 A2 A3 : Finset ι, A1 ⊆ X ∧ A2 ⊆ X ∧ A3 ⊆ X ∧
      Disjoint A1 A2 ∧ Disjoint A1 A3 ∧ Disjoint A2 A3 ∧
      frk F u A1 = frk F u X ∧ frk F u A2 = frk F u X ∧ frk F u A3 = frk F u X := by
  obtain ⟨A, hA, Z, hZ, h1⟩ := union_minmax_submodular X (fun Y => (frk F u Y : ℤ)) (rk2 F u)
    (frk_submod (F := F) u) (rk2_submod u)
  obtain ⟨W, hW, eW⟩ := exists_rk2 (F := F) u Z
  have hWX : W ⊆ X := hW.trans hZ
  have hmW := frk_mono (F := F) u hW
  have hWh := h W hWX
  have cXZ := card_sdiff_eq hZ
  have cZW := card_sdiff_eq hW
  have cXW := card_sdiff_eq hWX
  obtain ⟨A', hA', W', hW', h2⟩ := union_minmax_submodular (X \ A) (fun Y => (frk F u Y : ℤ))
    (fun Y => (frk F u Y : ℤ)) (frk_submod (F := F) u) (frk_submod (F := F) u)
  have h3 := rk2_le (F := F) u hW'
  have m1 := frk_mono (F := F) u hA
  have hA'X : A' ⊆ X := hA'.trans sdiff_subset
  have m2 := frk_mono (F := F) u hA'X
  have hA3X : (X \ A) \ A' ⊆ X := sdiff_subset.trans sdiff_subset
  have m3 := frk_mono (F := F) u hA3X

  rw [eW] at h1
  refine ⟨A, A', (X \ A) \ A', hA, hA'X, hA3X, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact disjoint_of_subset_right hA' disjoint_sdiff
  · exact disjoint_of_subset_right sdiff_subset disjoint_sdiff
  · exact disjoint_sdiff
  all_goals omega

/-- **Three disjoint bases.** Under the hypothesis of `three_full_rank_parts`, `X` contains three
pairwise disjoint sets `B₁, B₂, B₃`, each of size `rk(X)` and each spanning the span of `X`. -/
theorem three_spanning_bases (u : ι → V) (X : Finset ι)
    (h : ∀ Z ⊆ X, 3 * frk F u X ≤ (X \ Z).card + 3 * frk F u Z) :
    ∃ B1 B2 B3 : Finset ι, B1 ⊆ X ∧ B2 ⊆ X ∧ B3 ⊆ X ∧
      Disjoint B1 B2 ∧ Disjoint B1 B3 ∧ Disjoint B2 B3 ∧
      B1.card = frk F u X ∧ B2.card = frk F u X ∧ B3.card = frk F u X ∧
      span F (u '' (B1 : Set ι)) = span F (u '' (X : Set ι)) ∧
      span F (u '' (B2 : Set ι)) = span F (u '' (X : Set ι)) ∧
      span F (u '' (B3 : Set ι)) = span F (u '' (X : Set ι)) := by
  obtain ⟨A1, A2, A3, h1, h2, h3, d12, d13, d23, r1, r2, r3⟩ := three_full_rank_parts u X h
  have sp : ∀ A ⊆ X, frk F u A = frk F u X →
      ∃ B ⊆ A, B.card = frk F u X ∧ span F (u '' (B : Set ι)) = span F (u '' (X : Set ι)) := by
    intro A hA hr
    obtain ⟨B, hB, hc, hs⟩ := exists_basis_subset (F := F) u A
    refine ⟨B, hB, hc.trans hr, hs.trans ?_⟩
    exact Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (coe_subset.2 hA))) hr
  obtain ⟨B1, hB1, c1, s1⟩ := sp A1 h1 r1
  obtain ⟨B2, hB2, c2, s2⟩ := sp A2 h2 r2
  obtain ⟨B3, hB3, c3, s3⟩ := sp A3 h3 r3
  exact ⟨B1, B2, B3, hB1.trans h1, hB2.trans h2, hB3.trans h3,
    disjoint_of_subset_left hB1 (disjoint_of_subset_right hB2 d12),
    disjoint_of_subset_left hB1 (disjoint_of_subset_right hB3 d13),
    disjoint_of_subset_left hB2 (disjoint_of_subset_right hB3 d23), c1, c2, c3, s1, s2, s3⟩

end FreeDiagonal.EvenComplementation
