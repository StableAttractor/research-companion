import FreeDiagonal.EvenComplementation.Packing
import FreeDiagonal.Witness.Basic

/-!
# Part 54, Lean: the three-basis witness (any field)

For a symmetric completion `G = x + diag d₀` of a pattern `x` (`x` symmetric) there is a set `T`
of at most `3 rank G` indices such that every completion `H` of the sub-pattern `x_T` lifts to a
completion of `x` of rank at most `rank H` that keeps `H`'s diagonal value at any one prescribed
index of `T` (`witness3`).

This is the route of the pit-stop note (QX-01, Section 1.2 with `t = 3`), not the rank formula of
Part 54: choose `X` minimising `|Xᶜ| + 3 rk(X)` (rows of `G`), take three disjoint bases of the
rows in `X` (`three_spanning_bases`), put `T = Xᶜ ∪ B₁ ∪ B₂ ∪ B₃`, and compare ranks on the
rectangle `(Xᶜ ∪ P ∪ B_a) × (Xᶜ ∪ P ∪ B_b)` for two bases avoiding the prescribed set `P`
(`lift_two`, the rectangle comparison of Part 51 with a prescribed set `P`).
-/

open Matrix Module Submodule Finset

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Rectangle comparison with a prescribed set `P`.** `X` a set of indices, `Ba, Bb ⊆ X`
disjoint, both spanning the rows of `G = x + diag d₀` indexed by `X`, `G` symmetric; `T ⊇ Xᶜ ∪ Ba
∪ Bb ∪ P` and `P` disjoint from `Ba, Bb`. Then every completion `x_T + diag d` lifts to a
completion `x + diag d'` of no larger rank with `d' = d` on `P`. -/
theorem lift_two (x : Matrix n n F) (d0 : n → F) (hG : (x + diagonal d0).IsSymm)
    (X T P Ba Bb : Finset n) (hYT : univ \ X ⊆ T) (hBaX : Ba ⊆ X) (hBbX : Bb ⊆ X)
    (hBaT : Ba ⊆ T) (hBbT : Bb ⊆ T) (hPT : P ⊆ T) (hab : Disjoint Ba Bb) (hPa : Disjoint P Ba)
    (hPb : Disjoint P Bb)
    (hspa : span F ((x + diagonal d0).row '' (Ba : Set n)) =
      span F ((x + diagonal d0).row '' (X : Set n)))
    (hspb : span F ((x + diagonal d0).row '' (Bb : Set n)) =
      span F ((x + diagonal d0).row '' (X : Set n)))
    (d : n → F) :
    ∃ d' : n → F, (∀ j ∈ P, d' j = d j) ∧
      (x + diagonal d').rank ≤ (subPattern x T + diagonal (fun a : T => d a)).rank := by
  classical
  set G := x + diagonal d0 with hGdef
  set d' : n → F := fun j => if j ∈ X ∧ j ∉ P then d0 j else d j with hd'
  refine ⟨d', fun j hj => by simp [hd', hj], ?_⟩
  set H := x + diagonal d'
  set R := (univ \ X) ∪ P ∪ Ba
  set C := (univ \ X) ∪ P ∪ Bb
  have hRT : ∀ r ∈ R, r ∈ T := by
    intro r hr
    rcases mem_union.1 hr with h | h
    · rcases mem_union.1 h with h' | h'
      · exact hYT h'
      · exact hPT h'
    · exact hBaT h
  have hCT : ∀ s ∈ C, s ∈ T := by
    intro r hr
    rcases mem_union.1 hr with h | h
    · rcases mem_union.1 h with h' | h'
      · exact hYT h'
      · exact hPT h'
    · exact hBbT h
  have hrowX : ∀ i ∈ X, i ∉ P → H.row i = G.row i := by
    intro i hi hiP; ext s
    by_cases h : i = s
    · subst h; simp [H, G, d', hi, hiP]
    · simp [H, G, diagonal_apply_ne _ h]
  have hcolX : ∀ s ∈ X, s ∉ P → H.col s = G.col s := by
    intro s hs hsP; ext r
    by_cases h : r = s
    · subst h; simp [H, G, d', hs, hsP]
    · simp [H, G, diagonal_apply_ne _ h]
  have hcolrow : ∀ s, G.col s = G.row s := by
    intro s; ext r
    have := congrFun (congrFun hG r) s
    simpa [transpose_apply] using this.symm
  have hBaP : ∀ l ∈ Ba, l ∉ P := fun l hl hP => disjoint_left.1 hPa hP hl
  have hBbP : ∀ l ∈ Bb, l ∉ P := fun l hl hP => disjoint_left.1 hPb hP hl
  have hR : ∀ i, H.row i ∈ span F (H.row '' (R : Set n)) := by
    intro i
    by_cases hi : i ∈ X ∧ i ∉ P
    · have hGi : G.row i ∈ span F (G.row '' (Ba : Set n)) := by
        rw [hspa]; exact subset_span ⟨i, hi.1, rfl⟩
      have e : G.row '' (Ba : Set n) = H.row '' (Ba : Set n) :=
        Set.image_congr (fun l hl => (hrowX l (hBaX hl) (hBaP l hl)).symm)
      rw [hrowX i hi.1 hi.2]
      rw [e] at hGi
      exact span_mono (Set.image_mono (coe_subset.2 subset_union_right)) hGi
    · apply subset_span
      refine ⟨i, ?_, rfl⟩
      simp only [R, coe_union, Set.mem_union, mem_coe, mem_sdiff, mem_univ, true_and]
      by_cases hX : i ∈ X
      · exact Or.inl (Or.inr (by tauto))
      · exact Or.inl (Or.inl hX)
  have hC : ∀ s, H.col s ∈ span F (H.col '' (C : Set n)) := by
    intro s
    by_cases hs : s ∈ X ∧ s ∉ P
    · have hGs : G.col s ∈ span F (G.col '' (Bb : Set n)) := by
        rw [hcolrow, Set.image_congr (fun l _ => hcolrow l), hspb]
        exact subset_span ⟨s, hs.1, rfl⟩
      have e : G.col '' (Bb : Set n) = H.col '' (Bb : Set n) :=
        Set.image_congr (fun l hl => (hcolX l (hBbX hl) (hBbP l hl)).symm)
      rw [hcolX s hs.1 hs.2]
      rw [e] at hGs
      exact span_mono (Set.image_mono (coe_subset.2 subset_union_right)) hGs
    · apply subset_span
      refine ⟨s, ?_, rfl⟩
      simp only [C, coe_union, Set.mem_union, mem_coe, mem_sdiff, mem_univ, true_and]
      by_cases hX : s ∈ X
      · exact Or.inl (Or.inr (by tauto))
      · exact Or.inl (Or.inl hX)
  have key := rank_le_submatrix_of_span H R C hR hC
  have e : H.submatrix (fun r : R => (r : n)) (fun s : C => (s : n)) =
      (subPattern x T + diagonal (fun a : T => d a)).submatrix (fun r : R => ⟨r, hRT r r.2⟩)
        (fun s : C => ⟨s, hCT s s.2⟩) := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    by_cases hrs : r = s
    · subst hrs
      have hrX : ¬ (r ∈ X ∧ r ∉ P) := by
        rintro ⟨hX, hP⟩
        have h1 : r ∈ Ba := by
          rcases mem_union.1 hr with h | h
          · rcases mem_union.1 h with h' | h'
            · exact absurd hX (mem_sdiff.1 h').2
            · exact absurd h' hP
          · exact h
        have h2 : r ∈ Bb := by
          rcases mem_union.1 hs with h | h
          · rcases mem_union.1 h with h' | h'
            · exact absurd hX (mem_sdiff.1 h').2
            · exact absurd h' hP
          · exact h
        exact disjoint_left.1 hab h1 h2
      simp [H, d', hrX, subPattern]
    · have hne : (⟨r, hRT r hr⟩ : T) ≠ ⟨s, hCT s hs⟩ := fun h => hrs (congrArg Subtype.val h)
      simp [H, subPattern, diagonal_apply_ne _ hrs, diagonal_apply_ne _ hne]
  calc (x + diagonal d').rank ≤ _ := key
    _ = _ := by rw [e]
    _ ≤ _ := rank_submatrix_le _ _ _

omit [Fintype n] [DecidableEq n] in
lemma disjoint_of_card_le_one {P B B' : Finset n} (hP : P.card ≤ 1) (hB : ¬ Disjoint P B)
    (hBB' : Disjoint B B') : Disjoint P B' := by
  rw [not_disjoint_iff] at hB
  obtain ⟨p, hpP, hpB⟩ := hB
  rw [disjoint_left]
  intro q hqP hqB'
  have := card_le_one.1 hP p hpP q hqP
  subst this
  exact disjoint_left.1 hBB' hpB hqB'

/-- **The three-basis witness, for a given `X`.** If the rows of `G` indexed by `X` satisfy the
base-packing condition for three copies, then `T = Xᶜ ∪ B₁ ∪ B₂ ∪ B₃` (three disjoint bases of
those rows) has `|T| ≤ |Xᶜ| + 3 rk(X)` and lifts completions keeping one prescribed diagonal
value. -/
theorem witness3_of_set (x : Matrix n n F) (d0 : n → F) (hG : (x + diagonal d0).IsSymm)
    (X : Finset n)
    (hX : ∀ Z ⊆ X, 3 * frk F (x + diagonal d0).row X ≤
      (X \ Z).card + 3 * frk F (x + diagonal d0).row Z) :
    ∃ T : Finset n, T.card ≤ (univ \ X).card + 3 * frk F (x + diagonal d0).row X ∧
      ∀ (d : n → F) (P : Finset n), P ⊆ T → P.card ≤ 1 →
        ∃ d' : n → F, (∀ j ∈ P, d' j = d j) ∧
          (x + diagonal d').rank ≤ (subPattern x T + diagonal (fun a : T => d a)).rank := by
  classical
  obtain ⟨B1, B2, B3, h1, h2, h3, d12, d13, d23, c1, c2, c3, s1, s2, s3⟩ :=
    three_spanning_bases (x + diagonal d0).row X hX
  set T := (univ \ X) ∪ B1 ∪ B2 ∪ B3 with hT
  refine ⟨T, ?_, ?_⟩
  · calc T.card ≤ ((univ \ X) ∪ B1 ∪ B2).card + B3.card := card_union_le _ _
      _ ≤ ((univ \ X) ∪ B1).card + B2.card + B3.card := by gcongr; exact card_union_le _ _
      _ ≤ (univ \ X).card + B1.card + B2.card + B3.card := by gcongr; exact card_union_le _ _
      _ = _ := by rw [c1, c2, c3]; ring
  intro d P hPT hP
  have hYT : univ \ X ⊆ T := fun i hi => by simp [hT, mem_union, hi]
  have hB1T : B1 ⊆ T := fun i hi => by simp [hT, mem_union, hi]
  have hB2T : B2 ⊆ T := fun i hi => by simp [hT, mem_union, hi]
  have hB3T : B3 ⊆ T := fun i hi => by simp [hT, mem_union, hi]
  by_cases hP1 : Disjoint P B1
  · by_cases hP2 : Disjoint P B2
    · exact lift_two x d0 hG X T P B1 B2 hYT h1 h2 hB1T hB2T hPT d12 hP1 hP2 s1 s2 d
    · exact lift_two x d0 hG X T P B1 B3 hYT h1 h3 hB1T hB3T hPT d13 hP1
        (disjoint_of_card_le_one hP hP2 d23) s1 s3 d
  · exact lift_two x d0 hG X T P B2 B3 hYT h2 h3 hB2T hB3T hPT d23
      (disjoint_of_card_le_one hP hP1 d12) (disjoint_of_card_le_one hP hP1 d13) s2 s3 d

/-- **The three-basis witness.** For a symmetric completion `G = x + diag d₀` there is `T` with
`|T| ≤ 3 rank G` such that every completion of `x_T` lifts to a completion of `x` of no larger
rank keeping its diagonal value at any one prescribed index (or at none). -/
theorem witness3 (x : Matrix n n F) (d0 : n → F) (hG : (x + diagonal d0).IsSymm) :
    ∃ T : Finset n, T.card ≤ 3 * (x + diagonal d0).rank ∧
      ∀ (d : n → F) (P : Finset n), P ⊆ T → P.card ≤ 1 →
        ∃ d' : n → F, (∀ j ∈ P, d' j = d j) ∧
          (x + diagonal d').rank ≤ (subPattern x T + diagonal (fun a : T => d a)).rank := by
  classical
  set u := (x + diagonal d0).row
  set f : Finset n → ℕ := fun X => (univ \ X).card + 3 * frk F u X
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset (Finset n)) f univ_nonempty
  have hX : ∀ Z ⊆ X, 3 * frk F u X ≤ (X \ Z).card + 3 * frk F u Z := by
    intro Z hZ
    have h := hXmin Z (mem_univ _)
    simp only [f] at h
    have e1 := card_sdiff_add_card_eq_card (subset_univ X)
    have e2 := card_sdiff_add_card_eq_card (subset_univ Z)
    have e3 := card_sdiff_add_card_eq_card hZ
    omega
  obtain ⟨T, hT, hlift⟩ := witness3_of_set x d0 hG X hX
  refine ⟨T, ?_, hlift⟩
  have h := hXmin univ (mem_univ _)
  simp only [f, sdiff_self] at h
  rw [rank_eq_frk_univ]
  have h0 : (univ \ univ : Finset n).card = 0 := by simp
  simp only [u] at h hT
  rw [sdiff_self] at h0
  omega

end FreeDiagonal.EvenComplementation
