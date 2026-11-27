import FreeDiagonal.EvenComplementation.UpperBound
import FreeDiagonal.EvenComplementation.LinAlg

/-!
# Part 54-g in Lean, part 1: a minimal forbidden graph on `3k` vertices (`k ≥ 3`)

`G` minimal forbidden for `c₂ ≤ k`, `|V| = 3k`, `A` its adjacency matrix over `F₂`.
* `class_setup` (54-g (1)): `mr = k`, `rank A = k`, `A` is the only completion of rank `k`.
* `class_packing` (54-g (2), via 54-c): `3k ≤ |Zᶜ| + 3 rk(Z)` for every `Z`, so the rows split
  into three disjoint bases `B₁, B₂, B₃` (`class_bases`).
* `exists_word` (54-g (3)): for every vertex `v` some `w = A y` has `w v ≠ 0` and at most three
  non-zero entries. Proof: `c₂(G - v) ≤ k` gives `D ≠ 0` on `V - v` with `rank(A' + D) ≤ k`; the
  project's rank formula (`rank_formula`, Theorem 1 of the note, applied to the factorisation
  `A = C Θ Cᵀ` of `factor_symm`) gives `rank(A' + D) ≥ |T| + 2r - k`; counting rows of the three
  bases gives `|T| + 1 ≥ 3(k - r)`; so `r = k - 1` and `|Zᶜ| ≤ 3`, where `Z` is the zero set of
  `D`.
-/

open Matrix Module Submodule Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma add_diagonal_zero' {R : Type*} [AddMonoid R] (M : Matrix V V R) : M + diagonal 0 = M := by
  ext i j; by_cases h : i = j <;> simp [h]

/-- **54-g (1).** -/
theorem class_setup (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    mrF2 G = k ∧
      (∀ d : V → ZMod 2, (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G → d = 0) ∧
      (G.adjMatrix (ZMod 2)).rank = k := by
  classical
  have hmr : mrF2 G ≤ k := by
    by_contra hgt
    have h : ¬ ∀ s : Finset V, s.card ≤ 2 * k + 2 → mrF2 (G.induce (s : Set V)) ≤ k := by
      rw [← cor4_threshold]; exact hgt
    push Not at h
    obtain ⟨s, hs, hmrs⟩ := h
    have hsu : s ≠ univ := by
      intro h; rw [h, card_univ, hV] at hs; omega
    have := hmin s hsu
    have := mrF2_le_c2 (G.induce (s : Set V))
    omega
  have hup := c2_le_mrF2_add_one G
  have hmrk : mrF2 G = k := by omega
  have hpos : 0 < mrF2 G := by omega
  have huniq := (c2_eq_mrF2_add_one_iff G hpos).1 (by omega)
  refine ⟨hmrk, huniq, ?_⟩
  obtain ⟨d0, hd0⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
  rw [← mrF2_eq] at hd0
  have := huniq d0 hd0
  subst this
  rw [add_diagonal_zero'] at hd0
  rw [hd0, hmrk]

/-- **54-g (2).** -/
theorem class_packing (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∀ Z : Finset V, 3 * k ≤ (univ \ Z).card + 3 * frk (ZMod 2) (G.adjMatrix (ZMod 2)).row Z := by
  classical
  obtain ⟨hmrk, huniq, hrk⟩ := class_setup G hk hV hc hmin
  set A := G.adjMatrix (ZMod 2) with hA
  have hrow : (A + diagonal 0).row = A.row := by rw [add_diagonal_zero']
  by_contra hneg
  push Not at hneg
  obtain ⟨Z, hZ⟩ := hneg
  set f : Finset V → ℕ := fun X => (univ \ X).card + 3 * frk (ZMod 2) A.row X
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset (Finset V)) f univ_nonempty
  have hX : ∀ Z ⊆ X, 3 * frk (ZMod 2) (A + diagonal 0).row X ≤
      (X \ Z).card + 3 * frk (ZMod 2) (A + diagonal 0).row Z := by
    intro Z hZ
    rw [hrow]
    have h := hXmin Z (mem_univ _)
    simp only [f] at h
    have e1 := card_sdiff_add_card_eq_card (subset_univ X)
    have e2 := card_sdiff_add_card_eq_card (subset_univ Z)
    have e3 := card_sdiff_add_card_eq_card hZ
    omega
  obtain ⟨T, hT, hlift⟩ := witness3_of_set A 0 (isSymm_adj_add_diag G 0) X hX
  rw [hrow] at hT
  have hfX : f X < 3 * k := by
    have := hXmin Z (mem_univ _)
    simp only [f] at this ⊢
    omega
  have hlift' : ∀ (d : V → ZMod 2) (P : Finset V), P ⊆ T → P.card ≤ 1 →
      ∃ d' : V → ZMod 2, (∀ j ∈ P, d' j = d j) ∧
        (A + diagonal d').rank ≤ (subPattern A T + diagonal (fun a : T => d a)).rank := hlift
  have hcT := c2_induce_ge_of_lift G hmrk (by omega) huniq T hlift'
  have hTu : T ≠ univ := by
    intro h
    rw [h, card_univ, hV] at hT
    simp only [f] at hfX
    omega
  have := hmin T hTu
  omega

/-- **The three bases.** -/
theorem class_bases (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∃ B1 B2 B3 : Finset V, Disjoint B1 B2 ∧ Disjoint B1 B3 ∧ Disjoint B2 B3 ∧
      B1.card = k ∧ B2.card = k ∧ B3.card = k ∧
      frk (ZMod 2) (G.adjMatrix (ZMod 2)).row B1 = k ∧
      frk (ZMod 2) (G.adjMatrix (ZMod 2)).row B2 = k ∧
      frk (ZMod 2) (G.adjMatrix (ZMod 2)).row B3 = k ∧
      (∀ i, (G.adjMatrix (ZMod 2)).row i ∈
        span (ZMod 2) ((G.adjMatrix (ZMod 2)).row '' (B1 : Set V))) ∧
      (∀ i, (G.adjMatrix (ZMod 2)).row i ∈
        span (ZMod 2) ((G.adjMatrix (ZMod 2)).row '' (B2 : Set V))) ∧
      (∀ i, (G.adjMatrix (ZMod 2)).row i ∈
        span (ZMod 2) ((G.adjMatrix (ZMod 2)).row '' (B3 : Set V))) ∧
      (∀ x, x ∈ B1 ∨ x ∈ B2 ∨ x ∈ B3) := by
  classical
  obtain ⟨-, -, hrk⟩ := class_setup G hk hV hc hmin
  have hpack := class_packing G hk hV hc hmin
  set A := G.adjMatrix (ZMod 2)
  have hfu : frk (ZMod 2) A.row univ = k := by rw [← rank_eq_frk_univ, hrk]
  have hX : ∀ Z ⊆ (univ : Finset V), 3 * frk (ZMod 2) A.row univ ≤
      (univ \ Z).card + 3 * frk (ZMod 2) A.row Z := by
    intro Z _; rw [hfu]; exact hpack Z
  obtain ⟨B1, B2, B3, -, -, -, d12, d13, d23, c1, c2', c3, s1, s2, s3⟩ :=
    three_spanning_bases A.row univ hX
  rw [hfu] at c1 c2' c3
  have hsp : ∀ B : Finset V, span (ZMod 2) (A.row '' (B : Set V)) =
      span (ZMod 2) (A.row '' ((univ : Finset V) : Set V)) →
      (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (B : Set V))) ∧ frk (ZMod 2) A.row B = k := by
    intro B hB
    refine ⟨fun i => by rw [hB]; exact subset_span ⟨i, by simp, rfl⟩, ?_⟩
    unfold frk; rw [hB]; exact hfu
  obtain ⟨h1, f1⟩ := hsp B1 s1
  obtain ⟨h2, f2⟩ := hsp B2 s2
  obtain ⟨h3, f3⟩ := hsp B3 s3
  have hcov : B1 ∪ B2 ∪ B3 = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨d13, d23⟩), card_union_of_disjoint d12,
      c1, c2', c3, hV]
    ring
  refine ⟨B1, B2, B3, d12, d13, d23, c1, c2', c3, f1, f2, f3, h1, h2, h3, fun x => ?_⟩
  have : x ∈ B1 ∪ B2 ∪ B3 := by rw [hcov]; exact mem_univ x
  simp only [mem_union] at this
  tauto

/-- A graph with `c₂ ≤ k` whose adjacency matrix has rank `≥ k ≥ 1` has a completion of rank
`≤ k` with a non-zero diagonal entry. -/
lemma exists_nonzero_diag {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {k : ℕ} (hk : 1 ≤ k) (hc : c2 H ≤ k)
    (hr : k ≤ (H.adjMatrix (ZMod 2)).rank) :
    ∃ e : W → ZMod 2, e ≠ 0 ∧ (H.adjMatrix (ZMod 2) + diagonal e).rank ≤ k := by
  classical
  have hm := (mrF2_le_c2 H).trans hc
  obtain ⟨e, he⟩ := exists_minCompRank (H.adjMatrix (ZMod 2))
  rw [← mrF2_eq] at he
  rcases Nat.lt_or_ge (mrF2 H) k with hlt | hge
  · refine ⟨e, ?_, by omega⟩
    rintro rfl
    rw [add_diagonal_zero'] at he
    omega
  · have hmk : mrF2 H = k := le_antisymm hm hge
    have hne : ¬ ∀ d : W → ZMod 2, (H.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 H → d = 0 :=
      fun h => by have := (c2_eq_mrF2_add_one_iff H (by omega)).2 h; omega
    push Not at hne
    obtain ⟨d, hd, hd0⟩ := hne
    exact ⟨d, hd0, by omega⟩

lemma frk_comp_val {ι W : Type*} [DecidableEq ι] [AddCommGroup W] [Module (ZMod 2) W]
    (u : ι → W) (s : Finset ι) (Z : Finset s) :
    frk (ZMod 2) (u ∘ Subtype.val) Z = frk (ZMod 2) u (Z.map (Function.Embedding.subtype _)) := by
  unfold frk
  rw [Finset.coe_map, Set.image_comp]
  rfl

/-- **54-g (3): a word of weight at most three through every vertex.** -/
theorem exists_word (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) (v : V) :
    ∃ y : V → ZMod 2, (G.adjMatrix (ZMod 2) *ᵥ y) v ≠ 0 ∧
      (univ.filter fun i => (G.adjMatrix (ZMod 2) *ᵥ y) i ≠ 0).card ≤ 3 := by
  classical
  obtain ⟨-, -, hrk⟩ := class_setup G hk hV hc hmin
  obtain ⟨B1, B2, B3, d12, d13, d23, c1, c2', c3, f1, f2, f3, h1, h2, h3', hcov⟩ :=
    class_bases G hk hV hc hmin
  set A := G.adjMatrix (ZMod 2) with hA
  have hAs : A.IsSymm := isSymm_adjMatrix G
  -- (I) information sets
  have info : ∀ B : Finset V, (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (B : Set V))) →
      ∀ y, A *ᵥ y ≠ 0 → ∃ p ∈ B, (A *ᵥ y) p ≠ 0 := by
    intro B hB y hy
    by_contra h; push Not at h
    exact hy (mulVec_eq_zero_of_span A B hB y h)
  -- the factorisation through `B₁`
  obtain ⟨C, hfac, hC, hΘ⟩ := factor_symm A hAs B1 h1 (by rw [c1, hrk])
  have hfrkC := frk_C_eq A B1 C hC (by rw [f1, c1])
  set Θ := A.submatrix (fun b : B1 => (b : V)) (fun b : B1 => (b : V))
  -- (a) the rank of `A` restricted to `V - v` is `k`
  set s : Finset V := univ.erase v with hs
  have hcolrow : ∀ j, A.col j = A.row j := by
    intro j; ext i
    have := congrFun (congrFun hAs i) j
    simp only [transpose_apply] at this
    simp [Matrix.col, Matrix.row, this]
  have hrank_s : k ≤ (subPattern A s).rank := by
    have key : ∀ Bb Bc : Finset V, v ∉ Bb → v ∉ Bc →
        (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (Bb : Set V))) →
        (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (Bc : Set V))) → k ≤ (subPattern A s).rank := by
      intro Bb Bc hb hc' hBb hBc
      have hC' : ∀ j, A.col j ∈ span (ZMod 2) (A.col '' (Bc : Set V)) := by
        intro j
        rw [hcolrow, Set.image_congr (fun l _ => hcolrow l)]
        exact hBc j
      have h := rank_le_submatrix_of_span A Bb Bc hBb hC'
      rw [hrk] at h
      refine h.trans ?_
      have hbs : ∀ x ∈ Bb, x ∈ s := fun x hx => mem_erase.2 ⟨fun h => hb (h ▸ hx), mem_univ _⟩
      have hcs : ∀ x ∈ Bc, x ∈ s := fun x hx => mem_erase.2 ⟨fun h => hc' (h ▸ hx), mem_univ _⟩
      have e : A.submatrix (fun r : Bb => (r : V)) (fun c : Bc => (c : V)) =
          (subPattern A s).submatrix (fun r : Bb => ⟨r, hbs r r.2⟩) (fun c : Bc => ⟨c, hcs c c.2⟩) :=
        rfl
      rw [e]; exact rank_submatrix_le _ _ _
    have n12 : ∀ x, x ∈ B1 → x ∉ B2 := fun x h h' => disjoint_left.1 d12 h h'
    have n13 : ∀ x, x ∈ B1 → x ∉ B3 := fun x h h' => disjoint_left.1 d13 h h'
    have n23 : ∀ x, x ∈ B2 → x ∉ B3 := fun x h h' => disjoint_left.1 d23 h h'
    rcases hcov v with hv | hv | hv
    · exact key B2 B3 (n12 v hv) (n13 v hv) h2 h3'
    · exact key B1 B3 (fun h => n12 v h hv) (n23 v hv) h1 h3'
    · exact key B1 B2 (fun h => n13 v h hv) (fun h => n23 v h hv) h1 h2
  -- (b) a completion of `A_s` of rank `≤ k` with a non-zero diagonal entry
  have hsu : s ≠ univ := by
    intro h; have : v ∈ s := by rw [h]; exact mem_univ v
    simp [hs] at this
  have hcs := hmin s hsu
  have hrs' : k ≤ ((G.induce (s : Set V)).adjMatrix (ZMod 2)).rank := by
    rw [adjMatrix_induce]; exact hrank_s
  obtain ⟨e, he0, her⟩ := exists_nonzero_diag (G.induce (s : Set V)) (by omega) hcs hrs'
  rw [adjMatrix_induce] at her
  -- (c) the rank formula
  set C' : Matrix s B1 (ZMod 2) := C.submatrix (fun x : s => (x : V)) id
  have hsub : subPattern A s = C' * Θ⁻¹⁻¹ * C'ᵀ := by
    rw [nonsing_inv_nonsing_inv Θ hΘ]
    ext i j
    have := congrFun (congrFun hfac i.1) j.1
    simp only [subPattern, submatrix_apply]
    rw [this]
    simp [C', Matrix.mul_apply]
  have hneg : subPattern A s + diagonal e = C' * Θ⁻¹⁻¹ * C'ᵀ - diagonal e := by
    rw [← hsub, sub_eq_add_neg]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp [ZMod.neg_eq_self_mod_two]
    · simp [diagonal_apply_ne _ hij]
  set Z : Finset s := univ.filter fun i => e i = 0 with hZ
  have hRF := rank_formula C' C' Θ⁻¹ (isUnit_nonsing_inv_det Θ hΘ) e Z (by simp [hZ])
  rw [← hneg] at hRF
  have hfrkZ : frk (ZMod 2) C'.row Z = frk (ZMod 2) A.row (Z.map (Function.Embedding.subtype _)) := by
    have e1 : C'.row = C.row ∘ Subtype.val := rfl
    rw [e1, frk_comp_val, hfrkC]
  rw [hfrkZ, Fintype.card_coe, Fintype.card_coe] at hRF
  set Zv := Z.map (Function.Embedding.subtype (fun x => x ∈ s)) with hZv
  set r := frk (ZMod 2) A.row Zv with hr
  have hcardZ : Zv.card = Z.card := card_map _
  have hscard : s.card = 3 * k - 1 := by
    rw [hs, card_erase_of_mem (mem_univ v), card_univ, hV]
  have hvZ : v ∉ Zv := by
    intro h
    obtain ⟨x, -, hx⟩ := mem_map.1 h
    have hxv : (x : V) = v := hx
    have := x.2
    rw [hxv] at this
    simp [hs] at this
  -- (d) counting
  have hZlt : Z.card + 1 ≤ s.card := by
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h; push Not at h; exact he0 (funext h)
    have hiZ : i ∉ Z := by simp [hZ, hi]
    have := card_lt_card (ssubset_iff_of_subset (subset_univ Z) |>.2 ⟨i, mem_univ _, hiZ⟩)
    rw [card_univ, Fintype.card_coe] at this
    omega
  have hrle : r ≤ k := by
    rw [hr, ← hrk, rank_eq_frk_univ]; exact frk_mono _ (subset_univ _)
  have hBa : ∀ B : Finset V, frk (ZMod 2) A.row B = B.card → B.card = k →
      k ≤ (B \ Zv).card + r := by
    intro B hB hBk
    have h1 := frk_eq_card_of_subset (F := ZMod 2) A.row (inter_subset_left : B ∩ Zv ⊆ B) hB
    have h2 := frk_mono (F := ZMod 2) A.row (inter_subset_right : B ∩ Zv ⊆ Zv)
    have h3 := card_sdiff_add_card_inter B Zv
    omega
  have hb1 := hBa B1 (by rw [f1, c1]) c1
  have hb2 := hBa B2 (by rw [f2, c2']) c2'
  have hb3 := hBa B3 (by rw [f3, c3]) c3
  have hsum : (B1 \ Zv).card + (B2 \ Zv).card + (B3 \ Zv).card ≤ (univ \ Zv).card := by
    have hd1 : Disjoint (B1 \ Zv) (B2 \ Zv) :=
      disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset d12)
    have hd2 : Disjoint ((B1 \ Zv) ∪ (B2 \ Zv)) (B3 \ Zv) :=
      disjoint_union_left.2 ⟨disjoint_of_subset_left sdiff_subset
        (disjoint_of_subset_right sdiff_subset d13), disjoint_of_subset_left sdiff_subset
        (disjoint_of_subset_right sdiff_subset d23)⟩
    rw [← card_union_of_disjoint hd1, ← card_union_of_disjoint hd2]
    apply card_le_card
    intro x hx
    simp only [mem_union, mem_sdiff] at hx
    simp only [mem_sdiff, mem_univ, true_and]
    tauto
  have hcomp : (univ \ Zv).card + Zv.card = 3 * k := by
    rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ, hV]
  have her' : (subPattern A s + diagonal e).rank ≤ k := her
  have hr1 : r + 1 ≤ k := by omega
  have h3 : (univ \ Zv).card ≤ 3 := by omega
  -- (e) a vector `y` with `A y` zero on `Zv` but not zero
  obtain ⟨y, hyZ, hy0⟩ : ∃ y : V → ZMod 2, (∀ i ∈ Zv, (A *ᵥ y) i = 0) ∧ A *ᵥ y ≠ 0 := by
    by_contra hno
    push Not at hno
    have hle := rank_le_of_ker_le (A.submatrix (fun i : Zv => (i : V)) id) A (by
      intro y hy
      apply hno y
      intro i hi
      have := congrFun hy ⟨i, hi⟩
      simpa [mulVec, dotProduct] using this)
    rw [rank_submatrix_rows_eq_frk, hrk] at hle
    omega
  -- (f) its support is `Zvᶜ`, which contains `v` and has at most three elements
  set w := A *ᵥ y
  have hsupp : univ.filter (fun i => w i ≠ 0) ⊆ univ \ Zv := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_sdiff, mem_univ, true_and]
    exact fun h => hx (hyZ x h)
  obtain ⟨p1, hp1, hw1⟩ := info B1 h1 y hy0
  obtain ⟨p2, hp2, hw2⟩ := info B2 h2 y hy0
  obtain ⟨p3, hp3, hw3⟩ := info B3 h3' y hy0
  have hne12 : p1 ≠ p2 := fun h => disjoint_left.1 d12 hp1 (h ▸ hp2)
  have hne13 : p1 ≠ p3 := fun h => disjoint_left.1 d13 hp1 (h ▸ hp3)
  have hne23 : p2 ≠ p3 := fun h => disjoint_left.1 d23 hp2 (h ▸ hp3)
  have hthree : ({p1, p2, p3} : Finset V) ⊆ univ.filter (fun i => w i ≠ 0) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({p1, p2, p3} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hne12, hne13]), card_pair hne23]
  have hcs3 := card_le_card hthree
  have heq : univ.filter (fun i => w i ≠ 0) = univ \ Zv :=
    eq_of_subset_of_card_le hsupp (by omega)
  refine ⟨y, ?_, ?_⟩
  swap
  · show (univ.filter fun i => w i ≠ 0).card ≤ 3
    rw [heq]; exact h3
  have hv : v ∈ univ \ Zv := by simp [hvZ]
  rw [← heq] at hv
  simpa using hv

end FreeDiagonal.EvenComplementation
