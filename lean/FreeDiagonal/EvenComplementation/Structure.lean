import FreeDiagonal.EvenComplementation.Words
import FreeDiagonal.EvenComplementation.Tripling

/-!
# Part 54-g in Lean, part 2: the words of weight three, and the tripling

Continuing `Words.lean` (54-g (4)-(6)). Over `F₂`, a non-zero entry is `1`.
* `card_four`: a vector with at most three non-zero entries that is non-zero somewhere in each
  of three disjoint sets has exactly one non-zero entry in each.
* `word_eq_of_common`: two words (`A y`) of weight `≤ 3` that share a non-zero position are
  equal (they agree on the basis `B_a` through that position, which is an information set).
* `class_structure`: there are `B₁` (`k` elements) and `β : V → B₁` with fibres of size three
  such that `A x y = A (β x) (β y)` and `A[B₁, B₁]` is non-singular. (`β x` is the `B₁`-position
  of the unique weight-three word through `x`; every column of `A` is a word, hence constant on
  the fibres.)
* `class_iso`: `G ≅ tripling G₀` with `G₀` on `Fin k`, `det A₀ ≠ 0`.
-/

open Matrix Module Submodule Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma zmod2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by revert a; decide

omit [Fintype V] in
lemma card_four [Fintype V] {w : V → ZMod 2} {Ba Bb Bc : Finset V} (dab : Disjoint Ba Bb)
    (dac : Disjoint Ba Bc) (dbc : Disjoint Bb Bc) (hb : ∃ r ∈ Bb, w r ≠ 0)
    (hc : ∃ r ∈ Bc, w r ≠ 0) (h3 : (univ.filter fun i => w i ≠ 0).card ≤ 3) {p q : V}
    (hp : p ∈ Ba) (hq : q ∈ Ba) (hwp : w p ≠ 0) (hwq : w q ≠ 0) : p = q := by
  by_contra hpq
  obtain ⟨r, hr, hwr⟩ := hb
  obtain ⟨t, ht, hwt⟩ := hc
  have hpr : p ≠ r := fun h => disjoint_left.1 dab hp (h ▸ hr)
  have hqr : q ≠ r := fun h => disjoint_left.1 dab hq (h ▸ hr)
  have hpt : p ≠ t := fun h => disjoint_left.1 dac hp (h ▸ ht)
  have hqt : q ≠ t := fun h => disjoint_left.1 dac hq (h ▸ ht)
  have hrt : r ≠ t := fun h => disjoint_left.1 dbc hr (h ▸ ht)
  have hsub : ({p, q, r, t} : Finset V) ⊆ univ.filter fun i => w i ≠ 0 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({p, q, r, t} : Finset V).card = 4 := by
    rw [card_insert_of_notMem (by simp [hpq, hpr, hpt]), card_insert_of_notMem (by simp [hqr, hqt]),
      card_pair hrt]
  have := card_le_card hsub
  omega

/-- Two words of weight `≤ 3` sharing a non-zero position `p ∈ Ba` are equal. -/
lemma word_eq_of_common (A : Matrix V V (ZMod 2)) {Ba Bb Bc : Finset V} (dab : Disjoint Ba Bb)
    (dac : Disjoint Ba Bc) (dbc : Disjoint Bb Bc)
    (ha : ∀ i, A.row i ∈ span (ZMod 2) (A.row '' (Ba : Set V)))
    (hb : ∀ i, A.row i ∈ span (ZMod 2) (A.row '' (Bb : Set V)))
    (hc : ∀ i, A.row i ∈ span (ZMod 2) (A.row '' (Bc : Set V)))
    (z1 z2 : V → ZMod 2) (h1 : (univ.filter fun i => (A *ᵥ z1) i ≠ 0).card ≤ 3)
    (h2 : (univ.filter fun i => (A *ᵥ z2) i ≠ 0).card ≤ 3) {p : V} (hp : p ∈ Ba)
    (hw1 : (A *ᵥ z1) p ≠ 0) (hw2 : (A *ᵥ z2) p ≠ 0) : A *ᵥ z1 = A *ᵥ z2 := by
  have info : ∀ B : Finset V, (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (B : Set V))) →
      ∀ z, (∃ q, (A *ᵥ z) q ≠ 0) → ∃ r ∈ B, (A *ᵥ z) r ≠ 0 := by
    intro B hB z ⟨q, hq⟩
    by_contra h; push Not at h
    exact hq (by rw [mulVec_eq_zero_of_span A B hB z h]; rfl)
  have key : ∀ b ∈ Ba, (A *ᵥ (z1 - z2)) b = 0 := by
    intro b hb'
    rw [mulVec_sub, Pi.sub_apply]
    by_cases hbp : b = p
    · subst hbp
      rw [(zmod2_ne_zero_iff _).1 hw1, (zmod2_ne_zero_iff _).1 hw2, sub_self]
    · have e1 : (A *ᵥ z1) b = 0 := by
        by_contra hne
        exact hbp (card_four dab dac dbc (info Bb hb z1 ⟨p, hw1⟩) (info Bc hc z1 ⟨p, hw1⟩) h1
          hb' hp hne hw1)
      have e2 : (A *ᵥ z2) b = 0 := by
        by_contra hne
        exact hbp (card_four dab dac dbc (info Bb hb z2 ⟨p, hw2⟩) (info Bc hc z2 ⟨p, hw2⟩) h2
          hb' hp hne hw2)
      rw [e1, e2, sub_self]
  have := mulVec_eq_zero_of_span A Ba ha _ key
  rw [mulVec_sub, sub_eq_zero] at this
  exact this

/-- **54-g (4)-(6), structure.** -/
theorem class_structure (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∃ (B1 : Finset V) (β : V → V), B1.card = k ∧ (∀ x, β x ∈ B1) ∧
      (∀ b ∈ B1, (univ.filter fun x => β x = b).card = 3) ∧
      (∀ x y, G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) (β x) (β y)) ∧
      IsUnit ((G.adjMatrix (ZMod 2)).submatrix (fun b : B1 => (b : V))
        (fun b : B1 => (b : V))).det := by
  classical
  obtain ⟨-, -, hrk⟩ := class_setup G hk hV hc hmin
  obtain ⟨B1, B2, B3, d12, d13, d23, c1, c2', c3, f1, f2, f3, h1, h2, h3, hcov⟩ :=
    class_bases G hk hV hc hmin
  set A := G.adjMatrix (ZMod 2) with hA
  have hAs : A.IsSymm := isSymm_adjMatrix G
  have hAs' : ∀ i j, A i j = A j i := by
    intro i j; have := congrFun (congrFun hAs j) i; simpa [transpose_apply] using this
  obtain ⟨C, -, -, hΘ⟩ := factor_symm A hAs B1 h1 (by rw [c1, hrk])
  have hword := exists_word G hk hV hc hmin
  choose y hy1 hy3 using hword
  set W : V → V → ZMod 2 := fun x => A *ᵥ y x with hW
  have info : ∀ B : Finset V, (∀ i, A.row i ∈ span (ZMod 2) (A.row '' (B : Set V))) →
      ∀ z, (∃ q, (A *ᵥ z) q ≠ 0) → ∃ r ∈ B, (A *ᵥ z) r ≠ 0 := by
    intro B hB z ⟨q, hq⟩
    by_contra h; push Not at h
    exact hq (by rw [mulVec_eq_zero_of_span A B hB z h]; rfl)
  -- the word through `p` is unique
  have weq : ∀ z1 z2 : V → ZMod 2, (univ.filter fun i => (A *ᵥ z1) i ≠ 0).card ≤ 3 →
      (univ.filter fun i => (A *ᵥ z2) i ≠ 0).card ≤ 3 → ∀ p, (A *ᵥ z1) p ≠ 0 →
      (A *ᵥ z2) p ≠ 0 → A *ᵥ z1 = A *ᵥ z2 := by
    intro z1 z2 hz1 hz2 p hw1 hw2
    rcases hcov p with hp | hp | hp
    · exact word_eq_of_common A d12 d13 d23 h1 h2 h3 z1 z2 hz1 hz2 hp hw1 hw2
    · exact word_eq_of_common A d12.symm d23 d13 h2 h1 h3 z1 z2 hz1 hz2 hp hw1 hw2
    · exact word_eq_of_common A d13.symm d23.symm d12 h3 h1 h2 z1 z2 hz1 hz2 hp hw1 hw2
  -- uniqueness of the `B₁`-position of a word of weight `≤ 3`
  have b1uniq : ∀ z : V → ZMod 2, (univ.filter fun i => (A *ᵥ z) i ≠ 0).card ≤ 3 →
      ∀ p q, p ∈ B1 → q ∈ B1 → (A *ᵥ z) p ≠ 0 → (A *ᵥ z) q ≠ 0 → p = q := by
    intro z hz p q hp hq hwp hwq
    exact card_four d12 d13 d23 (info B2 h2 z ⟨p, hwp⟩) (info B3 h3 z ⟨p, hwp⟩) hz hp hq hwp hwq
  -- `β x`: the `B₁`-position of the word through `x`
  have hβex : ∀ x, ∃ b ∈ B1, W x b ≠ 0 := fun x => info B1 h1 (y x) ⟨x, hy1 x⟩
  choose β hβB hβW using hβex
  have hWβ : ∀ x, W (β x) = W x := fun x =>
    weq (y (β x)) (y x) (hy3 _) (hy3 _) (β x) (hy1 _) (hβW x)
  have hββ : ∀ b ∈ B1, β b = b := fun b hb =>
    b1uniq (y b) (hy3 b) _ _ (hβB b) hb (hβW b) (hy1 b)
  have hiff : ∀ b ∈ B1, ∀ x, W b x ≠ 0 ↔ β x = b := by
    intro b hb x
    constructor
    · intro hbx
      have e : W b = W x := weq (y b) (y x) (hy3 _) (hy3 _) x hbx (hy1 x)
      have hxb : W x b ≠ 0 := by rw [← e]; exact hy1 b
      exact (b1uniq (y x) (hy3 x) _ _ hb (hβB x) hxb (hβW x)).symm
    · intro hxb
      rw [← hxb, hWβ]; exact hy1 x
  have hWval : ∀ b ∈ B1, ∀ x, W b x = if β x = b then 1 else 0 := by
    intro b hb x
    by_cases h : β x = b
    · rw [if_pos h]; exact (zmod2_ne_zero_iff _).1 ((hiff b hb x).2 h)
    · rw [if_neg h]; by_contra hne; exact h ((hiff b hb x).1 hne)
  -- every word is constant on the fibres of `β`
  have hconst : ∀ z x, (A *ᵥ z) x = (A *ᵥ z) (β x) := by
    intro z x
    set c := A *ᵥ z
    set z' : V → ZMod 2 := ∑ b ∈ B1, c b • y b
    have hz' : A *ᵥ z' = ∑ b ∈ B1, c b • W b := by
      simp only [z', W, mulVec_sum, mulVec_smul]
    have hev : ∀ u, (A *ᵥ z') u = c (β u) := by
      intro u
      rw [hz', Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun b hb => by rw [hWval b hb u])]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq B1 (β u) (fun b => c b)]
      rw [if_pos (hβB u)]
    have hagree : ∀ b ∈ B1, (A *ᵥ (z' - z)) b = 0 := by
      intro b hb
      rw [mulVec_sub, Pi.sub_apply, hev, hββ b hb, sub_self]
    have := mulVec_eq_zero_of_span A B1 h1 _ hagree
    rw [mulVec_sub, sub_eq_zero] at this
    have this' : A *ᵥ z' = c := this
    rw [← this', hev, hev, hββ _ (hβB x)]
  have hrowβ : ∀ x j, A x j = A (β x) j := by
    intro x j
    have := hconst (Pi.single j 1) x
    simpa [mulVec_single_one] using this
  have hAβ : ∀ x x', A x x' = A (β x) (β x') := by
    intro x x'
    rw [hrowβ x x', hAs' (β x) x', hrowβ x' (β x), hAs']
  refine ⟨B1, β, c1, hβB, ?_, hAβ, hΘ⟩
  -- fibres have three elements
  intro b hb
  have hfib : (univ.filter fun x => β x = b) = univ.filter fun x => W b x ≠ 0 := by
    ext x; simp [hiff b hb x]
  rw [hfib]
  apply le_antisymm (hy3 b)
  obtain ⟨p1, hp1, hw1⟩ := info B1 h1 (y b) ⟨b, hy1 b⟩
  obtain ⟨p2, hp2, hw2⟩ := info B2 h2 (y b) ⟨b, hy1 b⟩
  obtain ⟨p3, hp3, hw3⟩ := info B3 h3 (y b) ⟨b, hy1 b⟩
  have hne12 : p1 ≠ p2 := fun h => disjoint_left.1 d12 hp1 (h ▸ hp2)
  have hne13 : p1 ≠ p3 := fun h => disjoint_left.1 d13 hp1 (h ▸ hp3)
  have hne23 : p2 ≠ p3 := fun h => disjoint_left.1 d23 hp2 (h ▸ hp3)
  have hsub : ({p1, p2, p3} : Finset V) ⊆ univ.filter fun x => W b x ≠ 0 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({p1, p2, p3} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hne12, hne13]), card_pair hne23]
  rw [← hc3]; exact card_le_card hsub

end FreeDiagonal.EvenComplementation
