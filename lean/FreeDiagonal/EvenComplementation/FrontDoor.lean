import FreeDiagonal.EvenComplementation.UpperBound
import FreeDiagonal.EvenComplementation.Sharpness
import FreeDiagonal.EvenComplementation.Classification

/-!
# Part 54 (even-`k` subgraph complementation), front door

Plain statements, in the vocabulary of `Graphs/Complementation.lean`: `c2` (subgraph
complementation number, defined by clique sums), `mrF2`, induced subgraphs
`H.induce (s : Set V)` for `s : Finset V`, and "minimal forbidden induced subgraph for
`c₂ ≤ k`" written exactly as in `cor5` / `cor5_odd`: `k + 1 ≤ c2 H` and
`∀ s ≠ univ, c2 (H.induce s) ≤ k`.

Stage 1 (54-e): `cor5_even`, `part54_e_witness`, `part54_e_threshold`.
Stage 2 (54-f): `part54_f`, `part54_f_c2`, `part54_f_sharp`; `even_k_remark` as the special case
of a perfect matching: `mK33_iso_tripling_pm`, `c2_mK33_via_tripling`.
Stage 3 (54-g): `part54_g`, `part54_g_iff`.
Stage 4 (54-h, even part): `part54_h_even`.

`tripling G₀` (Tripling.lean) is `G₀.comap Prod.fst` on `W × Fin 3`: `(w, c) ~ (w', c')` iff
`w ~ w'` in `G₀` (`tripling_adj`, a `simp` lemma, proved by `Iff.rfl`).
-/

open Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Part 54-e, witness form.** Let `k ≥ 2` be even and `c₂(G) > k`. Then `G` has an induced
subgraph on at most `3k` vertices with `c₂ > k`. -/
theorem part54_e_witness (G : SimpleGraph V) {k : ℕ} (_hk : Even k) (hk2 : 2 ≤ k)
    (hc : k + 1 ≤ c2 G) :
    ∃ s : Finset V, s.card ≤ 3 * k ∧ k + 1 ≤ c2 (G.induce (s : Set V)) :=
  exists_induce_card_le_three_mul G hk2 hc

/-- **Part 54-e, minimal form (Corollary 5 for even `k`).** For even `k ≥ 2`, every minimal
forbidden induced subgraph for `c₂ ≤ k` has at most `3k` vertices. -/
theorem cor5_even (H : SimpleGraph V) {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 3 * k := by
  obtain ⟨s, hs, hcs⟩ := part54_e_witness H hk hk2 hc
  by_cases hsu : s = univ
  · rw [hsu, card_univ] at hs; exact hs
  · have := hmin s hsu; omega

/-- **Part 54-e, threshold form.** For even `k ≥ 2`: `c₂(G) ≤ k` iff every induced subgraph on at
most `3k` vertices has `c₂ ≤ k`. -/
theorem part54_e_threshold (G : SimpleGraph V) {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    c2 G ≤ k ↔ ∀ s : Finset V, s.card ≤ 3 * k → c2 (G.induce (s : Set V)) ≤ k := by
  constructor
  · intro h s _; exact (c2_induce_le G s).trans h
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨s, hs, hcs⟩ := part54_e_witness G hk hk2 hc
    have := h s hs; omega

/-- **Parity-free version of 54-e** (the proof never uses parity; for odd `k` the bound `2k + 2`
of `cor5_odd` is better). -/
theorem cor5_three_mul (H : SimpleGraph V) {k : ℕ} (hk2 : 2 ≤ k) (hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 3 * k := by
  obtain ⟨s, hs, hcs⟩ := exists_induce_card_le_three_mul H hk2 hc
  by_cases hsu : s = univ
  · rw [hsu, card_univ] at hs; exact hs
  · have := hmin s hsu; omega

section Stage2

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Part 54-f.** Let `k ≥ 2` be even and `G₀` a graph on `k` vertices whose adjacency matrix is
non-singular over `F₂`. Then the tripling of `G₀` (on `3k` vertices) is a minimal forbidden
induced subgraph for `c₂ ≤ k`. -/
theorem part54_f (G0 : SimpleGraph W) [DecidableRel G0.Adj] {k : ℕ} (_hk : Even k) (hk2 : 2 ≤ k)
    (hW : Fintype.card W = k) (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) :
    Fintype.card (W × Fin 3) = 3 * k ∧ k + 1 ≤ c2 (tripling G0) ∧
      ∀ s : Finset (W × Fin 3), s ≠ univ →
        c2 ((tripling G0).induce (s : Set (W × Fin 3))) ≤ k := by
  subst hW
  exact ⟨card_tripling, (c2_tripling hdet (by omega)).ge, c2_proper_induce_tripling hdet⟩

/-- **Part 54-f, exact values** (only `k ≥ 1` is needed; `k` is then even,
`even_card_of_det_ne_zero`): `c₂ = k + 1` and `mr(F₂) = k` for the tripling. -/
theorem part54_f_c2 (G0 : SimpleGraph W) [DecidableRel G0.Adj] (hk : 1 ≤ Fintype.card W)
    (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) :
    c2 (tripling G0) = Fintype.card W + 1 ∧ mrF2 (tripling G0) = Fintype.card W ∧
      Even (Fintype.card W) :=
  ⟨c2_tripling hdet hk, mrF2_tripling hdet, even_card_of_det_ne_zero G0 hdet⟩

end Stage2

/-- **Part 54-f, "in particular".** For every even `k ≥ 2` the tripling of the perfect matching on
`k` vertices is a minimal forbidden induced subgraph for `c₂ ≤ k` on exactly `3k` vertices. -/
theorem part54_f_sharp {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    Fintype.card ((Fin (k / 2) × Bool) × Fin 3) = 3 * k ∧ k + 1 ≤ c2 (tripling (pm (k / 2))) ∧
      ∀ s : Finset ((Fin (k / 2) × Bool) × Fin 3), s ≠ univ →
        c2 ((tripling (pm (k / 2))).induce (s : Set ((Fin (k / 2) × Bool) × Fin 3))) ≤ k := by
  obtain ⟨m, rfl⟩ := hk
  have hm : (m + m) / 2 = m := by omega
  rw [hm]
  obtain ⟨h1, h2, h3⟩ := tripling_pm m (by omega)
  refine ⟨by rw [h1]; ring, by rw [h2]; omega, fun s hs => (h3 s hs).trans (by omega)⟩

/-- **Part 54-h, even case.** For even `k ≥ 2`, the largest number of vertices of a minimal
forbidden induced subgraph for `c₂ ≤ k` is exactly `3k`. -/
theorem part54_h_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    IsGreatest {n : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : SimpleGraph V),
      Fintype.card V = n ∧ k + 1 ≤ c2 H ∧
        ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k} (3 * k) := by
  constructor
  · obtain ⟨h1, h2, h3⟩ := part54_f_sharp hk hk2
    exact ⟨_, inferInstance, inferInstance, _, h1, h2, h3⟩
  · rintro n ⟨V, _, _, H, rfl, hc, hmin⟩
    exact cor5_even H hk hk2 hc hmin

/-- **Part 54-g.** Let `k ≥ 4` be even. Every minimal forbidden induced subgraph for `c₂ ≤ k` on
exactly `3k` vertices is isomorphic to the tripling of a graph on `k` vertices whose adjacency
matrix is non-singular over `F₂`. -/
theorem part54_g (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (_hk : Even k) (hk4 : 4 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∃ (G0 : SimpleGraph (Fin k)) (_ : DecidableRel G0.Adj),
      (G0.adjMatrix (ZMod 2)).det ≠ 0 ∧ Nonempty (G ≃g tripling G0) :=
  class_iso G (by omega) hV hc hmin

/-- **Part 54-g, both directions.** Let `k ≥ 4` be even and `|V| = 3k`. A graph on `V` is a
minimal forbidden induced subgraph for `c₂ ≤ k` if and only if it is isomorphic to the tripling
of a graph on `k` vertices with non-singular adjacency matrix over `F₂`. -/
theorem part54_g_iff (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : Even k)
    (hk4 : 4 ≤ k) (hV : Fintype.card V = 3 * k) :
    (k + 1 ≤ c2 G ∧ ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) ↔
      ∃ (G0 : SimpleGraph (Fin k)) (_ : DecidableRel G0.Adj),
        (G0.adjMatrix (ZMod 2)).det ≠ 0 ∧ Nonempty (G ≃g tripling G0) := by
  constructor
  · rintro ⟨hc, hmin⟩
    exact part54_g G hk hk4 hV hc hmin
  · rintro ⟨G0, _, hdet, ⟨φ⟩⟩
    obtain ⟨-, h2, h3⟩ := part54_f G0 hk (by omega) (Fintype.card_fin k) hdet
    exact minForb_of_iso φ h2 h3

end FreeDiagonal.EvenComplementation

/-! ### Axioms -/
#print axioms FreeDiagonal.EvenComplementation.part54_e_witness
#print axioms FreeDiagonal.EvenComplementation.cor5_even
#print axioms FreeDiagonal.EvenComplementation.part54_e_threshold
#print axioms FreeDiagonal.EvenComplementation.cor5_three_mul
#print axioms FreeDiagonal.EvenComplementation.part54_f
#print axioms FreeDiagonal.EvenComplementation.part54_f_c2
#print axioms FreeDiagonal.EvenComplementation.part54_f_sharp
#print axioms FreeDiagonal.EvenComplementation.mK33_iso_tripling_pm
#print axioms FreeDiagonal.EvenComplementation.c2_mK33_via_tripling
#print axioms FreeDiagonal.EvenComplementation.part54_g
#print axioms FreeDiagonal.EvenComplementation.part54_g_iff
#print axioms FreeDiagonal.EvenComplementation.part54_h_even
