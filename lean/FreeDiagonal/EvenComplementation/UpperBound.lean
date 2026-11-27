import FreeDiagonal.EvenComplementation.Witness3
import FreeDiagonal.Graphs.Complementation

/-!
# Part 54-e in Lean: a graph with `c₂ > k` has an induced subgraph on at most `3k` vertices with
`c₂ > k` (`k ≥ 2`)

Proof (pit-stop note QX-01, Section 1.3): if `mr(F₂, G) > k`, Corollary 4 (`cor4_threshold`)
gives an induced subgraph on at most `2k + 2 ≤ 3k` vertices with `mr > k`, hence `c₂ > k`.
Otherwise `mr = k`, `c₂ = k + 1`, the adjacency matrix `A` has rank `k` and is the only
completion of rank `k` (`c2_eq_mrF2_add_one_iff`); the three-basis witness `T` of `A`
(`witness3`, `|T| ≤ 3k`) keeps `mr = k` (lift with no prescribed index) and keeps "every
rank-`k` completion has zero diagonal" (lift prescribing one non-zero diagonal entry).

Parity is not used: the statement holds for every `k ≥ 2` (for odd `k` it is weaker than
`cor5_odd`).
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The adjacency matrix of an induced subgraph is the sub-pattern of the adjacency matrix. -/
lemma adjMatrix_induce (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    (G.induce (s : Set V)).adjMatrix (ZMod 2) = subPattern (G.adjMatrix (ZMod 2)) s := by
  ext a b
  simp [adjMatrix_apply, subPattern, comap_adj]

/-- **From the lifting property to `c₂ > k` on `T`.** If `mr(F₂, G) = k ≥ 1`, every completion of
rank `mr` has zero diagonal, and every completion of `A_T` lifts to a completion of `A` of no
larger rank keeping its diagonal value at any one prescribed index of `T`, then
`c₂(G[T]) ≥ k + 1`. -/
theorem c2_induce_ge_of_lift (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hmrk : mrF2 G = k) (hk : 0 < k)
    (huniq : ∀ d : V → ZMod 2, (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G → d = 0)
    (T : Finset V)
    (hlift : ∀ (d : V → ZMod 2) (P : Finset V), P ⊆ T → P.card ≤ 1 →
      ∃ d' : V → ZMod 2, (∀ j ∈ P, d' j = d j) ∧
        (G.adjMatrix (ZMod 2) + diagonal d').rank ≤
          (subPattern (G.adjMatrix (ZMod 2)) T + diagonal (fun a : T => d a)).rank) :
    k + 1 ≤ c2 (G.induce (T : Set V)) := by
  classical
  set A := G.adjMatrix (ZMod 2) with hA
  -- every completion of `A_T` has rank at least `k`
  have hlow : ∀ e : T → ZMod 2, k ≤ (subPattern A T + diagonal e).rank := by
    intro e
    set d : V → ZMod 2 := fun j => if h : j ∈ T then e ⟨j, h⟩ else 0
    have hde : (fun a : T => d a) = e := by funext a; simp [d, a.2]
    obtain ⟨d', -, hr⟩ := hlift d ∅ (empty_subset _) (by simp)
    rw [hde] at hr
    have := minCompRank_le A d'
    rw [← mrF2_eq, hmrk] at this
    omega
  have hmrT : mrF2 (G.induce (T : Set V)) = k := by
    apply le_antisymm
    · rw [mrF2_induce, ← hmrk, mrF2_eq]; exact minCompRank_subPattern_le A T
    · rw [mrF2_induce]; exact le_minCompRank _ hlow
  have hposT : 0 < mrF2 (G.induce (T : Set V)) := by omega
  have hiff := (c2_eq_mrF2_add_one_iff (G.induce (T : Set V)) hposT).2 (by
    intro e he
    rw [adjMatrix_induce, hmrT] at he
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h; push Not at h; exact hne (funext h)
    set d : V → ZMod 2 := fun j => if h : j ∈ T then e ⟨j, h⟩ else 0
    have hde : (fun a : T => d a) = e := by funext a; simp [d, a.2]
    obtain ⟨d', hd'P, hr⟩ := hlift d {i.1} (by simp) (by simp)
    rw [hde, he] at hr
    have hlo := minCompRank_le A d'
    rw [← mrF2_eq, hmrk] at hlo
    have hd'0 := huniq d' (by omega)
    have := hd'P i.1 (mem_singleton_self _)
    rw [hd'0] at this
    simp only [Pi.zero_apply, d] at this
    rw [dif_pos (show (i : V) ∈ T from i.2)] at this
    exact hi this.symm)
  omega

/-- **Witness form of 54-e.** For `k ≥ 2`, a graph with `c₂ > k` has an induced subgraph on at
most `3k` vertices with `c₂ > k`. -/
theorem exists_induce_card_le_three_mul (G : SimpleGraph V) {k : ℕ} (hk : 2 ≤ k)
    (hc : k + 1 ≤ c2 G) :
    ∃ s : Finset V, s.card ≤ 3 * k ∧ k + 1 ≤ c2 (G.induce (s : Set V)) := by
  classical
  by_cases hmr : k + 1 ≤ mrF2 G
  · have h : ¬ ∀ s : Finset V, s.card ≤ 2 * k + 2 → mrF2 (G.induce (s : Set V)) ≤ k := by
      rw [← cor4_threshold]; omega
    push Not at h
    obtain ⟨s, hs, hmrs⟩ := h
    exact ⟨s, by omega, hmrs.trans_le (mrF2_le_c2 _)⟩
  push Not at hmr
  have hup := c2_le_mrF2_add_one G
  have hmrk : mrF2 G = k := by omega
  have hpos : 0 < mrF2 G := by omega
  have hc2 : c2 G = mrF2 G + 1 := by omega
  have huniq := (c2_eq_mrF2_add_one_iff G hpos).1 hc2
  set A := G.adjMatrix (ZMod 2) with hA
  obtain ⟨d0, hd0⟩ := exists_minCompRank A
  rw [← mrF2_eq] at hd0
  have hd00 := huniq d0 hd0
  subst hd00
  have hsym : (A + diagonal 0).IsSymm := isSymm_adj_add_diag G 0
  obtain ⟨T, hT, hlift⟩ := witness3 A 0 hsym
  rw [hd0, hmrk] at hT
  exact ⟨T, hT, c2_induce_ge_of_lift G hmrk (by omega) huniq T hlift⟩

end FreeDiagonal.EvenComplementation
