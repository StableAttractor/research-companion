import FreeDiagonal.Witness.Unconditional

/-!
# Stage C: Corollary 4, graphs over `F₂`

`mrF2 G` is the least rank of a symmetric matrix over `ZMod 2` whose off-diagonal non-zero
entries are exactly the edges of `G` (the diagonal is free). It equals `minCompRank` of the
adjacency matrix (`mrF2_eq`), and induced subgraphs correspond to sub-patterns
(`mrF2_induce`). Corollary 4 then follows from Theorems 2 and 3.
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M` is a symmetric matrix over `F₂` with off-diagonal support exactly the edges of `G`. -/
def F2Fits (G : SimpleGraph V) (M : Matrix V V (ZMod 2)) : Prop :=
  M.IsSymm ∧ ∀ i j, i ≠ j → (M i j ≠ 0 ↔ G.Adj i j)

/-- `mr(F₂, G)`: minimum rank over `F₂` of the graph `G`. -/
noncomputable def mrF2 (G : SimpleGraph V) : ℕ :=
  ⨅ M : {M : Matrix V V (ZMod 2) // F2Fits G M}, (M : Matrix V V (ZMod 2)).rank

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- `mr(F₂, G)` is `c` of the adjacency pattern. Over `F₂` every matrix with the right
off-diagonal support agrees with the adjacency matrix off the diagonal, and every completion of
the (symmetric) adjacency pattern is symmetric. -/
theorem mrF2_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    mrF2 G = minCompRank (G.adjMatrix (ZMod 2)) := by
  have fits : ∀ d, F2Fits G (G.adjMatrix (ZMod 2) + diagonal d) := by
    intro d
    refine ⟨(isSymm_adjMatrix G).add (isSymm_diagonal d), ?_⟩
    intro i j hij
    by_cases h : G.Adj i j <;> simp [adjMatrix_apply, diagonal_apply_ne _ hij, h]
  have : Nonempty {M : Matrix V V (ZMod 2) // F2Fits G M} := ⟨⟨_, fits 0⟩⟩
  apply le_antisymm
  · obtain ⟨d, hd⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
    rw [← hd]
    exact ciInf_le (OrderBot.bddBelow _) (⟨_, fits d⟩ : {M // F2Fits G M})
  · apply le_ciInf
    rintro ⟨M, -, hsupp⟩
    have e : M = G.adjMatrix (ZMod 2) + diagonal (fun i => M i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [adjMatrix_apply]
      · have h := hsupp i j hij
        rcases zmod2_cases (M i j) with h0 | h1
        · have : ¬ G.Adj i j := fun hA => (h.2 hA) h0
          simp [adjMatrix_apply, diagonal_apply_ne _ hij, this, h0]
        · have : G.Adj i j := h.1 (by rw [h1]; decide)
          simp [adjMatrix_apply, diagonal_apply_ne _ hij, this, h1]
    show minCompRank (G.adjMatrix (ZMod 2)) ≤ M.rank
    rw [e]
    exact minCompRank_le _ _

/-- Induced subgraphs correspond to sub-patterns. -/
theorem mrF2_induce (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    mrF2 (G.induce (s : Set V)) = minCompRank (subPattern (G.adjMatrix (ZMod 2)) s) := by
  classical
  rw [mrF2_eq]
  apply le_antisymm
  · exact minCompRank_le_of_embedding (subPattern (G.adjMatrix (ZMod 2)) s) _
      (fun a => ⟨a.1, a.2⟩) (fun a b h => Subtype.ext (congrArg Subtype.val h))
      (fun a b _ => by simp [subPattern, adjMatrix_apply])
  · exact minCompRank_le_of_embedding _ (subPattern (G.adjMatrix (ZMod 2)) s)
      (fun a => ⟨a.1, a.2⟩) (fun a b h => Subtype.ext (congrArg Subtype.val h))
      (fun a b _ => by simp [subPattern, adjMatrix_apply])

/-- **Corollary 4 (i).** A minimal forbidden induced subgraph for `mr(F₂, ·) ≤ k` has at most
`2k + 2` vertices. -/
theorem cor4_minimal (G : SimpleGraph V) (k : ℕ) (hk : k + 1 ≤ mrF2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → mrF2 (G.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 2 * k + 2 := by
  classical
  rw [mrF2_eq] at hk
  refine thm3_minimal k (G.adjMatrix (ZMod 2)) hk (fun T hT => ?_)
  rw [← mrF2_induce]
  exact hmin T hT

/-- **Corollary 4, threshold form.** `mr(F₂, G) ≤ k` iff every induced subgraph on at most
`2k + 2` vertices has `mr(F₂, ·) ≤ k`. -/
theorem cor4_threshold (G : SimpleGraph V) (k : ℕ) :
    mrF2 G ≤ k ↔ ∀ s : Finset V, s.card ≤ 2 * k + 2 → mrF2 (G.induce (s : Set V)) ≤ k := by
  classical
  rw [mrF2_eq, thm3_threshold]
  simp only [mrF2_induce]

/-- **Corollary 4 (iii).** Every graph has an induced subgraph on at most `2 mr(F₂, G)` vertices
with the same minimum rank over `F₂`. -/
theorem cor4_witness (G : SimpleGraph V) :
    ∃ s : Finset V, s.card ≤ 2 * mrF2 G ∧ mrF2 (G.induce (s : Set V)) = mrF2 G := by
  classical
  obtain ⟨T, h1, h2⟩ := thm2_two_mul (G.adjMatrix (ZMod 2))
  refine ⟨T, ?_, ?_⟩
  · rw [mrF2_eq]; exact h1
  · rw [mrF2_induce, mrF2_eq]; exact h2

/-- `(k+1) K₂`: `k + 1` disjoint edges `(a, false) — (a, true)`. -/
def matchingGraph (k : ℕ) : SimpleGraph (Fin (k + 1) × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (k : ℕ) : DecidableRel (matchingGraph k).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 = q.1 ∧ p.2 ≠ q.2))

lemma adjMatrix_matchingGraph (k : ℕ) :
    (matchingGraph k).adjMatrix (ZMod 2) = matching (ZMod 2) k := by
  ext p q; rw [adjMatrix_apply]; rfl

/-- **Corollary 4 (ii).** `(k+1) K₂` attains the bound: it has `2k + 2` vertices,
`mr(F₂) ≥ k + 1`, and every proper induced subgraph has `mr(F₂) ≤ k`. -/
theorem cor4_sharp (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      k + 1 ≤ mrF2 (matchingGraph k) ∧
      ∀ s : Finset (Fin (k + 1) × Bool), s ≠ univ →
        mrF2 ((matchingGraph k).induce (s : Set (Fin (k + 1) × Bool))) ≤ k := by
  refine ⟨card_matching_index k, ?_, fun s hs => ?_⟩
  · rw [mrF2_eq, adjMatrix_matchingGraph]; exact matching_lower (ZMod 2) k
  · rw [mrF2_induce, adjMatrix_matchingGraph]; exact matching_proper (ZMod 2) k s hs

end FreeDiagonal
