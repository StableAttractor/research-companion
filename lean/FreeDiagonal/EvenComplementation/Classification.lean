import FreeDiagonal.EvenComplementation.Structure
import FreeDiagonal.EvenComplementation.Sharpness

/-!
# Part 54-g in Lean, part 3: the isomorphism with a tripling

`class_iso`: a minimal forbidden induced subgraph for `c₂ ≤ k` on exactly `3k` vertices
(`k ≥ 3`) is isomorphic to the tripling of a graph `G₀` on `Fin k` whose adjacency matrix is
non-singular over `F₂`.
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

instance decComap {W : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r : W → V) :
    DecidableRel (G.comap r).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj (r i) (r j)))

theorem class_iso (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hV : Fintype.card V = 3 * k) (hc : k + 1 ≤ c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∃ (G0 : SimpleGraph (Fin k)) (_ : DecidableRel G0.Adj),
      (G0.adjMatrix (ZMod 2)).det ≠ 0 ∧ Nonempty (G ≃g tripling G0) := by
  classical
  obtain ⟨B1, β, c1, hβB, hfib, hAβ, hΘ⟩ := class_structure G hk hV hc hmin
  obtain ⟨eqv⟩ : Nonempty (B1 ≃ Fin k) :=
    ⟨Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, c1])⟩
  set r : Fin k → V := fun i => (eqv.symm i : V) with hr
  let β' : V → Fin k := fun x => eqv ⟨β x, hβB x⟩
  have hrβ : ∀ x, r (β' x) = β x := by intro x; simp [r, β']
  have hfib' : ∀ i, Fintype.card {x // β' x = i} = 3 := by
    intro i
    rw [Fintype.card_subtype]
    have : (univ.filter fun x => β' x = i) = univ.filter fun x => β x = r i := by
      ext x
      simp only [mem_filter, mem_univ, true_and, β', r]
      constructor
      · intro h; rw [← h]; simp
      · intro h
        rw [Equiv.apply_eq_iff_eq_symm_apply]
        exact Subtype.ext h
    rw [this]; exact hfib _ (eqv.symm i).2
  let e : V ≃ Fin k × Fin 3 := (Equiv.sigmaFiberEquiv β').symm.trans
    ((Equiv.sigmaCongrRight fun i => Fintype.equivFinOfCardEq (hfib' i)).trans
      (Equiv.sigmaEquivProd _ _))
  have he1 : ∀ x, (e x).1 = β' x := fun x => rfl
  refine ⟨G.comap r, inferInstance, ?_, ⟨⟨e, fun {x x'} => ?_⟩⟩⟩
  · have hm : (G.comap r).adjMatrix (ZMod 2) = ((G.adjMatrix (ZMod 2)).submatrix (fun b : B1 => (b : V))
        (fun b : B1 => (b : V))).submatrix eqv.symm eqv.symm := by
      ext i j
      simp [adjMatrix_apply, r]
    rw [hm, det_submatrix_equiv_self]
    exact hΘ.ne_zero
  · show (tripling (G.comap r)).Adj (e x) (e x') ↔ G.Adj x x'
    rw [tripling_adj, he1, he1]
    show G.Adj (r (β' x)) (r (β' x')) ↔ G.Adj x x'
    rw [hrβ, hrβ]
    have h := hAβ x x'
    simp only [adjMatrix_apply] at h
    by_cases h1 : G.Adj x x' <;> by_cases h2 : G.Adj (β x) (β x') <;> simp_all

/-! ### Being minimal forbidden is invariant under isomorphism -/

variable {V' : Type*} [Fintype V'] [DecidableEq V']

/-- An isomorphism restricts to induced subgraphs. -/
def isoInduce {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (s : Finset V) :
    G.induce (s : Set V) ≃g G'.induce ((s.map φ.toEquiv.toEmbedding : Finset V') : Set V') where
  toEquiv := φ.toEquiv.subtypeEquiv (fun x => by simp)
  map_rel_iff' := by
    intro a b
    simp only [comap_adj, Function.Embedding.coe_subtype, Equiv.subtypeEquiv_apply]
    exact φ.map_adj_iff

theorem minForb_of_iso {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') {k : ℕ}
    (hc : k + 1 ≤ c2 G')
    (hmin : ∀ s : Finset V', s ≠ univ → c2 (G'.induce (s : Set V')) ≤ k) :
    k + 1 ≤ c2 G ∧ ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k := by
  classical
  refine ⟨by rw [c2_iso φ]; exact hc, fun s hs => ?_⟩
  rw [c2_iso (isoInduce φ s)]
  apply hmin
  intro h
  apply hs
  apply eq_univ_of_card
  have h1 := congrArg Finset.card h
  rw [card_map, card_univ] at h1
  rw [h1]
  exact Fintype.card_congr φ.toEquiv |>.symm

end FreeDiagonal.EvenComplementation
