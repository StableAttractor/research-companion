import FreeDiagonal.Graphs.Lempel
import FreeDiagonal.Graphs.MinRankF2

/-!
# Task C: subgraph complementation number, and Corollary 5 of the note

`c2 G` (Buchanan, Purcell, Rombach): the least number of vertex sets `S₁, …, S_s` whose cliques
sum to `G` modulo 2, i.e. two distinct vertices are adjacent iff they lie together in an odd
number of the `S_i`. (Equivalently: the least number of operations "complement the induced
subgraph on a vertex set" producing `G` from the edgeless graph.)

* `c2_eq_matrix_form`: `c2 G` is the least `s` with `adj(G) + D = B Bᵀ` for a diagonal `D` and a
  `V × s` matrix `B` over `ZMod 2`.
* C1: `mrF2_le_c2`, `c2_le_mrF2_add_one`, and `c2_eq_mrF2_add_one_iff` (c2 = mr + 1 iff every
  minimum-rank fitting matrix has zero diagonal), the last for graphs with `mr ≥ 1`. For
  edgeless graphs `c2 = mr = 0` (`c2_eq_zero_of_mrF2_eq_zero`) although the only optimal matrix
  has zero diagonal, so the hypothesis `mr ≥ 1` cannot be dropped there.
* `c2_le_iff_mrF2_le_of_odd`: for odd `k`, `c2 ≤ k ↔ mr ≤ k` (BPR Proposition 5.1, reproved).
* C2: `cor5` and `cor5_odd` (Corollary 5 of the note).
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` writes `G` as a sum modulo 2 of the cliques on the sets `S i`. -/
def IsCliqueSum (G : SimpleGraph V) {s : ℕ} (S : Fin s → Finset V) : Prop :=
  ∀ u v, u ≠ v → (G.Adj u v ↔ Odd (univ.filter fun i => u ∈ S i ∧ v ∈ S i).card)

/-- The subgraph complementation number `c₂(G)`. -/
noncomputable def c2 (G : SimpleGraph V) : ℕ :=
  sInf {s | ∃ S : Fin s → Finset V, IsCliqueSum G S}

/-- `B Bᵀ` agrees with the adjacency matrix off the diagonal. -/
def IsSqFit (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ} (B : Matrix V (Fin s) (ZMod 2)) :
    Prop :=
  ∀ u v, u ≠ v → (B * Bᵀ) u v = G.adjMatrix (ZMod 2) u v

lemma zmod2_mul_eq_ite (a b : ZMod 2) : a * b = if a = 1 ∧ b = 1 then 1 else 0 := by
  revert a b; decide

lemma zmod2_ite_iff (p : Prop) [Decidable p] (n : ℕ) :
    ((if p then 1 else 0 : ZMod 2) = (n : ZMod 2)) ↔ (p ↔ Odd n) := by
  by_cases hp : p
  · simp only [hp, if_true, true_iff]
    rw [eq_comm, ZMod.natCast_eq_one_iff_odd]
  · simp only [hp, if_false, false_iff, Nat.not_odd_iff_even]
    rw [eq_comm, ZMod.natCast_eq_zero_iff_even]

lemma cliqueSum_iff_sqFit (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    (∃ S : Fin s → Finset V, IsCliqueSum G S) ↔ ∃ B : Matrix V (Fin s) (ZMod 2), IsSqFit G B := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨Matrix.of fun u i => if u ∈ S i then 1 else 0, fun u v huv => ?_⟩
    rw [Matrix.mul_apply, adjMatrix_apply]
    have : ∑ i, (Matrix.of fun u i => if u ∈ S i then (1 : ZMod 2) else 0) u i *
        (Matrix.of fun u i => if u ∈ S i then (1 : ZMod 2) else 0)ᵀ i v =
        ∑ i, if (u ∈ S i ∧ v ∈ S i) then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl; intro i _
      by_cases h1 : u ∈ S i <;> by_cases h2 : v ∈ S i <;> simp [h1, h2]
    rw [this, Finset.sum_boole, eq_comm, zmod2_ite_iff]
    exact hS u v huv
  · rintro ⟨B, hB⟩
    refine ⟨fun i => univ.filter fun u => B u i = 1, fun u v huv => ?_⟩
    have h := hB u v huv
    rw [Matrix.mul_apply, adjMatrix_apply] at h
    have : ∑ i, B u i * Bᵀ i v = ∑ i, if (B u i = 1 ∧ B v i = 1) then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl; intro i _
      rw [transpose_apply, zmod2_mul_eq_ite]
    rw [this, Finset.sum_boole, eq_comm, zmod2_ite_iff] at h
    simpa using h

lemma sqFit_iff (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (B : Matrix V (Fin s) (ZMod 2)) :
    IsSqFit G B ↔ ∃ d : V → ZMod 2, G.adjMatrix (ZMod 2) + diagonal d = B * Bᵀ := by
  constructor
  · intro h
    refine ⟨fun u => (B * Bᵀ) u u, ?_⟩
    ext u v
    by_cases huv : u = v
    · subst huv; simp [adjMatrix_apply]
    · rw [Matrix.add_apply, diagonal_apply_ne _ huv, add_zero, h u v huv]
  · rintro ⟨d, hd⟩ u v huv
    rw [← hd, Matrix.add_apply, diagonal_apply_ne _ huv, add_zero]

/-- **The matrix form of `c₂`**: the least `s` such that `adj(G) + D = B Bᵀ` for some diagonal
`D` and some `B` with `s` columns over `ZMod 2`. -/
theorem c2_eq_matrix_form (G : SimpleGraph V) [DecidableRel G.Adj] :
    c2 G = sInf {s | ∃ (B : Matrix V (Fin s) (ZMod 2)) (d : V → ZMod 2),
      G.adjMatrix (ZMod 2) + diagonal d = B * Bᵀ} := by
  unfold c2
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  rw [cliqueSum_iff_sqFit]
  constructor
  · rintro ⟨B, hB⟩; obtain ⟨d, hd⟩ := (sqFit_iff G B).1 hB; exact ⟨B, d, hd⟩
  · rintro ⟨B, d, hd⟩; exact ⟨B, (sqFit_iff G B).2 ⟨d, hd⟩⟩

lemma isSymm_adj_add_diag (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ZMod 2) :
    (G.adjMatrix (ZMod 2) + diagonal d).IsSymm :=
  (isSymm_adjMatrix G).add (isSymm_diagonal d)

lemma sqFit_of_eq (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ} (B : Matrix V (Fin s) (ZMod 2))
    (d : V → ZMod 2) (h : G.adjMatrix (ZMod 2) + diagonal d = B * Bᵀ) : IsSqFit G B :=
  (sqFit_iff G B).2 ⟨d, h⟩

lemma c2_le_of_sqFit (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (B : Matrix V (Fin s) (ZMod 2)) (h : IsSqFit G B) : c2 G ≤ s :=
  Nat.sInf_le ((cliqueSum_iff_sqFit G s).2 ⟨B, h⟩)

/-- A fitting matrix exists, so the infimum defining `c₂` is attained. -/
lemma exists_sqFit_c2 (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ B : Matrix V (Fin (c2 G)) (ZMod 2), IsSqFit G B := by
  obtain ⟨s, -, B, hB⟩ := lempel_le_add_one (G.adjMatrix (ZMod 2) + diagonal 0)
    (isSymm_adj_add_diag G 0)
  have hne : {s | ∃ S : Fin s → Finset V, IsCliqueSum G S}.Nonempty :=
    ⟨s, (cliqueSum_iff_sqFit G s).2 ⟨B, sqFit_of_eq G B 0 hB⟩⟩
  exact (cliqueSum_iff_sqFit G _).1 (Nat.sInf_mem hne)

/-- **C1, lower bound.** `mr(F₂, G) ≤ c₂(G)`. -/
theorem mrF2_le_c2 (G : SimpleGraph V) : mrF2 G ≤ c2 G := by
  classical
  obtain ⟨B, hB⟩ := exists_sqFit_c2 G
  obtain ⟨d, hd⟩ := (sqFit_iff G B).1 hB
  rw [mrF2_eq]
  calc minCompRank (G.adjMatrix (ZMod 2)) ≤ (G.adjMatrix (ZMod 2) + diagonal d).rank :=
        minCompRank_le _ d
    _ = (B * Bᵀ).rank := by rw [hd]
    _ ≤ B.rank := rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin (c2 G)) := rank_le_card_width B
    _ = c2 G := Fintype.card_fin _

/-- If some minimum-rank fitting matrix has a non-zero diagonal entry, `c₂ ≤ mr`. -/
lemma c2_le_mrF2_of_diag (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ZMod 2)
    (hd : (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G) (hne : d ≠ 0) :
    c2 G ≤ mrF2 G := by
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  obtain ⟨s, hs, B, hB⟩ := lempel_diag _ (isSymm_adj_add_diag G d) ⟨i, by simpa using hi⟩
  rw [hd] at hs
  exact (c2_le_of_sqFit G B (sqFit_of_eq G B d hB)).trans hs

/-- **C1, upper bound.** `c₂(G) ≤ mr(F₂, G) + 1`. -/
theorem c2_le_mrF2_add_one (G : SimpleGraph V) : c2 G ≤ mrF2 G + 1 := by
  classical
  obtain ⟨d, hd⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
  rw [← mrF2_eq] at hd
  obtain ⟨s, hs, B, hB⟩ := lempel_le_add_one _ (isSymm_adj_add_diag G d)
  rw [hd] at hs
  exact (c2_le_of_sqFit G B (sqFit_of_eq G B d hB)).trans hs

/-- **C1, characterisation** (for graphs with at least one edge, i.e. `mr ≥ 1`):
`c₂ = mr + 1` iff every minimum-rank fitting matrix `adj(G) + diagonal d` has zero diagonal,
i.e. `d = 0`. -/
theorem c2_eq_mrF2_add_one_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hpos : 0 < mrF2 G) :
    c2 G = mrF2 G + 1 ↔
      ∀ d : V → ZMod 2, (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G → d = 0 := by
  constructor
  · intro h d hd
    by_contra hne
    have := c2_le_mrF2_of_diag G d hd hne
    omega
  · intro h
    apply le_antisymm (c2_le_mrF2_add_one G)
    by_contra hlt
    push_neg at hlt
    obtain ⟨B, hB⟩ := exists_sqFit_c2 G
    obtain ⟨d, hd⟩ := (sqFit_iff G B).1 hB
    have hge : mrF2 G ≤ (G.adjMatrix (ZMod 2) + diagonal d).rank := by
      rw [mrF2_eq]; exact minCompRank_le _ d
    have hle : (G.adjMatrix (ZMod 2) + diagonal d).rank ≤ c2 G := by
      rw [hd]
      calc (B * Bᵀ).rank ≤ B.rank := rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin (c2 G)) := rank_le_card_width B
        _ = c2 G := Fintype.card_fin _
    have hopt : (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G := by omega
    have hd0 := h d hopt
    subst hd0
    have hzero : ∀ i, (B * Bᵀ) i i = 0 := fun i => by rw [← hd]; simp [adjMatrix_apply]
    have hne : B * Bᵀ ≠ 0 := by
      intro h0
      rw [hd, h0, rank_zero] at hopt
      omega
    have := rank_add_one_le_of_zero_diag B hzero hne
    rw [← hd] at this
    omega

/-- The edge case: if `mr(F₂, G) = 0` (no edges) then `c₂(G) = 0`, although the only optimal
fitting matrix, `0`, has zero diagonal. -/
theorem c2_eq_zero_of_mrF2_eq_zero (G : SimpleGraph V) (h : mrF2 G = 0) : c2 G = 0 := by
  classical
  obtain ⟨d, hd⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
  rw [← mrF2_eq, h] at hd
  have h0 : G.adjMatrix (ZMod 2) + diagonal d = 0 := by
    unfold Matrix.rank at hd
    have h1 := Submodule.finrank_eq_zero.1 hd
    rw [LinearMap.range_eq_bot] at h1
    ext i j
    have := congrFun (LinearMap.congr_fun h1 (Pi.single j 1)) i
    rw [Matrix.mulVecLin_apply, mulVec_single_one, LinearMap.zero_apply] at this
    simpa only [Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply] using this
  have hfit : IsSqFit G (0 : Matrix V (Fin 0) (ZMod 2)) := by
    intro u v huv
    have := congrFun (congrFun h0 u) v
    rw [Matrix.add_apply, diagonal_apply_ne _ huv, add_zero] at this
    rw [this]; simp
  exact Nat.le_zero.1 (c2_le_of_sqFit G _ hfit)

/-- For odd `k`, the classes `c₂ ≤ k` and `mr ≤ k` coincide (BPR, Proposition 5.1 of the arXiv
version; reproved here from L1 and L3). -/
theorem c2_le_iff_mrF2_le_of_odd (G : SimpleGraph V) {k : ℕ} (hk : Odd k) :
    c2 G ≤ k ↔ mrF2 G ≤ k := by
  classical
  constructor
  · exact fun h => (mrF2_le_c2 G).trans h
  · intro h
    rcases Nat.lt_or_ge (mrF2 G) k with hlt | hge
    · exact (c2_le_mrF2_add_one G).trans (by omega)
    · have heq : mrF2 G = k := le_antisymm h hge
      obtain ⟨d, hd⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
      rw [← mrF2_eq] at hd
      by_cases hd0 : d = 0
      · -- zero diagonal: the rank would be even
        subst hd0
        have hev := even_rank_of_zero_diag _ (isSymm_adj_add_diag G 0)
          (fun i => by simp [adjMatrix_apply])
        rw [hd, heq] at hev
        exact absurd hev (Nat.not_even_iff_odd.2 hk)
      · exact (c2_le_mrF2_of_diag G d hd hd0).trans h

/-- `c₂` does not increase on induced subgraphs. -/
theorem c2_induce_mono (G : SimpleGraph V) {s t : Finset V} (hst : s ⊆ t) :
    c2 (G.induce (s : Set V)) ≤ c2 (G.induce (t : Set V)) := by
  classical
  have hne : {c | ∃ S : Fin c → Finset ↥(t : Set V), IsCliqueSum (G.induce (t : Set V)) S}.Nonempty := by
    obtain ⟨B, hB⟩ := exists_sqFit_c2 (G.induce (t : Set V))
    exact ⟨_, (cliqueSum_iff_sqFit _ _).2 ⟨B, hB⟩⟩
  obtain ⟨S, hS⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨fun i => univ.filter fun x : ↥(s : Set V) => (⟨x.1, hst x.2⟩ : ↥(t : Set V)) ∈ S i, ?_⟩
  intro u v huv
  have huv' : (⟨u.1, hst u.2⟩ : ↥(t : Set V)) ≠ ⟨v.1, hst v.2⟩ :=
    fun h => huv (Subtype.ext (by simpa using congrArg Subtype.val h))
  have := hS _ _ huv'
  simp only [comap_adj, Function.Embedding.coe_subtype] at this ⊢
  rw [this]
  exact Iff.of_eq (by congr; funext i; simp)

lemma c2_induce_le (G : SimpleGraph V) (s : Finset V) :
    c2 (G.induce (s : Set V)) ≤ c2 G := by
  classical
  obtain ⟨S, hS⟩ := (cliqueSum_iff_sqFit G _).2 (exists_sqFit_c2 G)
  apply Nat.sInf_le
  refine ⟨fun i => univ.filter fun x : ↥(s : Set V) => x.1 ∈ S i, ?_⟩
  intro u v huv
  have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  have := hS _ _ huv'
  simp only [comap_adj, Function.Embedding.coe_subtype] at this ⊢
  rw [this]
  simp

/-- **Corollary 5 of the note.** If `H` is a minimal forbidden induced subgraph for `c₂ ≤ k`
and `mr(F₂, H) ≥ k + 1`, then `H` has at most `2k + 2` vertices. (The hypothesis `k ≥ 1` of
the note is not needed.) -/
theorem cor5 (H : SimpleGraph V) (k : ℕ) (_hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k)
    (hmr : k + 1 ≤ mrF2 H) : Fintype.card V ≤ 2 * k + 2 :=
  cor4_minimal H k hmr (fun s hs => (mrF2_le_c2 _).trans (hmin s hs))

/-- **Corollary 5 for odd `k`.** Every minimal forbidden induced subgraph for `c₂ ≤ k` has at
most `2k + 2` vertices: the BPR conjecture holds for odd `k`. -/
theorem cor5_odd (H : SimpleGraph V) {k : ℕ} (hk : Odd k) (hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 2 * k + 2 := by
  have hmr : k + 1 ≤ mrF2 H := by
    by_contra h
    push_neg at h
    have := (c2_le_iff_mrF2_le_of_odd H hk).2 (by omega)
    omega
  exact cor5 H k hc hmin hmr

end FreeDiagonal
