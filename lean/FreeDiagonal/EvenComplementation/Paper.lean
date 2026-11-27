import FreeDiagonal.EvenComplementation.FrontDoor
import FreeDiagonal.EvenComplementation.LinAlg
import FreeDiagonal.EvenComplementation.Witness3
import FreeDiagonal.Witness.RankFormula

/-!
# The sharp `3k` obstruction bound for subgraph complementation at even `k`

Every numbered statement of the paper *The Sharp 3k Obstruction Bound for Subgraph
Complementation at Even k*, and the four facts (a)–(d) of its Section 1, under names that follow
the paper's numbering.

* Section 1: `fact_a`, `fact_b`, `fact_c`, `fact_d`; the definition `IsRigid` (`k`-rigid graphs);
  `lemma1` (with its two halves `lemma1_rigid`, `lemma1_dichotomy`).
* Section 2, over an arbitrary field: `lemma2` (the rank formula for the factorisation
  `A = U S Uᵀ` of Section 2), `lemma2_of_factor` (the same formula for any factorisation
  `A = U S Uᵀ` with `S` invertible), `lemma2_remark`; `lemma3` (the construction as printed) and
  `lemma3_exists` (its conclusion as an existence statement).
* Section 3: `theorem1`, `theorem2` (with `theorem2_tripling`, `theorem2_classification`),
  `corollary3`.

Conventions. Graphs live on a finite type `V`; `c2 G` is the subgraph complementation number
(least number of vertex sets whose cliques sum to `G` modulo 2), `mrF2 G` the minimum rank over
`F₂ = ZMod 2`, `G.induce s` the induced subgraph on a vertex set `s`. "Minimal forbidden induced
subgraph for `c₂ ≤ k`" is written `k < c2 H ∧ ∀ s ≠ univ, c2 (H.induce s) ≤ k`. A diagonal matrix
is `diagonal d` for a vector `d`; `d ≠ 0` means the diagonal matrix is non-zero. The rank of the
rows of a matrix `M` indexed by a set `Y` is `frk F M.row Y` (the dimension of their span); with
`M = A` this is the paper's `ρ(Y)` (`rho_eq`). The principal submatrix `A[I, I]` is
`A.submatrix (↑) (↑)` on the subtype of `I`.

The rank of the bilinear form `(x, y) ↦ xᵀ H y` restricted to a subspace `W` (`formRankOn`) is the
rank of the linear map `W → W*`, `y ↦ (x ↦ xᵀ H y)`; `formRankOn_eq_rank_gram` shows that this is
the rank of the Gram matrix `(b_a ᵀ H b_c)` in any basis `b` of `W`, the usual definition.
-/

open Matrix Module Submodule Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation.Paper

open FreeDiagonal FreeDiagonal.EvenComplementation

/-! ## Section 1: facts (a)–(d), `k`-rigid graphs, Lemma 1 -/

section Graphs

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The function `f` of fact (a): `f(M) = rank M` if `M = 0` or `M` has a non-zero diagonal entry,
and `f(M) = rank M + 1` otherwise. -/
noncomputable def fval {m : Type*} [Fintype m] (M : Matrix m m (ZMod 2)) : ℕ :=
  if M = 0 ∨ ∃ i, M i i ≠ 0 then M.rank else M.rank + 1

omit [DecidableEq V] in
lemma fval_le {m : Type*} [Fintype m] (M : Matrix m m (ZMod 2)) : fval M ≤ M.rank + 1 := by
  unfold fval; split_ifs <;> omega

omit [DecidableEq V] in
lemma fval_of_diag {m : Type*} [Fintype m] (M : Matrix m m (ZMod 2)) (h : ∃ i, M i i ≠ 0) :
    fval M = M.rank := by
  unfold fval
  split_ifs with h'
  · rfl
  · exact absurd (Or.inr h) h'

lemma c2_le_fval (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ZMod 2) :
    c2 G ≤ fval (G.adjMatrix (ZMod 2) + diagonal d) := by
  have hsym : (G.adjMatrix (ZMod 2) + diagonal d).IsSymm := isSymm_adj_add_diag G d
  unfold fval
  split_ifs with h
  · rcases h with h0 | hdiag
    · have hfit : IsSqFit G (0 : Matrix V (Fin 0) (ZMod 2)) := by
        intro u v huv
        have := congrFun (congrFun h0 u) v
        rw [Matrix.add_apply, diagonal_apply_ne _ huv, add_zero] at this
        rw [this]; simp
      exact (c2_le_of_sqFit G _ hfit).trans (Nat.zero_le _)
    · obtain ⟨s, hs, B, hB⟩ := lempel_diag _ hsym hdiag
      exact (c2_le_of_sqFit G B (sqFit_of_eq G B d hB)).trans hs
  · obtain ⟨s, hs, B, hB⟩ := lempel_le_add_one _ hsym
    exact (c2_le_of_sqFit G B (sqFit_of_eq G B d hB)).trans hs

lemma exists_fval_eq_c2 (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ d : V → ZMod 2, fval (G.adjMatrix (ZMod 2) + diagonal d) = c2 G := by
  obtain ⟨B, hB⟩ := exists_sqFit_c2 G
  obtain ⟨d, hd⟩ := (sqFit_iff G B).1 hB
  refine ⟨d, le_antisymm ?_ (c2_le_fval G d)⟩
  have hrk : (G.adjMatrix (ZMod 2) + diagonal d).rank ≤ c2 G := by
    rw [hd]
    calc (B * Bᵀ).rank ≤ B.rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin (c2 G)) := rank_le_card_width B
      _ = c2 G := Fintype.card_fin _
  unfold fval
  split_ifs with h
  · exact hrk
  · have h1 : G.adjMatrix (ZMod 2) + diagonal d ≠ 0 := fun h0 => h (Or.inl h0)
    have h2 : ∀ i, (G.adjMatrix (ZMod 2) + diagonal d) i i = 0 := fun i => by
      by_contra hi; exact h (Or.inr ⟨i, hi⟩)
    have hzero : ∀ i, (B * Bᵀ) i i = 0 := fun i => by rw [← hd]; exact h2 i
    have hne : B * Bᵀ ≠ 0 := by rw [← hd]; exact h1
    have := rank_add_one_le_of_zero_diag B hzero hne
    rw [← hd] at this
    exact this

/-- **Fact (a).** `c₂(G)` is the least value of `f(M)` over the completions `M = A + D` of `G`
(`A` the adjacency matrix over `F₂`, `D` diagonal), where `f(M) = rank M` if `M = 0` or `M` has a
non-zero diagonal entry and `f(M) = rank M + 1` otherwise. -/
theorem fact_a (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsLeast {m | ∃ d : V → ZMod 2, m = fval (G.adjMatrix (ZMod 2) + diagonal d)} (c2 G) := by
  obtain ⟨d, hd⟩ := exists_fval_eq_c2 G
  exact ⟨⟨d, hd.symm⟩, by rintro m ⟨d', rfl⟩; exact c2_le_fval G d'⟩

/-- **Fact (b).** `c₂` does not increase on induced subgraphs. -/
theorem fact_b (G : SimpleGraph V) (s : Finset V) : c2 (G.induce (s : Set V)) ≤ c2 G :=
  c2_induce_le G s

/-- **Fact (c).** A symmetric matrix over `F₂` with zero diagonal has even rank. -/
theorem fact_c {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m (ZMod 2)) (hM : M.IsSymm)
    (hd : ∀ i, M i i = 0) : Even M.rank :=
  even_rank_of_zero_diag M hM hd

/-- **Fact (d).** Every minimal forbidden induced subgraph for `mr(F₂, G) ≤ k` has at most
`2k + 2` vertices. -/
theorem fact_d (G : SimpleGraph V) (k : ℕ) (hk : k < mrF2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → mrF2 (G.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 2 * k + 2 :=
  cor4_minimal G k hk hmin

/-- A graph `G` is **`k`-rigid** if its adjacency matrix `A` over `F₂` has rank `k` and
`rank (A + D) > k` for every non-zero diagonal `D`: the adjacency matrix is the only completion
of rank at most `k`. -/
def IsRigid (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  (G.adjMatrix (ZMod 2)).rank = k ∧
    ∀ d : V → ZMod 2, d ≠ 0 → k < (G.adjMatrix (ZMod 2) + diagonal d).rank

/-- **Lemma 1, first statement.** Let `k ≥ 1`. If `G` is `k`-rigid, then `k` is even and
`c₂(G) = k + 1`. -/
theorem lemma1_rigid (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (hG : IsRigid G k) : Even k ∧ c2 G = k + 1 := by
  obtain ⟨hr, hrig⟩ := hG
  have hmr : mrF2 G = k := by
    rw [mrF2_eq]
    apply le_antisymm
    · have := minCompRank_le (G.adjMatrix (ZMod 2)) 0
      simpa [hr] using this
    · apply le_minCompRank
      intro d
      by_cases hd : d = 0
      · subst hd; simp [hr]
      · exact (hrig d hd).le
  refine ⟨?_, ?_⟩
  · rw [← hr]
    exact fact_c _ (isSymm_adjMatrix G) (fun i => by simp [adjMatrix_apply])
  · rw [← hmr]
    apply (c2_eq_mrF2_add_one_iff G (by omega)).2
    intro d hd
    by_contra hne
    have := hrig d hne
    omega

/-- **Lemma 1, second statement.** If `c₂(G) > k`, then `mr(F₂, G) > k` or `G` is `k`-rigid.
(This half holds for every `k ≥ 0`.) -/
theorem lemma1_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hc : k < c2 G) :
    k < mrF2 G ∨ IsRigid G k := by
  by_contra hcon
  rw [not_or, not_lt] at hcon
  obtain ⟨hmr, hnr⟩ := hcon
  apply hnr
  have hdiag : ∀ d : V → ZMod 2, d ≠ 0 → k < (G.adjMatrix (ZMod 2) + diagonal d).rank := by
    intro d hd
    have hne : ∃ i, (G.adjMatrix (ZMod 2) + diagonal d) i i ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hd
      exact ⟨i, by simpa [adjMatrix_apply] using hi⟩
    have := c2_le_fval G d
    rw [fval_of_diag _ hne] at this
    omega
  refine ⟨le_antisymm ?_ ?_, hdiag⟩
  · by_contra h
    rw [not_le] at h
    obtain ⟨d, hd⟩ := exists_minCompRank (G.adjMatrix (ZMod 2))
    rw [← mrF2_eq] at hd
    by_cases hd0 : d = 0
    · subst hd0
      have hz : G.adjMatrix (ZMod 2) + diagonal (0 : V → ZMod 2) = G.adjMatrix (ZMod 2) := by
        simp
      rw [hz] at hd
      omega
    · have := hdiag d hd0; omega
  · by_contra h
    rw [not_le] at h
    have h1 := c2_le_fval G 0
    have h2 := fval_le (G.adjMatrix (ZMod 2) + diagonal 0)
    have hz : G.adjMatrix (ZMod 2) + diagonal (0 : V → ZMod 2) = G.adjMatrix (ZMod 2) := by
      simp
    rw [hz] at h1 h2
    omega

/-- **Lemma 1.** Let `k ≥ 1`. If `G` is `k`-rigid, then `k` is even and `c₂(G) = k + 1`. If
`c₂(G) > k`, then `mr(F₂, G) > k` or `G` is `k`-rigid. -/
theorem lemma1 (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k) :
    (IsRigid G k → Even k ∧ c2 G = k + 1) ∧ (k < c2 G → k < mrF2 G ∨ IsRigid G k) :=
  ⟨lemma1_rigid G hk, lemma1_dichotomy G⟩

/-- The hypothesis `k ≥ 1` of Lemma 1 is needed for its first statement: the edgeless graph on
one vertex is `0`-rigid and has `c₂ = 0`. -/
theorem lemma1_rigid_needs_one_le :
    IsRigid (⊥ : SimpleGraph (Fin 1)) 0 ∧ c2 (⊥ : SimpleGraph (Fin 1)) = 0 := by
  have hA : (⊥ : SimpleGraph (Fin 1)).adjMatrix (ZMod 2) = 0 := by
    ext i j; simp [adjMatrix_apply]
  refine ⟨⟨by rw [hA, rank_zero], fun d hd => ?_⟩, ?_⟩
  · rw [hA, zero_add, rank_diagonal]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hd
    exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
  · have h := c2_le_fval (⊥ : SimpleGraph (Fin 1)) 0
    have h0 : fval ((⊥ : SimpleGraph (Fin 1)).adjMatrix (ZMod 2) + diagonal 0) = 0 := by
      have hz : (⊥ : SimpleGraph (Fin 1)).adjMatrix (ZMod 2) + diagonal (0 : Fin 1 → ZMod 2) = 0 := by
        rw [hA]; simp
      unfold fval
      rw [hz]
      simp
    omega

end Graphs

/-! ## Section 2: the rank formula and the witness, over any field -/

section LinearAlgebra

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `W^⊥ = {x : u x = 0 for all u ∈ W}` (orthogonal complement for the dot product). -/
def dotPerp (W : Submodule F (κ → F)) : Submodule F (κ → F) where
  carrier := {x | ∀ u ∈ W, u ⬝ᵥ x = 0}
  add_mem' := by
    intro a b ha hb u hu
    have ha' : ∀ u ∈ W, u ⬝ᵥ a = 0 := ha
    have hb' : ∀ u ∈ W, u ⬝ᵥ b = 0 := hb
    show u ⬝ᵥ (a + b) = 0
    rw [dotProduct_add, ha' u hu, hb' u hu, add_zero]
  zero_mem' := by intro u _; exact dotProduct_zero u
  smul_mem' := by
    intro c a ha u hu
    have ha' : ∀ u ∈ W, u ⬝ᵥ a = 0 := ha
    show u ⬝ᵥ (c • a) = 0
    rw [dotProduct_smul, ha' u hu, smul_zero]

/-- **The rank of the bilinear form `(x, y) ↦ xᵀ H y` restricted to `W`**: the rank of the linear
map `W → W*`, `y ↦ (x ↦ xᵀ H y)`. By `formRankOn_eq_rank_gram` it is the rank of the Gram matrix
of the form in any basis of `W`. -/
noncomputable def formRankOn (H : Matrix κ κ F) (W : Submodule F (κ → F)) : ℕ :=
  finrank F (LinearMap.range (betaForm H W W))

omit [DecidableEq κ] in
/-- The restricted rank is the rank of the Gram matrix `(b_aᵀ H b_c)_{a,c}` in any basis `b` of
`W`. -/
theorem formRankOn_eq_rank_gram (H : Matrix κ κ F) (W : Submodule F (κ → F)) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι F W) :
    formRankOn H W = (Matrix.of fun a c => (b a : κ → F) ⬝ᵥ (H *ᵥ (b c : κ → F))).rank := by
  set G : Matrix ι ι F := Matrix.of fun a c => (b a : κ → F) ⬝ᵥ (H *ᵥ (b c : κ → F)) with hG
  have key : Matrix.toLin b b.dualBasis G = betaForm H W W := by
    refine b.ext fun c => ?_
    refine Basis.ext b (f₁ := (Matrix.toLin b b.dualBasis G (b c) : W →ₗ[F] F))
      (f₂ := (betaForm H W W (b c) : W →ₗ[F] F)) fun a => ?_
    rw [Matrix.toLin_self]
    simp [betaForm, hG, Finsupp.single_apply]
  unfold formRankOn
  rw [Matrix.rank_eq_finrank_range_toLin G b.dualBasis b, key]

open Classical in
/-- The support `{i : d i ≠ 0}` of the diagonal matrix `diagonal d`. -/
noncomputable def supp (d : n → F) : Finset n := univ.filter fun i => d i ≠ 0

/-- `H_T = -S⁻¹ - Σ_{i ∈ T} D_ii⁻¹ u_iᵀ u_i`, where `u_i` is row `i` of `U`. -/
noncomputable def Hmat (U : Matrix n κ F) (S : Matrix κ κ F) (d : n → F) (T : Finset n) :
    Matrix κ κ F :=
  -S⁻¹ - ∑ i ∈ T, (d i)⁻¹ • vecMulVec (U i) (U i)

omit [DecidableEq κ] in
lemma betaForm_neg (M : Matrix κ κ F) (Ψ Φ : Submodule F (κ → F)) :
    betaForm (-M) Ψ Φ = -betaForm M Ψ Φ := by
  ext φ ψ
  simp [betaForm, neg_mulVec, dotProduct_neg]

lemma annSub_eq_dotPerp (U : Matrix n κ F) (Z : Finset n) :
    annSub U Z = dotPerp (span F (U.row '' (Z : Set n))) := by
  ext x
  rw [mem_annSub]
  constructor
  · intro h u hu
    have hle : span F (U.row '' (Z : Set n)) ≤ LinearMap.ker (dotL x) := by
      rw [span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact h i hi
    have := hle hu
    simpa [dotL] using this
  · intro h i hi
    exact h (U i) (subset_span ⟨i, hi, rfl⟩)

/-- **Lemma 2 for any factorisation.** Let `A = U S Uᵀ` with `S` an invertible `k × k` matrix
(`k = |κ|`) and `U` any `n × k` matrix, `u_i` the rows of `U`. Let `D = diagonal d` have support
`T`, let `V` be the span of the rows `u_i` with `i ∉ T`, of dimension `r`, and
`H_T = -S⁻¹ - Σ_{i ∈ T} D_ii⁻¹ u_iᵀ u_i`. Then
`rank (A + D) = |T| + 2r - k + rank (H_T restricted to V^⊥)`. -/
theorem lemma2_of_factor (U : Matrix n κ F) (S : Matrix κ κ F) (hS : IsUnit S.det) (d : n → F) :
    ((U * S * Uᵀ + diagonal d).rank : ℤ) =
      (supp d).card + 2 * finrank F (span F (U.row '' ↑(univ \ supp d))) - Fintype.card κ +
        formRankOn (Hmat U S d (supp d)) (dotPerp (span F (U.row '' ↑(univ \ supp d)))) := by
  set T := supp d with hT
  set Z := univ \ T with hZdef
  have hΘ : IsUnit (S⁻¹).det := isUnit_nonsing_inv_det S hS
  have hZ : ∀ i, i ∈ Z ↔ (-d) i = 0 := by intro i; simp [Z, T, supp]
  have h := rank_formula U U S⁻¹ hΘ (-d) Z hZ
  have e1 : U * S⁻¹⁻¹ * Uᵀ - diagonal (-d) = U * S * Uᵀ + diagonal d := by
    rw [nonsing_inv_nonsing_inv S hS, show diagonal (-d) = -diagonal d from (diagonal_neg d).symm,
      sub_neg_eq_add]
  have e2 : betaMat U U S⁻¹ (-d) Z = -Hmat U S d T := by
    have hc : Zᶜ = T := by ext i; simp [Z]
    rw [betaMat, hc, Hmat]
    simp only [Pi.neg_apply, inv_neg, neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add, neg_sub]
    abel
  rw [e1, e2, annSub_eq_dotPerp, betaForm_neg, LinearMap.range_neg] at h
  have hcard : Z.card + T.card = Fintype.card n := by
    rw [hZdef, card_sdiff_add_card_eq_card (subset_univ T), card_univ]
  unfold formRankOn
  unfold frk at h
  omega

/-- **Remark after Lemma 2.** In the setting of `lemma2_of_factor`,
`rank (A + D) ≥ |T| + k - 2d` with `d = k - r`. -/
theorem lemma2_remark_of_factor (U : Matrix n κ F) (S : Matrix κ κ F) (hS : IsUnit S.det)
    (d : n → F) :
    ((supp d).card : ℤ) + Fintype.card κ -
        2 * (Fintype.card κ - finrank F (span F (U.row '' ↑(univ \ supp d)))) ≤
      (U * S * Uᵀ + diagonal d).rank := by
  rw [lemma2_of_factor U S hS d]
  have : (0 : ℤ) ≤ formRankOn (Hmat U S d (supp d))
    (dotPerp (span F (U.row '' ↑(univ \ supp d)))) := Int.natCast_nonneg _
  linarith

/-- The block `S = A[B, B]` of Section 2. -/
def Smat (A : Matrix n n F) (B : Finset n) : Matrix B B F :=
  A.submatrix (fun b : B => (b : n)) (fun b : B => (b : n))

/-- The matrix `U = A[E, B] S⁻¹` of Section 2. -/
noncomputable def Umat (A : Matrix n n F) (B : Finset n) : Matrix n B F :=
  A.submatrix id (fun b : B => (b : n)) * (Smat A B)⁻¹

omit [Fintype n] [DecidableEq n] in
lemma frk_of_linearIndependent {W : Type*} [AddCommGroup W] [Module F W] (u : n → W)
    (B : Finset n) (h : LinearIndependent F (fun b : B => u b)) : frk F u B = B.card := by
  have hset : Set.range (fun b : B => u b) = u '' (B : Set n) := by
    ext x; constructor
    · rintro ⟨b, rfl⟩; exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
  have := linearIndependent_iff_card_eq_finrank_span.1 h
  rw [hset, Fintype.card_coe] at this
  exact this.symm

omit [Fintype n] [DecidableEq n] in
lemma linearIndependent_of_frk {W : Type*} [AddCommGroup W] [Module F W] (u : n → W)
    (B : Finset n) (h : frk F u B = B.card) : LinearIndependent F (fun b : B => u b) := by
  have hset : Set.range (fun b : B => u b) = u '' (B : Set n) := by
    ext x; constructor
    · rintro ⟨b, rfl⟩; exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
  rw [linearIndependent_iff_card_eq_finrank_span, hset, Fintype.card_coe]
  exact h.symm

omit [DecidableEq n] in
lemma rows_mem_span_of_indep (A : Matrix n n F) (B : Finset n) (hind : frk F A.row B = B.card)
    (hBk : B.card = A.rank) : ∀ i, A.row i ∈ span F (A.row '' (B : Set n)) := by
  have hle : span F (A.row '' (B : Set n)) ≤ span F (A.row '' ((univ : Finset n) : Set n)) :=
    span_mono (Set.image_mono (by simp))
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    have h1 := rank_eq_frk_univ A
    unfold frk at hind h1
    omega)
  intro i
  rw [heq]
  exact subset_span ⟨i, by simp, rfl⟩

/-- **Section 2, the factorisation.** `A` symmetric, `B` a set of `rank A` independent rows. Then
`S = A[B, B]` is invertible, `A = U S Uᵀ` with `U = A[E, B] S⁻¹`, `A = U A[B, E]`, and `U` has
rank `k = rank A`. -/
theorem section2_factor (A : Matrix n n F) (hA : A.IsSymm) (B : Finset n)
    (hBind : LinearIndependent F (fun b : B => A.row b)) (hBk : B.card = A.rank) :
    IsUnit (Smat A B).det ∧ A = Umat A B * Smat A B * (Umat A B)ᵀ ∧
      A = Umat A B * A.submatrix (fun b : B => (b : n)) id ∧ (Umat A B).rank = A.rank := by
  have hind := frk_of_linearIndependent A.row B hBind
  obtain ⟨C, hfac, hC, hΘ⟩ :=
    factor_symm A hA B (rows_mem_span_of_indep A B hind hBk) hBk
  have hcol : A.submatrix id (fun b : B => (b : n)) = C * Smat A B := by
    conv_lhs => rw [hC]
    ext i b
    simp [Matrix.mul_apply, Smat]
  have hU : Umat A B = C := by
    rw [Umat, hcol, Matrix.mul_assoc, mul_nonsing_inv (Smat A B) hΘ, Matrix.mul_one]
  rw [hU]
  refine ⟨hΘ, hfac, hC, le_antisymm ?_ ?_⟩
  · calc C.rank ≤ Fintype.card B := rank_le_card_width C
      _ = A.rank := by rw [Fintype.card_coe, hBk]
  · calc A.rank = (C * Smat A B * Cᵀ).rank := congrArg Matrix.rank hfac
      _ ≤ (C * Smat A B).rank := rank_mul_le_left _ _
      _ ≤ C.rank := rank_mul_le_left _ _

/-- **Section 2, `ρ` does not depend on `B`.** With `B` and `U` as in Section 2, the rank `ρ(Y)`
of the rows `u_i`, `i ∈ Y`, of `U` equals the rank of the rows of `A` indexed by `Y`. -/
theorem rho_eq (A : Matrix n n F) (hA : A.IsSymm) (B : Finset n)
    (hBind : LinearIndependent F (fun b : B => A.row b)) (hBk : B.card = A.rank) (Y : Finset n) :
    frk F (Umat A B).row Y = frk F A.row Y :=
  frk_C_eq A B (Umat A B) (section2_factor A hA B hBind hBk).2.2.1
    (frk_of_linearIndependent A.row B hBind) Y

/-- **Lemma 2 (rank formula).** Let `A` be a symmetric `n × n` matrix of rank `k` over a field,
`B` a set of `k` independent rows, `S = A[B, B]`, `U = A[E, B] S⁻¹` (so `A = U S Uᵀ`,
`section2_factor`), `u_i` the rows of `U`. Let `D = diagonal d` have support `T`, let `V` be the
span of the rows `u_i` with `i ∉ T`, of dimension `r`, `V^⊥ = {x : u x = 0 for all u ∈ V}`, and
`H_T = -S⁻¹ - Σ_{i ∈ T} D_ii⁻¹ u_iᵀ u_i`. Then
`rank (A + D) = |T| + 2r - k + rank (H_T|_{V^⊥})`, the last term being the rank of the bilinear
form `xᵀ H_T y` restricted to `V^⊥`. -/
theorem lemma2 (A : Matrix n n F) (hA : A.IsSymm) (B : Finset n)
    (hBind : LinearIndependent F (fun b : B => A.row b)) (hBk : B.card = A.rank) (d : n → F) :
    ((A + diagonal d).rank : ℤ) =
      (supp d).card + 2 * finrank F (span F ((Umat A B).row '' ↑(univ \ supp d))) - A.rank +
        formRankOn (Hmat (Umat A B) (Smat A B) d (supp d))
          (dotPerp (span F ((Umat A B).row '' ↑(univ \ supp d)))) := by
  obtain ⟨hS, hfac, -, -⟩ := section2_factor A hA B hBind hBk
  have h := lemma2_of_factor (Umat A B) (Smat A B) hS d
  rw [← hfac, Fintype.card_coe, hBk] at h
  exact h

/-- **Remark after Lemma 2.** In the setting of Lemma 2, `rank (A + D) ≥ |T| + k - 2d` with
`d = k - r`. -/
theorem lemma2_remark (A : Matrix n n F) (hA : A.IsSymm) (B : Finset n)
    (hBind : LinearIndependent F (fun b : B => A.row b)) (hBk : B.card = A.rank) (d : n → F) :
    ((supp d).card : ℤ) + A.rank -
        2 * (A.rank - finrank F (span F ((Umat A B).row '' ↑(univ \ supp d)))) ≤
      (A + diagonal d).rank := by
  rw [lemma2 A hA B hBind hBk d]
  have : (0 : ℤ) ≤ formRankOn (Hmat (Umat A B) (Smat A B) d (supp d))
    (dotPerp (span F ((Umat A B).row '' ↑(univ \ supp d)))) := Int.natCast_nonneg _
  linarith

/-- `Bs ⊆ X` is a basis of the span of the vectors `u i`, `i ∈ X`: the vectors `u b`, `b ∈ Bs`,
are linearly independent and span the same space. -/
def IsBasisIn {W : Type*} [AddCommGroup W] [Module F W] (u : n → W) (X Bs : Finset n) : Prop :=
  Bs ⊆ X ∧ LinearIndependent F (fun b : Bs => u b) ∧
    span F (u '' (Bs : Set n)) = span F (u '' (X : Set n))

omit [Fintype n] [DecidableEq n] in
lemma IsBasisIn.card {W : Type*} [AddCommGroup W] [Module F W] {u : n → W} {X Bs : Finset n}
    (h : IsBasisIn (F := F) u X Bs) : Bs.card = frk F u X := by
  rw [← frk_of_linearIndependent u Bs h.2.1]
  unfold frk; rw [h.2.2]

omit [Fintype n] [DecidableEq n] in
/-- Being a basis is a statement about `ρ` alone: `Bs ⊆ X`, `ρ(Bs) = |Bs|` and `ρ(Bs) = ρ(X)`. -/
lemma isBasisIn_iff_frk {W : Type*} [AddCommGroup W] [Module F W] (u : n → W) (X Bs : Finset n) :
    IsBasisIn (F := F) u X Bs ↔ Bs ⊆ X ∧ frk F u Bs = Bs.card ∧ frk F u Bs = frk F u X := by
  constructor
  · intro h
    refine ⟨h.1, frk_of_linearIndependent u Bs h.2.1, ?_⟩
    unfold frk; rw [h.2.2]
  · rintro ⟨hs, hc, he⟩
    refine ⟨hs, linearIndependent_of_frk u Bs hc, ?_⟩
    exact Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (coe_subset.2 hs))) he

/-- **Section 2, bases do not depend on `B`.** With `U` as in Section 2, a set `Bs ⊆ X` is a basis
of the span of the rows `u_i`, `i ∈ X`, of `U` iff it is a basis of the span of the rows of `A`
indexed by `X`. So Lemma 3 may be read with the rows of `U` (as printed) or of `A`. -/
theorem isBasisIn_Umat_iff (A : Matrix n n F) (hA : A.IsSymm) (B : Finset n)
    (hBind : LinearIndependent F (fun b : B => A.row b)) (hBk : B.card = A.rank)
    (X Bs : Finset n) :
    IsBasisIn (F := F) (Umat A B).row X Bs ↔ IsBasisIn (F := F) A.row X Bs := by
  rw [isBasisIn_iff_frk, isBasisIn_iff_frk, rho_eq A hA B hBind hBk,
    rho_eq A hA B hBind hBk]

/-- Three disjoint bases of the rows in `X` let every completion of `A[I, I]`,
`I = (E \ X) ∪ B₁ ∪ B₂ ∪ B₃`, lift to a completion of `A` of no larger rank that keeps the value
at any one prescribed index (or at none). -/
lemma lift_three (A : Matrix n n F) (hA : A.IsSymm) (X B1 B2 B3 : Finset n)
    (h1 : IsBasisIn (F := F) A.row X B1) (h2 : IsBasisIn (F := F) A.row X B2)
    (h3 : IsBasisIn (F := F) A.row X B3) (d12 : Disjoint B1 B2) (d13 : Disjoint B1 B3)
    (d23 : Disjoint B2 B3) (d : n → F) (P : Finset n) (hPI : P ⊆ (univ \ X) ∪ B1 ∪ B2 ∪ B3)
    (hP : P.card ≤ 1) :
    ∃ d' : n → F, (∀ j ∈ P, d' j = d j) ∧
      (A + diagonal d').rank ≤ (subPattern A ((univ \ X) ∪ B1 ∪ B2 ∪ B3) +
        diagonal (fun a : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) => d a)).rank := by
  set I := (univ \ X) ∪ B1 ∪ B2 ∪ B3 with hI
  have h0 : A + diagonal (0 : n → F) = A := by simp
  have hG : (A + diagonal (0 : n → F)).IsSymm := by rw [h0]; exact hA
  have s1 : span F ((A + diagonal (0 : n → F)).row '' (B1 : Set n)) =
      span F ((A + diagonal (0 : n → F)).row '' (X : Set n)) := by rw [h0]; exact h1.2.2
  have s2 : span F ((A + diagonal (0 : n → F)).row '' (B2 : Set n)) =
      span F ((A + diagonal (0 : n → F)).row '' (X : Set n)) := by rw [h0]; exact h2.2.2
  have s3 : span F ((A + diagonal (0 : n → F)).row '' (B3 : Set n)) =
      span F ((A + diagonal (0 : n → F)).row '' (X : Set n)) := by rw [h0]; exact h3.2.2
  have hYT : univ \ X ⊆ I := fun i hi => by simp [hI, mem_union, hi]
  have hB1T : B1 ⊆ I := fun i hi => by simp [hI, mem_union, hi]
  have hB2T : B2 ⊆ I := fun i hi => by simp [hI, mem_union, hi]
  have hB3T : B3 ⊆ I := fun i hi => by simp [hI, mem_union, hi]
  by_cases hP1 : Disjoint P B1
  · by_cases hP2 : Disjoint P B2
    · exact lift_two A 0 hG X I P B1 B2 hYT h1.1 h2.1 hB1T hB2T hPI d12 hP1 hP2 s1 s2 d
    · exact lift_two A 0 hG X I P B1 B3 hYT h1.1 h3.1 hB1T hB3T hPI d13 hP1
        (disjoint_of_card_le_one hP hP2 d23) s1 s3 d
  · exact lift_two A 0 hG X I P B2 B3 hYT h2.1 h3.1 hB2T hB3T hPI d23
      (disjoint_of_card_le_one hP hP1 d12) (disjoint_of_card_le_one hP hP1 d13) s2 s3 d

/-- **Lemma 3 (witness), the construction as printed.** Let `A` be a symmetric `n × n` matrix of
rank `k` over a field with `rank (A + D) > k` for every non-zero diagonal `D`, and let `X`
maximise `|X| - 3ρ(X)`, `ρ(X)` the rank of the rows indexed by `X`. Then the rows indexed by `X`
contain three pairwise disjoint bases `B₁, B₂, B₃` of their span, and for any such bases and
`I = (E \ X) ∪ B₁ ∪ B₂ ∪ B₃` the principal submatrix `A[I, I]` has rank `k`,
`rank (A[I, I] + D) > k` for every non-zero diagonal `D` on `I`, and
`|I| = n - (|X| - 3ρ(X)) ≤ 3k`. -/
theorem lemma3 (A : Matrix n n F) (hA : A.IsSymm)
    (hrig : ∀ d : n → F, d ≠ 0 → A.rank < (A + diagonal d).rank) (X : Finset n)
    (hX : ∀ Y : Finset n, (Y.card : ℤ) - 3 * frk F A.row Y ≤ X.card - 3 * frk F A.row X) :
    (∃ B1 B2 B3 : Finset n, IsBasisIn (F := F) A.row X B1 ∧ IsBasisIn (F := F) A.row X B2 ∧
        IsBasisIn (F := F) A.row X B3 ∧ Disjoint B1 B2 ∧ Disjoint B1 B3 ∧ Disjoint B2 B3) ∧
    ∀ B1 B2 B3 : Finset n, IsBasisIn (F := F) A.row X B1 → IsBasisIn (F := F) A.row X B2 →
      IsBasisIn (F := F) A.row X B3 → Disjoint B1 B2 → Disjoint B1 B3 → Disjoint B2 B3 →
      (A.submatrix (fun i : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) => (i : n))
          (fun i : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) => (i : n))).rank = A.rank ∧
      (∀ d : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) → F, d ≠ 0 →
        A.rank < (A.submatrix (fun i : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) => (i : n))
          (fun i : ↥((univ \ X) ∪ B1 ∪ B2 ∪ B3) => (i : n)) + diagonal d).rank) ∧
      ((((univ \ X) ∪ B1 ∪ B2 ∪ B3).card : ℤ) =
        Fintype.card n - ((X.card : ℤ) - 3 * frk F A.row X)) ∧
      ((univ \ X) ∪ B1 ∪ B2 ∪ B3).card ≤ 3 * A.rank := by
  -- every completion of `A` has rank at least `k`
  have hge : ∀ d' : n → F, A.rank ≤ (A + diagonal d').rank := by
    intro d'
    by_cases hd' : d' = 0
    · subst hd'; simp
    · exact (hrig d' hd').le
  have hrkU : frk F A.row univ = A.rank := (rank_eq_frk_univ A).symm
  refine ⟨?_, ?_⟩
  · -- base packing (Edmonds) for three copies
    have hpack : ∀ Z ⊆ X, 3 * frk F A.row X ≤ (X \ Z).card + 3 * frk F A.row Z := by
      intro Z hZ
      have h := hX Z
      have e := card_sdiff_add_card_eq_card hZ
      omega
    obtain ⟨B1, B2, B3, h1, h2, h3, d12, d13, d23, c1, c2, c3, s1, s2, s3⟩ :=
      three_spanning_bases (F := F) A.row X hpack
    have mk : ∀ Bs : Finset n, Bs ⊆ X → Bs.card = frk F A.row X →
        span F (A.row '' (Bs : Set n)) = span F (A.row '' (X : Set n)) →
        IsBasisIn (F := F) A.row X Bs := by
      intro Bs hB hc hs
      refine ⟨hB, linearIndependent_of_frk A.row Bs ?_, hs⟩
      unfold frk at hc ⊢; rw [hs]; exact hc.symm
    exact ⟨B1, B2, B3, mk B1 h1 c1 s1, mk B2 h2 c2 s2, mk B3 h3 c3 s3, d12, d13, d23⟩
  intro B1 B2 B3 h1 h2 h3 d12 d13 d23
  set I := (univ \ X) ∪ B1 ∪ B2 ∪ B3 with hI
  -- the extension by zero of a diagonal on `I`
  have ext_eq : ∀ e : ↥I → F,
      (fun a : ↥I => (fun i : n => if h : i ∈ I then e ⟨i, h⟩ else 0) (a : n)) = e := by
    intro e; funext a; simp
  have hsub : ∀ e : ↥I → F, A.submatrix (fun i : ↥I => (i : n)) (fun i : ↥I => (i : n)) +
      diagonal e = subPattern A I + diagonal e := fun e => rfl
  -- the cardinality
  have hcard : (I.card : ℤ) = Fintype.card n - ((X.card : ℤ) - 3 * frk F A.row X) := by
    have dX1 : Disjoint (univ \ X) B1 := disjoint_of_subset_right h1.1 sdiff_disjoint
    have dX2 : Disjoint (univ \ X) B2 := disjoint_of_subset_right h2.1 sdiff_disjoint
    have dX3 : Disjoint (univ \ X) B3 := disjoint_of_subset_right h3.1 sdiff_disjoint
    have e1 := card_union_of_disjoint dX1
    have e2 := card_union_of_disjoint (disjoint_union_left.2 ⟨dX2, d12⟩)
    have e3 := card_union_of_disjoint (disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨dX3, d13⟩, d23⟩)
    have e4 := card_sdiff_add_card_eq_card (subset_univ X)
    rw [card_univ] at e4
    have c1 := h1.card; have c2 := h2.card; have c3 := h3.card
    rw [hI]
    omega
  refine ⟨?_, ?_, hcard, ?_⟩
  · -- `A[I, I]` has rank `k`
    apply le_antisymm (rank_submatrix_le _ _ _)
    obtain ⟨d', -, hd'⟩ := lift_three A hA X B1 B2 B3 h1 h2 h3 d12 d13 d23 0 ∅
      (empty_subset _) (by simp)
    have e : (subPattern A I + diagonal (fun a : ↥I => (0 : n → F) a)) =
        A.submatrix (fun i : ↥I => (i : n)) (fun i : ↥I => (i : n)) := by
      ext a b; simp [subPattern]
    rw [e] at hd'
    exact (hge d').trans hd'
  · intro d hd
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hd
    set dext : n → F := fun i => if h : i ∈ I then d ⟨i, h⟩ else 0 with hdext
    obtain ⟨d', hd'P, hd'⟩ := lift_three A hA X B1 B2 B3 h1 h2 h3 d12 d13 d23 dext {(j : n)}
      (singleton_subset_iff.2 j.2) (by simp)
    have hj' : d' (j : n) ≠ 0 := by
      rw [hd'P _ (mem_singleton_self _)]
      simpa [hdext] using hj
    have hne : d' ≠ 0 := fun h0 => hj' (by rw [h0]; rfl)
    rw [ext_eq d] at hd'
    rw [hsub d]
    exact lt_of_lt_of_le (hrig d' hne) hd'
  · have h := hX univ
    rw [card_univ, hrkU] at h
    omega

/-- **Lemma 3 (witness), existence form.** Let `A` be a symmetric `n × n` matrix of rank `k` over
a field such that `rank (A + D) > k` for every non-zero diagonal `D`. Then there is a set `I` of
at most `3k` indices such that `A[I, I]` has rank `k` and `rank (A[I, I] + D) > k` for every
non-zero diagonal `D` on `I`. -/
theorem lemma3_exists (A : Matrix n n F) (hA : A.IsSymm)
    (hrig : ∀ d : n → F, d ≠ 0 → A.rank < (A + diagonal d).rank) :
    ∃ I : Finset n, I.card ≤ 3 * A.rank ∧
      (A.submatrix (fun i : I => (i : n)) (fun i : I => (i : n))).rank = A.rank ∧
      ∀ d : I → F, d ≠ 0 →
        A.rank < (A.submatrix (fun i : I => (i : n)) (fun i : I => (i : n)) + diagonal d).rank := by
  obtain ⟨X, -, hX⟩ := exists_max_image (univ : Finset (Finset n))
    (fun Y => (Y.card : ℤ) - 3 * frk F A.row Y) univ_nonempty
  obtain ⟨⟨B1, B2, B3, h1, h2, h3, d12, d13, d23⟩, hI⟩ :=
    lemma3 A hA hrig X (fun Y => hX Y (mem_univ _))
  obtain ⟨hr, hrig', -, hc⟩ := hI B1 B2 B3 h1 h2 h3 d12 d13 d23
  exact ⟨_, hc, hr, hrig'⟩

end LinearAlgebra

/-! ## Section 3: the bound and the extremal graphs -/

section Theorems

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 1.** Let `k ≥ 2` be even. Every graph with `c₂(G) > k` has an induced subgraph on at
most `3k` vertices with `c₂ > k`. Hence every minimal forbidden induced subgraph for `c₂ ≤ k` has
at most `3k` vertices. -/
theorem theorem1 (G : SimpleGraph V) {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    (k < c2 G → ∃ s : Finset V, s.card ≤ 3 * k ∧ k < c2 (G.induce (s : Set V))) ∧
      (k < c2 G → (∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) →
        Fintype.card V ≤ 3 * k) :=
  ⟨fun hc => part54_e_witness G hk hk2 hc, fun hc hmin => cor5_even G hk hk2 hc hmin⟩

/-- **Theorem 2, first statement.** Let `k ≥ 2` be even. The tripling of any graph `G₀` on `k`
vertices whose adjacency matrix is non-singular over `F₂` is a minimal forbidden induced subgraph
for `c₂ ≤ k`, on `3k` vertices. (`tripling G₀` replaces each vertex `w` by three pairwise
non-adjacent vertices `(w, 0), (w, 1), (w, 2)`, and each edge by the nine edges between the two
triples.) -/
theorem theorem2_tripling {W : Type*} [Fintype W] [DecidableEq W] (G0 : SimpleGraph W)
    [DecidableRel G0.Adj] {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (hW : Fintype.card W = k)
    (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) :
    Fintype.card (W × Fin 3) = 3 * k ∧ k < c2 (tripling G0) ∧
      ∀ s : Finset (W × Fin 3), s ≠ univ →
        c2 ((tripling G0).induce (s : Set (W × Fin 3))) ≤ k :=
  part54_f G0 hk hk2 hW hdet

/-- **Theorem 2, second statement.** For even `k ≥ 4`, every minimal forbidden induced subgraph for
`c₂ ≤ k` on `3k` vertices is (isomorphic to) the tripling of a graph on `k` vertices whose
adjacency matrix is non-singular over `F₂`. -/
theorem theorem2_classification (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : Even k)
    (hk4 : 4 ≤ k) (hV : Fintype.card V = 3 * k) (hc : k < c2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) :
    ∃ (G0 : SimpleGraph (Fin k)) (_ : DecidableRel G0.Adj),
      (G0.adjMatrix (ZMod 2)).det ≠ 0 ∧ Nonempty (G ≃g tripling G0) :=
  part54_g G hk hk4 hV hc hmin

end Theorems

/-- **Theorem 2.** Let `k ≥ 2` be even. The tripling of any graph on `k` vertices whose adjacency
matrix is non-singular over `F₂` is a minimal forbidden induced subgraph for `c₂ ≤ k`, on `3k`
vertices. For `k ≥ 4`, every minimal forbidden induced subgraph for `c₂ ≤ k` on `3k` vertices is
such a tripling, up to isomorphism. (Graphs on finite types in `Type`; the two halves,
universe-polymorphic, are `theorem2_tripling` and `theorem2_classification`.) -/
theorem theorem2 {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (G0 : SimpleGraph W) [DecidableRel G0.Adj],
      Fintype.card W = k → (G0.adjMatrix (ZMod 2)).det ≠ 0 →
        Fintype.card (W × Fin 3) = 3 * k ∧ k < c2 (tripling G0) ∧
          ∀ s : Finset (W × Fin 3), s ≠ univ →
            c2 ((tripling G0).induce (s : Set (W × Fin 3))) ≤ k) ∧
    (4 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 3 * k → k < c2 G →
        (∀ s : Finset V, s ≠ univ → c2 (G.induce (s : Set V)) ≤ k) →
        ∃ (G0 : SimpleGraph (Fin k)) (_ : DecidableRel G0.Adj),
          (G0.adjMatrix (ZMod 2)).det ≠ 0 ∧ Nonempty (G ≃g tripling G0)) :=
  ⟨fun _ _ _ G0 _ hW hdet => theorem2_tripling G0 hk hk2 hW hdet,
    fun hk4 _ _ _ G _ hV hc hmin => theorem2_classification G hk hk4 hV hc hmin⟩

/-- The numbers of vertices of minimal forbidden induced subgraphs for `c₂ ≤ k` (graphs on finite
types in `Type`). -/
def minForbSizes (k : ℕ) : Set ℕ :=
  {m | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : SimpleGraph V),
    Fintype.card V = m ∧ k < c2 H ∧ ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k}

/-- **Corollary 3.** The largest number of vertices of a minimal forbidden induced subgraph for
`c₂ ≤ k` is `2k + 2` for odd `k` and `3k` for even `k ≥ 2`. -/
theorem corollary3 (k : ℕ) :
    (Odd k → IsGreatest (minForbSizes k) (2 * k + 2)) ∧
      (Even k → 2 ≤ k → IsGreatest (minForbSizes k) (3 * k)) := by
  refine ⟨fun hk => ⟨?_, ?_⟩, fun hk hk2 => part54_h_even hk hk2⟩
  · obtain ⟨h1, h2, h3⟩ := cor4_sharp k
    refine ⟨Fin (k + 1) × Bool, inferInstance, inferInstance, matchingGraph k, h1,
      lt_of_lt_of_le h2 (mrF2_le_c2 _), fun s hs => ?_⟩
    exact (c2_le_iff_mrF2_le_of_odd _ hk).2 (h3 s hs)
  · rintro m ⟨V, _, _, H, rfl, hc, hmin⟩
    exact cor5_odd H hk hc hmin

end FreeDiagonal.EvenComplementation.Paper

/-! ### Axioms -/
#print axioms FreeDiagonal.EvenComplementation.Paper.fact_a
#print axioms FreeDiagonal.EvenComplementation.Paper.fact_b
#print axioms FreeDiagonal.EvenComplementation.Paper.fact_c
#print axioms FreeDiagonal.EvenComplementation.Paper.fact_d
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma1
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma1_rigid
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma1_dichotomy
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma1_rigid_needs_one_le
#print axioms FreeDiagonal.EvenComplementation.Paper.formRankOn_eq_rank_gram
#print axioms FreeDiagonal.EvenComplementation.Paper.section2_factor
#print axioms FreeDiagonal.EvenComplementation.Paper.rho_eq
#print axioms FreeDiagonal.EvenComplementation.Paper.isBasisIn_Umat_iff
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma2
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma2_of_factor
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma2_remark
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma2_remark_of_factor
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma3
#print axioms FreeDiagonal.EvenComplementation.Paper.lemma3_exists
#print axioms FreeDiagonal.EvenComplementation.Paper.theorem1
#print axioms FreeDiagonal.EvenComplementation.Paper.theorem2
#print axioms FreeDiagonal.EvenComplementation.Paper.theorem2_tripling
#print axioms FreeDiagonal.EvenComplementation.Paper.theorem2_classification
#print axioms FreeDiagonal.EvenComplementation.Paper.corollary3
