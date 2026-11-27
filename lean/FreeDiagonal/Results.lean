import FreeDiagonal.Foundations.Rank
import FreeDiagonal.Foundations.Union
import FreeDiagonal.Witness.Basic
import FreeDiagonal.Witness.Threshold
import FreeDiagonal.Witness.Unconditional
import FreeDiagonal.Witness.Restricted
import FreeDiagonal.Graphs.MinRankF2
import FreeDiagonal.Graphs.Complementation
import FreeDiagonal.Graphs.EvenK
import FreeDiagonal.Closure.Threshold
import FreeDiagonal.Variety.Section5
import FreeDiagonal.Variety.Lemma3Easy
import FreeDiagonal.Variety.Theorem3
import FreeDiagonal.Variety.Theorem4
import FreeDiagonal.Variety.Elimination
import FreeDiagonal.Variety.Sharpness
import FreeDiagonal.Variety.Theorem6
import FreeDiagonal.Variety.Completeness
import FreeDiagonal.Variety.Example18

/-!
# Results: the statements of the two papers, under the names the READMEs give

This file proves nothing new. It states each result of the two papers and proves it by citing
the library theorem that carries the work.

* Paper 1: "The Sharp 2k+2 Obstruction Bound for Minimum-Rank Completion with a Free Diagonal"
  (names `note_*`, `frobenius`, `union_minmax`).
* Paper 2: "The Sharp 2k+2 Threshold for Set-Theoretic Finiteness in Algebraic Factor Analysis"
  (names `paper_*`).

Notation (definitions in `Witness/Basic.lean`, `Closure/Basic.lean`, `Variety/`):
* a pattern on `n` is a matrix `x : Matrix n n F` whose diagonal is ignored;
  `minCompRank x` = `c(x)`, the least rank of `x + diagonal d`;
  `subPattern x T` = `x_T`; `CutRankLE x j`: every cut rank `rank x[A, Aᶜ]` is at most `j`;
* `minCompRankR Ω x`: `c` with each diagonal entry `d_i` confined to `Ω i`;
* `mrF2 G`: minimum rank of the graph `G` over `F₂`; `c2 G`: subgraph complementation number;
* `closRank x` = `ρ(x) = min_D |D| + c(x on Dᶜ)`;
* `Dvar n k`, `Xvar n k`: `D_{n,k}`, `X_{n,k}`, the Zariski closures of the patterns, respectively
  symmetric patterns, with `c ≤ k`, as subsets of `K^{OffIdx n}` and `K^{SymIdx n}`;
* `FAideal ι m` = `I_{p,m}`, `sumIdeal ι m t` = `Σ_{|A| = t} I_{A,m}`, `Jideal ι` = `J_{p,3}`.

The only hypothesis beyond those displayed is `DSSExample18Q` (`Variety/Example18.lean`), an
explicit argument of the Theorem 6 statements.
-/

open Matrix Finset

universe u v

namespace FreeDiagonal.Results

/-! ## Paper 1: minimum-rank completion with a free diagonal -/

section Note

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- Paper 1, fact (a): `c(x_T) ≤ c(x)`. -/
theorem note_fact_a (x : Matrix n n F) (T : Finset n) :
    minCompRank (subPattern x T) ≤ minCompRank x :=
  minCompRank_subPattern_le x T

/-- Paper 1, fact (b): `c(x)` is at least every cut rank. -/
theorem note_fact_b (x : Matrix n n F) (A : Finset n) :
    (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank ≤ minCompRank x :=
  cutRank_le_minCompRank x A

/-- Paper 1, fact (c): adding one index raises `c` by at most 2. -/
theorem note_fact_c (x : Matrix n n F) (i : n) :
    minCompRank x ≤ minCompRank (subPattern x (univ.erase i)) + 2 :=
  minCompRank_le_erase_add_two x i

/-- Paper 1, Theorem 1 (witness theorem): for any completion `G = x + diag(d0)`, some `T` with
`|T| ≤ rank G + j` has `c(x_T) = c(x)`. -/
theorem note_theorem_2_any_completion (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j)
    (d0 : n → F) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRank (subPattern x T) = minCompRank x :=
  thm2_any_completion x j hcut d0

/-- Paper 1, Theorem 1 for an optimal completion: `|T| ≤ c(x) + j`. -/
theorem note_theorem_2 (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ minCompRank x + j ∧
      minCompRank (subPattern x T) = minCompRank x :=
  thm2_witness x j hcut

/-- Paper 1, Theorem 1, last assertion: `|T| ≤ 2c(x)`. -/
theorem note_theorem_2_two_mul (x : Matrix n n F) :
    ∃ T : Finset n, T.card ≤ 2 * minCompRank x ∧
      minCompRank (subPattern x T) = minCompRank x :=
  thm2_two_mul x

/-- Paper 1, Section 4, first remark: every completion of `x_T` is matched by a completion of
`x` of no larger rank (`G` on `X`, the given completion on `T \ X`). -/
theorem note_theorem_2_construction (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j)
    (d0 : n → F) :
    ∃ T X : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧ (∀ i, i ∉ X → i ∈ T) ∧
      ∀ (d : T → F) (e : n → F), (∀ i ∈ X, e i = d0 i) →
        (∀ i (h : i ∈ T), i ∉ X → e i = d ⟨i, h⟩) →
          (x + diagonal e).rank ≤ (subPattern x T + diagonal d).rank :=
  witness_core x j hcut d0

/-- Paper 1, Section 4, second remark (restricted diagonals): fact (a). -/
theorem note_remark_restricted_fact_a {Ω : n → Set F} (hΩ : ∀ i, (Ω i).Nonempty)
    (x : Matrix n n F) (T : Finset n) :
    minCompRankR (restrictΩ Ω T) (subPattern x T) ≤ minCompRankR Ω x :=
  minCompRankR_subPattern_le hΩ x T

/-- Paper 1, Section 4, second remark (restricted diagonals): fact (b), for any off-diagonal
block. -/
theorem note_remark_restricted_fact_b {Ω : n → Set F} (hΩ : ∀ i, (Ω i).Nonempty)
    {α β : Type*} [Fintype β] (x : Matrix n n F) (r : α → n) (c : β → n)
    (h : ∀ a b, r a ≠ c b) : (x.submatrix r c).rank ≤ minCompRankR Ω x :=
  offDiag_rank_le_minCompRankR hΩ x r c h

/-- Paper 1, Section 4, second remark (restricted diagonals): fact (c). -/
theorem note_remark_restricted_fact_c {Ω : n → Set F} (hΩ : ∀ i, (Ω i).Nonempty)
    (x : Matrix n n F) (i : n) :
    minCompRankR Ω x ≤
      minCompRankR (restrictΩ Ω (univ.erase i)) (subPattern x (univ.erase i)) + 2 :=
  minCompRankR_le_erase_add_two hΩ x i

/-- Paper 1, Section 4, second remark (restricted diagonals): Theorem 1 for an admissible `G`. -/
theorem note_remark_restricted_witness {Ω : n → Set F} (hΩ : ∀ i, (Ω i).Nonempty)
    (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) (d0 : n → F) (hd0 : Admissible Ω x d0) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRankR (restrictΩ Ω T) (subPattern x T) = minCompRankR Ω x :=
  witnessR hΩ x j hcut d0 hd0

/-- Paper 1, Section 4, second remark: the bound `n ≤ 2k + 2` of Theorem 2. -/
theorem note_remark_restricted_bound {Ω : n → Set F} (hΩ : ∀ i, (Ω i).Nonempty) (k : ℕ)
    (x : Matrix n n F) (hk : k + 1 ≤ minCompRankR Ω x)
    (hmin : ∀ T : Finset n, T ≠ univ → minCompRankR (restrictΩ Ω T) (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 :=
  card_le_of_minimalR hΩ k x hk hmin

/-- Paper 1, Theorem 2, minimal obstructions (any `k ≥ 0`). -/
theorem note_theorem_3_minimal (k : ℕ) (x : Matrix n n F) (hk : k + 1 ≤ minCompRank x)
    (hmin : ∀ T : Finset n, T ≠ univ → minCompRank (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 :=
  thm3_minimal k x hk hmin

/-- Paper 1, Theorem 2, the equivalence. -/
theorem note_theorem_3 (k : ℕ) (x : Matrix n n F) :
    minCompRank x ≤ k ↔
      ∀ T : Finset n, T.card ≤ 2 * k + 2 → minCompRank (subPattern x T) ≤ k :=
  thm3_threshold k x

end Note

section NoteSharp

variable (F : Type*) [Field F]

/-- Paper 1, Theorem 2, sharpness: the perfect matching on `2k + 2` indices. -/
theorem note_theorem_3_sharp (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      ¬ minCompRank (matching F k) ≤ k ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T ≠ univ →
        minCompRank (subPattern (matching F k) T) ≤ k) ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        minCompRank (subPattern (matching F k) T) ≤ k) :=
  threshold_sharp F k

end NoteSharp

section NoteGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Paper 1, Corollary 3: minimal forbidden induced subgraphs for `mr(F₂, ·) ≤ k` have at most
`2k + 2` vertices. -/
theorem note_corollary_4_minimal (G : SimpleGraph V) (k : ℕ) (hk : k + 1 ≤ mrF2 G)
    (hmin : ∀ s : Finset V, s ≠ univ → mrF2 (G.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 2 * k + 2 :=
  cor4_minimal G k hk hmin

/-- Paper 1, Corollary 3, threshold form. -/
theorem note_corollary_4_threshold (G : SimpleGraph V) (k : ℕ) :
    mrF2 G ≤ k ↔ ∀ s : Finset V, s.card ≤ 2 * k + 2 → mrF2 (G.induce (s : Set V)) ≤ k :=
  cor4_threshold G k

/-- Paper 1, Corollary 3: an induced subgraph on at most `2 mr` vertices with the same `mr`. -/
theorem note_corollary_4_witness (G : SimpleGraph V) :
    ∃ s : Finset V, s.card ≤ 2 * mrF2 G ∧ mrF2 (G.induce (s : Set V)) = mrF2 G :=
  cor4_witness G

/-- Paper 1, Corollary 3: `(k+1) K₂` attains the bound. -/
theorem note_corollary_4_sharp (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      k + 1 ≤ mrF2 (matchingGraph k) ∧
      ∀ s : Finset (Fin (k + 1) × Bool), s ≠ univ →
        mrF2 ((matchingGraph k).induce (s : Set (Fin (k + 1) × Bool))) ≤ k :=
  cor4_sharp k

/-- Paper 1, Section 6: `c₂` in matrix form, the least `s` with `adj(G) + D = B Bᵀ` over `F₂`. -/
theorem note_c2_matrix_form (G : SimpleGraph V) [DecidableRel G.Adj] :
    c2 G = sInf {s | ∃ (B : Matrix V (Fin s) (ZMod 2)) (d : V → ZMod 2),
      G.adjMatrix (ZMod 2) + diagonal d = B * Bᵀ} :=
  c2_eq_matrix_form G

/-- Paper 1, Section 6: `mr(F₂, G) ≤ c₂(G) ≤ mr(F₂, G) + 1`. -/
theorem note_mr_le_c2_le_mr_add_one (G : SimpleGraph V) :
    mrF2 G ≤ c2 G ∧ c2 G ≤ mrF2 G + 1 :=
  ⟨mrF2_le_c2 G, c2_le_mrF2_add_one G⟩

/-- Paper 1, Section 6: for `mr ≥ 1`, `c₂ = mr + 1` exactly when every minimum-rank completion has
zero diagonal. -/
theorem note_c2_eq_mr_add_one_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hpos : 0 < mrF2 G) :
    c2 G = mrF2 G + 1 ↔
      ∀ d : V → ZMod 2, (G.adjMatrix (ZMod 2) + diagonal d).rank = mrF2 G → d = 0 :=
  c2_eq_mrF2_add_one_iff G hpos

/-- Paper 1, Section 6: for odd `k`, `c₂ ≤ k ↔ mr(F₂, ·) ≤ k`. -/
theorem note_odd_classes_coincide (G : SimpleGraph V) {k : ℕ} (hk : Odd k) :
    c2 G ≤ k ↔ mrF2 G ≤ k :=
  c2_le_iff_mrF2_le_of_odd G hk

/-- Paper 1, Theorem 4 (1), first sentence. -/
theorem note_corollary_5 (H : SimpleGraph V) (k : ℕ) (hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k)
    (hmr : k + 1 ≤ mrF2 H) : Fintype.card V ≤ 2 * k + 2 :=
  cor5 H k hc hmin hmr

/-- Paper 1, Theorem 4 (1), second sentence: for odd `k` the conjecture of [BPR22] holds. -/
theorem note_corollary_5_odd (H : SimpleGraph V) {k : ℕ} (hk : Odd k) (hc : k + 1 ≤ c2 H)
    (hmin : ∀ s : Finset V, s ≠ univ → c2 (H.induce (s : Set V)) ≤ k) :
    Fintype.card V ≤ 2 * k + 2 :=
  cor5_odd H hk hc hmin

end NoteGraphs

/-- Paper 1, Theorem 4 (2): for `k = 2m`, `m ≥ 2`, `m K₃,₃` is a minimal forbidden induced
subgraph for `c₂ ≤ k` on `3k > 2k + 2` vertices. -/
theorem note_remark_even_k {m : ℕ} (hm : 2 ≤ m) :
    Fintype.card (Fin 6 × Fin m) = 3 * (2 * m) ∧ 2 * (2 * m) + 2 < 3 * (2 * m) ∧
      c2 (EvenK.mK33 m) = 2 * m + 1 ∧ mrF2 (EvenK.mK33 m) = 2 * m ∧
      (∀ s : Finset (Fin 6 × Fin m), s ≠ univ →
        c2 ((EvenK.mK33 m).induce (s : Set (Fin 6 × Fin m))) ≤ 2 * m) :=
  EvenK.even_k_remark hm

/-- Paper 1, Lemma 1, in the Frobenius form: with `P`, `Q` the row and column selections of
`A` and `C`, it reads `rank G[A, E] + rank G[E, C] ≤ rank G + rank G[A, C]`. -/
theorem frobenius {F : Type*} [Field F] {a m k c : Type*} [Fintype m] [Fintype k] [Fintype c]
    (P : Matrix a m F) (G : Matrix m k F) (Q : Matrix k c F) :
    (P * G).rank + (G * Q).rank ≤ G.rank + (P * G * Q).rank :=
  rank_frobenius P G Q

/-- Paper 1, Section 4: the min-max inequality of the matroid union theorem, for any two
submodular integer-valued functions. -/
theorem union_minmax {ι : Type*} [DecidableEq ι] (S : Finset ι) (r1 r2 : Finset ι → ℤ)
    (h1 : Submod r1) (h2 : Submod r2) :
    ∃ A ⊆ S, ∃ X ⊆ S, ((S \ X).card : ℤ) + r1 X + r2 X ≤ r1 A + r2 (S \ A) :=
  union_minmax_submodular S r1 r2 h1 h2

/-! ## Paper 2: the factor-analysis threshold

A dial setting is `d : n → Option F` (`none` = `∞`); `cost(G, d)` is `rank (dialMat G d)`
(`Variety/Section5.lean`). A completion of `x` is any `G` with `G i j = x i j` for `i ≠ j`. -/

section Paper

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- Paper 2, fact (a): `ρ(x_T) ≤ ρ(x)`. -/
theorem paper_fact_a (x : Matrix n n F) (T : Finset n) :
    closRank (subPattern x T) ≤ closRank x :=
  closRank_subPattern_le x T

/-- Paper 2, fact (b): every cut rank is at most `ρ(x)`. -/
theorem paper_fact_b (x : Matrix n n F) (A : Finset n) :
    (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank ≤ closRank x :=
  cutRank_le_closRank x A

/-- Paper 2, fact (c): `ρ(x) ≤ ρ(x_{E ∖ {v}}) + 1`. -/
theorem paper_fact_c (x : Matrix n n F) (v : n) :
    closRank x ≤ closRank (subPattern x (univ.erase v)) + 1 :=
  closRank_le_erase_add_one x v

/-- Paper 2, fact (d): `ρ(x) ≤ c(x)`. -/
theorem paper_fact_d (x : Matrix n n F) : closRank x ≤ minCompRank x :=
  closRank_le_minCompRank x

/-- Paper 2, Section 1, definition of cost: `cost(G, d) = |N(d)| + rank G_d`,
`G_d = (G - diag(d))[S(d), S(d)]`, agrees with `rank (dialMat G d)`. -/
theorem paper_v4_cost_def (G : Matrix n n F) (d : n → Option F) (N : Finset n)
    (hN : ∀ i, d i = none ↔ i ∈ N) :
    (dialMat G d).rank = N.card +
      ((G - diagonal (fun i => (d i).getD 0)).submatrix (fun a : ↥(Nᶜ) => (a : n))
        (fun a : ↥(Nᶜ) => (a : n))).rank :=
  formula_1 G d N hN

/-- Paper 2, formula (1), and `ρ(x) = min_d cost(G, d)`, for every completion `G` of `x`. -/
theorem paper_v4_formula_1 (x G : Matrix n n F) (hG : ∀ i j, i ≠ j → G i j = x i j)
    (T : Finset n) :
    closRank x = (⨅ d : n → Option F, (dialMat G d).rank) ∧
    closRank (subPattern x T) + (univ \ T).card =
      ⨅ d : {d : n → Option F // ∀ i ∉ T, d i = none}, (dialMat G d.1).rank :=
  ⟨formula_2_global x G hG, formula_2_sub x G hG T⟩

/-- Paper 2, Lemma 2 (pivot): for `G[D, D]` invertible, with `G' = pivot G D` and
`d' = pivDial D d`: `d ↦ d'` is an involution, (i) `cost(G', d') = cost(G, d)`,
(ii) `rank G'[E ∖ A, A] = rank G[E ∖ A, A]`, (iii) `G'[D, D]` is invertible. -/
theorem paper_lemma_2 (G : Matrix n n F) (D : Finset n)
    (hD : IsUnit (G.submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).det) :
    (∀ d : n → Option F, pivDial D (pivDial D d) = d) ∧
    (∀ d : n → Option F, (dialMat (pivot G D) (pivDial D d)).rank = (dialMat G d).rank) ∧
    (∀ A : Finset n,
      ((pivot G D).submatrix (fun b : ↥(Aᶜ) => (b : n)) (fun a : A => (a : n))).rank =
        (G.submatrix (fun b : ↥(Aᶜ) => (b : n)) (fun a : A => (a : n))).rank) ∧
    IsUnit ((pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).det :=
  lemma_2_invertible G D hD

/-- Paper 2, Lemma 2, the map `d ↦ d'`: on `D` it exchanges `∞` and `0` and sends `t` to `1/t`;
off `D` it is the identity. -/
theorem paper_lemma_2_dial (D : Finset n) (d : n → Option F) (i : n) (t : F) (ht : t ≠ 0) :
    (i ∉ D → pivDial D d i = d i) ∧
    (flip (none : Option F) = some 0 ∧ flip (some (0 : F)) = none ∧ flip (some t) = some t⁻¹) ∧
    (i ∈ D → pivDial D d i = flip (d i)) := by
  refine ⟨fun h => by simp [pivDial, h], flip_values t ht, fun h => by simp [pivDial, h]⟩

/-- Paper 2, Theorem 1 (witness theorem): if all cut ranks are at most `j`, some `T` with
`|T| ≤ ρ(x) + j` has `ρ(x_T) = ρ(x)`. Any field, symmetric or not. -/
theorem paper_theorem_1 (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ closRank x + j ∧ closRank (subPattern x T) = closRank x :=
  closure_witness x j hcut

/-- Paper 2, Theorem 1, last sentence: `|T| ≤ 2ρ(x)`. -/
theorem paper_theorem_1_two_rho (x : Matrix n n F) :
    ∃ T : Finset n, T.card ≤ 2 * closRank x ∧ closRank (subPattern x T) = closRank x :=
  theorem_1_two_rho x

/-- Paper 2, Theorem 2, first sentence: minimal obstructions have at most `2k + 2` indices. -/
theorem paper_theorem_2_minimal (k : ℕ) (x : Matrix n n F) (hk : k + 1 ≤ closRank x)
    (hmin : ∀ T : Finset n, T ≠ univ → closRank (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 :=
  closure_card_le_of_minimal k x hk hmin

/-- Paper 2, Theorem 2, the equivalence. -/
theorem paper_theorem_2 (x : Matrix n n F) (k : ℕ) :
    closRank x ≤ k ↔ ∀ T : Finset n, T.card ≤ 2 * k + 2 → closRank (subPattern x T) ≤ k :=
  closure_threshold x k

end Paper

/-- Paper 2, Theorem 2, sharpness: the perfect matching on `2k + 2` indices. -/
theorem paper_theorem_2_sharp (F : Type*) [Field F] (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      ¬ closRank (matching F k) ≤ k ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T ≠ univ →
        closRank (subPattern (matching F k) T) ≤ k) ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        closRank (subPattern (matching F k) T) ≤ k) :=
  closure_threshold_sharp F k

/-- Paper 2, proof of Lemma 1: the completeness of `(ℙ¹)ⁿ`, in the form `ProjClosed K`
(`Variety/Elimination.lean`), for every algebraically closed `K`. -/
theorem paper_v4_projClosed (K : Type u) [Field K] [IsAlgClosed K] : ProjClosed K :=
  projClosed_of_isAlgClosed K

section PaperAlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Paper 2, Lemma 1, general patterns: `D_{n,k} = {x : ρ(x) ≤ k}`. -/
theorem paper_v4_lemma_1 (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Dvar n k = {p : OffIdx n → K | closRank (toMat p) ≤ k} :=
  Dvar_eq (closedRho_of_projClosed (projClosed_of_isAlgClosed K)) n k

/-- Paper 2, Lemma 1, symmetric patterns: `X_{n,k} = {x symmetric : ρ(x) ≤ k}`. -/
theorem paper_v4_lemma_1_sym (n : Type) [Fintype n] [LinearOrder n] (k : ℕ) :
    Xvar n k = {p : SymIdx n → K | closRank (toMatSym p) ≤ k} :=
  Xvar_eq (closedRhoSym_of_projClosed (projClosed_of_isAlgClosed K)) n k

/-- Paper 2, Theorem 3, symmetric patterns (`n ≥ 2k + 2`). -/
theorem paper_v4_theorem_3_sym {n : Type} [Fintype n] [LinearOrder n]
    (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) (p : SymIdx n → K) :
    p ∈ Xvar n k ↔ ∀ T : Finset n, T.card = 2 * k + 2 → restrictSym p T ∈ Xvar T k :=
  theorem_3_sym (closedRhoSym_of_projClosed (projClosed_of_isAlgClosed K)) k hn p

/-- Paper 2, Theorem 3, arbitrary patterns (`n ≥ 2k + 2`). -/
theorem paper_v4_theorem_3 {n : Type} [Fintype n] [DecidableEq n]
    (k : ℕ) (hn : 2 * k + 2 ≤ Fintype.card n) (p : OffIdx n → K) :
    p ∈ Dvar n k ↔ ∀ T : Finset n, T.card = 2 * k + 2 → restrictOff p T ∈ Dvar T k :=
  theorem_3 (closedRho_of_projClosed (projClosed_of_isAlgClosed K)) k hn p

/-- Paper 2, Corollary 5, symmetric patterns (`n ≥ 2k + 1`). -/
theorem paper_v4_corollary_5_sym {n : Type} [Fintype n] [LinearOrder n]
    (k : ℕ) (hn : 2 * k + 1 ≤ Fintype.card n) (p : SymIdx n → K) :
    p ∈ Xvar n k ↔ MinorsVanish (toMatSym p) k ∧
      ∀ T : Finset n, T.card = 2 * k + 1 → restrictSym p T ∈ Xvar T k :=
  corollary_5_sym (closedRhoSym_of_projClosed (projClosed_of_isAlgClosed K)) k hn p

/-- Paper 2, Corollary 5, arbitrary patterns (`n ≥ 2k + 1`). -/
theorem paper_v4_corollary_5 {n : Type} [Fintype n] [DecidableEq n]
    (k : ℕ) (hn : 2 * k + 1 ≤ Fintype.card n) (p : OffIdx n → K) :
    p ∈ Dvar n k ↔ MinorsVanish (toMat p) k ∧
      ∀ T : Finset n, T.card = 2 * k + 1 → restrictOff p T ∈ Dvar T k :=
  corollary_5 (closedRho_of_projClosed (projClosed_of_isAlgClosed K)) k hn p

end PaperAlgClosed

section PaperInfinite

variable {K : Type u} [Field K] [Infinite K]

/-- Paper 2, Theorem 3, sharpness, symmetric patterns: for every `n ≥ 2k + 2` there is a symmetric
pattern outside `X_{n,k}` whose sub-patterns on at most `2k + 1` indices lie in their varieties;
so for no `N ≤ 2k + 1` do the sub-patterns on `N` indices decide membership. -/
theorem paper_theorem_3_sym_sharp_every_n {n : Type v} [Fintype n] [LinearOrder n] (k : ℕ)
    (hn : 2 * k + 2 ≤ Fintype.card n) :
    (∃ p : SymIdx n → K, p ∉ Xvar n k ∧
      ∀ T : Finset n, T.card ≤ 2 * k + 1 → restrictSym p T ∈ Xvar T k) ∧
    ∀ N ≤ 2 * k + 1, ¬ ∀ p : SymIdx n → K,
      (∀ T : Finset n, T.card = N → restrictSym p T ∈ Xvar T k) → p ∈ Xvar n k :=
  ⟨theorem_3_sym_sharp_every_n k hn, fun N hN => theorem_3_sym_not_smaller_every_n k N hn hN⟩

/-- Paper 2, Theorem 3, sharpness, arbitrary patterns, every `n ≥ 2k + 2`. -/
theorem paper_theorem_3_sharp_every_n {n : Type v} [Fintype n] [DecidableEq n] (k : ℕ)
    (hn : 2 * k + 2 ≤ Fintype.card n) :
    (∃ p : OffIdx n → K, p ∉ Dvar n k ∧
      ∀ T : Finset n, T.card ≤ 2 * k + 1 → restrictOff p T ∈ Dvar T k) ∧
    ∀ N ≤ 2 * k + 1, ¬ ∀ p : OffIdx n → K,
      (∀ T : Finset n, T.card = N → restrictOff p T ∈ Dvar T k) → p ∈ Dvar n k :=
  ⟨theorem_3_sharp_every_n k hn, fun N hN => theorem_3_not_smaller_every_n k N hn hN⟩

/-- Paper 2, remark after Corollary 5: `X_{3,1}` is the whole space. -/
theorem paper_v4_X31 : Xvar (K := K) (Fin 3) 1 = Set.univ :=
  Xvar_fin3_one

end PaperInfinite

/-- Paper 2, Section 1: in characteristic other than 2, `X_{n,k}` is the closure of the patterns of
`Λ Λᵀ`, `Λ ∈ K^{n × k}` (`K` algebraically closed). -/
theorem paper_Xvar_LambdaLambdaT {K : Type u} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    {ι : Type} [Fintype ι] [LinearOrder ι] (k : ℕ) :
    Xvar (K := K) ι k =
      zariskiClosure (Set.range (fun Λ : Matrix ι (Fin k) K => symCoords (Λ * Λᵀ))) :=
  Xvar_eq_closure_factors h2 k

/-- Paper 2, Theorem 4: for every `m` and every `p ≥ 2m + 2`, `I_{p,m}` and
`Σ_{|A| = 2m+2} I_{A,m}` have the same radical. -/
theorem paper_v4_theorem_4 (m p : ℕ) (hp : 2 * m + 2 ≤ p) :
    (FAideal (Fin p) m).radical = (sumIdeal (Fin p) m (2 * m + 2)).radical :=
  theorem_4 (closedRhoSym_of_projClosed (projClosed_of_isAlgClosed ℂ)) m p hp

/-- Paper 2, Theorem 4, sharpness: for every `t ≤ 2m + 1` the radicals of `I_{2m+2,m}` and
`Σ_{|A| = t} I_{A,m}` differ. -/
theorem paper_v4_theorem_4_sharp (m t : ℕ) (ht : t ≤ 2 * m + 1) :
    (FAideal (Fin (2 * m + 2)) m).radical ≠ (sumIdeal (Fin (2 * m + 2)) m t).radical :=
  theorem_4_sharp_noHyp m t ht

/-- Paper 2, Section 3: the off-diagonal `4 × 4` minors and the septads lie in `I_{p,3}`. -/
theorem paper_theorem_6_J_le_I (ι : Type) [Fintype ι] [LinearOrder ι] :
    Jideal ι ≤ FAideal ι 3 :=
  Jideal_le_FAideal

/-- Paper 2, Theorem 6 (Conjecture 28 of [DSS07]), under the hypothesis `DSSExample18Q`: for every
`p`, the radical of `J_{p,3}` is `I_{p,3}`. -/
theorem paper_v4_theorem_6_Q (hQ : DSSExample18Q) (p : ℕ) :
    (Jideal (Fin p)).radical = FAideal (Fin p) 3 :=
  theorem_6 (projClosed_of_isAlgClosed ℂ) (dssExample18_of_Q hQ) p

/-- Paper 2, Theorem 6, variety form, under `DSSExample18Q`: the complex variety of `J_{p,3}` is
`X_{p,3}`. -/
theorem paper_v4_theorem_6_variety_Q (hQ : DSSExample18Q) (p : ℕ) :
    MvPolynomial.zeroLocus ℂ (Jideal (Fin p)) = Xvar (K := ℂ) (Fin p) 3 := by
  rw [← zeroLocus_FAideal, ← theorem_6 (projClosed_of_isAlgClosed ℂ) (dssExample18_of_Q hQ) p,
    zeroLocus_radical]

/-- The hypothesis, from the printed output of [DSS07, Example 18]: a generating set of the
elimination ideal each member of which lies in `J_{8,3}` or has its square there gives
`DSSExample18Q`. -/
theorem paper_v4_example18_of_generators (G : Set (MvPolynomial (SymIdx (Fin 8)) ℚ))
    (hG : Ideal.span G = Eideal (Fin 8) ℚ)
    (h : ∀ g ∈ G, g ∈ JidealQ (Fin 8) ℚ ∨ g ^ 2 ∈ JidealQ (Fin 8) ℚ) : DSSExample18Q :=
  dssExample18Q_of_generators G hG h

/-- The hypothesis is not vacuous: the elimination ideal contains a non-zero polynomial (an
off-diagonal `4 × 4` minor), and `rad J_{8,3}` over `ℚ` is not the whole ring. -/
theorem paper_v4_example18_nonvacuous :
    minor0123 ∈ Eideal (Fin 8) ℚ ∧ minor0123 ≠ 0 ∧ (JidealQ (Fin 8) ℚ).radical ≠ ⊤ :=
  dssExample18Q_nonvacuous

end FreeDiagonal.Results
