import FreeDiagonal.StatisticalFactorAnalysis.Theorem3

/-!
# The sharp quadratic threshold for finiteness in statistical factor analysis

Every numbered statement of the paper *The Sharp Quadratic Threshold for Finiteness in
Statistical Factor Analysis*, under names that follow the paper's numbering, together with the
unnumbered claims that carry weight.

* Section 1: the model `InModel m Σ` (`Σ = diag(D) + Λ Λᵀ`, `D > 0`, `Λ` real `n × m`, as in
  Drton and Xiao) and the weak model `InWeakModel m Σ` (`D ≥ 0`); fits, references, test sizes
  (`IsFit`, `IsReference`, `IsTestSize`, and the weak versions, in `Model.lean`);
  `setting_fit`, `setting_weakFit` (`Σ ∈ F` iff `Σ` has a fit); `lemma1`, `lemma1_weak`.
* Section 2: `theorem1`, `theorem2` (with `theorem2_weak` for the weak model), `theorem3`,
  `theorem4`.
* Section 3: `lemma2`; the remark after the proof of Theorem 2: `remark_theorem2` (true part)
  and `remark_theorem2_last_fails` (the last sentence of Theorem 2 does not carry over).
* Section 4: `lemma3` (all four assertions and `s_j, g_j > 0`).
* Section 6: `section6_ineq` (`q(m+3-q) > 2m+2` iff `3 ≤ q ≤ m`), `section6_gap`
  (`⌊(m+3)²/4⌋ - 2(m+1) = ⌊(m-1)²/4⌋`).

Conventions. The variables are `Fin N` (the paper's `E = {1, …, n}`), or `Fin q × Fin t`
(group, member) for replicated matrices. `subPattern Σ T` is the principal submatrix `Σ_T`.
"`q` is the least rank of a reference" is `IsLeast {r | ∃ G, IsReference Σ G ∧ G.rank = r} q`,
which includes that a reference exists. `⌊(m+3)²/4⌋` is the natural-number quotient
`(m + 3) ^ 2 / 4`. In Lemma 3, `IsLemma3Matrix S0` is the paper's list of hypotheses on `S0`
(symmetric, invertible, not positive semidefinite, principal submatrices of size `q - 1`
positive definite); `S0 j j` is `s_j` and `schurG S0 j` is `g_j`, with
`-g_j = s_j - r_jᵀ S0[-j]⁻¹ r_j` the Schur complement; `IsReplicated S0 Σ` says `Σ` is symmetric
with `Σ_il = (S0)_{jk}` for `i ≠ l` in groups `j, k`; `Cond1 S0 Σ` is condition (1).
"After multiplying each variable by a non-zero real number" is read as: there is `p` with all
`p_i ≠ 0` such that `(p_i Σ_il p_l)`, with its variables relabelled by an explicit bijection
`E ≃ Fin q × Fin t`, is replicated.
-/

open Matrix Module Submodule Finset

namespace FreeDiagonal.StatisticalFactorAnalysis.Paper

open FreeDiagonal FreeDiagonal.StatisticalFactorAnalysis

/-! ## Section 1 -/

/-- **Section 1.** `Σ ∈ F_{n,m}` if and only if `Σ` has a fit: a positive semidefinite `G` of
rank at most `m` with `G_ij = Σ_ij` for `i ≠ j` and `G_ii < Σ_ii`. -/
theorem setting_fit {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ) (Sig : Matrix n n ℝ) :
    InModel m Sig ↔ ∃ G, IsFit m Sig G :=
  inModel_iff_exists_fit m Sig

/-- **Section 1, weak model.** `Σ ∈ F̄_{n,m}` iff `Σ` has a weak fit (`G_ii ≤ Σ_ii`). -/
theorem setting_weakFit {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ) (Sig : Matrix n n ℝ) :
    InWeakModel m Sig ↔ ∃ G, IsWeakFit m Sig G :=
  inWeakModel_iff_exists_weakFit m Sig

/-- **Lemma 1 (references).** If for every `T ⊆ E` with `|T| ≤ 2m + 2` the matrix `Σ_T` has a
reference of rank at most `m`, then `Σ` has a reference of rank at most `m`. -/
theorem lemma1 {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      ∃ G, IsReference (subPattern Sig T) G ∧ G.rank ≤ m) :
    ∃ G, IsReference Sig G ∧ G.rank ≤ m :=
  StatisticalFactorAnalysis.lemma1 m Sig h

/-- **Lemma 1, weak form** (references with `0 ≤ G_ii ≤ Σ_ii`). -/
theorem lemma1_weak {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      ∃ G, IsWeakReference (subPattern Sig T) G ∧ G.rank ≤ m) :
    ∃ G, IsWeakReference Sig G ∧ G.rank ≤ m :=
  StatisticalFactorAnalysis.lemma1_weak m Sig h

/-! ## Section 2 -/

/-- **Theorem 1 (exact test size).** For every `m ≥ 0`, `b_m = b̄_m = ⌊(m+3)²/4⌋`: this number is
a test size for the model and for the weak model, and no smaller number is. -/
theorem theorem1 (m : ℕ) :
    IsLeast {b | IsTestSize m b} ((m + 3) ^ 2 / 4) ∧
      IsLeast {b | IsWeakTestSize m b} ((m + 3) ^ 2 / 4) :=
  StatisticalFactorAnalysis.theorem1 m

/-- **Theorem 2 (test size by reference rank).** Let `Σ` have a reference and let `q` be the
least rank of a reference. If `q > m`, then `Σ_T ∉ F_{|T|,m}` for some `T` with `|T| ≤ 2m + 2`.
If `q ≤ 1`, then `Σ ∈ F_{n,m}` for every `m ≥ q`. If `2 ≤ q ≤ m`, there is a set `T` of at most
`q (m + 3 - q)` variables with `Σ ∈ F_{n,m} ↔ Σ_T ∈ F_{|T|,m}`. For every `2 ≤ q ≤ m` the
number `q (m + 3 - q)` cannot be lowered: some positive definite `Σ` on `q (m + 3 - q)`
variables with least reference rank `q` is not in the model, while all its proper principal
submatrices are (it is not even in the weak model). -/
theorem theorem2 (m : ℕ) :
    (∀ (N : ℕ) (Sig : Matrix (Fin N) (Fin N) ℝ) (q : ℕ),
      IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q →
      (m < q → ∃ T : Finset (Fin N), T.card ≤ 2 * m + 2 ∧ ¬ InModel m (subPattern Sig T)) ∧
      (q ≤ 1 → ∀ m', q ≤ m' → InModel m' Sig) ∧
      (2 ≤ q → q ≤ m → ∃ T : Finset (Fin N), T.card ≤ q * (m + 3 - q) ∧
        (InModel m Sig ↔ InModel m (subPattern Sig T)))) ∧
    (∀ q : ℕ, 2 ≤ q → q ≤ m →
      ∃ Sig : Matrix (Fin q × Fin (m + 3 - q)) (Fin q × Fin (m + 3 - q)) ℝ,
        Fintype.card (Fin q × Fin (m + 3 - q)) = q * (m + 3 - q) ∧ Sig.PosDef ∧
        IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q ∧
        ¬ InWeakModel m Sig ∧ ¬ InModel m Sig ∧
        ∀ T : Finset (Fin q × Fin (m + 3 - q)), T ≠ univ → InModel m (subPattern Sig T)) :=
  ⟨fun _ Sig q hq => theorem2_first m Sig q hq, fun q hq hqm => theorem2_last m q hq hqm⟩

/-- **Theorem 2, first three statements, weak model** (weak references and `F̄`). -/
theorem theorem2_weak (m : ℕ) (N : ℕ) (Sig : Matrix (Fin N) (Fin N) ℝ) (q : ℕ)
    (hq : IsLeast {r | ∃ G, IsWeakReference Sig G ∧ G.rank = r} q) :
    (m < q → ∃ T : Finset (Fin N), T.card ≤ 2 * m + 2 ∧ ¬ InWeakModel m (subPattern Sig T)) ∧
    (q ≤ 1 → ∀ m', q ≤ m' → InWeakModel m' Sig) ∧
    (2 ≤ q → q ≤ m → ∃ T : Finset (Fin N), T.card ≤ q * (m + 3 - q) ∧
      (InWeakModel m Sig ↔ InWeakModel m (subPattern Sig T))) :=
  theorem2_first_weak m Sig q hq

/-- **Theorem 3 (extremal matrices).** Let `m ≥ 3` and `N = ⌊(m+3)²/4⌋`. If `Σ` is a positive
definite `N × N` matrix not in `F_{N,m}`, all of whose proper principal submatrices are in the
model, then after multiplying each variable by a non-zero real number (and relabelling the
variables as `q` groups of `t`) `Σ` is a replicated matrix of Lemma 3 satisfying condition (1),
with `q + t = m + 3` and `q t = N`. Conversely every positive definite replicated matrix with
such `q, t` satisfying (1) is positive definite on `N` variables, not in the model, and has all
its proper principal submatrices in the model. (Positive definiteness is not used in the first
direction: see `theorem3_forward`.) -/
theorem theorem3 (m : ℕ) (hm : 3 ≤ m) :
    (∀ Sig : Matrix (Fin ((m + 3) ^ 2 / 4)) (Fin ((m + 3) ^ 2 / 4)) ℝ, Sig.PosDef →
      ¬ InModel m Sig → (∀ T : Finset (Fin ((m + 3) ^ 2 / 4)), T ≠ univ →
        InModel m (subPattern Sig T)) →
      ∃ q t : ℕ, q + t = m + 3 ∧ q * t = (m + 3) ^ 2 / 4 ∧
        ∃ (e : Fin ((m + 3) ^ 2 / 4) ≃ Fin q × Fin t) (p : Fin ((m + 3) ^ 2 / 4) → ℝ),
          (∀ i, p i ≠ 0) ∧ ∃ S0 : Matrix (Fin q) (Fin q) ℝ, IsLemma3Matrix S0 ∧
            IsReplicated S0 ((diagonal p * Sig * diagonal p).submatrix e.symm e.symm) ∧
            Cond1 S0 ((diagonal p * Sig * diagonal p).submatrix e.symm e.symm)) ∧
    (∀ q t : ℕ, q + t = m + 3 → q * t = (m + 3) ^ 2 / 4 →
      ∀ S0 : Matrix (Fin q) (Fin q) ℝ, IsLemma3Matrix S0 →
      ∀ Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ, Sig.PosDef →
        IsReplicated S0 Sig → Cond1 S0 Sig →
        Fintype.card (Fin q × Fin t) = (m + 3) ^ 2 / 4 ∧ Sig.PosDef ∧ ¬ InModel m Sig ∧
          ∀ T : Finset (Fin q × Fin t), T ≠ univ → InModel m (subPattern Sig T)) := by
  refine ⟨fun Sig _ hnot hprop => ?_, fun q t hqt hN S0 hS0 Sig hpd hR hC => ?_⟩
  · obtain ⟨q, t, -, -, hqt, hN, rest⟩ :=
      theorem3_forward m hm Sig (Fintype.card_fin _) hnot hprop
    exact ⟨q, t, hqt, hN, rest⟩
  · obtain ⟨ht3, hq3⟩ := three_le_of_balanced m q t hm hqt hN
    obtain ⟨-, hn, hp⟩ := theorem3_converse (by omega : 2 ≤ q) (by omega : 2 ≤ t) m hqt hS0 hR hC
    exact ⟨by simp [hN], hpd, hn, hp⟩

/-- **Theorem 4 (positive correlations).** Let `m ≥ 1`, `N = ⌊(m+3)²/4⌋` and `0 ≤ ϱ ≤ 1`. For
every `ε > 0` there is a rational correlation matrix `C` (symmetric, unit diagonal, positive
definite) with all entries positive, within `ε` in every entry of the matrix with diagonal `1`
and all off-diagonal entries `ϱ`, which is not in `F̄_{N,m}` while all its proper principal
submatrices are in `F_{·,m}`. -/
theorem theorem4 (m : ℕ) (hm : 1 ≤ m) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Matrix (Fin ((m + 3) ^ 2 / 4)) (Fin ((m + 3) ^ 2 / 4)) ℚ, C.IsSymm ∧
      (∀ i, C i i = 1) ∧ (∀ i l, 0 < C i l) ∧ (C.map (fun x : ℚ => (x : ℝ))).PosDef ∧
      (∀ i l, |(C i l : ℝ) - (if i = l then 1 else ρ)| < ε) ∧
      ¬ InWeakModel m (C.map (fun x : ℚ => (x : ℝ))) ∧
      ∀ T : Finset (Fin ((m + 3) ^ 2 / 4)), T ≠ univ →
        InModel m (subPattern (C.map (fun x : ℚ => (x : ℝ))) T) :=
  theorem4_fin m hm ρ hρ0 hρ1 ε hε

/-! ## Section 3 -/

/-- **Lemma 2 (positivity).** Let `Φ` be a symmetric bilinear form of rank `r` on a real vector
space `V` (rank: dimension of the range of `v ↦ Φ(v, ·)`), and `W_1, …, W_t`, `t ≥ 2`, linear
maps from `V` to a Euclidean space of dimension `m'` with `⟨W_a v, W_b w⟩ = Φ(v, w)` for all
`v, w` and `a ≠ b`. If `t ≥ m' - r + 3` (written `m' + 3 ≤ t + r`), `Φ` is positive
semidefinite. -/
theorem lemma2 {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hΦ : ∀ v w, Φ v w = Φ w v) {m' r t : ℕ}
    (hE : finrank ℝ E = m') (hr : finrank ℝ (LinearMap.range Φ) = r)
    (W : Fin t → V →ₗ[ℝ] E) (ht2 : 2 ≤ t)
    (hW : ∀ a b, a ≠ b → ∀ v w, inner ℝ (W a v) (W b w) = Φ v w)
    (ht : m' + 3 ≤ t + r) :
    ∀ v, 0 ≤ Φ v v :=
  StatisticalFactorAnalysis.lemma2 Φ hΦ hE hr W ht2 hW ht

/-- **Remark after the proof of Theorem 2, the part that holds.** For arbitrary sets
`A_i ⊆ [0, ∞)` (non-emptiness is not needed), the first three statements of Theorem 2 and the
upper bound of Theorem 1 hold for positive semidefinite completions of rank `≤ m` with diagonal
entries in the `A_i` (`HasFitIn m A Σ`), with `q` the least rank of a symmetric completion with
diagonal in the `A_i`. -/
theorem remark_theorem2 {n : Type*} [Fintype n] [DecidableEq n] (A : n → Set ℝ)
    (hA : ∀ i, A i ⊆ Set.Ici 0) (m : ℕ) (Sig : Matrix n n ℝ) :
    (∀ q : ℕ, IsLeast {r | ∃ G, IsCompletionIn A Sig G ∧ G.rank = r} q →
      (m < q → ∃ T : Finset n, T.card ≤ 2 * m + 2 ∧
          ¬ HasFitIn m (fun a : T => A a) (subPattern Sig T)) ∧
      (q ≤ 1 → ∀ m', q ≤ m' → HasFitIn m' A Sig) ∧
      (2 ≤ q → q ≤ m → ∃ T : Finset n, T.card ≤ q * (m + 3 - q) ∧
        (HasFitIn m A Sig ↔ HasFitIn m (fun a : T => A a) (subPattern Sig T)))) ∧
    ((∀ T : Finset n, T.card ≤ (m + 3) ^ 2 / 4 →
      HasFitIn m (fun a : T => A a) (subPattern Sig T)) → HasFitIn m A Sig) :=
  ⟨fun q hq => theorem2_sets A hA m Sig q hq, upper_bound_sets A hA m Sig⟩

lemma hasFitIn_zero_iff {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ) (Sig : Matrix n n ℝ) :
    HasFitIn m (fun _ => ({0} : Set ℝ)) Sig ↔ ∀ i j, i ≠ j → Sig i j = 0 := by
  constructor
  · rintro ⟨G, ⟨-, hoff, hdiag⟩, hp, -⟩ i j hij
    obtain ⟨k, v, hv⟩ := exists_gram_of_posSemidef hp
    have h0 : ∀ a, v a = 0 := fun a => by
      have h1 : G a a = 0 := hdiag a
      rw [← hv, gram_apply] at h1
      exact inner_self_eq_zero.1 h1
    rw [← hoff i j hij, ← hv, gram_apply, h0 i, inner_zero_left]
  · intro h
    refine ⟨0, ⟨by simp [IsSymm], fun i j hij => (h i j hij).symm, fun i => by simp⟩,
      PosSemidef.zero, by simp⟩

/-- **The remark after Theorem 2 fails for its last sentence.** With every `A_i = {0}` (a
non-empty subset of `[0, ∞)`), a matrix has a positive semidefinite completion with diagonal in
the `A_i` only if it is diagonal, so every minimal obstruction has two variables: for
`2 ≤ q ≤ m` no `Σ` on `q (m + 3 - q)` variables lacks such a completion of rank `≤ m` while all
its proper principal submatrices have one. -/
theorem remark_theorem2_last_fails (m q : ℕ) (hq : 2 ≤ q) (hqm : q ≤ m) :
    ¬ ∃ Sig : Matrix (Fin (q * (m + 3 - q))) (Fin (q * (m + 3 - q))) ℝ,
      ¬ HasFitIn m (fun _ => ({0} : Set ℝ)) Sig ∧
      ∀ T : Finset (Fin (q * (m + 3 - q))), T ≠ univ →
        HasFitIn m (fun _ : T => ({0} : Set ℝ)) (subPattern Sig T) := by
  rintro ⟨Sig, hno, hall⟩
  rw [hasFitIn_zero_iff] at hno
  push Not at hno
  obtain ⟨i, j, hij, hne⟩ := hno
  have hcard : 3 ≤ q * (m + 3 - q) := by
    have : 3 ≤ m + 3 - q := by omega
    nlinarith
  have hT : ({i, j} : Finset _) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    rw [card_univ, Fintype.card_fin, card_pair hij] at this
    omega
  have := (hasFitIn_zero_iff m _).1 (hall _ hT) ⟨i, by simp⟩ ⟨j, by simp⟩
    (fun h => hij (congrArg Subtype.val h))
  exact hne this

/-! ## Section 4 -/

/-- **Lemma 3 (replicated matrices).** Let `q, t ≥ 2`, `m = q + t - 3`, `S0` as in the lemma,
and `Σ` replicated from `S0` on `q` groups of `t`, with diagonal entries `c_i`. Then `s_j > 0`
and `g_j > 0`; no positive semidefinite matrix of rank at most `m` has the off-diagonal entries
of `Σ`; the least rank of a reference of `Σ` is `q` if `c_i > s_j` for all `i`; if (1) holds,
every proper principal submatrix of `Σ` is in the `m`-factor model; and if `t ≥ 3` and every
proper principal submatrix is in the model, then (1) holds. -/
theorem lemma3 {q t : ℕ} (hq : 2 ≤ q) (ht : 2 ≤ t) {S0 : Matrix (Fin q) (Fin q) ℝ}
    (hS0 : IsLemma3Matrix S0) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ}
    (hSig : IsReplicated S0 Sig) :
    (∀ j, 0 < S0 j j ∧ 0 < schurG S0 j) ∧
    (∀ H : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ, H.PosSemidef →
      (∀ i l, i ≠ l → H i l = Sig i l) → q + t - 3 < H.rank) ∧
    ((∀ i, S0 i.1 i.1 < Sig i i) → IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q) ∧
    (Cond1 S0 Sig → ∀ T : Finset (Fin q × Fin t), T ≠ univ →
      InModel (q + t - 3) (subPattern Sig T)) ∧
    (3 ≤ t → (∀ T : Finset (Fin q × Fin t), T ≠ univ → InModel (q + t - 3) (subPattern Sig T)) →
      Cond1 S0 Sig) :=
  ⟨fun j => lemma3_pos hS0 hq j, fun H hH hoff => lemma3_no_psd hS0 hq ht hSig H hH hoff,
    fun hc => lemma3_least_ref hS0 hq ht hSig hc, fun hc T hT => lemma3_proper hS0 hq ht hSig hc T hT,
    fun ht3 h => lemma3_converse hS0 hq ht3 hSig h⟩

/-! ## Section 6 -/

/-- **Section 6.** `q (m + 3 - q) > 2m + 2` exactly when `3 ≤ q ≤ m` (for every integer `q`). -/
theorem section6_ineq (m : ℕ) (q : ℤ) : (2 * m + 2 : ℤ) < q * (m + 3 - q) ↔ 3 ≤ q ∧ q ≤ m :=
  StatisticalFactorAnalysis.section6_ineq m q

/-- **Section 6.** `⌊(m+3)²/4⌋ = ⌊(m-1)²/4⌋ + 2(m+1)`: the test size exceeds `2(m+1)` by
`⌊(m-1)²/4⌋`, which is positive exactly for `m ≥ 3`. -/
theorem section6_gap (m : ℕ) : (m + 3) ^ 2 / 4 = (m - 1) ^ 2 / 4 + (2 * m + 2) :=
  StatisticalFactorAnalysis.section6_gap m

end FreeDiagonal.StatisticalFactorAnalysis.Paper

#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.setting_fit
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.setting_weakFit
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.lemma1
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.lemma1_weak
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.theorem1
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.theorem2
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.theorem2_weak
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.theorem3
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.theorem4
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.lemma2
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.remark_theorem2
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.remark_theorem2_last_fails
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.lemma3
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.section6_ineq
#print axioms FreeDiagonal.StatisticalFactorAnalysis.Paper.section6_gap
#print axioms FreeDiagonal.StatisticalFactorAnalysis.theorem3_forward
