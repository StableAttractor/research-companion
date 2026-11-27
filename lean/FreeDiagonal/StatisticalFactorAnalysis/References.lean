import FreeDiagonal.StatisticalFactorAnalysis.Model

/-!
# Lemma 1 (references)

The bound `2m + 2` for minimum-rank completion with diagonal entries restricted to arbitrary
non-empty sets (`card_le_of_minimalR`, `Witness/Restricted.lean`) turned into a threshold
statement (`restricted_threshold`), then specialised to references (`[0, Σ_ii)`), weak
references (`[0, Σ_ii]`) and arbitrary admissible sets.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section Threshold

variable {F : Type*} [Field F]

lemma minCompRankR_le_of_embedding {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {Ω : β → Set F} (hΩ : ∀ i, (Ω i).Nonempty) (y : Matrix β β F) (f : α → β)
    (hf : Function.Injective f) :
    minCompRankR (fun a => Ω (f a)) (y.submatrix f f) ≤ minCompRankR Ω y := by
  obtain ⟨d, hd, e⟩ := exists_minCompRankR hΩ y
  have hadm : Admissible (fun a => Ω (f a)) (y.submatrix f f) (fun a => d (f a)) :=
    fun a => by simpa using hd (f a)
  have eq : y.submatrix f f + diagonal (fun a => d (f a)) = (y + diagonal d).submatrix f f := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (hf.ne h)]
  calc minCompRankR (fun a => Ω (f a)) (y.submatrix f f)
      ≤ (y.submatrix f f + diagonal (fun a => d (f a))).rank := minCompRankR_le _ _ hadm
    _ = ((y + diagonal d).submatrix f f).rank := by rw [eq]
    _ ≤ (y + diagonal d).rank := rank_submatrix_le _ _ _
    _ = minCompRankR Ω y := e

/-- **Threshold `2k + 2` with restricted diagonals**, over any field: if every sub-pattern on at
most `2k + 2` indices has an admissible completion of rank at most `k`, so has the pattern. -/
theorem restricted_threshold {n : Type*} [Fintype n] [DecidableEq n] {Ω : n → Set F}
    (hΩ : ∀ i, (Ω i).Nonempty) (k : ℕ) (x : Matrix n n F)
    (h : ∀ T : Finset n, T.card ≤ 2 * k + 2 →
      minCompRankR (restrictΩ Ω T) (subPattern x T) ≤ k) :
    minCompRankR Ω x ≤ k := by
  classical
  by_contra hc
  push Not at hc
  have hΩu : ∀ a : (univ : Finset n), (restrictΩ Ω univ a).Nonempty := fun a => hΩ a
  have huniv : minCompRankR Ω x ≤ minCompRankR (restrictΩ Ω univ) (subPattern x univ) :=
    minCompRankR_le_of_embedding hΩu (subPattern x univ) (fun i => ⟨i, mem_univ i⟩)
      (fun a b h => congrArg Subtype.val h)
  have hex : ∃ m, ∃ T : Finset n, T.card = m ∧
      k < minCompRankR (restrictΩ Ω T) (subPattern x T) :=
    ⟨_, univ, rfl, lt_of_lt_of_le hc huniv⟩
  obtain ⟨T, hTm, hTk⟩ := Nat.find_spec hex
  have hΩT : ∀ a : T, (restrictΩ Ω T a).Nonempty := fun a => hΩ a
  have hminT : ∀ T' : Finset T, T' ≠ univ →
      minCompRankR (restrictΩ (restrictΩ Ω T) T') (subPattern (subPattern x T) T') ≤ k := by
    intro T' hT'
    set T'' : Finset n := T'.map (Function.Embedding.subtype _)
    have hlt : T''.card < Nat.find hex := by
      rw [← hTm]
      have h1 : T''.card = T'.card := by simp [T'']
      have h2 : T'.card < Fintype.card T := (card_lt_iff_ne_univ T').2 hT'
      rw [Fintype.card_coe] at h2
      omega
    have hnot := Nat.find_min hex hlt
    push Not at hnot
    have h3 := hnot T'' rfl
    have hΩT'' : ∀ a : T'', (restrictΩ Ω T'' a).Nonempty := fun a => hΩ a
    refine le_trans ?_ h3
    exact minCompRankR_le_of_embedding hΩT'' (subPattern x T'')
      (fun a : T' => (⟨a.1.1, mem_map_of_mem _ a.2⟩ : T''))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : T'' => (z : n)) hab)))
  have hcard := card_le_of_minimalR hΩT k (subPattern x T) hTk hminT
  rw [Fintype.card_coe] at hcard
  have := h T hcard
  omega

end Threshold

section Lemma1

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma completion_of_isCompletionIn {A : n → Set ℝ} {Sig G : Matrix n n ℝ}
    (hG : IsCompletionIn A Sig G) :
    Admissible A Sig (fun i => G i i - Sig i i) ∧ G = Sig + diagonal (fun i => G i i - Sig i i) := by
  refine ⟨fun i => by simpa using hG.2.2 i, ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply_ne _ h, hG.2.1 i j h]

/-- **Lemma 1 for arbitrary admissible sets.** If for every `T` with `|T| ≤ 2m + 2` the matrix
`Σ_T` has a symmetric completion of rank at most `m` with diagonal entries in the sets `A i`,
then so has `Σ`. (No hypothesis on the sets; their non-emptiness follows.) -/
theorem lemma1_sets (m : ℕ) (A : n → Set ℝ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      ∃ G, IsCompletionIn (fun a : T => A a) (subPattern Sig T) G ∧ G.rank ≤ m) :
    ∃ G, IsCompletionIn A Sig G ∧ G.rank ≤ m := by
  classical
  -- `Σ` is symmetric
  have hsymm : Sig.IsSymm := by
    ext i j
    by_cases hij : i = j
    · subst hij; rfl
    · obtain ⟨G, hG, -⟩ := h {i, j} (by
        calc ({i, j} : Finset n).card ≤ 2 := card_le_two
          _ ≤ 2 * m + 2 := by omega)
      have e1 := hG.2.1 ⟨i, by simp⟩ ⟨j, by simp⟩ (fun e => hij (congrArg Subtype.val e))
      have e2 := hG.2.1 ⟨j, by simp⟩ ⟨i, by simp⟩ (fun e => hij (congrArg Subtype.val e).symm)
      have e3 := congrFun (congrFun hG.1 ⟨i, by simp⟩) ⟨j, by simp⟩
      simp only [transpose_apply] at e3
      simp only [subPattern, submatrix_apply] at e1 e2
      rw [transpose_apply]
      rw [← e1, ← e2, e3]
  -- the sets are non-empty
  have hΩ : ∀ i, (A i).Nonempty := by
    intro i
    obtain ⟨G, hG, -⟩ := h {i} (by simp)
    exact ⟨_, hG.2.2 ⟨i, by simp⟩⟩
  have hsmall : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      minCompRankR (restrictΩ A T) (subPattern Sig T) ≤ m := by
    intro T hT
    obtain ⟨G, hG, hr⟩ := h T hT
    obtain ⟨hadm, e⟩ := completion_of_isCompletionIn hG
    calc minCompRankR (restrictΩ A T) (subPattern Sig T)
        ≤ (subPattern Sig T + diagonal (fun a => G a a - subPattern Sig T a a)).rank :=
          minCompRankR_le _ _ hadm
      _ = G.rank := by rw [← e]
      _ ≤ m := hr
  have hc := restricted_threshold hΩ m Sig hsmall
  obtain ⟨d, hd, e⟩ := exists_minCompRankR hΩ Sig
  refine ⟨Sig + diagonal d, ⟨?_, ?_, ?_⟩, by rw [e]; exact hc⟩
  · rw [IsSymm, transpose_add, hsymm.eq, diagonal_transpose]
  · intro i j hij; simp [diagonal_apply_ne _ hij]
  · intro i; simpa using hd i

/-- **Lemma 1 (references).** If for every `T ⊆ E` with `|T| ≤ 2m + 2` the matrix `Σ_T` has a
reference of rank at most `m`, then `Σ` has a reference of rank at most `m`. -/
theorem lemma1 (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      ∃ G, IsReference (subPattern Sig T) G ∧ G.rank ≤ m) :
    ∃ G, IsReference Sig G ∧ G.rank ≤ m := by
  simp only [isReference_iff] at h ⊢
  exact lemma1_sets m (refSets Sig) Sig h

/-- **Lemma 1, weak form** (references with `0 ≤ G_ii ≤ Σ_ii`). -/
theorem lemma1_weak (m : ℕ) (Sig : Matrix n n ℝ)
    (h : ∀ T : Finset n, T.card ≤ 2 * m + 2 →
      ∃ G, IsWeakReference (subPattern Sig T) G ∧ G.rank ≤ m) :
    ∃ G, IsWeakReference Sig G ∧ G.rank ≤ m := by
  simp only [isWeakReference_iff] at h ⊢
  exact lemma1_sets m (weakRefSets Sig) Sig h

end Lemma1

end FreeDiagonal.StatisticalFactorAnalysis
