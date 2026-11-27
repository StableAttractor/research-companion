import FreeDiagonal.Closure.Witness
import FreeDiagonal.Witness.Threshold

/-!
# Task B2, B3: the closure threshold `t_k = 2k + 2`, in the `ρ` form

* `closure_cor71` (U6 Corollary 7.1): `ρ ≥ k + 1` and cross rank `j` give a sub-pattern on
  at most `k + 1 + j` indices with `ρ ≥ k + 1`.
* `closure_threshold` (U6 Theorem B, `ρ` form): `ρ(x) ≤ k ↔ ρ(x_T) ≤ k` for all `|T| ≤ 2k + 2`.
* `closure_card_le_of_minimal`: minimal obstructions to `ρ ≤ k` have at most `2k + 2` indices.
* `closure_threshold_sharp`: the perfect matching.
* `closure_corC` (U6 Corollary C, `ρ` form).

Any field, no symmetry. Not formalized: the identification of `{ρ ≤ k}` with the Zariski
closure `X_{n,k}` (U6 Proposition 1.1, the deletion formula).
-/

open Matrix Finset

universe u v

namespace FreeDiagonal

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- Every off-diagonal block bounds `ρ` from below. -/
lemma offDiag_rank_le_closRank {α β : Type*} [Fintype β] (x : Matrix n n F) (r : α → n)
    (c : β → n) (h : ∀ a b, r a ≠ c b) : (x.submatrix r c).rank ≤ closRank x := by
  classical
  set A : Finset n := univ.filter fun i => ∃ a, r a = i
  have hr : ∀ a, r a ∈ A := fun a => mem_filter.2 ⟨mem_univ _, a, rfl⟩
  have hc : ∀ b, c b ∈ Aᶜ := fun b => mem_compl.2 fun hb => by
    obtain ⟨a, ha⟩ := (mem_filter.1 hb).2
    exact h a b ha
  have e : x.submatrix r c = (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).submatrix
      (fun a => ⟨r a, hr a⟩) (fun b => ⟨c b, hc b⟩) := rfl
  rw [e]
  exact (rank_submatrix_le _ _ _).trans (cutRank_le_closRank x A)

lemma closRank_le_card (x : Matrix n n F) : closRank x ≤ Fintype.card n := by
  have h := closRank_le x univ
  have h0 : minCompRank (subPattern x (univ : Finset n)ᶜ) = 0 := by
    apply Nat.le_zero.1
    refine (minCompRank_le _ 0).trans ((rank_le_card_width _).trans ?_)
    simp
  rw [h0, add_zero, card_univ] at h
  exact h

/-- **U6 Corollary 7.1.** -/
theorem closure_cor71 (x : Matrix n n F) (k j : ℕ) (hk : k + 1 ≤ closRank x)
    (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ k + 1 + j ∧ k + 1 ≤ closRank (subPattern x T) := by
  obtain ⟨T0, hT0, hq⟩ := closure_witness x j hcut
  have hle : closRank (subPattern x T0) ≤ T0.card := by
    have := closRank_le_card (subPattern x T0); simpa using this
  obtain ⟨T, hsub, hcard, hρ⟩ := exists_subset_closRank x (closRank x - (k + 1)) T0 (by omega)
  exact ⟨T, by omega, by omega⟩

/-- A small obstruction exists whenever `ρ ≥ k + 1`. -/
theorem exists_small_obstruction (x : Matrix n n F) (k : ℕ) (hk : k + 1 ≤ closRank x) :
    ∃ T : Finset n, T.card ≤ 2 * k + 2 ∧ k + 1 ≤ closRank (subPattern x T) := by
  classical
  by_cases hcut : CutRankLE x k
  · obtain ⟨T, hT, hρ⟩ := closure_cor71 x k k hk hcut
    exact ⟨T, by omega, hρ⟩
  · simp only [CutRankLE, not_forall, not_le] at hcut
    obtain ⟨A, hA⟩ := hcut
    obtain ⟨R, C, hR, hC, hRC⟩ := exists_small_submatrix
      (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))) (k + 1) hA
    set T : Finset n := R.map (Function.Embedding.subtype _) ∪ C.map (Function.Embedding.subtype _)
    have hRT : ∀ a : R, ((a : A) : n) ∈ T := fun a => mem_union_left _ (mem_map_of_mem _ a.2)
    have hCT : ∀ b : C, ((b : ↥(Aᶜ)) : n) ∈ T := fun b => mem_union_right _ (mem_map_of_mem _ b.2)
    refine ⟨T, ?_, ?_⟩
    · calc T.card ≤ R.card + C.card := (card_union_le _ _).trans (by simp)
        _ ≤ 2 * k + 2 := by omega
    · refine le_trans hRC (le_of_eq_of_le ?_ (offDiag_rank_le_closRank (subPattern x T)
        (fun a : R => (⟨a, hRT a⟩ : T)) (fun b : C => (⟨b, hCT b⟩ : T)) ?_))
      · rfl
      · intro a b h
        have h' : ((a : A) : n) = ((b : ↥(Aᶜ)) : n) := congrArg Subtype.val h
        exact (mem_compl.1 (b : ↥(Aᶜ)).2) (h' ▸ (a : A).2)

/-- **The closure threshold** (U6 Theorem B, in the `ρ` form). -/
theorem closure_threshold (x : Matrix n n F) (k : ℕ) :
    closRank x ≤ k ↔ ∀ T : Finset n, T.card ≤ 2 * k + 2 → closRank (subPattern x T) ≤ k := by
  constructor
  · exact fun h T _ => (closRank_subPattern_le x T).trans h
  · intro h
    by_contra hc
    obtain ⟨T, hT, hρ⟩ := exists_small_obstruction x k (by omega)
    have := h T hT
    omega

/-- **Minimal obstructions to `ρ ≤ k` have at most `2k + 2` indices.** -/
theorem closure_card_le_of_minimal (k : ℕ) (x : Matrix n n F) (hk : k + 1 ≤ closRank x)
    (hmin : ∀ T : Finset n, T ≠ univ → closRank (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 := by
  obtain ⟨T, hT, hρ⟩ := exists_small_obstruction x k hk
  have hTu : T = univ := by
    by_contra h; have := hmin T h; omega
  rw [← card_univ, ← hTu]
  exact hT

/-- **Sharpness**: `2k + 2` cannot be replaced by `2k + 1` (the perfect matching). -/
theorem closure_threshold_sharp (F : Type*) [Field F] (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      ¬ closRank (matching F k) ≤ k ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T ≠ univ →
        closRank (subPattern (matching F k) T) ≤ k) ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        closRank (subPattern (matching F k) T) ≤ k) := by
  have hlow : k + 1 ≤ closRank (matching F k) := by
    have h := offDiag_rank_le_closRank (matching F k) (fun a : Fin (k + 1) => (a, false))
      (fun a : Fin (k + 1) => (a, true)) (fun a b h => by simp at h)
    have e : (matching F k).submatrix (fun a : Fin (k + 1) => (a, false))
        (fun a : Fin (k + 1) => (a, true)) = 1 := by
      ext a b; simp [matching, Matrix.one_apply]
    rw [e, Matrix.rank_one, Fintype.card_fin] at h
    exact h
  have hprop : ∀ T : Finset (Fin (k + 1) × Bool), T ≠ univ →
      closRank (subPattern (matching F k) T) ≤ k := fun T hT =>
    (closRank_le_minCompRank _).trans (matching_proper F k T hT)
  refine ⟨card_matching_index k, by omega, hprop, fun T hT => hprop T ?_⟩
  intro h
  have := card_matching_index k
  rw [h, card_univ] at hT
  omega

/-- **U6 Corollary C, in the `ρ` form.** For `n ≥ 2k + 1`: `ρ(x) ≤ k` iff every cut rank is at
most `k` (equivalently, every `(k+1) × (k+1)` minor `x[R, C]` with `R, C` disjoint vanishes) and
every sub-pattern on `2k + 1` indices has `ρ ≤ k`. -/
theorem closure_corC (x : Matrix n n F) (k : ℕ) (hn : 2 * k + 1 ≤ Fintype.card n) :
    closRank x ≤ k ↔ CutRankLE x k ∧
      ∀ T : Finset n, T.card = 2 * k + 1 → closRank (subPattern x T) ≤ k := by
  constructor
  · intro h
    exact ⟨fun A => (cutRank_le_closRank x A).trans h,
      fun T _ => (closRank_subPattern_le x T).trans h⟩
  · rintro ⟨hcut, h⟩
    by_contra hc
    obtain ⟨T, hT, hρ⟩ := closure_cor71 x k k (by omega) hcut
    obtain ⟨T', hTT', hT'⟩ := Finset.exists_superset_card_eq (show T.card ≤ 2 * k + 1 by omega)
      (by simpa using hn)
    have := closRank_subPattern_mono x hTT'
    have := h T' hT'
    omega

end FreeDiagonal
