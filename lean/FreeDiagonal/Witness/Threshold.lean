import FreeDiagonal.Witness.Basic

/-!
# Theorem 3: the sharp threshold `2k + 2`

* `card_le_of_minimal`: a minimal obstruction to `c ≤ k` has at most `2k + 2` indices.
* `threshold`: `c(x) ≤ k ↔ c(x_T) ≤ k` for every `T` with `|T| ≤ 2k + 2`.
* `matching`: the perfect matching on `2k + 2` indices shows that `2k + 2` is sharp.

The paper states Theorem 3 for `k ≥ 1`; the proofs below need no such restriction.
-/

open Matrix Module Submodule Finset

universe u v

namespace FreeDiagonal

section Threshold

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- **Theorem 3, minimal-obstruction form.** If `c(x) ≥ k + 1` and every proper sub-pattern has
`c ≤ k`, then `x` has at most `2k + 2` indices. -/
theorem card_le_of_minimal (hU : UnionRankFormula.{u, v, max u v} F) (k : ℕ)
    (x : Matrix n n F) (hk : k + 1 ≤ minCompRank x)
    (hmin : ∀ T : Finset n, T ≠ univ → minCompRank (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 := by
  classical
  by_cases hcut : CutRankLE x k
  · -- Case `j ≤ k`: Theorem 2.
    obtain ⟨T, hT, hTc⟩ := witness hU x k hcut
    have hTu : T = univ := by
      by_contra h; have := hmin T h; omega
    have hne : Nonempty n := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h0 := (minCompRank_le x 0).trans (rank_le_card_width _)
      rw [Fintype.card_eq_zero] at h0
      omega
    obtain ⟨i⟩ := hne
    have hc := minCompRank_le_erase_add_two x i
    have hi := hmin (univ.erase i) (fun h => by
      have : i ∈ univ.erase i := by rw [h]; exact mem_univ i
      simp at this)
    rw [← card_univ, ← hTu]
    omega
  · -- Case `j ≥ k + 1`: a non-singular `(k+1) × (k+1)` off-diagonal block.
    simp only [CutRankLE, not_forall, not_le] at hcut
    obtain ⟨A, hA⟩ := hcut
    obtain ⟨R, C, hR, hC, hRC⟩ := exists_small_submatrix
      (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))) (k + 1) hA
    set R' : Finset n := R.map (Function.Embedding.subtype _)
    set C' : Finset n := C.map (Function.Embedding.subtype _)
    set T := R' ∪ C'
    have hRT : ∀ a : R, ((a : A) : n) ∈ T :=
      fun a => mem_union_left _ (mem_map_of_mem _ a.2)
    have hCT : ∀ b : C, ((b : ↥(Aᶜ)) : n) ∈ T :=
      fun b => mem_union_right _ (mem_map_of_mem _ b.2)
    have hTk : k + 1 ≤ minCompRank (subPattern x T) := by
      refine le_trans hRC (le_of_eq_of_le ?_ (offDiag_rank_le_minCompRank (subPattern x T)
        (fun a : R => (⟨a, hRT a⟩ : T)) (fun b : C => (⟨b, hCT b⟩ : T)) ?_))
      · rfl
      · intro a b h
        have h' : ((a : A) : n) = ((b : ↥(Aᶜ)) : n) := congrArg Subtype.val h
        exact (mem_compl.1 (b : ↥(Aᶜ)).2) (h' ▸ (a : A).2)
    have hTu : T = univ := by
      by_contra h; have := hmin T h; omega
    have hcard : T.card ≤ 2 * k + 2 := by
      calc T.card ≤ R'.card + C'.card := card_union_le _ _
        _ = R.card + C.card := by simp [R', C']
        _ ≤ 2 * k + 2 := by omega
    rw [← card_univ, ← hTu]
    exact hcard

/-- **Theorem 3 (sharp threshold).** `c(x) ≤ k` if and only if `c(x_T) ≤ k` for every `T` with
`|T| ≤ 2k + 2`. -/
theorem threshold (hU : UnionRankFormula.{u, v, max u v} F) (k : ℕ) (x : Matrix n n F) :
    minCompRank x ≤ k ↔
      ∀ T : Finset n, T.card ≤ 2 * k + 2 → minCompRank (subPattern x T) ≤ k := by
  classical
  constructor
  · intro h T _
    exact (minCompRank_subPattern_le x T).trans h
  · intro h
    by_contra hc
    push_neg at hc
    have hex : ∃ m, ∃ T : Finset n, T.card = m ∧ k < minCompRank (subPattern x T) :=
      ⟨_, univ, rfl, lt_of_lt_of_le hc (minCompRank_le_subPattern_univ x)⟩
    obtain ⟨T, hTm, hTk⟩ := Nat.find_spec hex
    have hminT : ∀ T' : Finset T, T' ≠ univ →
        minCompRank (subPattern (subPattern x T) T') ≤ k := by
      intro T' hT'
      set T'' : Finset n := T'.map (Function.Embedding.subtype _)
      have hlt : T''.card < Nat.find hex := by
        rw [← hTm]
        have h1 : T''.card = T'.card := by simp [T'']
        have h2 : T'.card < Fintype.card T := (card_lt_iff_ne_univ T').2 hT'
        rw [Fintype.card_coe] at h2
        omega
      have hnot := Nat.find_min hex hlt
      push_neg at hnot
      have h3 := hnot T'' rfl
      refine le_trans (minCompRank_le_of_embedding (subPattern x T'') _
        (fun a : T' => (⟨a.1.1, mem_map_of_mem _ a.2⟩ : T''))
        (fun a b hab => ?_) (fun _ _ _ => rfl)) h3
      have := congrArg (fun z : T'' => (z : n)) hab
      exact Subtype.ext (Subtype.ext this)
    have hcard := card_le_of_minimal hU k (subPattern x T) hTk hminT
    rw [Fintype.card_coe] at hcard
    have := h T hcard
    omega

end Threshold

/-! ### Sharpness -/

section Sharp

variable (F : Type*) [Field F]

/-- The adjacency pattern of a perfect matching on `2k + 2` indices `(a, b)`,
`a : Fin (k+1)`, `b : Bool`: `(a, b)` is matched with `(a, !b)`. -/
def matching (k : ℕ) : Matrix (Fin (k + 1) × Bool) (Fin (k + 1) × Bool) F :=
  fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0

lemma card_matching_index (k : ℕ) : Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 := by
  simp [Fintype.card_prod]; ring

/-- The matching has a cut of rank `k + 1`, so `c ≥ k + 1`. -/
lemma matching_lower (k : ℕ) : k + 1 ≤ minCompRank (matching F k) := by
  have h := offDiag_rank_le_minCompRank (matching F k) (fun a : Fin (k + 1) => (a, false))
    (fun a : Fin (k + 1) => (a, true)) (fun a b h => by simp at h)
  have e : (matching F k).submatrix (fun a : Fin (k + 1) => (a, false))
      (fun a : Fin (k + 1) => (a, true)) = 1 := by
    ext a b; simp [matching, Matrix.one_apply]
  rw [e, rank_one, Fintype.card_fin] at h
  exact h

/-- Every proper sub-pattern of the matching has `c ≤ k`. -/
lemma matching_proper (k : ℕ) (T : Finset (Fin (k + 1) × Bool)) (hT : T ≠ univ) :
    minCompRank (subPattern (matching F k) T) ≤ k := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p ∉ T := by
    by_contra h; push_neg at h; exact hT (eq_univ_iff_forall.2 h)
  set d : T → F := fun r => if (r : Fin (k + 1) × Bool).1 = p.1 then 0 else 1
  set M := subPattern (matching F k) T + diagonal d
  set w : {a : Fin (k + 1) // a ≠ p.1} → (T → F) :=
    fun a s => if (s : Fin (k + 1) × Bool).1 = a.1 then 1 else 0
  have hM : ∀ r s : T, M r s = if (r : Fin (k + 1) × Bool).1 = (s : Fin (k + 1) × Bool).1 ∧
      (r : Fin (k + 1) × Bool).1 ≠ p.1 then 1 else 0 := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      by_cases hr : (r : Fin (k + 1) × Bool).1 = p.1 <;> simp [M, d, subPattern, matching, hr]
    · have hne : (r : Fin (k + 1) × Bool) ≠ s := fun h => hrs (Subtype.ext h)
      have e1 : M r s = matching F k r s := by simp [M, subPattern, diagonal_apply_ne _ hrs]
      rw [e1]; unfold matching
      by_cases h1 : (r : Fin (k + 1) × Bool).1 = (s : Fin (k + 1) × Bool).1
      · have h2 : (r : Fin (k + 1) × Bool).2 ≠ (s : Fin (k + 1) × Bool).2 :=
          fun h2 => hne (Prod.ext h1 h2)
        have h3 : (r : Fin (k + 1) × Bool).1 ≠ p.1 := by
          intro h3
          have hb := (by decide : ∀ a b c : Bool, b ≠ c → a = b ∨ a = c) p.2 _ _ h2
          rcases hb with hb | hb
          · have : p = r := Prod.ext h3.symm hb
            exact hp (by rw [this]; exact r.2)
          · have : p = s := Prod.ext (h3.symm.trans h1) hb
            exact hp (by rw [this]; exact s.2)
        have h4 : (s : Fin (k + 1) × Bool).1 ≠ p.1 := fun h => h3 (h1.trans h)
        simp [h1, h2, h3, h4]
      · simp [h1]
  have hrow : ∀ r : T, M.row r ∈ span F (Set.range w) := by
    intro r
    by_cases hr : (r : Fin (k + 1) × Bool).1 = p.1
    · have : M.row r = 0 := by
        ext s; show M r s = 0; rw [hM]; simp [hr]
      rw [this]; exact zero_mem _
    · have : M.row r = w ⟨(r : Fin (k + 1) × Bool).1, hr⟩ := by
        ext s; show M r s = _; rw [hM]
        by_cases h : (r : Fin (k + 1) × Bool).1 = (s : Fin (k + 1) × Bool).1
        · have h4 : (s : Fin (k + 1) × Bool).1 ≠ p.1 := fun h' => hr (h.trans h')
          simp [w, hr, h, h4]
        · simp [w, hr, h, Ne.symm h]
      rw [this]; exact subset_span ⟨_, rfl⟩
  have hle : M.rank ≤ k := by
    rw [rank_eq_frk_univ]
    unfold frk
    calc finrank F (span F (M.row '' ((univ : Finset T) : Set T)))
        ≤ finrank F (span F (Set.range w)) := by
          apply Submodule.finrank_mono
          apply span_le.2
          rintro _ ⟨r, -, rfl⟩
          exact hrow r
      _ ≤ Fintype.card {a : Fin (k + 1) // a ≠ p.1} := finrank_range_le_card w
      _ = k := by simp [Fintype.card_subtype_compl]
  exact (minCompRank_le _ d).trans hle

/-- **Theorem 3, sharpness.** The perfect matching on `2k + 2` indices has `c ≥ k + 1`, while
every sub-pattern on at most `2k + 1` indices has `c ≤ k`. So `2k + 2` cannot be replaced by
`2k + 1` in `threshold`. -/
theorem threshold_sharp (k : ℕ) :
    Fintype.card (Fin (k + 1) × Bool) = 2 * k + 2 ∧
      ¬ minCompRank (matching F k) ≤ k ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T ≠ univ →
        minCompRank (subPattern (matching F k) T) ≤ k) ∧
      (∀ T : Finset (Fin (k + 1) × Bool), T.card ≤ 2 * k + 1 →
        minCompRank (subPattern (matching F k) T) ≤ k) := by
  refine ⟨card_matching_index k, by have := matching_lower F k; omega,
    matching_proper F k, fun T hT => matching_proper F k T ?_⟩
  intro h
  have := card_matching_index k
  rw [h, card_univ] at hT
  omega

end Sharp

end FreeDiagonal
