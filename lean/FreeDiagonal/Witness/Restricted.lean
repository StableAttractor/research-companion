import FreeDiagonal.Witness.Unconditional

/-!
# Task A1: restricted diagonals

Each diagonal entry of a completion is confined to a non-empty set `Ω i ⊆ F`
(second remark of Section 4 of the note; Part 51-d). `minCompRankR Ω x` is the least rank of an
admissible completion. Proved: facts (a), (b), (c), the witness theorem for any admissible
completion (`witnessR`), and the bound `n ≤ 2k + 2` for minimal obstructions
(`card_le_of_minimalR`). At `Ω = univ` these give back the unrestricted statements.
Sharpness is NOT claimed for general `Ω`.

`witness_core` is the Part 51 construction extracted from the proof of `witness_of_completion`
(unchanged in `Main.lean`), so that it can be reused.
-/

open Matrix Module Submodule Finset

universe u v

namespace FreeDiagonal

section Core

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- **The Part 51 construction.** If all cut ranks are at most `j` and `G = x + diagonal d0`,
there are `T` with `|T| ≤ rank G + j` and `X` with `Xᶜ ⊆ T` such that every completion of `x_T`
has rank at least that of every completion of `x` which agrees with `G` on `X` and with the given
completion of `x_T` on `T \ X`. -/
theorem witness_core (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) (d0 : n → F) :
    ∃ T X : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧ (∀ i, i ∉ X → i ∈ T) ∧
      ∀ (d : T → F) (e : n → F), (∀ i ∈ X, e i = d0 i) →
        (∀ i (h : i ∈ T), i ∉ X → e i = d ⟨i, h⟩) →
          (x + diagonal e).rank ≤ (subPattern x T + diagonal d).rank := by
  classical
  have hU := unionRankFormula.{u, v, max u v} F
  set G := x + diagonal d0 with hG
  -- Step 1
  have step1 : ∀ A : Finset n, frk F G.row A + frk F G.col (univ \ A) ≤ G.rank + j := by
    intro A
    rw [← compl_eq_univ_sdiff]
    exact (rows_add_cols_le x d0 A).trans (Nat.add_le_add_left (hcut A) _)
  -- Step 2: a minimiser `X` of `|Xᶜ| + rk_rows X + rk_cols X`
  set fX : Finset n → ℕ := fun X => (univ \ X).card + frk F G.row X + frk F G.col X
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset (Finset n)) fX univ_nonempty
  obtain ⟨A0, -, X0, -, h0⟩ := hU n (n → F) G.row G.col univ
  have hX : fX X ≤ G.rank + j := (hXmin X0 (mem_univ _)).trans (h0.trans (step1 A0))
  obtain ⟨A', hA'X, X'', hX''X, h1⟩ := hU n (n → F) G.row G.col X
  have h2 := hXmin X'' (mem_univ _)
  have hXf : fX X ≤ G.rank + j := hX
  have hc2 := card_sdiff_add_card_eq_card (subset_univ X)
  have hc3 := card_sdiff_add_card_eq_card (subset_univ X'')
  have hc4 := card_sdiff_add_card_eq_card hX''X
  have m1 := frk_mono (F := F) G.row hA'X
  have m2 := frk_mono (F := F) G.col (sdiff_subset : X \ A' ⊆ X)
  simp only [fX] at hX h2
  have eA : frk F G.row A' = frk F G.row X := by omega
  have eC : frk F G.col (X \ A') = frk F G.col X := by omega
  have spA : span F (G.row '' (A' : Set n)) = span F (G.row '' (X : Set n)) :=
    Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (coe_subset.2 hA'X))) eA
  have spC : span F (G.col '' ((X \ A' : Finset n) : Set n)) = span F (G.col '' (X : Set n)) :=
    Submodule.eq_of_le_of_finrank_eq
      (span_mono (Set.image_mono (coe_subset.2 sdiff_subset))) eC
  obtain ⟨I1, hI1, hI1c, hI1s⟩ := exists_basis_subset (F := F) G.row A'
  obtain ⟨I2, hI2, hI2c, hI2s⟩ := exists_basis_subset (F := F) G.col (X \ A')
  have hI1X : ∀ i ∈ I1, i ∈ X := fun i hi => hA'X (hI1 hi)
  have hI2X : ∀ i ∈ I2, i ∈ X := fun i hi => (mem_sdiff.1 (hI2 hi)).1
  have hdisj : ∀ i, i ∈ I1 → i ∈ I2 → False :=
    fun i h1 h2 => (mem_sdiff.1 (hI2 h2)).2 (hI1 h1)
  set T := (univ \ X) ∪ I1 ∪ I2 with hT
  refine ⟨T, X, ?_, ?_, ?_⟩
  · -- the size bound
    calc T.card ≤ ((univ \ X) ∪ I1).card + I2.card := card_union_le _ _
      _ ≤ (univ \ X).card + I1.card + I2.card := by gcongr; exact card_union_le _ _
      _ = fX X := by simp only [fX]; rw [hI1c, hI2c, eA, eC]
      _ ≤ G.rank + j := hXf
  · intro i hi; exact mem_union_left _ (mem_union_left _ (mem_sdiff.2 ⟨mem_univ i, hi⟩))
  -- Steps 3 and 4, short form
  intro d d' hd'X hd'T
  set R := (univ \ X) ∪ I1
  set C := (univ \ X) ∪ I2
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => mem_union_left _ hr
  have hCT : ∀ s ∈ C, s ∈ T := fun s hs => by
    rcases mem_union.1 hs with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_right _ h
  set H := x + diagonal d'
  have hrowX : ∀ i ∈ X, H.row i = G.row i := by
    intro i hi; ext s
    by_cases h : i = s
    · subst h; simp [H, G, hd'X i hi]
    · simp [H, G, diagonal_apply_ne _ h]
  have hcolX : ∀ s ∈ X, H.col s = G.col s := by
    intro s hs; ext r
    by_cases h : r = s
    · subst h; simp [H, G, hd'X r hs]
    · simp [H, G, diagonal_apply_ne _ h]
  have hR : ∀ i, H.row i ∈ span F (H.row '' (R : Set n)) := by
    intro i
    by_cases hi : i ∈ X
    · have hG : G.row i ∈ span F (G.row '' (I1 : Set n)) := by
        rw [hI1s, spA]; exact subset_span ⟨i, hi, rfl⟩
      have e : G.row '' (I1 : Set n) = H.row '' (I1 : Set n) :=
        Set.image_congr (fun l hl => (hrowX l (hI1X l hl)).symm)
      rw [hrowX i hi]
      rw [e] at hG
      exact span_mono (Set.image_mono (coe_subset.2 subset_union_right)) hG
    · exact subset_span ⟨i, by simp [R, hi], rfl⟩
  have hC : ∀ s, H.col s ∈ span F (H.col '' (C : Set n)) := by
    intro s
    by_cases hs : s ∈ X
    · have hG : G.col s ∈ span F (G.col '' (I2 : Set n)) := by
        rw [hI2s, spC]; exact subset_span ⟨s, hs, rfl⟩
      have e : G.col '' (I2 : Set n) = H.col '' (I2 : Set n) :=
        Set.image_congr (fun l hl => (hcolX l (hI2X l hl)).symm)
      rw [hcolX s hs]
      rw [e] at hG
      exact span_mono (Set.image_mono (coe_subset.2 subset_union_right)) hG
    · exact subset_span ⟨s, by simp [C, hs], rfl⟩
  have key := rank_le_submatrix_of_span H R C hR hC
  have e : H.submatrix (fun r : R => (r : n)) (fun s : C => (s : n)) =
      (subPattern x T + diagonal d).submatrix (fun r : R => ⟨r, hRT r r.2⟩)
        (fun s : C => ⟨s, hCT s s.2⟩) := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    by_cases hrs : r = s
    · subst hrs
      have hrX : r ∉ X := by
        intro hX
        rcases mem_union.1 hr with h | h
        · exact (mem_sdiff.1 h).2 hX
        rcases mem_union.1 hs with h' | h'
        · exact (mem_sdiff.1 h').2 hX
        exact hdisj r h h'
      simp [H, hd'T r (hRT r hr) hrX, subPattern]
    · have hne : (⟨r, hRT r hr⟩ : T) ≠ ⟨s, hCT s hs⟩ := fun h => hrs (congrArg Subtype.val h)
      simp [H, subPattern, diagonal_apply_ne _ hrs, diagonal_apply_ne _ hne]
  calc H.rank ≤ _ := key
    _ = _ := by rw [e]
    _ ≤ _ := rank_submatrix_le _ _ _

end Core

section Restricted

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- `x + diagonal d` is admissible: its diagonal entries lie in the prescribed sets. -/
def Admissible (Ω : n → Set F) (x : Matrix n n F) (d : n → F) : Prop :=
  ∀ i, x i i + d i ∈ Ω i

/-- `c_Ω(x)`: least rank of an admissible completion. -/
noncomputable def minCompRankR (Ω : n → Set F) (x : Matrix n n F) : ℕ :=
  ⨅ d : {d : n → F // Admissible Ω x d}, (x + diagonal d.1).rank

/-- The sets `Ω` restricted to `T`. -/
def restrictΩ (Ω : n → Set F) (T : Finset n) : T → Set F := fun a => Ω a

variable {Ω : n → Set F}

lemma exists_admissible (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F) :
    ∃ d, Admissible Ω x d :=
  ⟨fun i => (hΩ i).some - x i i, fun i => by simpa using (hΩ i).some_mem⟩

lemma minCompRankR_le (x : Matrix n n F) (d : n → F) (hd : Admissible Ω x d) :
    minCompRankR Ω x ≤ (x + diagonal d).rank :=
  ciInf_le (OrderBot.bddBelow _) (⟨d, hd⟩ : {d // Admissible Ω x d})

lemma exists_minCompRankR (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F) :
    ∃ d, Admissible Ω x d ∧ (x + diagonal d).rank = minCompRankR Ω x := by
  obtain ⟨d0, hd0⟩ := exists_admissible hΩ x
  have h : minCompRankR Ω x ∈
      Set.range (fun d : {d // Admissible Ω x d} => (x + diagonal d.1).rank) := by
    unfold minCompRankR; exact Nat.sInf_mem ⟨_, ⟨d0, hd0⟩, rfl⟩
  obtain ⟨⟨d, hd⟩, e⟩ := h
  exact ⟨d, hd, e⟩

lemma le_minCompRankR (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F) {r : ℕ}
    (h : ∀ d, Admissible Ω x d → r ≤ (x + diagonal d).rank) : r ≤ minCompRankR Ω x := by
  obtain ⟨d0, hd0⟩ := exists_admissible hΩ x
  have : Nonempty {d // Admissible Ω x d} := ⟨⟨d0, hd0⟩⟩
  exact le_ciInf fun d => h d.1 d.2

/-- With no restriction, `c_Ω = c`. -/
lemma minCompRankR_univ (x : Matrix n n F) :
    minCompRankR (fun _ => (Set.univ : Set F)) x = minCompRank x := by
  apply le_antisymm
  · obtain ⟨d, hd⟩ := exists_minCompRank x
    rw [← hd]; exact minCompRankR_le x d (fun _ => Set.mem_univ _)
  · exact le_minCompRankR (fun _ => Set.univ_nonempty) x (fun d _ => minCompRank_le x d)

/-- **Fact (a), restricted.** -/
lemma minCompRankR_subPattern_le (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F)
    (T : Finset n) : minCompRankR (restrictΩ Ω T) (subPattern x T) ≤ minCompRankR Ω x := by
  obtain ⟨d, hd, e⟩ := exists_minCompRankR hΩ x
  have hadm : Admissible (restrictΩ Ω T) (subPattern x T) (fun a : T => d a) :=
    fun a => by simpa [subPattern, restrictΩ] using hd a
  have eq : subPattern x T + diagonal (fun a : T => d a) =
      (x + diagonal d).submatrix (fun a : T => (a : n)) (fun a : T => (a : n)) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [subPattern]
    · have : (a : n) ≠ b := fun h => hab (Subtype.ext h)
      simp [subPattern, diagonal_apply_ne _ hab, diagonal_apply_ne _ this]
  calc _ ≤ _ := minCompRankR_le _ _ hadm
    _ = _ := by rw [eq]
    _ ≤ _ := rank_submatrix_le _ _ _
    _ = _ := e

/-- **Fact (b), restricted.** Off-diagonal blocks bound `c_Ω` from below. -/
lemma offDiag_rank_le_minCompRankR (hΩ : ∀ i, (Ω i).Nonempty) {α β : Type*} [Fintype β]
    (x : Matrix n n F) (r : α → n) (c : β → n) (h : ∀ a b, r a ≠ c b) :
    (x.submatrix r c).rank ≤ minCompRankR Ω x := by
  obtain ⟨d, -, hd⟩ := exists_minCompRankR hΩ x
  have e : x.submatrix r c = (x + diagonal d).submatrix r c := by
    ext a b; simp [diagonal_apply_ne _ (h a b)]
  rw [e, ← hd]; exact rank_submatrix_le _ _ _

/-- **Fact (c), restricted.** -/
lemma minCompRankR_le_erase_add_two (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F) (i : n) :
    minCompRankR Ω x ≤
      minCompRankR (restrictΩ Ω (univ.erase i)) (subPattern x (univ.erase i)) + 2 := by
  set T := univ.erase i
  have hΩT : ∀ a : T, (restrictΩ Ω T a).Nonempty := fun a => hΩ a
  obtain ⟨d, hd, hdr⟩ := exists_minCompRankR hΩT (subPattern x T)
  set d' : n → F := fun i => if h : i ∈ T then d ⟨i, h⟩ else (hΩ i).some - x i i
  have hadm : Admissible Ω x d' := by
    intro l
    by_cases h : l ∈ T
    · simpa [d', h, subPattern, restrictΩ] using hd ⟨l, h⟩
    · simpa [d', h] using (hΩ l).some_mem
  set M := x + diagonal d'
  set N := M.submatrix (fun r : T => (r : n)) id
  have h1 : M.rank ≤ N.rank + (univ \ T).card := rank_le_rank_submatrix_rows_add M T
  have h2 := rank_le_rank_submatrix_rows_add Nᵀ T
  rw [rank_transpose] at h2
  have e : Nᵀ.submatrix (fun r : T => (r : n)) id = (subPattern x T + diagonal d)ᵀ := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [N, M, d', subPattern]
    · have : (a : n) ≠ b := fun h => hab (Subtype.ext h)
      simp [N, M, subPattern, diagonal_apply_ne _ this, diagonal_apply_ne _ this.symm,
        diagonal_apply_ne _ hab, diagonal_apply_ne _ (Ne.symm hab)]
  rw [e, rank_transpose, hdr] at h2
  have hc : (univ \ T).card = 1 := by
    rw [sdiff_erase (mem_univ i), sdiff_self]; simp
  calc minCompRankR Ω x ≤ M.rank := minCompRankR_le x d' hadm
    _ ≤ _ := h1
    _ ≤ _ := by omega

/-- **Witness theorem with restricted diagonals** (any admissible completion of rank `q` gives
`T` with `|T| ≤ q + j`). -/
theorem witnessR (hΩ : ∀ i, (Ω i).Nonempty) (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j)
    (d0 : n → F) (hd0 : Admissible Ω x d0) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRankR (restrictΩ Ω T) (subPattern x T) = minCompRankR Ω x := by
  classical
  obtain ⟨T, X, hT, hXT, hcore⟩ := witness_core x j hcut d0
  refine ⟨T, hT, le_antisymm (minCompRankR_subPattern_le hΩ x T) ?_⟩
  have hΩT : ∀ a : T, (restrictΩ Ω T a).Nonempty := fun a => hΩ a
  apply le_minCompRankR hΩT
  intro d hd
  set e : n → F := fun i => if i ∈ X then d0 i else if h : i ∈ T then d ⟨i, h⟩ else 0
  have hadm : Admissible Ω x e := by
    intro i
    by_cases hX : i ∈ X
    · simpa [e, hX] using hd0 i
    · have hiT := hXT i hX
      simpa [e, hX, hiT, subPattern, restrictΩ] using hd ⟨i, hiT⟩
  exact (minCompRankR_le x e hadm).trans
    (hcore d e (fun i hi => by simp [e, hi]) (fun i h hX => by simp [e, hX, h]))

/-- **Theorem 3, bound part, with restricted diagonals.** A minimal obstruction to `c_Ω ≤ k`
has at most `2k + 2` indices. -/
theorem card_le_of_minimalR (hΩ : ∀ i, (Ω i).Nonempty) (k : ℕ) (x : Matrix n n F)
    (hk : k + 1 ≤ minCompRankR Ω x)
    (hmin : ∀ T : Finset n, T ≠ univ → minCompRankR (restrictΩ Ω T) (subPattern x T) ≤ k) :
    Fintype.card n ≤ 2 * k + 2 := by
  classical
  by_cases hcut : CutRankLE x k
  · obtain ⟨d, hd, hdr⟩ := exists_minCompRankR hΩ x
    obtain ⟨T, hT, hTc⟩ := witnessR hΩ x k hcut d hd
    rw [hdr] at hT
    have hTu : T = univ := by
      by_contra h; have := hmin T h; omega
    have hne : Nonempty n := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h0 := (minCompRankR_le x d hd).trans (rank_le_card_width _)
      rw [Fintype.card_eq_zero] at h0
      omega
    obtain ⟨i⟩ := hne
    have hc := minCompRankR_le_erase_add_two hΩ x i
    have hi := hmin (univ.erase i) (fun h => by
      have : i ∈ univ.erase i := by rw [h]; exact mem_univ i
      simp at this)
    rw [← card_univ, ← hTu]
    omega
  · simp only [CutRankLE, not_forall, not_le] at hcut
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
    have hΩT : ∀ a : T, (restrictΩ Ω T a).Nonempty := fun a => hΩ a
    have hTk : k + 1 ≤ minCompRankR (restrictΩ Ω T) (subPattern x T) := by
      refine le_trans hRC (le_of_eq_of_le ?_ (offDiag_rank_le_minCompRankR hΩT
        (subPattern x T) (fun a : R => (⟨a, hRT a⟩ : T)) (fun b : C => (⟨b, hCT b⟩ : T)) ?_))
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

/-- At `Ω = univ`, `witnessR` gives back Theorem 2 in the any-completion form. -/
theorem witness_of_completion_via_restricted (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j)
    (d0 : n → F) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRank (subPattern x T) = minCompRank x := by
  obtain ⟨T, h1, h2⟩ := witnessR (Ω := fun _ => (Set.univ : Set F))
    (fun _ => Set.univ_nonempty) x j hcut d0 (fun _ => Set.mem_univ _)
  refine ⟨T, h1, ?_⟩
  have e : restrictΩ (fun _ => (Set.univ : Set F)) T = fun _ => Set.univ := rfl
  rw [e, minCompRankR_univ, minCompRankR_univ] at h2
  exact h2

end Restricted

end FreeDiagonal
