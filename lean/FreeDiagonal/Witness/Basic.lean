import FreeDiagonal.Foundations.Union

/-!
# Witnessing rank with a free diagonal

Definitions, the elementary facts (a), (b), (c), the witness theorem (Theorem 2 of the note,
Part 51-b, proved by the short route of Part 51), the sharp threshold (Theorem 3) and the
sharpness example.

The matroid union theorem enters only through the hypothesis `UnionRankFormula F`
(defined in `Foundations/Union.lean`).
-/

open Matrix Module Submodule Finset

universe u v w

namespace FreeDiagonal

section Defs

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- `c(x)`: the least rank of a matrix agreeing with `x` off the diagonal. -/
noncomputable def minCompRank (x : Matrix n n F) : ℕ :=
  ⨅ d : n → F, (x + diagonal d).rank

/-- The sub-pattern `x_T`: restriction of `x` to rows and columns in `T`. -/
def subPattern (x : Matrix n n F) (T : Finset n) : Matrix T T F :=
  x.submatrix (fun a : T => (a : n)) (fun b : T => (b : n))

/-- All cut ranks `rank x[A, Aᶜ]` are at most `j`. -/
def CutRankLE (x : Matrix n n F) (j : ℕ) : Prop :=
  ∀ A : Finset n, (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank ≤ j

lemma minCompRank_le (x : Matrix n n F) (d : n → F) :
    minCompRank x ≤ (x + diagonal d).rank :=
  ciInf_le (OrderBot.bddBelow _) d

lemma exists_minCompRank (x : Matrix n n F) :
    ∃ d : n → F, (x + diagonal d).rank = minCompRank x := by
  have h : minCompRank x ∈ Set.range (fun d : n → F => (x + diagonal d).rank) := by
    unfold minCompRank; exact Nat.sInf_mem (Set.range_nonempty _)
  obtain ⟨d, hd⟩ := h
  exact ⟨d, hd⟩

lemma le_minCompRank (x : Matrix n n F) {r : ℕ} (h : ∀ d : n → F, r ≤ (x + diagonal d).rank) :
    r ≤ minCompRank x :=
  le_ciInf h

/-- `c` only sees off-diagonal entries, and does not increase under injective reindexing. -/
lemma minCompRank_le_of_embedding {m : Type*} [Fintype m] [DecidableEq m] (x : Matrix n n F)
    (y : Matrix m m F) (f : m → n) (hf : Function.Injective f)
    (hy : ∀ a b, a ≠ b → y a b = x (f a) (f b)) : minCompRank y ≤ minCompRank x := by
  obtain ⟨d, hd⟩ := exists_minCompRank x
  set d' : m → F := fun a => x (f a) (f a) + d (f a) - y a a
  have e : y + diagonal d' = (x + diagonal d).submatrix f f := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [d']
    · have : f a ≠ f b := fun h => hab (hf h)
      simp [diagonal_apply_ne _ hab, diagonal_apply_ne _ this, hy a b hab]
  calc minCompRank y ≤ (y + diagonal d').rank := minCompRank_le y d'
    _ = ((x + diagonal d).submatrix f f).rank := by rw [e]
    _ ≤ (x + diagonal d).rank := rank_submatrix_le _ _ _
    _ = minCompRank x := hd

/-- **Fact (a).** `c(x_T) ≤ c(x)`. -/
lemma minCompRank_subPattern_le (x : Matrix n n F) (T : Finset n) :
    minCompRank (subPattern x T) ≤ minCompRank x :=
  minCompRank_le_of_embedding x _ _ Subtype.val_injective (fun _ _ _ => rfl)

lemma minCompRank_le_subPattern_univ (x : Matrix n n F) :
    minCompRank x ≤ minCompRank (subPattern x univ) :=
  minCompRank_le_of_embedding (subPattern x univ) x (fun i => ⟨i, mem_univ i⟩)
    (fun _ _ h => by simpa using h) (fun _ _ _ => rfl)

/-- **Fact (b), general form.** Every off-diagonal block bounds `c(x)` from below. -/
lemma offDiag_rank_le_minCompRank {α β : Type*} [Fintype β] (x : Matrix n n F) (r : α → n)
    (c : β → n) (h : ∀ a b, r a ≠ c b) : (x.submatrix r c).rank ≤ minCompRank x := by
  obtain ⟨d, hd⟩ := exists_minCompRank x
  have e : x.submatrix r c = (x + diagonal d).submatrix r c := by
    ext a b; simp [diagonal_apply_ne _ (h a b)]
  rw [e, ← hd]; exact rank_submatrix_le _ _ _

/-- **Fact (b).** Every cut rank is at most `c(x)`. -/
lemma cutRank_le_minCompRank (x : Matrix n n F) (A : Finset n) :
    (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank ≤ minCompRank x :=
  offDiag_rank_le_minCompRank x _ _ (fun a b h => (mem_compl.1 b.2) (h ▸ a.2))

lemma cutRankLE_minCompRank (x : Matrix n n F) : CutRankLE x (minCompRank x) :=
  cutRank_le_minCompRank x

lemma rank_submatrix_cols_eq_frk {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k F)
    (C : Finset k) : (M.submatrix id (fun c : C => (c : k))).rank = frk F M.col C := by
  rw [← rank_transpose]; exact rank_submatrix_rows_eq_frk Mᵀ C

/-- **Fact (c), general form.** Removing the indices outside `T` lowers `c` by at most
`2 |Tᶜ|`. -/
lemma minCompRank_le_subPattern_add (x : Matrix n n F) (T : Finset n) :
    minCompRank x ≤ minCompRank (subPattern x T) + 2 * (univ \ T).card := by
  obtain ⟨d, hd⟩ := exists_minCompRank (subPattern x T)
  set d' : n → F := fun i => if h : i ∈ T then d ⟨i, h⟩ else 0
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
  rw [e, rank_transpose, hd] at h2
  calc minCompRank x ≤ M.rank := minCompRank_le x d'
    _ ≤ _ := h1
    _ ≤ _ := by omega

/-- **Fact (c).** Adding one index raises `c` by at most 2. -/
lemma minCompRank_le_erase_add_two (x : Matrix n n F) (i : n) :
    minCompRank x ≤ minCompRank (subPattern x (univ.erase i)) + 2 := by
  have h := minCompRank_le_subPattern_add x (univ.erase i)
  have : (univ \ univ.erase i).card = 1 := by
    rw [sdiff_erase (mem_univ i), sdiff_self]; simp
  rw [this] at h; simpa using h

end Defs

/-! ### Theorem 2: the witness theorem -/

section Witness

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma one_submatrix_mul {α m k : Type*} [Fintype m] [DecidableEq m] (r : α → m)
    (M : Matrix m k F) : (1 : Matrix m m F).submatrix r id * M = M.submatrix r id := by
  ext a b; rw [Matrix.mul_apply]; simp [Matrix.one_apply]

omit [DecidableEq n] in
lemma mul_one_submatrix {β m k : Type*} [Fintype k] [DecidableEq k] (c : β → k)
    (M : Matrix m k F) : M * (1 : Matrix k k F).submatrix id c = M.submatrix id c := by
  ext a b; rw [Matrix.mul_apply]; simp [Matrix.one_apply]

/-- **Step 1** (Frobenius form, on `G` directly). For any completion `G` and any `A`,
`rk(rows A) + rk(cols Aᶜ) ≤ rank G + rank G[A, Aᶜ]`, and `G[A, Aᶜ] = x[A, Aᶜ]`. -/
lemma rows_add_cols_le (x : Matrix n n F) (d0 : n → F) (A : Finset n) :
    frk F (x + diagonal d0).row A + frk F (x + diagonal d0).col Aᶜ ≤
      (x + diagonal d0).rank +
        (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank := by
  set G := x + diagonal d0
  have hfr := rank_frobenius ((1 : Matrix n n F).submatrix (fun a : A => (a : n)) id) G
    ((1 : Matrix n n F).submatrix id (fun b : ↥(Aᶜ) => (b : n)))
  rw [one_submatrix_mul, mul_one_submatrix, mul_one_submatrix] at hfr
  have ecut : (G.submatrix (fun a : A => (a : n)) id).submatrix id (fun b : ↥(Aᶜ) => (b : n)) =
      x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n)) := by
    ext a b
    have : (a : n) ≠ b := fun h => (mem_compl.1 b.2) (h ▸ a.2)
    simp [G, diagonal_apply_ne _ this]
  rw [ecut, rank_submatrix_rows_eq_frk, rank_submatrix_cols_eq_frk] at hfr
  exact hfr

/-- **Theorem 2 (witness theorem), any completion** (Part 51-b; Theorem 2 of the note together
with its first remark). If all cut ranks of `x` are at most `j` and `G = x + diagonal d0` is any
completion, there is `T` with `|T| ≤ rank G + j` and `c(x_T) = c(x)`. -/
theorem witness_of_completion (hU : UnionRankFormula.{u, v, max u v} F) (x : Matrix n n F)
    (j : ℕ) (hcut : CutRankLE x j) (d0 : n → F) :
    ∃ T : Finset n, T.card ≤ (x + diagonal d0).rank + j ∧
      minCompRank (subPattern x T) = minCompRank x := by
  classical
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
  refine ⟨T, ?_, ?_⟩
  · -- the size bound
    calc T.card ≤ ((univ \ X) ∪ I1).card + I2.card := card_union_le _ _
      _ ≤ (univ \ X).card + I1.card + I2.card := by gcongr; exact card_union_le _ _
      _ = fX X := by simp only [fX]; rw [hI1c, hI2c, eA, eC]
      _ ≤ G.rank + j := hXf
  -- Steps 3 and 4, short form: `c(x_T) ≥ c(x)`
  apply le_antisymm (minCompRank_subPattern_le x T)
  apply le_minCompRank
  intro d
  set R := (univ \ X) ∪ I1
  set C := (univ \ X) ∪ I2
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => mem_union_left _ hr
  have hCT : ∀ s ∈ C, s ∈ T := fun s hs => by
    rcases mem_union.1 hs with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_right _ h
  set d' : n → F := fun i => if i ∈ X then d0 i else if h : i ∈ T then d ⟨i, h⟩ else 0
  set H := x + diagonal d'
  have hrowX : ∀ i ∈ X, H.row i = G.row i := by
    intro i hi; ext s
    by_cases h : i = s
    · subst h; simp [H, G, d', hi]
    · simp [H, G, diagonal_apply_ne _ h]
  have hcolX : ∀ s ∈ X, H.col s = G.col s := by
    intro s hs; ext r
    by_cases h : r = s
    · subst h; simp [H, G, d', hs]
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
      simp [H, d', hrX, subPattern, hRT r hr]
    · have hne : (⟨r, hRT r hr⟩ : T) ≠ ⟨s, hCT s hs⟩ := fun h => hrs (congrArg Subtype.val h)
      simp [H, subPattern, diagonal_apply_ne _ hrs, diagonal_apply_ne _ hne]
  calc minCompRank x ≤ H.rank := minCompRank_le x d'
    _ ≤ _ := key
    _ = _ := by rw [e]
    _ ≤ _ := rank_submatrix_le _ _ _

/-- **Theorem 2 (witness theorem).** If all cut ranks of `x` are at most `j`, some `T` with
`|T| ≤ c(x) + j` has `c(x_T) = c(x)`. -/
theorem witness (hU : UnionRankFormula.{u, v, max u v} F) (x : Matrix n n F) (j : ℕ)
    (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ minCompRank x + j ∧
      minCompRank (subPattern x T) = minCompRank x := by
  obtain ⟨d, hd⟩ := exists_minCompRank x
  obtain ⟨T, h1, h2⟩ := witness_of_completion hU x j hcut d
  exact ⟨T, hd ▸ h1, h2⟩

/-- **Theorem 2, "in particular".** Some `T` with `|T| ≤ 2 c(x)` has `c(x_T) = c(x)`. -/
theorem witness_two_mul (hU : UnionRankFormula.{u, v, max u v} F) (x : Matrix n n F) :
    ∃ T : Finset n, T.card ≤ 2 * minCompRank x ∧
      minCompRank (subPattern x T) = minCompRank x := by
  obtain ⟨T, h1, h2⟩ := witness hU x _ (cutRankLE_minCompRank x)
  exact ⟨T, by omega, h2⟩

end Witness

end FreeDiagonal
