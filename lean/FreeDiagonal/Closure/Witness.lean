import FreeDiagonal.Closure.Pivot
import FreeDiagonal.Witness.Restricted

/-!
# Task B1: the witness theorem for closure rank (U6 Theorem A; Part 47; Part 48)

`closure_core`: the Part 51 construction for a matrix `H` and its dial settings. It produces
`T ⊇ B` with `|T| ≤ rank H + j`, where `B` is any set whose rows and columns are independent.
Every dial setting deleting the indices outside `T` then costs at least `|Tᶜ|` plus the cost of
some dial setting. Deletions inside `T` are paid for: each removes one row or one column of the
key block.

`closure_witness`: pivot on an optimal deletion set `D*` (the optimum becomes the finite matrix
`pivot G D*`), apply `closure_core` with `B = D*`, and translate back.

Any field; the pattern need not be symmetric.
-/

open Matrix Module Submodule Finset

universe u v

namespace FreeDiagonal

section Bases

variable {F : Type*} [Field F] {ι V : Type*} [AddCommGroup V] [Module F V]

/-- An independent subfamily extends to a basis inside a larger set. -/
lemma exists_basis_superset [DecidableEq ι] (f : ι → V) {J S : Finset ι} (hJS : J ⊆ S)
    (hJ : frk F f J = J.card) :
    ∃ I, J ⊆ I ∧ I ⊆ S ∧ I.card = frk F f S ∧
      span F (f '' (I : Set ι)) = span F (f '' (S : Set ι)) := by
  classical
  have hli : LinearIndepOn F f (J : Set ι) := by
    show LinearIndependent F (fun i : (J : Set ι) => f i)
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [← Set.image_eq_range]
    unfold frk at hJ
    unfold Set.finrank
    simpa using hJ.symm
  obtain ⟨b, hbS, hJb, hspan, hlib⟩ :=
    exists_linearIndepOn_extension (K := F) (v := f) hli (coe_subset.2 hJS)
  set I : Finset ι := S.filter (· ∈ b) with hI
  have hIb : (I : Set ι) = b := by
    ext i; simp only [hI, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hbS h, h⟩⟩
  have hsp : span F (f '' (I : Set ι)) = span F (f '' (S : Set ι)) := by
    apply le_antisymm
    · exact span_mono (Set.image_mono (fun x hx => (Finset.mem_filter.1 hx).1))
    · rw [hIb]; exact span_le.2 hspan
  refine ⟨I, fun i hi => ?_, fun i hi => (mem_filter.1 hi).1, ?_, hsp⟩
  · have : i ∈ (I : Set ι) := by rw [hIb]; exact hJb hi
    exact this
  · unfold frk
    rw [← hsp]
    have hli' : LinearIndependent F (fun i : (I : Set ι) => f i) := by rw [hIb]; exact hlib
    have := finrank_span_eq_card hli'
    rw [← Set.image_eq_range] at this
    rw [this]
    simp

end Bases

section Sub

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- Finset-indexed submatrix. -/
abbrev subM (M : Matrix n n F) (R C : Finset n) : Matrix R C F :=
  M.submatrix (fun a : R => (a : n)) (fun b : C => (b : n))

lemma rank_subM_mono (M : Matrix n n F) {R R' C C' : Finset n} (hR : R ⊆ R') (hC : C ⊆ C') :
    (subM M R C).rank ≤ (subM M R' C').rank := by
  have : subM M R C = (subM M R' C').submatrix (fun a : R => (⟨a.1, hR a.2⟩ : R'))
      (fun b : C => (⟨b.1, hC b.2⟩ : C')) := rfl
  rw [this]; exact rank_submatrix_le _ _ _

lemma rank_subM_rows (M : Matrix n n F) {R R' : Finset n} (C : Finset n) (h : R' ⊆ R) :
    (subM M R C).rank ≤ (subM M R' C).rank + (R \ R').card := by
  classical
  set Rf : Finset ↥R := univ.filter fun a => a.1 ∈ R'
  have h1 := rank_le_rank_submatrix_rows_add (subM M R C) Rf
  have h2 : ((subM M R C).submatrix (fun a : Rf => (a : ↥R)) id).rank ≤ (subM M R' C).rank := by
    have : (subM M R C).submatrix (fun a : Rf => (a : ↥R)) id =
        (subM M R' C).submatrix (fun a : Rf => (⟨a.1.1, (mem_filter.1 a.2).2⟩ : R')) id := rfl
    rw [this]; exact rank_submatrix_le _ _ _
  have h3 : (univ \ Rf).card ≤ (R \ R').card := by
    apply Finset.card_le_card_of_injOn (fun a : ↥R => a.1)
    · intro a ha
      simp only [Rf, Finset.mem_coe, mem_sdiff, mem_univ, true_and, mem_filter] at ha
      exact mem_sdiff.2 ⟨a.2, ha⟩
    · intro a _ b _ hab; exact Subtype.ext hab
  omega

lemma rank_subM_cols (M : Matrix n n F) (R : Finset n) {C C' : Finset n} (h : C' ⊆ C) :
    (subM M R C).rank ≤ (subM M R C').rank + (C \ C').card := by
  have h1 := rank_subM_rows Mᵀ R h
  rw [← rank_transpose (subM M R C), ← rank_transpose (subM M R C')]
  exact h1

end Sub

section Core

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- **The Part 51 construction for dial settings.** -/
theorem closure_core (H : Matrix n n F) (j : ℕ) (hcut : CutRankLE H j) (B : Finset n)
    (hBr : frk F H.row B = B.card) (hBc : frk F H.col B = B.card) :
    ∃ T : Finset n, B ⊆ T ∧ T.card ≤ H.rank + j ∧
      ∀ l : n → Option F, (∀ i ∉ T, l i = none) →
        ∃ e : n → Option F, (univ \ T).card + (dialMat H e).rank ≤ (dialMat H l).rank := by
  classical
  have hU := unionRankFormula.{u, v, max u v} F
  have hH0 : H + diagonal (0 : n → F) = H := by simp
  -- Step 1
  have step1 : ∀ A : Finset n, frk F H.row A + frk F H.col (univ \ A) ≤ H.rank + j := by
    intro A
    rw [← compl_eq_univ_sdiff]
    have := rows_add_cols_le H 0 A
    rw [hH0] at this
    exact this.trans (Nat.add_le_add_left (hcut A) _)
  -- Step 2
  set fX : Finset n → ℕ := fun X => (univ \ X).card + frk F H.row X + frk F H.col X
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset (Finset n)) fX univ_nonempty
  obtain ⟨A0, -, X0, -, h0⟩ := hU n (n → F) H.row H.col univ
  have hX : fX X ≤ H.rank + j := (hXmin X0 (mem_univ _)).trans (h0.trans (step1 A0))
  obtain ⟨A', hA'X, X'', hX''X, h1⟩ := hU n (n → F) H.row H.col X
  have h2 := hXmin X'' (mem_univ _)
  have hXf : fX X ≤ H.rank + j := hX
  have hc2 := card_sdiff_add_card_eq_card (subset_univ X)
  have hc3 := card_sdiff_add_card_eq_card (subset_univ X'')
  have hc4 := card_sdiff_add_card_eq_card hX''X
  have m1 := frk_mono (F := F) H.row hA'X
  have m2 := frk_mono (F := F) H.col (sdiff_subset : X \ A' ⊆ X)
  simp only [fX] at hX h2
  have eA : frk F H.row A' = frk F H.row X := by omega
  have eC : frk F H.col (X \ A') = frk F H.col X := by omega
  have spA : span F (H.row '' (A' : Set n)) = span F (H.row '' (X : Set n)) :=
    Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (coe_subset.2 hA'X))) eA
  have spC : span F (H.col '' ((X \ A' : Finset n) : Set n)) = span F (H.col '' (X : Set n)) :=
    Submodule.eq_of_le_of_finrank_eq
      (span_mono (Set.image_mono (coe_subset.2 sdiff_subset))) eC
  -- bases containing the forced set
  have hJ1 : frk F H.row (B ∩ A') = (B ∩ A').card :=
    frk_eq_card_of_subset H.row inter_subset_left hBr
  have hJ2 : frk F H.col (B ∩ (X \ A')) = (B ∩ (X \ A')).card :=
    frk_eq_card_of_subset H.col inter_subset_left hBc
  obtain ⟨I1, hJI1, hI1, hI1c, hI1s⟩ := exists_basis_superset H.row inter_subset_right hJ1
  obtain ⟨I2, hJI2, hI2, hI2c, hI2s⟩ := exists_basis_superset H.col inter_subset_right hJ2
  have hI1X : ∀ i ∈ I1, i ∈ X := fun i hi => hA'X (hI1 hi)
  have hI2X : ∀ i ∈ I2, i ∈ X := fun i hi => (mem_sdiff.1 (hI2 hi)).1
  have hdisj : ∀ i, i ∈ I1 → i ∈ I2 → False :=
    fun i h1 h2 => (mem_sdiff.1 (hI2 h2)).2 (hI1 h1)
  set T := (univ \ X) ∪ I1 ∪ I2 with hT
  have hmemT : ∀ i, i ∈ T ↔ i ∉ X ∨ i ∈ I1 ∨ i ∈ I2 := by
    intro i; simp [hT, or_assoc]
  refine ⟨T, ?_, ?_, ?_⟩
  · intro b hb
    rw [hmemT]
    by_cases hbX : b ∈ X
    · by_cases hbA : b ∈ A'
      · exact Or.inr (Or.inl (hJI1 (mem_inter.2 ⟨hb, hbA⟩)))
      · exact Or.inr (Or.inr (hJI2 (mem_inter.2 ⟨hb, mem_sdiff.2 ⟨hbX, hbA⟩⟩)))
    · exact Or.inl hbX
  · calc T.card ≤ ((univ \ X) ∪ I1).card + I2.card := card_union_le _ _
      _ ≤ (univ \ X).card + I1.card + I2.card := by gcongr; exact card_union_le _ _
      _ = fX X := by simp only [fX]; rw [hI1c, hI2c, eA, eC]
      _ ≤ H.rank + j := hXf
  -- Step 3
  intro l hl
  set e : n → Option F := fun i => if i ∈ X then some 0 else l i with he
  refine ⟨e, ?_⟩
  set Ne : Finset n := univ.filter fun i => e i = none
  set Nl : Finset n := univ.filter fun i => l i = none
  set Ze := dialMat H e
  set Zl := dialMat H l
  have heX : ∀ i ∈ X, e i = some 0 := fun i hi => by simp [he, hi]
  have heY : ∀ i ∉ X, e i = l i := fun i hi => by simp [he, hi]
  -- (1), (2): unit rows split off
  have r1 : Ze.rank = Ne.card + (subM Ze Neᶜ Neᶜ).rank :=
    rank_unit_rows Ze Ne (fun i hi j => dialMat_none_row (mem_filter.1 hi).2 j)
  have r2 : Zl.rank = Nl.card + (subM Zl Nlᶜ Nlᶜ).rank :=
    rank_unit_rows Zl Nl (fun i hi j => dialMat_none_row (mem_filter.1 hi).2 j)
  -- the index sets
  set Ys : Finset n := (univ \ X) ∩ Neᶜ
  set R := Ys ∪ I1
  set C := Ys ∪ I2
  set R0 := Ys ∪ (I1 \ Nl)
  set C0 := Ys ∪ (I2 \ Nl)
  have hXNe : ∀ i ∈ X, i ∈ Neᶜ := fun i hi => by simp [Ne, heX i hi]
  have hRS : R ⊆ Neᶜ := union_subset inter_subset_right (fun i hi => hXNe i (hI1X i hi))
  have hCS : C ⊆ Neᶜ := union_subset inter_subset_right (fun i hi => hXNe i (hI2X i hi))
  -- entries of `Ze` touching `X`
  have hZeX : ∀ i ∈ X, ∀ k ∈ Neᶜ, Ze i k = H i k := by
    intro i hi k hk
    have hk' : e k ≠ none := by simpa [Ne] using hk
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hk'
    show dialMat H e i k = H i k
    rw [dialMat_some (heX i hi) ht]; simp
  have hZeXc : ∀ s ∈ X, ∀ r ∈ Neᶜ, Ze r s = H r s := by
    intro s hs r hr
    have hr' : e r ≠ none := by simpa [Ne] using hr
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hr'
    show dialMat H e r s = H r s
    rw [dialMat_some ht (heX s hs)]
    by_cases hrs : r = s
    · subst hrs; rw [heX r hs] at ht; cases ht; simp
    · simp [hrs]
  -- (3) span argument inside `Neᶜ`
  have s3 : (subM Ze Neᶜ Neᶜ).rank ≤ (subM Ze R C).rank := by
    set M := subM Ze Neᶜ Neᶜ
    set R' : Finset ↥(Neᶜ) := univ.filter fun a => a.1 ∈ R
    set C' : Finset ↥(Neᶜ) := univ.filter fun a => a.1 ∈ C
    have hrowH : ∀ i (hi : i ∈ X), M.row ⟨i, hXNe i hi⟩ =
        LinearMap.funLeft F F (fun a : ↥(Neᶜ) => (a : n)) (H.row i) := by
      intro i hi; ext k; exact hZeX i hi k k.2
    have hcolH : ∀ s (hs : s ∈ X), M.col ⟨s, hXNe s hs⟩ =
        LinearMap.funLeft F F (fun a : ↥(Neᶜ) => (a : n)) (H.col s) := by
      intro s hs; ext r; exact hZeXc s hs r r.2
    have hR : ∀ i, M.row i ∈ span F (M.row '' (R' : Set ↥(Neᶜ))) := by
      intro i
      by_cases hiR : i.1 ∈ R
      · exact subset_span ⟨i, by simp [R', hiR], rfl⟩
      · have hiX : i.1 ∈ X := by
          by_contra h
          exact hiR (mem_union_left _ (mem_inter.2 ⟨mem_sdiff.2 ⟨mem_univ _, h⟩, i.2⟩))
        have hH : H.row i.1 ∈ span F (H.row '' (I1 : Set n)) := by
          rw [hI1s, spA]; exact subset_span ⟨i.1, hiX, rfl⟩
        have := Submodule.apply_mem_span_image_of_mem_span
          (LinearMap.funLeft F F (fun a : ↥(Neᶜ) => (a : n))) hH
        have e1 : M.row i = LinearMap.funLeft F F (fun a : ↥(Neᶜ) => (a : n)) (H.row i.1) :=
          hrowH i.1 hiX
        rw [e1]
        refine span_mono ?_ this
        rintro _ ⟨_, ⟨l', hl', rfl⟩, rfl⟩
        refine ⟨⟨l', hXNe l' (hI1X l' hl')⟩, by simp [R', R]; exact Or.inr hl', ?_⟩
        exact (hrowH l' (hI1X l' hl')).symm ▸ rfl
    have hC : ∀ s, M.col s ∈ span F (M.col '' (C' : Set ↥(Neᶜ))) := by
      intro s
      by_cases hsC : s.1 ∈ C
      · exact subset_span ⟨s, by simp [C', hsC], rfl⟩
      · have hsX : s.1 ∈ X := by
          by_contra h
          exact hsC (mem_union_left _ (mem_inter.2 ⟨mem_sdiff.2 ⟨mem_univ _, h⟩, s.2⟩))
        have hH : H.col s.1 ∈ span F (H.col '' (I2 : Set n)) := by
          rw [hI2s, spC]; exact subset_span ⟨s.1, hsX, rfl⟩
        have := Submodule.apply_mem_span_image_of_mem_span
          (LinearMap.funLeft F F (fun a : ↥(Neᶜ) => (a : n))) hH
        rw [hcolH s.1 hsX]
        refine span_mono ?_ this
        rintro _ ⟨_, ⟨l', hl', rfl⟩, rfl⟩
        refine ⟨⟨l', hXNe l' (hI2X l' hl')⟩, by simp [C', C]; exact Or.inr hl', ?_⟩
        exact (hcolH l' (hI2X l' hl')).symm ▸ rfl
    have key := rank_le_submatrix_of_span M R' C' hR hC
    refine key.trans ?_
    have : M.submatrix (fun a : R' => (a : ↥(Neᶜ))) (fun b : C' => (b : ↥(Neᶜ))) =
        (subM Ze R C).submatrix (fun a : R' => (⟨a.1.1, (mem_filter.1 a.2).2⟩ : R))
          (fun b : C' => (⟨b.1.1, (mem_filter.1 b.2).2⟩ : C)) := rfl
    rw [this]; exact rank_submatrix_le _ _ _
  -- (4) removing the rows `I1 ∩ Nl` and the columns `I2 ∩ Nl`
  have hR0 : R0 ⊆ R := union_subset_union_right sdiff_subset
  have hC0 : C0 ⊆ C := union_subset_union_right sdiff_subset
  have hRR0 : R \ R0 ⊆ I1 ∩ Nl := by
    intro i hi
    simp only [R, R0, mem_sdiff, mem_union, not_or] at hi
    rcases hi.1 with h | h
    · exact absurd h hi.2.1
    · exact mem_inter.2 ⟨h, by by_contra hn; exact hi.2.2 ⟨h, hn⟩⟩
  have hCC0 : C \ C0 ⊆ I2 ∩ Nl := by
    intro i hi
    simp only [C, C0, mem_sdiff, mem_union, not_or] at hi
    rcases hi.1 with h | h
    · exact absurd h hi.2.1
    · exact mem_inter.2 ⟨h, by by_contra hn; exact hi.2.2 ⟨h, hn⟩⟩
  have s4 : (subM Ze R C).rank ≤ (subM Ze R0 C0).rank + (I1 ∩ Nl).card + (I2 ∩ Nl).card := by
    have a1 := rank_subM_rows Ze C hR0
    have a2 := rank_subM_cols Ze R0 hC0
    have b1 := card_le_card hRR0
    have b2 := card_le_card hCC0
    omega
  -- (5) the common block
  have hYsNl : ∀ i ∈ Ys, i ∉ X ∧ l i ≠ none := by
    intro i hi
    have h1 := (mem_sdiff.1 (mem_inter.1 hi).1).2
    have h2 := (mem_inter.1 hi).2
    refine ⟨h1, fun hn => ?_⟩
    have : e i = none := by rw [heY i h1, hn]
    exact (mem_compl.1 h2) (by simp [Ne, this])
  have s5 : subM Ze R0 C0 = subM Zl R0 C0 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp only [subM, submatrix_apply]
    have hr' : e r = l r ∨ (r ∈ I1 ∧ l r ≠ none) := by
      rcases mem_union.1 hr with h | h
      · exact Or.inl (heY r (hYsNl r h).1)
      · exact Or.inr ⟨(mem_sdiff.1 h).1, fun hn => (mem_sdiff.1 h).2 (by simp [Nl, hn])⟩
    have hs' : e s = l s ∨ (s ∈ I2 ∧ l s ≠ none) := by
      rcases mem_union.1 hs with h | h
      · exact Or.inl (heY s (hYsNl s h).1)
      · exact Or.inr ⟨(mem_sdiff.1 h).1, fun hn => (mem_sdiff.1 h).2 (by simp [Nl, hn])⟩
    have hlr : l r ≠ none := by
      rcases mem_union.1 hr with h | h
      · exact (hYsNl r h).2
      · exact fun hn => (mem_sdiff.1 h).2 (by simp [Nl, hn])
    have hls : l s ≠ none := by
      rcases mem_union.1 hs with h | h
      · exact (hYsNl s h).2
      · exact fun hn => (mem_sdiff.1 h).2 (by simp [Nl, hn])
    obtain ⟨tl, htl⟩ := Option.ne_none_iff_exists'.1 hlr
    obtain ⟨sl, hsl⟩ := Option.ne_none_iff_exists'.1 hls
    have her : ∃ te, e r = some te := by
      rcases hr' with h | ⟨h, -⟩
      · exact ⟨tl, h.trans htl⟩
      · exact ⟨0, heX r (hI1X r h)⟩
    have hes : ∃ se, e s = some se := by
      rcases hs' with h | ⟨h, -⟩
      · exact ⟨sl, h.trans hsl⟩
      · exact ⟨0, heX s (hI2X s h)⟩
    obtain ⟨te, hte⟩ := her
    obtain ⟨se, hse⟩ := hes
    rw [show Ze r s = dialMat H e r s from rfl, show Zl r s = dialMat H l r s from rfl,
      dialMat_some hte hse, dialMat_some htl hsl]
    by_cases hrs : r = s
    · subst hrs
      -- `r` lies in `Ys`, where `e = l`
      have hrY : r ∈ Ys := by
        rcases mem_union.1 hr with h | h
        · exact h
        · rcases mem_union.1 hs with h' | h'
          · exact h'
          · exact absurd (mem_sdiff.1 h').1 (fun h2 => hdisj r (mem_sdiff.1 h).1 h2)
      have := heY r (hYsNl r hrY).1
      rw [hte, htl] at this
      cases this
      rfl
    · simp [hrs]
  -- (6)
  have hR0Nl : R0 ⊆ Nlᶜ := by
    intro i hi
    rcases mem_union.1 hi with h | h
    · exact mem_compl.2 (by simp [Nl, (hYsNl i h).2])
    · exact mem_compl.2 (fun h' => (mem_sdiff.1 h).2 h')
  have hC0Nl : C0 ⊆ Nlᶜ := by
    intro i hi
    rcases mem_union.1 hi with h | h
    · exact mem_compl.2 (by simp [Nl, (hYsNl i h).2])
    · exact mem_compl.2 (fun h' => (mem_sdiff.1 h).2 h')
  have s6 : (subM Zl R0 C0).rank ≤ (subM Zl Nlᶜ Nlᶜ).rank := rank_subM_mono Zl hR0Nl hC0Nl
  -- (7) counting deleted indices
  have s7 : (univ \ T).card + Ne.card + (I1 ∩ Nl).card + (I2 ∩ Nl).card ≤ Nl.card := by
    have hP : univ \ T ⊆ Nl := fun i hi => by
      simp [Nl, hl i (mem_sdiff.1 hi).2]
    have hNe : Ne ⊆ Nl := fun i hi => by
      have h := (mem_filter.1 hi).2
      by_cases hiX : i ∈ X
      · rw [heX i hiX] at h; cases h
      · rw [heY i hiX] at h; simp [Nl, h]
    have d1 : Disjoint (univ \ T) Ne := disjoint_left.2 fun i hi hi' => by
      have h := (mem_filter.1 hi').2
      by_cases hiX : i ∈ X
      · rw [heX i hiX] at h; cases h
      · exact (mem_sdiff.1 hi).2 ((hmemT i).2 (Or.inl hiX))
    have d2 : Disjoint ((univ \ T) ∪ Ne) (I1 ∩ Nl) := disjoint_left.2 fun i hi hi' => by
      have hI := (mem_inter.1 hi').1
      rcases mem_union.1 hi with h | h
      · exact (mem_sdiff.1 h).2 ((hmemT i).2 (Or.inr (Or.inl hI)))
      · have h' := (mem_filter.1 h).2
        rw [heX i (hI1X i hI)] at h'; cases h'
    have d3 : Disjoint ((univ \ T) ∪ Ne ∪ (I1 ∩ Nl)) (I2 ∩ Nl) := disjoint_left.2 fun i hi hi' => by
      have hI := (mem_inter.1 hi').1
      rcases mem_union.1 hi with h | h
      · rcases mem_union.1 h with h | h
        · exact (mem_sdiff.1 h).2 ((hmemT i).2 (Or.inr (Or.inr hI)))
        · have h' := (mem_filter.1 h).2
          rw [heX i (hI2X i hI)] at h'; cases h'
      · exact hdisj i (mem_inter.1 h).1 hI
    have hsub : (univ \ T) ∪ Ne ∪ (I1 ∩ Nl) ∪ (I2 ∩ Nl) ⊆ Nl :=
      union_subset (union_subset (union_subset hP hNe) inter_subset_right) inter_subset_right
    have := card_le_card hsub
    rw [card_union_of_disjoint d3, card_union_of_disjoint d2, card_union_of_disjoint d1] at this
    exact this
  rw [r1, r2]
  rw [s5] at s4
  omega

end Core

section Main

variable {F : Type u} [Field F] {n : Type v} [Fintype n] [DecidableEq n]

/-- **Task B1: the witness theorem for closure rank** (U6 Theorem A; Part 47 Witness Lemma;
Part 48 for non-symmetric patterns). Over ANY field: if every cut rank of `x` is at most `j`,
some `T` with `|T| ≤ ρ(x) + j` has `ρ(x_T) = ρ(x)`. -/
theorem closure_witness (x : Matrix n n F) (j : ℕ) (hcut : CutRankLE x j) :
    ∃ T : Finset n, T.card ≤ closRank x + j ∧ closRank (subPattern x T) = closRank x := by
  classical
  obtain ⟨D, hD⟩ := exists_closRank x
  obtain ⟨g0, hg0⟩ := exists_minCompRank (subPattern x Dᶜ)
  obtain ⟨e0, he0⟩ := exists_pivotOK x D
  set g : n → F := fun i => if h : i ∈ D then e0 i else g0 ⟨i, mem_compl.2 h⟩
  set G := x + diagonal g
  have hOK : PivotOK G D := by
    intro v hv hGv
    apply he0 v hv
    intro i hi
    have := hGv i hi
    simp only [G, add_mulVec, mulVec_diagonal, Pi.add_apply] at this ⊢
    have hg : g i = e0 i := by simp [g, hi]
    rwa [hg] at this
  -- the optimum as a dial setting
  set dstar : n → Option F := fun i => if i ∈ D then none else some 0
  have hdstar : ∀ i, dstar i = none ↔ i ∈ D := fun i => by by_cases h : i ∈ D <;> simp [dstar, h]
  have hstar : (dialMat G dstar).rank = closRank x := by
    rw [rank_dialMat_eq x g dstar D hdstar]
    have : (fun a : ↥(Dᶜ) => g a - (dstar a).getD 0) = g0 := by
      funext a
      have ha : (a : n) ∉ D := mem_compl.1 a.2
      simp [g, dstar, ha]
    rw [this, hg0, hD]
  have hrank : (pivot G D).rank = closRank x := by
    have h := rank_dialMat_pivot hOK dstar
    have e : pivDial D dstar = fun _ => some 0 := by
      funext i; by_cases h : i ∈ D <;> simp [pivDial, dstar, h, flip]
    rw [e, dialMat_some_zero] at h
    rw [h, hstar]
  have hcut' : CutRankLE (pivot G D) j := by
    intro A
    have h := rank_cut_pivot hOK Aᶜ A (compl_compl A).symm
    rw [h]
    have e : G.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n)) =
        x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n)) := by
      ext a b
      have : (a : n) ≠ b := fun h => (mem_compl.1 b.2) (h ▸ a.2)
      simp [G, diagonal_apply_ne _ this]
    rw [e]; exact hcut A
  obtain ⟨T, hDT, hT, hcore⟩ :=
    closure_core (pivot G D) j hcut' D (frk_pivot_row hOK) (frk_pivot_col hOK)
  refine ⟨T, by rw [← hrank]; exact hT, le_antisymm (closRank_subPattern_le x T) ?_⟩
  apply closRank_subPattern_ge x g T
  intro d hd
  have h1 := rank_dialMat_pivot hOK d
  have hoff : ∀ i ∉ T, pivDial D d i = none := by
    intro i hi
    have hiD : i ∉ D := fun h => hi (hDT h)
    simp [pivDial, hiD, hd i hi]
  obtain ⟨e, he⟩ := hcore (pivDial D d) hoff
  have h2 := rank_dialMat_pivot hOK (pivDial D e)
  rw [pivDial_pivDial] at h2
  have h3 : closRank x ≤ (dialMat G (pivDial D e)).rank := closRank_le_cost x g (pivDial D e)
  show (univ \ T).card + closRank x ≤ (dialMat G d).rank
  omega

end Main

end FreeDiagonal
