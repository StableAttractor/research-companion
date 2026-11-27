import Mathlib

/-!
# Linear-algebra tools

* `frk F u S`: the rank of the family `(u i)_{i ∈ S}`.
* bases inside a finite family, sub-additivity.
* the Frobenius rank inequality `rank (P G) + rank (G Q) ≤ rank G + rank (P G Q)`.
* deleting rows (columns) that lie in the span of the remaining ones keeps the rank.
-/

open Matrix Module Submodule

namespace FreeDiagonal

variable (F : Type*) [Field F]

/-- The rank of the family `(u i)_{i ∈ S}`: dimension of the span of `{u i : i ∈ S}`. -/
noncomputable def frk {ι V : Type*} [AddCommGroup V] [Module F V] (u : ι → V)
    (S : Finset ι) : ℕ :=
  finrank F (span F (u '' (S : Set ι)))

variable {F}
variable {ι V : Type*} [AddCommGroup V] [Module F V]

instance fd_span_image (u : ι → V) (S : Finset ι) :
    FiniteDimensional F (span F (u '' (S : Set ι))) :=
  FiniteDimensional.span_of_finite F (S.finite_toSet.image u)

lemma frk_mono (u : ι → V) {S S' : Finset ι} (h : S ⊆ S') : frk F u S ≤ frk F u S' :=
  Submodule.finrank_mono (span_mono (Set.image_mono (by exact_mod_cast h)))

lemma frk_le_card (u : ι → V) (S : Finset ι) : frk F u S ≤ S.card := by
  classical
  unfold frk
  have h : u '' (S : Set ι) = ((S.image u : Finset V) : Set V) := by simp
  rw [h]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

lemma frk_le_frk_add_card [DecidableEq ι] (u : ι → V) (S R : Finset ι) :
    frk F u S ≤ frk F u R + (S \ R).card := by
  have hle : span F (u '' (S : Set ι)) ≤
      span F (u '' (R : Set ι)) ⊔ span F (u '' ((S \ R : Finset ι) : Set ι)) := by
    rw [← span_union, ← Set.image_union]
    apply span_mono
    apply Set.image_mono
    intro i hi
    by_cases hR : i ∈ R
    · exact Or.inl hR
    · exact Or.inr (by simpa [hR] using hi)
  calc frk F u S ≤ finrank F (↥(span F (u '' (R : Set ι)) ⊔
        span F (u '' ((S \ R : Finset ι) : Set ι)))) := Submodule.finrank_mono hle
    _ ≤ frk F u R + frk F u (S \ R) := Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ frk F u R + (S \ R).card := by gcongr; exact frk_le_card u _

/-- Every finite family contains an independent subfamily with the same span. -/
lemma exists_basis_subset (u : ι → V) (S : Finset ι) :
    ∃ I ⊆ S, I.card = frk F u S ∧ span F (u '' (I : Set ι)) = span F (u '' (S : Set ι)) := by
  classical
  obtain ⟨b, hbS, -, hspan, hli⟩ :=
    exists_linearIndepOn_extension (K := F) (v := u) (linearIndepOn_empty F u)
      (Set.empty_subset (S : Set ι))
  set I : Finset ι := S.filter (· ∈ b) with hI
  have hIb : (I : Set ι) = b := by
    ext i; simp only [hI, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hbS h, h⟩⟩
  have hsp : span F (u '' (I : Set ι)) = span F (u '' (S : Set ι)) := by
    apply le_antisymm
    · exact span_mono (Set.image_mono (fun x hx => (Finset.mem_filter.1 hx).1))
    · rw [hIb]; exact span_le.2 hspan
  refine ⟨I, by simp [hI], ?_, hsp⟩
  unfold frk
  rw [← hsp]
  have hli' : LinearIndependent F (fun i : (I : Set ι) => u i) := by rw [hIb]; exact hli
  have := finrank_span_eq_card hli'
  rw [← Set.image_eq_range] at this
  rw [this]
  simp

/-- An independent family stays independent on subsets. -/
lemma frk_eq_card_of_subset [DecidableEq ι] (u : ι → V) {I R : Finset ι}
    (hRI : R ⊆ I) (hI : frk F u I = I.card) : frk F u R = R.card := by
  apply le_antisymm (frk_le_card (F := F) u R)
  have h1 := frk_le_frk_add_card (F := F) u I R
  have h2 : (I \ R).card + R.card = I.card := Finset.card_sdiff_add_card_eq_card hRI
  omega

/-! ### Frobenius inequality -/

lemma finrank_map_le_add {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F V]
    (p : V →ₗ[F] W) {W1 W0 : Submodule F V} (h : W1 ≤ W0) :
    finrank F (W0.map p) + finrank F W1 ≤ finrank F W0 + finrank F (W1.map p) := by
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl W1
  set C := C' ⊓ W0
  have hsup : W1 ⊔ C = W0 := by
    rw [← sup_inf_assoc_of_le C' h, hC'.sup_eq_top, top_inf_eq]
  have hinf : W1 ⊓ C = ⊥ := by
    apply eq_bot_iff.2
    calc W1 ⊓ C ≤ W1 ⊓ C' := inf_le_inf_left _ inf_le_left
      _ = ⊥ := hC'.inf_eq_bot
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W1 C
  rw [hsup, hinf, finrank_bot] at hdim
  have hmap : W0.map p = W1.map p ⊔ C.map p := by rw [← hsup, Submodule.map_sup]
  have h1 : finrank F (W0.map p) ≤ finrank F (W1.map p) + finrank F (C.map p) := by
    rw [hmap]; exact Submodule.finrank_add_le_finrank_add_finrank _ _
  have h2 : finrank F (C.map p) ≤ finrank F C := Submodule.finrank_map_le p C
  omega

variable {a m k c : Type*} [Fintype m] [Fintype k] [Fintype c]

/-- Frobenius rank inequality. -/
theorem rank_frobenius (P : Matrix a m F) (G : Matrix m k F) (Q : Matrix k c F) :
    (P * G).rank + (G * Q).rank ≤ G.rank + (P * G * Q).rank := by
  classical
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul,
    LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_comp]
  have hle : (LinearMap.range Q.mulVecLin).map G.mulVecLin ≤ LinearMap.range G.mulVecLin :=
    LinearMap.map_le_range
  have := finrank_map_le_add P.mulVecLin hle
  rw [Submodule.map_comp] at *
  simpa [LinearMap.range_comp, Submodule.map_comp] using this

/-! ### Rows, columns and submatrices -/

omit [Fintype m] in
/-- The rank of a matrix is the rank of its family of rows. -/
lemma rank_eq_frk_univ [Fintype m] (M : Matrix m k F) : M.rank = frk F M.row Finset.univ := by
  rw [rank_eq_finrank_span_row]; unfold frk; rw [Finset.coe_univ, Set.image_univ]

omit [Fintype m] in
lemma rank_submatrix_rows_eq_frk (M : Matrix m k F) (R : Finset m) :
    (M.submatrix (fun r : R => (r : m)) id).rank = frk F M.row R := by
  have h : Set.range (M.submatrix (fun r : R => (r : m)) id).row = M.row '' (R : Set m) := by
    ext v; constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  rw [rank_eq_finrank_span_row, h]; rfl

omit [Fintype m] in
/-- Deleting rows outside `R` loses at most `|Rᶜ|` of the rank. -/
lemma rank_le_rank_submatrix_rows_add [Fintype m] [DecidableEq m] (M : Matrix m k F)
    (R : Finset m) :
    M.rank ≤ (M.submatrix (fun r : R => (r : m)) id).rank + (Finset.univ \ R).card := by
  rw [rank_eq_frk_univ, rank_submatrix_rows_eq_frk]; exact frk_le_frk_add_card M.row _ R

omit [Fintype m] in
/-- If every row lies in the span of the rows indexed by `R`, deleting the other rows keeps
the rank. -/
lemma rank_le_submatrix_rows [Fintype m] (M : Matrix m k F) (R : Finset m)
    (h : ∀ i, M.row i ∈ span F (M.row '' (R : Set m))) :
    M.rank ≤ (M.submatrix (fun r : R => (r : m)) id).rank := by
  rw [rank_eq_frk_univ, rank_submatrix_rows_eq_frk]
  apply Submodule.finrank_mono
  apply span_le.2
  rintro _ ⟨i, -, rfl⟩
  exact h i

omit [Fintype m] in
/-- Row and column version: if every row lies in the span of the rows indexed by `R` and every
column in the span of the columns indexed by `C`, then the `R × C` submatrix has full rank. -/
lemma rank_le_submatrix_of_span [Fintype m] (M : Matrix m k F) (R : Finset m) (C : Finset k)
    (hR : ∀ i, M.row i ∈ span F (M.row '' (R : Set m)))
    (hC : ∀ s, M.col s ∈ span F (M.col '' (C : Set k))) :
    M.rank ≤ (M.submatrix (fun r : R => (r : m)) (fun s : C => (s : k))).rank := by
  set N := M.submatrix (fun r : R => (r : m)) id
  have h1 := rank_le_submatrix_rows M R hR
  have hC' : ∀ s, Nᵀ.row s ∈ span F (Nᵀ.row '' (C : Set k)) := by
    intro s
    have := Submodule.apply_mem_span_image_of_mem_span
      (LinearMap.funLeft F F (fun r : R => (r : m))) (hC s)
    rw [Set.image_image] at this
    exact this
  have h2 := rank_le_submatrix_rows Nᵀ C hC'
  rw [rank_transpose] at h2
  calc M.rank ≤ N.rank := h1
    _ ≤ _ := h2
    _ = _ := by rw [← rank_transpose]; rfl

/-- Any matrix of rank at least `r` has an `R × C` submatrix with `|R|, |C| ≤ r` and rank at
least `r`. -/
lemma exists_small_submatrix [DecidableEq m] [DecidableEq k] (M : Matrix m k F)
    (r : ℕ) (hr : r ≤ M.rank) :
    ∃ R : Finset m, ∃ C : Finset k, R.card ≤ r ∧ C.card ≤ r ∧
      r ≤ (M.submatrix (fun a : R => (a : m)) (fun b : C => (b : k))).rank := by
  obtain ⟨I, -, hIcard, hIspan⟩ := exists_basis_subset (F := F) M.row Finset.univ
  have hIfrk : frk F M.row I = M.rank := by
    rw [rank_eq_frk_univ]; unfold frk; rw [hIspan]
  rw [← rank_eq_frk_univ] at hIcard
  obtain ⟨R, hRI, hRcard⟩ := Finset.exists_subset_card_eq (hr.trans hIcard.ge)
  have hRfrk : frk F M.row R = r := by
    rw [frk_eq_card_of_subset M.row hRI (by rw [hIcard, hIfrk]), hRcard]
  set N := M.submatrix (fun a : R => (a : m)) id
  have hN : N.rank = r := by rw [rank_submatrix_rows_eq_frk, hRfrk]
  obtain ⟨C, -, hCcard, hCspan⟩ := exists_basis_subset (F := F) Nᵀ.row Finset.univ
  rw [← rank_eq_frk_univ, rank_transpose, hN] at hCcard
  refine ⟨R, C, hRcard.le, hCcard.le, ?_⟩
  have hC : ∀ s, Nᵀ.row s ∈ span F (Nᵀ.row '' (C : Set k)) := by
    intro s; rw [hCspan]; exact subset_span ⟨s, by simp, rfl⟩
  have := rank_le_submatrix_rows Nᵀ C hC
  rw [rank_transpose, hN] at this
  calc r ≤ _ := this
    _ = _ := by rw [← rank_transpose]; rfl

end FreeDiagonal
