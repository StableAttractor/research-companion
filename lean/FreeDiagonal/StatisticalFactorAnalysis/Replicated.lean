import FreeDiagonal.StatisticalFactorAnalysis.UpperBound

/-!
# Lemma 3 (replicated matrices): definitions and the first assertions

Variables are `Fin q × Fin t` (group, member). `S0` is a real symmetric invertible `q × q`
matrix, not positive semidefinite, whose principal submatrices of size `q - 1` (on
`{k // k ≠ j}`) are positive definite. `s_j = S0_jj`, and `-g_j` is the Schur complement of
`S0` at `j`: `g_j = r_jᵀ S0[-j]⁻¹ r_j - s_j` with `r_j = (S0_jk)_{k ≠ j}` (`schurG`).
A replicated matrix `Σ` has `Σ_il = S0_{group i, group l}` for `i ≠ l`.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {q : ℕ}

/-- The principal submatrix `S0[-j]` on `{k // k ≠ j}`. -/
def offPrinc (S0 : Matrix (Fin q) (Fin q) ℝ) (j : Fin q) : Matrix {k // k ≠ j} {k // k ≠ j} ℝ :=
  S0.submatrix Subtype.val Subtype.val

/-- `r_j = (S0_jk)_{k ≠ j}`. -/
def offRow (S0 : Matrix (Fin q) (Fin q) ℝ) (j : Fin q) : {k // k ≠ j} → ℝ := fun k => S0 j k

/-- `g_j`: minus the Schur complement of `S0` at position `j`,
`g_j = r_jᵀ S0[-j]⁻¹ r_j - s_j`. -/
noncomputable def schurG (S0 : Matrix (Fin q) (Fin q) ℝ) (j : Fin q) : ℝ :=
  offRow S0 j ⬝ᵥ ((offPrinc S0 j)⁻¹ *ᵥ offRow S0 j) - S0 j j

/-- The hypotheses of Lemma 3 on `S0`. -/
structure IsLemma3Matrix (S0 : Matrix (Fin q) (Fin q) ℝ) : Prop where
  symm : S0.IsSymm
  det_ne : S0.det ≠ 0
  not_psd : ¬ S0.PosSemidef
  princ : ∀ j, (offPrinc S0 j).PosDef

/-- `Σ` is replicated from `S0`: `Σ_il = S0_{group i, group l}` for `i ≠ l`. -/
def IsReplicated {t : ℕ} (S0 : Matrix (Fin q) (Fin q) ℝ) (Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ) :
    Prop :=
  Sig.IsSymm ∧ ∀ i l, i ≠ l → Sig i l = S0 i.1 l.1

/-- Condition (1) of Lemma 3: for every group `j` and every variable `i₀` in it,
`c_i > s_j` for `i` in group `j` and `g_j Σ_{i ≠ i₀ in group j} 1/(c_i - s_j) < 1`. -/
def Cond1 {t : ℕ} (S0 : Matrix (Fin q) (Fin q) ℝ) (Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ) :
    Prop :=
  ∀ j : Fin q, (∀ a, S0 j j < Sig (j, a) (j, a)) ∧
    ∀ a0 : Fin t, schurG S0 j * ∑ a ∈ univ.erase a0, 1 / (Sig (j, a) (j, a) - S0 j j) < 1

lemma symm_apply {ι : Type*} {M : Matrix ι ι ℝ} (h : M.IsSymm) (i j : ι) : M i j = M j i := by
  have := congrFun (congrFun h j) i; simpa using this

/-- Gram vectors `w_k` (`k ≠ j`) realising `S0[-j]`, completed at `j` by the vector `p` of the
span with `⟪p, w_k⟫ = S0_jk`; `‖p‖² = s_j + g_j`. All lie in a space of dimension `q - 1`. -/
lemma schur_gram (S0 : Matrix (Fin q) (Fin q) ℝ) (hS : S0.IsSymm) (j : Fin q)
    (hP : (offPrinc S0 j).PosDef) :
    ∃ (K : ℕ) (w : Fin q → EuclideanSpace ℝ (Fin K)),
      (∀ k l, inner ℝ (w k) (w l) = S0 k l + if k = j ∧ l = j then schurG S0 j else 0) ∧
      finrank ℝ (span ℝ (Set.range w)) ≤ q - 1 := by
  classical
  obtain ⟨K, v, hv⟩ := exists_gram_of_posSemidef hP.posSemidef
  have hv' : ∀ a b, inner ℝ (v a) (v b) = S0 a b := fun a b => by
    rw [← gram_apply (𝕜 := ℝ), hv]; rfl
  set Sj := offPrinc S0 j
  set r := offRow S0 j
  set c := Sj⁻¹ *ᵥ r with hc
  have hSc : Sj *ᵥ c = r := by
    rw [hc, mulVec_mulVec, mul_nonsing_inv _ ((hP.isUnit).map Matrix.detMonoidHom), one_mulVec]
  have hSsym : ∀ a b, Sj a b = Sj b a := fun a b => symm_apply hS a b
  set p := ∑ k, c k • v k with hp
  have hpv : ∀ l, inner ℝ p (v l) = r l := by
    intro l
    rw [hp, sum_inner]
    have := congrFun hSc l
    simp only [mulVec, dotProduct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, hv']
    simp only [Sj, offPrinc, submatrix_apply]
    rw [symm_apply hS l k]; ring
  have hpp : inner ℝ p p = S0 j j + schurG S0 j := by
    have : inner ℝ p p = r ⬝ᵥ c := by
      conv_lhs => rw [hp]
      rw [sum_inner]
      simp only [real_inner_smul_left]
      rw [dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm, hpv, mul_comm]
    rw [this, schurG]; ring
  set w : Fin q → EuclideanSpace ℝ (Fin K) := fun k => if h : k = j then p else v ⟨k, h⟩ with hw
  refine ⟨K, w, ?_, ?_⟩
  · intro k l
    by_cases hk : k = j <;> by_cases hl : l = j
    · rw [hk, hl]; simp only [w, dite_true, and_self, ite_true]; exact hpp
    · rw [hk]; simp only [w, dite_true, hl, dite_false, and_false, ite_false, add_zero]
      exact hpv ⟨l, hl⟩
    · rw [hl]; simp only [w, dite_true, hk, dite_false, false_and, ite_false, add_zero]
      rw [real_inner_comm, hpv]; exact symm_apply hS j k
    · simp only [w, hk, hl, dite_false, false_and, ite_false, add_zero]; exact hv' _ _
  · have hsub : Set.range w ⊆ span ℝ (Set.range v) := by
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · simp only [w, hk, dite_true, hp]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)
      · simp only [w, hk, dite_false]; exact subset_span ⟨_, rfl⟩
    have h1 := Submodule.finrank_mono (span_le.2 hsub)
    have h2 : finrank ℝ (span ℝ (Set.range v)) ≤ q - 1 := by
      rw [← rank_gram, hv]
      calc Sj.rank ≤ Fintype.card {k : Fin q // k ≠ j} := rank_le_card_width _
        _ = q - 1 := by simp [Fintype.card_subtype_compl]
    omega

/-- **Lemma 3, preliminary assertion.** `s_j > 0` and `g_j > 0`. -/
theorem lemma3_pos {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    (j : Fin q) : 0 < S0 j j ∧ 0 < schurG S0 j := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k : Fin q, k ≠ j := by
      by_cases h : j = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, fun e => h e.symm⟩
    have := (hS0.princ k).diag_pos (i := ⟨j, fun e => hk e.symm⟩)
    simpa [offPrinc] using this
  · by_contra hg
    push Not at hg
    obtain ⟨K, w, hw, -⟩ := schur_gram S0 hS0.symm j (hS0.princ j)
    apply hS0.not_psd
    have e : S0 = gram ℝ w + diagonal (Pi.single j (-schurG S0 j)) := by
      ext k l
      rw [Matrix.add_apply, gram_apply, hw]
      by_cases hk : k = j <;> by_cases hl : l = j
      · rw [hk, hl]; simp
      · rw [hk]; simp [hl, diagonal_apply_ne _ (Ne.symm hl)]
      · rw [hl]; simp [hk]
      · by_cases hkl : k = l
        · rw [hkl]; simp [hl]
        · simp [hk, hl, diagonal_apply_ne _ hkl]
    rw [e]
    refine (posSemidef_gram ℝ w).add (posSemidef_diagonal_iff.2 fun i => ?_)
    by_cases hi : i = j
    · subst hi; simp; linarith
    · simp [hi]

lemma rank_S0 {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) : S0.rank = q := by
  rw [Matrix.rank_of_isUnit S0 ((Matrix.isUnit_iff_isUnit_det S0).2
    (isUnit_iff_ne_zero.2 hS0.det_ne)), Fintype.card_fin]

/-- **Lemma 3, first assertion.** With `m = q + t - 3`, no positive semidefinite matrix of rank
at most `m` has the off-diagonal entries of a replicated matrix `Σ`. Route (not the printed
one): Gram vectors of such a matrix give `t` maps `ℝ^q → ℝ^{rank}` with common cross form
`S0`, and Lemma 2 would make `S0` positive semidefinite. -/
theorem lemma3_no_psd {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    {t : ℕ} (ht : 2 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (H : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ) (hH : H.PosSemidef)
    (hoff : ∀ i l, i ≠ l → H i l = Sig i l) : q + t - 3 < H.rank := by
  classical
  obtain ⟨K, v, hv⟩ := exists_gram_of_posSemidef hH
  set Esp := span ℝ (Set.range v)
  set vE : Fin q × Fin t → Esp := fun i => ⟨v i, subset_span ⟨i, rfl⟩⟩ with hvE
  have hdim : finrank ℝ Esp = H.rank := by rw [← hv, rank_gram]
  have hvv : ∀ i l, inner ℝ (vE i) (vE l) = H i l := fun i l => by
    rw [← hv, gram_apply]; rfl
  set W : Fin t → (Fin q → ℝ) →ₗ[ℝ] Esp :=
    fun a => Fintype.linearCombination ℝ (fun k => vE (k, a)) with hW
  have hcross : ∀ a b, a ≠ b → ∀ α β, inner ℝ (W a α) (W b β) = formOf S0 α β := by
    intro a b hab α β
    have lhs : inner ℝ (W a α) (W b β) = ∑ k, ∑ l, α k * β l * S0 k l := by
      rw [hW]
      simp only [Fintype.linearCombination_apply, sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [real_inner_smul_right, hvv]
      have hne : (k, a) ≠ (l, b) := fun e => hab (congrArg Prod.snd e)
      rw [hoff _ _ hne, hSig.2 _ _ hne]; ring
    rw [lhs, formOf_apply]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  by_contra hcon
  push Not at hcon
  have hpos := lemma2 (formOf S0) (fun α β => by
      rw [formOf_apply, formOf_apply, dotProduct_mulVec, ← mulVec_transpose, hS0.symm.eq,
        dotProduct_comm]) rfl ((finrank_range_formOf S0).trans (rank_S0 hS0)) W ht hcross
      (by omega)
  exact hS0.not_psd (posSemidef_of_form hS0.symm (fun α => by rw [← formOf_apply]; exact hpos α))

/-- Any matrix with the off-diagonal entries of `Σ` has rank at least `q`. -/
lemma q_le_rank {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) {t : ℕ} (ht : 2 ≤ t)
    {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (G : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ) (hoff : ∀ i l, i ≠ l → G i l = Sig i l) :
    q ≤ G.rank := by
  have e : G.submatrix (fun k => (k, (⟨0, by omega⟩ : Fin t))) (fun k => (k, ⟨1, by omega⟩)) = S0 := by
    ext k l
    have hne : (k, (⟨0, by omega⟩ : Fin t)) ≠ (l, ⟨1, by omega⟩) := by simp [Fin.ext_iff]
    simp only [submatrix_apply]
    rw [hoff _ _ hne, hSig.2 _ _ hne]
  calc q = S0.rank := (rank_S0 hS0).symm
    _ = _ := by rw [← e]
    _ ≤ G.rank := rank_submatrix_le _ _ _

/-- The replicated matrix with diagonal `s_j`: `G_il = S0_{group i, group l}`. -/
def replG {t : ℕ} (S0 : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ :=
  Matrix.of fun i l => S0 i.1 l.1

lemma replG_eq {t : ℕ} (S0 : Matrix (Fin q) (Fin q) ℝ) :
    replG (t := t) S0 = (Matrix.of fun (i : Fin q × Fin t) (k : Fin q) => if i.1 = k then (1 : ℝ) else 0) *
      S0 * (Matrix.of fun (i : Fin q × Fin t) (k : Fin q) => if i.1 = k then (1 : ℝ) else 0)ᵀ := by
  ext i l
  simp [replG, Matrix.mul_apply, ite_mul, Finset.sum_ite_eq]

lemma rank_replG_le {t : ℕ} (S0 : Matrix (Fin q) (Fin q) ℝ) : (replG (t := t) S0).rank ≤ q := by
  rw [replG_eq]
  exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans
    ((rank_le_card_width _).trans (by simp)))

/-- **Lemma 3, second assertion.** If `c_i > s_j` for all `i` (in group `j`), the least rank of a
reference of `Σ` is `q`. -/
theorem lemma3_least_ref {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    {t : ℕ} (ht : 2 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ}
    (hSig : IsReplicated S0 Sig) (hc : ∀ i, S0 i.1 i.1 < Sig i i) :
    IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q := by
  refine ⟨⟨replG S0, ⟨?_, ?_, ?_⟩, le_antisymm (rank_replG_le S0) ?_⟩, ?_⟩
  · ext i l; simp [replG, symm_apply hS0.symm i.1 l.1]
  · intro i l hil; simp [replG, hSig.2 i l hil]
  · intro i; exact ⟨(lemma3_pos hS0 hq i.1).1.le, hc i⟩
  · exact q_le_rank hS0 ht hSig _ (fun i l hil => by simp [replG, hSig.2 i l hil])
  · rintro r ⟨G, hG, rfl⟩
    exact q_le_rank hS0 ht hSig G hG.2.1

end FreeDiagonal.StatisticalFactorAnalysis
