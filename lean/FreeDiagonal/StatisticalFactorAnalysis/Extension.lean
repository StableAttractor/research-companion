import FreeDiagonal.StatisticalFactorAnalysis.Model
import FreeDiagonal.StatisticalFactorAnalysis.Positivity
import FreeDiagonal.StatisticalFactorAnalysis.Helpers

/-!
# The extension step of Theorem 2

`G` a symmetric completion of least rank `q` (diagonal in the sets `A i`); `X ⊆ E`, `t ≥ 2`
pairwise disjoint subsets `B_a ⊆ X` whose rows of `G` span the rows of `G` in `X`; vectors
`h_i` (`i ∈ T = (E \ X) ∪ ⋃ B_a`) in a Euclidean space `E` of dimension `≤ m` realising the
off-diagonal entries of `Σ` on `T` and admissible diagonal entries on `E \ X`. If
`dim E + 3 ≤ t + q`, then `Σ` has a positive semidefinite admissible completion of rank
`≤ dim E` (`extend_fit`). This is the second half of the printed proof of Theorem 2, with the
maps `W_a` defined on the coefficient space `ℝ^X` instead of on the span of the rows.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coefficients of a row on a spanning subset. -/
lemma exists_coef (G : Matrix n n ℝ) (S X : Finset n)
    (hs : span ℝ (G.row '' (S : Set n)) = span ℝ (G.row '' (X : Set n))) {x : n} (hx : x ∈ X) :
    ∃ c : n → ℝ, G.row x = ∑ b ∈ S, c b • G.row b := by
  have hmem : G.row x ∈ span ℝ (G.row '' (S : Set n)) := by
    rw [hs]; exact subset_span ⟨x, hx, rfl⟩
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).1 hmem
  refine ⟨l, ?_⟩
  rw [← e, Finsupp.linearCombination_apply]
  exact Finsupp.sum_of_support_subset l (fun i hi => by
    have := (Finsupp.mem_supported ℝ l).1 hl hi; exact_mod_cast this) _ (fun i _ => zero_smul _ _)

lemma row_coef_apply {G : Matrix n n ℝ} {S : Finset n} {x : n} {c : n → ℝ}
    (h : G.row x = ∑ b ∈ S, c b • G.row b) (j : n) : G x j = ∑ b ∈ S, c b * G b j := by
  have := congrFun h j
  simpa [Finset.sum_apply] using this

lemma coef_bilin {G : Matrix n n ℝ} (hG : G.IsSymm) {S S' : Finset n} {x x' : n} {c c' : n → ℝ}
    (h : G.row x = ∑ b ∈ S, c b • G.row b) (h' : G.row x' = ∑ b ∈ S', c' b • G.row b) :
    ∑ b ∈ S, ∑ b' ∈ S', c b * c' b' * G b b' = G x x' := by
  have hs : ∀ i j, G i j = G j i := fun i j => by
    have := congrFun (congrFun hG j) i; simpa using this
  rw [row_coef_apply h x']
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hs b x', row_coef_apply h' b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [hs b' b]; ring

lemma sum_subtype_ite {X : Finset n} (f : X → ℝ) (i : n) :
    ∑ x : X, (if (x : n) = i then f x else 0) = if hi : i ∈ X then f ⟨i, hi⟩ else 0 := by
  by_cases hi : i ∈ X
  · simp only [hi, ↓reduceDIte]
    rw [Fintype.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro x hx
      have : (x : n) ≠ i := fun e => hx (Subtype.ext e)
      simp [this]
  · simp only [hi, ↓reduceDIte]
    refine Finset.sum_eq_zero fun x _ => ?_
    have : (x : n) ≠ i := fun e => hi (e ▸ x.2)
    simp [this]

/-- Extension by zero of a matrix on `X`. -/
def extZero {X : Finset n} (M : Matrix X X ℝ) : Matrix n n ℝ :=
  fun i j => if hi : i ∈ X then if hj : j ∈ X then M ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

lemma extZero_eq {X : Finset n} (M : Matrix X X ℝ) :
    extZero M = (Matrix.of fun i (x : X) => if (x : n) = i then (1 : ℝ) else 0) * M *
      (Matrix.of fun i (x : X) => if (x : n) = i then (1 : ℝ) else 0)ᵀ := by
  ext i j
  simp only [extZero, Matrix.mul_apply, of_apply, transpose_apply]
  have e1 : ∀ x' : X, ∑ x : X, (if (x : n) = i then (1 : ℝ) else 0) * M x x' =
      if hi : i ∈ X then M ⟨i, hi⟩ x' else 0 := by
    intro x'
    rw [← sum_subtype_ite (fun x => M x x') i]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  simp_rw [e1]
  by_cases hi : i ∈ X
  · simp only [hi, ↓reduceDIte]
    rw [← sum_subtype_ite (fun x' => M ⟨i, hi⟩ x') j]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  · simp [hi]

lemma rank_extZero_le {X : Finset n} (M : Matrix X X ℝ) : (extZero M).rank ≤ M.rank := by
  rw [extZero_eq]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

lemma posSemidef_extZero {X : Finset n} {M : Matrix X X ℝ} (hM : M.PosSemidef) :
    (extZero M).PosSemidef := by
  rw [extZero_eq]
  have := hM.mul_mul_conjTranspose_same
    (Matrix.of fun i (x : X) => if (x : n) = i then (1 : ℝ) else 0)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma inner_sum_sum (S S' : Finset n) (c c' : n → ℝ) (h : n → E) :
    inner ℝ (∑ b ∈ S, c b • h b) (∑ b' ∈ S', c' b' • h b') =
      ∑ b ∈ S, ∑ b' ∈ S', c b * c' b' * inner ℝ (h b) (h b') := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [real_inner_smul_right]; ring

/-- **The extension step.** See the module docstring. -/
theorem extend_fit (A : n → Set ℝ) (Sig G : Matrix n n ℝ) (hG : IsCompletionIn A Sig G)
    (hmin : ∀ G', IsCompletionIn A Sig G' → G.rank ≤ G'.rank)
    (X : Finset n) (t : ℕ) (ht : 2 ≤ t) (B : Fin t → Finset n) (hBX : ∀ a, B a ⊆ X)
    (hBd : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hBs : ∀ a, span ℝ (G.row '' (B a : Set n)) = span ℝ (G.row '' (X : Set n)))
    (hv : n → E)
    (hoff : ∀ i j, i ∈ (univ \ X) ∪ univ.biUnion B → j ∈ (univ \ X) ∪ univ.biUnion B → i ≠ j →
      inner ℝ (hv i) (hv j) = Sig i j)
    (hdiag : ∀ i, i ∉ X → inner ℝ (hv i) (hv i) ∈ A i)
    (hdim : finrank ℝ E + 3 ≤ t + G.rank) :
    ∃ G', IsCompletionIn A Sig G' ∧ G'.PosSemidef ∧ G'.rank ≤ finrank ℝ E := by
  classical
  obtain ⟨hGsym, hGoff, hGdiag⟩ := hG
  have hs : ∀ i j, G i j = G j i := fun i j => by
    have := congrFun (congrFun hGsym j) i; simpa using this
  set T := (univ \ X) ∪ univ.biUnion B with hT
  have hBT : ∀ a, ∀ b ∈ B a, b ∈ T := fun a b hb =>
    mem_union_right _ (mem_biUnion.2 ⟨a, mem_univ _, hb⟩)
  have hYT : ∀ y, y ∉ X → y ∈ T := fun y hy => mem_union_left _ (by simp [hy])
  -- coefficients
  have hcoef : ∀ (a : Fin t) (x : X), ∃ c : n → ℝ, G.row x = ∑ b ∈ B a, c b • G.row b :=
    fun a x => exists_coef G (B a) X (hBs a) x.2
  choose coef hcoef using hcoef
  set kv : Fin t → X → E := fun a x => ∑ b ∈ B a, coef a x b • hv b with hkv
  -- (I1) cross products of the `kv`
  have hI1 : ∀ a a', a ≠ a' → ∀ x x' : X, inner ℝ (kv a x) (kv a' x') = G x x' := by
    intro a a' haa' x x'
    rw [hkv, inner_sum_sum, ← coef_bilin hGsym (hcoef a x) (hcoef a' x')]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
    have hne : b ≠ b' := fun e => Finset.disjoint_left.1 (hBd a a' haa') hb (e ▸ hb')
    rw [hoff b b' (hBT a b hb) (hBT a' b' hb') hne, hGoff b b' hne]
  -- (I2) products with `h_y`, `y ∉ X`
  have hI2 : ∀ a, ∀ x : X, ∀ y, y ∉ X → inner ℝ (kv a x) (hv y) = G x y := by
    intro a x y hy
    rw [hkv, sum_inner, row_coef_apply (hcoef a x) y]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hne : b ≠ y := fun e => hy (e ▸ hBX a hb)
    rw [real_inner_smul_left, hoff b y (hBT a b hb) (hYT y hy) hne, hGoff b y hne]
  set a0 : Fin t := ⟨0, by omega⟩
  set a1 : Fin t := ⟨1, by omega⟩
  have ha01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  set H0 : Submodule ℝ E := span ℝ (hv '' ((univ \ X : Finset n) : Set n)) with hH0
  have hgen : ∀ y, y ∉ X → hv y ∈ H0 := fun y hy => subset_span ⟨y, by simp [hy], rfl⟩
  set p : X → E := fun x => H0.starProjection (kv a0 x) with hp
  have hpmem : ∀ x, p x ∈ H0 := fun x => H0.starProjection_apply_mem _
  have hpy : ∀ x : X, ∀ y, y ∉ X → inner ℝ (p x) (hv y) = G x y := by
    intro x y hy
    have h0 := Submodule.starProjection_inner_eq_zero (K := H0) (kv a0 x) (hv y) (hgen y hy)
    rw [inner_sub_left] at h0
    rw [← hI2 a0 x y hy]; linarith
  set z : Fin t → X → E := fun a x => kv a x - p x with hz
  have hzorth : ∀ a x, z a x ∈ H0ᗮ := by
    intro a x
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      have hy' : y ∉ X := by simpa using hy
      rw [hz, inner_sub_right, real_inner_comm, hI2 a x y hy', real_inner_comm, hpy x y hy',
        sub_self]
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
    | smul r u _ hu => rw [real_inner_smul_left, hu, mul_zero]
  have hcross : ∀ a a', a ≠ a' → ∀ x x' : X,
      inner ℝ (z a x) (z a' x') = G x x' - inner ℝ (p x) (p x') := by
    intro a a' haa' x x'
    have e1 : inner ℝ (z a x) (p x') = 0 :=
      Submodule.inner_left_of_mem_orthogonal (hpmem x') (hzorth a x)
    have e2 : inner ℝ (p x) (z a' x') = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hpmem x) (hzorth a' x')
    rw [hz] at e1 e2
    show inner ℝ (kv a x - p x) (kv a' x' - p x') = _
    simp only [inner_sub_left, inner_sub_right] at e1 e2 ⊢
    rw [hI1 a a' haa' x x']
    linarith
  set M : Matrix X X ℝ := Matrix.of fun x x' => G x x' - inner ℝ (p x) (p x') with hM
  have hMsym : M.IsSymm := by
    ext x x'
    simp only [hM, transpose_apply, of_apply]
    rw [hs, real_inner_comm]
  -- the maps of Lemma 2, into `H0ᗮ`
  set P := H0ᗮ with hP
  set zP : Fin t → X → P := fun a x => ⟨z a x, hzorth a x⟩ with hzP
  set Wm : Fin t → (X → ℝ) →ₗ[ℝ] P := fun a => Fintype.linearCombination ℝ (zP a) with hWm
  have hWmc : ∀ a b, a ≠ b → ∀ α β, inner ℝ (Wm a α) (Wm b β) = formOf M α β := by
    intro a b hab α β
    have e : ∀ a (γ : X → ℝ), ((Wm a γ : P) : E) = ∑ x, γ x • z a x := by
      intro a γ
      simp [hWm, Fintype.linearCombination_apply, hzP]
    rw [formOf_apply, Submodule.coe_inner, e, e, sum_inner]
    simp only [dotProduct, mulVec, hM, of_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, hcross a b hab x x']; ring
  have hdimP : finrank ℝ H0 + finrank ℝ P = finrank ℝ E := Submodule.finrank_add_finrank_orthogonal H0
  -- the completion `G'`
  set Pv : n → H0 := fun i => if hi : i ∈ X then ⟨p ⟨i, hi⟩, hpmem _⟩ else ⟨hv i, hgen i hi⟩
    with hPv
  set G' : Matrix n n ℝ := gram ℝ Pv + extZero M with hG'
  have hG'e : ∀ i j, G' i j =
      if i ∈ X then (if j ∈ X then G i j else G i j) else
        (if j ∈ X then G i j else inner ℝ (hv i) (hv j)) := by
    intro i j
    simp only [hG', Matrix.add_apply, gram_apply, Submodule.coe_inner, extZero, hPv]
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;>
      simp only [hi, hj, ↓reduceDIte, ↓reduceIte, hM, of_apply,
        add_zero]
    · ring
    · exact hpy ⟨i, hi⟩ j hj
    · rw [real_inner_comm, hpy ⟨j, hj⟩ i hi, hs]
  have hG'c : IsCompletionIn A Sig G' := by
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      simp only [transpose_apply, hG'e]
      by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp [hi, hj, hs, real_inner_comm]
    · intro i j hij
      rw [hG'e]
      by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp only [hi, hj, ↓reduceIte]
      all_goals first
        | exact hGoff i j hij
        | exact hoff i j (hYT i hi) (hYT j hj) hij
    · intro i
      rw [hG'e]
      by_cases hi : i ∈ X <;> simp only [hi, ↓reduceIte]
      · exact hGdiag i
      · exact hdiag i hi
  have hG'r : G'.rank ≤ finrank ℝ H0 + M.rank :=
    (rank_add_le' _ _).trans (add_le_add (rank_gram_le Pv) (rank_extZero_le M))
  have hq : G.rank ≤ finrank ℝ H0 + M.rank := (hmin G' hG'c).trans hG'r
  have hMr : M.rank ≤ finrank ℝ P := by
    have e : M = Matrix.of fun x x' => inner ℝ (zP a0 x) (zP a1 x') := by
      ext x x'
      simp only [hM, of_apply, Submodule.coe_inner, hzP]
      rw [hcross a0 a1 ha01 x x']
    rw [e]; exact rank_cross_le _ _
  -- Lemma 2
  have hpos := lemma2 (formOf M) (fun α β => by
      rw [formOf_apply, formOf_apply, dotProduct_mulVec, ← mulVec_transpose, hMsym.eq,
        dotProduct_comm]) rfl (finrank_range_formOf M) Wm ht hWmc (by omega)
  have hMpsd : M.PosSemidef := posSemidef_of_form hMsym (fun α => by
    rw [← formOf_apply]; exact hpos α)
  refine ⟨G', hG'c, (posSemidef_gram ℝ Pv).add (posSemidef_extZero hMpsd), ?_⟩
  omega

end FreeDiagonal.StatisticalFactorAnalysis
