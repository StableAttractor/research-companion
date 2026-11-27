import FreeDiagonal.StatisticalFactorAnalysis.Replicated

/-!
# Lemma 3, third assertion: condition (1) gives fits of all proper principal submatrices

Route: for the deleted variable `i₀` in group `j`, the fit is `H = H₁ + K` where `H₁` is the
Gram matrix of the vectors `w_{group i}` of `schur_gram` (rank `≤ q - 1`; group `j` gets the
vector `p` with `‖p‖² = s_j + g_j`), and `K` is `diag(δ) - g_j J` on the other `t - 1`
variables of group `j`, with `δ = κ (c_i - s_j)`, `κ = g_j Σ 1/(c_i - s_j) < 1`, so that
`g_j Σ 1/δ = 1` and `K` is positive semidefinite of rank `≤ t - 2`. This replaces the
printed choice "subtract the least eigenvalue" by an explicit scaling.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Fits transfer along injective maps: if `Σ ∈ F` then `Σ.submatrix f f ∈ F`. -/
lemma InModel.comp_inj {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} {Sig : Matrix n n ℝ}
    (h : InModel m Sig) (f : α → n) (hf : Function.Injective f) : InModel m (Sig.submatrix f f) := by
  rw [inModel_iff_exists_fit] at h ⊢
  obtain ⟨G, hp, hr, ho, hd⟩ := h
  exact ⟨G.submatrix f f, hp.submatrix _, (rank_submatrix_le _ _ _).trans hr,
    fun a b hab => ho _ _ (hf.ne hab), fun a => hd _⟩

lemma InWeakModel.comp_inj {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} {Sig : Matrix n n ℝ}
    (h : InWeakModel m Sig) (f : α → n) (hf : Function.Injective f) :
    InWeakModel m (Sig.submatrix f f) := by
  rw [inWeakModel_iff_exists_weakFit] at h ⊢
  obtain ⟨G, hp, hr, ho, hd⟩ := h
  exact ⟨G.submatrix f f, hp.submatrix _, (rank_submatrix_le _ _ _).trans hr,
    fun a b hab => ho _ _ (hf.ne hab), fun a => hd _⟩

/-- If every principal submatrix on `E` minus one variable is in the model, so is every proper
principal submatrix. -/
lemma inModel_proper_of_erase {m : ℕ} {Sig : Matrix n n ℝ}
    (h : ∀ i0, InModel m (subPattern Sig (univ.erase i0))) (T : Finset n) (hT : T ≠ univ) :
    InModel m (subPattern Sig T) := by
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ T := by
    by_contra hc; push Not at hc; exact hT (eq_univ_of_forall hc)
  have := (h i0).comp_inj (fun a : T => (⟨a.1, mem_erase.2 ⟨fun e => hi0 (e ▸ a.2), mem_univ _⟩⟩ :
    (univ.erase i0 : Finset n))) (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  exact this

/-- Embedding of a matrix on `ι` along an injective map `f : ι → n` (zero elsewhere). -/
def embedMat {ι : Type*} [Fintype ι] (f : ι → n) (K : Matrix ι ι ℝ) : Matrix n n ℝ :=
  (Matrix.of fun i a => if f a = i then (1 : ℝ) else 0) * K *
    (Matrix.of fun i a => if f a = i then (1 : ℝ) else 0)ᵀ

lemma sum_ind_mul {ι : Type*} [Fintype ι] (f : ι → n) (hf : Function.Injective f) (g : ι → ℝ)
    (a0 : ι) : ∑ a, (if f a = f a0 then (1 : ℝ) else 0) * g a = g a0 := by
  rw [Fintype.sum_eq_single a0]
  · simp
  · intro a ha
    have : f a ≠ f a0 := hf.ne ha
    simp [this]

lemma sum_ind_mul_zero {ι : Type*} [Fintype ι] (f : ι → n) (g : ι → ℝ) (x : n)
    (hx : ∀ a, f a ≠ x) : ∑ a, (if f a = x then (1 : ℝ) else 0) * g a = 0 :=
  Finset.sum_eq_zero fun a _ => by simp [hx a]

lemma embedMat_apply_apply {ι : Type*} [Fintype ι] (f : ι → n) (hf : Function.Injective f)
    (K : Matrix ι ι ℝ) (a b : ι) : embedMat f K (f a) (f b) = K a b := by
  simp only [embedMat, Matrix.mul_apply, of_apply, transpose_apply]
  simp_rw [sum_ind_mul f hf (fun a' => K a' _) a]
  rw [← sum_ind_mul f hf (fun b' => K a b') b]
  exact Finset.sum_congr rfl fun b' _ => by ring

lemma embedMat_apply_left {ι : Type*} [Fintype ι] (f : ι → n) (K : Matrix ι ι ℝ) (i l : n)
    (hi : ∀ a, f a ≠ i) : embedMat f K i l = 0 := by
  simp only [embedMat, Matrix.mul_apply, of_apply, transpose_apply]
  simp_rw [sum_ind_mul_zero f (fun a' => K a' _) i hi]
  simp

lemma embedMat_apply_right {ι : Type*} [Fintype ι] (f : ι → n) (K : Matrix ι ι ℝ) (i l : n)
    (hl : ∀ b, f b ≠ l) : embedMat f K i l = 0 := by
  simp only [embedMat, Matrix.mul_apply, of_apply, transpose_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  simp [hl b]

lemma rank_embedMat_le {ι : Type*} [Fintype ι] (f : ι → n) (K : Matrix ι ι ℝ) :
    (embedMat f K).rank ≤ K.rank :=
  (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

lemma posSemidef_embedMat {ι : Type*} [Fintype ι] (f : ι → n) {K : Matrix ι ι ℝ}
    (hK : K.PosSemidef) : (embedMat f K).PosSemidef := by
  have := hK.mul_mul_conjTranspose_same (Matrix.of fun i a => if f a = i then (1 : ℝ) else 0)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- A matrix with a non-zero kernel vector has rank at most `card - 1`. -/
lemma rank_le_card_sub_one {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v : ι → ℝ) (hv : v ≠ 0)
    (hMv : M *ᵥ v = 0) : M.rank ≤ Fintype.card ι - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 : 0 < finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, by simpa using hMv⟩, by simpa using hv⟩
  simp only [Module.finrank_fintype_fun_eq_card] at h1
  unfold Matrix.rank
  omega

/-- `diag(δ) - g J` with `δ > 0` and `g Σ 1/δ = 1` is positive semidefinite and kills
`(1/δ_i)`. -/
lemma diag_sub_const {ι : Type*} [Fintype ι] [DecidableEq ι] (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (g : ℝ) (h1 : g * ∑ i, 1 / δ i = 1) :
    (diagonal δ - g • Matrix.of fun (_ _ : ι) => (1 : ℝ)).PosSemidef ∧
      (diagonal δ - g • Matrix.of fun (_ _ : ι) => (1 : ℝ)) *ᵥ (fun i => 1 / δ i) = 0 := by
  have hpos : 0 < ∑ i, 1 / δ i := by
    by_contra h
    push Not at h
    have hs : ∑ i, 1 / δ i = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => (one_div_pos.2 (hδ i)).le)
    rw [hs, mul_zero] at h1; exact zero_ne_one h1
  have hg : 0 < g := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hpos.le
    linarith
  refine ⟨?_, ?_⟩
  · refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      ext i l
      by_cases h : i = l
      · subst h; simp
      · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
    · simp only [star_trivial]
      have e1 : (diagonal δ - g • Matrix.of fun (_ _ : ι) => (1 : ℝ)) *ᵥ x =
          fun i => δ i * x i - g * ∑ l, x l := by
        funext i
        rw [sub_mulVec, smul_mulVec, Pi.sub_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        congr 2
        simp [mulVec, dotProduct]
      have e : x ⬝ᵥ ((diagonal δ - g • Matrix.of fun (_ _ : ι) => (1 : ℝ)) *ᵥ x) =
          ∑ i, δ i * x i ^ 2 - g * (∑ i, x i) ^ 2 := by
        rw [e1]
        simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · rw [← Finset.sum_mul]; ring
      rw [e]
      have ht := Finset.sq_sum_div_le_sum_sq_div (s := univ) x (g := fun i => 1 / δ i)
        (fun i _ => one_div_pos.2 (hδ i))
      have e2 : ∑ i, x i ^ 2 / (1 / δ i) = ∑ i, δ i * x i ^ 2 :=
        Finset.sum_congr rfl fun i _ => by field_simp
      rw [e2, div_le_iff₀ hpos] at ht
      nlinarith
  · funext i
    simp only [sub_mulVec, mulVec_diagonal, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    have : (Matrix.of fun (_ _ : ι) => (1 : ℝ)) *ᵥ (fun i => 1 / δ i) = fun _ => ∑ l, 1 / δ l := by
      funext i; simp [mulVec, dotProduct]
    rw [this, h1]
    field_simp [(hδ i).ne']
    ring

end General

section Fit

variable {q t : ℕ}

lemma exists_ne_fin {t : ℕ} (ht : 2 ≤ t) (a0 : Fin t) : ∃ a : Fin t, a ≠ a0 := by
  by_cases h : a0 = ⟨0, by omega⟩
  · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
  · exact ⟨⟨0, by omega⟩, fun e => h e.symm⟩

/-- **Lemma 3, third assertion, for one deleted variable.** Under condition (1), `Σ` without any
one variable is in the `m`-factor model, `m = q + t - 3`. -/
theorem lemma3_fit_erase {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    (ht : 2 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (hc : Cond1 S0 Sig) (i0 : Fin q × Fin t) :
    InModel (q + t - 3) (subPattern Sig (univ.erase i0)) := by
  classical
  obtain ⟨j, a0⟩ := i0
  obtain ⟨K, w, hw, hwr⟩ := schur_gram S0 hS0.symm j (hS0.princ j)
  set g := schurG S0 j with hgdef
  have hg : 0 < g := (lemma3_pos hS0 hq j).2
  set γ : {a : Fin t // a ≠ a0} → ℝ := fun a => Sig (j, a.1) (j, a.1) - S0 j j with hγdef
  have hγ : ∀ a, 0 < γ a := fun a => sub_pos.2 ((hc j).1 a.1)
  obtain ⟨a1, ha1⟩ := exists_ne_fin ht a0
  have hne : (univ : Finset {a : Fin t // a ≠ a0}).Nonempty := ⟨⟨a1, ha1⟩, mem_univ _⟩
  set κ := g * ∑ a, 1 / γ a with hκdef
  have hκ1 : κ < 1 := by
    have h := (hc j).2 a0
    rw [Finset.sum_subtype (univ.erase a0) (p := fun a => a ≠ a0) (by simp)] at h
    exact h
  have hκ0 : 0 < κ := mul_pos hg (Finset.sum_pos (fun a _ => one_div_pos.2 (hγ a)) hne)
  set δ : {a : Fin t // a ≠ a0} → ℝ := fun a => κ * γ a with hδdef
  have hδ : ∀ a, 0 < δ a := fun a => mul_pos hκ0 (hγ a)
  have hsum : g * ∑ a, 1 / δ a = 1 := by
    have : ∑ a, 1 / δ a = (1 / κ) * ∑ a, 1 / γ a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        simp only [hδdef]; field_simp [(hγ a).ne', hκ0.ne']
    rw [this, ← mul_assoc, mul_comm g, mul_assoc, ← hκdef]
    field_simp [hκ0.ne']
  obtain ⟨hKpsd, hKker⟩ := diag_sub_const δ hδ g hsum
  set K' := diagonal δ - g • Matrix.of fun (_ _ : {a : Fin t // a ≠ a0}) => (1 : ℝ) with hK'
  have hK'r : K'.rank ≤ t - 2 := by
    have h := rank_le_card_sub_one K' (fun a => 1 / δ a)
      (fun e => by
        have := congrFun e ⟨a1, ha1⟩
        simp only [Pi.zero_apply] at this
        exact (one_div_pos.2 (hδ ⟨a1, ha1⟩)).ne' this) hKker
    have hcard : Fintype.card {a : Fin t // a ≠ a0} = t - 1 := by
      simp [Fintype.card_subtype_compl]
    omega
  set f : {a : Fin t // a ≠ a0} → Fin q × Fin t := fun a => (j, a.1) with hf
  have hfi : Function.Injective f := fun a b h => Subtype.ext (congrArg Prod.snd h)
  set H1 := gram ℝ (fun i : Fin q × Fin t => w i.1) with hH1
  have hH1r : H1.rank ≤ q - 1 := by
    rw [hH1, rank_gram]
    refine le_trans (Submodule.finrank_mono (span_mono ?_)) hwr
    rintro _ ⟨i, rfl⟩; exact ⟨i.1, rfl⟩
  have hH1e : ∀ i l, H1 i l = S0 i.1 l.1 + if i.1 = j ∧ l.1 = j then g else 0 := by
    intro i l; rw [hH1, gram_apply, hw]
  set H := H1 + embedMat f K' with hH
  have hHpsd : H.PosSemidef := (posSemidef_gram ℝ _).add (posSemidef_embedMat f hKpsd)
  have hHr : H.rank ≤ q + t - 3 :=
    (rank_add_le' _ _).trans (by have := rank_embedMat_le f K'; omega)
  -- entries away from the deleted variable
  have hKj : ∀ i l : Fin q × Fin t, i ≠ (j, a0) → l ≠ (j, a0) → i.1 = j → l.1 = j →
      embedMat f K' i l = (if i = l then κ * (Sig i i - S0 j j) else 0) - g := by
    intro i l hi hl hij hlj
    have hi2 : i.2 ≠ a0 := fun e => hi (Prod.ext hij e)
    have hl2 : l.2 ≠ a0 := fun e => hl (Prod.ext hlj e)
    have hL : embedMat f K' i l = K' ⟨i.2, hi2⟩ ⟨l.2, hl2⟩ := by
      have := embedMat_apply_apply f hfi K' ⟨i.2, hi2⟩ ⟨l.2, hl2⟩
      have ei : f ⟨i.2, hi2⟩ = i := Prod.ext hij.symm rfl
      have el : f ⟨l.2, hl2⟩ = l := Prod.ext hlj.symm rfl
      rwa [ei, el] at this
    rw [hL, hK', Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul, mul_one]
    by_cases h : i = l
    · subst h
      have ei : (j, i.2) = i := Prod.ext hij.symm rfl
      simp only [diagonal_apply_eq, hδdef, hγdef, ei, ↓reduceIte]
    · have h' : (⟨i.2, hi2⟩ : {a : Fin t // a ≠ a0}) ≠ ⟨l.2, hl2⟩ :=
        fun e => h (Prod.ext (hij.trans hlj.symm) (congrArg Subtype.val e))
      simp [diagonal_apply_ne _ h', h]
  have hKo : ∀ i l : Fin q × Fin t, ¬ (i.1 = j ∧ l.1 = j) → embedMat f K' i l = 0 := by
    intro i l h
    by_cases hi : i.1 = j
    · have hl : l.1 ≠ j := fun e => h ⟨hi, e⟩
      exact embedMat_apply_right f K' i l (fun b e => hl (by rw [← e]))
    · exact embedMat_apply_left f K' i l (fun a e => hi (by rw [← e]))
  rw [inModel_iff_exists_fit]
  refine ⟨subPattern H (univ.erase (j, a0)), hHpsd.submatrix _,
    (rank_submatrix_le _ _ _).trans hHr, ?_, ?_⟩
  · rintro ⟨i, hi⟩ ⟨l, hl⟩ hil
    have hil' : i ≠ l := fun e => hil (Subtype.ext e)
    have hi' : i ≠ (j, a0) := (mem_erase.1 hi).1
    have hl' : l ≠ (j, a0) := (mem_erase.1 hl).1
    simp only [subPattern, submatrix_apply, hH, Matrix.add_apply]
    rw [hSig.2 i l hil', hH1e]
    by_cases hb : i.1 = j ∧ l.1 = j
    · rw [hKj i l hi' hl' hb.1 hb.2]
      simp only [hb, hil', and_self, ↓reduceIte]
      ring
    · rw [hKo i l hb]
      simp only [hb, ↓reduceIte]; ring
  · rintro ⟨i, hi⟩
    have hi' : i ≠ (j, a0) := (mem_erase.1 hi).1
    simp only [subPattern, submatrix_apply, hH, Matrix.add_apply]
    rw [hH1e]
    by_cases hb : i.1 = j
    · rw [hKj i i hi' hi' hb hb]
      simp only [hb, and_self, ↓reduceIte]
      have hlt : S0 j j < Sig i i := by rw [← hb]; exact (hc i.1).1 i.2
      nlinarith
    · rw [hKo i i (fun h => hb h.1)]
      simp only [hb, false_and, ↓reduceIte, add_zero]
      exact (hc i.1).1 i.2

/-- **Lemma 3, third assertion.** If condition (1) holds, every proper principal submatrix of
`Σ` is in the `m`-factor model, `m = q + t - 3`. -/
theorem lemma3_proper {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    (ht : 2 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (hc : Cond1 S0 Sig) (T : Finset (Fin q × Fin t)) (hT : T ≠ univ) :
    InModel (q + t - 3) (subPattern Sig T) :=
  inModel_proper_of_erase (lemma3_fit_erase hS0 hq ht hSig hc) T hT

end Fit

end FreeDiagonal.StatisticalFactorAnalysis
