import FreeDiagonal.StatisticalFactorAnalysis.ReplicatedConverse

/-!
# Theorem 1 (exact test size), the last sentence of Theorem 2, and Section 6

The example matrix is `S0 = (1 + c) I - c J` with `c = 2/(2q - 3)`, which lies in
`(1/(q-1), 1/(q-2))` for `q ≥ 3` and is `2 > 1` for `q = 2` (one choice of `c` for all `q`).
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section Example

variable {q : ℕ}

/-- `S0 = (1 + c) I - c J`: diagonal `1`, off-diagonal `-c`. -/
def equiS (q : ℕ) (c : ℝ) : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun k l => if k = l then 1 else -c

lemma equiS_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ k l, M k l = if k = l then 1 else -c) (x : ι → ℝ) (k : ι) :
    (M *ᵥ x) k = (1 + c) * x k - c * ∑ l, x l := by
  simp only [mulVec, dotProduct, hM]
  rw [← Finset.sum_erase_add _ _ (mem_univ k)]
  have : ∀ l ∈ univ.erase k, (if k = l then (1 : ℝ) else -c) * x l = -c * x l := by
    intro l hl; simp [Ne.symm (ne_of_mem_erase hl)]
  rw [Finset.sum_congr rfl this]
  simp only [ite_true, one_mul]
  rw [← Finset.mul_sum, ← Finset.sum_erase_add (f := x) _ (mem_univ k)]
  ring

lemma equiS_form {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ k l, M k l = if k = l then 1 else -c) (x : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = (1 + c) * ∑ k, x k ^ 2 - c * (∑ k, x k) ^ 2 := by
  rw [dotProduct]
  simp_rw [equiS_mulVec c M hM x]
  have h1 : ∑ k, x k * ((1 + c) * x k) = (1 + c) * ∑ k, x k ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∑ k, x k * (c * ∑ l, x l) = c * (∑ k, x k) ^ 2 := by
    rw [← Finset.sum_mul]; ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]

lemma equiS_isLemma3 (hq : 2 ≤ q) : IsLemma3Matrix (equiS q (2 / (2 * q - 3))) := by
  classical
  set c : ℝ := 2 / (2 * q - 3) with hc
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 2 * q - 3 := by linarith
  have hc0 : 0 < c := div_pos (by norm_num) hden
  have hc2 : c ≤ 2 := by rw [hc, div_le_iff₀ hden]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext k l; simp [equiS, eq_comm]
  · -- the kernel is trivial
    intro hdet
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
    have hk : ∀ k, (1 + c) * v k = c * ∑ l, v l := by
      intro k
      have h1 := congrFun hv k
      have hform : (equiS q c *ᵥ v) k = (1 + c) * v k - c * ∑ l, v l :=
        equiS_mulVec c _ (fun k l => by simp [equiS]) v k
      rw [hform] at h1; simp at h1; linarith
    have hsum : (∑ l, v l) * (1 + c - c * q) = 0 := by
      have : ∑ k, (1 + c) * v k = ∑ k : Fin q, c * ∑ l, v l := Finset.sum_congr rfl fun k _ => hk k
      rw [← Finset.mul_sum, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    have hne : 1 + c - c * q ≠ 0 := by
      have : 1 + c - c * q = -1 / (2 * q - 3) := by rw [hc]; field_simp; ring
      rw [this]; exact div_ne_zero (by norm_num) hden.ne'
    have hs0 : ∑ l, v l = 0 := (mul_eq_zero.1 hsum).resolve_right hne
    apply hv0; funext k
    have := hk k; rw [hs0, mul_zero] at this
    have h1c : (1 + c) ≠ 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h1c
  · intro hpsd
    have := hpsd.dotProduct_mulVec_nonneg (fun _ => 1)
    simp only [star_trivial] at this
    rw [equiS_form c _ (fun k l => by simp [equiS])] at this
    simp only [one_pow, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at this
    have e : (1 + c) * q - c * q ^ 2 = -q / (2 * q - 3) := by rw [hc]; field_simp; ring
    rw [e] at this
    have : (-(q : ℝ)) / (2 * q - 3) < 0 := div_neg_of_neg_of_pos (by linarith) hden
    linarith
  · intro j
    refine PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      ext k l; simp [offPrinc, equiS, eq_comm]
    · simp only [star_trivial]
      rw [equiS_form c _ (fun k l => by simp [offPrinc, equiS, Subtype.ext_iff])]
      have hcard : Fintype.card {k : Fin q // k ≠ j} = q - 1 := by
        simp [Fintype.card_subtype_compl]
      have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset {k : Fin q // k ≠ j})) (f := x)
      rw [card_univ, hcard] at hcs
      have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hq1] at hcs
      have hpos : 0 < ∑ k, x k ^ 2 := by
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
        exact Finset.sum_pos' (fun k _ => sq_nonneg _)
          ⟨k, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))⟩
      have hlow : (1 + c) * ∑ k, x k ^ 2 - c * (∑ k, x k) ^ 2 ≥
          (1 + c - c * (q - 1)) * ∑ k, x k ^ 2 := by nlinarith
      have e : 1 + c - c * (q - 1) = 1 / (2 * q - 3) := by rw [hc]; field_simp; ring
      rw [e] at hlow
      have : 0 < 1 / (2 * (q : ℝ) - 3) * ∑ k, x k ^ 2 := mul_pos (one_div_pos.2 hden) hpos
      linarith

end Example

section PD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric matrix with constant diagonal `C` and off-diagonal entries bounded by `B`, with
`B · n < C`, is positive definite. -/
lemma posDef_of_large_diag (A : Matrix n n ℝ) (hA : A.IsSymm) (C B : ℝ) (hd : ∀ i, A i i = C)
    (ho : ∀ i l, i ≠ l → |A i l| ≤ B) (hB : 0 ≤ B) (hC : B * Fintype.card n < C) : A.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hA
  · simp only [star_trivial]
    have hterm : ∀ i l, (if i = l then C * x i ^ 2 else 0) - B * (|x i| * |x l|) ≤
        x i * (A i l * x l) := by
      intro i l
      by_cases h : i = l
      · subst h; simp only [ite_true, hd]
        have : 0 ≤ B * (|x i| * |x i|) := by positivity
        nlinarith [sq_nonneg (x i)]
      · simp only [h, ite_false, zero_sub]
        have h1 : |x i * (A i l * x l)| ≤ B * (|x i| * |x l|) := by
          rw [abs_mul, abs_mul]
          calc |x i| * (|A i l| * |x l|) = |A i l| * (|x i| * |x l|) := by ring
            _ ≤ B * (|x i| * |x l|) := mul_le_mul_of_nonneg_right (ho i l h) (by positivity)
        linarith [neg_abs_le (x i * (A i l * x l))]
    have hsum : C * ∑ i, x i ^ 2 - B * (∑ i, |x i|) ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => Finset.sum_le_sum
        (fun l (_ : l ∈ univ) => hterm i l))
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
      simp only [dotProduct, mulVec, Finset.mul_sum]
      have e : ∑ i, ∑ l, B * (|x i| * |x l|) = B * (∑ i, |x i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      rw [e, ← Finset.mul_sum] at this
      rw [← Finset.mul_sum]
      exact this
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset n)) (f := fun i => |x i|)
    simp only [sq_abs, card_univ] at hcs
    have hpos : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
      exact Finset.sum_pos' (fun k _ => sq_nonneg _)
          ⟨k, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))⟩
    have : B * (∑ i, |x i|) ^ 2 ≤ B * (Fintype.card n * ∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hB
    nlinarith

end PD

section Extremal

variable {q t : ℕ}

/-- The replicated matrix of `equiS` with constant diagonal `C`. -/
noncomputable def replEqui (q t : ℕ) (C : ℝ) : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ :=
  Matrix.of fun i l => if i = l then C else equiS q (2 / (2 * q - 3)) i.1 l.1

/-- For `q, t ≥ 2` there is a positive definite replicated matrix of `S0 = (1+c)I - cJ`
satisfying condition (1), with `c_i > s_j`. -/
theorem exists_extremal (hq : 2 ≤ q) (ht : 2 ≤ t) :
    ∃ Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ,
      IsReplicated (equiS q (2 / (2 * q - 3))) Sig ∧ Cond1 (equiS q (2 / (2 * q - 3))) Sig ∧
      (∀ i, equiS q (2 / (2 * q - 3)) i.1 i.1 < Sig i i) ∧ Sig.PosDef := by
  classical
  set S0 := equiS q (2 / (2 * q - 3)) with hS0
  have hL := equiS_isLemma3 hq
  set c : ℝ := 2 / (2 * q - 3) with hc
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 2 * q - 3 := by linarith
  have hc0 : 0 < c := div_pos (by norm_num) hden
  have hc2 : c ≤ 2 := by rw [hc, div_le_iff₀ hden]; linarith
  set Gs := ∑ j, schurG S0 j with hGs
  have hgpos : ∀ j, 0 < schurG S0 j := fun j => (lemma3_pos hL hq j).2
  have hgle : ∀ j, schurG S0 j ≤ Gs := fun j =>
    Finset.single_le_sum (fun k _ => (hgpos k).le) (mem_univ j)
  have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun k _ => (hgpos k).le
  set C : ℝ := 2 + Gs * t + 3 * (q * t) with hC
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hdiag1 : ∀ k : Fin q, S0 k k = 1 := fun k => by simp [hS0, equiS]
  have hsymm : (replEqui q t C).IsSymm := by
    ext i l
    by_cases h : i = l
    · subst h; rfl
    · have h1 : i.1 = l.1 ↔ l.1 = i.1 := eq_comm
      simp [replEqui, h, Ne.symm h, equiS, h1]
  refine ⟨replEqui q t C, ⟨hsymm, ?_⟩, ?_, ?_, ?_⟩
  · intro i l hil; simp only [replEqui, of_apply, hil, ite_false]; rfl
  · intro j
    refine ⟨fun a => ?_, fun a0 => ?_⟩
    · simp only [replEqui, of_apply, ite_true, hdiag1]
      nlinarith
    · simp only [replEqui, of_apply, ite_true, hdiag1]
      rw [Finset.sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hC1 : 0 < C - 1 := by nlinarith
      have ht1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [ht1, mul_one_div, ← mul_div_assoc, div_lt_one hC1]
      have := hgle j
      nlinarith [hgpos j]
  · intro i
    simp only [replEqui, of_apply, ite_true, hdiag1]
    nlinarith
  · refine posDef_of_large_diag _ hsymm C 2 (fun i => by simp [replEqui]) (fun i l hil => ?_)
      (by norm_num) ?_
    · simp only [replEqui, of_apply, hil, ite_false, equiS]
      split_ifs
      · norm_num
      · rw [abs_neg, abs_of_pos hc0]; exact hc2
    · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      push_cast; nlinarith

end Extremal

section Theorems

/-- **Theorem 2, last sentence.** For every `2 ≤ q ≤ m` there is a positive definite `Σ` on
`q (m + 3 - q)` variables whose least reference rank is `q`, which is not in the model (not even
in the weak model), while all its proper principal submatrices are in the model. -/
theorem theorem2_last (m q : ℕ) (hq : 2 ≤ q) (hqm : q ≤ m) :
    ∃ Sig : Matrix (Fin q × Fin (m + 3 - q)) (Fin q × Fin (m + 3 - q)) ℝ,
      Fintype.card (Fin q × Fin (m + 3 - q)) = q * (m + 3 - q) ∧ Sig.PosDef ∧
      IsLeast {r | ∃ G, IsReference Sig G ∧ G.rank = r} q ∧
      ¬ InWeakModel m Sig ∧ ¬ InModel m Sig ∧
      ∀ T : Finset (Fin q × Fin (m + 3 - q)), T ≠ univ → InModel m (subPattern Sig T) := by
  set t := m + 3 - q with htdef
  have ht : 3 ≤ t := by omega
  have hm : q + t - 3 = m := by omega
  obtain ⟨Sig, hR, hC, hlt, hpd⟩ := exists_extremal hq (by omega : 2 ≤ t)
  have hL := equiS_isLemma3 hq
  have hnw : ¬ InWeakModel m Sig := by
    rw [inWeakModel_iff_exists_weakFit]
    rintro ⟨G, hp, hr, ho, -⟩
    have := lemma3_no_psd hL hq (by omega) hR G hp ho
    omega
  refine ⟨Sig, by simp, hpd, lemma3_least_ref hL hq (by omega) hR hlt, hnw,
    fun h => hnw h.inWeakModel, fun T hT => ?_⟩
  have := lemma3_proper hL hq (by omega) hR hC T hT
  rwa [hm] at this

lemma half_mul (m : ℕ) : (m + 3) / 2 * (m + 3 - (m + 3) / 2) = (m + 3) ^ 2 / 4 := by
  obtain ⟨u, hu | hu⟩ := Nat.even_or_odd' (m + 3)
  · rw [hu]
    have h1 : 2 * u / 2 = u := by omega
    rw [h1, show 2 * u - u = u by omega, show (2 * u) ^ 2 = 4 * (u * u) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  · rw [hu]
    have h1 : (2 * u + 1) / 2 = u := by omega
    rw [h1, show 2 * u + 1 - u = u + 1 by omega,
      show (2 * u + 1) ^ 2 = 4 * (u * u + u) + 1 by ring]
    have : (4 * (u * u + u) + 1) / 4 = u * u + u := by omega
    rw [this]; ring

/-- An obstruction on `⌊(m+3)²/4⌋` variables: not in the weak model, every proper principal
submatrix in the model. -/
theorem obstruction (m : ℕ) :
    ∃ Sig : Matrix (Fin ((m + 3) ^ 2 / 4)) (Fin ((m + 3) ^ 2 / 4)) ℝ, Sig.IsSymm ∧
      ¬ InWeakModel m Sig ∧
      ∀ T : Finset (Fin ((m + 3) ^ 2 / 4)), T ≠ univ → InModel m (subPattern Sig T) := by
  classical
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    refine ⟨Matrix.of fun i j => if i = j then 1 else 1 / 2, ?_, ?_, ?_⟩
    · ext i j; simp [eq_comm]
    · rintro ⟨D, Λ, -, e⟩
      have := congrFun (congrFun e ⟨0, by norm_num⟩) ⟨1, by norm_num⟩
      simp [Fin.ext_iff] at this
    · intro T hT
      have hT1 : T.card ≤ 1 := by
        have := (Finset.card_lt_iff_ne_univ T).2 hT
        simp at this; omega
      have hsub : ∀ a b : T, a = b := fun a b =>
        Subtype.ext (Finset.card_le_one.1 hT1 _ a.2 _ b.2)
      refine ⟨fun _ => 1, 0, fun _ => one_pos, ?_⟩
      ext a b
      have := hsub a b; subst this
      simp [subPattern]
  · set q := (m + 3) / 2 with hqdef
    set t := m + 3 - q with htdef
    have hq : 2 ≤ q := by omega
    have ht : 2 ≤ t := by omega
    have hm : q + t - 3 = m := by omega
    have hN : q * t = (m + 3) ^ 2 / 4 := half_mul m
    obtain ⟨Sig, hR, hC, -, -⟩ := exists_extremal hq ht
    have hL := equiS_isLemma3 hq
    set e : Fin q × Fin t ≃ Fin ((m + 3) ^ 2 / 4) := finProdFinEquiv.trans (finCongr hN)
    refine ⟨Sig.submatrix e.symm e.symm, ?_, ?_, ?_⟩
    · ext i j; exact (symm_apply hR.1 _ _)
    · intro h
      have h2 := InWeakModel.comp_inj h e e.injective
      have e2 : (Sig.submatrix e.symm e.symm).submatrix e e = Sig := by ext i j; simp
      rw [e2, inWeakModel_iff_exists_weakFit] at h2
      obtain ⟨G, hp, hr, ho, -⟩ := h2
      have := lemma3_no_psd hL hq ht hR G hp ho
      omega
    · intro T hT
      obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
        by_contra hc; push Not at hc; exact hT (eq_univ_of_forall hc)
      have hfit := lemma3_fit_erase hL hq ht hR hC (e.symm i)
      rw [hm] at hfit
      have := hfit.comp_inj (fun a : T => (⟨e.symm a, mem_erase.2 ⟨fun h => hi
          (by rw [← e.symm.injective h]; exact a.2), mem_univ _⟩⟩ :
          (univ.erase (e.symm i) : Finset _)))
        (fun a b hab => Subtype.ext (e.symm.injective (by simpa using congrArg Subtype.val hab)))
      exact this

/-- **Theorem 1 (exact test size).** For every `m ≥ 0`,
`b_m = b̄_m = ⌊(m+3)²/4⌋`: this number is a valid test size for the model and for the weak
model, and no smaller number is. -/
theorem theorem1 (m : ℕ) :
    IsLeast {b | IsTestSize m b} ((m + 3) ^ 2 / 4) ∧
      IsLeast {b | IsWeakTestSize m b} ((m + 3) ^ 2 / 4) := by
  obtain ⟨Sig, hS, hnw, hprop⟩ := obstruction m
  have hlow : ∀ b, b < (m + 3) ^ 2 / 4 → ∀ T : Finset (Fin ((m + 3) ^ 2 / 4)),
      T.card ≤ b → T ≠ univ := fun b hb T hT e => by
    rw [e, card_univ, Fintype.card_fin] at hT; omega
  refine ⟨⟨fun N Sig' _ => ⟨fun h T _ => h.sub T, upper_bound m Sig'⟩, fun b hb => ?_⟩,
    ⟨fun N Sig' _ => ⟨fun h T _ => h.sub T, upper_bound_weak m Sig'⟩, fun b hb => ?_⟩⟩
  · by_contra hlt; push Not at hlt
    exact hnw ((hb _ Sig hS).2 (fun T hT => hprop T (hlow b hlt T hT))).inWeakModel
  · by_contra hlt; push Not at hlt
    exact hnw ((hb _ Sig hS).2 (fun T hT => (hprop T (hlow b hlt T hT)).inWeakModel))

/-- **Section 6.** `q (m + 3 - q) > 2m + 2` exactly when `3 ≤ q ≤ m` (for every integer `q`). -/
theorem section6_ineq (m : ℕ) (q : ℤ) : (2 * m + 2 : ℤ) < q * (m + 3 - q) ↔ 3 ≤ q ∧ q ≤ m := by
  have e : q * (m + 3 - q) - (2 * m + 2) = (q - 2) * ((m : ℤ) + 1 - q) := by ring
  constructor
  · intro h
    have hp : 0 < (q - 2) * ((m : ℤ) + 1 - q) := by linarith
    rcases lt_trichotomy (q - 2) 0 with h1 | h1 | h1
    · have : (m : ℤ) + 1 - q < 0 := by
        by_contra h2; push Not at h2; nlinarith
      have : (0 : ℤ) ≤ m := by positivity
      omega
    · rw [h1, zero_mul] at hp; exact absurd hp (lt_irrefl 0)
    · have : 0 < (m : ℤ) + 1 - q := by
        by_contra h2; push Not at h2; nlinarith
      omega
  · rintro ⟨h1, h2⟩
    have : 0 < (q - 2) * ((m : ℤ) + 1 - q) := mul_pos (by linarith) (by linarith)
    linarith

/-- **Section 6.** The test size exceeds `2(m+1)` by `⌊(m-1)²/4⌋`. -/
theorem section6_gap (m : ℕ) : (m + 3) ^ 2 / 4 = (m - 1) ^ 2 / 4 + (2 * m + 2) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show k + 1 - 1 = k by omega, show (k + 1 + 3) ^ 2 = k ^ 2 + (2 * (k + 1) + 2) * 4 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 4)]

end Theorems

end FreeDiagonal.StatisticalFactorAnalysis
