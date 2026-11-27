import FreeDiagonal.StatisticalFactorAnalysis.Scaling

/-!
# Theorem 4 (positive correlations): the matrices `S_L = D B D + L w wᵀ`

`B = (1+c)I - cJ` (`c = 2/(2q-3)`), `d = (1, -1, …, -1)`, `D = diag(d)`,
`w = (q-1, 1, …, 1) > 0` with `w ⬝ d = 0`, and `S_L = D B D + L w wᵀ` for `L ≥ 0`.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

section SL

variable {q : ℕ}

/-- `d = (1, -1, …, -1)`. -/
def sgnv (q : ℕ) : Fin q → ℝ := fun k => if k.val = 0 then 1 else -1

/-- `w = (q - 1, 1, …, 1)`. -/
def wtv (q : ℕ) : Fin q → ℝ := fun k => if k.val = 0 then (q : ℝ) - 1 else 1

/-- `S_L = D B D + L w wᵀ`. -/
noncomputable def SL (q : ℕ) (L : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  diagonal (sgnv q) * equiS q (2 / (2 * q - 3)) * diagonal (sgnv q) + L • vecMulVec (wtv q) (wtv q)

lemma sgnv_sq (k : Fin q) : sgnv q k * sgnv q k = 1 := by
  unfold sgnv; split_ifs <;> norm_num

lemma wtv_pos (hq : 2 ≤ q) (k : Fin q) : 0 < wtv q k := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold wtv; split_ifs <;> linarith

lemma wtv_ge_one (hq : 2 ≤ q) (k : Fin q) : 1 ≤ wtv q k := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold wtv; split_ifs <;> linarith

lemma SL_apply (L : ℝ) (k l : Fin q) :
    SL q L k l = sgnv q k * sgnv q l * equiS q (2 / (2 * q - 3)) k l + L * (wtv q k * wtv q l) := by
  simp [SL, diagonal_mul, mul_diagonal, vecMulVec_apply]; ring

lemma SL_diag (L : ℝ) (k : Fin q) : SL q L k k = 1 + L * wtv q k ^ 2 := by
  rw [SL_apply, sgnv_sq]; simp [equiS, sq]

lemma equiS_abs_le (hq : 2 ≤ q) (k l : Fin q) : |equiS q (2 / (2 * q - 3)) k l| ≤ 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 2 * q - 3 := by linarith
  have hc0 : 0 < (2 : ℝ) / (2 * q - 3) := div_pos (by norm_num) hden
  have hc2 : (2 : ℝ) / (2 * q - 3) ≤ 2 := by rw [div_le_iff₀ hden]; linarith
  simp only [equiS, of_apply]
  split_ifs
  · norm_num
  · rw [abs_neg, abs_of_pos hc0]; exact hc2

lemma sum_sgnv_wtv (hq : 2 ≤ q) : ∑ k, sgnv q k * wtv q k = 0 := by
  have h0 : (0 : ℕ) < q := by omega
  rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨0, h0⟩]
  have : ∀ k : {k : Fin q // k ≠ ⟨0, h0⟩}, sgnv q k * wtv q k = -1 := by
    intro k
    have hk : (k : Fin q).val ≠ 0 := fun e => k.2 (Fin.ext e)
    simp [sgnv, wtv, hk]
  simp only [this, Finset.sum_const, card_univ, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_unique, nsmul_eq_mul, mul_neg, mul_one]
  simp only [sgnv, wtv, ite_true, one_mul]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma vecMulVec_self_mulVec {n : Type*} [Fintype n] (w x : n → ℝ) :
    vecMulVec w w *ᵥ x = (w ⬝ᵥ x) • w := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma form_add_rank_one {n : Type*} [Fintype n] (A : Matrix n n ℝ) (L : ℝ) (w x : n → ℝ) :
    x ⬝ᵥ ((A + L • vecMulVec w w) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) + L * (w ⬝ᵥ x) ^ 2 := by
  rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, vecMulVec_self_mulVec,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm x w]; ring

lemma SL_symm (L : ℝ) : (SL q L).IsSymm := by
  ext k l; rw [transpose_apply, SL_apply, SL_apply]
  simp only [equiS, of_apply, eq_comm (a := l)]; ring

lemma SL_isLemma3 (hq : 2 ≤ q) {L : ℝ} (hL : 0 ≤ L) : IsLemma3Matrix (SL q L) := by
  classical
  have hB := equiS_isLemma3 hq
  have hprinc : ∀ j, (offPrinc (SL q L) j).PosDef := by
    intro j
    set D' : Matrix {k // k ≠ j} {k // k ≠ j} ℝ := diagonal fun k => sgnv q k
    set w' : {k // k ≠ j} → ℝ := fun k => wtv q k
    have e : offPrinc (SL q L) j =
        D'ᴴ * offPrinc (equiS q (2 / (2 * q - 3))) j * D' + L • vecMulVec w' (star w') := by
      ext a b
      simp [offPrinc, SL_apply, D', w', conjTranspose_eq_transpose_of_trivial, diagonal_transpose,
        diagonal_mul, mul_diagonal, vecMulVec_apply]
      ring
    rw [e]
    have hinj : Function.Injective D'.mulVec := by
      intro x y h
      funext k
      have := congrFun h k
      simp only [D', mulVec_diagonal] at this
      have h1 := sgnv_sq (q := q) k
      have : sgnv q k * (sgnv q k * x k) = sgnv q k * (sgnv q k * y k) := by rw [this]
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, one_mul] at this
      exact this
    exact (hB.princ j).conjTranspose_mul_mul_same hinj |>.add_posSemidef
      ((posSemidef_vecMulVec_self_star w').smul hL)
  have hnot : ¬ (SL q L).PosSemidef := by
    intro hp
    have h1 := hp.dotProduct_mulVec_nonneg (sgnv q)
    simp only [star_trivial] at h1
    rw [SL, form_add_rank_one] at h1
    have e : sgnv q ⬝ᵥ ((diagonal (sgnv q) * equiS q (2 / (2 * q - 3)) * diagonal (sgnv q)) *ᵥ
        sgnv q) = (fun _ => (1 : ℝ)) ⬝ᵥ (equiS q (2 / (2 * q - 3)) *ᵥ fun _ => 1) := by
      simp only [dotProduct, mulVec, diagonal_mul, mul_diagonal, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have h1 := sgnv_sq (q := q) k; have h2 := sgnv_sq (q := q) l
      calc sgnv q k * (sgnv q k * equiS q (2 / (2 * q - 3)) k l * sgnv q l * sgnv q l)
          = (sgnv q k * sgnv q k) * equiS q (2 / (2 * q - 3)) k l * (sgnv q l * sgnv q l) := by
            ring
        _ = _ := by rw [h1, h2]; ring
    have hw0 : sgnv q ⬝ᵥ wtv q = 0 := by rw [dotProduct]; exact sum_sgnv_wtv hq
    rw [e, dotProduct_comm (wtv q), hw0] at h1
    have hneg : ¬ (equiS q (2 / (2 * q - 3))).PosSemidef := hB.not_psd
    -- `1ᵀ B 1 < 0`
    have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hden : (0 : ℝ) < 2 * q - 3 := by linarith
    rw [equiS_form (2 / (2 * (q : ℝ) - 3)) _ (fun k l => by simp [equiS])] at h1
    simp only [one_pow, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    have e2 : (1 + 2 / (2 * (q : ℝ) - 3)) * q - 2 / (2 * q - 3) * q ^ 2 = -q / (2 * q - 3) := by
      field_simp; ring
    have : (-(q : ℝ)) / (2 * q - 3) < 0 := div_neg_of_neg_of_pos (by linarith) hden
    nlinarith [e2]
  exact ⟨SL_symm L, det_ne_zero_of_princ _ (SL_symm L) ⟨0, by omega⟩ (hprinc _) hnot, hnot, hprinc⟩

lemma schurG_SL_le (hq : 2 ≤ q) {L : ℝ} (hL : 0 ≤ L) (j : Fin q) :
    schurG (SL q L) j ≤ schurG (SL q 0) j := by
  obtain ⟨x, hxj, hx⟩ := (schur_min (SL q L) (SL_symm L) j ((SL_isLemma3 hq hL).princ j)).2
  have h0 := (schur_min (SL q 0) (SL_symm 0) j ((SL_isLemma3 hq le_rfl).princ j)).1 x hxj
  have e : x ⬝ᵥ (SL q L *ᵥ x) = x ⬝ᵥ (SL q 0 *ᵥ x) + L * (wtv q ⬝ᵥ x) ^ 2 := by
    have : SL q L = SL q 0 + L • vecMulVec (wtv q) (wtv q) := by simp [SL]
    rw [this, form_add_rank_one]
  have : 0 ≤ L * (wtv q ⬝ᵥ x) ^ 2 := mul_nonneg hL (sq_nonneg _)
  linarith

end SL

section Repl

variable {q t : ℕ}

/-- A symmetric matrix with diagonal at least `C` and off-diagonal entries bounded by `B`, with
`B · n < C`, is positive definite. -/
lemma posDef_of_large_diag' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsSymm) (C B : ℝ) (hd : ∀ i, C ≤ A i i)
    (ho : ∀ i l, i ≠ l → |A i l| ≤ B) (hB : 0 ≤ B) (hC : B * Fintype.card n < C) : A.PosDef := by
  have h1 : (A - diagonal (fun i => A i i - C)).PosDef :=
    posDef_of_large_diag _ (by
      ext i l
      by_cases h : i = l
      · subst h; rfl
      · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h), symm_apply hA i l])
      C B (fun i => by simp) (fun i l hil => by simpa [diagonal_apply_ne _ hil] using ho i l hil)
      hB hC
  have h2 : (diagonal (fun i => A i i - C)).PosSemidef :=
    posSemidef_diagonal_iff.2 fun i => by linarith [hd i]
  have := h1.add_posSemidef h2
  simpa using this

/-- The replicated matrix of `S_L` with diagonal `V w_j²` on group `j`. -/
noncomputable def replSL (q t : ℕ) (L V : ℝ) : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ :=
  Matrix.of fun i l => if i = l then V * wtv q i.1 ^ 2 else SL q L i.1 l.1

lemma replSL_replicated (L V : ℝ) : IsReplicated (SL q L) (replSL q t L V) := by
  refine ⟨?_, fun i l hil => by simp [replSL, hil]⟩
  ext i l
  by_cases h : i = l
  · subst h; rfl
  · simp [replSL, h, Ne.symm h, symm_apply (SL_symm L) i.1 l.1]

/-- The bound `V₀` used for the diagonal. -/
noncomputable def V0 (q t : ℕ) : ℝ := 2 + 2 * (q * t) + t * ∑ j, schurG (SL q 0) j

lemma V0_spec (hq : 2 ≤ q) (ht : 2 ≤ t) :
    (∀ j, 1 + (t - 1) * schurG (SL q 0) j < V0 q t) ∧ 2 * (q * t) < V0 q t ∧ 0 ≤ V0 q t := by
  have hg : ∀ j, 0 < schurG (SL q 0) j := fun j => (lemma3_pos (SL_isLemma3 hq le_rfl) hq j).2
  have hsum : ∀ j, schurG (SL q 0) j ≤ ∑ k, schurG (SL q 0) k := fun j =>
    Finset.single_le_sum (fun k _ => (hg k).le) (mem_univ j)
  have hs0 : 0 ≤ ∑ k, schurG (SL q 0) k := Finset.sum_nonneg fun k _ => (hg k).le
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hqt : (0 : ℝ) ≤ q * t := by positivity
  refine ⟨fun j => ?_, ?_, ?_⟩
  · unfold V0; nlinarith [hsum j, hg j]
  · unfold V0; nlinarith
  · unfold V0; positivity

lemma replSL_cond1 (hq : 2 ≤ q) (ht : 2 ≤ t) {L V : ℝ} (hL : 0 ≤ L) (hV : V0 q t + L ≤ V) :
    Cond1 (SL q L) (replSL q t L V) := by
  obtain ⟨h1, -, -⟩ := V0_spec hq ht
  intro j
  have hw := wtv_ge_one hq j
  have hw2 : 1 ≤ wtv q j ^ 2 := by nlinarith
  have hgL := schurG_SL_le hq hL j
  have hgpos : 0 < schurG (SL q L) j := (lemma3_pos (SL_isLemma3 hq hL) hq j).2
  have hgl := h1 j
  have hg0 : 0 < schurG (SL q 0) j := (lemma3_pos (SL_isLemma3 hq le_rfl) hq j).2
  have hden : V0 q t * wtv q j ^ 2 - 1 ≤ V * wtv q j ^ 2 - (1 + L * wtv q j ^ 2) := by nlinarith
  have hV0w : V0 q t ≤ V0 q t * wtv q j ^ 2 := by nlinarith [(V0_spec hq ht).2.2]
  have htg : 0 < ((t : ℝ) - 1) * schurG (SL q 0) j := by
    have : (2 : ℝ) ≤ t := by exact_mod_cast ht
    exact mul_pos (by linarith) hg0
  refine ⟨fun a => ?_, fun a0 => ?_⟩
  · simp only [replSL, of_apply, ite_true, SL_diag]
    linarith [hden, hV0w, hgl, htg]
  · simp only [replSL, of_apply, ite_true, SL_diag]
    rw [Finset.sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have ht1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [ht1]
    have hpos : 0 < V * wtv q j ^ 2 - (1 + L * wtv q j ^ 2) := by nlinarith
    rw [mul_one_div, ← mul_div_assoc, div_lt_one hpos]
    have ht' : (0 : ℝ) ≤ (t : ℝ) - 1 := by
      have : (2 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hgL ht']

lemma replSL_posDef (hq : 2 ≤ q) (ht : 2 ≤ t) {L V : ℝ} (hL : 0 ≤ L) (hV : V0 q t + L ≤ V) :
    (replSL q t L V).PosDef := by
  classical
  obtain ⟨-, h2, h3⟩ := V0_spec hq ht
  have hbase : (replSL q t 0 (V0 q t)).PosDef := by
    refine posDef_of_large_diag' _ (replSL_replicated 0 _).1 (V0 q t) 2 (fun i => ?_)
      (fun i l hil => ?_) (by norm_num) ?_
    · simp only [replSL, of_apply, ite_true]
      have := wtv_ge_one hq i.1
      have hw2 : 1 ≤ wtv q i.1 ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hw2 h3]
    · simp only [replSL, of_apply, hil, ite_false, SL_apply, zero_mul, add_zero]
      rw [abs_mul, abs_mul]
      have e1 : |sgnv q i.1| = 1 := by unfold sgnv; split_ifs <;> simp
      have e2 : |sgnv q l.1| = 1 := by unfold sgnv; split_ifs <;> simp
      rw [e1, e2, one_mul, one_mul]
      exact equiS_abs_le hq _ _
    · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; linarith
  set wh : Fin q × Fin t → ℝ := fun i => wtv q i.1
  have e : replSL q t L V = replSL q t 0 (V0 q t) + L • vecMulVec wh (star wh) +
      diagonal (fun i => (V - V0 q t - L) * wtv q i.1 ^ 2) := by
    ext i l
    by_cases h : i = l
    · subst h; simp [replSL, wh, vecMulVec_apply, sq]; ring
    · simp [replSL, h, wh, vecMulVec_apply, SL_apply]
  rw [e]
  refine (hbase.add_posSemidef ((posSemidef_vecMulVec_self_star wh).smul hL)).add_posSemidef
    (posSemidef_diagonal_iff.2 fun i => ?_)
  have : 0 ≤ V - V0 q t - L := by linarith
  positivity

end Repl

section Corr

variable {q t : ℕ}

/-- Rational versions of `d`, `w` and `B`. -/
def sgnq (q : ℕ) (k : Fin q) : ℚ := if k.val = 0 then 1 else -1
def wtq (q : ℕ) (k : Fin q) : ℚ := if k.val = 0 then (q : ℚ) - 1 else 1
def Bq (q : ℕ) (k l : Fin q) : ℚ := if k = l then 1 else -(2 / (2 * q - 3))

/-- `κ_jk = d_j d_k B_jk / (w_j w_k)`. -/
def kap (q : ℕ) (k l : Fin q) : ℚ := sgnq q k * sgnq q l * Bq q k l / (wtq q k * wtq q l)

/-- The rational correlation matrix: off-diagonal entry `r (κ_jk / L + 1)` between groups `j, k`. -/
def corrQ (q t : ℕ) (r L : ℚ) : Matrix (Fin q × Fin t) (Fin q × Fin t) ℚ :=
  Matrix.of fun i l => if i = l then 1 else r * (kap q i.1 l.1 / L + 1)

lemma kap_cast (k l : Fin q) : ((kap q k l : ℚ) : ℝ) =
    sgnv q k * sgnv q l * equiS q (2 / (2 * q - 3)) k l / (wtv q k * wtv q l) := by
  simp only [kap, sgnq, wtq, Bq, sgnv, wtv, equiS, of_apply]
  split_ifs <;> push_cast <;> ring

lemma kap_abs_le (hq : 2 ≤ q) (k l : Fin q) : |((kap q k l : ℚ) : ℝ)| ≤ 2 := by
  rw [kap_cast, abs_div, abs_mul, abs_mul]
  have e1 : |sgnv q k| = 1 := by unfold sgnv; split_ifs <;> simp
  have e2 : |sgnv q l| = 1 := by unfold sgnv; split_ifs <;> simp
  rw [e1, e2, one_mul, one_mul, div_le_iff₀ (abs_pos.2 (mul_pos (wtv_pos hq k)
    (wtv_pos hq l)).ne')]
  have h1 := wtv_ge_one hq k
  have h2 := wtv_ge_one hq l
  rw [abs_of_pos (mul_pos (wtv_pos hq k) (wtv_pos hq l))]
  have := equiS_abs_le hq k l
  nlinarith

/-- `corrQ` is the rescaling of `replSL` by `p_i = 1 / (w_j √V)` with `V = L / r`. -/
lemma corrQ_eq (hq : 2 ≤ q) {r L : ℚ} (hr : 0 < r) (hL : 0 < L) :
    (corrQ q t r L).map (fun x : ℚ => (x : ℝ)) =
      diagonal (fun i : Fin q × Fin t => (wtv q i.1 * Real.sqrt ((L : ℝ) / r))⁻¹) *
        replSL q t L ((L : ℝ) / r) *
        diagonal (fun i : Fin q × Fin t => (wtv q i.1 * Real.sqrt ((L : ℝ) / r))⁻¹) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hV : (0 : ℝ) < (L : ℝ) / r := div_pos hL' hr'
  have hs : Real.sqrt ((L : ℝ) / r) * Real.sqrt ((L : ℝ) / r) = L / r :=
    Real.mul_self_sqrt hV.le
  have hs0 : 0 < Real.sqrt ((L : ℝ) / r) := Real.sqrt_pos.2 hV
  ext i l
  simp only [map_apply, diagonal_mul, mul_diagonal, corrQ, replSL, of_apply]
  have hwi := wtv_pos hq i.1
  have hwl := wtv_pos hq l.1
  by_cases h : i = l
  · subst h
    simp only [ite_true, Rat.cast_one]
    field_simp
    rw [show Real.sqrt (↑L / ↑r) ^ 2 = L / r by rw [sq]; exact hs]
    field_simp
  · simp only [h, ite_false, SL_apply]
    push_cast
    rw [kap_cast]
    field_simp
    rw [show Real.sqrt (↑L / ↑r) ^ 2 = L / r by rw [sq]; exact hs]
    field_simp

/-- Theorem 4 on the replicated index set. -/
theorem theorem4_repl (hq : 2 ≤ q) (ht : 2 ≤ t) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Matrix (Fin q × Fin t) (Fin q × Fin t) ℚ, C.IsSymm ∧ (∀ i, C i i = 1) ∧
      (∀ i l, 0 < C i l) ∧ (C.map (fun x : ℚ => (x : ℝ))).PosDef ∧
      (∀ i l, |(C i l : ℝ) - (if i = l then 1 else ρ)| < ε) ∧
      ¬ InWeakModel (q + t - 3) (C.map (fun x : ℚ => (x : ℝ))) ∧
      ∀ T : Finset (Fin q × Fin t), T ≠ univ →
        InModel (q + t - 3) (subPattern (C.map (fun x : ℚ => (x : ℝ))) T) := by
  classical
  -- choose `r`
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
    (show max 0 (ρ - ε / 2) < min 1 (ρ + ε / 2) by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨by norm_num, by linarith⟩, by linarith, by linarith⟩)
  rw [max_lt_iff] at hr1
  rw [lt_min_iff] at hr2
  have hr0 : (0 : ℝ) < r := hr1.1
  have hr1' : (r : ℝ) < 1 := hr2.1
  have hrρ : |(r : ℝ) - ρ| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith [hr2.2], by linarith [hr1.2]⟩
  -- choose `L`
  set V0r := V0 q t with hV0r
  obtain ⟨M, hM⟩ := exists_nat_gt (2 + V0r * r / (1 - r) + 4 * r / ε)
  have hV0 : 0 ≤ V0r := (V0_spec hq ht).2.2
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have ha : 0 ≤ V0r * r / (1 - r) := div_nonneg (mul_nonneg hV0 hr0.le) h1r.le
  have hb : 0 ≤ 4 * r / ε := div_nonneg (by linarith) hε.le
  set L : ℚ := (M : ℚ) with hLdef
  have hLr : (L : ℝ) = M := by rw [hLdef]; push_cast; rfl
  have hL2 : (2 : ℝ) < L := by rw [hLr]; linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL0
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr0
  have hLa : V0r * r / (1 - r) ≤ L := by rw [hLr]; linarith
  have hLb : 4 * r / ε < L := by rw [hLr]; linarith
  have hVge : V0 q t + L ≤ (L : ℝ) / r := by
    rw [le_div_iff₀ hr0]
    have := (div_le_iff₀ h1r).1 hLa
    rw [← hV0r]; nlinarith
  have hLnn : (0 : ℝ) ≤ L := hL0.le
  set p : Fin q × Fin t → ℝ := fun i => (wtv q i.1 * Real.sqrt ((L : ℝ) / r))⁻¹ with hpdef
  have hp : ∀ i, p i ≠ 0 := fun i => inv_ne_zero (mul_pos (wtv_pos hq i.1)
    (Real.sqrt_pos.2 (div_pos hL0 hr0))).ne'
  have heq := corrQ_eq (t := t) hq hrq hLq
  rw [← hpdef] at heq
  have hR := replSL_replicated (q := q) (t := t) (L : ℝ) ((L : ℝ) / r)
  have hS := SL_isLemma3 hq hLnn
  -- entries
  have hoff : ∀ i l, i ≠ l → ((corrQ q t r L i l : ℚ) : ℝ) =
      r * (((kap q i.1 l.1 : ℚ) : ℝ) / L + 1) := by
    intro i l h; simp [corrQ, h]
  have hk : ∀ i l : Fin q × Fin t, |((kap q i.1 l.1 : ℚ) : ℝ) / L| ≤ 2 / L := fun i l => by
    rw [abs_div, abs_of_pos hL0]; exact div_le_div_of_nonneg_right (kap_abs_le hq _ _) hL0.le
  refine ⟨corrQ q t r L, ?_, fun i => by simp [corrQ], fun i l => ?_, ?_, fun i l => ?_, ?_,
    fun T hT => ?_⟩
  · ext i l
    by_cases h : i = l
    · subst h; rfl
    · have e : kap q l.1 i.1 = kap q i.1 l.1 := by
        have hc : (l.1 = i.1) ↔ (i.1 = l.1) := eq_comm
        simp only [kap, Bq, hc]; ring
      simp [corrQ, h, Ne.symm h, e]
  · by_cases h : i = l
    · simp [corrQ, h]
    · have : (0 : ℝ) < ((corrQ q t r L i l : ℚ) : ℝ) := by
        rw [hoff i l h]
        have := (abs_le.1 (hk i l)).1
        have h2L : 2 / (L : ℝ) < 1 := by rw [div_lt_one hL0]; exact hL2
        exact mul_pos hr0 (by linarith)
      exact_mod_cast this
  · rw [heq]
    have hpd := replSL_posDef hq ht hLnn hVge
    have := hpd.conjTranspose_mul_mul_same (B := diagonal p) (fun x y hxy => by
      funext i
      have := congrFun hxy i
      simp only [mulVec_diagonal] at this
      exact mul_left_cancel₀ (hp i) this)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  · by_cases h : i = l
    · subst h; simp [corrQ, hε]
    · simp only [h, ite_false]
      rw [hoff i l h]
      have h1 := hk i l
      have : (r : ℝ) * (((kap q i.1 l.1 : ℚ) : ℝ) / L + 1) - ρ =
          ((r : ℝ) - ρ) + r * (((kap q i.1 l.1 : ℚ) : ℝ) / L) := by ring
      rw [this]
      calc |((r : ℝ) - ρ) + r * (((kap q i.1 l.1 : ℚ) : ℝ) / L)|
          ≤ |(r : ℝ) - ρ| + |r * (((kap q i.1 l.1 : ℚ) : ℝ) / L)| := abs_add_le _ _
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add_of_lt_of_le hrρ ?_
            rw [abs_mul, abs_of_pos hr0]
            have e2 : (r : ℝ) * (2 / L) ≤ ε / 2 := by
              have := (div_lt_iff₀ hε).1 hLb
              rw [mul_div_assoc', div_le_iff₀ hL0]; nlinarith
            nlinarith [mul_le_mul_of_nonneg_left h1 hr0.le]
        _ = ε := by ring
  · rw [heq, inWeakModel_scale_iff _ p hp, inWeakModel_iff_exists_weakFit]
    rintro ⟨G, hpG, hrG, hoG, -⟩
    have := lemma3_no_psd hS hq ht hR G hpG hoG
    omega
  · rw [heq, subPattern_scale, inModel_scale_iff (subPattern (replSL q t (L : ℝ) ((L : ℝ) / r)) T) (fun a : T => p a) (fun a => hp a)]
    exact lemma3_proper hS hq ht hR (replSL_cond1 hq ht hLnn hVge) T hT

/-- Theorem 4 on `N = ⌊(m+3)²/4⌋` variables. -/
theorem theorem4_fin (m : ℕ) (hm : 1 ≤ m) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Matrix (Fin ((m + 3) ^ 2 / 4)) (Fin ((m + 3) ^ 2 / 4)) ℚ, C.IsSymm ∧
      (∀ i, C i i = 1) ∧ (∀ i l, 0 < C i l) ∧ (C.map (fun x : ℚ => (x : ℝ))).PosDef ∧
      (∀ i l, |(C i l : ℝ) - (if i = l then 1 else ρ)| < ε) ∧
      ¬ InWeakModel m (C.map (fun x : ℚ => (x : ℝ))) ∧
      ∀ T : Finset (Fin ((m + 3) ^ 2 / 4)), T ≠ univ →
        InModel m (subPattern (C.map (fun x : ℚ => (x : ℝ))) T) := by
  classical
  set q := (m + 3) / 2 with hqdef
  set t := m + 3 - q with htdef
  have hq : 2 ≤ q := by omega
  have ht : 2 ≤ t := by omega
  have hm' : q + t - 3 = m := by omega
  have hN : q * t = (m + 3) ^ 2 / 4 := half_mul m
  obtain ⟨C, hsy, hd, hpos, hpd, hclose, hnw, hprop⟩ := theorem4_repl hq ht ρ hρ0 hρ1 ε hε
  rw [hm'] at hnw hprop
  set e : Fin q × Fin t ≃ Fin ((m + 3) ^ 2 / 4) := finProdFinEquiv.trans (finCongr hN)
  refine ⟨C.submatrix e.symm e.symm, ?_, fun i => hd _, fun i l => hpos _ _, ?_,
    fun i l => ?_, ?_, ?_⟩
  · ext i l; exact congrFun (congrFun hsy (e.symm i)) (e.symm l)
  · exact hpd.submatrix e.symm.injective
  · have := hclose (e.symm i) (e.symm l)
    simp only [submatrix_apply]
    by_cases h : i = l
    · subst h; simpa using this
    · have h' : e.symm i ≠ e.symm l := fun h2 => h (e.symm.injective h2)
      simpa [h, h'] using this
  · intro h
    have h2 := InWeakModel.comp_inj h e e.injective
    have e2 : ((C.submatrix e.symm e.symm).map (fun x : ℚ => (x : ℝ))).submatrix e e =
        C.map (fun x : ℚ => (x : ℝ)) := by ext i j; simp
    rw [e2] at h2
    exact hnw h2
  · intro T hT
    obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
      by_contra hc; push Not at hc; exact hT (eq_univ_of_forall hc)
    have hne : univ.erase (e.symm i) ≠ univ := fun h => by
      have : e.symm i ∈ univ.erase (e.symm i) := by rw [h]; exact mem_univ _
      simp at this
    have hfit := hprop (univ.erase (e.symm i)) hne
    have := hfit.comp_inj (fun a : T => (⟨e.symm a, mem_erase.2 ⟨fun h => hi
        (by rw [← e.symm.injective h]; exact a.2), mem_univ _⟩⟩ :
        (univ.erase (e.symm i) : Finset _)))
      (fun a b hab => Subtype.ext (e.symm.injective (by simpa using congrArg Subtype.val hab)))
    exact this

end Corr

end FreeDiagonal.StatisticalFactorAnalysis
