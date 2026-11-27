import Mathlib

/-!
# Lemma 2 (positivity)

Let `Φ` be a symmetric bilinear form of rank `r` on a real vector space `V`, and let
`W₁, …, W_t` (`t ≥ 2`) be linear maps from `V` to a Euclidean space of dimension `m'` with
`⟪W_a v, W_b w⟫ = Φ(v, w)` for all `v, w` and all `a ≠ b`. If `t ≥ m' - r + 3`, then `Φ` is
positive semidefinite.

Route (a slight simplification of the printed proof): if `Φ(v, v) = d < 0`, the vectors
`W_c v`, `c ≠ a`, are linearly independent (pair a vanishing combination with `W_a v` and with
each `W_e v`), so the space `P` orthogonal to them has dimension `m' - t + 1`; every functional
`Φ(x, ·)` is `⟪u, W_b ·⟫` for some `u ∈ P` plus a multiple of `Φ(v, ·)`, so `r ≤ m' - t + 2`.
The rank of `Φ` is the dimension of the range of `V → V*`, `x ↦ Φ(x, ·)`.
-/

open Module Submodule

namespace FreeDiagonal.StatisticalFactorAnalysis

/-- **Lemma 2 (positivity).** `Φ` symmetric bilinear on a real vector space `V` (any dimension),
of rank `r` (the dimension of the range of `x ↦ Φ(x, ·)`); `W : Fin t → V →ₗ E` with `t ≥ 2`,
`E` a Euclidean space of dimension `m'`, and `⟪W_a v, W_b w⟫ = Φ(v, w)` for `a ≠ b`. If
`t ≥ m' - r + 3` (written `m' + 3 ≤ t + r`), then `Φ(v, v) ≥ 0` for every `v`. -/
theorem lemma2 {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hΦ : ∀ v w, Φ v w = Φ w v) {m' r t : ℕ}
    (hE : finrank ℝ E = m') (hr : finrank ℝ (LinearMap.range Φ) = r)
    (W : Fin t → V →ₗ[ℝ] E) (ht2 : 2 ≤ t)
    (hW : ∀ a b, a ≠ b → ∀ v w, inner ℝ (W a v) (W b w) = Φ v w)
    (ht : m' + 3 ≤ t + r) :
    ∀ v, 0 ≤ Φ v v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hcon
  set d := Φ v v with hd
  have hd0 : d ≠ 0 := ne_of_lt hv
  set a : Fin t := ⟨0, by omega⟩ with ha
  set b : Fin t := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  set w : Fin t → E := fun c => W c v with hw
  have hcross : ∀ c e, c ≠ e → inner ℝ (w c) (w e) = d := fun c e h => hW c e h v v
  set w' : {c // c ≠ a} → E := fun c => w c with hw'
  -- the vectors `w_c`, `c ≠ a`, are independent
  have hli : LinearIndependent ℝ w' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∀ e, inner ℝ (∑ c, g c • w' c) (w e) = 0 := by
      intro e; rw [hg, inner_zero_left]
    have hs : ∑ c, g c = 0 := by
      have h1 := key a
      rw [sum_inner] at h1
      have h2 : ∑ c, inner ℝ (g c • w' c) (w a) = d * ∑ c, g c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [real_inner_smul_left, hw', hcross c a c.2, mul_comm]
      rw [h2] at h1
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hd0
      · exact h
    intro e
    have h1 := key e
    rw [sum_inner] at h1
    have h2 : ∑ c, inner ℝ (g c • w' c) (w e) =
        d * ∑ c, g c + g e * (inner ℝ (w e) (w e) - d) := by
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ e),
        ← Finset.sum_erase_add (f := fun c => d * g c) _ (Finset.mem_univ e)]
      have : ∀ c ∈ Finset.univ.erase e, inner ℝ (g c • w' c) (w e) = d * g c := by
        intro c hc
        have hce : c ≠ e := Finset.ne_of_mem_erase hc
        rw [real_inner_smul_left, hw', hcross c.1 e.1 (fun h => hce (Subtype.ext h)), mul_comm]
      rw [Finset.sum_congr rfl this, real_inner_smul_left]
      simp only [hw']
      ring
    rw [h2, hs, mul_zero, zero_add] at h1
    have hpos : 0 < inner ℝ (w e) (w e) - d := by
      have := real_inner_self_nonneg (x := w e)
      linarith
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)
  set K := span ℝ (Set.range w') with hK
  set P := Kᗮ with hP
  have hKdim : finrank ℝ K = t - 1 := by
    rw [hK, finrank_span_eq_card hli, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  have hPdim : finrank ℝ P + (t - 1) = m' := by
    have := Submodule.finrank_add_finrank_orthogonal K
    rw [hKdim, hE] at this
    change finrank ℝ Kᗮ + (t - 1) = m'
    omega
  -- `x' = x - (Φ x v / d) v` satisfies `Φ x' v = 0`, so `W_a x' ∈ P`
  have hmem : ∀ x : V, W a (x - (Φ x v / d) • v) ∈ P := by
    intro x
    rw [hP, Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      have hca : c.1 ≠ a := c.2
      rw [hw', hw]
      simp only
      rw [hW c.1 a hca, hΦ]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  set L : P →ₗ[ℝ] (V →ₗ[ℝ] ℝ) := (LinearMap.lcomp ℝ ℝ (W b)) ∘ₗ (innerₗ E) ∘ₗ P.subtype with hL
  have hrange : LinearMap.range Φ ≤ LinearMap.range L ⊔ span ℝ {Φ v} := by
    rintro f ⟨x, rfl⟩
    have e : Φ x = L ⟨_, hmem x⟩ + (Φ x v / d) • Φ v := by
      ext y
      simp only [hL, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.lcomp_apply', innerₗ_apply_apply, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hW a b hab]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have h1 := Submodule.finrank_mono hrange
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range L) (span ℝ {Φ v})
  have h3 : finrank ℝ (LinearMap.range L) ≤ finrank ℝ P := LinearMap.finrank_range_le L
  have h4 : finrank ℝ (span ℝ {Φ v}) ≤ 1 := by
    by_cases h0 : Φ v = 0
    · rw [h0, span_singleton_eq_bot.2 rfl, finrank_bot]; omega
    · rw [finrank_span_singleton h0]
  omega

end FreeDiagonal.StatisticalFactorAnalysis
