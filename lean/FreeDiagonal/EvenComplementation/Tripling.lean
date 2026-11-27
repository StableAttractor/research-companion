import FreeDiagonal.Graphs.EvenK

/-!
# Part 54-f in Lean: triplings of graphs with non-singular adjacency matrix

`tripling G₀` (vertices `W × Fin 3`): `(w, c) ~ (w', c')` iff `w ~ w'` in `G₀`. Each vertex of
`G₀` becomes three pairwise non-adjacent vertices, each edge a `K₃,₃`.

For `G₀` on `k ≥ 1` vertices with `det A₀ ≠ 0` over `F₂`:
* `mrF2_tripling`: `mr(F₂, tripling G₀) = k`;
* `rank_ge_of_diag_ne_zero'`: a completion with a non-zero diagonal entry has rank `≥ k + 1`
  (a `(k+1) × (k+1)` submatrix with Schur complement `1`);
* `c2_tripling`: `c₂(tripling G₀) = k + 1`;
* `c2_erase_le'`: deleting any vertex gives `c₂ ≤ k`: an explicit completion of rank `≤ k` with
  diagonal `1` on the two remaining copies, written as `L * Q` with `Q` having `k` rows; it uses
  `A₀⁻¹` and the fact that `A₀⁻¹` has zero diagonal (`inv_diag_eq_zero`);
* `even_card_of_det_ne_zero`: `k` is then even (`even_rank_of_zero_diag`).
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The tripling of `G₀`. -/
def tripling (G0 : SimpleGraph W) : SimpleGraph (W × Fin 3) := G0.comap Prod.fst

instance (G0 : SimpleGraph W) [DecidableRel G0.Adj] : DecidableRel (tripling G0).Adj :=
  fun p q => inferInstanceAs (Decidable (G0.Adj p.1 q.1))

omit [Fintype W] [DecidableEq W] in
@[simp] lemma tripling_adj (G0 : SimpleGraph W) (p q : W × Fin 3) :
    (tripling G0).Adj p q ↔ G0.Adj p.1 q.1 := Iff.rfl

variable (G0 : SimpleGraph W) [DecidableRel G0.Adj]

lemma fin3_12 (c : Fin 3) : c + 1 ≠ c + 2 := by revert c; decide
lemma fin3_10 (c : Fin 3) : c + 1 ≠ c := by revert c; decide
lemma fin3_02 (c : Fin 3) : c ≠ c + 2 := by revert c; decide

omit [Fintype W] [DecidableEq W] in
lemma adj_tripling_apply (p q : W × Fin 3) :
    (tripling G0).adjMatrix (ZMod 2) p q = G0.adjMatrix (ZMod 2) p.1 q.1 := by
  simp [adjMatrix_apply, tripling_adj]

omit [Fintype W] [DecidableEq W] in
lemma adj_tripling_eq :
    (tripling G0).adjMatrix (ZMod 2) = (G0.adjMatrix (ZMod 2)).submatrix Prod.fst Prod.fst := by
  ext p q; rw [adj_tripling_apply]; rfl

omit [DecidableEq W] in
lemma card_tripling : Fintype.card (W × Fin 3) = 3 * Fintype.card W := by
  simp [mul_comm]

/-- A non-singular adjacency matrix over `F₂` has even size. -/
theorem even_card_of_det_ne_zero (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) :
    Even (Fintype.card W) := by
  have h := even_rank_of_zero_diag (G0.adjMatrix (ZMod 2)) (isSymm_adjMatrix G0)
    (fun i => by simp [adjMatrix_apply])
  rwa [rank_of_det_ne_zero hdet] at h

variable {G0}

/-- `mr(F₂, tripling G₀) = k`. -/
theorem mrF2_tripling (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) :
    mrF2 (tripling G0) = Fintype.card W := by
  rw [mrF2_eq]
  apply le_antisymm
  · calc minCompRank ((tripling G0).adjMatrix (ZMod 2))
        ≤ ((tripling G0).adjMatrix (ZMod 2) + diagonal 0).rank := minCompRank_le _ 0
      _ = ((G0.adjMatrix (ZMod 2)).submatrix Prod.fst Prod.fst).rank := by
          rw [adj_tripling_eq, show (diagonal (0 : W × Fin 3 → ZMod 2)) = 0 by ext; simp,
            add_zero]
      _ ≤ (G0.adjMatrix (ZMod 2)).rank := rank_submatrix_le _ _ _
      _ ≤ Fintype.card W := rank_le_card_width _
  · have h := offDiag_rank_le_minCompRank ((tripling G0).adjMatrix (ZMod 2))
      (fun w : W => (w, (0 : Fin 3))) (fun w : W => (w, (1 : Fin 3)))
      (fun a b h => by simpa using congrArg Prod.snd h)
    have e : ((tripling G0).adjMatrix (ZMod 2)).submatrix (fun w : W => (w, (0 : Fin 3)))
        (fun w : W => (w, (1 : Fin 3))) = G0.adjMatrix (ZMod 2) := by
      ext a b; simp [adjMatrix_apply, tripling_adj]
    rw [e, rank_of_det_ne_zero hdet] at h
    exact h

/-- **Uniqueness.** A completion of the tripling with a non-zero diagonal entry has rank at least
`k + 1`. -/
theorem rank_ge_of_diag_ne_zero' (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0)
    (d : W × Fin 3 → ZMod 2) (p : W × Fin 3) (hp : d p ≠ 0) :
    Fintype.card W + 1 ≤ ((tripling G0).adjMatrix (ZMod 2) + diagonal d).rank := by
  classical
  obtain ⟨w, c⟩ := p
  have hd : d (w, c) = 1 := zmod2_eq_one_of_ne_zero hp
  set A0 := G0.adjMatrix (ZMod 2) with hA0
  have hA0w : A0 w w = 0 := by simp [hA0, adjMatrix_apply]
  have : Invertible A0 := invertibleOfIsUnitDet A0 (isUnit_iff_ne_zero.2 hdet)
  set r : W ⊕ Unit → W × Fin 3 := Sum.elim (fun v => (v, c + 1)) (fun _ => (w, c))
  set s : W ⊕ Unit → W × Fin 3 := Sum.elim (fun v => (v, c + 2)) (fun _ => (w, c))
  set B : Matrix W Unit (ZMod 2) := fun v _ => A0 v w
  set C : Matrix Unit W (ZMod 2) := fun _ v => A0 w v
  have hc1 : c + 1 ≠ c + 2 := fin3_12 c
  have hc2 : c + 1 ≠ c := fin3_10 c
  have hc3 : c ≠ c + 2 := fin3_02 c
  have e : ((tripling G0).adjMatrix (ZMod 2) + diagonal d).submatrix r s =
      fromBlocks A0 B C 1 := by
    ext (v | _) (v' | _)
    · have hne : ((v, c + 1) : W × Fin 3) ≠ (v', c + 2) := fun h => hc1 (congrArg Prod.snd h)
      simp [r, s, diagonal_apply_ne _ hne, adj_tripling_apply, hA0]
    · have hne : ((v, c + 1) : W × Fin 3) ≠ (w, c) := fun h => hc2 (congrArg Prod.snd h)
      rw [submatrix_apply, fromBlocks_apply₁₂]
      simp [r, s, B, diagonal_apply_ne _ hne, adjMatrix_apply, hA0]
    · have hne : ((w, c) : W × Fin 3) ≠ (v', c + 2) := fun h => hc3 (congrArg Prod.snd h)
      rw [submatrix_apply, fromBlocks_apply₂₁]
      simp [r, s, C, diagonal_apply_ne _ hne, adjMatrix_apply, hA0]
    · simp [r, s, adj_tripling_apply, ← hA0, hA0w, hd]
  have hCB : C * ⅟A0 * B = 0 := by
    rw [invOf_eq_nonsing_inv]
    ext a b
    have h1 : (C * A0⁻¹ * B) a b = (A0 * A0⁻¹ * A0) w w := by
      simp only [Matrix.mul_apply]; rfl
    rw [h1, mul_nonsing_inv A0 (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul, hA0w]
    rfl
  have hdet' : (fromBlocks A0 B C 1).det ≠ 0 := by
    rw [det_fromBlocks₁₁, hCB, sub_zero, det_one, mul_one]; exact hdet
  have h := rank_of_det_ne_zero hdet'
  rw [Fintype.card_sum, Fintype.card_unit] at h
  rw [← h, ← e]
  exact rank_submatrix_le _ _ _

/-- **`c₂(tripling G₀) = k + 1`** (for `k ≥ 1` and `det A₀ ≠ 0`). -/
theorem c2_tripling (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) (hk : 1 ≤ Fintype.card W) :
    c2 (tripling G0) = Fintype.card W + 1 := by
  have hpos : 0 < mrF2 (tripling G0) := by rw [mrF2_tripling hdet]; omega
  have := (c2_eq_mrF2_add_one_iff (tripling G0) hpos).2 (by
    intro d hd
    by_contra hne
    obtain ⟨p, hp⟩ : ∃ p, d p ≠ 0 := by
      by_contra h; push Not at h; exact hne (funext h)
    have := rank_ge_of_diag_ne_zero' hdet d p hp
    rw [hd, mrF2_tripling hdet] at this
    omega)
  rw [this, mrF2_tripling hdet]

/-! ### Deleting a vertex -/

omit [Fintype W] [DecidableEq W] in
/-- In characteristic 2, the quadratic form of an alternating matrix vanishes. -/
lemma quad_alt_eq_zero [Fintype W] (A : Matrix W W (ZMod 2)) (hA : A.IsSymm) (hd : ∀ i, A i i = 0)
    (y : W → ZMod 2) : ∑ a, ∑ b, y a * A a b * y b = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ (fun _ _ => mem_univ _)
    (fun _ _ => rfl)
  · intro x _
    have : A x.2 x.1 = A x.1 x.2 := by
      have := congrFun (congrFun hA x.1) x.2; simpa [transpose_apply] using this
    simp only [this]
    have e : y x.2 * A x.1 x.2 * y x.1 = y x.1 * A x.1 x.2 * y x.2 := by ring
    rw [e]; exact zmod2_add_self _
  · intro x _ hx heq
    apply hx
    have h1 : x.1 = x.2 := (congrArg Prod.fst heq).symm
    rw [h1, hd]; ring

/-- The inverse of a non-singular alternating matrix over `F₂` has zero diagonal. -/
lemma inv_diag_eq_zero (A : Matrix W W (ZMod 2)) (hA : A.IsSymm) (hd : ∀ i, A i i = 0)
    (hdet : A.det ≠ 0) (w : W) : A⁻¹ w w = 0 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hsym : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hA.eq]
  have e : A⁻¹ = A⁻¹ * A * A⁻¹ := by rw [nonsing_inv_mul A hu, Matrix.one_mul]
  rw [e]
  have h2 : (A⁻¹ * A * A⁻¹) w w = ∑ a, ∑ b, A⁻¹ w a * A a b * A⁻¹ w b := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have := congrFun (congrFun hsym b) w
    simp only [transpose_apply] at this
    rw [this]
  rw [h2]
  exact quad_alt_eq_zero A hA hd _

variable (G0)

/-- `Q`: `k` rows; row `v` is row `v` of the tripled adjacency matrix, plus `e_{p₁}` for `v = w`. -/
noncomputable def Qm (w : W) (p1 : W × Fin 3) : Matrix W (W × Fin 3) (ZMod 2) :=
  fun v q => G0.adjMatrix (ZMod 2) v q.1 + if v = w ∧ q = p1 then 1 else 0

/-- `L`: row `q` is `e_{q.1}`, except for the copies of `w` other than `p₁`: `e_w + (row w of
A₀⁻¹)`. -/
noncomputable def Lm (w : W) (p1 : W × Fin 3) : Matrix (W × Fin 3) W (ZMod 2) :=
  fun q v => if q.1 = w ∧ q ≠ p1 then (if v = w then 1 else 0) + (G0.adjMatrix (ZMod 2))⁻¹ w v
    else if q.1 = v then 1 else 0

variable {G0}

lemma fin3_third (c a b : Fin 3) (ha : a ≠ c) (ha' : a ≠ c + 1) (hb : b ≠ c) (hb' : b ≠ c + 1) :
    a = b := by
  revert c a b; decide

omit [Fintype W] in
lemma indic_third (w : W) (c : Fin 3) (q q' : W × Fin 3) (hqw : q.1 = w) (hq : q ≠ (w, c))
    (hq1 : q ≠ (w, c + 1)) (hq' : q' ≠ (w, c)) :
    ((if q' = (w, c + 1) then (1 : ZMod 2) else 0) + if w = q'.1 then 1 else 0) =
      if q = q' then 1 else 0 := by
  obtain ⟨wq, cq⟩ := q
  obtain ⟨w', c'⟩ := q'
  simp only at hqw
  subst hqw
  have hcq : cq ≠ c := fun h => hq (by rw [h])
  have hcq1 : cq ≠ c + 1 := fun h => hq1 (by rw [h])
  by_cases hw : wq = w'
  · subst hw
    have hc' : c' ≠ c := fun h => hq' (by rw [h])
    by_cases hc1 : c' = c + 1
    · subst hc1
      have : ¬ ((wq, cq) = (wq, c + 1)) := hq1
      rw [if_pos rfl, if_pos rfl, if_neg this]; decide
    · have := fin3_third c cq c' hcq hcq1 hc' hc1
      subst this
      have h2 : ¬ ((wq, cq) = (wq, c + 1)) := hq1
      rw [if_neg h2, if_pos rfl, if_pos rfl, zero_add]
  · have h1 : ¬ ((w', c') = (wq, c + 1)) := fun h => hw (congrArg Prod.fst h).symm
    have h3 : ¬ ((wq, cq) = (w', c')) := fun h => hw (congrArg Prod.fst h)
    simp only at h1 h3 ⊢
    rw [if_neg h1, if_neg hw, if_neg h3, add_zero]

theorem LQ_apply (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) (w : W) (c : Fin 3)
    (q q' : W × Fin 3) (hq : q ≠ (w, c)) (hq' : q' ≠ (w, c)) :
    (Lm G0 w (w, c + 1) * Qm G0 w (w, c + 1)) q q' =
      G0.adjMatrix (ZMod 2) q.1 q'.1 + if q = q' ∧ q.1 = w then 1 else 0 := by
  classical
  have hu : IsUnit (G0.adjMatrix (ZMod 2)).det := isUnit_iff_ne_zero.2 hdet
  have hNw : (G0.adjMatrix (ZMod 2))⁻¹ w w = 0 := inv_diag_eq_zero _ (isSymm_adjMatrix G0)
    (fun i => by simp [adjMatrix_apply]) hdet w
  have hNA : ∀ v', ∑ v, (G0.adjMatrix (ZMod 2))⁻¹ w v * G0.adjMatrix (ZMod 2) v v' =
      if w = v' then 1 else 0 := by
    intro v'
    have := congrFun (congrFun (nonsing_inv_mul _ hu) w) v'
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
  rw [Matrix.mul_apply]
  by_cases h1 : q.1 = w ∧ q ≠ (w, c + 1)
  · have e : ∀ v, Lm G0 w (w, c + 1) q v * Qm G0 w (w, c + 1) v q' =
        (if v = w then Qm G0 w (w, c + 1) w q' else 0) +
          (G0.adjMatrix (ZMod 2))⁻¹ w v * G0.adjMatrix (ZMod 2) v q'.1 +
          (G0.adjMatrix (ZMod 2))⁻¹ w v * (if v = w ∧ q' = (w, c + 1) then 1 else 0) := by
      intro v
      simp only [Lm, Qm, if_pos h1]
      by_cases hv : v = w
      · subst hv; simp only [if_true]; ring
      · simp only [hv, if_false]; ring
    rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', if_pos (mem_univ _), hNA]
    have e2 : ∑ v, (G0.adjMatrix (ZMod 2))⁻¹ w v *
        (if v = w ∧ q' = (w, c + 1) then (1 : ZMod 2) else 0) = 0 := by
      rw [Finset.sum_eq_single w]
      · simp [hNw]
      · intro b _ hb; simp [hb]
      · simp
    rw [e2, add_zero]
    simp only [Qm, true_and]
    rw [h1.1]
    have := indic_third w c q q' h1.1 hq h1.2 hq'
    rw [add_assoc, this]
    simp [h1.1]
  · have hq1 : ∀ v, Lm G0 w (w, c + 1) q v = if v = q.1 then 1 else 0 := by
      intro v; simp only [Lm, if_neg h1]
      by_cases h : q.1 = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [hq1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, if_true, Qm]
    congr 1
    by_cases hqw : q.1 = w
    · have hqp : q = (w, c + 1) := by
        by_contra h; exact h1 ⟨hqw, h⟩
      subst hqp
      by_cases hq'p : q' = (w, c + 1)
      · subst hq'p; simp
      · simp [Ne.symm hq'p, hq'p]
    · have : ¬ (q = q' ∧ q.1 = w) := fun h => hqw h.2
      simp [hqw, this]

/-- **Deleting a vertex** of the tripling leaves a graph with `c₂ ≤ k`. -/
theorem c2_erase_le' (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0) (p : W × Fin 3) :
    c2 ((tripling G0).induce ((univ.erase p : Finset _) : Set (W × Fin 3))) ≤ Fintype.card W := by
  classical
  obtain ⟨w, c⟩ := p
  set s : Finset (W × Fin 3) := univ.erase (w, c)
  set M := Lm G0 w (w, c + 1) * Qm G0 w (w, c + 1)
  set Ms : Matrix ↥(s : Set (W × Fin 3)) ↥(s : Set (W × Fin 3)) (ZMod 2) :=
    M.submatrix Subtype.val Subtype.val
  have hmem : ∀ u : ↥(s : Set (W × Fin 3)), u.1 ≠ (w, c) := by
    intro u; have := u.2; simpa [s] using this
  have hMs : ∀ u v : ↥(s : Set (W × Fin 3)), Ms u v =
      G0.adjMatrix (ZMod 2) u.1.1 v.1.1 + if u.1 = v.1 ∧ u.1.1 = w then 1 else 0 :=
    fun u v => LQ_apply hdet w c u.1 v.1 (hmem u) (hmem v)
  have hsymm : Ms.IsSymm := by
    ext u v
    rw [transpose_apply, hMs, hMs]
    have hs := congrFun (congrFun (isSymm_adjMatrix (α := ZMod 2) G0) v.1.1) u.1.1
    simp only [transpose_apply] at hs
    rw [hs]
    congr 1
    by_cases h : u.1 = v.1
    · rw [h]
    · have h' : v.1 ≠ u.1 := Ne.symm h
      simp [h, h']
  have hc1 : c + 1 ≠ c := fin3_10 c
  have hq : ((w, c + 1) : W × Fin 3) ∈ (s : Set (W × Fin 3)) := by
    simp [s, hc1]
  have hdiag : ∃ i, Ms i i ≠ 0 := by
    refine ⟨⟨_, hq⟩, ?_⟩
    rw [hMs]; simp [adjMatrix_apply]
  obtain ⟨s', hs', B, hB⟩ := lempel_diag Ms hsymm hdiag
  have hfit : IsSqFit ((tripling G0).induce (s : Set (W × Fin 3))) B := by
    intro u v huv
    rw [← hB, hMs, adjMatrix_apply]
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    simp only [comap_adj, Function.Embedding.coe_subtype, tripling_adj, huv', false_and,
      if_false, add_zero, adjMatrix_apply]
  calc _ ≤ s' := c2_le_of_sqFit _ B hfit
    _ ≤ Ms.rank := hs'
    _ ≤ M.rank := rank_submatrix_le _ _ _
    _ ≤ (Lm G0 w (w, c + 1)).rank := rank_mul_le_left _ _
    _ ≤ Fintype.card W := rank_le_card_width _

/-- **Every proper induced subgraph of the tripling has `c₂ ≤ k`.** -/
theorem c2_proper_induce_tripling (hdet : (G0.adjMatrix (ZMod 2)).det ≠ 0)
    (s : Finset (W × Fin 3)) (hs : s ≠ univ) :
    c2 ((tripling G0).induce (s : Set (W × Fin 3))) ≤ Fintype.card W := by
  obtain ⟨p, hp⟩ : ∃ p, p ∉ s := by
    by_contra h; push Not at h; exact hs (eq_univ_iff_forall.2 h)
  have hsub : s ⊆ univ.erase p := fun x hx => mem_erase.2 ⟨fun h => hp (h ▸ hx), mem_univ _⟩
  exact (c2_induce_mono _ hsub).trans (c2_erase_le' hdet p)

end FreeDiagonal.EvenComplementation
