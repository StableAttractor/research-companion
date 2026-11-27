import FreeDiagonal.Closure.Threshold

/-!
# The statements of the closure-threshold paper in its own phrasing

"The Sharp 2k+2 Threshold for Set-Theoretic Finiteness in Algebraic Factor Analysis",
Sections 1 and 2. The proofs are in `Closure/`; this file only restates them in the paper's
form.

* `cost_eq_card_sub_finrank_ker`: `cost(G, d) = n - dim Ker(G, d)`, with `Ker(G, d)` defined by
  the paper's conditions (`dialKer`) and `cost(G, d) = rank (dialMat G d)`.
* `formula_2_global`, `formula_2_sub`: formula (2) as two equalities, for any completion `G`.
* `pivotOK_iff_isUnit_det`: `PivotOK G S` iff the block `G[S, S]` is invertible.
* `lemma_1_invertible`, `lemma_2_invertible`: Lemmas 1 and 2 with invertibility.
* `theorem_1_two_rho`: the addendum `|T| ≤ 2 ρ` of Theorem 1.
-/

open Matrix Finset Module

namespace FreeDiagonal

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- `Ker(G, d) = {v : v_i = 0 if d_i = ∞, (G v)_i = d_i v_i otherwise}` (Section 1). -/
def dialKer (G : Matrix n n F) (d : n → Option F) : Submodule F (n → F) where
  carrier := {v | ∀ i, DialCond (d i) (v i) ((G *ᵥ v) i)}
  zero_mem' := fun i => by cases h : d i <;> simp [DialCond, h]
  add_mem' := fun {v w} hv hw i => by
    have h1 := hv i; have h2 := hw i
    cases h : d i <;> simp only [h, DialCond] at h1 h2 ⊢
    · simp [h1, h2]
    · rw [mulVec_add, Pi.add_apply, Pi.add_apply, h1, h2]; ring
  smul_mem' := fun c v hv i => by
    have h1 := hv i
    cases h : d i <;> simp only [h, DialCond] at h1 ⊢
    · simp [h1]
    · rw [mulVec_smul, Pi.smul_apply, Pi.smul_apply, h1, smul_eq_mul, smul_eq_mul]; ring

lemma dialKer_eq_ker (G : Matrix n n F) (d : n → Option F) :
    dialKer G d = LinearMap.ker (dialMat G d).mulVecLin := by
  ext v; rw [mem_ker_dialMat]; rfl

/-- **`cost(G, d) = n - dim Ker(G, d)`** (Section 1), with `cost(G, d) = rank (dialMat G d)`. -/
theorem cost_eq_card_sub_finrank_ker (G : Matrix n n F) (d : n → Option F) :
    (dialMat G d).rank = Fintype.card n - finrank F (dialKer G d) := by
  have h := rank_add_finrank_ker (dialMat G d)
  rw [dialKer_eq_ker]; omega

/-- A completion of `x` is `x + diagonal g` for `g i = G i i - x i i`. -/
lemma eq_add_diagonal_of_completion (x G : Matrix n n F) (hG : ∀ i j, i ≠ j → G i j = x i j) :
    G = x + diagonal (fun i => G i i - x i i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [hG i j h, diagonal_apply_ne _ h]

/-- **Formula (2), first equality**: `ρ(x) = min_d cost(G, d)` for every completion `G`. -/
theorem formula_2_global (x G : Matrix n n F) (hG : ∀ i j, i ≠ j → G i j = x i j) :
    closRank x = ⨅ d : n → Option F, (dialMat G d).rank := by
  rw [eq_add_diagonal_of_completion x G hG]
  set g := fun i => G i i - x i i
  apply le_antisymm
  · exact le_ciInf fun d => closRank_le_cost x g d
  · obtain ⟨D, hD⟩ := exists_closRank x
    obtain ⟨e, he⟩ := exists_minCompRank (subPattern x Dᶜ)
    obtain ⟨d, -, hd⟩ := exists_dial_of_deletion x g D e
    refine (ciInf_le (OrderBot.bddBelow _) d).trans ?_
    rw [hd, he, hD]

/-- `ρ(x_T) + |E ∖ T| ≤ cost(G, d)` whenever `d = ∞` off `T`. -/
lemma closRank_sub_add_le_cost (x : Matrix n n F) (g : n → F) (T : Finset n)
    (d : n → Option F) (hd : ∀ i ∉ T, d i = none) :
    closRank (subPattern x T) + (univ \ T).card ≤ (dialMat (x + diagonal g) d).rank := by
  classical
  set N : Finset n := univ.filter (fun i => d i = none) with hN
  have hNiff : ∀ i, d i = none ↔ i ∈ N := fun i => by simp [hN]
  rw [rank_dialMat_eq x g d N hNiff]
  -- the deletion set inside `T`
  set D' : Finset T := univ.filter (fun a : T => d a = none) with hD'
  have h1 := closRank_le (subPattern x T) D'
  have h2 : minCompRank (subPattern (subPattern x T) D'ᶜ) ≤ minCompRank (subPattern x Nᶜ) := by
    refine minCompRank_le_of_embedding (subPattern x Nᶜ) _
      (fun a : ↥(D'ᶜ) => (⟨a.1.1, ?_⟩ : ↥(Nᶜ))) ?_ (fun _ _ _ => rfl)
    · have : (a.1 : T) ∉ D' := mem_compl.1 a.2
      rw [mem_compl, ← hNiff]; simpa [hD'] using this
    · intro a b hab
      have := congrArg (fun z : ↥(Nᶜ) => (z : n)) hab
      exact Subtype.ext (Subtype.ext this)
  have h3 := minCompRank_le (subPattern x Nᶜ) (fun a : ↥(Nᶜ) => g a - (d a).getD 0)
  have hcard : N.card = (univ \ T).card + D'.card := by
    have hsub : univ \ T ⊆ N := fun i hi => by
      rw [← hNiff]; exact hd i (by simpa using hi)
    have e1 : N = (univ \ T) ∪ (N ∩ T) := by
      ext i
      simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_inter]
      constructor
      · intro h
        by_cases hi : i ∈ T
        · exact Or.inr ⟨h, hi⟩
        · exact Or.inl hi
      · rintro (h | h)
        · exact hsub (by simpa using h)
        · exact h.1
    have e2 : Disjoint (univ \ T) (N ∩ T) := by
      rw [Finset.disjoint_left]; intro i h1 h2; simp at h1; exact h1 (mem_inter.1 h2).2
    have e3 : D'.card = (N ∩ T).card := by
      rw [hD']
      refine Finset.card_bij (fun a _ => (a : n)) ?_ ?_ ?_
      · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha
        exact mem_inter.2 ⟨(hNiff _).1 ha, a.2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro i hi
        obtain ⟨hiN, hiT⟩ := mem_inter.1 hi
        exact ⟨⟨i, hiT⟩, by simpa using (hNiff i).2 hiN, rfl⟩
    rw [e3]; conv_lhs => rw [e1]
    exact Finset.card_union_of_disjoint e2
  omega

/-- **Formula (2), second equality**: `ρ(x_T) + |E ∖ T| = min {cost(G, d) : d = ∞ off T}` for
every completion `G` and every `T`. -/
theorem formula_2_sub (x G : Matrix n n F) (hG : ∀ i j, i ≠ j → G i j = x i j) (T : Finset n) :
    closRank (subPattern x T) + (univ \ T).card =
      ⨅ d : {d : n → Option F // ∀ i ∉ T, d i = none}, (dialMat G d.1).rank := by
  rw [eq_add_diagonal_of_completion x G hG]
  set g := fun i => G i i - x i i
  haveI : Nonempty {d : n → Option F // ∀ i ∉ T, d i = none} := ⟨⟨fun _ => none, fun _ _ => rfl⟩⟩
  apply le_antisymm
  · exact le_ciInf fun d => closRank_sub_add_le_cost x g T d.1 d.2
  · set m := ⨅ d : {d : n → Option F // ∀ i ∉ T, d i = none},
      (dialMat (x + diagonal g) d.1).rank with hm
    have hge : (univ \ T).card ≤ m :=
      le_ciInf fun d => le_trans (Nat.le_add_left _ _) (closRank_sub_add_le_cost x g T d.1 d.2)
    have hq : m - (univ \ T).card ≤ closRank (subPattern x T) := by
      apply closRank_subPattern_ge x g T
      intro d hd
      have := ciInf_le (OrderBot.bddBelow (Set.range fun d : {d : n → Option F //
        ∀ i ∉ T, d i = none} => (dialMat (x + diagonal g) d.1).rank)) ⟨d, hd⟩
      rw [← hm] at this; simp only at this; omega
    have hfin : m ≤ closRank (subPattern x T) + (univ \ T).card := by omega
    exact hfin

/-- **`PivotOK G S` iff the block `G[S, S]` is invertible.** -/
theorem pivotOK_iff_isUnit_det (G : Matrix n n F) (S : Finset n) :
    PivotOK G S ↔ IsUnit (G.submatrix (fun a : S => (a : n)) (fun a : S => (a : n))).det := by
  set B := G.submatrix (fun a : S => (a : n)) (fun a : S => (a : n)) with hB
  have hBmul : ∀ (v : n → F), (∀ j ∉ S, v j = 0) → ∀ a : S,
      (B *ᵥ fun b : S => v b) a = (G *ᵥ v) a := by
    intro v hv a
    rw [mulVec_of_supp G S v hv]; rfl
  rw [isUnit_iff_ne_zero]
  constructor
  · intro hP h0
    obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have hsupp : ∀ j ∉ S, extZ S w j = 0 := fun j hj => extZ_apply_not_mem S w hj
    have hz := hP (extZ S w) hsupp (fun i hi => by
      have := hBmul (extZ S w) hsupp ⟨i, hi⟩
      rw [← this]
      have e : (fun b : S => extZ S w b) = w := funext fun b => extZ_apply_mem S w b.2
      rw [e, hw]; rfl)
    apply hw0; funext a
    have := congrFun hz a
    rwa [extZ_apply_mem S w a.2] at this
  · intro hdet v hv hGv
    have hw : B *ᵥ (fun b : S => v b) = 0 := by
      funext a; rw [hBmul v hv a]; exact hGv a a.2
    have hw0 : (fun b : S => v b) = 0 := by
      by_contra hne
      exact hdet ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨_, hne, hw⟩)
    funext i
    by_cases hi : i ∈ S
    · exact congrFun hw0 ⟨i, hi⟩
    · exact hv i hi

/-- **Lemma 1** with invertibility: the diagonal entries at `S` can be chosen so that the
completed block on `S × S` is invertible. -/
theorem lemma_1_invertible (x : Matrix n n F) (S : Finset n) :
    ∃ e : n → F, IsUnit ((x + diagonal e).submatrix (fun a : S => (a : n))
      (fun a : S => (a : n))).det := by
  obtain ⟨e, he⟩ := exists_pivotOK x S
  exact ⟨e, (pivotOK_iff_isUnit_det _ S).1 he⟩

/-- **Lemma 2** with invertibility. For `G[D, D]` invertible, `G' = pivot G D` satisfies
(i) `cost(G', d') = cost(G, d)`, (ii) `rank G'[E ∖ A, A] = rank G[E ∖ A, A]`, and
(iii) `G'[D, D]` is invertible; `d ↦ d'` (`pivDial D`) is an involution. -/
theorem lemma_2_invertible (G : Matrix n n F) (D : Finset n)
    (hD : IsUnit (G.submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).det) :
    (∀ d : n → Option F, pivDial D (pivDial D d) = d) ∧
    (∀ d : n → Option F, (dialMat (pivot G D) (pivDial D d)).rank = (dialMat G d).rank) ∧
    (∀ A : Finset n,
      ((pivot G D).submatrix (fun b : ↥(Aᶜ) => (b : n)) (fun a : A => (a : n))).rank =
        (G.submatrix (fun b : ↥(Aᶜ) => (b : n)) (fun a : A => (a : n))).rank) ∧
    IsUnit ((pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).det := by
  have hP : PivotOK G D := (pivotOK_iff_isUnit_det G D).2 hD
  refine ⟨fun d => pivDial_pivDial d, fun d => rank_dialMat_pivot hP d,
    fun A => rank_cut_pivot hP A Aᶜ rfl, ?_⟩
  set B' := (pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n))
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have hrank : B'.rank = D.card := rank_pivot_block hP
  have hk := rank_add_finrank_ker B'
  have hpos : 0 < finrank F (LinearMap.ker B'.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨w, LinearMap.mem_ker.2 (by rw [mulVecLin_apply]; exact hw)⟩,
        fun h => hw0 (congrArg Subtype.val h)⟩
  have hc : Fintype.card D = D.card := Fintype.card_coe D
  omega

/-- The flip `d ↦ d'` on one coordinate: `∞ ↦ 0`, `0 ↦ ∞`, `t ↦ 1/t` (`t ≠ 0`). -/
theorem flip_values (t : F) (ht : t ≠ 0) :
    flip (none : Option F) = some 0 ∧ flip (some (0 : F)) = none ∧ flip (some t) = some t⁻¹ := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [flip, ht]

/-- **Theorem 1, addendum**: some `T` with `|T| ≤ 2 ρ(x)` has `ρ(x_T) = ρ(x)`. -/
theorem theorem_1_two_rho (x : Matrix n n F) :
    ∃ T : Finset n, T.card ≤ 2 * closRank x ∧ closRank (subPattern x T) = closRank x := by
  obtain ⟨T, hT, hTr⟩ := closure_witness x (closRank x) (fun A => cutRank_le_closRank x A)
  exact ⟨T, by omega, hTr⟩

/-- **Formula (1)** in the paper's form: `cost(G, d) = |N(d)| + rank G_d` with
`G_d = (G - diag(d))[S(d), S(d)]`, `S(d) = E ∖ N(d)`, for any matrix `G`. -/
theorem formula_1 (G : Matrix n n F) (d : n → Option F) (N : Finset n)
    (hN : ∀ i, d i = none ↔ i ∈ N) :
    (dialMat G d).rank = N.card +
      ((G - diagonal (fun i => (d i).getD 0)).submatrix (fun a : ↥(Nᶜ) => (a : n))
        (fun a : ↥(Nᶜ) => (a : n))).rank := by
  have h := rank_dialMat_eq G 0 d N hN
  have e : G + diagonal (0 : n → F) = G := by simp
  rw [e] at h
  rw [h]
  congr 2
  ext a b
  by_cases hab : a = b
  · subst hab; simp [subPattern, sub_eq_add_neg]
  · have : (a : n) ≠ b := fun h => hab (Subtype.ext h)
    simp [subPattern, diagonal_apply_ne _ hab, diagonal_apply_ne _ this]

end FreeDiagonal
