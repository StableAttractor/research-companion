import FreeDiagonal.Closure.Dial

/-!
# The principal pivot on a set of indices

Let `G` be a matrix and `D` a set of indices on which `G` is non-singular (`PivotOK G D`: no
non-zero `v` supported on `D` has `(Gv)_D = 0`). With `K v = (Gv on D, v off D)` and
`Ψ v = (v on D, Gv off D)`, put `pivot G D = Ψ K⁻¹`. For `u = K v` the pairs
`(uᵢ, (G' u)ᵢ)` are the pairs `(vᵢ, (Gv)ᵢ)`, swapped on `D`. Hence:

* `rank_dialMat_pivot`: dial-matrix ranks carry over, with dial values on `D` transformed by
  `flip` (`none ↦ 0`, `0 ↦ none`, `t ↦ t⁻¹`);
* `rank_cut_pivot`: cut ranks carry over;
* `rank_pivot_block`: the block of the pivot on `D × D` is non-singular.

`exists_pivotOK`: over ANY field, every pattern has a completion that is non-singular on a
given set `S` (one diagonal entry at a time).
-/

open Matrix Finset Module Submodule

namespace FreeDiagonal

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- `G` is non-singular on `D`. -/
def PivotOK (G : Matrix n n F) (D : Finset n) : Prop :=
  ∀ v : n → F, (∀ i ∉ D, v i = 0) → (∀ i ∈ D, (G *ᵥ v) i = 0) → v = 0

/-! ### Every pattern has a completion non-singular on `S` (any field) -/

lemma mulVec_update_diag (x : Matrix n n F) (e : n → F) (a : n) (τ : F) (v : n → F) {i : n}
    (hi : i ≠ a) :
    ((x + diagonal (Function.update e a τ)) *ᵥ v) i = ((x + diagonal e) *ᵥ v) i := by
  simp [add_mulVec, mulVec_diagonal, Function.update_of_ne hi]

lemma mulVec_update_diag_self (x : Matrix n n F) (e : n → F) (a : n) (τ : F) (v : n → F) :
    ((x + diagonal (Function.update e a τ)) *ᵥ v) a = (x *ᵥ v) a + τ * v a := by
  simp [add_mulVec, mulVec_diagonal]

theorem exists_pivotOK (x : Matrix n n F) (S : Finset n) :
    ∃ e : n → F, PivotOK (x + diagonal e) S := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, fun v hv _ => funext fun i => hv i (by simp)⟩
  | insert a S ha ih =>
    obtain ⟨e, he⟩ := ih
    -- a bad vector for the value `τ` at `a` has `v a ≠ 0`
    have key : ∀ τ : F, ¬ PivotOK (x + diagonal (Function.update e a τ)) (insert a S) →
        ∃ v : n → F, (∀ i ∉ insert a S, v i = 0) ∧
          (∀ i ∈ S, ((x + diagonal e) *ᵥ v) i = 0) ∧ (x *ᵥ v) a + τ * v a = 0 ∧ v a ≠ 0 := by
      intro τ hbad
      simp only [PivotOK, not_forall] at hbad
      obtain ⟨v, hsupp, heq, hne⟩ := hbad
      have hS : ∀ i ∈ S, ((x + diagonal e) *ᵥ v) i = 0 := fun i hi => by
        rw [← mulVec_update_diag x e a τ v (fun h => ha (h ▸ hi))]
        exact heq i (mem_insert_of_mem hi)
      have ha' : (x *ᵥ v) a + τ * v a = 0 := by
        rw [← mulVec_update_diag_self]; exact heq a (mem_insert_self a S)
      refine ⟨v, hsupp, hS, ha', fun h0 => hne ?_⟩
      apply he v _ hS
      intro i hi
      by_cases hia : i = a
      · subst hia; exact h0
      · exact hsupp i (by simp [hia, hi])
    by_cases h0 : PivotOK (x + diagonal (Function.update e a 0)) (insert a S)
    · exact ⟨_, h0⟩
    by_cases h1 : PivotOK (x + diagonal (Function.update e a 1)) (insert a S)
    · exact ⟨_, h1⟩
    exfalso
    obtain ⟨v0, s0, e0, r0, n0⟩ := key 0 h0
    obtain ⟨v1, s1, e1, r1, n1⟩ := key 1 h1
    set w := v1 a • v0 - v0 a • v1
    have hw : w = 0 := by
      apply he w
      · intro i hi
        by_cases hia : i = a
        · subst hia; simp [w, mul_comm]
        · have hi' : i ∉ insert a S := by simp [hia, hi]
          simp [w, s0 i hi', s1 i hi']
      · intro i hi
        simp only [w, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          e0 i hi, e1 i hi, mul_zero, sub_zero]
    have hx : (x *ᵥ w) a = 0 := by rw [hw, mulVec_zero]; rfl
    simp only [w, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx
    simp only [zero_mul, add_zero] at r0
    rw [r0, mul_zero, zero_sub, neg_eq_zero] at hx
    have : (x *ᵥ v1) a = 0 := (mul_eq_zero.1 hx).resolve_left n0
    rw [this, zero_add, one_mul] at r1
    exact n1 r1

/-! ### The pivot -/

/-- `K v = (Gv on D, v off D)`. -/
def pivK (G : Matrix n n F) (D : Finset n) : Matrix n n F :=
  Matrix.of fun i j => if i ∈ D then G i j else if i = j then 1 else 0

/-- `Ψ v = (v on D, Gv off D)`. -/
def pivPsi (G : Matrix n n F) (D : Finset n) : Matrix n n F :=
  Matrix.of fun i j => if i ∈ D then (if i = j then 1 else 0) else G i j

/-- The principal pivot transform of `G` on `D`. -/
noncomputable def pivot (G : Matrix n n F) (D : Finset n) : Matrix n n F :=
  pivPsi G D * (pivK G D)⁻¹

variable {G : Matrix n n F} {D : Finset n}

lemma pivK_mulVec (v : n → F) (i : n) :
    (pivK G D *ᵥ v) i = if i ∈ D then (G *ᵥ v) i else v i := by
  by_cases h : i ∈ D <;> simp [pivK, mulVec, dotProduct, h]

lemma pivPsi_mulVec (v : n → F) (i : n) :
    (pivPsi G D *ᵥ v) i = if i ∈ D then v i else (G *ᵥ v) i := by
  by_cases h : i ∈ D <;> simp [pivPsi, mulVec, dotProduct, h]

lemma pivK_isUnit_det (hG : PivotOK G D) : IsUnit (pivK G D).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro v w hvw
  have h0 : pivK G D *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  have := hG (v - w)
    (fun i hi => by have := congrFun h0 i; rwa [pivK_mulVec, if_neg hi] at this)
    (fun i hi => by have := congrFun h0 i; rwa [pivK_mulVec, if_pos hi] at this)
  exact sub_eq_zero.1 this

lemma pivot_mulVec_pivK (hG : PivotOK G D) (v : n → F) :
    pivot G D *ᵥ (pivK G D *ᵥ v) = pivPsi G D *ᵥ v := by
  rw [pivot, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ (pivK_isUnit_det hG),
    Matrix.mul_one]

lemma pivK_mulVec_inv (hG : PivotOK G D) (u : n → F) :
    pivK G D *ᵥ ((pivK G D)⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (pivK_isUnit_det hG), one_mulVec]

lemma pivK_inv_mulVec (hG : PivotOK G D) (v : n → F) :
    (pivK G D)⁻¹ *ᵥ (pivK G D *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul _ (pivK_isUnit_det hG), one_mulVec]

/-! ### Dial values under the pivot -/

open Classical in
/-- How a dial value on `D` transforms: `none ↦ 0`, `0 ↦ none`, `t ↦ t⁻¹`. -/
noncomputable def flip : Option F → Option F
  | none => some 0
  | some t => if t = 0 then none else some t⁻¹

lemma flip_flip (o : Option F) : flip (flip o) = o := by
  cases o with
  | none => simp [flip]
  | some t => by_cases h : t = 0 <;> simp [flip, h]

lemma dialCond_flip (o : Option F) (a b : F) : DialCond (flip o) b a ↔ DialCond o a b := by
  cases o with
  | none => simp [flip, DialCond]
  | some t =>
    by_cases h : t = 0
    · simp [flip, DialCond, h, eq_comm]
    · simp only [flip, h, if_false, DialCond]
      constructor
      · intro h1; rw [h1, ← mul_assoc, mul_inv_cancel₀ h, one_mul]
      · intro h1; rw [h1, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The dial setting transformed on `D`. -/
noncomputable def pivDial (D : Finset n) (d : n → Option F) : n → Option F :=
  fun i => if i ∈ D then flip (d i) else d i

lemma pivDial_pivDial (d : n → Option F) : pivDial D (pivDial D d) = d := by
  funext i; by_cases h : i ∈ D <;> simp [pivDial, h, flip_flip]

/-- The pair identity: dial conditions at `v` for `G` are those at `K v` for the pivot. -/
lemma dialCond_pivot (hG : PivotOK G D) (d : n → Option F) (v : n → F) :
    (∀ i, DialCond (d i) (v i) ((G *ᵥ v) i)) ↔
      ∀ i, DialCond (pivDial D d i) ((pivK G D *ᵥ v) i)
        ((pivot G D *ᵥ (pivK G D *ᵥ v)) i) := by
  rw [pivot_mulVec_pivK hG]
  apply forall_congr'
  intro i
  rw [pivK_mulVec, pivPsi_mulVec]
  by_cases h : i ∈ D
  · simp only [pivDial, h, if_true]; exact (dialCond_flip _ _ _).symm
  · simp only [pivDial, h, if_false]

/-- **Dial ranks carry over to the pivot.** -/
theorem rank_dialMat_pivot (hG : PivotOK G D) (d : n → Option F) :
    (dialMat (pivot G D) (pivDial D d)).rank = (dialMat G d).rank := by
  have hk : finrank F (LinearMap.ker (dialMat G d).mulVecLin) =
      finrank F (LinearMap.ker (dialMat (pivot G D) (pivDial D d)).mulVecLin) := by
    apply finrank_eq_of_inverse _ _ (pivK G D).mulVecLin (pivK G D)⁻¹.mulVecLin
    · intro v hv
      rw [mem_ker_dialMat] at hv ⊢
      exact (dialCond_pivot hG d v).1 hv
    · intro u hu
      rw [mem_ker_dialMat] at hu ⊢
      rw [Matrix.mulVecLin_apply]
      apply (dialCond_pivot hG d _).2
      rw [pivK_mulVec_inv hG]; exact hu
    · intro v _; simp [Matrix.mulVecLin_apply, pivK_inv_mulVec hG]
    · intro u _; simp [Matrix.mulVecLin_apply, pivK_mulVec_inv hG]
  have h1 := rank_add_finrank_ker (dialMat G d)
  have h2 := rank_add_finrank_ker (dialMat (pivot G D) (pivDial D d))
  omega

lemma dialMat_some_zero (H : Matrix n n F) : dialMat H (fun _ => some 0) = H := by
  ext i j; simp [dialMat]

/-! ### Cut ranks under the pivot -/

/-- `{v supported on A with (Gv) = 0 off A}`. -/
def cutSub (G : Matrix n n F) (A : Finset n) : Submodule F (n → F) where
  carrier := {v | ∀ i ∉ A, v i = 0 ∧ (G *ᵥ v) i = 0}
  zero_mem' := fun i _ => by simp
  add_mem' := fun {v w} hv hw i hi => by
    simp only [Set.mem_setOf_eq] at hv hw
    simp [mulVec_add, (hv i hi).1, (hv i hi).2, (hw i hi).1, (hw i hi).2]
  smul_mem' := fun c v hv i hi => by
    simp only [Set.mem_setOf_eq] at hv
    simp [mulVec_smul, (hv i hi).1, (hv i hi).2]

lemma mulVec_of_supp (G : Matrix n n F) (A : Finset n) (v : n → F) (hv : ∀ j ∉ A, v j = 0)
    (i : n) : (G *ᵥ v) i = ∑ a : ↥A, G i a * v a := by
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_add_sum_compl A, Finset.sum_coe_sort A (fun j => G i j * v j)]
  have : ∑ j ∈ Aᶜ, G i j * v j = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hv j (mem_compl.1 hj), mul_zero]
  rw [this, add_zero]

lemma finrank_cutSub (G : Matrix n n F) (A B : Finset n) (hB : B = Aᶜ) :
    finrank F (cutSub G A) = finrank F
      (LinearMap.ker (G.submatrix (fun b : B => (b : n)) (fun a : A => (a : n))).mulVecLin) := by
  subst hB
  apply finrank_eq_of_inverse _ _ (LinearMap.funLeft F F (fun a : ↥A => (a : n))) (extZ A)
  · intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    ext b
    have hbA : (b : n) ∉ A := mem_compl.1 b.2
    have h0 := (hv b hbA).2
    rw [mulVec_of_supp G A v (fun j hj => (hv j hj).1)] at h0
    simpa [mulVec, dotProduct] using h0
  · intro w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    intro i hi
    have hiB : i ∈ Aᶜ := mem_compl.2 hi
    refine ⟨extZ_apply_not_mem A w hi, ?_⟩
    rw [mulVec_of_supp G A _ (fun j hj => extZ_apply_not_mem A w hj)]
    have := congrFun hw ⟨i, hiB⟩
    simpa [mulVec, dotProduct, extZ_apply_mem] using this
  · intro v hv
    ext i
    by_cases hi : i ∈ A
    · rw [extZ_apply_mem A _ hi]; rfl
    · rw [extZ_apply_not_mem A _ hi, (hv i hi).1]
  · intro w _
    ext a
    exact extZ_apply_mem A w a.2

lemma finrank_cutSub_pivot (hG : PivotOK G D) (A : Finset n) :
    finrank F (cutSub (pivot G D) A) = finrank F (cutSub G A) := by
  symm
  apply finrank_eq_of_inverse _ _ (pivK G D).mulVecLin (pivK G D)⁻¹.mulVecLin
  · intro v hv i hi
    rw [Matrix.mulVecLin_apply, pivot_mulVec_pivK hG, pivK_mulVec, pivPsi_mulVec]
    by_cases h : i ∈ D <;> simp [h, (hv i hi).1, (hv i hi).2]
  · intro u hu i hi
    rw [Matrix.mulVecLin_apply]
    set v := (pivK G D)⁻¹ *ᵥ u
    have hKv : pivK G D *ᵥ v = u := pivK_mulVec_inv hG u
    have h1 := (hu i hi).1
    have h2 := (hu i hi).2
    rw [← hKv, pivK_mulVec] at h1
    rw [← hKv, pivot_mulVec_pivK hG, pivPsi_mulVec] at h2
    by_cases h : i ∈ D
    · rw [if_pos h] at h1 h2; exact ⟨h2, h1⟩
    · rw [if_neg h] at h1 h2; exact ⟨h1, h2⟩
  · intro v _; simp [Matrix.mulVecLin_apply, pivK_inv_mulVec hG]
  · intro u _; simp [Matrix.mulVecLin_apply, pivK_mulVec_inv hG]

/-- **Cut ranks carry over to the pivot.** -/
theorem rank_cut_pivot (hG : PivotOK G D) (A B : Finset n) (hB : B = Aᶜ) :
    ((pivot G D).submatrix (fun b : B => (b : n)) (fun a : A => (a : n))).rank =
      (G.submatrix (fun b : B => (b : n)) (fun a : A => (a : n))).rank := by
  have h1 := rank_add_finrank_ker
    ((pivot G D).submatrix (fun b : B => (b : n)) (fun a : A => (a : n)))
  have h2 := rank_add_finrank_ker (G.submatrix (fun b : B => (b : n)) (fun a : A => (a : n)))
  rw [← finrank_cutSub _ A B hB] at h1 h2
  rw [finrank_cutSub_pivot hG] at h1
  omega

/-- **The block of the pivot on `D × D` is non-singular.** -/
theorem rank_pivot_block (hG : PivotOK G D) :
    ((pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).rank = D.card := by
  have hker : finrank F (LinearMap.ker
      ((pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n))).mulVecLin) = 0 := by
    rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    rw [Submodule.mem_bot]
    set u := extZ D w
    have hu0 : ∀ i ∉ D, u i = 0 := fun i hi => extZ_apply_not_mem D w hi
    have hGu : ∀ i ∈ D, (pivot G D *ᵥ u) i = 0 := by
      intro i hi
      rw [mulVec_of_supp _ D u hu0]
      have := congrFun hw ⟨i, hi⟩
      simpa [mulVec, dotProduct, u, extZ_apply_mem] using this
    set v := (pivK G D)⁻¹ *ᵥ u
    have hKv : pivK G D *ᵥ v = u := pivK_mulVec_inv hG u
    have hv0 : v = 0 := by
      funext i
      by_cases hi : i ∈ D
      · have := hGu i hi
        rw [← hKv, pivot_mulVec_pivK hG, pivPsi_mulVec, if_pos hi] at this
        exact this
      · have := hu0 i hi
        rw [← hKv, pivK_mulVec, if_neg hi] at this
        exact this
    have hu : u = 0 := by rw [← hKv, hv0, mulVec_zero]
    funext a
    have h := congrFun hu a
    have e : u a = w a := extZ_apply_mem D w a.2
    rw [e] at h
    exact h
  have := rank_add_finrank_ker
    ((pivot G D).submatrix (fun a : D => (a : n)) (fun a : D => (a : n)))
  rw [hker, add_zero, Fintype.card_coe] at this
  exact this

/-- The rows and the columns of the pivot indexed by `D` are independent. -/
theorem frk_pivot_row (hG : PivotOK G D) : frk F (pivot G D).row D = D.card := by
  apply le_antisymm (frk_le_card (F := F) _ _)
  have h1 := rank_submatrix_rows_eq_frk (pivot G D) D
  have h2 := rank_submatrix_le ((pivot G D).submatrix (fun a : D => (a : n)) id)
    (id : D → D) (fun a : D => (a : n))
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at h2
  rw [rank_pivot_block hG] at h2
  omega

theorem frk_pivot_col (hG : PivotOK G D) : frk F (pivot G D).col D = D.card := by
  apply le_antisymm (frk_le_card (F := F) _ _)
  have h1 := rank_submatrix_cols_eq_frk (pivot G D) D
  have h2 := rank_submatrix_le ((pivot G D).submatrix id (fun a : D => (a : n)))
    (fun a : D => (a : n)) (id : D → D)
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at h2
  rw [rank_pivot_block hG] at h2
  omega

end FreeDiagonal
