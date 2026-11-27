import FreeDiagonal.Graphs.Complementation

/-!
# Task C3: the even-`k` Remark of the note (`m` copies of `K₃,₃`)

`mK33 m` is the disjoint union of `m` copies of `K₃,₃`, on vertices `(a, c)` with `a : Fin 6`
(`a < 3` one side, `a ≥ 3` the other) and `c : Fin m` the component. For `m ≥ 1`:

* `mrF2_mK33`: `mr(F₂, mK₃,₃) = 2m`;
* `optimum_zero_diag`: every completion of rank `2m` has zero diagonal;
* `c2_mK33`: `c₂(mK₃,₃) = 2m + 1`;
* `c2_proper_induce_mK33`: every proper induced subgraph has `c₂ ≤ 2m`.

So for `k = 2m`, `m ≥ 2`, `mK₃,₃` is a minimal forbidden induced subgraph for `c₂ ≤ k` with
`3k > 2k + 2` vertices (`even_k_remark`). The finite facts about `K₃,₃` (a non-zero diagonal
entry forces rank ≥ 3; `K₃,₃` minus a vertex has a rank-2 completion with a non-zero diagonal
entry) are checked by `decide` on explicit tables.
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal.EvenK

/-- The adjacency matrix of `K₃,₃` over `F₂` (as a function, so that `decide` can evaluate it). -/
def A33 (a b : Fin 6) : ZMod 2 := if (a.val < 3 ↔ ¬ b.val < 3) then 1 else 0

/-- `m` disjoint copies of `K₃,₃`. -/
def mK33 (m : ℕ) : SimpleGraph (Fin 6 × Fin m) where
  Adj p q := p.2 = q.2 ∧ (p.1.val < 3 ↔ ¬ q.1.val < 3)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => by tauto⟩

instance (m : ℕ) : DecidableRel (mK33 m).Adj :=
  fun p q => inferInstanceAs (Decidable (p.2 = q.2 ∧ (p.1.val < 3 ↔ ¬ q.1.val < 3)))

variable {m : ℕ}


lemma adj_apply (p q : Fin 6 × Fin m) :
    (mK33 m).adjMatrix (ZMod 2) p q = if p.2 = q.2 then A33 p.1 q.1 else 0 := by
  rw [adjMatrix_apply]
  by_cases h : p.2 = q.2 <;> simp [mK33, A33, h]

lemma A33_symm (a b : Fin 6) : A33 b a = A33 a b := by revert a b; decide

lemma card_mK33 : Fintype.card (Fin 6 × Fin m) = 6 * m := by simp

/-! ### Rank of the adjacency matrix -/

lemma rank_sum_le {F : Type*} [Field F] {ι n k : Type*} [Fintype n] [Fintype k]
    (s : Finset ι) (f : ι → Matrix n k F) : (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (rank_add_le_add _ _).trans (by omega)

/-- Indicator of one side of component `c`. -/
def Lv (c : Fin m) : Fin 6 × Fin m → ZMod 2 := fun p => if p.2 = c ∧ p.1.val < 3 then 1 else 0
def Rv (c : Fin m) : Fin 6 × Fin m → ZMod 2 := fun p => if p.2 = c ∧ ¬ p.1.val < 3 then 1 else 0

/-- The adjacency matrix of component `c`, as a rank-2 symmetric matrix. -/
def blk (c : Fin m) : Matrix (Fin 6 × Fin m) (Fin 6 × Fin m) (ZMod 2) :=
  vecMulVec (Lv c) (Rv c) + vecMulVec (Rv c) (Lv c)

lemma blk_apply (c : Fin m) (p q : Fin 6 × Fin m) :
    blk c p q = if p.2 = c ∧ q.2 = c then A33 p.1 q.1 else 0 := by
  by_cases h1 : p.2 = c <;> by_cases h2 : q.2 = c <;> by_cases h3 : p.1.val < 3 <;>
    by_cases h4 : q.1.val < 3 <;>
    simp [blk, Lv, Rv, vecMulVec_apply, A33, h1, h2, h3, h4]

lemma rank_blk (c : Fin m) : (blk c).rank ≤ 2 :=
  (rank_add_le_add _ _).trans (by
    have := rank_vecMulVec_le (Lv c) (Rv c)
    have := rank_vecMulVec_le (Rv c) (Lv c)
    omega)

lemma adj_eq_sum : (mK33 m).adjMatrix (ZMod 2) = ∑ c, blk c := by
  ext p q
  rw [Matrix.sum_apply, adj_apply]
  simp_rw [blk_apply]
  rw [Finset.sum_eq_single p.2 (fun c _ hc => by simp [Ne.symm hc]) (fun h => absurd (mem_univ _) h)]
  by_cases h : p.2 = q.2
  · simp [h]
  · simp [h, Ne.symm h]

lemma rank_adj_le : ((mK33 m).adjMatrix (ZMod 2)).rank ≤ 2 * m := by
  rw [adj_eq_sum]
  calc _ ≤ ∑ c, (blk c).rank := rank_sum_le _ _
    _ ≤ ∑ _c : Fin m, 2 := Finset.sum_le_sum fun c _ => rank_blk c
    _ = 2 * m := by simp [mul_comm]

/-! ### Lower bound: a `2m × 2m` identity off the diagonal -/

def rowI : Fin 2 × Fin m → Fin 6 × Fin m := fun x => (![0, 3] x.1, x.2)
def colI : Fin 2 × Fin m → Fin 6 × Fin m := fun x => (![4, 1] x.1, x.2)

lemma rowI_ne_colI (a b : Fin 2 × Fin m) : rowI a ≠ colI b := by
  intro h
  have := congrArg Prod.fst h
  obtain ⟨e, c⟩ := a; obtain ⟨e', c'⟩ := b
  fin_cases e <;> fin_cases e' <;> simp [rowI, colI] at this

lemma submatrix_rowI_colI :
    ((mK33 m).adjMatrix (ZMod 2)).submatrix rowI colI = 1 := by
  ext ⟨e, c⟩ ⟨e', c'⟩
  rw [submatrix_apply, adj_apply, Matrix.one_apply]
  by_cases hc : c = c'
  · subst hc; fin_cases e <;> fin_cases e' <;> simp [rowI, colI, A33]
  · simp [rowI, colI, hc]

lemma two_mul_le_minCompRank : 2 * m ≤ minCompRank ((mK33 m).adjMatrix (ZMod 2)) := by
  have h := offDiag_rank_le_minCompRank ((mK33 m).adjMatrix (ZMod 2)) rowI colI rowI_ne_colI
  rw [submatrix_rowI_colI, Matrix.rank_one] at h
  simpa using h

/-- **`mr(F₂, mK₃,₃) = 2m`.** -/
theorem mrF2_mK33 : mrF2 (mK33 m) = 2 * m := by
  rw [mrF2_eq]
  apply le_antisymm _ two_mul_le_minCompRank
  calc minCompRank ((mK33 m).adjMatrix (ZMod 2))
      ≤ ((mK33 m).adjMatrix (ZMod 2) + diagonal 0).rank := minCompRank_le _ 0
    _ ≤ 2 * m := by simpa using rank_adj_le

/-! ### A non-zero diagonal entry forces rank `≥ 2m + 1` -/

/-- For each vertex `a0` of `K₃,₃`: rows and columns of a `3 × 3` submatrix through `(a0, a0)`
that avoids every other diagonal entry and is non-singular once that entry is `1`. -/
def ra : Fin 6 → Fin 3 → Fin 6 :=
  ![![0, 1, 3], ![1, 0, 3], ![2, 0, 3], ![3, 0, 4], ![4, 0, 3], ![5, 0, 3]]
def ca : Fin 6 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![1, 2, 4], ![2, 1, 4], ![3, 1, 5], ![4, 1, 5], ![5, 1, 4]]

def K3 (a0 : Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun t t' => A33 (ra a0 t) (ca a0 t') + if t = 0 ∧ t' = 0 then 1 else 0

lemma ra_zero (a0 : Fin 6) : ra a0 0 = a0 := by revert a0; decide
lemma ca_zero (a0 : Fin 6) : ca a0 0 = a0 := by revert a0; decide
lemma ra_ca (a0 : Fin 6) (t t' : Fin 3) : ra a0 t = ca a0 t' → t = 0 ∧ t' = 0 := by
  revert a0 t t'; decide

lemma det_K3 (a0 : Fin 6) : (K3 a0).det = 1 := by
  rw [Matrix.det_fin_three]
  simp only [K3, Matrix.of_apply]
  revert a0; decide

/-- Index set of the big submatrix: a `2 × 2` identity in every other component, and the
`3 × 3` block in component `c0`. -/
abbrev BigIdx (c0 : Fin m) := (Fin 2 × {c : Fin m // c ≠ c0}) ⊕ Fin 3

def bigRow (a0 : Fin 6) (c0 : Fin m) : BigIdx c0 → Fin 6 × Fin m :=
  Sum.elim (fun x => (![0, 3] x.1, x.2.1)) (fun t => (ra a0 t, c0))
def bigCol (a0 : Fin 6) (c0 : Fin m) : BigIdx c0 → Fin 6 × Fin m :=
  Sum.elim (fun x => (![4, 1] x.1, x.2.1)) (fun t => (ca a0 t, c0))

lemma big_submatrix (d : Fin 6 × Fin m → ZMod 2) (a0 : Fin 6) (c0 : Fin m)
    (hd : d (a0, c0) = 1) :
    ((mK33 m).adjMatrix (ZMod 2) + diagonal d).submatrix (bigRow a0 c0) (bigCol a0 c0) =
      fromBlocks 1 0 0 (K3 a0) := by
  ext (⟨e, c, hc⟩ | t) (⟨e', c', hc'⟩ | t')
  · have hne : ((![0, 3] e : Fin 6), c) ≠ (![4, 1] e', c') := by
      intro h; have := congrArg Prod.fst h
      fin_cases e <;> fin_cases e' <;> simp at this
    simp only [submatrix_apply, bigRow, bigCol, Sum.elim_inl, Matrix.add_apply,
      diagonal_apply_ne _ hne, add_zero, adj_apply, fromBlocks_apply₁₁, one_apply]
    by_cases hcc : c = c'
    · subst hcc; fin_cases e <;> fin_cases e' <;> simp [A33]
    · have : ¬ ((e, (⟨c, hc⟩ : {c : Fin m // c ≠ c0})) = (e', ⟨c', hc'⟩)) := by
        intro h; exact hcc (congrArg (fun z => z.2.1) h)
      simp [hcc, this]
  · have hne : ((![0, 3] e : Fin 6), c) ≠ (ca a0 t', c0) := fun h => hc (congrArg Prod.snd h)
    simp [bigRow, bigCol, diagonal_apply_ne _ hne, adjMatrix_apply, mK33, hc]
  · have hne : (ra a0 t, c0) ≠ ((![4, 1] e' : Fin 6), c') :=
      fun h => hc' (congrArg Prod.snd h).symm
    simp [bigRow, bigCol, diagonal_apply_ne _ hne, adjMatrix_apply, mK33, Ne.symm hc']
  · simp only [submatrix_apply, bigRow, bigCol, Sum.elim_inr, Matrix.add_apply, adj_apply,
      if_true, fromBlocks_apply₂₂, K3, Matrix.of_apply]
    congr 1
    by_cases h0 : t = 0 ∧ t' = 0
    · obtain ⟨rfl, rfl⟩ := h0
      have e1 : (ra a0 0, c0) = (ca a0 0, c0) := by rw [ra_zero, ca_zero]
      rw [e1, diagonal_apply_eq, ca_zero, hd]; simp
    · have hne : (ra a0 t, c0) ≠ (ca a0 t', c0) :=
        fun h => h0 (ra_ca a0 t t' (congrArg Prod.fst h))
      rw [diagonal_apply_ne _ hne, if_neg h0]

lemma card_bigIdx (c0 : Fin m) : Fintype.card (BigIdx c0) = 2 * m + 1 := by
  have h1 : Fintype.card {c : Fin m // c ≠ c0} = m - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact c0.elim0)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, h1]
  omega

/-- **Every completion of rank `2m` has zero diagonal**: a non-zero diagonal entry forces rank at
least `2m + 1`. -/
theorem rank_ge_of_diag_ne_zero (d : Fin 6 × Fin m → ZMod 2) (p : Fin 6 × Fin m)
    (hp : d p ≠ 0) : 2 * m + 1 ≤ ((mK33 m).adjMatrix (ZMod 2) + diagonal d).rank := by
  obtain ⟨a0, c0⟩ := p
  have hd : d (a0, c0) = 1 := zmod2_eq_one_of_ne_zero hp
  have hdet : (((mK33 m).adjMatrix (ZMod 2) + diagonal d).submatrix (bigRow a0 c0)
      (bigCol a0 c0)).det ≠ 0 := by
    rw [big_submatrix d a0 c0 hd, det_fromBlocks_zero₂₁, det_one, det_K3]; decide
  have h := rank_of_det_ne_zero hdet
  rw [card_bigIdx] at h
  rw [← h]
  exact rank_submatrix_le _ _ _

theorem optimum_zero_diag (d : Fin 6 × Fin m → ZMod 2)
    (hd : ((mK33 m).adjMatrix (ZMod 2) + diagonal d).rank = mrF2 (mK33 m)) : d = 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, d p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  have := rank_ge_of_diag_ne_zero d p hp
  rw [hd, mrF2_mK33] at this
  omega

/-- **`c₂(mK₃,₃) = 2m + 1`** for `m ≥ 1`. -/
theorem c2_mK33 (hm : 1 ≤ m) : c2 (mK33 m) = 2 * m + 1 := by
  have hpos : 0 < mrF2 (mK33 m) := by rw [mrF2_mK33]; omega
  have := (c2_eq_mrF2_add_one_iff (mK33 m) hpos).2 (fun d hd => optimum_zero_diag d hd)
  rw [this, mrF2_mK33]

/-! ### Deleting a vertex: a completion of rank `2m` with a non-zero diagonal entry -/

/-- For `K₃,₃` minus `a0`: `x xᵀ + y yᵀ` agrees with `K₃,₃` off the diagonal away from `a0`,
and has diagonal entry `1` at `a1 a0`. -/
def xT : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 1, 0, 1, 1, 1], ![1, 0, 0, 1, 1, 1], ![1, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 1, 0],
    ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 0, 0]]
def yT : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1], ![1, 1, 1, 0, 1, 0]]
def a1T : Fin 6 → Fin 6 := ![1, 0, 0, 4, 3, 3]

lemma xy_fit (a0 i j : Fin 6) (hij : i ≠ j) (hi : i ≠ a0) (hj : j ≠ a0) :
    xT a0 i * xT a0 j + yT a0 i * yT a0 j = A33 i j := by
  revert a0 i j; decide

lemma xy_diag (a0 : Fin 6) :
    xT a0 (a1T a0) * xT a0 (a1T a0) + yT a0 (a1T a0) * yT a0 (a1T a0) = 1 := by
  revert a0; decide

lemma a1T_ne (a0 : Fin 6) : a1T a0 ≠ a0 := by revert a0; decide

def Xv (a0 : Fin 6) (c0 : Fin m) : Fin 6 × Fin m → ZMod 2 :=
  fun p => if p.2 = c0 then xT a0 p.1 else 0
def Yv (a0 : Fin 6) (c0 : Fin m) : Fin 6 × Fin m → ZMod 2 :=
  fun p => if p.2 = c0 then yT a0 p.1 else 0

/-- The completion of `mK₃,₃ − (a0, c0)`, extended to all vertices. -/
def Mp (a0 : Fin 6) (c0 : Fin m) : Matrix (Fin 6 × Fin m) (Fin 6 × Fin m) (ZMod 2) :=
  ∑ c ∈ univ.erase c0, blk c + vecMulVec (Xv a0 c0) (Xv a0 c0) + vecMulVec (Yv a0 c0) (Yv a0 c0)

lemma Mp_apply (a0 : Fin 6) (c0 : Fin m) (u v : Fin 6 × Fin m) :
    Mp a0 c0 u v = (if u.2 = v.2 ∧ u.2 ≠ c0 then A33 u.1 v.1 else 0) +
      (if u.2 = c0 ∧ v.2 = c0 then xT a0 u.1 * xT a0 v.1 + yT a0 u.1 * yT a0 v.1 else 0) := by
  simp only [Mp, Matrix.add_apply, Matrix.sum_apply, blk_apply, vecMulVec_apply, Xv, Yv]
  have hs : (∑ c ∈ univ.erase c0, if u.2 = c ∧ v.2 = c then A33 u.1 v.1 else 0) =
      if u.2 = v.2 ∧ u.2 ≠ c0 then A33 u.1 v.1 else 0 := by
    by_cases h : u.2 = v.2 ∧ u.2 ≠ c0
    · rw [if_pos h, Finset.sum_eq_single_of_mem u.2 (mem_erase.2 ⟨h.2, mem_univ _⟩)]
      · simp [h.1]
      · intro c _ hc; simp [Ne.symm hc]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro c hc
      have hc0 := (mem_erase.1 hc).1
      by_cases h1 : u.2 = c
      · by_cases h2 : v.2 = c
        · exact absurd ⟨h1.trans h2.symm, h1 ▸ hc0⟩ h
        · simp [h2]
      · simp [h1]
  rw [hs, add_assoc]
  congr 1
  by_cases h1 : u.2 = c0 <;> by_cases h2 : v.2 = c0 <;> simp [h1, h2]

lemma rank_Mp (a0 : Fin 6) (c0 : Fin m) : (Mp a0 c0).rank ≤ 2 * m := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact c0.elim0)
  have h1 : (∑ c ∈ univ.erase c0, blk c).rank ≤ 2 * (m - 1) :=
    calc _ ≤ ∑ c ∈ univ.erase c0, (blk c).rank := rank_sum_le _ _
      _ ≤ ∑ _c ∈ univ.erase c0, 2 := Finset.sum_le_sum fun c _ => rank_blk c
      _ = 2 * (m - 1) := by simp [card_erase_of_mem, mul_comm]
  have h2 := rank_vecMulVec_le (Xv a0 c0) (Xv a0 c0)
  have h3 := rank_vecMulVec_le (Yv a0 c0) (Yv a0 c0)
  calc (Mp a0 c0).rank ≤ (∑ c ∈ univ.erase c0, blk c + vecMulVec (Xv a0 c0) (Xv a0 c0)).rank +
        (vecMulVec (Yv a0 c0) (Yv a0 c0)).rank := rank_add_le_add _ _
    _ ≤ (∑ c ∈ univ.erase c0, blk c).rank + (vecMulVec (Xv a0 c0) (Xv a0 c0)).rank +
        (vecMulVec (Yv a0 c0) (Yv a0 c0)).rank := by gcongr; exact rank_add_le_add _ _
    _ ≤ 2 * m := by omega

lemma Mp_symm (a0 : Fin 6) (c0 : Fin m) : (Mp a0 c0).IsSymm := by
  ext u v
  rw [transpose_apply, Mp_apply, Mp_apply, A33_symm u.1 v.1]
  have c1 : (v.2 = u.2 ∧ v.2 ≠ c0) ↔ (u.2 = v.2 ∧ u.2 ≠ c0) :=
    ⟨fun h => ⟨h.1.symm, h.1 ▸ h.2⟩, fun h => ⟨h.1.symm, h.1 ▸ h.2⟩⟩
  have c2 : (v.2 = c0 ∧ u.2 = c0) ↔ (u.2 = c0 ∧ v.2 = c0) := And.comm
  have e1 : (if v.2 = u.2 ∧ v.2 ≠ c0 then A33 u.1 v.1 else 0) =
      (if u.2 = v.2 ∧ u.2 ≠ c0 then A33 u.1 v.1 else 0) := by
    by_cases h : u.2 = v.2 ∧ u.2 ≠ c0
    · rw [if_pos (c1.2 h), if_pos h]
    · rw [if_neg (fun h' => h (c1.1 h')), if_neg h]
  have e2 : (if v.2 = c0 ∧ u.2 = c0 then xT a0 v.1 * xT a0 u.1 + yT a0 v.1 * yT a0 u.1 else 0) =
      (if u.2 = c0 ∧ v.2 = c0 then xT a0 u.1 * xT a0 v.1 + yT a0 u.1 * yT a0 v.1 else 0) := by
    by_cases h : u.2 = c0 ∧ v.2 = c0
    · rw [if_pos (c2.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (c2.1 h')), if_neg h]
  rw [e1, e2]

/-- Deleting one vertex leaves a graph with `c₂ ≤ 2m`. -/
theorem c2_erase_le (p : Fin 6 × Fin m) :
    c2 ((mK33 m).induce ((univ.erase p : Finset _) : Set (Fin 6 × Fin m))) ≤ 2 * m := by
  classical
  obtain ⟨a0, c0⟩ := p
  set s : Finset (Fin 6 × Fin m) := univ.erase (a0, c0)
  set Ms : Matrix ↥(s : Set (Fin 6 × Fin m)) ↥(s : Set (Fin 6 × Fin m)) (ZMod 2) :=
    (Mp a0 c0).submatrix Subtype.val Subtype.val
  have hsymm : Ms.IsSymm := by
    ext u v; have := congrFun (congrFun (Mp_symm a0 c0) u.1) v.1
    simpa [Ms, transpose_apply] using this
  have hq : ((a1T a0, c0) : Fin 6 × Fin m) ∈ (s : Set (Fin 6 × Fin m)) := by
    simp [s, a1T_ne a0]
  have hdiag : ∃ i, Ms i i ≠ 0 := by
    refine ⟨⟨_, hq⟩, ?_⟩
    simp only [Ms, submatrix_apply, Mp_apply]
    rw [xy_diag]; simp
  obtain ⟨s', hs', B, hB⟩ := lempel_diag Ms hsymm hdiag
  have hfit : IsSqFit ((mK33 m).induce (s : Set (Fin 6 × Fin m))) B := by
    intro u v huv
    rw [← hB, adjMatrix_apply]
    have hadj : ((mK33 m).induce (s : Set (Fin 6 × Fin m))).Adj u v ↔ (mK33 m).Adj u.1 v.1 := by
      simp [comap_adj]
    have e2 : (if ((mK33 m).induce (s : Set (Fin 6 × Fin m))).Adj u v then (1 : ZMod 2) else 0) =
        (mK33 m).adjMatrix (ZMod 2) u.1 v.1 := by
      rw [adjMatrix_apply]; simp only [hadj]
    rw [e2, adj_apply]
    simp only [Ms, submatrix_apply, Mp_apply]
    have hu : u.1 ≠ (a0, c0) := by have := u.2; simpa [s] using this
    have hv : v.1 ≠ (a0, c0) := by have := v.2; simpa [s] using this
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    by_cases h1 : u.1.2 = v.1.2
    · by_cases h2 : u.1.2 = c0
      · have h3 : v.1.2 = c0 := h1 ▸ h2
        have hi : u.1.1 ≠ a0 := fun h => hu (Prod.ext h h2)
        have hj : v.1.1 ≠ a0 := fun h => hv (Prod.ext h h3)
        have hij : u.1.1 ≠ v.1.1 := fun h => huv' (Prod.ext h h1)
        simp [h1, h2, h3, xy_fit a0 _ _ hij hi hj]
      · rw [if_pos ⟨h1, h2⟩, if_neg (fun h => h2 h.1), if_pos h1, add_zero]
    · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 (h.1.trans h.2.symm)), if_neg h1]
      simp
  calc _ ≤ s' := c2_le_of_sqFit _ B hfit
    _ ≤ Ms.rank := hs'
    _ ≤ (Mp a0 c0).rank := rank_submatrix_le _ _ _
    _ ≤ 2 * m := rank_Mp a0 c0

/-- **Every proper induced subgraph of `mK₃,₃` has `c₂ ≤ 2m`.** -/
theorem c2_proper_induce_mK33 (s : Finset (Fin 6 × Fin m)) (hs : s ≠ univ) :
    c2 ((mK33 m).induce (s : Set (Fin 6 × Fin m))) ≤ 2 * m := by
  obtain ⟨p, hp⟩ : ∃ p, p ∉ s := by
    by_contra h; push_neg at h; exact hs (eq_univ_iff_forall.2 h)
  have hsub : s ⊆ univ.erase p := fun x hx => mem_erase.2 ⟨fun h => hp (h ▸ hx), mem_univ _⟩
  exact (c2_induce_mono _ hsub).trans (c2_erase_le p)

/-- **The even-`k` Remark of the note.** For `m ≥ 2` and `k = 2m`, the disjoint union of `m`
copies of `K₃,₃` has `3k > 2k + 2` vertices, `c₂ = k + 1` (and `mr = k`), and every proper
induced subgraph has `c₂ ≤ k`. So it is a minimal forbidden induced subgraph for `c₂ ≤ k` with
more than `2k + 2` vertices: the BPR bound `2k + 2` fails for every even `k ≥ 4`. -/
theorem even_k_remark (hm : 2 ≤ m) :
    Fintype.card (Fin 6 × Fin m) = 3 * (2 * m) ∧ 2 * (2 * m) + 2 < 3 * (2 * m) ∧
      c2 (mK33 m) = 2 * m + 1 ∧ mrF2 (mK33 m) = 2 * m ∧
      (∀ s : Finset (Fin 6 × Fin m), s ≠ univ →
        c2 ((mK33 m).induce (s : Set (Fin 6 × Fin m))) ≤ 2 * m) := by
  refine ⟨by rw [card_mK33]; ring, by omega, c2_mK33 (by omega), mrF2_mK33,
    c2_proper_induce_mK33⟩

end FreeDiagonal.EvenK
