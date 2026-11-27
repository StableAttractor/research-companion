import FreeDiagonal.EvenComplementation.Tripling

/-!
# Part 54-f, sharpness: the tripling of a perfect matching, and `m K₃,₃`

`pm m`: the perfect matching on `Fin m × Bool` (`(a, b) ~ (a, !b)`). Its adjacency matrix is the
permutation matrix of `(a, b) ↦ (a, !b)`, so it is non-singular over `F₂` (`det_pm_ne_zero`).
Its tripling therefore has `c₂ = 2m + 1` and every proper induced subgraph has `c₂ ≤ 2m`
(`tripling_pm_*`). `mK33_iso_tripling_pm`: `mK33 m` (Graphs/EvenK.lean) is isomorphic to
`tripling (pm m)`, so `even_k_remark` is the special case "perfect matching" of 54-f;
`c2_mK33_via_tripling` re-derives `c₂(mK₃,₃) = 2m + 1` through the isomorphism
(`c2_iso`: `c₂` is invariant under graph isomorphism).
-/

open Matrix Finset SimpleGraph

namespace FreeDiagonal.EvenComplementation

open FreeDiagonal

/-- The perfect matching `m K₂` on `Fin m × Bool`. -/
def pm (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (m : ℕ) : DecidableRel (pm m).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 = q.1 ∧ p.2 ≠ q.2))

/-- The involution `(a, b) ↦ (a, !b)`. -/
def pmPerm (m : ℕ) : Equiv.Perm (Fin m × Bool) := Equiv.prodCongr (Equiv.refl _) Equiv.boolNot

lemma adj_pm_eq (m : ℕ) : (pm m).adjMatrix (ZMod 2) = (pmPerm m).permMatrix (ZMod 2) := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  rw [adjMatrix_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, pm, pmPerm, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id, Prod.mk.injEq, Equiv.boolNot_apply]
  by_cases h : a = a'
  · subst h; cases b <;> cases b' <;> simp
  · simp [h]

theorem det_pm_ne_zero (m : ℕ) : ((pm m).adjMatrix (ZMod 2)).det ≠ 0 := by
  rw [adj_pm_eq, det_permutation]
  exact (Units.isUnit _).map (Int.castRingHom (ZMod 2)) |>.ne_zero

lemma card_pm (m : ℕ) : Fintype.card (Fin m × Bool) = 2 * m := by simp [mul_comm]

/-- The tripling of `m K₂` (`m ≥ 1`) is a minimal forbidden induced subgraph for `c₂ ≤ 2m` on
`6m = 3 (2m)` vertices. -/
theorem tripling_pm (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card ((Fin m × Bool) × Fin 3) = 3 * (2 * m) ∧
      c2 (tripling (pm m)) = 2 * m + 1 ∧
      ∀ s : Finset ((Fin m × Bool) × Fin 3), s ≠ univ →
        c2 ((tripling (pm m)).induce (s : Set ((Fin m × Bool) × Fin 3))) ≤ 2 * m := by
  refine ⟨by rw [card_tripling, card_pm], ?_, ?_⟩
  · rw [c2_tripling (det_pm_ne_zero m) (by rw [card_pm]; omega), card_pm]
  · intro s hs
    have := c2_proper_induce_tripling (det_pm_ne_zero m) s hs
    rwa [card_pm] at this

/-! ### `c₂` is an isomorphism invariant; `m K₃,₃ ≅ tripling (m K₂)` -/

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

omit [Fintype V'] in
lemma c2_le_of_iso {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') : c2 G' ≤ c2 G := by
  classical
  obtain ⟨S, hS⟩ := (cliqueSum_iff_sqFit G _).2 (exists_sqFit_c2 G)
  apply Nat.sInf_le
  refine ⟨fun i => (S i).map e.toEquiv.toEmbedding, ?_⟩
  intro u v huv
  have huv' : e.symm u ≠ e.symm v := fun h => huv (e.symm.injective h)
  have h := hS _ _ huv'
  have hadj : G'.Adj u v ↔ G.Adj (e.symm u) (e.symm v) := (e.symm.map_adj_iff).symm
  rw [hadj, h]
  have : ∀ i, (u ∈ (S i).map e.toEquiv.toEmbedding ∧ v ∈ (S i).map e.toEquiv.toEmbedding) ↔
      (e.symm u ∈ S i ∧ e.symm v ∈ S i) := by
    intro i
    simp only [Finset.mem_map_equiv]
    rfl
  simp only [this]

theorem c2_iso {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') : c2 G = c2 G' :=
  le_antisymm (c2_le_of_iso e.symm) (c2_le_of_iso e)

/-- `Fin 6 ≃ Bool × Fin 3`: `a ↦ (a < 3, a mod 3)`. -/
def six : Fin 6 ≃ Bool × Fin 3 where
  toFun a := (decide (a.val < 3), ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩)
  invFun p := ⟨(if p.1 then 0 else 3) + p.2.val, by cases p.1 <;> simp <;> omega⟩
  left_inv a := by revert a; decide
  right_inv p := by revert p; decide

/-- The vertex bijection `(a, c) ↦ ((c, a < 3), a mod 3)`. -/
def mK33Equiv (m : ℕ) : Fin 6 × Fin m ≃ (Fin m × Bool) × Fin 3 :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr (Equiv.refl _) six).trans
    (Equiv.prodAssoc _ _ _).symm)

lemma mK33Equiv_apply (m : ℕ) (a : Fin 6) (c : Fin m) :
    mK33Equiv m (a, c) = ((c, decide (a.val < 3)), ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩) :=
  rfl

/-- **`m K₃,₃` is the tripling of `m K₂`.** -/
def mK33_iso_tripling_pm (m : ℕ) : EvenK.mK33 m ≃g tripling (pm m) where
  toEquiv := mK33Equiv m
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    simp only [mK33Equiv_apply, tripling_adj, pm, EvenK.mK33, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_cases ha : a.val < 3 <;> by_cases ha' : a'.val < 3 <;> simp_all
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_cases ha : a.val < 3 <;> by_cases ha' : a'.val < 3 <;> simp_all

/-- `even_k_remark`'s value `c₂(m K₃,₃) = 2m + 1`, re-derived from 54-f through the isomorphism. -/
theorem c2_mK33_via_tripling (m : ℕ) (hm : 1 ≤ m) : c2 (EvenK.mK33 m) = 2 * m + 1 := by
  rw [c2_iso (mK33_iso_tripling_pm m)]
  exact (tripling_pm m hm).2.1

end FreeDiagonal.EvenComplementation
