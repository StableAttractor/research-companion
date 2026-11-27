import FreeDiagonal.Closure.Basic

/-!
# Dial settings

A dial setting gives each index `i` a value `d i : Option F`: `none` means "deleted" (U6's `∞`),
`some t` means "row `i` of `G` minus `t eᵢ`". `dialMat G d` is the matrix whose rows and
columns at deleted indices are unit vectors and which equals `G - diag t` elsewhere.

* `mem_ker_dialMat`: its kernel is `{v | ∀ i, (vᵢ, (Gv)ᵢ) satisfies the dial condition}`.
* `rank_unit_rows`: unit rows split off: `rank Z = |N| + rank Z[Nᶜ, Nᶜ]`.
* `rank_dialMat_eq` (U6 (1.1)): for `G = x + diagonal g`, the rank of `dialMat G d` is
  (number of deleted indices) + (rank of a completion of `x` on the others).
* `closRank_le_cost`, `closRank_subPattern_ge`: `ρ(x)` and `ρ(x_T)` through dial settings.
-/

open Matrix Finset Module Submodule

namespace FreeDiagonal

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- The condition a dial value imposes on the pair `(vᵢ, (Gv)ᵢ)`. -/
def DialCond : Option F → F → F → Prop
  | none, a, _ => a = 0
  | some t, a, b => b = t * a

/-- The dial matrix. -/
def dialMat (G : Matrix n n F) (d : n → Option F) : Matrix n n F :=
  Matrix.of fun i j => match d i, d j with
    | some t, some _ => G i j - if i = j then t else 0
    | _, _ => if i = j then 1 else 0

variable {G : Matrix n n F} {d : n → Option F}

lemma dialMat_none_row {i : n} (h : d i = none) (j : n) :
    dialMat G d i j = if i = j then 1 else 0 := by
  simp [dialMat, h]

lemma dialMat_none_col {j : n} (h : d j = none) (i : n) :
    dialMat G d i j = if i = j then 1 else 0 := by
  cases hi : d i <;> simp [dialMat, hi, h]

lemma dialMat_some {i j : n} {t t' : F} (hi : d i = some t) (hj : d j = some t') :
    dialMat G d i j = G i j - if i = j then t else 0 := by
  simp [dialMat, hi, hj]

lemma dialMat_mulVec_none (v : n → F) {i : n} (h : d i = none) :
    (dialMat G d *ᵥ v) i = v i := by
  simp [mulVec, dotProduct, dialMat_none_row h]

lemma dialMat_mulVec_some (v : n → F) (hv : ∀ j, d j = none → v j = 0) {i : n} {t : F}
    (h : d i = some t) : (dialMat G d *ᵥ v) i = (G *ᵥ v) i - t * v i := by
  have : ∀ j, dialMat G d i j * v j = (G i j - if i = j then t else 0) * v j := by
    intro j
    cases hj : d j with
    | none => simp [hv j hj]
    | some t' => rw [dialMat_some h hj]
  simp only [mulVec, dotProduct, this, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, mem_univ, if_true]

/-- The kernel of a dial matrix. -/
lemma mem_ker_dialMat (G : Matrix n n F) (d : n → Option F) (v : n → F) :
    v ∈ LinearMap.ker (dialMat G d).mulVecLin ↔ ∀ i, DialCond (d i) (v i) ((G *ᵥ v) i) := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    have hv : ∀ j, d j = none → v j = 0 := fun j hj => by
      have := congrFun h j; rwa [dialMat_mulVec_none v hj] at this
    intro i
    cases hi : d i with
    | none => exact hv i hi
    | some t =>
      have := congrFun h i
      rw [dialMat_mulVec_some v hv hi] at this
      exact (sub_eq_zero.1 this)
  · intro h
    have hv : ∀ j, d j = none → v j = 0 := fun j hj => by
      have := h j; rw [hj] at this; exact this
    ext i
    cases hi : d i with
    | none => rw [dialMat_mulVec_none v hi, hv i hi]; rfl
    | some t =>
      have := h i; rw [hi] at this
      rw [dialMat_mulVec_some v hv hi]
      simp only [DialCond] at this
      rw [this]; simp

/-! ### Rank and kernels -/

lemma rank_add_finrank_ker {m k : Type*} [Fintype k] (M : Matrix m k F) [Fintype m] :
    M.rank + finrank F (LinearMap.ker M.mulVecLin) = Fintype.card k := by
  unfold Matrix.rank
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- Two subspaces matched by mutually inverse linear maps have the same dimension. -/
lemma finrank_eq_of_inverse {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (p : Submodule F V) (q : Submodule F W) (f : V →ₗ[F] W) (g : W →ₗ[F] V)
    (hf : ∀ x ∈ p, f x ∈ q) (hg : ∀ y ∈ q, g y ∈ p) (hgf : ∀ x ∈ p, g (f x) = x)
    (hfg : ∀ y ∈ q, f (g y) = y) : finrank F p = finrank F q := by
  let e : p ≃ₗ[F] q :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp)
      invFun := fun y => ⟨g y, hg y y.2⟩
      left_inv := fun x => Subtype.ext (hgf x x.2)
      right_inv := fun y => Subtype.ext (hfg y y.2) }
  exact e.finrank_eq

/-- Extension by zero from a subset. -/
def extZ (S : Finset n) : (↥S → F) →ₗ[F] (n → F) where
  toFun w i := if h : i ∈ S then w ⟨i, h⟩ else 0
  map_add' w w' := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c w := by ext i; by_cases h : i ∈ S <;> simp [h]

lemma extZ_apply_mem (S : Finset n) (w : ↥S → F) {i : n} (h : i ∈ S) :
    extZ S w i = w ⟨i, h⟩ := by simp [extZ, h]

lemma extZ_apply_not_mem (S : Finset n) (w : ↥S → F) {i : n} (h : i ∉ S) :
    extZ S w i = 0 := by simp [extZ, h]

/-- **Unit rows split off.** If the rows of `Z` indexed by `N` are unit vectors, then
`rank Z = |N| + rank Z[Nᶜ, Nᶜ]`. -/
lemma rank_unit_rows (Z : Matrix n n F) (N : Finset n)
    (h : ∀ i ∈ N, ∀ j, Z i j = if i = j then 1 else 0) :
    Z.rank = N.card + (Z.submatrix (fun a : ↥(Nᶜ) => (a : n)) (fun a : ↥(Nᶜ) => (a : n))).rank := by
  set S := Nᶜ
  set Zs := Z.submatrix (fun a : ↥S => (a : n)) (fun a : ↥S => (a : n))
  have hrow : ∀ v : n → F, ∀ i ∈ N, (Z *ᵥ v) i = v i := by
    intro v i hi; simp [mulVec, dotProduct, h i hi]
  have hsum : ∀ (v : n → F), (∀ j ∈ N, v j = 0) → ∀ a : ↥S,
      (Zs *ᵥ (fun b : ↥S => v b)) a = (Z *ᵥ v) a := by
    intro v hv a
    simp only [mulVec, dotProduct, Zs, submatrix_apply]
    rw [Finset.sum_coe_sort S (fun j => Z a j * v j), ← Finset.sum_add_sum_compl S]
    have : ∑ j ∈ Sᶜ, Z a j * v j = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [hv j (by simpa [S] using hj), mul_zero]
    rw [this, add_zero]
  have hk : finrank F (LinearMap.ker Z.mulVecLin) = finrank F (LinearMap.ker Zs.mulVecLin) := by
    apply finrank_eq_of_inverse _ _ (LinearMap.funLeft F F (fun a : ↥S => (a : n))) (extZ S)
    · intro v hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      have hv0 : ∀ j ∈ N, v j = 0 := fun j hj => by
        have := congrFun hv j; rwa [hrow v j hj] at this
      ext a
      show (Zs *ᵥ (fun b : ↥S => v b)) a = (0 : ↥S → F) a
      rw [hsum v hv0 a, hv]; rfl
    · intro w hw
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
      ext i
      by_cases hi : i ∈ N
      · rw [hrow _ i hi, extZ_apply_not_mem S w (by simpa [S] using hi)]; rfl
      · have hiS : i ∈ S := by simpa [S] using hi
        have := hsum (extZ S w) (fun j hj => extZ_apply_not_mem S w (by simpa [S] using hj))
          ⟨i, hiS⟩
        have e : (fun b : ↥S => extZ S w b) = w := funext fun b => extZ_apply_mem S w b.2
        rw [e] at this
        rw [← this, congrFun hw]; rfl
    · intro v hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      ext i
      by_cases hi : i ∈ S
      · rw [extZ_apply_mem S _ hi]; rfl
      · rw [extZ_apply_not_mem S _ hi]
        have hiN : i ∈ N := by simpa [S] using hi
        have := congrFun hv i
        rw [hrow v i hiN] at this
        exact this.symm
    · intro w _
      ext a
      rw [LinearMap.funLeft_apply]
      exact extZ_apply_mem S w a.2
  have h1 := rank_add_finrank_ker Z
  have h2 := rank_add_finrank_ker Zs
  have h3 : Fintype.card ↥S = Fintype.card n - N.card := by
    simp [S, Fintype.card_coe, card_compl]
  have h4 : N.card ≤ Fintype.card n := card_le_univ N
  omega

/-- **U6 (1.1).** For `G = x + diagonal g` and a dial setting `d` deleting exactly `N`, the rank
of the dial matrix is `|N|` plus the rank of a completion of `x` on `Nᶜ`. -/
lemma rank_dialMat_eq (x : Matrix n n F) (g : n → F) (d : n → Option F) (N : Finset n)
    (hN : ∀ i, d i = none ↔ i ∈ N) :
    (dialMat (x + diagonal g) d).rank = N.card +
      (subPattern x Nᶜ + diagonal (fun a : ↥(Nᶜ) => g a - (d a).getD 0)).rank := by
  rw [rank_unit_rows (dialMat (x + diagonal g) d) N
    (fun i hi j => dialMat_none_row ((hN i).2 hi) j)]
  congr 2
  ext a b
  have ha : d a ≠ none := fun h => (mem_compl.1 a.2) ((hN a).1 h)
  have hb : d b ≠ none := fun h => (mem_compl.1 b.2) ((hN b).1 h)
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 ha
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.1 hb
  simp only [submatrix_apply, dialMat_some ht ht', Matrix.add_apply, subPattern]
  by_cases hab : a = b
  · subst hab; simp [ht]; ring
  · have : (a : n) ≠ b := fun h => hab (Subtype.ext h)
    simp [diagonal_apply_ne _ this, diagonal_apply_ne _ hab, this]

/-- `ρ(x)` is at most the rank of every dial matrix of every completion. -/
lemma closRank_le_cost (x : Matrix n n F) (g : n → F) (d : n → Option F) :
    closRank x ≤ (dialMat (x + diagonal g) d).rank := by
  classical
  set N := univ.filter fun i => d i = none
  rw [rank_dialMat_eq x g d N (fun i => by simp [N])]
  exact (closRank_le x N).trans (Nat.add_le_add_left (minCompRank_le _ _) _)

/-- Every generalized completion of `x` is a dial setting. -/
lemma exists_dial_of_deletion (x : Matrix n n F) (g : n → F) (D : Finset n) (e : ↥(Dᶜ) → F) :
    ∃ d : n → Option F, (∀ i, d i = none ↔ i ∈ D) ∧
      (dialMat (x + diagonal g) d).rank = D.card + (subPattern x Dᶜ + diagonal e).rank := by
  classical
  set d : n → Option F := fun i => if h : i ∈ D then none else some (g i - e ⟨i, mem_compl.2 h⟩)
  have hN : ∀ i, d i = none ↔ i ∈ D := fun i => by by_cases h : i ∈ D <;> simp [d, h]
  refine ⟨d, hN, ?_⟩
  rw [rank_dialMat_eq x g d D hN]
  have : (fun a : ↥(Dᶜ) => g a - (d a).getD 0) = e := by
    funext a
    have ha : (a : n) ∉ D := mem_compl.1 a.2
    simp [d, ha]
  rw [this]

/-- **`ρ(x_T)` through dial settings.** If every dial setting deleting at least the indices
outside `T` has rank at least `|Tᶜ| + q`, then `ρ(x_T) ≥ q`. -/
lemma closRank_subPattern_ge (x : Matrix n n F) (g : n → F) (T : Finset n) (q : ℕ)
    (h : ∀ d : n → Option F, (∀ i ∉ T, d i = none) →
      (univ \ T).card + q ≤ (dialMat (x + diagonal g) d).rank) :
    q ≤ closRank (subPattern x T) := by
  classical
  apply le_closRank
  intro D'
  obtain ⟨e', he'⟩ := exists_minCompRank (subPattern (subPattern x T) D'ᶜ)
  set D : Finset n := (univ \ T) ∪ D'.map (Function.Embedding.subtype _)
  have hmem : ∀ i : ↥(Dᶜ), i.1 ∈ T ∧ ∀ h : i.1 ∈ T, (⟨i.1, h⟩ : ↥T) ∈ D'ᶜ := by
    intro i
    have hi := i.2
    simp only [D, mem_compl, mem_union, mem_sdiff, mem_univ, true_and, mem_map,
      Function.Embedding.coe_subtype, not_or, not_not] at hi
    exact ⟨hi.1, fun h => mem_compl.2 (fun h' => hi.2 ⟨_, h', rfl⟩)⟩
  set φ : ↥(Dᶜ) → ↥(D'ᶜ) := fun i => ⟨⟨i.1, (hmem i).1⟩, (hmem i).2 _⟩
  set e : ↥(Dᶜ) → F := fun i => e' (φ i)
  have hrank : (subPattern x Dᶜ + diagonal e).rank ≤
      minCompRank (subPattern (subPattern x T) D'ᶜ) := by
    rw [← he']
    have hφ : Function.Injective φ := fun a b hab =>
      Subtype.ext (by simpa [φ] using congrArg (fun z => z.1.1) hab)
    have eq : subPattern x Dᶜ + diagonal e =
        (subPattern (subPattern x T) D'ᶜ + diagonal e').submatrix φ φ := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [e, subPattern, φ]
      · have : φ a ≠ φ b := fun h => hab (hφ h)
        simp [subPattern, diagonal_apply_ne _ hab, diagonal_apply_ne _ this, φ]
    rw [eq]; exact rank_submatrix_le _ _ _
  obtain ⟨d, hd, hcost⟩ := exists_dial_of_deletion x g D e
  have hoff : ∀ i ∉ T, d i = none := fun i hi =>
    (hd i).2 (mem_union_left _ (mem_sdiff.2 ⟨mem_univ _, hi⟩))
  have hcardD : D.card = (univ \ T).card + D'.card := by
    rw [card_union_of_disjoint, card_map]
    rw [disjoint_left]
    intro i hi hi'
    simp only [mem_map, Function.Embedding.coe_subtype] at hi'
    obtain ⟨a, -, rfl⟩ := hi'
    exact (mem_sdiff.1 hi).2 a.2
  have := h d hoff
  omega

end FreeDiagonal
