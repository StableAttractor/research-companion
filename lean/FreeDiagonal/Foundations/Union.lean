import FreeDiagonal.Foundations.Rank

/-!
# Stage B: the union rank formula, proved

`union_minmax_submodular` is the min-max inequality behind the matroid union theorem, in the
form `max_A r₁(A) + r₂(S \ A) ≥ min_X |S \ X| + r₁(X) + r₂(X)`. It holds for any two
submodular functions `r₁ r₂ : Finset ι → ℤ`; monotonicity and the unit-increase property are
not needed. The proof is by induction on `S`, contracting the new element in `r₁` and in `r₂`.

`frk_submod`: the rank of a family of vectors is submodular. Together these give
`unionRankFormula : UnionRankFormula F` for every field `F`, which discharges the one hypothesis
of Stage A.
-/

open Finset Submodule Module

universe u v w

namespace FreeDiagonal

/-- **The one assumption of Stage A.** The hard direction of the matroid union theorem
(Edmonds; Nash-Williams) for two linear matroids: for any two families `f g` of vectors indexed
by `ι` and any finite ground set `S`, some partition `S = A ⊔ (S \ A)` and some `X ⊆ S` satisfy
`|S \ X| + rk_f(X) + rk_g(X) ≤ rk_f(A) + rk_g(S \ A)`. -/
def UnionRankFormula (F : Type u) [Field F] : Prop :=
  ∀ (ι : Type v) (V : Type w) [DecidableEq ι] [AddCommGroup V] [Module F V] (f g : ι → V)
    (S : Finset ι), ∃ A ⊆ S, ∃ X ⊆ S,
      (S \ X).card + frk F f X + frk F g X ≤ frk F f A + frk F g (S \ A)


/-- `r` is submodular on finite sets. -/
def Submod {ι : Type*} [DecidableEq ι] (r : Finset ι → ℤ) : Prop :=
  ∀ P Q : Finset ι, r (P ∪ Q) + r (P ∩ Q) ≤ r P + r Q

lemma Submod.contract {ι : Type*} [DecidableEq ι] {r : Finset ι → ℤ} (h : Submod r) (e : ι) :
    Submod (fun Y => r (insert e Y) - 1) := by
  intro P Q
  have hU : insert e (P ∪ Q) = insert e P ∪ insert e Q := by ext x; simp only [mem_insert, mem_union]; tauto
  have := h (insert e P) (insert e Q)
  simp only
  rw [hU, insert_inter_distrib]
  linarith

/-- **Min-max inequality for two submodular functions** (the hard direction of the matroid
union theorem when `r₁, r₂` are matroid rank functions). -/
theorem union_minmax_submodular {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    ∀ (r1 r2 : Finset ι → ℤ), Submod r1 → Submod r2 →
      ∃ A ⊆ S, ∃ X ⊆ S, ((S \ X).card : ℤ) + r1 X + r2 X ≤ r1 A + r2 (S \ A) := by
  induction S using Finset.induction_on with
  | empty =>
    intro r1 r2 _ _
    exact ⟨∅, Subset.refl _, ∅, Subset.refl _, by simp⟩
  | insert e S' he ih =>
    intro r1 r2 h1 h2
    -- a minimiser `X` of `g(X) = |S \ X| + r₁ X + r₂ X`
    set g : Finset ι → ℤ := fun X => ((insert e S' \ X).card : ℤ) + r1 X + r2 X with hg
    obtain ⟨X, hXS, hXmin⟩ :=
      exists_min_image (insert e S').powerset g ⟨∅, empty_mem_powerset _⟩
    rw [mem_powerset] at hXS
    -- the induction hypothesis, after contracting `e` in `r₁` and in `r₂`
    obtain ⟨A1, hA1, Y, hY, hy⟩ := ih (fun Y => r1 (insert e Y) - 1) r2 (h1.contract e) h2
    obtain ⟨A2, hA2, Z, hZ, hz⟩ := ih r1 (fun Y => r2 (insert e Y) - 1) h1 (h2.contract e)
    try dsimp only at hy hz
    have heY : e ∉ Y := fun h => he (hY h)
    have heZ : e ∉ Z := fun h => he (hZ h)
    have heA2 : e ∉ A2 := fun h => he (hA2 h)
    -- set identities
    have c1 : insert e S' \ insert e A1 = S' \ A1 := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd (Or.inl h) h'
        · exact ⟨h, fun h'' => h' (Or.inr h'')⟩
      · rintro ⟨h, h'⟩
        exact ⟨Or.inr h, fun h'' => h''.elim (fun h3 => he (h3 ▸ h)) h'⟩
    have c2 : insert e S' \ A2 = insert e (S' \ A2) := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact ⟨Or.inl h, h ▸ heA2⟩
        · exact ⟨Or.inr h, h'⟩
    have hYZu : Y ∪ Z ⊆ S' := union_subset hY hZ
    have hYZi : Y ∩ Z ⊆ S' := inter_subset_left.trans hY
    have c5 : insert e S' \ insert e (Y ∪ Z) = S' \ (Y ∪ Z) := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd (Or.inl h) h'
        · exact ⟨h, fun h'' => h' (Or.inr h'')⟩
      · rintro ⟨h, h'⟩
        exact ⟨Or.inr h, fun h'' => h''.elim (fun h3 => he (h3 ▸ h)) h'⟩
    have c6 : insert e S' \ (Y ∩ Z) = insert e (S' \ (Y ∩ Z)) := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact ⟨Or.inl h, fun h'' => heY (h ▸ (mem_inter.1 h'').1)⟩
        · exact ⟨Or.inr h, h'⟩
    have he6 : e ∉ S' \ (Y ∩ Z) := fun h => he (mem_sdiff.1 h).1
    -- cardinalities
    have k1 := card_sdiff_add_card_eq_card hY
    have k2 := card_sdiff_add_card_eq_card hZ
    have k3 := card_sdiff_add_card_eq_card hYZu
    have k4 := card_sdiff_add_card_eq_card hYZi
    have k5 := card_union_add_card_inter Y Z
    have k6 := card_insert_of_notMem he6
    -- the two candidate sets for the minimum
    have hV : insert e (Y ∪ Z) ⊆ insert e S' := insert_subset_insert e hYZu
    have hW : Y ∩ Z ⊆ insert e S' := hYZi.trans (subset_insert e S')
    have gV := hXmin _ (mem_powerset.2 hV)
    have gW := hXmin _ (mem_powerset.2 hW)
    simp only [hg, c5, c6] at gV gW
    -- submodularity
    have s1 := h1 (insert e Y) Z
    have s2 := h2 Y (insert e Z)
    have u1 : insert e Y ∪ Z = insert e (Y ∪ Z) := by ext x; simp only [mem_insert, mem_union]; tauto
    have u2 : Y ∪ insert e Z = insert e (Y ∪ Z) := by ext x; simp only [mem_insert, mem_union]; tauto
    have i1 : insert e Y ∩ Z = Y ∩ Z := by
      ext x; simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd (h ▸ h') heZ
        · exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨Or.inr h, h'⟩
    have i2 : Y ∩ insert e Z = Y ∩ Z := by
      ext x; simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact absurd (h' ▸ h) heY
        · exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, Or.inr h'⟩
    rw [u1, i1] at s1
    rw [u2, i2] at s2
    -- one of the two partitions reaches the minimum
    by_cases hcase : g X ≤ r1 (insert e A1) + r2 (insert e S' \ insert e A1)
    · exact ⟨insert e A1, insert_subset_insert e hA1, X, hXS, hcase⟩
    · refine ⟨A2, hA2.trans (subset_insert e S'), X, hXS, ?_⟩
      rw [c1] at hcase
      rw [c2]
      simp only [hg] at hcase ⊢
      omega

/-- The rank of a family of vectors is submodular. -/
lemma frk_submod {F : Type*} [Field F] {ι V : Type*} [DecidableEq ι] [AddCommGroup V]
    [Module F V] (f : ι → V) : Submod (fun X => (frk F f X : ℤ)) := by
  intro P Q
  have hU : span F (f '' ((P ∪ Q : Finset ι) : Set ι)) =
      span F (f '' (P : Set ι)) ⊔ span F (f '' (Q : Set ι)) := by
    rw [coe_union, Set.image_union, span_union]
  have hI : span F (f '' ((P ∩ Q : Finset ι) : Set ι)) ≤
      span F (f '' (P : Set ι)) ⊓ span F (f '' (Q : Set ι)) :=
    le_inf (span_mono (Set.image_mono (coe_subset.2 inter_subset_left)))
      (span_mono (Set.image_mono (coe_subset.2 inter_subset_right)))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (span F (f '' (P : Set ι)))
    (span F (f '' (Q : Set ι)))
  have h2 := Submodule.finrank_mono hI
  dsimp only
  unfold frk
  rw [hU]
  omega

/-- **Stage B.** The union rank formula holds over every field. -/
theorem unionRankFormula (F : Type u) [Field F] : UnionRankFormula.{u, v, w} F := by
  intro ι V _ _ _ f g S
  obtain ⟨A, hA, X, hX, h⟩ :=
    union_minmax_submodular S _ _ (frk_submod (F := F) f) (frk_submod (F := F) g)
  exact ⟨A, hA, X, hX, by exact_mod_cast h⟩

end FreeDiagonal
