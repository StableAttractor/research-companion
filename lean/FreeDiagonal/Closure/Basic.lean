import FreeDiagonal.Witness.Unconditional

/-!
# Closure rank: definition and elementary facts

`closRank x = min over D of |D| + c(x on the complement of D)`: each index is either given a
diagonal entry or deleted at cost one (draft U6, Section 1, formula (1.1); Part 47). Any field;
the pattern need not be symmetric. Its equality with the Zariski closure of the completable
patterns (U6 Proposition 1.1) is NOT formalized.

Facts: (a) `closRank_subPattern_le`, (b) `cutRank_le_closRank`, (c) `closRank_le_erase_add_one`,
`closRank_le_minCompRank`, monotonicity on nested index sets.
-/

open Matrix Finset

namespace FreeDiagonal

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- Closure rank `ρ(x)`. -/
noncomputable def closRank (x : Matrix n n F) : ℕ :=
  ⨅ D : Finset n, D.card + minCompRank (subPattern x Dᶜ)

lemma closRank_le (x : Matrix n n F) (D : Finset n) :
    closRank x ≤ D.card + minCompRank (subPattern x Dᶜ) :=
  ciInf_le (OrderBot.bddBelow _) D

lemma exists_closRank (x : Matrix n n F) :
    ∃ D : Finset n, D.card + minCompRank (subPattern x Dᶜ) = closRank x := by
  have h : closRank x ∈ Set.range (fun D : Finset n => D.card + minCompRank (subPattern x Dᶜ)) := by
    unfold closRank; exact Nat.sInf_mem (Set.range_nonempty _)
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hD⟩

lemma le_closRank (x : Matrix n n F) {r : ℕ}
    (h : ∀ D : Finset n, r ≤ D.card + minCompRank (subPattern x Dᶜ)) : r ≤ closRank x :=
  le_ciInf h

/-- `ρ` does not increase under injective reindexing (it only sees off-diagonal entries). -/
lemma closRank_le_of_embedding {m : Type*} [Fintype m] [DecidableEq m] (x : Matrix n n F)
    (y : Matrix m m F) (f : m → n) (hf : Function.Injective f)
    (hy : ∀ a b, a ≠ b → y a b = x (f a) (f b)) : closRank y ≤ closRank x := by
  obtain ⟨D, hD⟩ := exists_closRank x
  set Dy : Finset m := univ.filter (fun a => f a ∈ D)
  have hcard : Dy.card ≤ D.card :=
    Finset.card_le_card_of_injOn f (fun a ha => (mem_filter.1 ha).2) hf.injOn
  have hmem : ∀ a : ↥(Dyᶜ), f a.1 ∈ Dᶜ := fun a => by
    have := a.2; simp only [Dy, mem_compl, mem_filter, mem_univ, true_and] at this
    exact mem_compl.2 this
  have hc : minCompRank (subPattern y Dyᶜ) ≤ minCompRank (subPattern x Dᶜ) :=
    minCompRank_le_of_embedding (subPattern x Dᶜ) (subPattern y Dyᶜ)
      (fun a => ⟨f a.1, hmem a⟩)
      (fun a b h => Subtype.ext (hf (congrArg Subtype.val h)))
      (fun a b hab => hy a.1 b.1 (fun h => hab (Subtype.ext h)))
  calc closRank y ≤ Dy.card + minCompRank (subPattern y Dyᶜ) := closRank_le y Dy
    _ ≤ D.card + minCompRank (subPattern x Dᶜ) := add_le_add hcard hc
    _ = closRank x := hD

/-- **Fact (a) for `ρ`.** -/
lemma closRank_subPattern_le (x : Matrix n n F) (T : Finset n) :
    closRank (subPattern x T) ≤ closRank x :=
  closRank_le_of_embedding x _ _ Subtype.val_injective (fun _ _ _ => rfl)

lemma closRank_subPattern_mono (x : Matrix n n F) {T T' : Finset n} (h : T ⊆ T') :
    closRank (subPattern x T) ≤ closRank (subPattern x T') :=
  closRank_le_of_embedding (subPattern x T') (subPattern x T) (fun a => ⟨a.1, h a.2⟩)
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) (fun _ _ _ => rfl)

lemma closRank_le_subPattern_univ (x : Matrix n n F) :
    closRank x ≤ closRank (subPattern x univ) :=
  closRank_le_of_embedding (subPattern x univ) x (fun i => ⟨i, mem_univ i⟩)
    (fun _ _ h => by simpa using h) (fun _ _ _ => rfl)

/-- `ρ ≤ c`. -/
lemma closRank_le_minCompRank (x : Matrix n n F) : closRank x ≤ minCompRank x := by
  have h := closRank_le x ∅
  rw [card_empty, zero_add] at h
  exact h.trans (minCompRank_subPattern_le x _)

/-- **Fact (c) for `ρ`.** Adding one index raises `ρ` by at most one. -/
lemma closRank_le_erase_add_one (x : Matrix n n F) (v : n) :
    closRank x ≤ closRank (subPattern x (univ.erase v)) + 1 := by
  set T := univ.erase v
  obtain ⟨D', hD'⟩ := exists_closRank (subPattern x T)
  set D : Finset n := insert v (D'.map (Function.Embedding.subtype _))
  have hcard : D.card ≤ D'.card + 1 := (card_insert_le _ _).trans (by simp)
  have hmem : ∀ i : ↥(Dᶜ), i.1 ∈ T ∧ ∀ h : i.1 ∈ T, (⟨i.1, h⟩ : ↥T) ∈ D'ᶜ := by
    intro i
    have hi := i.2
    simp only [D, mem_compl, mem_insert, mem_map, Function.Embedding.coe_subtype,
      not_or] at hi
    refine ⟨mem_erase.2 ⟨hi.1, mem_univ _⟩, fun h => mem_compl.2 (fun h' => hi.2 ⟨_, h', rfl⟩)⟩
  have hc : minCompRank (subPattern x Dᶜ) ≤ minCompRank (subPattern (subPattern x T) D'ᶜ) :=
    minCompRank_le_of_embedding (subPattern (subPattern x T) D'ᶜ) (subPattern x Dᶜ)
      (fun i => ⟨⟨i.1, (hmem i).1⟩, (hmem i).2 _⟩)
      (fun a b h => Subtype.ext (by simpa using congrArg (fun z => z.1.1) h))
      (fun _ _ _ => rfl)
  calc closRank x ≤ D.card + minCompRank (subPattern x Dᶜ) := closRank_le x D
    _ ≤ (D'.card + 1) + minCompRank (subPattern (subPattern x T) D'ᶜ) := add_le_add hcard hc
    _ = closRank (subPattern x T) + 1 := by rw [← hD']; ring

/-- Fact (c) inside a sub-pattern. -/
lemma closRank_subPattern_le_erase (x : Matrix n n F) (T : Finset n) {v : n} (hv : v ∈ T) :
    closRank (subPattern x T) ≤ closRank (subPattern x (T.erase v)) + 1 := by
  have h := closRank_le_erase_add_one (subPattern x T) ⟨v, hv⟩
  have h2 : closRank (subPattern (subPattern x T) (univ.erase ⟨v, hv⟩)) ≤
      closRank (subPattern x (T.erase v)) := by
    apply closRank_le_of_embedding (subPattern x (T.erase v)) _
      (fun a => ⟨a.1.1, mem_erase.2 ⟨fun h => (mem_erase.1 a.2).1 (Subtype.ext h), a.1.2⟩⟩)
      (fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
      (fun _ _ _ => rfl)
  omega

/-- Removing `s` indices lowers `ρ` by at most `s`. -/
lemma exists_subset_closRank (x : Matrix n n F) :
    ∀ (s : ℕ) (T : Finset n), s ≤ T.card → ∃ T' ⊆ T, T'.card = T.card - s ∧
      closRank (subPattern x T) ≤ closRank (subPattern x T') + s := by
  intro s
  induction s with
  | zero => intro T _; exact ⟨T, Subset.refl _, by simp, by simp⟩
  | succ s ih =>
    intro T hs
    obtain ⟨T'', hsub, hcard, hle⟩ := ih T (by omega)
    obtain ⟨v, hv⟩ : T''.Nonempty := by
      rw [← card_pos]; omega
    refine ⟨T''.erase v, (erase_subset _ _).trans hsub, ?_, ?_⟩
    · rw [card_erase_of_mem hv]; omega
    · have := closRank_subPattern_le_erase x T'' hv
      omega

/-- **Fact (b) for `ρ`.** Every cut rank is at most `ρ`. -/
lemma cutRank_le_closRank (x : Matrix n n F) (A : Finset n) :
    (x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))).rank ≤ closRank x := by
  classical
  obtain ⟨D, hD⟩ := exists_closRank x
  rw [← hD]
  set M := x.submatrix (fun a : A => (a : n)) (fun b : ↥(Aᶜ) => (b : n))
  set R : Finset ↥A := univ.filter fun a => a.1 ∉ D
  set C : Finset ↥(Aᶜ) := univ.filter fun b => b.1 ∉ D
  set N := M.submatrix (fun r : R => (r : ↥A)) id
  have h1 : M.rank ≤ N.rank + (univ \ R).card := rank_le_rank_submatrix_rows_add M R
  have h2 := rank_le_rank_submatrix_rows_add Nᵀ C
  rw [rank_transpose] at h2
  set Q := Nᵀ.submatrix (fun c : C => (c : ↥(Aᶜ))) id
  have hQ : Q.rank ≤ minCompRank (subPattern x Dᶜ) := by
    have hr : ∀ r : R, (r.1 : n) ∈ Dᶜ := fun r => mem_compl.2 (mem_filter.1 r.2).2
    have hc : ∀ c : C, (c.1 : n) ∈ Dᶜ := fun c => mem_compl.2 (mem_filter.1 c.2).2
    have e : Qᵀ = (subPattern x Dᶜ).submatrix (fun r : R => (⟨r.1, hr r⟩ : ↥(Dᶜ)))
        (fun c : C => (⟨c.1, hc c⟩ : ↥(Dᶜ))) := by
      ext r c; rfl
    rw [← rank_transpose, e]
    apply offDiag_rank_le_minCompRank
    intro r c h
    have h' : (r.1 : n) = c.1 := congrArg Subtype.val h
    exact (mem_compl.1 c.1.2) (h' ▸ r.1.2)
  have hcards : (univ \ R).card + (univ \ C).card ≤ D.card := by
    have e1 : ((univ \ R).map (Function.Embedding.subtype _)) ⊆ D.filter (· ∈ A) := by
      intro i hi
      simp only [mem_map, mem_sdiff, mem_univ, true_and, R, mem_filter, not_not,
        Function.Embedding.coe_subtype] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact mem_filter.2 ⟨ha, a.2⟩
    have e2 : ((univ \ C).map (Function.Embedding.subtype _)) ⊆ D.filter (· ∉ A) := by
      intro i hi
      simp only [mem_map, mem_sdiff, mem_univ, true_and, C, mem_filter, not_not,
        Function.Embedding.coe_subtype] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact mem_filter.2 ⟨ha, mem_compl.1 a.2⟩
    have c1 := card_le_card e1
    have c2 := card_le_card e2
    rw [card_map] at c1 c2
    have := card_filter_add_card_filter_not (s := D) (fun i => i ∈ A)
    omega
  calc M.rank ≤ N.rank + (univ \ R).card := h1
    _ ≤ Q.rank + (univ \ C).card + (univ \ R).card := by omega
    _ ≤ D.card + minCompRank (subPattern x Dᶜ) := by omega

end FreeDiagonal
