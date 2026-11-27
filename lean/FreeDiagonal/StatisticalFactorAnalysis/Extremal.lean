import FreeDiagonal.StatisticalFactorAnalysis.Correlations

/-!
# Theorem 3 (extremal matrices): preparations

`G` is a reference of least rank `q` of `Σ`, `ρ(X)` the rank of the rows of `G` indexed by
`X` (`frk ℝ G.row X`), `t = m + 3 - q`.

* `theorem2_sets_iii'`: the set `T` of the proof of Theorem 2 has
  `|T| ≤ |E \ Z| + t ρ(Z)` for every `Z` (not only for `Z = E`).
* `factor_of_span`: if the rows of `G` indexed by `B` span all rows, then `G = C G[B,B] Cᵀ`
  with `C` the coefficient matrix.
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

universe u

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The extension step of Theorem 2 with the sharper size bound: there is `T` with
`|T| ≤ |E \ Z| + t ρ(Z)` for every `Z ⊆ E`, such that a fit on `T` gives one on `E`. -/
theorem theorem2_sets_iii' (A : n → Set ℝ) (m : ℕ) (Sig G : Matrix n n ℝ)
    (hG : IsCompletionIn A Sig G) (hmin : ∀ G', IsCompletionIn A Sig G' → G.rank ≤ G'.rank)
    (hqm : G.rank ≤ m) :
    ∃ T : Finset n, (∀ Z : Finset n,
        (T.card : ℤ) ≤ (univ \ Z).card + ((m + 3 - G.rank : ℕ) : ℤ) * frk ℝ G.row Z) ∧
      (HasFitIn m (fun a : T => A a) (subPattern Sig T) → HasFitIn m A Sig) := by
  classical
  set q := G.rank with hq
  set t := m + 3 - q with ht
  obtain ⟨X, -, hXmin⟩ := exists_min_image (univ : Finset n).powerset
    (fun X => ((univ \ X).card : ℤ) + (t : ℤ) * frk ℝ G.row X)
    ⟨univ, mem_powerset.2 (Subset.refl _)⟩
  have hpack : ∀ Z ⊆ X, (t : ℤ) * frk ℝ G.row X ≤ (X \ Z).card + (t : ℤ) * frk ℝ G.row Z := by
    intro Z hZ
    have h1 := hXmin Z (mem_powerset.2 (subset_univ Z))
    have e1 := card_sdiff_eq' (subset_univ X)
    have e2 := card_sdiff_eq' (subset_univ Z)
    have e3 := card_sdiff_eq' hZ
    linarith
  obtain ⟨B, hBX, hBd, hBc, hBs⟩ := spanning_bases (F := ℝ) G.row t X hpack
  set T := (univ \ X) ∪ univ.biUnion B with hT
  have hTcard : ∀ Z : Finset n, (T.card : ℤ) ≤ (univ \ Z).card + (t : ℤ) * frk ℝ G.row Z := by
    intro Z
    have h1 : T.card ≤ (univ \ X).card + ∑ a, (B a).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
    have h2 : ∑ a : Fin t, (B a).card = t * frk ℝ G.row X := by simp [hBc]
    rw [h2] at h1
    have h1' : (T.card : ℤ) ≤ (univ \ X).card + (t : ℤ) * frk ℝ G.row X := by exact_mod_cast h1
    have := hXmin Z (mem_powerset.2 (subset_univ Z))
    linarith
  refine ⟨T, hTcard, ?_⟩
  rintro ⟨H, hHc, hHpsd, hHr⟩
  obtain ⟨k, v, hv⟩ := exists_gram_of_posSemidef hHpsd
  set Esp := span ℝ (Set.range v) with hEspdef
  set w : T → Esp := fun a => ⟨v a, subset_span ⟨a, rfl⟩⟩ with hwdef
  have hw : ∀ a b, inner ℝ (w a) (w b) = H a b := by
    intro a b; rw [← hv]; simp [w, gram_apply]
  have hEsp : finrank ℝ Esp ≤ m := by
    have := rank_gram v
    rw [hv] at this
    change finrank ℝ (span ℝ (Set.range v)) ≤ m
    omega
  set hn : n → Esp := fun i => if hi : i ∈ T then w ⟨i, hi⟩ else 0 with hndef
  have hnT : ∀ i (hi : i ∈ T) j (hj : j ∈ T), inner ℝ (hn i) (hn j) = H ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i hi j hj; simp [hn, hi, hj, hw]
  obtain ⟨G', hG'c, hG'p, hG'r⟩ := extend_fit A Sig G hG hmin X t (by omega) B hBX hBd hBs hn
    (fun i j hi hj hij => by
      rw [hnT i hi j hj]
      exact hHc.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (fun e => hij (congrArg Subtype.val e)))
    (fun i hi => by
      have hiT : i ∈ T := mem_union_left _ (by simp [hi])
      rw [hnT i hiT i hiT]; exact hHc.2.2 ⟨i, hiT⟩)
    (by omega)
  exact ⟨G', hG'c, hG'p, hG'r.trans hEsp⟩

/-- Coefficient matrix of the rows of `G` on a spanning set `B`. -/
lemma exists_coefMat (G : Matrix n n ℝ) (B : Finset n)
    (hB : span ℝ (G.row '' (B : Set n)) = span ℝ (G.row '' ((univ : Finset n) : Set n))) :
    ∃ C : Matrix n B ℝ, ∀ i, G.row i = ∑ b : B, C i b • G.row b := by
  have h : ∀ i, ∃ c : n → ℝ, G.row i = ∑ b ∈ B, c b • G.row b := fun i =>
    exists_coef G B univ hB (mem_univ i)
  choose c hc using h
  refine ⟨Matrix.of fun i b => c i b, fun i => ?_⟩
  rw [hc i, ← Finset.sum_coe_sort B]
  rfl

/-- `G = C G[B,B] Cᵀ` when the rows `B` span. -/
lemma factor_of_coef {G : Matrix n n ℝ} (hG : G.IsSymm) (B : Finset n) (C : Matrix n B ℝ)
    (hC : ∀ i, G.row i = ∑ b : B, C i b • G.row b) :
    G = C * G.submatrix (fun b : B => (b : n)) (fun b : B => (b : n)) * Cᵀ := by
  have hs : ∀ i j, G i j = G j i := fun i j => symm_apply hG i j
  have hrow : ∀ i j, G i j = ∑ b : B, C i b * G (b : n) j := fun i j => by
    have := congrFun (hC i) j
    simpa [Finset.sum_apply] using this
  refine Matrix.ext fun i l => ?_
  simp only [Matrix.mul_apply, submatrix_apply, transpose_apply]
  rw [hrow i l]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hs (y : n) l, hrow l y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hs (x : n) y]; ring

/-- The rank of rows of `G` is at most the rank of their coefficient rows. -/
lemma frk_le_coef {G : Matrix n n ℝ} (B : Finset n) (C : Matrix n B ℝ)
    (hC : ∀ i, G.row i = ∑ b : B, C i b • G.row b) (X : Finset n) :
    frk ℝ G.row X ≤ frk ℝ C.row X := by
  set f : (B → ℝ) →ₗ[ℝ] (n → ℝ) := Fintype.linearCombination ℝ (fun b : B => G.row b) with hf
  have himg : G.row '' (X : Set n) = f '' (C.row '' (X : Set n)) := by
    rw [Set.image_image]
    refine Set.image_congr fun i _ => ?_
    rw [hC i, hf, Fintype.linearCombination_apply]; rfl
  unfold frk
  rw [himg, span_image]
  exact finrank_map_le f _

/-- `G` is positive definite on the span of its rows indexed by `X`, in coefficient form. -/
def PSDon {ν : Type u} (G : Matrix ν ν ℝ) (X : Finset ν) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (f : ι → ν), (∀ a, f a ∈ X) → ∀ x : ι → ℝ,
    0 ≤ ∑ a, ∑ b, x a * x b * G (f a) (f b) ∧
      (∑ a, ∑ b, x a * x b * G (f a) (f b) = 0 → ∑ a, x a • G.row (f a) = 0)

lemma sum_push {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (g : ι → α) (x : ι → ℝ)
    (w : α → ℝ) : ∑ e, (∑ a, if g a = e then x a else 0) * w e = ∑ a, x a * w (g a) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]; simp

lemma mulVec_push {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (g : ι → α) (x : ι → ℝ)
    (H : Matrix α α ℝ) (e : α) :
    (H *ᵥ fun e => ∑ a, if g a = e then x a else 0) e = ∑ b, H e (g b) * x b := by
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]; simp

section Hyp

variable {Sig G : Matrix n n ℝ} {q t : ℕ}

/-- The rows of `G` outside one variable still span (from `|Z| ≤ t ρ(Z)`). -/
lemma span_erase (hq : G.rank = q) (hcard : Fintype.card n = t * q)
    (h3 : ∀ Z : Finset n, Z.card ≤ t * frk ℝ G.row Z) (ht : 2 ≤ t) (i : n) :
    span ℝ (G.row '' ((univ.erase i : Finset n) : Set n)) =
      span ℝ (G.row '' ((univ : Finset n) : Set n)) ∧ frk ℝ G.row (univ.erase i) = q := by
  have hu : frk ℝ G.row univ = q := by rw [← rank_eq_frk_univ, hq]
  have hle := frk_mono (F := ℝ) G.row (subset_univ (univ.erase i))
  have hc : (univ.erase i).card = t * q - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, hcard]
  have h1 := h3 (univ.erase i)
  have hq0 : 1 ≤ q := by
    by_contra h0; push Not at h0
    have : q = 0 := by omega
    subst this
    have := Fintype.card_pos_iff.2 (⟨i⟩ : Nonempty n)
    omega
  have heq : frk ℝ G.row (univ.erase i) = q := by
    by_contra hne
    have hlt : frk ℝ G.row (univ.erase i) ≤ q - 1 := by omega
    have : t * frk ℝ G.row (univ.erase i) ≤ t * (q - 1) := Nat.mul_le_mul_left _ hlt
    have e : t * (q - 1) = t * q - t := by rw [Nat.mul_sub, mul_one]
    have : t * q ≥ t := Nat.le_mul_of_pos_right t (by omega)
    omega
  refine ⟨Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (by simp))) ?_, heq⟩
  change frk ℝ G.row (univ.erase i) = frk ℝ G.row univ
  rw [heq, hu]

/-- **The hyperplane of a variable.** For a fit `H` of `Σ` without `i`, the set `X` of
variables where `H` keeps the diagonal of `G` has rank `q - 1` and `t (q - 1)` elements, is
closed (no further row lies in its span), does not contain `i`, and `G` is positive definite on
the span of its rows. -/
theorem hyperplane (hGs : G.IsSymm) (hoffG : ∀ i j, i ≠ j → G i j = Sig i j)
    (hq : G.rank = q) (hcard : Fintype.card n = t * q)
    (h3 : ∀ Z : Finset n, Z.card ≤ t * frk ℝ G.row Z) (ht : 3 ≤ t) (hq2 : 2 ≤ q)
    (hnpsd : ¬ G.PosSemidef) (i : n)
    (H : Matrix (univ.erase i : Finset n) (univ.erase i : Finset n) ℝ)
    (hH : IsFit (q + t - 3) (subPattern Sig (univ.erase i)) H) :
    ∃ X : Finset n, i ∉ X ∧ frk ℝ G.row X = q - 1 ∧ X.card = t * (q - 1) ∧
      (∀ l, G.row l ∈ span ℝ (G.row '' (X : Set n)) → l ∈ X) ∧ PSDon G X := by
  classical
  obtain ⟨hHp, hHr, hHo, -⟩ := hH
  have hs : ∀ a b, G a b = G b a := fun a b => symm_apply hGs a b
  have hHoff : ∀ a b : (univ.erase i), a ≠ b → H a b = G a b := fun a b hab => by
    rw [hHo a b hab, hoffG a b (fun e => hab (Subtype.ext e))]; rfl
  set Xs : Finset (univ.erase i) := univ.filter (fun a => H a a = G a a) with hXs
  set X : Finset n := Xs.map (Function.Embedding.subtype _) with hX
  have hmemX : ∀ l, l ∈ X ↔ ∃ h : l ∈ (univ.erase i), H ⟨l, h⟩ ⟨l, h⟩ = G l l := by
    intro l; simp [hX, hXs]
  have hXE : ∀ l, l ∈ X → l ∈ (univ.erase i) := fun l hl => ((hmemX l).1 hl).1
  have hiX : i ∉ X := fun h => by simpa using hXE i h
  have hHG : ∀ a b : (univ.erase i), (a : n) ∈ X → (b : n) ∈ X → H a b = G a b := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab
      obtain ⟨h, e⟩ := (hmemX a).1 ha
      simpa using e
    · exact hHoff a b hab
  have hHG1 : ∀ (e : (univ.erase i)) (b : (univ.erase i)), (b : n) ∈ X → H e b = G e b := by
    intro e b hb
    by_cases heb : e = b
    · subst heb; exact hHG e e hb hb
    · exact hHoff e b heb
  obtain ⟨hspanE, hfrkE⟩ := span_erase hq hcard h3 (by omega) i
  have hu : frk ℝ G.row univ = q := by rw [← rank_eq_frk_univ, hq]
  -- a basis inside `(univ.erase i)` and the factorisation
  obtain ⟨I, hIE, hIc, hIs⟩ := exists_basis_subset (F := ℝ) G.row (univ.erase i)
  rw [hfrkE] at hIc
  have hIs' : span ℝ (G.row '' (I : Set n)) = span ℝ (G.row '' ((univ : Finset n) : Set n)) :=
    hIs.trans hspanE
  obtain ⟨C0, hC0⟩ := exists_coefMat G I hIs'
  set S := G.submatrix (fun b : I => (b : n)) (fun b : I => (b : n)) with hSdef
  have hfac := factor_of_coef hGs I C0 hC0
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hSv⟩ := (exists_mulVec_eq_zero_iff).2 h0
    have h1 := rank_le_card_sub_one S v hv hSv
    have h2 : G.rank ≤ S.rank := by
      rw [hfac]
      exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    rw [Fintype.card_coe, hIc] at h1
    omega
  -- (B1) rank of `X` at most `q - 1`
  have hB1 : frk ℝ G.row X ≤ q - 1 := by
    by_contra hcon
    have hge : q ≤ frk ℝ G.row X := by omega
    have hle := frk_mono (F := ℝ) G.row (subset_univ X)
    rw [hu] at hle
    have hspX : span ℝ (G.row '' (X : Set n)) = span ℝ (G.row '' ((univ : Finset n) : Set n)) :=
      Submodule.eq_of_le_of_finrank_eq (span_mono (Set.image_mono (by simp)))
        (by change frk ℝ G.row X = frk ℝ G.row univ; omega)
    obtain ⟨C, hC⟩ := exists_coefMat G X hspX
    have hf := factor_of_coef hGs X C hC
    set φ : X → (univ.erase i) := fun x => ⟨x, hXE x x.2⟩ with hφ
    have hM : G.submatrix (fun b : X => (b : n)) (fun b : X => (b : n)) = H.submatrix φ φ := by
      ext a b
      simp only [submatrix_apply, hφ]
      exact (hHG ⟨a, hXE a a.2⟩ ⟨b, hXE b b.2⟩ a.2 b.2).symm
    apply hnpsd
    rw [hf, hM]
    have := (hHp.submatrix φ).mul_mul_conjTranspose_same C
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  -- (B2) the rank inequality
  set U' : Matrix (univ.erase i) I ℝ := C0.submatrix (fun a : (univ.erase i) => (a : n)) id with hU'
  set d : (univ.erase i) → ℝ := fun a => H a a - G a a with hd
  have hGent : ∀ a b : n, G a b = (C0 * S * C0ᵀ) a b := fun a b => by
    conv_lhs => rw [hfac]
  have hHeq : U' * S * U'ᵀ + diagonal d = H := by
    ext a b
    have e1 : (U' * S * U'ᵀ) a b = G a b := by
      rw [hGent]; simp [U', Matrix.mul_apply]
    rw [Matrix.add_apply, e1]
    by_cases hab : a = b
    · subst hab; simp [hd]
    · rw [diagonal_apply_ne _ hab, add_zero, hHoff a b hab]
  have hrem := EvenComplementation.Paper.lemma2_remark_of_factor U' S (isUnit_iff_ne_zero.2 hdet) d
  rw [hHeq] at hrem
  have hsuppc : univ \ EvenComplementation.Paper.supp d = Xs := by
    ext a; simp [EvenComplementation.Paper.supp, hd, hXs, sub_eq_zero]
  rw [hsuppc] at hrem
  have himg : U'.row '' (Xs : Set (univ.erase i)) = C0.row '' (X : Set n) := by
    have e : U'.row = fun a : (univ.erase i : Finset n) => C0.row (a : n) := rfl
    rw [e, ← Set.image_image (g := C0.row) (f := Subtype.val)]
    congr 1
    simp [hX]
  have hr' : finrank ℝ (span ℝ (U'.row '' (Xs : Set (univ.erase i)))) = frk ℝ C0.row X := by
    rw [himg]; rfl
  rw [hr'] at hrem
  have hrr : frk ℝ G.row X ≤ frk ℝ C0.row X := frk_le_coef I C0 hC0 X
  have hcardI : Fintype.card I = q := by rw [Fintype.card_coe, hIc]
  rw [hcardI] at hrem
  have hcs : (EvenComplementation.Paper.supp d).card + Xs.card = t * q - 1 := by
    have := card_sdiff_add_card_eq_card (subset_univ (EvenComplementation.Paper.supp d))
    rw [hsuppc, card_univ, Fintype.card_coe, card_erase_of_mem (mem_univ _), card_univ,
      hcard] at this
    omega
  have hXc : X.card = Xs.card := by rw [hX, card_map]
  have hX3 := h3 X
  -- arithmetic
  set r := frk ℝ G.row X with hr
  set x := X.card with hx
  have hqt : 1 ≤ t * q := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hz1 : ((EvenComplementation.Paper.supp d).card : ℤ) = (t : ℤ) * q - 1 - x := by
    have : ((EvenComplementation.Paper.supp d).card : ℤ) + x = (t * q - 1 : ℕ) := by
      rw [hXc]; exact_mod_cast hcs
    rw [Nat.cast_sub hqt] at this; push_cast at this; linarith
  have hHr' : (H.rank : ℤ) ≤ q + t - 3 := by
    have : H.rank ≤ q + t - 3 := hHr
    have h' : ((q + t - 3 : ℕ) : ℤ) = q + t - 3 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← h']; exact_mod_cast this
  have hrr' : (r : ℤ) ≤ frk ℝ C0.row X := by exact_mod_cast hrr
  have hx3 : (x : ℤ) ≤ t * r := by exact_mod_cast hX3
  have hr1 : (r : ℤ) ≤ q - 1 := by have := hB1; omega
  have ht' : (3 : ℤ) ≤ t := by exact_mod_cast ht
  have hA : (x : ℤ) ≥ (t : ℤ) * q - 2 * q - t + 2 + 2 * r := by linarith
  have hrq : (r : ℤ) = q - 1 := by
    by_contra hne
    have hr2 : (r : ℤ) ≤ q - 2 := by omega
    have hp : 0 ≤ ((t : ℤ) - 2) * ((q : ℤ) - r - 2) := mul_nonneg (by linarith) (by linarith)
    have e : ((t : ℤ) - 2) * ((q : ℤ) - r - 2) = (t : ℤ) * q - t * r - 2 * q + 2 * r - 2 * t + 4 := by
      ring
    linarith
  have hxq : (x : ℤ) = t * (q - 1) := by
    rw [hrq] at hx3 hA
    have e : (t : ℤ) * (q - 1) = t * q - t := by ring
    linarith
  have hrN : r = q - 1 := by omega
  have hxN : x = t * (q - 1) := by
    have : ((t * (q - 1) : ℕ) : ℤ) = t * (q - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    omega
  refine ⟨X, hiX, hrN, hxN, ?_, ?_⟩
  · -- closure
    intro l hl
    set Y := univ.filter (fun l => G.row l ∈ span ℝ (G.row '' (X : Set n))) with hY
    have hXY : X ⊆ Y := fun y hy => by
      simp only [hY, mem_filter, mem_univ, true_and]; exact subset_span ⟨y, hy, rfl⟩
    have hspY : span ℝ (G.row '' (Y : Set n)) ≤ span ℝ (G.row '' (X : Set n)) := by
      rw [span_le]; rintro _ ⟨y, hy, rfl⟩
      simp only [hY, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy; exact hy
    have hfY : frk ℝ G.row Y ≤ q - 1 := (Submodule.finrank_mono hspY).trans hrN.le
    have hY3 := h3 Y
    have hYc : Y.card ≤ X.card := by
      rw [← hx, hxN]; exact hY3.trans (Nat.mul_le_mul_left _ hfY)
    have := eq_of_subset_of_card_le hXY hYc
    rw [this]; simp [hY, hl]
  · -- positive definiteness on the span
    intro ι _ f hf x
    set g : ι → (univ.erase i) := fun a => ⟨f a, hXE _ (hf a)⟩ with hg
    set v : (univ.erase i) → ℝ := fun e => ∑ a, if g a = e then x a else 0 with hv
    have hHv : ∀ e : (univ.erase i), (H *ᵥ v) e = ∑ b, G e (f b) * x b := by
      intro e
      rw [hv, mulVec_push]
      exact Finset.sum_congr rfl fun b _ => by rw [hHG1 e (g b) (hf b)]
    have hQ : v ⬝ᵥ H *ᵥ v = ∑ a, ∑ b, x a * x b * G (f a) (f b) := by
      rw [dotProduct, hv, sum_push g x (H *ᵥ v)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hHv, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hnn := hHp.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at hnn
    refine ⟨hQ ▸ hnn, fun h0 => ?_⟩
    have hzero : H *ᵥ v = 0 := by
      rw [← hQ] at h0
      have := (hHp.dotProduct_mulVec_zero_iff (x := v)).1 (by simpa using h0)
      exact this
    have hk : ∀ k : n, k ∈ (univ.erase i) → ∑ b, G k (f b) * x b = 0 := by
      intro k hk
      have := congrFun hzero ⟨k, hk⟩
      rw [hHv] at this; simpa using this
    have hall : ∀ k : n, ∑ b, G k (f b) * x b = 0 := by
      intro k
      by_cases hkE : k ∈ (univ.erase i)
      · exact hk k hkE
      · have hrow : ∀ j, G k j = ∑ y : I, C0 k y * G y j := fun j => by
          have := congrFun (hC0 k) j; simpa [Finset.sum_apply] using this
        simp_rw [hrow, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun y _ => ?_
        have := hk y (hIE y.2)
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, this, mul_zero]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hall k]
    refine Finset.sum_congr rfl fun a _ => ?_
    change x a * G (f a) k = G k (f a) * x a
    rw [hs (f a) k]; ring

end Hyp

end FreeDiagonal.StatisticalFactorAnalysis
