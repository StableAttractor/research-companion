import FreeDiagonal.StatisticalFactorAnalysis.ReplicatedFit
import FreeDiagonal.EvenComplementation.Paper

/-!
# Lemma 3, last assertion: if `t ≥ 3` and every proper principal submatrix is in the model,
then condition (1) holds

Route (the printed one, with Lemma 2 of the even-complementation paper doing the Schur
complement count): for a fit `H` of `Σ` without `i₀ = (j, a₀)`, let `X` be the variables where
`H` and the replicated matrix `G` (diagonal `s_j`) agree. The rank formula's remark
(`EvenComplementation.Paper.lemma2_remark_of_factor`, any field) gives
`|E'| - |X| ≤ rank H + q - 2r`, `r` the number of groups meeting `X`; `r ≤ q - 1` because
otherwise `S0` would be a principal submatrix of `H`; counting then forces `X` to be the
union of the groups other than `j`. Gram vectors of `H` and the vector `p` of the Schur
complement give `diag(H_ii - s_j) - g_j J ⪰ 0` on the rest of group `j`, whence (1).
-/

open Matrix Module Submodule Finset

set_option linter.unusedSectionVars false

namespace FreeDiagonal.StatisticalFactorAnalysis

open FreeDiagonal

variable {q t : ℕ}

/-- Abbreviation: all variables except `(j, a₀)`. -/
abbrev Ers (j : Fin q) (a0 : Fin t) : Finset (Fin q × Fin t) := univ.erase (j, a0)

lemma card_Ers (j : Fin q) (a0 : Fin t) : (Ers j a0).card = q * t - 1 := by
  rw [Ers, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]

/-- In a fit of `Σ` without `(j, a₀)`, every variable outside group `j` keeps the replicated
diagonal entry `s_k`. -/
lemma converse_X {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0)
    (ht : 3 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (j : Fin q) (a0 : Fin t) (H : Matrix (Ers j a0) (Ers j a0) ℝ)
    (hH : IsFit (q + t - 3) (subPattern Sig (Ers j a0)) H) :
    ∀ i : Ers j a0, i.1.1 ≠ j → H i i = S0 i.1.1 i.1.1 := by
  classical
  obtain ⟨hHp, hHr, hHo, -⟩ := hH
  set U : Matrix (Ers j a0) (Fin q) ℝ := Matrix.of fun i k => if i.1.1 = k then 1 else 0
    with hU
  set d : Ers j a0 → ℝ := fun i => H i i - S0 i.1.1 i.1.1 with hd
  have hUS : U * S0 * Uᵀ = Matrix.of fun i l : Ers j a0 => S0 i.1.1 l.1.1 := by
    ext i l
    simp [hU, Matrix.mul_apply, ite_mul, Finset.sum_ite_eq]
  have hHeq : U * S0 * Uᵀ + diagonal d = H := by
    rw [hUS]
    ext i l
    by_cases h : i = l
    · subst h; simp [hd]
    · have h' : (i : Fin q × Fin t) ≠ l := fun e => h (Subtype.ext e)
      rw [hHo i l h]
      simp [diagonal_apply_ne _ h, subPattern, hSig.2 _ _ h']
  have hrem := EvenComplementation.Paper.lemma2_remark_of_factor U S0
    (isUnit_iff_ne_zero.2 hS0.det_ne) d
  rw [hHeq] at hrem
  set X := univ \ EvenComplementation.Paper.supp d with hX
  have hmemX : ∀ i, i ∈ X ↔ H i i = S0 i.1.1 i.1.1 := by
    intro i
    simp [hX, EvenComplementation.Paper.supp, hd, sub_eq_zero]
  set Gx := X.image (fun i : Ers j a0 => i.1.1) with hGx
  have hrowe : U.row = fun i => (Pi.single i.1.1 (1 : ℝ) : Fin q → ℝ) := by
    funext i; ext k; simp [hU, Pi.single_apply, eq_comm]
  have hr : finrank ℝ (span ℝ (U.row '' (X : Set (Ers j a0)))) = Gx.card := by
    have hli : LinearIndependent ℝ (fun k : Gx => (Pi.single k.1 (1 : ℝ) : Fin q → ℝ)) := by
      have := (Pi.basisFun ℝ (Fin q)).linearIndependent.comp (fun k : Gx => k.1)
        Subtype.val_injective
      convert this using 1
      funext k; simp
    have h1 := finrank_span_eq_card hli
    rw [Fintype.card_coe] at h1
    have hset : U.row '' (X : Set (Ers j a0)) =
        Set.range (fun k : Gx => (Pi.single k.1 (1 : ℝ) : Fin q → ℝ)) := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i.1.1, mem_image_of_mem _ hi⟩, by rw [hrowe]⟩
      · rintro ⟨⟨k, hk⟩, rfl⟩
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
        exact ⟨i, hi, by rw [hrowe]⟩
    rw [hset, h1]
  rw [hr] at hrem
  set c := Fintype.card (Ers j a0) with hc
  have hcardX : X.card + (EvenComplementation.Paper.supp d).card = c := by
    have := card_sdiff_add_card_eq_card (subset_univ (EvenComplementation.Paper.supp d))
    rwa [card_univ, ← hX] at this
  -- `X` does not meet every group
  have hGne : Gx ≠ univ := by
    intro hG
    have hex : ∀ k : Fin q, ∃ i ∈ X, i.1.1 = k := by
      intro k
      have : k ∈ Gx := hG ▸ mem_univ k
      obtain ⟨i, hi, hik⟩ := mem_image.1 this
      exact ⟨i, hi, hik⟩
    choose rep hrepX hrepk using hex
    have hrepi : Function.Injective rep := fun k l h => by
      rw [← hrepk k, ← hrepk l, h]
    have e : H.submatrix rep rep = S0 := by
      ext k l
      simp only [submatrix_apply]
      by_cases hkl : k = l
      · subst hkl; rw [(hmemX _).1 (hrepX k), hrepk]
      · have hne : rep k ≠ rep l := hrepi.ne hkl
        have hne' : ((rep k : Ers j a0) : Fin q × Fin t) ≠ rep l := fun e => hne (Subtype.ext e)
        rw [hHo _ _ hne]
        simp only [subPattern, submatrix_apply]
        rw [hSig.2 _ _ hne', hrepk, hrepk]
    exact hS0.not_psd (e ▸ hHp.submatrix rep)
  have hGle : Gx.card ≤ q - 1 := by
    have := (Finset.card_lt_iff_ne_univ Gx).2 hGne
    rw [Fintype.card_fin] at this; omega
  -- counting `X` inside the groups it meets
  set R := (Gx ×ˢ (univ : Finset (Fin t))).erase (j, a0) with hR
  have hXR : X.map (Function.Embedding.subtype _) ⊆ R := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
    refine mem_erase.2 ⟨(mem_erase.1 i.2).1, mem_product.2 ⟨mem_image_of_mem _ hi, mem_univ _⟩⟩
  have hRcard : R.card + (if j ∈ Gx then 1 else 0) = Gx.card * t := by
    split_ifs with hj
    · rw [hR, card_erase_of_mem (mem_product.2 ⟨hj, mem_univ _⟩), card_product, card_univ,
        Fintype.card_fin]
      have : 0 < Gx.card * t := Nat.mul_pos (card_pos.2 ⟨j, hj⟩) (by omega)
      omega
    · rw [hR, erase_eq_of_notMem (fun h => hj (mem_product.1 h).1), card_product, card_univ,
        Fintype.card_fin, add_zero]
  have hXle : X.card ≤ R.card := by
    have := card_le_card hXR; rwa [card_map] at this
  -- arithmetic
  have hq1 : 1 ≤ q := by
    by_contra h; push Not at h
    have : q = 0 := by omega
    subst this; exact Fin.elim0 j
  have hqt : 1 ≤ q * t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hc' : (c : ℤ) = (q : ℤ) * t - 1 := by
    rw [hc, Fintype.card_coe, card_Ers, Nat.cast_sub hqt]; push_cast; ring
  set g := Gx.card with hgdef
  set e := if j ∈ Gx then 1 else 0 with he
  have hfin : g = q - 1 ∧ e = 0 ∧ X.card = R.card := by
    have h0 : (0 : ℤ) ≤ e := by simp only [he]; split_ifs <;> simp
    rw [Fintype.card_fin] at hrem
    have A2 : ((q + t - 3 : ℕ) : ℤ) = (q : ℤ) + t - 3 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hrk' : (H.rank : ℤ) ≤ (q : ℤ) + t - 3 := by rw [← A2]; exact_mod_cast hHr
    have hXle' : (X.card : ℤ) ≤ R.card := by exact_mod_cast hXle
    have hR' : (R.card : ℤ) + e = (g : ℤ) * t := by exact_mod_cast hRcard
    have hg' : (g : ℤ) ≤ q - 1 := by
      have : (g : ℤ) ≤ ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hGle
      rwa [Nat.cast_sub hq1, Nat.cast_one] at this
    have hS : ((EvenComplementation.Paper.supp d).card : ℤ) = c - X.card := by omega
    rw [hS, hc'] at hrem
    have ht3 : (3 : ℤ) ≤ t := by exact_mod_cast ht
    have hprod : (0 : ℤ) ≤ ((t : ℤ) - 2) * ((q : ℤ) - 1 - g) :=
      mul_nonneg (by linarith) (by linarith)
    have hpe : ((t : ℤ) - 2) * ((g : ℤ) - (q - 1)) = 0 := by
      have : (e : ℤ) ≤ ((t : ℤ) - 2) * ((g : ℤ) - (q - 1)) := by ring_nf; ring_nf at hR' hrem; linarith
      have h2 : ((t : ℤ) - 2) * ((g : ℤ) - (q - 1)) ≤ 0 := by ring_nf; ring_nf at hprod; linarith
      linarith
    have hgeq : (g : ℤ) = q - 1 := by
      rcases mul_eq_zero.1 hpe with h | h
      · linarith
      · linarith
    have heq : (e : ℤ) = 0 := by
      have : (e : ℤ) ≤ ((t : ℤ) - 2) * ((g : ℤ) - (q - 1)) := by ring_nf; ring_nf at hR' hrem; linarith
      rw [hpe] at this; linarith
    have hgt : (g : ℤ) * t = ((q : ℤ) - 1) * t := by rw [hgeq]
    refine ⟨by omega, by exact_mod_cast heq, ?_⟩
    have : (X.card : ℤ) = R.card := by
      apply le_antisymm hXle'
      ring_nf at hgt hR' hrem; linarith
    exact_mod_cast this
  obtain ⟨hg, he0, hXRc⟩ := hfin
  have hjG : j ∉ Gx := by
    intro hj; simp [he, hj] at he0
  have hGx : Gx = univ.erase j := by
    refine eq_of_subset_of_card_le (fun k hk => mem_erase.2 ⟨fun e => hjG (e ▸ hk), mem_univ _⟩) ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  have hXRe : X.map (Function.Embedding.subtype _) = R :=
    eq_of_subset_of_card_le hXR (by rw [card_map]; omega)
  intro i hi
  rw [← hmemX]
  have : (i : Fin q × Fin t) ∈ R := by
    refine mem_erase.2 ⟨(mem_erase.1 i.2).1, mem_product.2 ⟨?_, mem_univ _⟩⟩
    rw [hGx]; exact mem_erase.2 ⟨hi, mem_univ _⟩
  rw [← hXRe] at this
  obtain ⟨i', hi', hii'⟩ := mem_map.1 this
  have : i' = i := Subtype.ext hii'
  rwa [← this]

/-- The Schur complement step: in a fit of `Σ` without `(j, a₀)`, the other variables of
group `j` satisfy `c_i > s_j` and `g_j Σ 1/(c_i - s_j) < 1`. -/
lemma converse_group {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    (ht : 3 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (j : Fin q) (a0 : Fin t) (H : Matrix (Ers j a0) (Ers j a0) ℝ)
    (hH : IsFit (q + t - 3) (subPattern Sig (Ers j a0)) H) :
    (∀ a, a ≠ a0 → S0 j j < Sig (j, a) (j, a)) ∧
      schurG S0 j * ∑ a ∈ univ.erase a0, 1 / (Sig (j, a) (j, a) - S0 j j) < 1 := by
  classical
  have hX := converse_X hS0 ht hSig j a0 H hH
  obtain ⟨hHp, -, hHo, hHd⟩ := hH
  obtain ⟨K, h, hh⟩ := exists_gram_of_posSemidef hHp
  have hinner : ∀ x y, inner ℝ (h x) (h y) = H x y := fun x y => by
    rw [← gram_apply (𝕜 := ℝ), hh]
  set g := schurG S0 j with hgdef
  have hg : 0 < g := (lemma3_pos hS0 hq j).2
  set s := S0 j j
  -- the variables of group `j` and representatives of the other groups
  let ja : {a : Fin t // a ≠ a0} → Ers j a0 := fun a =>
    ⟨(j, a.1), mem_erase.2 ⟨fun e => a.2 (congrArg Prod.snd e), mem_univ _⟩⟩
  let rep : {k : Fin q // k ≠ j} → Ers j a0 := fun k =>
    ⟨(k.1, a0), mem_erase.2 ⟨fun e => k.2 (congrArg Prod.fst e), mem_univ _⟩⟩
  set Sj := offPrinc S0 j
  set r := offRow S0 j
  set c := Sj⁻¹ *ᵥ r with hc
  have hSc : Sj *ᵥ c = r := by
    rw [hc, mulVec_mulVec, mul_nonsing_inv _ (((hS0.princ j).isUnit).map Matrix.detMonoidHom),
      one_mulVec]
  set w : {k : Fin q // k ≠ j} → EuclideanSpace ℝ (Fin K) := fun k => h (rep k)
  have hww : ∀ k l, inner ℝ (w k) (w l) = Sj k l := by
    intro k l
    simp only [w, hinner]
    by_cases hkl : k = l
    · subst hkl
      have := hX (rep k) k.2
      simp only [rep] at this ⊢
      rw [this]; rfl
    · have hne : rep k ≠ rep l := fun e => hkl (Subtype.ext (congrArg (fun x => x.1.1) e))
      have hne' : ((rep k : Ers j a0) : Fin q × Fin t) ≠ rep l := fun e => hne (Subtype.ext e)
      rw [hHo _ _ hne]
      simp only [subPattern, submatrix_apply]
      rw [hSig.2 _ _ hne']; rfl
  have hhw : ∀ a k, inner ℝ (h (ja a)) (w k) = r k := by
    intro a k
    simp only [w, hinner]
    have hne : ja a ≠ rep k := fun e => k.2 (congrArg (fun x => x.1.1) e).symm
    have hne' : ((ja a : Ers j a0) : Fin q × Fin t) ≠ rep k := fun e => hne (Subtype.ext e)
    rw [hHo _ _ hne]
    simp only [subPattern, submatrix_apply]
    rw [hSig.2 _ _ hne']; rfl
  set p := ∑ k, c k • w k with hp
  have hwp : ∀ k, inner ℝ (w k) p = r k := by
    intro k
    rw [hp, inner_sum]
    have := congrFun hSc k
    simp only [mulVec, dotProduct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_right, hww, mul_comm]
  have hhp : ∀ a, inner ℝ (h (ja a)) p = s + g := by
    intro a
    rw [hp, inner_sum]
    simp only [real_inner_smul_right, hhw]
    rw [hgdef, schurG, dotProduct]
    have : ∑ k, c k * r k = ∑ k, r k * c k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]; ring
  have hpp : inner ℝ p p = s + g := by
    have e1 : inner ℝ p p = inner ℝ (∑ k, c k • w k) p := congrArg (fun x => inner ℝ x p) hp
    rw [e1, sum_inner]
    simp only [real_inner_smul_left, hwp]
    rw [hgdef, schurG, dotProduct]
    have : ∑ k, c k * r k = ∑ k, r k * c k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]; ring
  -- the Gram matrix of `h_i - p` on the rest of group `j`
  have hHjj : ∀ a b : {a : Fin t // a ≠ a0}, a ≠ b → H (ja a) (ja b) = s := by
    intro a b hab
    have hne : ja a ≠ ja b := fun e => hab (Subtype.ext (congrArg (fun x => x.1.2) e))
    have hne' : ((ja a : Ers j a0) : Fin q × Fin t) ≠ ja b := fun e => hne (Subtype.ext e)
    rw [hHo _ _ hne]
    simp only [subPattern, submatrix_apply]
    rw [hSig.2 _ _ hne']
  have key : ∀ v : {a : Fin t // a ≠ a0} → ℝ,
      0 ≤ ∑ a, v a ^ 2 * (H (ja a) (ja a) - s) - g * (∑ a, v a) ^ 2 := by
    intro v
    have h0 := real_inner_self_nonneg (x := ∑ a, v a • (h (ja a) - p))
    have e : inner ℝ (∑ a, v a • (h (ja a) - p)) (∑ a, v a • (h (ja a) - p)) =
        ∑ a, ∑ b, v a * v b * ((if a = b then H (ja a) (ja a) - s else 0) - g) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_right]
      have : inner ℝ (h (ja a) - p) (h (ja b) - p) =
          (if a = b then H (ja a) (ja a) - s else 0) - g := by
        simp only [inner_sub_left, inner_sub_right, hinner, hhp, hpp]
        rw [real_inner_comm, hhp]
        by_cases hab : a = b
        · subst hab; simp; ring
        · rw [hHjj a b hab]; simp [hab]
      rw [this]; ring
    rw [e] at h0
    have e2 : ∑ a, ∑ b, v a * v b * ((if a = b then H (ja a) (ja a) - s else 0) - g) =
        ∑ a, v a ^ 2 * (H (ja a) (ja a) - s) - g * (∑ a, v a) ^ 2 := by
      have s1 : ∑ a, ∑ b, v a * v b * ((if a = b then H (ja a) (ja a) - s else 0) - g) =
          ∑ a, ∑ b, (if a = b then v a * v b * (H (ja a) (ja a) - s) else 0) -
            ∑ a, ∑ b, g * (v a * v b) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring
      have s2 : ∑ a, ∑ b, g * (v a * v b) = g * (∑ a, v a) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
      rw [s1, s2]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      congr 1
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [e2] at h0; exact h0
  have hdiag1 : ∀ a : {a : Fin t // a ≠ a0}, s + g ≤ H (ja a) (ja a) := by
    intro a
    have := key (Pi.single a 1)
    have h1 : ∑ b, (Pi.single a (1 : ℝ) : {a : Fin t // a ≠ a0} → ℝ) b ^ 2 *
        (H (ja b) (ja b) - s) = H (ja a) (ja a) - s := by
      rw [Fintype.sum_eq_single a]
      · simp
      · intro b hb; simp [hb]
    have h2 : ∑ b, (Pi.single a (1 : ℝ) : {a : Fin t // a ≠ a0} → ℝ) b = 1 := by
      rw [Fintype.sum_eq_single a]
      · simp
      · intro b hb; simp [hb]
    rw [h1, h2] at this; linarith
  have hlt : ∀ a : {a : Fin t // a ≠ a0}, H (ja a) (ja a) < Sig (j, a.1) (j, a.1) := fun a => hHd _
  refine ⟨fun a ha => ?_, ?_⟩
  · have := hdiag1 ⟨a, ha⟩; have := hlt ⟨a, ha⟩; linarith
  · set D : {a : Fin t // a ≠ a0} → ℝ := fun a => Sig (j, a.1) (j, a.1) - s
    have hD : ∀ a, 0 < D a := fun a => by
      have := hdiag1 a; have := hlt a; simp only [D]; linarith
    rw [Finset.sum_subtype (univ.erase a0) (p := fun a => a ≠ a0) (by simp)]
    set σ := ∑ a, 1 / D a with hσ
    obtain ⟨a1, ha1⟩ := exists_ne_fin (by omega : 2 ≤ t) a0
    have hσpos : 0 < σ := Finset.sum_pos (fun a _ => one_div_pos.2 (hD a))
      ⟨⟨a1, ha1⟩, mem_univ _⟩
    have hk := key (fun a => 1 / D a)
    have hstrict : ∑ a, (1 / D a) ^ 2 * (H (ja a) (ja a) - s) < σ := by
      rw [hσ]
      refine Finset.sum_lt_sum (fun a _ => ?_) ⟨⟨a1, ha1⟩, mem_univ _, ?_⟩
      · have h1 : H (ja a) (ja a) - s ≤ D a := by have := hlt a; simp only [D]; linarith
        calc (1 / D a) ^ 2 * (H (ja a) (ja a) - s) ≤ (1 / D a) ^ 2 * D a :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = 1 / D a := by field_simp [(hD a).ne']
      · have h1 : H (ja ⟨a1, ha1⟩) (ja ⟨a1, ha1⟩) - s < D ⟨a1, ha1⟩ := by
          have := hlt ⟨a1, ha1⟩; simp only [D]; linarith
        calc (1 / D ⟨a1, ha1⟩) ^ 2 * (H (ja ⟨a1, ha1⟩) (ja ⟨a1, ha1⟩) - s)
            < (1 / D ⟨a1, ha1⟩) ^ 2 * D ⟨a1, ha1⟩ :=
              mul_lt_mul_of_pos_left h1 (by have := hD ⟨a1, ha1⟩; positivity)
          _ = 1 / D ⟨a1, ha1⟩ := by field_simp [(hD _).ne']
    have : g * σ ^ 2 < σ := by linarith
    have : g * σ < 1 := by nlinarith
    exact this

/-- **Lemma 3, last assertion.** If `t ≥ 3` and every proper principal submatrix of `Σ` is in the
`m`-factor model (`m = q + t - 3`), then condition (1) holds. -/
theorem lemma3_converse {S0 : Matrix (Fin q) (Fin q) ℝ} (hS0 : IsLemma3Matrix S0) (hq : 2 ≤ q)
    (ht : 3 ≤ t) {Sig : Matrix (Fin q × Fin t) (Fin q × Fin t) ℝ} (hSig : IsReplicated S0 Sig)
    (h : ∀ T : Finset (Fin q × Fin t), T ≠ univ → InModel (q + t - 3) (subPattern Sig T)) :
    Cond1 S0 Sig := by
  have fit : ∀ j a0, ∃ H, IsFit (q + t - 3) (subPattern Sig (Ers j a0)) H := by
    intro j a0
    have hne : Ers j a0 ≠ univ := fun e => by
      have : (j, a0) ∈ Ers j a0 := by rw [e]; exact mem_univ _
      simp [Ers] at this
    exact (inModel_iff_exists_fit _ _).1 (h _ hne)
  intro j
  refine ⟨fun a => ?_, fun a0 => ?_⟩
  · obtain ⟨a0, ha0⟩ := exists_ne_fin (by omega : 2 ≤ t) a
    obtain ⟨H, hH⟩ := fit j a0
    exact (converse_group hS0 hq ht hSig j a0 H hH).1 a (Ne.symm ha0)
  · obtain ⟨H, hH⟩ := fit j a0
    exact (converse_group hS0 hq ht hSig j a0 H hH).2

end FreeDiagonal.StatisticalFactorAnalysis
