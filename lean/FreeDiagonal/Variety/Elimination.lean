import FreeDiagonal.Variety.Theorem4
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# `ClosedRho` from the closedness of the projection along `(ℙ¹)ⁿ`

`ProjClosed K` is the named hypothesis "the projection `K^σ × (ℙ¹)ⁿ → K^σ` maps Zariski-closed
sets to Zariski-closed sets" (the main theorem of elimination theory, true for `K` algebraically
closed; Lean/Mathlib does not have it for points). Concretely:

* the variables are `σ ⊕ (n × Bool)`: the affine coordinates `y_s`, and for each `i : n` the pair
  `(λ_i, μ_i) = (w (i, false), w (i, true))`;
* a closed subset of `K^σ × (ℙ¹)ⁿ` is the zero set of a family `F` of polynomials that are
  multihomogeneous in the `n` pairs: weighted homogeneous for the weight `pairWeight`, which
  gives the two variables of pair `i` the weight `e_i ∈ ℕⁿ` and the affine variables weight `0`;
* a point of `(ℙ¹)ⁿ` is given by representatives `(λ_i, μ_i) ≠ (0, 0)`; the zero set does not
  depend on the representatives, by multihomogeneity;
* the projection of the zero set is `{y | ∃ w, every pair nonzero, every f ∈ F vanishes at (y, w)}`,
  and `ProjClosed K` says that this set is Zariski closed.

`closed_closRank_le` proves, from `ProjClosed K` alone, that `{y : ρ(G(y)) ≤ k}` is closed for any
matrix `G` of polynomials, following the paper's proof of Lemma 3: the matrix `W` with row
`i` equal to `μ_i · (row i of G) − λ_i e_iᵀ` has rank `cost(G, d)`, `d_i = λ_i / μ_i`
(`∞` when `μ_i = 0`); by formula (2), `{ρ ≤ k}` is the projection of the set where the minors of
`W` of size `k + 1` vanish, and these minors are multihomogeneous. Hence `ClosedRho K` and
`ClosedRhoSym K`.
-/

open Matrix Finset MvPolynomial

universe u

namespace FreeDiagonal

variable {K : Type u} [Field K]

/-! ### The named hypothesis -/

/-- The weight making a polynomial multihomogeneous in the pairs `(λ_i, μ_i)`: both variables of
pair `i` have weight `e_i`, the affine variables weight `0`. -/
def pairWeight (σ n : Type) [DecidableEq n] : σ ⊕ (n × Bool) → (n → ℕ) :=
  Sum.elim 0 (fun ib => Pi.single ib.1 1)

variable (K) in
/-- **The named hypothesis `ProjClosed K`: the projection `K^σ × (ℙ¹)ⁿ → K^σ` is closed.**
For finite `σ`, `n` and every family `F` of polynomials in `y_s` (`s : σ`) and `λ_i = w (i, false)`,
`μ_i = w (i, true)` (`i : n`) that are multihomogeneous in the `n` pairs, the set of `y` for which
some point `((λ_i : μ_i))_i` of `(ℙ¹)ⁿ` makes every `f ∈ F` vanish is Zariski closed. This is the
main theorem of elimination theory for `(ℙ¹)ⁿ` (true for `K` algebraically closed). -/
def ProjClosed : Prop :=
  ∀ (σ n : Type) [Fintype σ] [Fintype n] [DecidableEq n]
    (F : Set (MvPolynomial (σ ⊕ (n × Bool)) K)),
    (∀ f ∈ F, ∃ D : n → ℕ, f.IsWeightedHomogeneous (pairWeight σ n) D) →
    IsZariskiClosed {y : σ → K | ∃ w : n × Bool → K, (∀ i, w (i, false) ≠ 0 ∨ w (i, true) ≠ 0) ∧
      ∀ f ∈ F, aeval (Sum.elim y w) f = 0}

/-! ### Rank and minors -/

/-- `rank M ≤ k` iff every `(k+1) × (k+1)` minor vanishes. -/
theorem rank_le_iff_minors {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (M : Matrix m l K) (k : ℕ) :
    M.rank ≤ k ↔ ∀ r : Fin (k + 1) → m, ∀ c : Fin (k + 1) → l, (M.submatrix r c).det = 0 := by
  constructor
  · intro h r c
    by_contra hdet
    have h1 := rank_of_det_ne_zero hdet
    have h2 := rank_submatrix_le M r c
    simp at h1; omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨R, C, hR, hC, hRC⟩ := exists_small_submatrix M (k + 1) hlt
    set N := M.submatrix (fun a : R => (a : m)) (fun b : C => (b : l))
    have hNR : N.rank ≤ R.card := by simpa using rank_le_card_height N
    have hNC : N.rank ≤ C.card := by simpa using rank_le_card_width N
    have eR : Fintype.card R = k + 1 := by simp; omega
    have eC : Fintype.card C = k + 1 := by simp; omega
    set fR := Fintype.equivFinOfCardEq eR
    set fC := Fintype.equivFinOfCardEq eC
    have hS : (N.submatrix fR.symm fC.symm).rank = N.rank := rank_submatrix N fR.symm fC.symm
    exact det_ne_zero_of_rank (N.submatrix fR.symm fC.symm) (by simp; omega)
      (h (fun i => (fR.symm i : m)) (fun j => (fC.symm j : l)))

/-! ### The matrix `W` -/

section W

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix `W`: row `i` is `μ_i · (row i of G) − λ_i e_iᵀ`. -/
def Wmat (G : Matrix n n K) (w : n × Bool → K) : Matrix n n K :=
  Matrix.of fun i j => w (i, true) * G i j - if i = j then w (i, false) else 0

open Classical in
/-- The dial setting of a point of `(ℙ¹)ⁿ`: `d_i = λ_i / μ_i`, and `∞` when `μ_i = 0`. -/
noncomputable def dialOf (w : n × Bool → K) : n → Option K :=
  fun i => if w (i, true) = 0 then none else some (w (i, false) / w (i, true))

/-- **`rank W = cost(G, d)`** (proof of Lemma 3). -/
theorem rank_Wmat (G : Matrix n n K) (w : n × Bool → K)
    (hw : ∀ i, w (i, false) ≠ 0 ∨ w (i, true) ≠ 0) :
    (Wmat G w).rank = (dialMat G (dialOf w)).rank := by
  classical
  set N : Finset n := univ.filter (fun i => w (i, true) = 0)
  have hN : ∀ i, i ∈ N ↔ w (i, true) = 0 := by simp [N]
  set s : n → K := fun i => if w (i, true) = 0 then -w (i, false) else w (i, true)
  have hs : ∀ i, s i ≠ 0 := by
    intro i; simp only [s]
    split_ifs with h
    · exact neg_ne_zero.2 ((hw i).resolve_right (not_not.2 h))
    · exact h
  let W' : Matrix n n K := Matrix.of fun i j =>
    if w (i, true) = 0 then (if i = j then 1 else 0)
    else G i j - if i = j then w (i, false) / w (i, true) else 0
  have hW : Wmat G w = diagonal s * W' := by
    ext i j
    rw [diagonal_mul]
    simp only [Wmat, W', s, of_apply]
    by_cases ht : w (i, true) = 0
    · simp only [ht, if_true, zero_mul, zero_sub]
      split_ifs <;> simp
    · simp only [ht, if_false]
      split_ifs with hij
      · field_simp
      · ring
  have hdet : IsUnit (diagonal s).det := by
    rw [det_diagonal]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => hs i))
  rw [hW, rank_mul_eq_right_of_isUnit_det _ _ hdet]
  rw [rank_unit_rows W' N (fun i hi j => by simp [W', (hN i).1 hi]),
    rank_unit_rows (dialMat G (dialOf w)) N
      (fun i hi j => dialMat_none_row (by simp [dialOf, (hN i).1 hi]) j)]
  congr 2
  ext a b
  have ha : w ((a : n), true) ≠ 0 := fun h => (mem_compl.1 a.2) ((hN a).2 h)
  have hb : w ((b : n), true) ≠ 0 := fun h => (mem_compl.1 b.2) ((hN b).2 h)
  have hda : dialOf w a = some (w ((a : n), false) / w ((a : n), true)) := by simp [dialOf, ha]
  have hdb : dialOf w b = some (w ((b : n), false) / w ((b : n), true)) := by simp [dialOf, hb]
  simp only [submatrix_apply, W', of_apply, ha, if_false, dialMat, hda, hdb]

/-- `ρ(G) ≤ k` iff some point of `(ℙ¹)ⁿ` gives `rank W ≤ k` (formula (2)). -/
theorem closRank_le_iff_exists_Wmat (G : Matrix n n K) (k : ℕ) :
    closRank G ≤ k ↔ ∃ w : n × Bool → K, (∀ i, w (i, false) ≠ 0 ∨ w (i, true) ≠ 0) ∧
      (Wmat G w).rank ≤ k := by
  have h2 := formula_2_global G G (fun _ _ _ => rfl)
  constructor
  · intro h
    have hmem : closRank G ∈ Set.range (fun d : n → Option K => (dialMat G d).rank) := by
      rw [h2]; exact Nat.sInf_mem (Set.range_nonempty _)
    obtain ⟨d, hd⟩ := hmem
    have hd' : (dialMat G d).rank = closRank G := hd
    let w : n × Bool → K := fun ib =>
      if ib.2 then (if d ib.1 = none then 0 else 1) else (d ib.1).getD 1
    have hwd : dialOf w = d := by
      funext i
      rcases hdi : d i with _ | t
      · simp [dialOf, w, hdi]
      · simp [dialOf, w, hdi]
    have hw : ∀ i, w (i, false) ≠ 0 ∨ w (i, true) ≠ 0 := by
      intro i
      rcases hdi : d i with _ | t
      · left; simp [w, hdi]
      · right; simp [w, hdi]
    refine ⟨w, hw, ?_⟩
    rw [rank_Wmat G w hw, hwd, hd']; exact h
  · rintro ⟨w, hw, hr⟩
    rw [h2]
    exact (ciInf_le (OrderBot.bddBelow _) (dialOf w)).trans (by rw [← rank_Wmat G w hw]; exact hr)

end W

/-! ### The main step: `{ρ ≤ k}` is closed -/

lemma isWeightedHomogeneous_rename_inl {σ n : Type} [DecidableEq n] (g : MvPolynomial σ K) :
    (rename (Sum.inl : σ → σ ⊕ (n × Bool)) g).IsWeightedHomogeneous (pairWeight σ n) 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact isWeightedHomogeneous_C _ a
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul, rename_X]
    have := hp.mul (isWeightedHomogeneous_X K (pairWeight σ n) (Sum.inl s))
    simpa [pairWeight] using this

/-- **`{y : ρ(G(y)) ≤ k}` is Zariski closed**, for any matrix `G` of polynomials, assuming only
`ProjClosed K`. -/
theorem closed_closRank_le (hP : ProjClosed K) {σ n : Type} [Fintype σ] [Fintype n]
    [DecidableEq n] (Gp : Matrix n n (MvPolynomial σ K)) (k : ℕ) :
    IsZariskiClosed {y : σ → K | closRank (Gp.map (aeval y)) ≤ k} := by
  classical
  set wt := pairWeight σ n
  let Wp : Matrix n n (MvPolynomial (σ ⊕ (n × Bool)) K) := Matrix.of fun i j =>
    X (Sum.inr (i, true)) * rename Sum.inl (Gp i j) - if i = j then X (Sum.inr (i, false)) else 0
  let F : Set (MvPolynomial (σ ⊕ (n × Bool)) K) :=
    Set.range (fun rc : (Fin (k + 1) → n) × (Fin (k + 1) → n) => (Wp.submatrix rc.1 rc.2).det)
  -- every entry of row `i` of `W` has multidegree `e_i`
  have hWp : ∀ i j, (Wp i j).IsWeightedHomogeneous wt (Pi.single i 1) := by
    intro i j
    have hX : ∀ b, (X (Sum.inr (i, b)) : MvPolynomial (σ ⊕ (n × Bool)) K).IsWeightedHomogeneous
        wt (Pi.single i 1) := fun b => by
      have := isWeightedHomogeneous_X K wt (Sum.inr (i, b)); simpa [wt, pairWeight] using this
    have h1 := (hX true).mul (isWeightedHomogeneous_rename_inl (n := n) (Gp i j))
    rw [add_zero] at h1
    simp only [Wp, of_apply]
    split_ifs
    · exact h1.sub (hX false)
    · rw [sub_zero]; exact h1
  have hF : ∀ f ∈ F, ∃ D : n → ℕ, f.IsWeightedHomogeneous wt D := by
    rintro _ ⟨⟨r, c⟩, rfl⟩
    refine ⟨∑ a, Pi.single (r a) 1, ?_⟩
    show IsWeightedHomogeneous wt (Wp.submatrix r c).det _
    rw [det_apply]
    refine IsWeightedHomogeneous.sum _ _ _ (fun τ _ => ?_)
    rw [Units.smul_def]
    have hprod : (∏ a, Wp.submatrix r c (τ a) a) ∈
        weightedHomogeneousSubmodule K wt (∑ a, Pi.single (r a) 1) := by
      rw [mem_weightedHomogeneousSubmodule]
      have := IsWeightedHomogeneous.prod univ (fun a => Wp.submatrix r c (τ a) a)
        (fun a => Pi.single (r (τ a)) 1) (fun a _ => hWp _ _)
      rwa [Equiv.sum_comp τ (fun a => (Pi.single (r a) 1 : n → ℕ))] at this
    exact zsmul_mem hprod _
  convert hP σ n F hF using 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [closRank_le_iff_exists_Wmat]
  refine exists_congr (fun w => and_congr_right (fun _ => ?_))
  rw [rank_le_iff_minors, Set.forall_mem_range, Prod.forall]
  refine forall_congr' (fun r => forall_congr' (fun c => ?_))
  rw [AlgHom.map_det]
  apply Eq.congr_left
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, map_apply, submatrix_apply, Wp, Wmat, of_apply, map_sub,
    map_mul, aeval_X, Sum.elim_inr, aeval_rename, Sum.elim_comp_inl]
  split_ifs <;> simp

/-! ### `ClosedRho` and `ClosedRhoSym` -/

/-- **`ProjClosed K` implies `ClosedRho K`.** -/
theorem closedRho_of_projClosed (hP : ProjClosed K) : ClosedRho.{u, 0} K := by
  intro n _ _ k
  let Gp : Matrix n n (MvPolynomial (OffIdx n) K) :=
    Matrix.of fun i j => if h : i = j then 0 else X ⟨(i, j), h⟩
  have e : ∀ p : OffIdx n → K, Gp.map (aeval p) = toMat p := by
    intro p; ext i j
    by_cases h : i = j
    · subst h; simp [Gp, toMat_apply_self]
    · simp [Gp, h, toMat_apply_ne _ h]
  have hs : {p : OffIdx n → K | closRank (toMat p) ≤ k} =
      {y | closRank (Gp.map (aeval y)) ≤ k} := by
    ext p; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, e]
  rw [hs]; exact closed_closRank_le hP Gp k

/-- **`ProjClosed K` implies `ClosedRhoSym K`.** -/
theorem closedRhoSym_of_projClosed (hP : ProjClosed K) : ClosedRhoSym.{u, 0} K := by
  intro n _ _ k
  let Gp : Matrix n n (MvPolynomial (SymIdx n) K) :=
    Matrix.of fun i j => if h : i < j then X ⟨(i, j), h⟩ else
      if h' : j < i then X ⟨(j, i), h'⟩ else 0
  have e : ∀ p : SymIdx n → K, Gp.map (aeval p) = toMatSym p := by
    intro p; ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [Gp, h, toMatSym_apply_lt _ h]
    · subst h; simp [Gp, toMatSym_apply_self]
    · simp [Gp, h, not_lt_of_gt h, toMatSym_apply_gt _ h]
  have hs : {p : SymIdx n → K | closRank (toMatSym p) ≤ k} =
      {y | closRank (Gp.map (aeval y)) ≤ k} := by
    ext p; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, e]
  rw [hs]; exact closed_closRank_le hP Gp k

end FreeDiagonal
