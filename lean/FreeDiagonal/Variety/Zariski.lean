import FreeDiagonal.Variety.Section5
import Mathlib.RingTheory.Nullstellensatz

/-!
# Coordinates, Zariski closure, and the varieties `D_{n,k}`, `X_{n,k}`

Points of an affine space `K^σ` are functions `σ → K`. The Zariski closure of a set `S` is
`zeroLocus (vanishingIdeal S)` (Mathlib, `Mathlib/RingTheory/Nullstellensatz.lean`).

* A pattern on a finite index type `n` has one coordinate per ordered pair `(i, j)` with `i ≠ j`
  (`OffIdx n`); `toMat p` is the matrix with these entries and zero diagonal.
* A symmetric pattern has one coordinate per pair `i < j` (`SymIdx n`, for a linear order on
  `n`); `toMatSym p` is the symmetric matrix with zero diagonal.
* `Dvar n k` is the closure of `{x : c(x) ≤ k}`; `Xvar n k` the closure of the symmetric patterns
  with `c(x) ≤ k`, in the space of symmetric patterns.
* `mem_zariskiClosure_of_line`: over an infinite field, if `x + t y ∈ S` for every `t ≠ 0`, then
  `x` lies in the closure of `S`.
-/

open Matrix Finset MvPolynomial

namespace FreeDiagonal

variable {K : Type*} [Field K]

/-- The Zariski closure of a set of points of `K^σ`. -/
def zariskiClosure {σ : Type*} (S : Set (σ → K)) : Set (σ → K) :=
  zeroLocus K (vanishingIdeal K S)

lemma subset_zariskiClosure {σ : Type*} (S : Set (σ → K)) : S ⊆ zariskiClosure S :=
  zeroLocus_vanishingIdeal_le S

/-- **A line through `x` whose other points lie in `S`** puts `x` in the closure of `S`
(`K` infinite). -/
theorem mem_zariskiClosure_of_line [Infinite K] {σ : Type*} (S : Set (σ → K)) (x y : σ → K)
    (h : ∀ t : K, t ≠ 0 → x + t • y ∈ S) : x ∈ zariskiClosure S := by
  rw [zariskiClosure, mem_zeroLocus_iff]
  intro f hf
  rw [mem_vanishingIdeal_iff] at hf
  set P : Polynomial K :=
    MvPolynomial.aeval (fun s => Polynomial.C (x s) + Polynomial.C (y s) * Polynomial.X) f
  have hev : ∀ (g : MvPolynomial σ K) (t : K),
      (MvPolynomial.aeval (fun s => Polynomial.C (x s) + Polynomial.C (y s) * Polynomial.X) g).eval t
        = MvPolynomial.aeval (x + t • y) g := by
    intro g t
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p s hp =>
      simp only [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hp, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hroots : {t : K | t ≠ 0} ⊆ {t | Polynomial.IsRoot P t} := by
    intro t ht
    show P.eval t = 0
    rw [hev f t]; exact hf _ (h t ht)
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P
    (Set.Infinite.mono hroots (Set.finite_singleton (0 : K)).infinite_compl)
  have := hev f 0
  simp only [zero_smul, add_zero] at this
  rw [← this]
  change P.eval 0 = 0
  rw [hP]; simp

/-! ### Rank of a sum -/

lemma rank_add_le' {m l : Type*} [Fintype l] [Fintype m] (A B : Matrix m l K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

lemma rank_sum_le {m l ι : Type*} [Fintype l] [Fintype m] (s : Finset ι)
    (A : ι → Matrix m l K) : (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (by omega)

/-! ### Coordinates for patterns -/

/-- One coordinate per ordered pair of distinct indices. -/
abbrev OffIdx (n : Type*) := {p : n × n // p.1 ≠ p.2}

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The pattern with coordinates `p`, as a matrix with zero diagonal. -/
def toMat (p : OffIdx n → K) : Matrix n n K :=
  fun i j => if h : i = j then 0 else p ⟨(i, j), h⟩

lemma toMat_apply_ne (p : OffIdx n → K) {i j : n} (h : i ≠ j) : toMat p i j = p ⟨(i, j), h⟩ := by
  simp [toMat, h]

lemma toMat_apply_self (p : OffIdx n → K) (i : n) : toMat p i i = 0 := by simp [toMat]

variable (n) in
/-- `D_{n,k}`: the Zariski closure of the patterns with `c(x) ≤ k`. -/
def Dvar (k : ℕ) : Set (OffIdx n → K) :=
  zariskiClosure {p | minCompRank (toMat p) ≤ k}

end General

/-- One coordinate per pair `i < j`. -/
abbrev SymIdx (n : Type*) [LinearOrder n] := {p : n × n // p.1 < p.2}

section Symmetric

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The symmetric pattern with coordinates `p`, as a symmetric matrix with zero diagonal. -/
def toMatSym (p : SymIdx n → K) : Matrix n n K :=
  fun i j => if h : i < j then p ⟨(i, j), h⟩ else if h' : j < i then p ⟨(j, i), h'⟩ else 0

lemma toMatSym_symm (p : SymIdx n → K) (i j : n) : toMatSym p i j = toMatSym p j i := by
  unfold toMatSym
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt_of_gt h]
  · subst h; simp
  · simp [h, not_lt_of_gt h]

lemma toMatSym_apply_self (p : SymIdx n → K) (i : n) : toMatSym p i i = 0 := by
  simp [toMatSym]

variable (n) in
/-- `X_{n,k}`: the Zariski closure, in the space of symmetric patterns, of the symmetric patterns
with `c(x) ≤ k`. -/
def Xvar (k : ℕ) : Set (SymIdx n → K) :=
  zariskiClosure {p | minCompRank (toMatSym p) ≤ k}

end Symmetric

end FreeDiagonal
