import FreeDiagonal.Variety.Theorem6

/-!
# [DSS07, Example 18] as computed: the elimination ideal over `ℚ`

[DSS07, Example 18] does not compute the real vanishing ideal `I_{8,3}`. It computes, in Singular
over `ℚ` (`ring R = 0, (p11, …, p88, p12, …), dp`), the ELIMINATION IDEAL
`eliminate(minor(Psi, 4), p11*p22*…*p88)` of the `4 × 4` minors of the generic symmetric
`8 × 8` matrix `Psi`, i.e. `M_{8,3} ∩ ℚ[ψ_ij : i < j]`. It then reports a minimal generating set,
each member lying in `J_{8,3}` or having its square there. The named hypothesis of this file says
exactly that, in its weakest form:

  `DSSExample18Q : Eideal ℚ (Fin 8) ≤ (JidealQ ℚ (Fin 8)).radical`,

where `Eideal ℚ (Fin 8)` is the elimination ideal (`comap` of the minors ideal along the inclusion
`ℚ[ψ_ij : i < j] → ℚ[ψ_ij : i ≤ j]`) and `JidealQ ℚ` is `J_{8,3}` with rational coefficients.

## Route to `DSSExample18` (no further hypothesis)

Let `z ∈ ℂ^{i<j}` be a zero of `J_{8,3}`. Its minors and septads vanish, so it is a zero of
`J_{8,3}` over `ℚ`, hence of the elimination ideal over `ℚ` (the hypothesis). To show
`z ∈ X_{8,3}`, take a complex polynomial `g` vanishing on `{c ≤ 3}`.
* As a polynomial in all the `ψ_ij` (`i ≤ j`), `g` vanishes on the complex symmetric matrices of
  rank `≤ 3`, the zeros of the minors. By the Nullstellensatz over `ℂ`, `gᵐ` lies in the complex
  minors ideal.
* **Extension of scalars of the elimination ideal** (`cproj`). Take a basis `(b_j)` of `ℂ` over
  `ℚ` and split each coefficient along it. The `j`-th part `cproj_j` of an element of the complex
  minors ideal lies in the rational minors ideal, since the minors have rational coefficients
  (`cproj_mem_Mideal`). Splitting commutes with renaming variables, so `cproj_j (gᵐ)` lies in the
  rational elimination ideal and vanishes at `z`. Since `gᵐ = Σ_j b_j · cproj_j (gᵐ)`, also
  `g(z)ᵐ = 0`.

So `V_ℂ(J_{8,3}) ⊆ X_{8,3}`, which is `DSSExample18` (`dssExample18_iff_points`). Conversely
`DSSExample18` implies `DSSExample18Q`, by Mathlib's Nullstellensatz for `ℚ`-ideals and `ℂ`-points
(`dssExample18Q_iff`). So the two hypotheses are equivalent, and the new one is word for word what
the computation establishes. [DSS07, Theorem 7] (elimination ideal = vanishing ideal, which needs
primality of symmetric determinantal ideals) is not used.

Also here: `FAideal_isPrime` (adapted from the audit of 27 Nov 2026).
-/

open Matrix Finset MvPolynomial

namespace FreeDiagonal

/-! ### Splitting complex coefficients along a basis of `ℂ` over `ℚ` -/

section Split

variable {σ τ : Type*}

/-- Apply a `ℚ`-linear functional `φ : ℂ → ℚ` to every coefficient. -/
noncomputable def cproj (φ : ℂ →ₗ[ℚ] ℚ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℚ :=
  ∑ s ∈ p.support, monomial s (φ (p.coeff s))

lemma coeff_cproj (φ : ℂ →ₗ[ℚ] ℚ) (p : MvPolynomial σ ℂ) (s : σ →₀ ℕ) :
    (cproj φ p).coeff s = φ (p.coeff s) := by
  classical
  rw [cproj, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

lemma cproj_add (φ : ℂ →ₗ[ℚ] ℚ) (p q : MvPolynomial σ ℂ) :
    cproj φ (p + q) = cproj φ p + cproj φ q := by
  ext s; simp [coeff_cproj]

lemma cproj_zero (φ : ℂ →ₗ[ℚ] ℚ) : cproj φ (0 : MvPolynomial σ ℂ) = 0 := by
  ext s; simp [coeff_cproj]

/-- `cproj φ` as an additive map. -/
noncomputable def cprojHom (φ : ℂ →ₗ[ℚ] ℚ) : MvPolynomial σ ℂ →+ MvPolynomial σ ℚ where
  toFun := cproj φ
  map_zero' := cproj_zero φ
  map_add' := cproj_add φ

lemma cproj_mul_map (φ : ℂ →ₗ[ℚ] ℚ) (c : MvPolynomial σ ℂ) (g : MvPolynomial σ ℚ) :
    cproj φ (c * map (algebraMap ℚ ℂ) g) = cproj φ c * g := by
  classical
  ext s
  rw [coeff_cproj, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [coeff_cproj, coeff_map, mul_comm (c.coeff x.1), ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]

lemma cproj_monomial (φ : ℂ →ₗ[ℚ] ℚ) (s : σ →₀ ℕ) (a : ℂ) :
    cproj φ (monomial s a) = monomial s (φ a) := by
  classical
  ext t
  rw [coeff_cproj, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

lemma cproj_rename (φ : ℂ →ₗ[ℚ] ℚ) (e : σ → τ) (p : MvPolynomial σ ℂ) :
    cproj φ (rename e p) = rename e (cproj φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a => rw [rename_monomial, cproj_monomial, cproj_monomial, rename_monomial]
  | add p q hp hq => rw [map_add, cproj_add, hp, hq, cproj_add, map_add]

/-- The basis of `ℂ` over `ℚ` used for splitting. -/
noncomputable abbrev qBasis : Module.Basis (Module.Basis.ofVectorSpaceIndex ℚ ℂ) ℚ ℂ :=
  Module.Basis.ofVectorSpace ℚ ℂ

/-- **Reassembling**: a complex polynomial vanishes at `z` if all its rational parts do. -/
theorem eval_eq_zero_of_cproj (z : σ → ℂ) (p : MvPolynomial σ ℂ)
    (h : ∀ j, aeval z (cproj (qBasis.coord j) p) = 0) : eval z p = 0 := by
  classical
  set J := p.support.biUnion (fun s => (qBasis.repr (p.coeff s)).support)
  have hrec : p = ∑ j ∈ J, C (qBasis j) * map (algebraMap ℚ ℂ) (cproj (qBasis.coord j) p) := by
    ext s
    rw [coeff_sum]
    simp only [coeff_C_mul, coeff_map, coeff_cproj, Module.Basis.coord_apply]
    by_cases hs : s ∈ p.support
    · have hsub : (qBasis.repr (p.coeff s)).support ⊆ J := fun j hj =>
        Finset.mem_biUnion.2 ⟨s, hs, hj⟩
      conv_lhs => rw [← qBasis.linearCombination_repr (p.coeff s)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      rw [Finset.sum_subset hsub (fun j _ hj => by
        rw [Finsupp.notMem_support_iff.1 hj]; simp)]
      apply Finset.sum_congr rfl
      intro j _
      rw [Algebra.smul_def, mul_comm]
    · rw [notMem_support_iff.1 hs]
      simp
  rw [hrec, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_mul, eval_C, eval_map, ← aeval_def, h j, mul_zero]

end Split

/-! ### The generic symmetric matrix, its minors, and the elimination ideal -/

section Elim

variable {n : Type*} [LinearOrder n]

variable (n) in
/-- The variables `ψ_ij`, `i ≤ j`, of the generic symmetric matrix (diagonal included). -/
abbrev UpIdx : Type _ := {q : n × n // q.1 ≤ q.2}

/-- The variable in position `(a, b)` of the generic symmetric matrix. -/
def upVar (a b : n) : UpIdx n :=
  if h : a ≤ b then ⟨(a, b), h⟩ else ⟨(b, a), le_of_lt (not_le.1 h)⟩

lemma upVar_of_le {a b : n} (h : a ≤ b) : upVar a b = ⟨(a, b), h⟩ := by simp [upVar, h]

lemma upVar_of_lt {a b : n} (h : b < a) : upVar a b = ⟨(b, a), le_of_lt h⟩ := by
  simp [upVar, not_le.2 h]

variable (k : Type*) [Field k]

variable (n) in
/-- The generic symmetric matrix `Ψ = (ψ_ij)` over `k`. -/
noncomputable def PsiFull : Matrix n n (MvPolynomial (UpIdx n) k) :=
  Matrix.of fun a b => X (upVar a b)

variable (n) in
/-- All `4 × 4` minors of `Ψ` (Singular's `minor(Psi, 4)`). -/
def fullMinors : Set (MvPolynomial (UpIdx n) k) :=
  {g | ∃ r c : Fin 4 → n, g = ((PsiFull n k).submatrix r c).det}

variable (n) in
/-- `M_{p,3}`: the ideal of the `4 × 4` minors (Singular's `M83`). -/
noncomputable def Mideal : Ideal (MvPolynomial (UpIdx n) k) := Ideal.span (fullMinors n k)

/-- The off-diagonal variables among all the variables. -/
def offIncl : SymIdx n → UpIdx n := fun q => ⟨q.1, le_of_lt q.2⟩

variable (n) in
/-- **The elimination ideal** `M_{p,3} ∩ k[ψ_ij : i < j]` (Singular's
`eliminate(M83, p11*…*p88)`), as an ideal of `k[ψ_ij : i < j]`. -/
noncomputable def Eideal : Ideal (MvPolynomial (SymIdx n) k) :=
  (Mideal n k).comap (rename (R := k) (offIncl (n := n)))

variable {k}

/-- The symmetric matrix of a point. -/
def symMatOf {K : Type*} (x : UpIdx n → K) : Matrix n n K := Matrix.of fun a b => x (upVar a b)

lemma aeval_det_PsiFull {K : Type*} [Field K] [Algebra k K] (x : UpIdx n → K) (r c : Fin 4 → n) :
    aeval x ((PsiFull n k).submatrix r c).det = ((symMatOf x).submatrix r c).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp [PsiFull, symMatOf, RingHom.mapMatrix_apply]

lemma mem_zeroLocus_span_iff_gen {σ K : Type*} [Field K] [Algebra k K]
    (S : Set (MvPolynomial σ k)) (z : σ → K) :
    z ∈ zeroLocus K (Ideal.span S) ↔ ∀ g ∈ S, aeval z g = 0 := by
  rw [mem_zeroLocus_iff_le_ker, Ideal.span_le]
  exact ⟨fun h g hg => (RingHom.mem_ker).1 (h hg), fun h g hg => (RingHom.mem_ker).2 (h g hg)⟩

/-- The zeros of the minors ideal are the symmetric matrices of rank `≤ 3`. -/
theorem mem_zeroLocus_Mideal_iff [Fintype n] {K : Type*} [Field K] [Algebra k K]
    (x : UpIdx n → K) : x ∈ zeroLocus K (Mideal n k) ↔ (symMatOf x).rank ≤ 3 := by
  rw [Mideal, mem_zeroLocus_span_iff_gen, rank_le_iff_minors]
  constructor
  · intro h r c
    rw [← aeval_det_PsiFull (k := k)]
    exact h _ ⟨r, c, rfl⟩
  · rintro h _ ⟨r, c, rfl⟩
    rw [aeval_det_PsiFull]
    exact h r c

/-- A symmetric pattern with a chosen diagonal, as a point of the space of symmetric matrices. -/
def liftPt {K : Type*} (p : SymIdx n → K) (d : n → K) : UpIdx n → K :=
  fun q => if h : q.1.1 < q.1.2 then p ⟨q.1, h⟩ else d q.1.1

lemma liftPt_of_lt {K : Type*} (p : SymIdx n → K) (d : n → K) (q : UpIdx n)
    (h : q.1.1 < q.1.2) : liftPt p d q = p ⟨q.1, h⟩ := by simp [liftPt, h]

lemma liftPt_diag {K : Type*} (p : SymIdx n → K) (d : n → K) (a : n) :
    liftPt p d ⟨(a, a), le_rfl⟩ = d a := by simp [liftPt]

lemma symMatOf_liftPt [Fintype n] {K : Type*} [Field K] (p : SymIdx n → K) (d : n → K) :
    symMatOf (liftPt p d) = toMatSym p + diagonal d := by
  ext a b
  simp only [symMatOf, of_apply, Matrix.add_apply]
  rcases lt_trichotomy a b with h | h | h
  · rw [upVar_of_le h.le, liftPt_of_lt _ _ _ h, toMatSym_apply_lt _ h,
      diagonal_apply_ne _ h.ne, add_zero]
  · subst h
    rw [upVar_of_le le_rfl, liftPt_diag, toMatSym_apply_self, diagonal_apply_eq, zero_add]
  · rw [upVar_of_lt h, liftPt_of_lt _ _ _ h, toMatSym_apply_gt _ h,
      diagonal_apply_ne _ (ne_of_gt h), add_zero]

lemma liftPt_comp_offIncl {K : Type*} (p : SymIdx n → K) (d : n → K) :
    liftPt p d ∘ offIncl = p := by
  funext q
  rw [Function.comp_apply, liftPt_of_lt _ _ _ q.2]
  rfl

lemma toMatSym_offIncl_offDiag [Fintype n] {K : Type*} [Field K] (x : UpIdx n → K) (a b : n)
    (hab : a ≠ b) : toMatSym (x ∘ offIncl) a b = symMatOf x a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [toMatSym_apply_lt _ h, symMatOf, of_apply, upVar_of_le h.le]; rfl
  · rw [toMatSym_apply_gt _ h, symMatOf, of_apply, upVar_of_lt h]; rfl

/-- **Elements of the elimination ideal vanish on `{c ≤ 3}`** (any field `K ⊇ k`). -/
theorem aeval_eq_zero_of_mem_Eideal [Fintype n] {K : Type*} [Field K] [Algebra k K]
    {f : MvPolynomial (SymIdx n) k} (hf : f ∈ Eideal n k) (p : SymIdx n → K)
    (hp : minCompRank (toMatSym p) ≤ 3) : aeval p f = 0 := by
  obtain ⟨d, hd⟩ := exists_minCompRank (toMatSym p)
  have hx : liftPt p d ∈ zeroLocus K (Mideal n k) := by
    rw [mem_zeroLocus_Mideal_iff, symMatOf_liftPt, hd]; exact hp
  have := (mem_zeroLocus_iff.1 hx) _ hf
  rwa [aeval_rename, liftPt_comp_offIncl] at this

/-- The off-diagonal part of a zero of the minors ideal has `c ≤ 3`. -/
theorem minCompRank_le_of_mem_zeroLocus_Mideal [Fintype n] {K : Type*} [Field K] [Algebra k K]
    (x : UpIdx n → K) (hx : x ∈ zeroLocus K (Mideal n k)) :
    minCompRank (toMatSym (x ∘ offIncl)) ≤ 3 :=
  (minCompRank_le_of_offDiag _ (symMatOf x) (toMatSym_apply_self _)
    (fun a b hab => (toMatSym_offIncl_offDiag x a b hab).symm)).trans
    ((mem_zeroLocus_Mideal_iff x).1 hx)

/-- The complex minors are the rational ones, with coefficients mapped. -/
lemma map_det_PsiFull (r c : Fin 4 → n) :
    map (algebraMap ℚ ℂ) ((PsiFull n ℚ).submatrix r c).det = ((PsiFull n ℂ).submatrix r c).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [PsiFull, RingHom.mapMatrix_apply]

/-- **Splitting maps the complex minors ideal into the rational one.** -/
theorem cproj_mem_Mideal (φ : ℂ →ₗ[ℚ] ℚ) {h : MvPolynomial (UpIdx n) ℂ}
    (hh : h ∈ Mideal n ℂ) : cproj φ h ∈ Mideal n ℚ := by
  obtain ⟨N, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  have hsum : cproj φ (∑ i, f i • (g i : MvPolynomial (UpIdx n) ℂ)) =
      ∑ i, cproj φ (f i • (g i : MvPolynomial (UpIdx n) ℂ)) := map_sum (cprojHom φ) _ _
  rw [hsum]
  apply Ideal.sum_mem
  intro i _
  obtain ⟨r, c, hg⟩ := (g i).2
  rw [smul_eq_mul]
  rw [hg, ← map_det_PsiFull, cproj_mul_map]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, c, rfl⟩)

end Elim

/-! ### `J_{p,3}` over any field -/

section JOver

variable {n : Type*} [LinearOrder n] (k : Type*) [Field k]

variable (n) in
/-- `Ψ⁰` over `k`. -/
noncomputable def Psi0Q : Matrix n n (MvPolynomial (SymIdx n) k) :=
  Matrix.of fun a b => symEntryPoly (K := k) a b

variable (n) in
/-- `J_{p,3}` over `k`: the off-diagonal `4 × 4` minors and the septads, coefficients in `k`. -/
noncomputable def JidealQ : Ideal (MvPolynomial (SymIdx n) k) :=
  Ideal.span ({g | ∃ r c : Fin 4 → n, IsOffMinorIdx r c ∧ g = minorVal (Psi0Q n k) r c} ∪
    {g | ∃ (i : n) (r c r' c' : Fin 3 → n), IsSeptadIdx i r c r' c' ∧
      g = septadVal (Psi0Q n k) i r c r' c'})

/-- Over `ℝ` this is the project's `J_{p,3}`. -/
lemma JidealQ_real : JidealQ n ℝ = Jideal n := rfl

variable {k}

lemma aeval_symEntryPoly_gen {K : Type*} [Field K] [Algebra k K] (z : SymIdx n → K) (a b : n) :
    aeval z (symEntryPoly (K := k) a b) = toMatSym z a b := by
  unfold symEntryPoly toMatSym
  split_ifs <;> simp

lemma aeval_det_Psi0Q {K : Type*} [Field K] [Algebra k K] (z : SymIdx n → K) {m : ℕ}
    (r c : Fin m → n) :
    aeval z ((Psi0Q n k).submatrix r c).det = ((toMatSym z).submatrix r c).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp [Psi0Q, aeval_symEntryPoly_gen, RingHom.mapMatrix_apply]

/-- **The zeros of `J_{p,3}` over `k`** are the patterns on which the minors and septads vanish,
for every coefficient field `k`. -/
theorem mem_zeroLocus_JidealQ_iff {K : Type*} [Field K] [Algebra k K] (z : SymIdx n → K) :
    z ∈ zeroLocus K (JidealQ n k) ↔ MSVanish (toMatSym z) := by
  rw [JidealQ, mem_zeroLocus_span_iff_gen]
  constructor
  · intro h
    refine ⟨fun r c hrc => ?_, fun i r c r' c' hs => ?_⟩
    · rw [minorVal, ← aeval_det_Psi0Q (k := k)]; exact h _ (Or.inl ⟨r, c, hrc, rfl⟩)
    · have := h _ (Or.inr ⟨i, r, c, r', c', hs, rfl⟩)
      simpa only [septadVal, map_sub, map_mul, aeval_det_Psi0Q] using this
  · rintro h g (⟨r, c, hrc, rfl⟩ | ⟨i, r, c, r', c', hs, rfl⟩)
    · rw [minorVal, aeval_det_Psi0Q]; exact h.1 r c hrc
    · simp only [septadVal, map_sub, map_mul, aeval_det_Psi0Q]; exact h.2 i r c r' c' hs

end JOver

/-! ### The named hypothesis `DSSExample18Q` and the bridge -/

/-- **The named hypothesis `DSSExample18Q`**, [DSS07, Example 18] as computed: over `ℚ`, every
element of the elimination ideal `M_{8,3} ∩ ℚ[ψ_ij : i < j]` of the `4 × 4` minors of the generic
symmetric `8 × 8` matrix has a power in `J_{8,3}` (off-diagonal `4 × 4` minors and septads, rational
coefficients). -/
def DSSExample18Q : Prop := Eideal (Fin 8) ℚ ≤ (JidealQ (Fin 8) ℚ).radical

/-- A finite generating set of the elimination ideal each of whose members lies in `J_{8,3}` or has
its square there (what [DSS07, Example 18] prints) gives `DSSExample18Q`. -/
theorem dssExample18Q_of_generators (G : Set (MvPolynomial (SymIdx (Fin 8)) ℚ))
    (hG : Ideal.span G = Eideal (Fin 8) ℚ)
    (h : ∀ g ∈ G, g ∈ JidealQ (Fin 8) ℚ ∨ g ^ 2 ∈ JidealQ (Fin 8) ℚ) : DSSExample18Q := by
  rw [DSSExample18Q, ← hG, Ideal.span_le]
  intro g hg
  rcases h g hg with h1 | h2
  · exact Ideal.le_radical h1
  · exact ⟨2, h2⟩

/-- **The bridge**: `DSSExample18Q` gives `V_ℂ(J_{8,3}) ⊆ X_{8,3}` (no other hypothesis). -/
theorem zeroLocus_Jideal_subset_Xvar_of_Q (hQ : DSSExample18Q) :
    zeroLocus ℂ (Jideal (Fin 8)) ⊆ Xvar (K := ℂ) (Fin 8) 3 := by
  intro z hz
  have hzJ : z ∈ zeroLocus ℂ (JidealQ (Fin 8) ℚ) :=
    (mem_zeroLocus_JidealQ_iff z).2 ((mem_zeroLocus_Jideal_iff z).1 hz)
  rw [← zeroLocus_radical] at hzJ
  have hzE : ∀ f ∈ Eideal (Fin 8) ℚ, aeval z f = 0 := fun f hf =>
    (mem_zeroLocus_iff.1 hzJ) f (hQ hf)
  rw [Xvar, zariskiClosure, mem_zeroLocus_iff]
  intro g hg
  rw [mem_vanishingIdeal_iff] at hg
  -- the Nullstellensatz over `ℂ`, on the space of symmetric matrices
  have hG : rename (R := ℂ) (offIncl (n := Fin 8)) g ∈ (Mideal (Fin 8) ℂ).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    rw [aeval_rename]
    exact hg _ (minCompRank_le_of_mem_zeroLocus_Mideal x hx)
  obtain ⟨m, hm⟩ := hG
  rw [← map_pow] at hm
  -- split the coefficients of `gᵐ` along a basis of `ℂ` over `ℚ`
  have hparts : ∀ j, aeval z (cproj (qBasis.coord j) (g ^ m)) = 0 := by
    intro j
    apply hzE
    show rename (R := ℚ) offIncl (cproj (qBasis.coord j) (g ^ m)) ∈ Mideal (Fin 8) ℚ
    rw [← cproj_rename]
    exact cproj_mem_Mideal _ hm
  have h0 := eval_eq_zero_of_cproj z (g ^ m) hparts
  rw [map_pow] at h0
  change eval z g = 0
  exact pow_eq_zero_iff'.1 h0 |>.1

/-- **`DSSExample18Q` implies `DSSExample18`** (whose definition is unchanged). -/
theorem dssExample18_of_Q (hQ : DSSExample18Q) : DSSExample18 :=
  dssExample18_iff_points.2 (zeroLocus_Jideal_subset_Xvar_of_Q hQ)

/-- **Conversely**, `DSSExample18` implies `DSSExample18Q` (Mathlib's Nullstellensatz for
`ℚ`-ideals with `ℂ`-points). So the two hypotheses are equivalent. -/
theorem dssExample18Q_of_dssExample18 (h8 : DSSExample18) : DSSExample18Q := by
  intro f hf
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
  intro z hz
  have hz' : z ∈ zeroLocus ℂ (Jideal (Fin 8)) :=
    (mem_zeroLocus_Jideal_iff z).2 ((mem_zeroLocus_JidealQ_iff z).1 hz)
  have hX := dssExample18_iff_points.1 h8 hz'
  rw [Xvar, zariskiClosure, mem_zeroLocus_iff] at hX
  have := hX (map (algebraMap ℚ ℂ) f) (by
    rw [mem_vanishingIdeal_iff]
    intro p hp
    rw [aeval_map_algebraMap]
    exact aeval_eq_zero_of_mem_Eideal hf p hp)
  rwa [aeval_map_algebraMap] at this

theorem dssExample18Q_iff : DSSExample18Q ↔ DSSExample18 :=
  ⟨dssExample18_of_Q, dssExample18Q_of_dssExample18⟩

/-! ### Non-vacuity -/

/-- The off-diagonal `4 × 4` minor on rows `{0,1,2,3}`, columns `{4,5,6,7}`. -/
noncomputable def minor0123 : MvPolynomial (SymIdx (Fin 8)) ℚ :=
  ((Psi0Q (Fin 8) ℚ).submatrix ![0, 1, 2, 3] ![4, 5, 6, 7]).det

lemma rename_symEntryPoly (a b : Fin 8) (hab : a ≠ b) :
    rename (R := ℚ) (offIncl (n := Fin 8)) (symEntryPoly (K := ℚ) a b) = X (upVar a b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp only [symEntryPoly, h, dite_true, rename_X, upVar_of_le h.le]; rfl
  · simp only [symEntryPoly, not_lt.2 h.le, h, dite_false, dite_true, rename_X, upVar_of_lt h]
    rfl

/-- **Non-vacuity**: the elimination ideal is not zero (it contains the off-diagonal minor
`minor0123`, which takes the value `1` at a rational point), and `J_{8,3}` over `ℚ` is not the whole
ring (all its generators vanish at `0`). -/
theorem dssExample18Q_nonvacuous :
    minor0123 ∈ Eideal (Fin 8) ℚ ∧ minor0123 ≠ 0 ∧ (JidealQ (Fin 8) ℚ).radical ≠ ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · show rename (R := ℚ) offIncl minor0123 ∈ Mideal (Fin 8) ℚ
    apply Ideal.subset_span
    refine ⟨![0, 1, 2, 3], ![4, 5, 6, 7], ?_⟩
    rw [minor0123, ← AlgHom.coe_toRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun a b => ?_
    simp only [RingHom.mapMatrix_apply, map_apply, submatrix_apply, Psi0Q, PsiFull, of_apply,
      AlgHom.coe_toRingHom]
    apply rename_symEntryPoly
    fin_cases a <;> fin_cases b <;> decide
  · intro h0
    set z : SymIdx (Fin 8) → ℚ := fun q => if (q.1.2 : ℕ) = q.1.1 + 4 then 1 else 0
    have := congrArg (aeval z) h0
    rw [minor0123, aeval_det_Psi0Q, map_zero] at this
    have h1 : (toMatSym z).submatrix ![(0 : Fin 8), 1, 2, 3] ![4, 5, 6, 7] = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [z, toMatSym]
    rw [h1, det_one] at this
    exact one_ne_zero this
  · intro htop
    have h1 : (1 : MvPolynomial (SymIdx (Fin 8)) ℚ) ∈ (JidealQ (Fin 8) ℚ).radical := by
      rw [htop]; trivial
    obtain ⟨m, hm⟩ := h1
    rw [one_pow] at hm
    have h0 : (0 : SymIdx (Fin 8) → ℂ) ∈ zeroLocus ℂ (JidealQ (Fin 8) ℚ) := by
      rw [mem_zeroLocus_JidealQ_iff]
      have hz : toMatSym (0 : SymIdx (Fin 8) → ℂ) = 0 := by
        ext a b; unfold toMatSym; split_ifs <;> rfl
      rw [hz]
      refine ⟨fun r c _ => ?_, fun i r c r' c' _ => ?_⟩
      · simp [minorVal]
      · simp [septadVal]
    have := (mem_zeroLocus_iff.1 h0) 1 hm
    rw [map_one] at this
    exact one_ne_zero this

/-! ### `I_{p,m}` is prime (adapted from the audit of 27 Nov 2026, `V4Ideals.lean`) -/

section Prime

variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- The off-diagonal entries of `Λ Λᵀ` as polynomials in the entries of `Λ`. -/
noncomputable def faParamPoly (m : ℕ) (q : SymIdx ι) : MvPolynomial (ι × Fin m) ℝ :=
  ∑ l : Fin m, X (q.1.1, l) * X (q.1.2, l)

omit [Fintype ι] in
lemma aeval_bind_faParamPoly (m : ℕ) (v : ι × Fin m → ℝ) (f : MvPolynomial (SymIdx ι) ℝ) :
    aeval v (bind₁ (faParamPoly m) f) =
      aeval (symCoords ((Matrix.of fun i l => v (i, l) : Matrix ι (Fin m) ℝ) *
        (Matrix.of fun i l => v (i, l) : Matrix ι (Fin m) ℝ)ᵀ)) f := by
  rw [aeval_bind₁]
  have hq : (fun q => aeval v (faParamPoly m q)) = symCoords
      ((Matrix.of fun i l => v (i, l) : Matrix ι (Fin m) ℝ) *
        (Matrix.of fun i l => v (i, l) : Matrix ι (Fin m) ℝ)ᵀ) := by
    funext q
    simp [faParamPoly, symCoords, Matrix.mul_apply]
  rw [hq]

lemma mem_FAideal_iff_bind (m : ℕ) (f : MvPolynomial (SymIdx ι) ℝ) :
    f ∈ FAideal ι m ↔ bind₁ (faParamPoly m) f = 0 := by
  rw [FAideal, mem_vanishingIdeal_iff, symCoords_FAmodel]
  constructor
  · intro h
    apply MvPolynomial.funext
    intro v
    rw [map_zero]
    change aeval v (bind₁ (faParamPoly m) f) = 0
    rw [aeval_bind_faParamPoly]
    exact h _ ⟨_, rfl⟩
  · rintro h _ ⟨Λ, rfl⟩
    have := congrArg (aeval (fun il : ι × Fin m => Λ il.1 il.2)) h
    rw [aeval_bind_faParamPoly, map_zero] at this
    exact this

/-- **`I_{p,m}` is a prime ideal**: the kernel of `ψ_ij ↦ Σ_l λ_il λ_jl` into a polynomial ring. -/
theorem FAideal_isPrime (m : ℕ) : (FAideal ι m).IsPrime := by
  have : FAideal ι m = RingHom.ker (bind₁ (faParamPoly (ι := ι) m)).toRingHom := by
    ext f; rw [mem_FAideal_iff_bind, RingHom.mem_ker]; rfl
  rw [this]
  exact RingHom.ker_isPrime _

end Prime

end FreeDiagonal
