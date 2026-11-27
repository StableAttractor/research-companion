import FreeDiagonal.Foundations.Rank

/-!
# Symmetric matrices over `F₂` as sums of squares (Lempel's facts, proved from scratch)

For a symmetric matrix `M` over `ZMod 2`:
* (L1) `lempel_diag`: if some diagonal entry is non-zero, `M = B Bᵀ` with at most `rank M`
  columns;
* (L4) `lempel_zero_diag`: if the diagonal is zero, `M = B Bᵀ` with at most `rank M + 1` columns;
* (L2) `rank_add_one_le_of_zero_diag`: if the diagonal is zero, `M = B Bᵀ` with `s` columns and
  `M ≠ 0`, then `rank M + 1 ≤ s`;
* (L3) `even_rank_of_zero_diag`: if the diagonal is zero, `rank M` is even.

The proofs peel a rank-one square off a non-zero diagonal entry, or a hyperbolic pair
`u wᵀ + w uᵀ` off a zero-diagonal matrix. The identity
`z zᵀ + u wᵀ + w uᵀ = (z+u)(z+u)ᵀ + (z+w)(z+w)ᵀ + (z+u+w)(z+u+w)ᵀ` (over `F₂`) absorbs each
hyperbolic pair into a spare square.
-/

open Matrix Module Submodule

namespace FreeDiagonal

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by revert a; decide

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

section General

variable {F : Type*} [Field F] {m k : Type*} [Fintype m] [Fintype k]

/-- Rank is subadditive. -/
lemma rank_add_le_add (A B : Matrix m k F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- If `P` kills a subspace `K` of the column space of `M`, then `rank (P M) + dim K ≤ rank M`. -/
lemma rank_mul_add_finrank_le {n : Type*} [Fintype n] (P : Matrix n m F) (M : Matrix m k F)
    (K : Submodule F (m → F)) (hK : K ≤ LinearMap.range M.mulVecLin)
    (hP : ∀ v ∈ K, P *ᵥ v = 0) : (P * M).rank + finrank F K ≤ M.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  have h := finrank_map_le_add P.mulVecLin hK
  have h0 : finrank F (K.map P.mulVecLin) = 0 := by
    have : K.map P.mulVecLin ≤ ⊥ :=
      Submodule.map_le_iff_le_comap.2 (fun v hv => by simp [hP v hv])
    have := Submodule.finrank_mono this
    rw [finrank_bot] at this
    omega
  omega

end General

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "F2" => ZMod 2

lemma col_mem_range (M : Matrix n n F2) (i : n) :
    (fun a => M a i) ∈ LinearMap.range M.mulVecLin :=
  ⟨Pi.single i 1, by ext a; simp [Matrix.mulVecLin_apply, mulVec, dotProduct, Pi.single_apply]⟩

lemma vecMulVec_single_mul (x : n → F2) (j : n) (M : Matrix n n F2) :
    vecMulVec x (Pi.single j 1) * M = vecMulVec x (M j) := by
  ext a b; rw [Matrix.mul_apply]; simp [vecMulVec_apply, Pi.single_apply]

lemma vecMulVec_single_mulVec (x : n → F2) (j : n) (y : n → F2) :
    vecMulVec x (Pi.single j 1) *ᵥ y = y j • x := by
  ext a; simp [mulVec, dotProduct, vecMulVec_apply, Pi.single_apply, mul_comm]

lemma zmod2_sub_self_sub (x : F2) : 0 - x - x = 0 := by revert x; decide

/-- Peeling off a non-zero diagonal entry. -/
lemma diag_peel (M : Matrix n n F2) (hM : M.IsSymm) (i : n) (hi : M i i ≠ 0) :
    ∃ v : n → F2, ∃ M' : Matrix n n F2, M = vecMulVec v v + M' ∧ M'.IsSymm ∧
      M'.rank + 1 ≤ M.rank := by
  have hi1 : M i i = 1 := zmod2_eq_one_of_ne_zero hi
  have hsym : ∀ a b, M b a = M a b := fun a b => by
    have := congrFun (congrFun hM a) b; simpa [transpose_apply] using this
  set v : n → F2 := fun a => M a i
  have hMi : M i = v := funext fun b => hsym b i
  set P : Matrix n n F2 := 1 - vecMulVec v (Pi.single i 1)
  have hPM : P * M = M - vecMulVec v v := by
    rw [sub_mul, one_mul, vecMulVec_single_mul, hMi]
  refine ⟨v, P * M, ?_, ?_, ?_⟩
  · rw [hPM]; abel
  · rw [hPM]
    ext a b
    simp [Matrix.sub_apply, vecMulVec_apply, hsym a b, mul_comm]
  · have hv0 : v ≠ 0 := fun h => by
      have := congrFun h i; simp [v, hi1] at this
    have hK : span F2 {v} ≤ LinearMap.range M.mulVecLin :=
      (span_singleton_le_iff_mem _ _).2 (col_mem_range M i)
    have hP : ∀ w ∈ span F2 {v}, P *ᵥ w = 0 := by
      intro w hw
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hw
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_single_mulVec]
      simp [v, hi1]
    have h := rank_mul_add_finrank_le P M _ hK hP
    rwa [finrank_span_singleton hv0] at h

/-- Peeling off a hyperbolic pair from a non-zero zero-diagonal matrix. -/
lemma alt_peel (M : Matrix n n F2) (hM : M.IsSymm) (hd : ∀ i, M i i = 0) (hne : M ≠ 0) :
    ∃ u w : n → F2, ∃ M'' : Matrix n n F2,
      M = vecMulVec u w + vecMulVec w u + M'' ∧ M''.IsSymm ∧ (∀ i, M'' i i = 0) ∧
      M''.rank + 2 ≤ M.rank ∧ M.rank ≤ M''.rank + 2 := by
  have hsym : ∀ a b, M b a = M a b := fun a b => by
    have := congrFun (congrFun hM a) b; simpa [transpose_apply] using this
  obtain ⟨a, b, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Matrix.ext h)
  have hab1 : M a b = 1 := zmod2_eq_one_of_ne_zero hab
  have hba1 : M b a = 1 := by rw [hsym]; exact hab1
  set u : n → F2 := fun c => M c a
  set w : n → F2 := fun c => M c b
  have hMa : M a = u := funext fun c => hsym c a
  have hMb : M b = w := funext fun c => hsym c b
  set P : Matrix n n F2 := 1 - vecMulVec u (Pi.single b 1) - vecMulVec w (Pi.single a 1)
  have hPM : P * M = M - vecMulVec u w - vecMulVec w u := by
    rw [sub_mul, sub_mul, one_mul, vecMulVec_single_mul, vecMulVec_single_mul, hMa, hMb]
  refine ⟨u, w, P * M, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPM]; abel
  · rw [hPM]
    ext c e
    simp only [transpose_apply, Matrix.sub_apply, vecMulVec_apply, hsym c e]
    ring
  · intro c
    rw [hPM]
    simp only [Matrix.sub_apply, vecMulVec_apply, hd c]
    rw [mul_comm (w c)]
    exact zmod2_sub_self_sub _
  · have hK : span F2 {u, w} ≤ LinearMap.range M.mulVecLin := by
      rw [span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact col_mem_range M a
      · exact col_mem_range M b
    have hP : ∀ x ∈ span F2 {u, w}, P *ᵥ x = 0 := by
      intro x hx
      obtain ⟨s, t, rfl⟩ := mem_span_pair.1 hx
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_single_mulVec,
        vecMulVec_single_mulVec]
      have hua : u a = 0 := hd a
      have hub : u b = 1 := hba1
      have hwa : w a = 1 := hab1
      have hwb : w b = 0 := hd b
      simp [hua, hub, hwa, hwb]
    have hli : LinearIndependent F2 ![u, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrFun hst b
      have h2 := congrFun hst a
      have hua : u a = 0 := hd a
      have hub : u b = 1 := hba1
      have hwa : w a = 1 := hab1
      have hwb : w b = 0 := hd b
      simp [hua, hub, hwa, hwb] at h1 h2
      exact ⟨h1, h2⟩
    have hrange : Set.range ![u, w] = {u, w} := by
      ext x; simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff,
        Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one]; tauto
    have hfin : finrank F2 (span F2 {u, w}) = 2 := by
      have := finrank_span_eq_card hli
      rw [hrange] at this
      simpa using this
    have h := rank_mul_add_finrank_le P M _ hK hP
    rwa [hfin] at h
  · have e : M = P * M + vecMulVec u w + vecMulVec w u := by rw [hPM]; abel
    calc M.rank = (P * M + vecMulVec u w + vecMulVec w u).rank := by rw [← e]
      _ ≤ (P * M + vecMulVec u w).rank + (vecMulVec w u).rank := rank_add_le_add _ _
      _ ≤ (P * M).rank + (vecMulVec u w).rank + (vecMulVec w u).rank := by
          gcongr; exact rank_add_le_add _ _
      _ ≤ (P * M).rank + 1 + 1 := by
          gcongr <;> exact rank_vecMulVec_le _ _
      _ = (P * M).rank + 2 := by ring

/-- The `F₂` identity behind the absorption step. -/
lemma absorb_identity (z u w : n → F2) :
    vecMulVec z z + vecMulVec u w + vecMulVec w u =
      vecMulVec (z + u) (z + u) + vecMulVec (z + w) (z + w) +
        vecMulVec (z + u + w) (z + u + w) := by
  have key : ∀ za zb ua ub wa wb : F2,
      za * zb + ua * wb + wa * ub =
        (za + ua) * (zb + ub) + (za + wa) * (zb + wb) + (za + ua + wa) * (zb + ub + wb) := by
    decide
  ext a b
  simp only [Matrix.add_apply, vecMulVec_apply, Pi.add_apply]
  exact key _ _ _ _ _ _

/-- `B` with two extra columns in front. -/
def cons2 {s : ℕ} (x y : n → F2) (B : Matrix n (Fin s) F2) : Matrix n (Fin (s + 2)) F2 :=
  fun a => Fin.cons (x a) (Fin.cons (y a) (B a))

lemma cons2_mul (x y : n → F2) {s : ℕ} (B : Matrix n (Fin s) F2) :
    cons2 x y B * (cons2 x y B)ᵀ = vecMulVec x x + vecMulVec y y + B * Bᵀ := by
  ext a b
  rw [Matrix.mul_apply]; simp only [Matrix.add_apply]; rw [Matrix.mul_apply]
  simp [cons2, Fin.sum_univ_succ, vecMulVec_apply, add_assoc]

/-- `B` with one extra column in front. -/
def cons1 {s : ℕ} (x : n → F2) (B : Matrix n (Fin s) F2) : Matrix n (Fin (s + 1)) F2 :=
  fun a => Fin.cons (x a) (B a)

lemma cons1_mul (x : n → F2) {s : ℕ} (B : Matrix n (Fin s) F2) :
    cons1 x B * (cons1 x B)ᵀ = vecMulVec x x + B * Bᵀ := by
  ext a b
  rw [Matrix.mul_apply]; simp only [Matrix.add_apply]; rw [Matrix.mul_apply]
  simp [cons1, Fin.sum_univ_succ, vecMulVec_apply]

/-- **Absorption.** A zero-diagonal symmetric `M` plus one square `z zᵀ` is `B Bᵀ` with at most
`rank M + 1` columns. -/
theorem absorb (r : ℕ) : ∀ (M : Matrix n n F2), M.rank ≤ r → M.IsSymm → (∀ i, M i i = 0) →
    ∀ z : n → F2, ∃ s ≤ M.rank + 1, ∃ B : Matrix n (Fin s) F2,
      vecMulVec z z + M = B * Bᵀ := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro M hr hM hd z
  by_cases h0 : M = 0
  · refine ⟨1, by omega, Matrix.of fun a (_ : Fin 1) => z a, ?_⟩
    subst h0
    ext a b
    simp only [add_zero]
    rw [Matrix.mul_apply]
    simp [vecMulVec_apply]
  · obtain ⟨u, w, M'', e, hs'', hd'', hr1, -⟩ := alt_peel M hM hd h0
    obtain ⟨s, hs, B, hB⟩ := ih M''.rank (by omega) M'' le_rfl hs'' hd'' (z + u + w)
    refine ⟨s + 2, by omega, cons2 (z + u) (z + w) B, ?_⟩
    rw [cons2_mul, ← hB, e]
    have := absorb_identity z u w
    calc vecMulVec z z + (vecMulVec u w + vecMulVec w u + M'')
        = (vecMulVec z z + vecMulVec u w + vecMulVec w u) + M'' := by abel
      _ = _ := by rw [this]; abel

/-- **(L1)** A symmetric matrix over `F₂` with a non-zero diagonal entry is `B Bᵀ` with at most
`rank M` columns. -/
theorem lempel_diag (M : Matrix n n F2) (hM : M.IsSymm) (hdiag : ∃ i, M i i ≠ 0) :
    ∃ s ≤ M.rank, ∃ B : Matrix n (Fin s) F2, M = B * Bᵀ := by
  suffices h : ∀ r, ∀ M : Matrix n n F2, M.rank ≤ r → M.IsSymm → (∃ i, M i i ≠ 0) →
      ∃ s ≤ M.rank, ∃ B : Matrix n (Fin s) F2, M = B * Bᵀ from h _ M le_rfl hM hdiag
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro M hr hM ⟨i, hi⟩
  obtain ⟨v, M', e, hs', hr'⟩ := diag_peel M hM i hi
  by_cases hd' : ∃ j, M' j j ≠ 0
  · obtain ⟨s, hs, B, hB⟩ := ih M'.rank (by omega) M' le_rfl hs' hd'
    refine ⟨s + 1, by omega, cons1 v B, ?_⟩
    rw [cons1_mul, ← hB, e]
  · push_neg at hd'
    obtain ⟨s, hs, B, hB⟩ := absorb M'.rank M' le_rfl hs' hd' v
    exact ⟨s, by omega, B, by rw [e, hB]⟩

/-- **(L4)** A zero-diagonal symmetric matrix over `F₂` is `B Bᵀ` with at most `rank M + 1`
columns. -/
theorem lempel_zero_diag (M : Matrix n n F2) (hM : M.IsSymm) (hd : ∀ i, M i i = 0) :
    ∃ s ≤ M.rank + 1, ∃ B : Matrix n (Fin s) F2, M = B * Bᵀ := by
  obtain ⟨s, hs, B, hB⟩ := absorb M.rank M le_rfl hM hd 0
  exact ⟨s, hs, B, by rw [← hB]; simp⟩

/-- Every symmetric matrix over `F₂` is `B Bᵀ` with at most `rank M + 1` columns. -/
theorem lempel_le_add_one (M : Matrix n n F2) (hM : M.IsSymm) :
    ∃ s ≤ M.rank + 1, ∃ B : Matrix n (Fin s) F2, M = B * Bᵀ := by
  by_cases h : ∃ i, M i i ≠ 0
  · obtain ⟨s, hs, B, hB⟩ := lempel_diag M hM h
    exact ⟨s, by omega, B, hB⟩
  · push_neg at h
    exact lempel_zero_diag M hM h

/-- **(L2)** If `M = B Bᵀ` has zero diagonal and `M ≠ 0`, then `B` has at least `rank M + 1`
columns: every row of `B` has even weight, so `B` kills the all-ones vector. -/
theorem rank_add_one_le_of_zero_diag {s : ℕ} (B : Matrix n (Fin s) F2)
    (hd : ∀ i, (B * Bᵀ) i i = 0) (hne : B * Bᵀ ≠ 0) : (B * Bᵀ).rank + 1 ≤ s := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    exact absurd (by ext a b; rw [Matrix.mul_apply]; simp) hne
  have hker : B *ᵥ (fun _ => 1) = 0 := by
    ext a
    have := hd a
    rw [Matrix.mul_apply] at this
    simpa [mulVec, dotProduct, zmod2_mul_self] using this
  have hone : (fun _ : Fin s => (1 : F2)) ≠ 0 := fun h => by
    have := congrFun h ⟨0, hs⟩; simp at this
  have hrn := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at hrn
  have hk : 1 ≤ finrank F2 (LinearMap.ker B.mulVecLin) := by
    have hmem : (fun _ : Fin s => (1 : F2)) ∈ LinearMap.ker B.mulVecLin := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hker
    have hpos : 0 < finrank F2 (LinearMap.ker B.mulVecLin) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨_, hmem⟩, fun h => hone (by simpa using h)⟩
    omega
  have h1 : (B * Bᵀ).rank ≤ B.rank := rank_mul_le_left _ _
  unfold Matrix.rank at h1 ⊢
  omega

/-- **(L3)** A zero-diagonal symmetric matrix over `F₂` has even rank. -/
theorem even_rank_of_zero_diag (M : Matrix n n F2) (hM : M.IsSymm) (hd : ∀ i, M i i = 0) :
    Even M.rank := by
  suffices h : ∀ r, ∀ M : Matrix n n F2, M.rank ≤ r → M.IsSymm → (∀ i, M i i = 0) →
      Even M.rank from h _ M le_rfl hM hd
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro M hr hM hd
  by_cases h0 : M = 0
  · subst h0; simp
  · obtain ⟨u, w, M'', -, hs'', hd'', h1, h2⟩ := alt_peel M hM hd h0
    have := ih M''.rank (by omega) M'' le_rfl hs'' hd''
    have e : M.rank = M''.rank + 2 := by omega
    rw [e]
    exact this.add even_two

end FreeDiagonal
