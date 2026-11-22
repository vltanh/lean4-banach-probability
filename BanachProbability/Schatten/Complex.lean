module

public import BanachProbability.Schatten.Horn
public import BanachProbability.Schatten.Space

/-!
# Schatten norms of complex matrices

For a complex `m × n` matrix `A`, the singular values `s_i (A) = √λ_i (Aᴴ A)`, `i : n`, and the
Schatten `q`-norm `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}`, `max_i s_i` for `q = ∞` (`complexSchattenNorm`),
as in the real case (`schattenNorm`). With the *realification*
`realify A = [[Re A, −Im A], [Im A, Re A]]`, a real `2m × 2n` matrix, every singular value of `A`
occurs twice, so `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}` (`complexSchattenNorm_eq_realify`), and
the facts about real Schatten norms carry over: norm axioms, adjoints,
`‖Aᴴ A‖_{S_{q/2}} = ‖A‖_{S_q}²`, Hölder's inequality. A square matrix has a singular value
decomposition `A = U diag (s_i) Vᴴ` with unitary `U`, `V` (`exists_eq_unitary_mul_diagonal_mul`).
`ComplexSchattenSpace q m n` is the complex normed space of the Schatten `q`-norm; as a real space
it embeds isometrically in `SchattenSpace q (m ⊕ m) (n ⊕ n)` (see
`BanachProbability.Noncommutative.ComplexSchattenUMD` for its UMD constants).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-! ### Realification -/

/-- The realification `[[Re A, −Im A], [Im A, Re A]]` of a complex matrix. -/
def realify (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-A.map Complex.im) (A.map Complex.im) (A.map Complex.re)

omit [Fintype m] [Fintype n] in
/-- The realification is additive. -/
theorem realify_add (A B : Matrix m n ℂ) : realify (A + B) = realify A + realify B := by
  ext (i | i) (j | j) <;> simp [realify, add_comm]

omit [Fintype m] [Fintype n] in
/-- The realification is homogeneous, for real scalars. -/
theorem realify_smul (c : ℝ) (A : Matrix m n ℂ) : realify (c • A) = c • realify A := by
  ext (i | i) (j | j) <;> simp [realify]

omit [Fintype l] [Fintype n] in
/-- The realification is multiplicative. -/
theorem realify_mul (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    realify (A * B) = realify A * realify B := by
  ext (i | i) (j | j) <;>
    simp [realify, Matrix.mul_apply, Finset.sum_add_distrib, sub_eq_add_neg, add_comm]

omit [Fintype m] [Fintype n] in
/-- The realification of the adjoint is the transpose of the realification. -/
theorem realify_conjTranspose (A : Matrix m n ℂ) : realify Aᴴ = (realify A)ᵀ := by
  ext (i | i) (j | j) <;> simp [realify]

omit [Fintype m] [Fintype n] in
/-- The realification is injective. -/
theorem realify_injective : Function.Injective (realify : Matrix m n ℂ → _) := by
  intro A B h
  ext i j
  refine Complex.ext ?_ ?_
  · simpa [realify] using congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · simpa [realify] using congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

omit [Fintype n] in
/-- The realification of the unit matrix is the unit matrix. -/
theorem realify_one [DecidableEq n] : realify (1 : Matrix n n ℂ) = 1 := by
  ext (i | i) (j | j) <;> simp [realify, Matrix.one_apply, apply_ite]

omit [Fintype n] in
private theorem realify_diagonal_ofReal [DecidableEq n] (d : n → ℝ) :
    realify (Matrix.diagonal fun i => (d i : ℂ)) = Matrix.diagonal (Sum.elim d d) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [realify, h]

omit [Fintype n] in
private theorem transpose_realify_mul_realify (A : Matrix m n ℂ) :
    (realify A)ᵀ * realify A = realify (Aᴴ * A) := by
  rw [realify_mul, realify_conjTranspose]

/-! ### Schatten norms -/

section Norm

variable [DecidableEq n]

/-- The singular values of `A ∈ ℂ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᴴ A)`. -/
noncomputable def complexSingularValue (A : Matrix m n ℂ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm of a complex matrix: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`,
`‖A‖_{S_∞} = max_i s_i`. -/
noncomputable def complexSchattenNorm (q : ℝ≥0∞) (A : Matrix m n ℂ) : ℝ :=
  if q = ⊤ then ⨆ i, complexSingularValue A i
  else (∑ i, complexSingularValue A i ^ q.toReal) ^ (1 / q.toReal)

/-- The singular values are nonnegative. -/
theorem complexSingularValue_nonneg (A : Matrix m n ℂ) (i : n) : 0 ≤ complexSingularValue A i :=
  Real.sqrt_nonneg _

/-- `‖A‖_{S_q}^q = Σ_i s_i^q`. -/
theorem complexSchattenNorm_ofReal_rpow {q : ℝ} (hq : 0 < q) (A : Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, complexSingularValue A i ^ q := by
  rw [complexSchattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le, one_div,
    Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (complexSingularValue_nonneg A i) _) hq.ne']

/-- The spectral theorem for a complex Hermitian matrix: `A = U diag (λ) Uᴴ`, as
`eq_eigenvectorUnitary_mul_diagonal_mul_star` for real symmetric matrices. -/
theorem eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rfl

/-- The eigenvalues of a complex matrix `B = U diag (μ) Uᴴ`, `U` unitary and `μ` real, are the `μ_i`
up to order, as `map_eigenvalues_eq_of_eq_mul_diagonal_mul_star` for real matrices. -/
theorem map_eigenvalues_eq_of_eq_mul_diagonal_mul_conjTranspose {B : Matrix n n ℂ}
    (hB : B.IsHermitian) {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (μ : n → ℝ)
    (h : B = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ) :
    Multiset.map hB.eigenvalues Finset.univ.val = Multiset.map μ Finset.univ.val := by
  have hc : B.charpoly = (Matrix.diagonal fun i => (μ i : ℂ)).charpoly := by
    rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hr := hB.roots_charpoly_eq_eigenvalues
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _
    (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hr
  refine Multiset.map_injective Complex.ofReal_injective ?_
  rw [Multiset.map_map, Multiset.map_map]
  simpa using hr.symm

/-- The singular values of `A`, if `Aᴴ A = V diag (μ) Vᴴ` with `V` unitary. -/
private theorem map_complexSingularValue {A : Matrix m n ℂ} {V : Matrix n n ℂ} (hV : Vᴴ * V = 1)
    (μ : n → ℝ) (h : Aᴴ * A = V * Matrix.diagonal (fun i => (μ i : ℂ)) * Vᴴ) :
    Multiset.map (complexSingularValue A) Finset.univ.val =
      Multiset.map (fun i => √(μ i)) Finset.univ.val := by
  change Multiset.map (Real.sqrt ∘ _) _ = Multiset.map (Real.sqrt ∘ μ) _
  rw [← Multiset.map_map, map_eigenvalues_eq_of_eq_mul_diagonal_mul_conjTranspose
    (Matrix.isHermitian_conjTranspose_mul_self A) hV μ h, Multiset.map_map]

/-- The Schatten norms are determined by the multiset of the nonzero singular values. -/
private theorem complexSchattenNorm_eq_of_filter_map_eq {κ : Type*} [Fintype κ] {q : ℝ≥0∞}
    (hq : q ≠ 0) {A : Matrix m n ℂ} {f : κ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : (Multiset.map (complexSingularValue A) Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map f Finset.univ.val).filter (· ≠ 0)) :
    complexSchattenNorm q A =
      if q = ⊤ then ⨆ i, f i else (∑ i, f i ^ q.toReal) ^ (1 / q.toReal) := by
  unfold complexSchattenNorm
  split_ifs with ht
  · exact iSup_eq_of_filter_map_eq (complexSingularValue_nonneg A) hf h
  · rw [sum_comp_eq_of_filter_map_eq h (F := fun x => x ^ q.toReal)
      (Real.zero_rpow (ENNReal.toReal_ne_zero.2 ⟨hq, ht⟩))]

/-- The realification has every singular value twice: if `Aᴴ A = U diag (λ) Uᴴ`, then
`(realify A)ᵀ (realify A) = realify U · diag (λ, λ) · (realify U)ᵀ`, and `realify U` is
orthogonal. -/
private theorem map_singularValue_realify (A : Matrix m n ℂ) :
    Multiset.map (singularValue (realify A)) Finset.univ.val =
      Multiset.map (Sum.elim (complexSingularValue A) (complexSingularValue A))
        Finset.univ.val := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hR : realify U ∈ Matrix.unitaryGroup (n ⊕ n) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, transpose_realify_mul_realify, hU, realify_one]
  have h : (realify A)ᴴ * realify A =
      realify U * Matrix.diagonal (Sum.elim hA.eigenvalues hA.eigenvalues) * star (realify U) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial (realify A),
      Matrix.conjTranspose_eq_transpose_of_trivial (realify U), transpose_realify_mul_realify,
      ← realify_conjTranspose U, ← realify_diagonal_ofReal, ← realify_mul, ← realify_mul]
    exact congrArg realify (eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hA)
  have he := map_eigenvalues_eq_of_eq_mul_diagonal_mul_star
    (Matrix.isHermitian_conjTranspose_mul_self (realify A)) ⟨_, hR⟩ _ h
  change Multiset.map (Real.sqrt ∘ _) _ = _
  rw [← Multiset.map_map, he, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  rcases i with i | i <;> rfl

/-- `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}`: the realification has every singular value twice. -/
theorem complexSchattenNorm_eq_realify {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℂ) :
    complexSchattenNorm q A = (2 : ℝ) ^ (-(1 / q.toReal)) * schattenNorm q (realify A) := by
  have hmap := map_singularValue_realify A
  have hs : ∀ i, 0 ≤ Sum.elim (complexSingularValue A) (complexSingularValue A) i := by
    rintro (i | i) <;> exact complexSingularValue_nonneg A i
  unfold complexSchattenNorm schattenNorm
  split_ifs with ht
  · rw [iSup_eq_of_filter_map_eq (singularValue_nonneg _) hs
      (congrArg (Multiset.filter (· ≠ 0)) hmap), ht, ENNReal.toReal_top, div_zero, neg_zero,
      Real.rpow_zero, one_mul]
    refine le_antisymm (Real.iSup_le (fun i => ?_) (Real.iSup_nonneg hs))
      (Real.iSup_le ?_ (Real.iSup_nonneg (complexSingularValue_nonneg A)))
    · exact le_ciSup (f := Sum.elim (complexSingularValue A) (complexSingularValue A))
        (Finite.bddAbove_range _) (Sum.inl i)
    · rintro (i | i) <;> exact le_ciSup (f := complexSingularValue A) (Finite.bddAbove_range _) i
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq ht
    have h0 : 0 ≤ ∑ i, complexSingularValue A i ^ q.toReal :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (complexSingularValue_nonneg A i) _
    rw [sum_comp_eq_of_map_eq hmap (fun x => x ^ q.toReal), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← two_mul, Real.mul_rpow zero_le_two h0, ← mul_assoc, ← Real.rpow_add two_pos,
      neg_add_cancel, Real.rpow_zero, one_mul]

omit [Fintype l] [Fintype n] [DecidableEq n] in
private theorem map_ofReal_mul (B : Matrix l m ℝ) (C : Matrix m n ℝ) :
    (B * C).map Complex.ofReal = B.map Complex.ofReal * C.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

omit [Fintype m] [Fintype n] [DecidableEq n] in
private theorem map_ofReal_conjTranspose (B : Matrix m n ℝ) :
    Bᴴ.map Complex.ofReal = (B.map Complex.ofReal)ᴴ := by
  ext i j
  simp

/-- A real matrix has the same Schatten norms as a complex one. -/
theorem complexSchattenNorm_map_ofReal {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℝ) :
    complexSchattenNorm q (A.map Complex.ofReal) = schattenNorm q A := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  -- `Aᵀ A = U diag (λ) Uᵀ` with `U` orthogonal, over `ℝ` and so over `ℂ`
  have hV : (U.map Complex.ofReal)ᴴ * U.map Complex.ofReal = 1 := by
    rw [← map_ofReal_conjTranspose, ← map_ofReal_mul, hU]
    simp
  have hd : (Matrix.diagonal hA.eigenvalues).map Complex.ofReal =
      Matrix.diagonal fun i => (hA.eigenvalues i : ℂ) := by
    simp [Matrix.diagonal_map]
  have h : (A.map Complex.ofReal)ᴴ * A.map Complex.ofReal = U.map Complex.ofReal *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * (U.map Complex.ofReal)ᴴ := by
    rw [← map_ofReal_conjTranspose, ← map_ofReal_conjTranspose, ← hd, ← map_ofReal_mul,
      ← map_ofReal_mul, ← map_ofReal_mul]
    exact congrArg (fun M => M.map Complex.ofReal) (eq_eigenvectorUnitary_mul_diagonal_mul_star hA)
  exact complexSchattenNorm_eq_of_filter_map_eq hq (singularValue_nonneg A)
    (congrArg (Multiset.filter (· ≠ 0)) (map_complexSingularValue hV _ h))

/-- The Schatten norms are nonnegative. -/
theorem complexSchattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n ℂ) : 0 ≤ complexSchattenNorm q A := by
  unfold complexSchattenNorm
  split_ifs
  · exact Real.iSup_nonneg (complexSingularValue_nonneg A)
  · exact Real.rpow_nonneg
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (complexSingularValue_nonneg A i) _) _

/-- The Schatten norms are definite. -/
theorem complexSchattenNorm_eq_zero_iff {q : ℝ≥0∞} (hq : q ≠ 0) {A : Matrix m n ℂ} :
    complexSchattenNorm q A = 0 ↔ A = 0 := by
  have h0 : realify (0 : Matrix m n ℂ) = 0 := by
    ext (i | i) (j | j) <;> simp [realify]
  rw [complexSchattenNorm_eq_realify hq, mul_eq_zero, schattenNorm_eq_zero_iff hq, ← h0,
    realify_injective.eq_iff]
  exact or_iff_right (Real.rpow_pos_of_pos two_pos _).ne'

/-- The Schatten norms are homogeneous, for complex scalars. -/
theorem complexSchattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : ℂ) (A : Matrix m n ℂ) :
    complexSchattenNorm q (c • A) = ‖c‖ * complexSchattenNorm q A := by
  -- `(c A)ᴴ (c A) = |c|² Aᴴ A = (|c| A)ᴴ (|c| A)`
  have h : (realify (c • A))ᵀ * realify (c • A) =
      (‖c‖ • realify A)ᵀ * (‖c‖ • realify A) := by
    rw [← realify_smul, transpose_realify_mul_realify, transpose_realify_mul_realify]
    congr 1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, star_trivial ‖c‖, ← sq ‖c‖,
      ← starRingEnd_apply, Complex.conj_mul', ← Complex.ofReal_pow, Complex.coe_smul]
  rw [complexSchattenNorm_eq_realify hq, complexSchattenNorm_eq_realify hq,
    schattenNorm_eq_of_X_pow_mul_charpoly_eq (a := 0) (b := 0)
      (congrArg (fun M => Polynomial.X ^ 0 * M.charpoly) h) q, schattenNorm_smul hq,
    abs_norm, mul_left_comm]

/-- The triangle inequality for the Schatten norms, `1 ≤ q ≤ ∞`. -/
theorem complexSchattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n ℂ) :
    complexSchattenNorm q (A + B) ≤ complexSchattenNorm q A + complexSchattenNorm q B := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  rw [complexSchattenNorm_eq_realify hq0, complexSchattenNorm_eq_realify hq0,
    complexSchattenNorm_eq_realify hq0, realify_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (schattenNorm_add_le hq _ _) (Real.rpow_nonneg zero_le_two _)

/-- `‖Aᴴ‖_{S_q} = ‖A‖_{S_q}`. -/
theorem complexSchattenNorm_conjTranspose [DecidableEq m] (q : ℝ≥0∞) (A : Matrix m n ℂ) :
    complexSchattenNorm q Aᴴ = complexSchattenNorm q A := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [complexSchattenNorm]
  · rw [complexSchattenNorm_eq_realify hq, complexSchattenNorm_eq_realify hq,
      realify_conjTranspose, schattenNorm_transpose]

/-- `‖Aᴴ A‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem complexSchattenNorm_conjTranspose_mul_self {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℂ) :
    complexSchattenNorm (q / 2) (Aᴴ * A) = complexSchattenNorm q A ^ 2 := by
  have hq2 : q / 2 ≠ 0 := ENNReal.div_ne_zero.2 ⟨hq, ENNReal.ofNat_ne_top⟩
  rw [complexSchattenNorm_eq_realify hq2, complexSchattenNorm_eq_realify hq,
    ← transpose_realify_mul_realify, schattenNorm_transpose_mul_self hq, mul_pow,
    ← Real.rpow_mul_natCast zero_le_two, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  congr 2
  push_cast
  rw [one_div_div, neg_mul, one_div, ← div_eq_inv_mul]

/-- `‖A Aᴴ‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem complexSchattenNorm_mul_conjTranspose_self [DecidableEq m] {q : ℝ≥0∞} (hq : q ≠ 0)
    (A : Matrix m n ℂ) : complexSchattenNorm (q / 2) (A * Aᴴ) = complexSchattenNorm q A ^ 2 := by
  rw [← complexSchattenNorm_conjTranspose q A, ← complexSchattenNorm_conjTranspose_mul_self hq,
    Matrix.conjTranspose_conjTranspose]

/-- **Hölder's inequality**, `schattenNorm_mul_le` for complex matrices, from the real case by
realification: `‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r`. -/
theorem complexSchattenNorm_mul_le [DecidableEq m] {p q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / p = 1 / q + 1 / r) (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (A * B) ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal r) B := by
  have hp : 0 < p := one_div_pos.1 (hpqr ▸ by positivity)
  rw [complexSchattenNorm_eq_realify (ENNReal.ofReal_pos.2 hp).ne',
    complexSchattenNorm_eq_realify (ENNReal.ofReal_pos.2 hq).ne',
    complexSchattenNorm_eq_realify (ENNReal.ofReal_pos.2 hr).ne', ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hr.le, realify_mul, mul_mul_mul_comm,
    ← Real.rpow_add two_pos, ← neg_add, ← hpqr]
  exact mul_le_mul_of_nonneg_left (schattenNorm_mul_le hq hr hpqr _ _)
    (Real.rpow_nonneg zero_le_two _)

/-- `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`, `1/q + 1/q' = 1`, that is, `abs_trace_mul_le` for complex
matrices, from the real case by realification. -/
theorem norm_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    ‖(A * B).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal q') B := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq.pos).ne'
  have hq0' : ENNReal.ofReal q' ≠ 0 := (ENNReal.ofReal_pos.2 hq.symm.pos).ne'
  -- `|tr (A B)| = Re tr ((ω A) B)` for a unimodular `ω`, and `Re tr C = ½ tr (realify C)`
  obtain ⟨ω, hω, h⟩ := Complex.exists_norm_eq_mul_self (A * B).trace
  have hre : ∀ C : Matrix n n ℂ, (realify C).trace = 2 * C.trace.re := fun C => by
    simp [realify, Matrix.trace, two_mul]
  have h1 : 2 * ‖(A * B).trace‖ = (realify (ω • A) * realify B).trace := by
    rw [← realify_mul, hre, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← h, Complex.ofReal_re]
  have h2 := (le_abs_self _).trans (abs_trace_mul_le hq (realify (ω • A)) (realify B))
  -- `2^{−1/q} 2^{−1/q'} = ½`
  have h3 : (2 : ℝ) ^ (-(1 / q)) * (2 : ℝ) ^ (-(1 / q')) = 2⁻¹ := by
    rw [← Real.rpow_add two_pos, ← neg_add, one_div, one_div, hq.inv_add_inv_eq_one,
      Real.rpow_neg_one]
  rw [← one_mul (complexSchattenNorm (ENNReal.ofReal q) A), ← hω, ← complexSchattenNorm_smul hq0,
    complexSchattenNorm_eq_realify hq0, complexSchattenNorm_eq_realify hq0',
    ENNReal.toReal_ofReal hq.nonneg, ENNReal.toReal_ofReal hq.symm.nonneg, mul_mul_mul_comm, h3]
  linarith

/-- `(U diag (c) Vᴴ)ᴴ (U diag (d) Vᴴ) = V diag (c̄_i d_i) Vᴴ` for a unitary `U`. -/
theorem conjTranspose_unitary_mul_diagonal_mul {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (V : Matrix n n ℂ) (c d : n → ℂ) :
    (U * Matrix.diagonal c * Vᴴ)ᴴ * (U * Matrix.diagonal d * Vᴴ) =
      V * Matrix.diagonal (fun i => star (c i) * d i) * Vᴴ := by
  have hU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hd : Matrix.diagonal (fun i => star (c i) * d i) =
      (Matrix.diagonal c)ᴴ * Matrix.diagonal d := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rfl
  rw [hd, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]

/-- If `A = U diag (c) Vᴴ` with `U`, `V` unitary and `c_i ∈ ℂ`, then
`‖A‖_{S_q} = (Σ_i |c_i|^q)^{1/q}`. -/
theorem complexSchattenNorm_unitary_mul_diagonal_mul {q : ℝ} (hq : 0 < q)
    {U V : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (c : n → ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (U * Matrix.diagonal c * Vᴴ) =
      (∑ i, ‖c i‖ ^ q) ^ (1 / q) := by
  -- `(U D Vᴴ)ᴴ (U D Vᴴ) = V |D|² Vᴴ`
  have h : (U * Matrix.diagonal c * Vᴴ)ᴴ * (U * Matrix.diagonal c * Vᴴ) =
      V * Matrix.diagonal (fun i => ((‖c i‖ ^ 2 : ℝ) : ℂ)) * Vᴴ := by
    simp only [conjTranspose_unitary_mul_diagonal_mul hU, ← starRingEnd_apply, Complex.conj_mul',
      Complex.ofReal_pow]
  rw [complexSchattenNorm_eq_of_filter_map_eq (ENNReal.ofReal_pos.2 hq).ne'
    (fun i => Real.sqrt_nonneg _) (congrArg (Multiset.filter (· ≠ 0))
      (map_complexSingularValue (Matrix.mem_unitaryGroup_iff'.1 hV) _ h)),
    ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
  simp only [Real.sqrt_sq (norm_nonneg _)]

/-- The **singular value decomposition** `A = U diag (s_i) Vᴴ`, with unitary `U`, `V`, of a square
matrix. The columns of `V` are the eigenvectors `e_i` of `Aᴴ A`; those of `U` are `s_i⁻¹ A e_i` for
`s_i ≠ 0`, completed to an orthonormal basis. -/
theorem exists_eq_unitary_mul_diagonal_mul (A : Matrix n n ℂ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ V ∈ Matrix.unitaryGroup n ℂ,
      A = U * Matrix.diagonal (fun i => (complexSingularValue A i : ℂ)) * Vᴴ := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  set s := complexSingularValue A
  -- the vectors `f_i = A e_i` are orthogonal, with norm `s_i`
  set f : n → EuclideanSpace ℂ n := fun i => WithLp.toLp 2 fun k => (A * V) k i
  have hAV : (A * V)ᴴ * (A * V) = Matrix.diagonal fun i => ((s i ^ 2 : ℝ) : ℂ) := by
    have hs : ∀ i, s i ^ 2 = hA.eigenvalues i := fun i =>
      Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ,
      eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hA]
    simp only [← hVdef, Matrix.mul_assoc, hV, Matrix.mul_one, hs]
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hf : ∀ i j, inner ℂ (f i) (f j) = if i = j then ((s i ^ 2 : ℝ) : ℂ) else 0 := fun i j => by
    rw [← Matrix.diagonal_apply (d := fun i => ((s i ^ 2 : ℝ) : ℂ)), ← hAV, PiLp.inner_apply,
      Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the `s_i⁻¹ f_i`, `s_i ≠ 0`, are orthonormal
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := n)) (v := fun i => ((s i)⁻¹ : ℂ) • f i)
    (s := {i | s i ≠ 0}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.domRestrict_apply, inner_smul_left, inner_smul_right, hf, Subtype.mk.injEq]
      split_ifs with h
      · subst h
        have hi' : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hi
        rw [← Complex.ofReal_inv, Complex.conj_ofReal]
        push_cast
        field_simp
      · rw [mul_zero, mul_zero])
  refine ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b, V,
    hA.eigenvectorUnitary.2, ?_⟩
  -- `f_i = s_i b_i`
  have h : A * V = (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b *
      Matrix.diagonal fun i => (s i : ℂ) := by
    ext k i
    rw [Matrix.mul_diagonal]
    change f i k = b i k * s i
    rcases eq_or_ne (s i) 0 with h0 | h0
    · have hfi : f i = 0 := by
        rw [← inner_self_eq_zero (𝕜 := ℂ), hf, ite_eq_left rfl, h0, zero_pow two_ne_zero,
          Complex.ofReal_zero]
      rw [hfi, h0, Complex.ofReal_zero, mul_zero, PiLp.zero_apply]
    · rw [hb i h0, PiLp.smul_apply, smul_eq_mul, mul_right_comm, inv_mul_cancel₀
        (Complex.ofReal_ne_zero.2 h0), one_mul]
  rw [← h, Matrix.mul_assoc, hV', Matrix.mul_one]

/-- `‖A‖_{S_q}^q = Σ_i |λ_i|^q` for a Hermitian matrix. -/
theorem complexSchattenNorm_rpow_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) {q : ℝ}
    (hq : 0 < q) :
    complexSchattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, |hA.eigenvalues i| ^ q := by
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hA]
  rw [complexSchattenNorm_unitary_mul_diagonal_mul hq hA.eigenvectorUnitary.2
    hA.eigenvectorUnitary.2, ← Real.rpow_mul
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hq.ne',
    Real.rpow_one]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The Schatten norms are continuous functions of the entries, `1 ≤ q ≤ ∞`. -/
theorem continuous_complexSchattenNorm {q : ℝ≥0∞} (hq : 1 ≤ q) :
    Continuous (complexSchattenNorm q : Matrix m n ℂ → ℝ) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  -- the real Schatten norm is a norm on a finite-dimensional space
  have h : Continuous fun A : Matrix (m ⊕ m) (n ⊕ n) ℝ => schattenNorm q A :=
    (LinearMap.continuous_of_finiteDimensional
      (SchattenSpace.ofMatrix (q := q) (m := m ⊕ m) (n := n ⊕ n)).toLinearMap).norm
  have hr : Continuous (realify : Matrix m n ℂ → _) :=
    (continuous_id.matrix_map Complex.continuous_re).matrix_fromBlocks
      (continuous_id.matrix_map Complex.continuous_im).neg
      (continuous_id.matrix_map Complex.continuous_im)
      (continuous_id.matrix_map Complex.continuous_re)
  rw [funext (complexSchattenNorm_eq_realify (m := m) (n := n) (zero_lt_one.trans_le hq).ne')]
  exact continuous_const.mul (h.comp hr)

end Norm

/-! ### The normed space -/

/-- The complex `m × n` matrices with the Schatten `q`-norm. -/
def ComplexSchattenSpace (_q : ℝ≥0∞) (m n : Type*) : Type _ := Matrix m n ℂ

namespace ComplexSchattenSpace

variable {q : ℝ≥0∞}

/-- The vector space structure is that of the matrices. -/
instance {m n : Type*} : AddCommGroup (ComplexSchattenSpace q m n) :=
  inferInstanceAs (AddCommGroup (Matrix m n ℂ))

/-- The vector space structure is that of the matrices. -/
instance {m n : Type*} : Module ℂ (ComplexSchattenSpace q m n) :=
  inferInstanceAs (Module ℂ (Matrix m n ℂ))

/-- The identity map `Matrix m n ℂ → ComplexSchattenSpace q m n`, as a linear equivalence. -/
def ofMatrix {m n : Type*} : Matrix m n ℂ ≃ₗ[ℂ] ComplexSchattenSpace q m n := LinearEquiv.refl ℂ _

/-- The space of complex matrices of a given size is finite-dimensional. -/
instance {m n : Type*} [Finite m] [Finite n] : FiniteDimensional ℂ (ComplexSchattenSpace q m n) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix m n ℂ))

variable [DecidableEq n]

/-- The norm is the Schatten `q`-norm. -/
noncomputable instance : Norm (ComplexSchattenSpace q m n) :=
  ⟨fun A => complexSchattenNorm q (ofMatrix.symm A)⟩

/-- The norm of `ComplexSchattenSpace` is the Schatten `q`-norm, by definition. -/
theorem norm_def (A : ComplexSchattenSpace q m n) : ‖A‖ = complexSchattenNorm q (ofMatrix.symm A) :=
  rfl

/-- The norm of a matrix in `ComplexSchattenSpace` is its Schatten `q`-norm. -/
@[simp] theorem norm_ofMatrix (A : Matrix m n ℂ) :
    ‖(ofMatrix A : ComplexSchattenSpace q m n)‖ = complexSchattenNorm q A := rfl

/-- The axioms of a normed space, for `1 ≤ q ≤ ∞`. -/
theorem normedSpaceCore [hq : Fact (1 ≤ q)] :
    NormedSpace.Core ℂ (ComplexSchattenSpace q m n) where
  norm_nonneg A := complexSchattenNorm_nonneg q _
  norm_smul c A := by
    rw [norm_def, norm_def, map_smul, complexSchattenNorm_smul (zero_lt_one.trans_le hq.out).ne']
  norm_triangle A B := by
    rw [norm_def, norm_def, norm_def, map_add]
    exact complexSchattenNorm_add_le hq.out _ _
  norm_eq_zero_iff A := by
    rw [norm_def, complexSchattenNorm_eq_zero_iff (zero_lt_one.trans_le hq.out).ne',
      LinearEquiv.map_eq_zero_iff]

/-- The Schatten `q`-norm is a norm, `1 ≤ q ≤ ∞`. -/
noncomputable instance [Fact (1 ≤ q)] : NormedAddCommGroup (ComplexSchattenSpace q m n) :=
  NormedAddCommGroup.ofCore normedSpaceCore

/-- The complex normed space of the Schatten `q`-norm, `1 ≤ q ≤ ∞`. -/
noncomputable instance [Fact (1 ≤ q)] : NormedSpace ℂ (ComplexSchattenSpace q m n) :=
  NormedSpace.ofCore normedSpaceCore

/-- The space is complete, as it is finite-dimensional. -/
instance [Fact (1 ≤ q)] : CompleteSpace (ComplexSchattenSpace q m n) :=
  FiniteDimensional.complete ℂ _

end ComplexSchattenSpace

end BanachProbability
