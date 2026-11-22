module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm

/-!
# Block rows, block columns and block diagonal matrices

For matrices `a_1, …, a_K`, `blockRow a = (a_1 … a_K)` and `blockCol a = (a_1; …; a_K)`. Their
Schatten norms are the row and column square functions:
`‖blockCol a‖_{S_q} = ‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q}` and
`‖blockRow a‖_{S_q} = ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q}`, that is,
`‖blockCol a‖_{S_q}² = ‖Σ a_kᴴ a_k‖_{S_{q/2}}` (Lust-Piquard–Pisier, *Non commutative Khintchine and
Paley inequalities*, Ark. Mat. 29 (1991), (I.2), p. 245; `‖blockCol a‖_{S_q}` is their norm of
`C_E (ℓ²_R)`, `‖blockRow a‖_{S_q}` that of `C_E (ℓ²_L)`, `E = ℓ^q`, p. 246). Hölder's inequality for
a block row times a block column is their (I.3), p. 246; and for `q ≥ 2` the square functions are
dominated by the Rademacher sums, (I.5)–(I.7), pp. 246–247:
`‖blockCol a‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`.

For real block diagonal matrices, `‖diag (A_i)‖_{S_q}^q = Σ ‖A_i‖_{S_q}^q`
(`schattenNorm_blockDiagonal_rpow`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {𝕜 : Type*} {K : ℕ} {l m n : Type*}

/-- The block column `(a_1; …; a_K)`. -/
def blockCol (a : Fin K → Matrix m n 𝕜) : Matrix (Fin K × m) n 𝕜 :=
  Matrix.of fun p j => a p.1 p.2 j

/-- The block row `(a_1 … a_K)`. -/
def blockRow (a : Fin K → Matrix m n 𝕜) : Matrix m (Fin K × n) 𝕜 :=
  Matrix.of fun i p => a p.1 i p.2

section Algebra

variable [CommRing 𝕜] [StarRing 𝕜]

/-- The adjoint of a block row is the block column of the adjoints. -/
theorem conjTranspose_blockRow (a : Fin K → Matrix m n 𝕜) :
    (blockRow a)ᴴ = blockCol fun k => (a k)ᴴ :=
  rfl

omit [StarRing 𝕜] in
/-- A block row times a block column: `(a_1 … a_K) (b_1; …; b_K) = Σ a_k b_k`. -/
theorem blockRow_mul_blockCol [Fintype m] (a : Fin K → Matrix l m 𝕜) (b : Fin K → Matrix m n 𝕜) :
    blockRow a * blockCol b = ∑ k, a k * b k := by
  ext i j
  simp [blockRow, blockCol, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- `(a_1; …; a_K)ᴴ (b_1; …; b_K) = Σ a_kᴴ b_k`. -/
theorem conjTranspose_blockCol_mul_blockCol [Fintype m] (a b : Fin K → Matrix m n 𝕜) :
    (blockCol a)ᴴ * blockCol b = ∑ k, (a k)ᴴ * b k := by
  ext i j
  simp [blockCol, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- `(a_1 … a_K) (b_1 … b_K)ᴴ = Σ a_k b_kᴴ`. -/
theorem blockRow_mul_conjTranspose_blockRow [Fintype n] (a b : Fin K → Matrix m n 𝕜) :
    blockRow a * (blockRow b)ᴴ = ∑ k, a k * (b k)ᴴ := by
  rw [conjTranspose_blockRow, blockRow_mul_blockCol]

omit [StarRing 𝕜] in
/-- `x (a_1 … a_K) = (x a_1 … x a_K)`. -/
theorem mul_blockRow [Fintype m] (x : Matrix l m 𝕜) (a : Fin K → Matrix m n 𝕜) :
    x * blockRow a = blockRow fun k => x * a k := by
  ext i j
  simp [blockRow, Matrix.mul_apply]

omit [StarRing 𝕜] in
/-- `(a_1; …; a_K) x = (a_1 x; …; a_K x)`. -/
theorem blockCol_mul [Fintype n] (a : Fin K → Matrix m n 𝕜) {o : Type*} (x : Matrix n o 𝕜) :
    blockCol a * x = blockCol fun k => a k * x := by
  ext i j
  simp [blockCol, Matrix.mul_apply]

end Algebra

variable [Fintype m] [Fintype n] [DecidableEq n]

/-- `‖blockCol a‖_{S_q}² = ‖Σ a_kᴴ a_k‖_{S_{q/2}}`. -/
theorem complexSchattenNorm_blockCol_sq {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockCol a) ^ 2 = complexSchattenNorm (q / 2) (∑ k, (a k)ᴴ * a k) := by
  rw [← complexSchattenNorm_conjTranspose_mul_self hq, conjTranspose_blockCol_mul_blockCol]

/-- `‖blockRow a‖_{S_q}² = ‖Σ a_k a_kᴴ‖_{S_{q/2}}`. -/
theorem complexSchattenNorm_blockRow_sq [DecidableEq m] {q : ℝ≥0∞} (hq : q ≠ 0)
    (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockRow a) ^ 2 = complexSchattenNorm (q / 2) (∑ k, a k * (a k)ᴴ) := by
  rw [← complexSchattenNorm_mul_conjTranspose_self hq, blockRow_mul_conjTranspose_blockRow]

/-- `‖blockRow (a_1ᴴ, …, a_Kᴴ)‖_{S_q} = ‖blockCol a‖_{S_q}`. -/
theorem complexSchattenNorm_blockRow_conjTranspose [DecidableEq m] (q : ℝ≥0∞)
    (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockRow fun k => (a k)ᴴ) = complexSchattenNorm q (blockCol a) := by
  rw [← complexSchattenNorm_conjTranspose q (blockRow _), conjTranspose_blockRow]
  simp only [Matrix.conjTranspose_conjTranspose]

private theorem star_mul_self_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : star c * c = 1 := by
  rw [← starRingEnd_apply, Complex.conj_mul', hc, Complex.ofReal_one, one_pow]

/-- The row square function does not change when the `a_k` are multiplied by unimodular scalars. -/
theorem complexSchattenNorm_blockRow_smul {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ)
    {c : Fin K → ℂ} (hc : ∀ k, ‖c k‖ = 1) :
    complexSchattenNorm q (blockRow fun k => c k • a k) = complexSchattenNorm q (blockRow a) := by
  classical
  -- `(c a) (c a)ᴴ = a aᴴ` for `|c| = 1`
  have h : ∀ k, (c k • a k) * (c k • a k)ᴴ = a k * (a k)ᴴ := fun k => by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm,
      star_mul_self_of_norm_eq_one (hc k), one_smul]
  rw [← sq_eq_sq₀ (complexSchattenNorm_nonneg q _) (complexSchattenNorm_nonneg q _),
    complexSchattenNorm_blockRow_sq hq, complexSchattenNorm_blockRow_sq hq]
  simp only [h]

/-- The column square function does not change when the `a_k` are multiplied by unimodular scalars.
-/
theorem complexSchattenNorm_blockCol_smul {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ)
    {c : Fin K → ℂ} (hc : ∀ k, ‖c k‖ = 1) :
    complexSchattenNorm q (blockCol fun k => c k • a k) = complexSchattenNorm q (blockCol a) := by
  -- `(c a)ᴴ (c a) = aᴴ a` for `|c| = 1`
  have h : ∀ k, (c k • a k)ᴴ * (c k • a k) = (a k)ᴴ * a k := fun k => by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      star_mul_self_of_norm_eq_one (hc k), one_smul]
  rw [← sq_eq_sq₀ (complexSchattenNorm_nonneg q _) (complexSchattenNorm_nonneg q _),
    complexSchattenNorm_blockCol_sq hq, complexSchattenNorm_blockCol_sq hq]
  simp only [h]

/-- Lust-Piquard–Pisier (1991), (I.3), for the trace:
`|Σ tr (a_k b_k)| ≤ ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q} ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_{q'}}`. -/
theorem norm_sum_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (a : Fin K → Matrix n m ℂ) (b : Fin K → Matrix m n ℂ) :
    ‖∑ k, (a k * b k).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) (blockRow a) *
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b) := by
  rw [← Matrix.trace_sum, ← blockRow_mul_blockCol]
  exact norm_trace_mul_le hq _ _

omit [Fintype n] [DecidableEq n] in
/-- Orthonormality of the signs: `E [Yᴴ Y] = Σ a_kᴴ a_k` for `Y = Σ ε_k a_k`. -/
private theorem sum_smul_conjTranspose_mul_self (a : Fin K → Matrix m n ℂ) :
    ∑ ε : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹ •
        ((∑ k, coin (ε k) • a k)ᴴ * ∑ k, coin (ε k) • a k) = ∑ k, (a k)ᴴ * a k := by
  have hexp : ∀ ε : Fin K → Bool, (∑ k, coin (ε k) • a k)ᴴ * ∑ k, coin (ε k) • a k =
      ∑ i, ∑ j, (coin (ε i) * coin (ε j)) • ((a i)ᴴ * a j) := fun ε => by
    rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcoin : ∀ i j, ∑ ε : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹ * (coin (ε i) * coin (ε j)) =
      if i = j then 1 else 0 := fun i j => by
    rw [← avg_coin_mul_coin i j, avg, ← Finset.mul_sum, div_eq_inv_mul]
  simp only [hexp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hcoin, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Lust-Piquard–Pisier (1991), (I.7) with signs, column form: for `q ≥ 2`,
`‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`. -/
theorem complexSchattenNorm_blockCol_sq_le_avg {q : ℝ} (hq : 2 ≤ q) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockCol a) ^ 2 ≤
      avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • a k) ^ 2 := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hq1 : 1 ≤ ENNReal.ofReal q / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), one_mul]
    simpa using ENNReal.ofReal_le_ofReal hq
  have hq2 : ENNReal.ofReal q / 2 ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  -- `‖blockCol a‖² = ‖E [Yᴴ Y]‖_{S_{q/2}}`, then the triangle inequality in `S_{q/2}`
  rw [complexSchattenNorm_blockCol_sq hq0, ← sum_smul_conjTranspose_mul_self]
  refine (Finset.le_sum_of_subadditive _ ((complexSchattenNorm_eq_zero_iff hq2).2 rfl).le
    (complexSchattenNorm_add_le hq1) _ _).trans (le_of_eq ?_)
  rw [avg, Finset.sum_div]
  refine Finset.sum_congr rfl fun ε _ => ?_
  -- `‖Yᴴ Y‖_{S_{q/2}} = ‖Y‖_{S_q}²`
  rw [← Complex.coe_smul, complexSchattenNorm_smul hq2,
    complexSchattenNorm_conjTranspose_mul_self hq0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), div_eq_inv_mul]

/-- Lust-Piquard–Pisier (1991), (I.7) with signs, row form: for `q ≥ 2`,
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`. -/
theorem complexSchattenNorm_blockRow_sq_le_avg {q : ℝ} (hq : 2 ≤ q) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockRow a) ^ 2 ≤
      avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • a k) ^ 2 := by
  classical
  -- the column form for the `a_kᴴ`
  have h := complexSchattenNorm_blockCol_sq_le_avg hq fun k => (a k)ᴴ
  rw [← conjTranspose_blockRow, complexSchattenNorm_conjTranspose] at h
  refine h.trans_eq ?_
  congr 1
  funext ε
  rw [← complexSchattenNorm_conjTranspose _ (∑ k, coin (ε k) • a k), Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, star_trivial]

/-! ### Block diagonal matrices -/

/-- Real block diagonal matrices: `‖diag (A_i)‖_{S_q}^q = Σ ‖A_i‖_{S_q}^q`; in other words,
`ℓ^q (S_q)` embeds isometrically in `S_q`. -/
theorem schattenNorm_blockDiagonal_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ}
    (hq : 0 < q) (A : ι → Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.blockDiagonal A) ^ q =
      ∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ q := by
  have hA : ∀ i, ((A i)ᴴ * A i).IsHermitian := fun i =>
    Matrix.isHermitian_conjTranspose_mul_self (A i)
  -- diagonalise each block
  set U : Matrix (n × ι) (n × ι) ℝ :=
    Matrix.blockDiagonal fun i => ((hA i).eigenvectorUnitary : Matrix n n ℝ) with hU
  have hUs : star U =
      Matrix.blockDiagonal fun i => star ((hA i).eigenvectorUnitary : Matrix n n ℝ) := by
    simp only [hU, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose]
  have hUU : U ∈ Matrix.unitaryGroup (n × ι) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, hUs, hU, ← Matrix.blockDiagonal_mul]
    simp only [Unitary.mul_star_self_of_mem (hA _).eigenvectorUnitary.2]
    exact Matrix.blockDiagonal_one
  set μ : n × ι → ℝ := fun x => (hA x.2).eigenvalues x.1 with hμ
  have hdiag : Matrix.diagonal μ =
      Matrix.blockDiagonal fun i => Matrix.diagonal (hA i).eigenvalues := by
    rw [Matrix.blockDiagonal_diagonal]
  have h : (Matrix.blockDiagonal A)ᴴ * Matrix.blockDiagonal A =
      (⟨U, hUU⟩ : Matrix.unitaryGroup (n × ι) ℝ) * Matrix.diagonal μ *
        star ((⟨U, hUU⟩ : Matrix.unitaryGroup (n × ι) ℝ) : Matrix (n × ι) (n × ι) ℝ) := by
    change _ = U * Matrix.diagonal μ * star U
    rw [hUs, hdiag, hU, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    exact eq_eigenvectorUnitary_mul_diagonal_mul_star (hA i)
  have h1 := sum_comp_eq_of_map_eq (map_eigenvalues_eq_of_eq_mul_diagonal_mul_star
    (Matrix.isHermitian_conjTranspose_mul_self (Matrix.blockDiagonal A)) ⟨U, hUU⟩ μ h)
    fun x => √x ^ q
  rw [schattenNorm_ofReal_rpow hq]
  simp only [schattenNorm_ofReal_rpow hq, singularValue]
  rw [h1, Fintype.sum_prod_type_right]

end BanachProbability
