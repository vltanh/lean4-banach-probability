module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm

/-!
# Block rows, block columns and block diagonal matrices

For matrices `a_1, …, a_K`, `blockRow a = (a_1 … a_K)` and `blockCol a = (a_1; …; a_K)`. Their
Schatten norms are the row and column square functions:
`‖blockCol a‖_{S_q} = ‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q}` and
`‖blockRow a‖_{S_q} = ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q}`, that is,
`‖blockCol a‖_{S_q}² = ‖Σ a_kᴴ a_k‖_{S_{q/2}}` (F. Lust-Piquard, G. Pisier, *Non commutative
Khintchine and Paley inequalities*, Ark. Mat. 29 (1991) 241–260, (I.2), p. 245; `‖blockCol a‖_{S_q}`
is their norm of `C_E (ℓ²_R)`, `‖blockRow a‖_{S_q}` that of `C_E (ℓ²_L)`, `E = ℓ^q`, p. 246).

From the same paper:

* (I.3), p. 246, in trace form: Hölder's inequality for the trace of a block row times a block
  column (`norm_sum_trace_mul_le`);
* the bounds in the dualities of `C_q (ℓ²_R)` and `C_{q'} (ℓ²_R)` and of `C_q (ℓ²_L)` and
  `C_{q'} (ℓ²_L)`, p. 246 (`norm_sum_trace_mul_conjTranspose_le_blockCol`,
  `norm_sum_trace_mul_conjTranspose_le_blockRow`);
* for `q ≥ 2` the square functions are dominated by the Rademacher sums, (I.7), p. 247, by (I.5) and
  the triangle inequality, as (I.6), p. 246: `‖blockCol a‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`
  (`complexSchattenNorm_blockCol_sq_le_avg`, `complexSchattenNorm_blockRow_sq_le_avg`).

For block diagonal matrices, `‖diag (A_i)‖_{S_q} = (Σ ‖A_i‖_{S_q}^q)^{1/q}`
(`complexSchattenNorm_blockDiagonal`, `schattenNorm_blockDiagonal_rpow`; N. Tomczak-Jaegermann, *The
moduli of smoothness and convexity and the Rademacher averages of trace classes `S_p`
(`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, p. 166), so, for real matrices, `ℓ^q (S_q)` embeds
isometrically in `S_q` (`schattenBlockDiagonal`).
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

/-- Lust-Piquard–Pisier (1991), (I.3), p. 246, in trace form:
`|Σ tr (a_k b_k)| ≤ ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q} ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_{q'}}`. -/
theorem norm_sum_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (a : Fin K → Matrix n m ℂ) (b : Fin K → Matrix m n ℂ) :
    ‖∑ k, (a k * b k).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) (blockRow a) *
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b) := by
  rw [← Matrix.trace_sum, ← blockRow_mul_blockCol]
  exact norm_trace_mul_le hq _ _

/-- The bound in the duality `⟨a, b⟩ = Σ tr (a_k b_kᴴ)` of `C_q (ℓ²_L)` and `C_{q'} (ℓ²_L)`
(Lust-Piquard–Pisier (1991), p. 246, who write the duality for `ℓ²_R`), by (I.3) for the `a_k` and
the `b_kᴴ`: `|Σ tr (a_k b_kᴴ)| ≤ ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q} ‖(Σ b_k b_kᴴ)^{1/2}‖_{S_{q'}}`. -/
theorem norm_sum_trace_mul_conjTranspose_le_blockRow {q q' : ℝ} (hq : q.HolderConjugate q')
    (a b : Fin K → Matrix m n ℂ) :
    ‖∑ k, (a k * (b k)ᴴ).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) (blockRow a) *
        complexSchattenNorm (ENNReal.ofReal q') (blockRow b) := by
  classical
  rw [← complexSchattenNorm_conjTranspose _ (blockRow b)]
  exact norm_sum_trace_mul_le hq a fun k => (b k)ᴴ

/-- The bound in the duality `⟨a, b⟩ = Σ tr (a_k b_kᴴ)` of `C_q (ℓ²_R)` and `C_{q'} (ℓ²_R)`
(Lust-Piquard–Pisier (1991), p. 246), by (I.3) for the `b_kᴴ` and the `a_k`:
`|Σ tr (a_k b_kᴴ)| ≤ ‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q} ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_{q'}}`. -/
theorem norm_sum_trace_mul_conjTranspose_le_blockCol {q q' : ℝ} (hq : q.HolderConjugate q')
    (a b : Fin K → Matrix m n ℂ) :
    ‖∑ k, (a k * (b k)ᴴ).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) (blockCol a) *
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b) := by
  classical
  simp only [Matrix.trace_mul_comm (a _)]
  rw [mul_comm, ← complexSchattenNorm_blockRow_conjTranspose]
  exact norm_sum_trace_mul_le hq.symm (fun k => (b k)ᴴ) a

omit [Fintype n] [DecidableEq n] in
/-- Orthonormality of the signs: `E [Yᴴ Y] = Σ a_kᴴ a_k` for `Y = Σ ε_k a_k`. -/
private theorem sum_smul_conjTranspose_mul_self (a : Fin K → Matrix m n ℂ) :
    ∑ ε : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹ •
        ((∑ k, coin (ε k) • a k)ᴴ * ∑ k, coin (ε k) • a k) = ∑ k, (a k)ᴴ * a k := by
  have hcoin : ∀ i j, ∑ ε : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹ * (coin (ε i) * coin (ε j)) =
      if i = j then 1 else 0 := fun i j => by
    rw [← avg_coin_mul_coin i j, avg, ← Finset.mul_sum, div_eq_inv_mul]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, hcoin, ite_smul]

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

section BlockDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex block diagonal matrices: `‖diag (A_i)‖_{S_p} = (Σ ‖A_i‖_{S_p}^p)^{1/p}`
(Tomczak-Jaegermann (1974), p. 166), as the singular value decompositions of the blocks give one of
the block diagonal matrix. -/
theorem complexSchattenNorm_blockDiagonal {p : ℝ} (hp : 0 < p) (A : ι → Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (Matrix.blockDiagonal A) =
      (∑ i, complexSchattenNorm (ENNReal.ofReal p) (A i) ^ p) ^ (1 / p) := by
  choose U hU V hV hA using fun i => exists_eq_unitary_mul_diagonal_mul (A i)
  have hb : ∀ W : ι → Matrix n n ℂ, (∀ i, W i ∈ Matrix.unitaryGroup n ℂ) →
      Matrix.blockDiagonal W ∈ Matrix.unitaryGroup (n × ι) ℂ := fun W hW => by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem (hW _)]
    exact Matrix.blockDiagonal_one
  have h : Matrix.blockDiagonal A = Matrix.blockDiagonal U *
      Matrix.diagonal (fun x : n × ι => (complexSingularValue (A x.2) x.1 : ℂ)) *
      (Matrix.blockDiagonal V)ᴴ := by
    rw [← Matrix.blockDiagonal_diagonal fun i j => (complexSingularValue (A i) j : ℂ),
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    exact congrArg Matrix.blockDiagonal (funext hA)
  rw [h, complexSchattenNorm_unitary_mul_diagonal_mul hp (hb U hU) (hb V hV),
    Fintype.sum_prod_type_right]
  simp only [complexSchattenNorm_ofReal_rpow hp, Complex.norm_real,
    Real.norm_of_nonneg (complexSingularValue_nonneg _ _)]

/-- Real block diagonal matrices: `‖diag (A_i)‖_{S_q}^q = Σ ‖A_i‖_{S_q}^q`, from the complex case.
-/
theorem schattenNorm_blockDiagonal_rpow {q : ℝ} (hq : 0 < q) (A : ι → Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.blockDiagonal A) ^ q =
      ∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ q := by
  have hq0 := (ENNReal.ofReal_pos.2 hq).ne'
  have h := complexSchattenNorm_blockDiagonal hq fun i => (A i).map Complex.ofReal
  rw [← Matrix.blockDiagonal_map _ _ Complex.ofReal_zero] at h
  simp only [complexSchattenNorm_map_ofReal hq0] at h
  rw [h, one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _) hq.ne']

/-- The isometric embedding of `ℓ^q (S_q)` in `S_q`, `1 ≤ q < ∞`, by block diagonal matrices. -/
noncomputable def schattenBlockDiagonal (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] :
    PiLp (ENNReal.ofReal q) (fun _ : ι => SchattenSpace (ENNReal.ofReal q) n n) →ₗᵢ[ℝ]
      SchattenSpace (ENNReal.ofReal q) (n × ι) (n × ι) where
  toFun A := SchattenSpace.ofMatrix
    (Matrix.blockDiagonal fun i => SchattenSpace.ofMatrix.symm (A i))
  map_add' A B := by
    rw [← map_add, ← Matrix.blockDiagonal_add]
    rfl
  map_smul' c A := by
    rw [RingHom.id_apply, ← map_smul, ← Matrix.blockDiagonal_smul]
    rfl
  norm_map' A := by
    have hq : 0 < q := zero_lt_one.trans_le (ENNReal.one_le_ofReal.1 Fact.out)
    change schattenNorm (ENNReal.ofReal q)
      (Matrix.blockDiagonal fun i => SchattenSpace.ofMatrix.symm (A i)) = ‖A‖
    rw [PiLp.norm_eq_sum (by rwa [ENNReal.toReal_ofReal hq.le]), ENNReal.toReal_ofReal hq.le,
      one_div, Real.eq_rpow_inv (schattenNorm_nonneg _ _)
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) hq.ne',
      schattenNorm_blockDiagonal_rpow hq]
    rfl

end BlockDiagonal

end BanachProbability
