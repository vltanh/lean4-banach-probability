module

public import BanachProbability.Schatten.Spectral
public import Mathlib.Data.Matrix.Block

/-!
# The Hermitian dilation

The dilation of `A ∈ ℝ^{m×n}` is the symmetric matrix `D (A) = [[0, A], [Aᵀ, 0]]` on `m ⊕ n`
(`dilation`, through `Matrix.fromBlocks`). It is linear, `D (A) D (B) = diag (A Bᵀ, Aᵀ B)`, and its
eigenvalues are `±s_i (A)` (and zeros): `‖D (A)‖_{S_q}^q = 2 ‖A‖_{S_q}^q`
(`schattenNorm_dilation_rpow`), since `D (A)² = diag (A Aᵀ, Aᵀ A)` is block diagonal and `A Aᵀ` and
`Aᵀ A` have the same nonzero eigenvalues. This is how statements about symmetric matrices pass to
all real matrices (Mackey–Jordan–Chen–Farrell–Tropp, Ann. Probab. 42 (2014), §8; Randrianantoanina,
J. Funct. Anal. 194 (2002), for martingales).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Hermitian dilation `D (A) = [[0, A], [Aᵀ, 0]]`. -/
def dilation (A : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks 0 A Aᵀ 0

/-- The dilation as a linear map. -/
def dilationLinearMap : Matrix m n ℝ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℝ where
  toFun := dilation
  map_add' A B := by
    simp [dilation, Matrix.fromBlocks_add]
  map_smul' c A := by
    simp [dilation, Matrix.fromBlocks_smul]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem dilation_isHermitian (A : Matrix m n ℝ) : (dilation A).IsHermitian := by
  sorry

omit [DecidableEq m] [DecidableEq n] in
theorem dilation_mul_dilation (A B : Matrix m n ℝ) :
    dilation A * dilation B = Matrix.fromBlocks (A * Bᵀ) 0 0 (Aᵀ * B) := by
  simp [dilation, Matrix.fromBlocks_multiply]

/-- `‖A Aᵀ‖_{S_q} = ‖Aᵀ A‖_{S_q}`: the two have the same nonzero eigenvalues. -/
theorem schattenNorm_mul_transpose_self (q : ENNReal) (A : Matrix m n ℝ) :
    schattenNorm q (A * Aᵀ) = schattenNorm q (Aᵀ * A) := by
  sorry

/-- The Schatten norm of a block-diagonal matrix:
`‖diag (B, C)‖_{S_q}^q = ‖B‖_{S_q}^q + ‖C‖_{S_q}^q`. -/
theorem schattenNorm_fromBlocks_rpow {q : ℝ} (hq : 0 < q) (B : Matrix m m ℝ) (C : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.fromBlocks B 0 0 C) ^ q =
      schattenNorm (ENNReal.ofReal q) B ^ q + schattenNorm (ENNReal.ofReal q) C ^ q := by
  sorry

/-- `‖D (A)‖_{S_q}^q = 2 ‖A‖_{S_q}^q`. -/
theorem schattenNorm_dilation_rpow {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) (dilation A) ^ q =
      2 * schattenNorm (ENNReal.ofReal q) A ^ q := by
  sorry

omit [DecidableEq m] [DecidableEq n] in
/-- The square function of a family of dilations is block diagonal:
`Σ_i D (x_i)² = diag (Σ_i x_i x_iᵀ, Σ_i x_iᵀ x_i)`. -/
theorem sum_dilation_mul_self {ι : Type*} (s : Finset ι) (x : ι → Matrix m n ℝ) :
    ∑ i ∈ s, dilation (x i) * dilation (x i) =
      Matrix.fromBlocks (∑ i ∈ s, x i * (x i)ᵀ) 0 0 (∑ i ∈ s, (x i)ᵀ * x i) := by
  sorry

end BanachProbability
