module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Schatten norms of real matrices

For a real `m × n` matrix `A`, the singular values `s_i (A) = √λ_i (Aᵀ A)`, `i : n`, are the
square roots of the eigenvalues of the positive semidefinite matrix `Aᵀ A` (`singularValue`; when
`n` is larger than `m` the extra ones are `0`, which changes no Schatten norm). The Schatten
`q`-norm is `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞` and `‖A‖_{S_∞} = max_i s_i`
(`schattenNorm`, with `q : ℝ≥0∞`). For `q ≥ 1` it is a norm (`schattenNorm_add_le`, in
`BanachProbability.Schatten.Triangle`), and `SchattenSpace q m n` is the corresponding normed
space (`BanachProbability.Schatten.Space`).

Basic facts: nonnegativity, homogeneity, definiteness, the Frobenius identity
`‖A‖_{S_2}² = Σ A_{ij}²`, invariance under transposition and orthogonal conjugation,
`‖Aᵀ A‖_{S_{q/2}} = ‖A‖_{S_q}²`, and the comparison of the norms for different exponents.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The singular values of `A ∈ ℝ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᵀ A)`. -/
noncomputable def singularValue (A : Matrix m n ℝ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`, `‖A‖_{S_∞} = max_i s_i`. -/
noncomputable def schattenNorm (q : ℝ≥0∞) (A : Matrix m n ℝ) : ℝ :=
  if q = ⊤ then ⨆ i, singularValue A i else (∑ i, singularValue A i ^ q.toReal) ^ (1 / q.toReal)

theorem singularValue_nonneg (A : Matrix m n ℝ) (i : n) : 0 ≤ singularValue A i :=
  Real.sqrt_nonneg _

theorem schattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n ℝ) : 0 ≤ schattenNorm q A := by
  sorry

theorem schattenNorm_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (A : Matrix m n ℝ) :
    schattenNorm q A ^ q.toReal = ∑ i, singularValue A i ^ q.toReal := by
  sorry

@[simp] theorem schattenNorm_zero {q : ℝ≥0∞} (hq : q ≠ 0) :
    schattenNorm q (0 : Matrix m n ℝ) = 0 := by
  sorry

theorem schattenNorm_eq_zero_iff {q : ℝ≥0∞} (hq : q ≠ 0) {A : Matrix m n ℝ} :
    schattenNorm q A = 0 ↔ A = 0 := by
  sorry

theorem schattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : ℝ) (A : Matrix m n ℝ) :
    schattenNorm q (c • A) = |c| * schattenNorm q A := by
  sorry

theorem schattenNorm_neg (q : ℝ≥0∞) (A : Matrix m n ℝ) :
    schattenNorm q (-A) = schattenNorm q A := by
  sorry

/-- The Frobenius identity `‖A‖_{S_2}² = Σ_{ij} A_{ij}² = tr (Aᵀ A)`. -/
theorem schattenNorm_two_sq (A : Matrix m n ℝ) :
    schattenNorm 2 A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  sorry

theorem schattenNorm_transpose [DecidableEq m] (q : ℝ≥0∞) (A : Matrix m n ℝ) :
    schattenNorm q Aᵀ = schattenNorm q A := by
  sorry

/-- `‖Aᵀ A‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem schattenNorm_transpose_mul_self {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℝ) :
    schattenNorm (q / 2) (Aᵀ * A) = schattenNorm q A ^ 2 := by
  sorry

/-- Invariance under orthogonal conjugation: `‖U A Uᵀ‖_{S_q} = ‖A‖_{S_q}`. -/
theorem schattenNorm_conj {U : Matrix n n ℝ} (hU : U ∈ Matrix.orthogonalGroup n ℝ) (q : ℝ≥0∞)
    (A : Matrix n n ℝ) : schattenNorm q (U * A * Uᵀ) = schattenNorm q A := by
  sorry

/-- The Schatten norms decrease in the exponent: `‖A‖_{S_r} ≤ ‖A‖_{S_q}` for `0 < q ≤ r`. -/
theorem schattenNorm_anti {q r : ℝ≥0∞} (hq : q ≠ 0) (hqr : q ≤ r) (A : Matrix m n ℝ) :
    schattenNorm r A ≤ schattenNorm q A := by
  sorry

/-- The reverse comparison: `‖A‖_{S_q} ≤ (#n)^{1/q − 1/r} ‖A‖_{S_r}` for `0 < q ≤ r < ∞`. -/
theorem schattenNorm_le_card_rpow_mul {q r : ℝ} (hq : 0 < q) (hqr : q ≤ r) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A ≤
      (Fintype.card n : ℝ) ^ (1 / q - 1 / r) * schattenNorm (ENNReal.ofReal r) A := by
  sorry

end BanachProbability
