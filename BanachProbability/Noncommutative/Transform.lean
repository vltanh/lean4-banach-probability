module

public import BanachProbability.Noncommutative.CondExp
public import Mathlib.Probability.Process.Filtration

/-!
# Martingale transforms on `L^∞ (Ω) ⊗ M_n`

For a filtration `ℱ` of a probability space and `x : Ω → M_n (ℝ)`, the martingale
`x_k = E_k x = 𝔼 [x | ℱ_k] ⊗ Id` has the differences `d_k x = E_{k+1} x − E_k x`, and its transform
by multipliers `c_k` is
`T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` (`ncTransform`), the source's
`x_1 + Σ_{k=2}^N ξ_{k−1} dx_k` (N. Randrianantoanina, *Non-commutative martingale transforms*,
J. Funct. Anal. 194 (2002), Theorem 3.1, with its `x_1, …, x_N` our `E_0 x, …, E_N x`).

The multipliers are scalar: `c_k : Ω → ℝ` is `ℱ_k`-measurable with `|c_k| ≤ 1`. In
`N = L^∞ (Ω) ⊗ M_n` an element commutes with `N_{k+1} = L^∞ (Ω, ℱ_{k+1}) ⊗ M_n` exactly when it
lies in `L^∞ (Ω) ⊗ 1`, so these are the multipliers of the source's Theorem 3.1 (its hypothesis
(i) that `ξ_{k−1}` commutes with `N_k`, and (ii) `‖ξ‖_∞ ≤ 1`), for real matrices.

Facts: `T_c x` is `ℱ_N`-measurable and in `L^p` with `x` (`MatrixMemLp.ncTransform`), `T_c` is
additive a.e. (`ncTransform_add`), it is a contraction of `L² (τ)` (`matrixTrace_ncTransform_le`,
by the orthogonality of the martingale differences, entrywise), and it is self-adjoint for the
trace pairing `τ (x y)` (`matrixTrace_ncTransform_mul`), since
`τ (T_c x · y) = τ (E_0 x E_0 y) + Σ_k τ (c_k d_k x d_k y)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : MeasureTheory.Filtration ℕ mΩ}
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The martingale transform `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)`. -/
noncomputable def ncTransform (ℱ : MeasureTheory.Filtration ℕ mΩ) (μ : Measure Ω)
    (c : ℕ → Ω → ℝ) (N : ℕ) (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω => matrixCondExp (ℱ 0) μ x ω +
    ∑ k ∈ Finset.range N, c k ω • (matrixCondExp (ℱ (k + 1)) μ x ω - matrixCondExp (ℱ k) μ x ω)

variable {c : ℕ → Ω → ℝ} {N : ℕ}

theorem measurable_ncTransform (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (x : Ω → Matrix n n ℝ) :
    Measurable[ℱ N] (ncTransform ℱ μ c N x) := by
  sorry

theorem MatrixMemLp.ncTransform [IsFiniteMeasure μ] (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hp : 1 ≤ p) : MatrixMemLp (ncTransform ℱ μ c N x) p μ := by
  sorry

theorem ncTransform_add {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    ncTransform ℱ μ c N (x + y) =ᵐ[μ] ncTransform ℱ μ c N x + ncTransform ℱ μ c N y := by
  sorry

theorem ncTransform_sub {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    ncTransform ℱ μ c N (x - y) =ᵐ[μ] ncTransform ℱ μ c N x - ncTransform ℱ μ c N y := by
  sorry

theorem ncTransform_neg (x : Ω → Matrix n n ℝ) :
    ncTransform ℱ μ c N (-x) =ᵐ[μ] -ncTransform ℱ μ c N x := by
  sorry

theorem ncTransform_smul (a : ℝ) (x : Ω → Matrix n n ℝ) :
    ncTransform ℱ μ c N (a • x) =ᵐ[μ] a • ncTransform ℱ μ c N x := by
  sorry

/-- The transform of an (a.e.) symmetric function is (a.e.) symmetric. -/
theorem isHermitian_ncTransform {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (ncTransform ℱ μ c N x ω).IsHermitian := by
  sorry

/-- A transform by predictable multipliers with `|c_k| ≤ 1` is a contraction of `L² (τ)`:
`τ ((T_c x)ᵀ T_c x) ≤ τ (xᵀ x)` for `ℱ_N`-measurable `x`. -/
theorem matrixTrace_ncTransform_le [IsFiniteMeasure μ] (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {x : Ω → Matrix n n ℝ} (hx : Measurable[ℱ N] x)
    (hx2 : MatrixMemLp x 2 μ) :
    matrixTrace μ (fun ω => (ncTransform ℱ μ c N x ω)ᵀ * ncTransform ℱ μ c N x ω) ≤
      matrixTrace μ (fun ω => (x ω)ᵀ * x ω) := by
  sorry

/-- The transform is self-adjoint for the trace pairing: `τ (T_c x · y) = τ (x · T_c y)` for
`x ∈ L^p`, `y ∈ L^q`, `1/p + 1/q = 1`. -/
theorem matrixTrace_ncTransform_mul [IsFiniteMeasure μ] (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {p q : ℝ≥0∞} [p.HolderConjugate q] {x y : Ω → Matrix n n ℝ}
    (hx : MatrixMemLp x p μ) (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => ncTransform ℱ μ c N x ω * y ω) =
      matrixTrace μ (fun ω => x ω * ncTransform ℱ μ c N y ω) := by
  sorry

end BanachProbability
