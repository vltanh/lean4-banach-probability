module

public import BanachProbability.TypeTwo.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# K-convexity and type 2

The Rademacher projection of `f : {±1}^N → X` is `Σ_k ε_k E (ε_k f)` (`rademacherProj f`). A normed
space
`X` is K-convex with constant `K` in `L^p` when `‖Σ_k ε_k E (ε_k f)‖_{L^p} ≤ K ‖f‖_{L^p}` for all
`N` and `f` (`IsKConvexBound X p K`; Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach
spaces II* (2017), Section 7.4).

`IsTypeTwoBound.isKConvexBound`: a space of type 2 with constant `τ` is K-convex in `L²`, with
constant `√(π/2) τ` (HNVW II, Proposition 7.4.22, p. 124; Maurey–Pisier (1976), Remark 2.10). The
steps are HNVW's: type 2 gives Gaussian type 2 with the same constant (Proposition 7.1.18);
Rademacher sums are dominated by Gaussian sums, with the factor `1 / E |g| = √(π/2)` (Proposition
6.1.15); and Gaussian sums over an orthonormal system are compared by the rotation invariance of the
Gaussian measure (Theorem 7.1.20).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BanachProbability

open SignCube

variable {N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The expectation `E (ε_k f)` of a function on the sign cube. -/
noncomputable def rademacherCoeff (f : (Fin N → Bool) → X) (k : Fin N) : X :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η

/-- The Rademacher projection `Σ_k ε_k E (ε_k f)`. -/
noncomputable def rademacherProj (f : (Fin N → Bool) → X) (ε : Fin N → Bool) : X :=
  ∑ k, coin (ε k) • rademacherCoeff f k

variable (X) in
/-- `X` is K-convex in `L^p` with constant `K`. -/
def IsKConvexBound (p K : ℝ) : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → X),
    SignCube.lpNorm (fun y => ‖y‖) p (rademacherProj f) ≤ K * SignCube.lpNorm (fun y => ‖y‖) p f

/-- Type 2 implies Gaussian type 2, with the same constant (HNVW II, Proposition 7.1.18):
`E ‖Σ g_i y_i‖² ≤ τ² Σ ‖y_i‖²` for independent standard Gaussian `g_i`. -/
theorem IsTypeTwoBound.integral_stdGaussian_le {τ : ℝ} (h : IsTypeTwoBound X τ) {ι : Type*}
    [Fintype ι] (y : ι → X) :
    ∫ g, ‖∑ i, g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤ τ ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
  sorry

/-- Rademacher sums are dominated by Gaussian sums (HNVW II, Proposition 6.1.15, `p = 2`):
`E ‖Σ ε_k x_k‖² ≤ (π/2) E ‖Σ g_k x_k‖²`. -/
theorem avg_norm_sq_le_integral_stdGaussian (x : Fin N → X) :
    (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • x k‖ ^ 2) ≤
      Real.pi / 2 * ∫ g, ‖∑ k, g k • x k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  sorry

/-- The extremality of Gaussian sums (HNVW II, Theorem 7.1.20), for the orthonormal system of the
signs: with `x_k = E (ε_k f)`, `E ‖Σ_k g_k x_k‖² ≤ E ‖Σ_η g_η 2^{−N/2} f (η)‖²`. -/
theorem integral_stdGaussian_rademacherCoeff_le (f : (Fin N → Bool) → X) :
    ∫ g, ‖∑ k, g k • rademacherCoeff f k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      ∫ g, ‖∑ η, g η • √((2 : ℝ) ^ N)⁻¹ • f η‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin N → Bool)) := by
  sorry

/-- **Type 2 implies K-convexity** (HNVW II, Proposition 7.4.22; Maurey–Pisier (1976), Remark 2.10).
-/
theorem IsTypeTwoBound.isKConvexBound {τ : ℝ} (hτ : 0 ≤ τ) (h : IsTypeTwoBound X τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) := by
  sorry

end BanachProbability
