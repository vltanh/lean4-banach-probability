module

public import BanachProbability.Noncommutative.Interpolation
public import BanachProbability.Noncommutative.Transform
public import BanachProbability.Schatten.Holder

/-!
# Duality for noncommutative martingale transforms

* Hölder's inequality in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}` for symmetric
  matrix-valued `x`, `y`, from the trace Hölder inequality pointwise and Hölder's inequality for
  the integral; equality for a norming function built from `normingElement` (measurable, as a
  continuous function of the matrix).
* The transform is self-adjoint for `τ (x y)` (`matrixTrace_ncTransform_mul`).
* Hence a strong `(r, r)` bound for `T_c` on symmetric `ℱ_N`-measurable functions gives the strong
  `(r', r')` bound with the same constant (`isStrongTypeNC_ncTransform_dual`; the duality step of
  N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002),
  Theorem 4.3).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- **Duality**: a strong `(r, r)` bound for a transform by predictable multipliers on symmetric
`ℱ_N`-measurable functions gives the strong `(r', r')` bound with the same constant,
`r' = r / (r − 1)`. -/
theorem isStrongTypeNC_ncTransform_dual [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {c : ℕ → Ω → ℝ} {N : ℕ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (h : IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r K) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) (r / (r - 1)) K := by
  sorry

end BanachProbability
