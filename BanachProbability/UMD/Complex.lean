module

public import BanachProbability.UMD.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Complex UMD constants

For a complex Banach space `X` and `p ∈ (1, ∞)`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)` (Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Proposition 4.2.10; Yaroslavtsev, *Even Fourier multipliers and
martingale transforms in infinite dimensions*, Indag. Math. 29 (2018), Lemma 3.2), for general
filtrations.

The first inequality holds because real signs are unimodular complex numbers. The second is the
standard averaging argument: for `|λ| = 1`, `λ = e^{iθ}`,
`(1 / 2π) ∫₀^{2π} sgn cos (θ − φ) e^{iφ} dφ = (2 / π) e^{iθ}` (`integral_signOf_cos`), and for
each fixed `φ` the signs `σ_k^φ = sgn cos (θ_k − φ)` are predictable. The integral is replaced by
Riemann sums over `M` equally spaced angles, with a uniform error `O (1 / M)`
(`riemannSum_signOf_cos`), so that no joint measurability in `(φ, ω)` is needed:
`‖Σ λ_k dY_k‖_p ≤ (π / 2) max_φ ‖Σ σ_k^φ dY_k‖_p + O (1 / M) · 2n ‖Y_n‖_p`, and `M → ∞`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

/-- The sign of a real number, with `0 ↦ 1`: a `±1`-valued function. -/
noncomputable def signOf (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem signOf_eq_one_or_eq_neg_one (t : ℝ) : signOf t = 1 ∨ signOf t = -1 := by
  unfold signOf
  split_ifs <;> simp

/-- `(1 / 2π) ∫₀^{2π} sgn cos (θ − φ) e^{iφ} dφ = (2 / π) e^{iθ}`. -/
theorem integral_signOf_cos (θ : ℝ) :
    ((2 * Real.pi)⁻¹ : ℂ) * ∫ φ in (0 : ℝ)..2 * Real.pi,
        (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I) =
      (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I) := by
  sorry

/-- The Riemann sums of `φ ↦ sgn cos (θ − φ) e^{iφ}` over `M` equally spaced angles converge to
`(2 / π) e^{iθ}` uniformly in `θ`, with error `O (1 / M)` (both `|cos|` and `sgn · sin` are of
bounded variation). -/
theorem riemannSum_signOf_cos : ∃ C : ℝ, ∀ M : ℕ, 0 < M → ∀ θ : ℝ,
    ‖(M : ℂ)⁻¹ * ∑ j : Fin M, (signOf (Real.cos (θ - 2 * Real.pi * j / M)) : ℂ) *
        Complex.exp ((2 * Real.pi * j / M : ℝ) * Complex.I) -
      (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ C / M := by
  sorry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- `UMD_p (X) ≤ UMD_{ℂ,p} (X)`: real signs are unimodular complex multipliers. -/
theorem umdConst_le_complexUMDConst {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p := by
  sorry

/-- `UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`, by averaging over the signs `sgn cos (θ_k − φ)`. -/
theorem complexUMDConst_le_pi_div_two_mul {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p := by
  sorry

/-- **Complex UMD constants** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.10;
Yaroslavtsev 2018, Lemma 3.2): `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
theorem umdConst_le_complexUMDConst_le {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  ⟨umdConst_le_complexUMDConst hp, complexUMDConst_le_pi_div_two_mul hp⟩

end BanachProbability
