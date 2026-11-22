module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Martingale transforms

For a martingale `Y` and multipliers `φ` with `φ_{k+1}` `ℱ_k`-measurable (predictable) and bounded,
the transform `(φ • Y)_n = Σ_{k<n} φ_{k+1} (Y_{k+1} − Y_k)` (`martingaleTransform φ Y n`) is a
martingale (`martingale_martingaleTransform`), by the pull-out property of the conditional
expectation. The multipliers may take values in any `RCLike` field acting on the space.

Also: the image of a martingale under a continuous linear map is a martingale
(`martingale_map_continuousLinearMap`), and `‖Y_{k+1} − Y_k‖_{L^p} ≤ 2 ‖Y_n‖_{L^p}` for
`k < n` and `p ≥ 1` (`eLpNorm_sub_le_two_mul`), since conditional expectations are `L^p`
contractions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The martingale transform `(φ • Y)_n = Σ_{k<n} φ_{k+1} (Y_{k+1} − Y_k)` of a process `Y` by
multipliers `φ` (predictable in the applications: `φ_{k+1}` is `ℱ_k`-measurable). -/
noncomputable def martingaleTransform {𝕜 : Type*} [SMul 𝕜 E] (φ : ℕ → Ω → 𝕜) (Y : ℕ → Ω → E)
    (n : ℕ) (ω : Ω) : E :=
  ∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω)

/-- The transform of a martingale by bounded predictable multipliers is a martingale. -/
theorem martingale_martingaleTransform {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    [IsScalarTower ℝ 𝕜 E] [IsFiniteMeasure μ] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ)
    {φ : ℕ → Ω → 𝕜} (hφ : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1)))
    (hb : ∀ k, ∃ C : ℝ, ∀ ω, ‖φ (k + 1) ω‖ ≤ C) :
    Martingale (martingaleTransform φ Y) ℱ μ := by
  sorry

/-- The image of a martingale under a continuous linear map is a martingale. -/
theorem martingale_map_continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {M : ℕ → Ω → E} (hM : Martingale M ℱ μ) (T : E →L[ℝ] F) :
    Martingale (fun m ω => T (M m ω)) ℱ μ := by
  refine ⟨fun m => T.continuous.comp_stronglyMeasurable (hM.stronglyAdapted m),
    fun i j hij => ?_⟩
  filter_upwards [T.comp_condExp_comm (m := ℱ i) (hM.integrable j), hM.condExp_ae_eq hij]
    with ω h1 h2
  change μ[T ∘ M j | ℱ i] ω = T (M i ω)
  rw [← h1, Function.comp_apply, h2]

/-- The increments of a martingale are bounded in `L^p`, `p ≥ 1`, by twice its last value:
`‖Y_{k+1} − Y_k‖_{L^p} ≤ 2 ‖Y_n‖_{L^p}` for `k < n`. -/
theorem eLpNorm_sub_le_two_mul [IsFiniteMeasure μ] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {k n : ℕ} (hkn : k < n) :
    eLpNorm (fun ω => Y (k + 1) ω - Y k ω) p μ ≤ 2 * eLpNorm (Y n) p μ := by
  sorry

end BanachProbability
