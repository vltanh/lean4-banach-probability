module

public import BanachProbability.UMD.Defs
public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Hilbert spaces are UMD

For a real Hilbert space `H` and `p ∈ (1, ∞)`, `UMD_p (H) ≤ p* − 1` with
`p* = max (p, p / (p − 1))` (Burkholder, *Sharp inequalities for martingales and stochastic
integrals*, Astérisque 157–158 (1988), Theorem 1.1; for real-valued martingales, Burkholder,
*Boundary value problems and sharp inequalities for martingale transforms*, Ann. Probab. 12 (1984),
Theorem 1.1; the constant is sharp, `Martingale/Osekowski/Sharpness`). A transform by predictable
signs is a martingale (`martingale_martingaleTransform`) whose increments have the same norms as
those of the original martingale, so Burkholder's inequality
(`BanachProbability.Burkholder.inequality_of_subordinate`) applies to the pair. The complex
numbers, as the real Hilbert space `ℝ²`, are a case.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Burkholder's theorem**: a real Hilbert space is `UMD_p` with constant `p* − 1`. -/
theorem umdConst_le_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    umdConst H p ≤ ENNReal.ofReal (pStar p - 1) := by
  refine umdConst_le_of_isUMDBound fun Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n => ?_
  have hσ1 : ∀ k ω, ‖σ k ω‖ = 1 := fun k ω => by rcases hσ k ω with h | h <;> simp [h]
  -- the transform `X = Σ σ_{k+1} (Y_{k+1} − Y_k)` is a martingale started at `0`
  have hX : Martingale (martingaleTransform σ Y) ℱ μ :=
    martingale_martingaleTransform (𝕜 := ℝ) hY hσm fun k => ⟨1, fun ω => (hσ1 (k + 1) ω).le⟩
  have hX0 : ∀ ω, martingaleTransform σ Y 0 ω = 0 := fun ω => by simp [martingaleTransform]
  -- `‖X_{k+1} − X_k‖ = |σ_{k+1}| ‖Y_{k+1} − Y_k‖ = ‖Y_{k+1} − Y_k‖`
  have hsub : ∀ k, ∀ᵐ ω ∂μ, ‖martingaleTransform σ Y (k + 1) ω - martingaleTransform σ Y k ω‖ ≤
      ‖Y (k + 1) ω - Y k ω‖ := fun k => Filter.Eventually.of_forall fun ω => by
    simp only [martingaleTransform, Finset.sum_range_succ, add_sub_cancel_left, norm_smul,
      hσ1, one_mul, le_refl]
  have key := Burkholder.inequality_of_subordinate hp hX hY hX0 hY0 hsub n
  rwa [← eLpNorm_norm _ (hX.integrable n).aestronglyMeasurable,
    ← eLpNorm_norm _ (hY.integrable n).aestronglyMeasurable] at key

/-- The dyadic form of Burkholder's theorem: `UMD_p^Δ (H) ≤ p* − 1`. -/
theorem dyadicUMDConst_le_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst H p ≤ ENNReal.ofReal (pStar p - 1) :=
  (dyadicUMDConst_le_umdConst hp).trans (umdConst_le_of_innerProductSpace hp)

end BanachProbability
