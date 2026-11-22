module

public import BanachProbability.UMD.Defs
public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Hilbert spaces are UMD

For a real Hilbert space `H` and `p ∈ (1, ∞)`, `UMD_p (H) ≤ p* − 1` with
`p* = max (p, p / (p − 1))` (Burkholder, *Boundary value problems and sharp inequalities for
martingale transforms*, Ann. Probab. 12 (1984); the constant is sharp). A transform by predictable
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
  sorry

/-- The dyadic form of Burkholder's theorem: `UMD_p^Δ (H) ≤ p* − 1`. -/
theorem dyadicUMDConst_le_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst H p ≤ ENNReal.ofReal (pStar p - 1) := by
  sorry

end BanachProbability
