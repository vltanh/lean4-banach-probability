module

public import BanachProbability.UMD.Hilbert
public import BanachProbability.UMD.Maurey.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `L^p` spaces of UMD spaces are UMD

For any measure space `(S, μ)`, any Banach space `B` and `p ∈ (1, ∞)`,
`UMD_p (L^p (μ; B)) ≤ UMD_p (B)`; in particular `UMD_p (L^p (μ; ℂ)) ≤ p* − 1` and the complex
`L^p (μ)` is UMD (Pisier, *Martingales in Banach spaces* (2016), Corollary 5.22, "by Fubini").

The proof is the dyadic one, which needs neither σ-finiteness nor joint measurability. A
Paley–Walsh martingale with values in `L^p (μ; B)` takes finitely many values; choosing
representatives, the finitely many linear relations among them hold off one null set, so for
almost every `s` the evaluations `ε ↦ ξ_k (ε) (s)` form a `B`-valued Paley–Walsh martingale and the
transform commutes with evaluation. The finite averages commute with the integral:
`E_ε ‖F (ε)‖_{L^p}^p = ∫ E_ε ‖F (ε) (s)‖^p dμ (s)`, and the dyadic bound of `B` applied pointwise
in `s` gives `UMD_p^Δ (L^p (μ; B)) ≤ UMD_p^Δ (B)` (`dyadicUMDConst_Lp_le`). Maurey's theorem gives
the full constants.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

/-- `UMD_p^Δ (L^p (μ; B)) ≤ UMD_p^Δ (B)`, for every measure `μ`. -/
theorem dyadicUMDConst_Lp_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    dyadicUMDConst (Lp B p μ) p.toReal ≤ dyadicUMDConst B p.toReal := by
  sorry

/-- `UMD_p (L^p (μ; B)) ≤ UMD_p (B)`, for every measure `μ` and every Banach space `B`. -/
theorem umdConst_Lp_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp B p μ) p.toReal ≤ umdConst B p.toReal := by
  sorry

/-- The complex `L^p (μ)` is UMD with `UMD_p (L^p (μ; ℂ)) ≤ p* − 1`, for every measure `μ`. -/
theorem umdConst_Lp_complex_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp ℂ p μ) p.toReal ≤ ENNReal.ofReal (pStar p.toReal - 1) := by
  sorry

/-- **`L^p` is UMD** (Pisier 2016, Corollary 5.22): for every measure space and `p ∈ (1, ∞)`, the
complex `L^p (μ)` has `UMD_p (L^p (μ)) < ∞`. -/
theorem umdConst_Lp_complex_lt_top (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp ℂ p μ) p.toReal < ⊤ :=
  (umdConst_Lp_complex_le μ p hp hpt).trans_lt ENNReal.ofReal_lt_top

end BanachProbability
