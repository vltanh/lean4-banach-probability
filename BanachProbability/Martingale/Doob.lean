module

public import BanachProbability.SignCube.Bridge
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Doob's `L^r` maximal inequality

For a nonnegative submartingale `f` and `r ∈ (1, ∞)`,
`‖max_{k ≤ n} f_k‖_{L^r} ≤ r' ‖f_n‖_{L^r}`, `r' = r / (r − 1)`
(`eLpNorm_runningMax_le_of_submartingale`). Applied to the submartingale `‖Y_n‖` of a
Banach-space-valued martingale (conditional Jensen, `norm_condExp_le`), it gives
`‖Y*_n‖_{L^r} ≤ r' ‖Y_n‖_{L^r}` (`eLpNorm_runningMax_norm_le`), and on the sign cube the same for
Paley–Walsh martingales (`SignCube.lpNorm_runningMax_le`).

The proof is the standard one: Doob's weak-type estimate (Mathlib's `MeasureTheory.maximal_ineq`),
the layer-cake formula (`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`) and Hölder's
inequality. The constant `r'` is sharp and is used as such by the extrapolation of the UMD
property.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

/-- The running maximum `max_{k ≤ n} f_k (ω)`. -/
noncomputable def runningMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω

theorem le_runningMax (f : ℕ → Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    f k ω ≤ runningMax f n ω :=
  Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- **Doob's `L^r` inequality** for nonnegative submartingales:
`‖max_{k ≤ n} f_k‖_{L^r} ≤ (r / (r − 1)) ‖f_n‖_{L^r}`, `r ∈ (1, ∞)`. -/
theorem eLpNorm_runningMax_le_of_submartingale [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {r : ℝ} (hr : 1 < r) (n : ℕ) :
    eLpNorm (runningMax f n) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (r / (r - 1)) * eLpNorm (f n) (ENNReal.ofReal r) μ := by
  sorry

/-- **Doob's `L^r` inequality** for martingales with values in a Banach space:
`‖max_{k ≤ n} ‖Y_k‖‖_{L^r} ≤ (r / (r − 1)) ‖Y_n‖_{L^r}`, `r ∈ (1, ∞)`. -/
theorem eLpNorm_runningMax_norm_le [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {r : ℝ}
    (hr : 1 < r) (n : ℕ) :
    eLpNorm (runningMax (fun k ω => ‖Y k ω‖) n) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (r / (r - 1)) * eLpNorm (Y n) (ENNReal.ofReal r) μ := by
  sorry

/-- **Doob's `L^r` inequality** for Paley–Walsh martingales on the sign cube (no completeness of
the space of values is needed: the values lie in a finite-dimensional subspace). -/
theorem SignCube.lpNorm_runningMax_le {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ξ : Fin N → (Fin N → Bool) → E} (hξ : SignCube.IsPredictable ξ) {r : ℝ}
    (hr : 1 < r) (n : ℕ) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) r
        (runningMax (fun k ε => ‖SignCube.paleyWalsh ξ k ε‖) n) ≤
      r / (r - 1) * SignCube.lpNorm (fun x => ‖x‖) r (SignCube.paleyWalsh ξ n) := by
  sorry

end BanachProbability
