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
(`martingale_map_continuousLinearMap`), so is a finite sum of martingales (`martingale_finsetSum`),
and `‖Y_{k+1} − Y_k‖_{L^p} ≤ 2 ‖Y_n‖_{L^p}` for
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
  -- the `k`-th term `φ_{k+1} (Y_{k+1} − Y_k)` is `ℱ_{k+1}`-measurable and integrable
  have hterm_meas : ∀ k, StronglyMeasurable[ℱ (k + 1)]
      fun ω => φ (k + 1) ω • (Y (k + 1) ω - Y k ω) := fun k =>
    ((hφ k).mono (ℱ.mono k.le_succ)).smul
      ((hY.stronglyAdapted (k + 1)).sub ((hY.stronglyAdapted k).mono (ℱ.mono k.le_succ)))
  have hdY_int : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) μ := fun k =>
    (hY.integrable (k + 1)).sub (hY.integrable k)
  have hterm_int : ∀ k, Integrable (fun ω => φ (k + 1) ω • (Y (k + 1) ω - Y k ω)) μ := by
    intro k
    obtain ⟨C, hC⟩ := hb k
    exact (hdY_int k).bdd_smul C ((hφ k).mono (ℱ.le k)).aestronglyMeasurable (ae_of_all _ hC)
  have hsucc : ∀ i, martingaleTransform φ Y (i + 1) - martingaleTransform φ Y i =
      fun ω => φ (i + 1) ω • (Y (i + 1) ω - Y i ω) := by
    intro i
    funext ω
    simp [martingaleTransform, Finset.sum_range_succ]
  refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_) (fun n => ?_) (fun i => ?_)
  · change StronglyMeasurable[ℱ n]
      (fun ω => ∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω))
    exact Finset.stronglyMeasurable_fun_sum _ fun k hk =>
      (hterm_meas k).mono (ℱ.mono (Finset.mem_range.1 hk))
  · exact integrable_finsetSum _ fun k _ => hterm_int k
  · -- the pull-out property for the `ℝ`-bilinear map `(c, v) ↦ c • v` on `𝕜 × E`
    rw [hsucc]
    have hdY : μ[fun ω => Y (i + 1) ω - Y i ω | ℱ i] =ᵐ[μ] 0 := by
      filter_upwards [condExp_sub (hY.integrable (i + 1)) (hY.integrable i) (ℱ i),
        hY.condExp_ae_eq i.le_succ, hY.condExp_ae_eq (le_refl i)] with ω h1 h2 h3
      change μ[Y (i + 1) - Y i | ℱ i] ω = 0
      rw [h1, Pi.sub_apply, h2, h3, sub_self]
    filter_upwards [condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.lsmul ℝ 𝕜)
      (hφ i) (hterm_int i) (hdY_int i), hdY] with ω h1 h2
    simpa [h2] using h1

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

/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum {ι : Type*} (s : Finset ι) {M : ι → ℕ → Ω → E}
    (hM : ∀ i ∈ s, Martingale (M i) ℱ μ) : Martingale (fun m ω => ∑ i ∈ s, M i m ω) ℱ μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert martingale_zero E ℱ μ using 1
    funext m ω; simp
  | insert a s ha ih =>
    have := (hM a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hM i (Finset.mem_insert_of_mem hi))
    convert this using 1
    funext m ω; simp [Finset.sum_insert ha]

/-- The increments of a martingale are bounded in `L^p`, `p ≥ 1`, by twice its last value:
`‖Y_{k+1} − Y_k‖_{L^p} ≤ 2 ‖Y_n‖_{L^p}` for `k < n`. -/
theorem eLpNorm_sub_le_two_mul [IsFiniteMeasure μ] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {k n : ℕ} (hkn : k < n) :
    eLpNorm (fun ω => Y (k + 1) ω - Y k ω) p μ ≤ 2 * eLpNorm (Y n) p μ := by
  -- `Y_j = E[Y_n | ℱ_j]` for `j ≤ n`, and conditional expectations are `L^p` contractions
  have hle : ∀ j, j ≤ n → eLpNorm (Y j) p μ ≤ eLpNorm (Y n) p μ := fun j hj => by
    rw [← eLpNorm_congr_ae (hY.condExp_ae_eq hj)]
    exact eLpNorm_condExp_le_eLpNorm _ hp
  calc eLpNorm (fun ω => Y (k + 1) ω - Y k ω) p μ
      ≤ eLpNorm (Y (k + 1)) p μ + eLpNorm (Y k) p μ := eLpNorm_sub_le (f := Y (k + 1)) hp
    _ ≤ eLpNorm (Y n) p μ + eLpNorm (Y n) p μ := add_le_add (hle _ hkn) (hle _ hkn.le)
    _ = 2 * eLpNorm (Y n) p μ := (two_mul _).symm

end BanachProbability
