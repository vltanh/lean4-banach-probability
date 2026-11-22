module

public import BanachProbability.SignCube.Bridge
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Doob's `L^r` maximal inequality

For a nonnegative submartingale `f` and `r ∈ (1, ∞)`,
`‖max_{k ≤ n} f_k‖_{L^r} ≤ r' ‖f_n‖_{L^r}`, `r' = r / (r − 1)`
(`eLpNorm_runningMax_le_of_submartingale`). Applied to the submartingale `‖Y_n‖` of a
Banach-space-valued martingale (conditional Jensen, `norm_condExp_le`), it gives
`‖Y*_n‖_{L^r} ≤ r' ‖Y_n‖_{L^r}` (`eLpNorm_runningMax_norm_le`), and on the sign cube the same for
Paley–Walsh martingales (`SignCube.lpNorm_runningMax_le`).

The proof is the standard one: Doob's weak-type estimate (Mathlib's `MeasureTheory.maximal_ineq`),
the layer-cake formula (`MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`, for `μ` and,
in place of Tonelli's theorem, for the measure `f_n dμ`) and Hölder's inequality. The constant
`r'` is sharp and is used as such by the extrapolation of the UMD property.
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

/-- The `L^r` norm of a nonnegative function as a lintegral:
`‖g‖_{L^r} = (∫ g^r)^{1/r}`. -/
private lemma eLpNorm_eq_lintegral_ofReal_rpow {g : Ω → ℝ} (hg : ∀ ω, 0 ≤ g ω)
    (hgm : AEStronglyMeasurable g μ) {r : ℝ} (hr : 0 < r) :
    eLpNorm g (ENNReal.ofReal r) μ = (∫⁻ ω, ENNReal.ofReal (g ω ^ r) ∂μ) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top hgm,
    ENNReal.toReal_ofReal hr.le]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_of_nonneg (hg ω), ENNReal.ofReal_rpow_of_nonneg (hg ω) hr.le]

/-- Doob's weak-type estimate (`maximal_ineq`) integrated by the layer-cake formula: for the
running maximum `M` of a nonnegative submartingale and `r > 1`,
`E M^r = r ∫_0^∞ t^{r−1} μ{M ≥ t} dt ≤ r ∫_0^∞ t^{r−2} ∫_{M ≥ t} f_n dt`
`= (r / (r − 1)) E[f_n M^{r−1}]`.
The last equality (Tonelli and `∫_0^M t^{r−2} dt = M^{r−1} / (r − 1)`) is the layer-cake formula
for the measure `f_n dμ`. -/
private lemma lintegral_rpow_runningMax_le [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {r : ℝ} (hr : 1 < r) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (runningMax f n ω ^ r) ∂μ ≤
      ENNReal.ofReal (r / (r - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) * ENNReal.ofReal (runningMax f n ω ^ (r - 1)) ∂μ := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  set M := runningMax f n with hM
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hM_meas : Measurable M := Finset.measurable_range_sup'' fun k _ => hmeas k
  have hM_nonneg : ∀ ω, 0 ≤ M ω := fun ω =>
    (hnonneg 0 ω).trans (le_runningMax f (Nat.zero_le n) ω)
  -- the measure `f_n dμ`
  set ν := μ.withDensity fun ω => ENNReal.ofReal (f n ω) with hν
  -- the weak-type estimate `t μ{M ≥ t} ≤ ∫_{M ≥ t} f_n`
  have hweak : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤ ν {ω | t ≤ M ω} := by
    intro t ht
    have h := maximal_ineq hf hnonneg (ε := t.toNNReal) n
    rw [Real.coe_toNNReal t ht] at h
    rw [hν, withDensity_apply _ (s := {ω | t ≤ M ω}) (hM_meas measurableSet_Ici),
      ← ofReal_integral_eq_lintegral_ofReal (hf.integrable n).integrableOn
        (ae_of_all _ fun ω => hnonneg n ω)]
    exact h
  calc ∫⁻ ω, ENNReal.ofReal (M ω ^ r) ∂μ
      = ENNReal.ofReal r *
          ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ M ω} * ENNReal.ofReal (t ^ (r - 1)) :=
        lintegral_rpow_eq_lintegral_meas_le_mul μ (ae_of_all _ hM_nonneg) hM_meas.aemeasurable hr0
    _ ≤ ENNReal.ofReal r *
          ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ M ω} * ENNReal.ofReal (t ^ (r - 1 - 1)) := by
        gcongr ENNReal.ofReal r * ?_
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := ht
        rw [show t ^ (r - 1) = t * t ^ (r - 1 - 1) by
            rw [Real.rpow_sub_one ht'.ne' (r - 1)]; field_simp,
          ENNReal.ofReal_mul ht'.le, ← mul_assoc, mul_comm (μ _)]
        gcongr
        exact hweak t ht'.le
    _ = ENNReal.ofReal r / ENNReal.ofReal (r - 1) *
          ∫⁻ ω, ENNReal.ofReal (M ω ^ (r - 1)) ∂ν := by
        rw [lintegral_rpow_eq_lintegral_meas_le_mul ν (ae_of_all _ hM_nonneg)
          hM_meas.aemeasurable hr1, ← mul_assoc,
          ENNReal.div_mul_cancel (by simpa using hr1) ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (r / (r - 1)) *
          ∫⁻ ω, ENNReal.ofReal (f n ω) * ENNReal.ofReal (M ω ^ (r - 1)) ∂μ := by
        rw [ENNReal.ofReal_div_of_pos hr1, hν, lintegral_withDensity_eq_lintegral_mul μ
          (hmeas n).ennreal_ofReal (hM_meas.pow_const (r - 1)).ennreal_ofReal]
        rfl

/-- **Doob's `L^r` inequality** for nonnegative submartingales:
`‖max_{k ≤ n} f_k‖_{L^r} ≤ (r / (r − 1)) ‖f_n‖_{L^r}`, `r ∈ (1, ∞)`. -/
theorem eLpNorm_runningMax_le_of_submartingale [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {r : ℝ} (hr : 1 < r) (n : ℕ) :
    eLpNorm (runningMax f n) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (r / (r - 1)) * eLpNorm (f n) (ENNReal.ofReal r) μ := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hR : 1 ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le
  set M := runningMax f n with hM
  -- nothing to prove if `‖f_n‖_{L^r} = ∞`
  by_cases hfn : eLpNorm (f n) (ENNReal.ofReal r) μ = ∞
  · rw [hfn, ENNReal.mul_top (by simpa using div_pos hr0 hr1)]
    exact le_top
  have hsm : ∀ k, StronglyMeasurable (f k) := fun k => (hf.stronglyAdapted k).mono (ℱ.le k)
  have hM_meas : Measurable M := Finset.measurable_range_sup'' fun k _ => (hsm k).measurable
  have hM_nonneg : ∀ ω, 0 ≤ M ω := fun ω =>
    (hnonneg 0 ω).trans (le_runningMax f (Nat.zero_le n) ω)
  -- each `f_k`, `k ≤ n`, is in `L^r`, since `0 ≤ f_k ≤ E[f_n | ℱ_k]`; hence so is `M ≤ Σ_k f_k`
  have hfn_mem : MemLp (f n) (ENNReal.ofReal r) μ := lt_top_iff_ne_top.2 hfn
  have hfk_mem : ∀ k ≤ n, MemLp (f k) (ENNReal.ofReal r) μ := fun k hk => by
    refine (hfn_mem.condExp (m := ℱ k) hR).mono (hsm k).aestronglyMeasurable ?_
    filter_upwards [hf.ae_le_condExp hk] with ω hω
    rw [Real.norm_of_nonneg (hnonneg k ω)]
    exact hω.trans (Real.le_norm_self _)
  have hM_mem : MemLp M (ENNReal.ofReal r) μ := by
    refine (memLp_finsetSum (Finset.range (n + 1)) fun k hk =>
      hfk_mem k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).mono hM_meas.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hM_nonneg ω)]
    refine (Finset.sup'_le _ _ fun k hk => ?_).trans (Real.le_norm_self _)
    exact Finset.single_le_sum (fun j _ => hnonneg j ω) hk
  -- `A = E M^r`, `B = E f_n^r`
  set A := ∫⁻ ω, ENNReal.ofReal (M ω ^ r) ∂μ with hA
  set B := ∫⁻ ω, ENNReal.ofReal (f n ω ^ r) ∂μ with hB
  have hA_eq : eLpNorm M (ENNReal.ofReal r) μ = A ^ (1 / r) :=
    eLpNorm_eq_lintegral_ofReal_rpow hM_nonneg hM_meas.aestronglyMeasurable hr0
  have hB_eq : eLpNorm (f n) (ENNReal.ofReal r) μ = B ^ (1 / r) :=
    eLpNorm_eq_lintegral_ofReal_rpow (hnonneg n) (hsm n).aestronglyMeasurable hr0
  have hA_top : A ≠ ∞ := by
    have h : eLpNorm M (ENNReal.ofReal r) μ < ∞ := hM_mem
    rw [hA_eq] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 h).ne
  -- Hölder's inequality with the conjugate exponents `r` and `r' = r / (r − 1)`
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hr).2 rfl
  have hholder : ∫⁻ ω, ENNReal.ofReal (f n ω) * ENNReal.ofReal (M ω ^ (r - 1)) ∂μ ≤
      B ^ (1 / r) * A ^ (1 / (r / (r - 1))) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
      (hsm n).measurable.ennreal_ofReal.aemeasurable
      (hM_meas.pow_const (r - 1)).ennreal_ofReal.aemeasurable
    have hF : ∫⁻ ω, ENNReal.ofReal (f n ω) ^ r ∂μ = B :=
      lintegral_congr fun ω => ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hr0.le
    have hG : ∫⁻ ω, ENNReal.ofReal (M ω ^ (r - 1)) ^ (r / (r - 1)) ∂μ = A :=
      lintegral_congr fun ω => by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hM_nonneg ω) _) (by positivity),
          ← Real.rpow_mul (hM_nonneg ω), mul_div_cancel₀ _ hr1.ne']
    rw [hF, hG] at h
    exact h
  have key : A ≤ ENNReal.ofReal (r / (r - 1)) * (B ^ (1 / r) * A ^ (1 / (r / (r - 1)))) :=
    (lintegral_rpow_runningMax_le hf hnonneg hr n).trans (by gcongr)
  -- divide by `‖M‖_{L^r}^{r − 1} = A^{1 / r'}` (finite; the case `A = 0` is trivial)
  rw [hA_eq, hB_eq]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hsplit : A = A ^ (1 / r) * A ^ (1 / (r / (r - 1))) := by
    rw [← ENNReal.rpow_add _ _ hA0 hA_top,
      show 1 / r + 1 / (r / (r - 1)) = 1 by field_simp; ring, ENNReal.rpow_one]
  have hX0 : A ^ (1 / (r / (r - 1))) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA_top).ne'
  have hXtop : A ^ (1 / (r / (r - 1))) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hA_top
  rw [← ENNReal.mul_le_mul_iff_left hX0 hXtop, ← hsplit, mul_assoc]
  exact key

/-- **Doob's `L^r` inequality** for martingales with values in a Banach space:
`‖max_{k ≤ n} ‖Y_k‖‖_{L^r} ≤ (r / (r − 1)) ‖Y_n‖_{L^r}`, `r ∈ (1, ∞)`. -/
theorem eLpNorm_runningMax_norm_le [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {r : ℝ}
    (hr : 1 < r) (n : ℕ) :
    eLpNorm (runningMax (fun k ω => ‖Y k ω‖) n) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (r / (r - 1)) * eLpNorm (Y n) (ENNReal.ofReal r) μ := by
  -- `k ↦ ‖Y_k‖` is a nonnegative submartingale, by conditional Jensen:
  -- `‖Y_i‖ = ‖E[Y_j | ℱ_i]‖ ≤ E[‖Y_j‖ | ℱ_i]`
  have hsub : Submartingale (fun k ω => ‖Y k ω‖) ℱ μ := by
    refine ⟨fun k => (hY.stronglyAdapted k).norm, fun i j hij => ?_,
      fun k => (hY.integrable k).norm⟩
    filter_upwards [hY.condExp_ae_eq hij, norm_condExp_le (μ := μ) (m := ℱ i) (Y j)]
      with ω h1 h2
    rw [← h1]
    exact h2
  calc eLpNorm (runningMax (fun k ω => ‖Y k ω‖) n) (ENNReal.ofReal r) μ
      ≤ ENNReal.ofReal (r / (r - 1)) * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal r) μ :=
        eLpNorm_runningMax_le_of_submartingale hsub (fun k ω => norm_nonneg _) hr n
    _ = ENNReal.ofReal (r / (r - 1)) * eLpNorm (Y n) (ENNReal.ofReal r) μ := by
        rw [eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]

/-- **Doob's `L^r` inequality** for Paley–Walsh martingales on the sign cube (no completeness of
the space of values is needed: the martingale is mapped isometrically into the completion of the
space, where it is a martingale). -/
theorem SignCube.lpNorm_runningMax_le {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ξ : Fin N → (Fin N → Bool) → E} (hξ : SignCube.IsPredictable ξ) {r : ℝ}
    (hr : 1 < r) (n : ℕ) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) r
        (runningMax (fun k ε => ‖SignCube.paleyWalsh ξ k ε‖) n) ≤
      r / (r - 1) * SignCube.lpNorm (fun x => ‖x‖) r (SignCube.paleyWalsh ξ n) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  -- the isometric image `T ∘ M` of the martingale in the completion `Ê` of `E`
  let T : E →ₗᵢ[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  set ξ' : Fin N → (Fin N → Bool) → UniformSpace.Completion E := fun k ε => T (ξ k ε) with hξ'
  have hξ'p : SignCube.IsPredictable ξ' := fun k ε ε' h => by
    simp only [hξ', hξ k ε ε' h]
  have hnorm : ∀ k ε, ‖SignCube.paleyWalsh ξ' k ε‖ = ‖SignCube.paleyWalsh ξ k ε‖ := by
    intro k ε
    calc ‖SignCube.paleyWalsh ξ' k ε‖ = ‖T.toLinearMap (SignCube.paleyWalsh ξ k ε)‖ := by
          rw [SignCube.map_paleyWalsh]
          rfl
      _ = ‖SignCube.paleyWalsh ξ k ε‖ := T.norm_map _
  have hmax : runningMax (fun k ε => ‖SignCube.paleyWalsh ξ' k ε‖) n =
      runningMax (fun k ε => ‖SignCube.paleyWalsh ξ k ε‖) n := by
    simp only [hnorm]
  have hlast : SignCube.lpNorm (fun x => ‖x‖) r (SignCube.paleyWalsh ξ' n) =
      SignCube.lpNorm (fun x => ‖x‖) r (SignCube.paleyWalsh ξ n) := by
    simp only [SignCube.lpNorm, hnorm]
  -- Doob's inequality for the martingale `T ∘ M` in `Ê`, and `L^r` norms on the cube
  have h := eLpNorm_runningMax_norm_le (SignCube.martingale_paleyWalsh ξ' hξ'p) hr n
  rw [SignCube.eLpNorm_uniformOn _ hr0, SignCube.eLpNorm_uniformOn _ hr0,
    ← ENNReal.ofReal_mul (div_nonneg hr0.le hr1.le), hmax, hlast] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg hr0.le hr1.le)
    (Real.rpow_nonneg (SignCube.avg_nonneg fun ε => Real.rpow_nonneg (norm_nonneg _) _) _))).1 h

end BanachProbability
