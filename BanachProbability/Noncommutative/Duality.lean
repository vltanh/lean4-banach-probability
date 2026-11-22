module

public import BanachProbability.Noncommutative.Interpolation
public import BanachProbability.Noncommutative.Transform
public import BanachProbability.Schatten.Holder

/-!
# Duality for noncommutative martingale transforms

* Hölder's inequality in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}` for symmetric
  matrix-valued `x`, `y` (`ofReal_matrixTrace_mul_le`), from the trace Hölder inequality pointwise
  (`abs_trace_mul_le_of_isHermitian`) and Hölder's inequality for the integral; equality for a
  norming function built from `normingElement` (`exists_matrixTrace_mul_eq_eLpNorm`), which is
  measurable as a continuous function of the matrix (`measurable_normingElement`).
* The transform is self-adjoint for `τ (x y)` (`matrixTrace_ncTransform_mul`).
* Hence a strong `(r, r)` bound for `T_c` on symmetric `ℱ_N`-measurable functions gives the strong
  `(r', r')` bound with the same constant (`isStrongTypeNC_ncTransform_dual`; the duality step of
  N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002),
  Theorem 4.3): for the norming function `y` of `T_c x` in `L^{r'}`,
  `‖T_c x‖_{r'} = τ (T_c x · y) = τ (x · T_c y) ≤ ‖x‖_{r'} ‖T_c y‖_r ≤ K ‖x‖_{r'} ‖y‖_r`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- `t ↦ sgn (t) |t|^{r−1}` is continuous for `r > 1`: it is `t₊^{r−1} − t₋^{r−1}`. -/
private theorem continuous_sign_mul_abs_rpow {r : ℝ} (hr : 1 < r) :
    Continuous fun t : ℝ => Real.sign t * |t| ^ (r - 1) := by
  have h : (fun t : ℝ => Real.sign t * |t| ^ (r - 1)) =
      fun t => max t 0 ^ (r - 1) - max (-t) 0 ^ (r - 1) := by
    funext t
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [Real.sign_of_neg ht, abs_of_neg ht, max_eq_right ht.le, max_eq_left (by linarith),
        Real.zero_rpow (by linarith)]
      ring
    · simp [Real.zero_rpow (by linarith : r - 1 ≠ 0)]
    · rw [Real.sign_of_pos ht, abs_of_pos ht, max_eq_left ht.le, max_eq_right (by linarith),
        Real.zero_rpow (by linarith)]
      ring
  rw [h]
  exact ((continuous_id.max continuous_const).rpow_const fun _ => Or.inr (by linarith)).sub
    ((continuous_neg.max continuous_const).rpow_const fun _ => Or.inr (by linarith))

/-- The norming element is a Borel measurable function of the matrix, for `r > 1`. -/
theorem measurable_normingElement {r : ℝ} (hr : 1 < r) :
    Measurable (normingElement (n := n) r) :=
  measurable_cfc_of_continuous (continuous_sign_mul_abs_rpow hr)

/-- **Hölder's inequality** in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}` for (a.e.) symmetric
`x`, `y`, `r' = r / (r − 1)`. -/
theorem ofReal_matrixTrace_mul_le {x y : Ω → Matrix n n ℝ} (hxm : AEMeasurable x μ)
    (hym : AEMeasurable y μ) (hx : ∀ᵐ ω ∂μ, (x ω).IsHermitian)
    (hy : ∀ᵐ ω ∂μ, (y ω).IsHermitian) {r : ℝ} (hr : 1 < r) :
    ENNReal.ofReal (matrixTrace μ fun ω => x ω * y ω) ≤
      eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal (r / (r - 1))) (y ω))
          (ENNReal.ofReal (r / (r - 1))) μ := by
  have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
  have : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal (r / (r - 1))) :=
    ENNReal.holderConjugate_iff.mpr hpq.inv_add_inv_ennreal
  set f := fun ω => schattenNorm (ENNReal.ofReal r) (x ω)
  set g := fun ω => schattenNorm (ENNReal.ofReal (r / (r - 1))) (y ω)
  have hf : AEStronglyMeasurable f μ :=
    ((measurable_schattenNorm _).comp_aemeasurable hxm).aestronglyMeasurable
  have hg : AEStronglyMeasurable g μ :=
    ((measurable_schattenNorm _).comp_aemeasurable hym).aestronglyMeasurable
  calc ENNReal.ofReal (matrixTrace μ fun ω => x ω * y ω)
      ≤ ‖∫ ω, (x ω * y ω).trace ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ ω, ‖(x ω * y ω).trace‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ω, ‖(f • g) ω‖ₑ ∂μ := by
        -- the trace Hölder inequality, pointwise
        refine lintegral_mono_ae ?_
        filter_upwards [hx, hy] with ω hxω hyω
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Pi.smul_apply', smul_eq_mul,
          abs_of_nonneg (mul_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _))]
        exact ENNReal.ofReal_le_ofReal (abs_trace_mul_le_of_isHermitian hxω hyω hr)
    _ ≤ eLpNorm (f • g) 1 μ := lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm f (ENNReal.ofReal r) μ * eLpNorm g (ENNReal.ofReal (r / (r - 1))) μ :=
        eLpNorm_smul_le_mul_eLpNorm hf hg

/-- **The norming function** of `z` in `L^p (τ)`, `p > 1`: an `m`-measurable symmetric `y` with
`‖y‖_{L^{p'}} ≤ 1` and `τ (z y) = ‖z‖_{L^p}`, namely
`y = ‖z‖_{L^p}^{1−p} normingElement p (z)`. -/
theorem exists_matrixTrace_mul_eq_eLpNorm {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {z : Ω → Matrix n n ℝ} (hzm : Measurable[m] z) (hz : ∀ᵐ ω ∂μ, (z ω).IsHermitian) {p : ℝ}
    (hp : 1 < p) (hzp : MatrixMemLp z (ENNReal.ofReal p) μ) :
    ∃ y : Ω → Matrix n n ℝ, Measurable[m] y ∧ (∀ ω, (y ω).IsHermitian) ∧
      MatrixMemLp y (ENNReal.ofReal (p / (p - 1))) μ ∧
      eLpNorm (fun ω => schattenNorm (ENNReal.ofReal (p / (p - 1))) (y ω))
        (ENNReal.ofReal (p / (p - 1))) μ ≤ 1 ∧
      ENNReal.ofReal (matrixTrace μ fun ω => z ω * y ω) =
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal p) (z ω)) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set q := p / (p - 1) with hq_def
  have hq0 : 0 < q := div_pos hp0 hp1
  have hpq : (p - 1) * q = p := by
    rw [hq_def]
    field_simp
  have hq0' : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  set f := fun ω => schattenNorm (ENNReal.ofReal p) (z ω) with hf_def
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => schattenNorm_nonneg _ _
  have hf : MemLp f (ENNReal.ofReal p) μ :=
    hzp.memLp_schattenNorm (ENNReal.one_le_ofReal.2 hp.le)
  -- `‖z‖_{L^p} = A = I^{1/p}`, `I = ∫ ‖z‖_{S_p}^p`
  set I := ∫ ω, f ω ^ p ∂μ with hI_def
  have hI0 : 0 ≤ I := integral_nonneg fun ω => Real.rpow_nonneg (hf0 ω) _
  set A := I ^ p⁻¹ with hA_def
  have hfA : eLpNorm f (ENNReal.ofReal p) μ = ENNReal.ofReal A := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    simp only [Real.norm_of_nonneg (hf0 _), hA_def, hI_def]
  have hA0 : 0 ≤ A := Real.rpow_nonneg hI0 _
  have hAI : A ^ p = I := Real.rpow_inv_rpow hI0 hp0.ne'
  rcases hA0.eq_or_lt with hA | hA
  · -- `‖z‖_{L^p} = 0`: take `y = 0`
    refine ⟨fun _ => 0, measurable_const, fun _ => Matrix.isHermitian_zero, fun i j => ?_, ?_, ?_⟩
    · exact MemLp.zero'
    · simp [schattenNorm_zero hq0']
    · rw [hfA, ← hA]
      simp [matrixTrace]
  · -- `y = c • normingElement p (z)`, `c = A^{1−p}`
    set c := (A ^ (p - 1))⁻¹ with hc_def
    have hAp : 0 < A ^ (p - 1) := Real.rpow_pos_of_pos hA _
    have hc : 0 < c := inv_pos.2 hAp
    set y := fun ω => c • normingElement p (z ω) with hy_def
    have hym : Measurable[m] y := ((measurable_normingElement hp).comp hzm).const_smul c
    -- `‖y‖_{S_q} = c ‖z‖_{S_p}^{p−1}` a.e.
    have hyN : ∀ᵐ ω ∂μ, schattenNorm (ENNReal.ofReal q) (y ω) = c * f ω ^ (p - 1) := by
      filter_upwards [hz] with ω hω
      rw [hy_def, schattenNorm_smul hq0', abs_of_pos hc, schattenNorm_normingElement hω hp]
    have hg : MemLp (fun ω => c * f ω ^ (p - 1)) (ENNReal.ofReal q) μ := by
      have h := hf.norm_rpow_div (ENNReal.ofReal (p - 1))
      rw [ENNReal.toReal_ofReal hp1.le, ← ENNReal.ofReal_div_of_pos hp1] at h
      simp only [Real.norm_of_nonneg (hf0 _)] at h
      exact h.const_mul c
    have hyq : MemLp (fun ω => schattenNorm (ENNReal.ofReal q) (y ω)) (ENNReal.ofReal q) μ :=
      hg.ae_eq (hyN.mono fun ω h => h.symm)
    have hyM : MatrixMemLp y (ENNReal.ofReal q) μ :=
      matrixMemLp_of_memLp_schattenNorm (hym.mono hm le_rfl).aemeasurable hq0' hyq
    refine ⟨y, hym, fun ω => (isHermitian_normingElement p (z ω)).smul (IsSelfAdjoint.all _),
      hyM, le_of_eq ?_, ?_⟩
    · -- `∫ ‖y‖_{S_q}^q = c^q I = 1`
      rw [hyq.eLpNorm_eq_integral_rpow_norm hq0' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hq0.le]
      have h : ∫ ω, ‖schattenNorm (ENNReal.ofReal q) (y ω)‖ ^ q ∂μ = c ^ q * I := by
        rw [hI_def, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hyN] with ω hω
        rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _), hω,
          Real.mul_rpow hc.le (Real.rpow_nonneg (hf0 ω) _), ← Real.rpow_mul (hf0 ω), hpq]
      have h1 : c ^ q * I = 1 := by
        rw [← hAI, hc_def, Real.inv_rpow hAp.le, ← Real.rpow_mul hA0, hpq,
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hA _).ne']
      rw [h, h1, Real.one_rpow, ENNReal.ofReal_one]
    · -- `τ (z y) = c I = A`
      rw [hfA]
      congr 1
      have h : (matrixTrace μ fun ω => z ω * y ω) = c * I := by
        unfold matrixTrace
        rw [hI_def, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hz] with ω hω
        simp only [hy_def, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
          trace_mul_normingElement hω hp, hf_def]
      have hApos : 0 < A ^ p := Real.rpow_pos_of_pos hA _
      rw [h, ← hAI, hc_def, Real.rpow_sub hA, Real.rpow_one]
      field_simp

/-- **Duality**: a strong `(r, r)` bound for a transform by predictable multipliers on symmetric
`ℱ_N`-measurable functions gives the strong `(r', r')` bound with the same constant,
`r' = r / (r − 1)`. -/
theorem isStrongTypeNC_ncTransform_dual [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {c : ℕ → Ω → ℝ} {N : ℕ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1)
    {r K : ℝ} (hr : 1 < r)
    (h : IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r K) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) (r / (r - 1)) K := by
  intro x hxm hx hxp
  have hr1 : 0 < r - 1 := by linarith
  set p := r / (r - 1) with hp_def
  have hp : 1 < p := by
    rw [hp_def, one_lt_div hr1]
    linarith
  have hpr : p / (p - 1) = r := by
    have : p - 1 = 1 / (r - 1) := by
      rw [hp_def]
      field_simp
      ring
    rw [this, div_div_eq_mul_div, div_one, hp_def, div_mul_cancel₀ _ hr1.ne']
  have : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal r) :=
    ENNReal.holderConjugate_iff.mpr
      ((Real.holderConjugate_iff_eq_conjExponent hp).2 hpr.symm).inv_add_inv_ennreal
  -- the norming function `y` of `T_c x` in `L^p`, with `‖y‖_{L^r} ≤ 1`
  have hzm := measurable_ncTransform (μ := μ) (N := N) hc x
  have hz := isHermitian_ncTransform (μ := μ) (ℱ := ℱ) (c := c) (N := N)
    (Filter.Eventually.of_forall hx)
  have hzp := hxp.ncTransform (N := N) hc hc1 (ENNReal.one_le_ofReal.2 hp.le)
  obtain ⟨y, hym, hy, hyr, hy1, hzy⟩ := exists_matrixTrace_mul_eq_eLpNorm (ℱ.le N) hzm hz hp hzp
  rw [hpr] at hyr hy1
  -- Hölder's inequality for `x` and `T_c y`
  have hH := ofReal_matrixTrace_mul_le hxp.aemeasurable
    ((measurable_ncTransform (μ := μ) (N := N) hc y).mono (ℱ.le N) le_rfl).aemeasurable
    (Filter.Eventually.of_forall hx)
    (isHermitian_ncTransform (μ := μ) (ℱ := ℱ) (c := c) (N := N)
      (Filter.Eventually.of_forall hy)) hp
  rw [hpr] at hH
  calc eLpNorm (fun ω => schattenNorm (ENNReal.ofReal p) (ncTransform ℱ μ c N x ω))
        (ENNReal.ofReal p) μ
      = ENNReal.ofReal (matrixTrace μ fun ω => ncTransform ℱ μ c N x ω * y ω) := hzy.symm
    _ = ENNReal.ofReal (matrixTrace μ fun ω => x ω * ncTransform ℱ μ c N y ω) := by
        rw [matrixTrace_ncTransform_mul hc hc1 hxp hyr]
    _ ≤ eLpNorm (fun ω => schattenNorm (ENNReal.ofReal p) (x ω)) (ENNReal.ofReal p) μ *
          eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (ncTransform ℱ μ c N y ω))
            (ENNReal.ofReal r) μ := hH
    _ ≤ eLpNorm (fun ω => schattenNorm (ENNReal.ofReal p) (x ω)) (ENNReal.ofReal p) μ *
          (ENNReal.ofReal K * 1) := by
        gcongr
        exact (h y hym hy hyr).trans (by gcongr)
    _ = ENNReal.ofReal K *
          eLpNorm (fun ω => schattenNorm (ENNReal.ofReal p) (x ω)) (ENNReal.ofReal p) μ := by
        rw [mul_one, mul_comm]

end BanachProbability
