module

public import BanachProbability.Noncommutative.CondExp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Distribution functions of matrix-valued functions

For a matrix-valued function `x` on a probability space, the distribution function
`λ_s (x) = τ (1_{(s, ∞)} (|x|)) = ∫ #{i : s_i (x ω) > s} dμ (ω)` (`ncDistribution`; the
noncommutative weak `L¹` quasi-norm is `sup_s s λ_s (x)`). It is subadditive,
`λ_{s+t} (x + y) ≤ λ_s (x) + λ_t (y)` (from Weyl's inequality `countAbove_add_add_le`), satisfies
Chebyshev's inequality `s^r λ_s (x) ≤ ‖x‖_{L^r}^r`, and gives the layer-cake formula
`‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`. The spectral truncations of a symmetric matrix at level
`s`, `A 1_{(s, ∞)} (|A|)` and `A 1_{[0, s]} (|A|)` (`truncAbove`, `truncBelow`), split it into its
large and small eigenvalues; both are measurable functions of the matrix.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

private theorem mcd_rpow_ite_eq_indicator (r a : ℝ) :
    (fun s : ℝ => r * s ^ (r - 1) * (if s < a then 1 else 0)) =
      (Set.Iio a).indicator fun s => r * s ^ (r - 1) := by
  funext s
  by_cases hs : s < a <;> simp [hs, Set.indicator]

/-- `∫_{(0, ∞)} r s^{r−1} 1_{s < a} ds = a^r` for `a ≥ 0`, `r > 0`. -/
private theorem mcd_integral_rpow_ite {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * (if s < a then 1 else 0) = a ^ r := by
  rw [mcd_rpow_ite_eq_indicator, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hr.ne', sub_zero, mul_div_cancel₀ _ hr.ne']

/-- `s ↦ r s^{r−1} 1_{s < a}` is integrable on `(0, ∞)` for `r > 0`. -/
private theorem mcd_integrableOn_rpow_ite {r : ℝ} (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun s : ℝ => r * s ^ (r - 1) * (if s < a then 1 else 0)) (Set.Ioi 0) := by
  rw [mcd_rpow_ite_eq_indicator, IntegrableOn, integrable_indicator_iff measurableSet_Iio,
    IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a)
    (r := r - 1) (by linarith)).const_mul r
  rw [intervalIntegrable_iff] at h
  refine h.mono_set fun s hs => ?_
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi] at hs
  simp only [Set.uIoc, Set.mem_Ioc, inf_lt_iff, le_sup_iff]
  exact ⟨Or.inl hs.2, Or.inr hs.1.le⟩

variable {m : Type*} [Fintype m] in
/-- `r s^{r−1} #{i : s_i (A) > s} = Σ_i r s^{r−1} 1_{s < s_i (A)}`. -/
private theorem mcd_mul_countAbove_eq_sum {r : ℝ} (A : Matrix m n ℝ) :
    (fun s : ℝ => r * s ^ (r - 1) * (countAbove s A : ℝ)) =
      fun s => ∑ i, r * s ^ (r - 1) * (if s < singularValue A i then 1 else 0) := by
  funext s
  rw [countAbove, Finset.natCast_card_filter, Finset.mul_sum]

variable {m : Type*} [Fintype m] in
/-- `s ↦ r s^{r−1} #{i : s_i (A) > s}` is integrable on `(0, ∞)` for `r > 0`. -/
theorem mcd_integrableOn_countAbove {r : ℝ} (hr : 0 < r) (A : Matrix m n ℝ) :
    IntegrableOn (fun s : ℝ => r * s ^ (r - 1) * (countAbove s A : ℝ)) (Set.Ioi 0) := by
  rw [mcd_mul_countAbove_eq_sum]
  exact integrable_finsetSum _ fun i _ => mcd_integrableOn_rpow_ite hr _

variable {m : Type*} [Fintype m] in
/-- The layer-cake formula for one matrix: `∫₀^∞ r s^{r−1} #{i : s_i (A) > s} ds = ‖A‖_{S_r}^r`. -/
theorem mcd_integral_countAbove {r : ℝ} (hr : 0 < r) (A : Matrix m n ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * (countAbove s A : ℝ) =
      schattenNorm (ENNReal.ofReal r) A ^ r := by
  have h := schattenNorm_rpow (q := ENNReal.ofReal r) (by simpa using hr) ENNReal.ofReal_ne_top A
  rw [ENNReal.toReal_ofReal hr.le] at h
  rw [h, mcd_mul_countAbove_eq_sum, integral_finsetSum _ fun i _ => mcd_integrableOn_rpow_ite hr _]
  exact Finset.sum_congr rfl fun i _ => mcd_integral_rpow_ite hr (singularValue_nonneg A i)

theorem integrable_countAbove [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ} (hx : AEMeasurable x μ)
    (s : ℝ) : Integrable (fun ω => (countAbove s (x ω) : ℝ)) μ := by
  refine Integrable.of_bound ((measurable_countAbove s).comp_aemeasurable hx).aestronglyMeasurable
    (Fintype.card n) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_natCast]
  exact_mod_cast countAbove_le_card s (x ω)

theorem ncDistribution_nonneg (s : ℝ) (x : Ω → Matrix n n ℝ) : 0 ≤ ncDistribution μ s x :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem ncDistribution_congr_ae {x y : Ω → Matrix n n ℝ} (h : x =ᵐ[μ] y) (s : ℝ) :
    ncDistribution μ s x = ncDistribution μ s y :=
  integral_congr_ae (h.mono fun ω hω => by simp only [hω])

/-- `s_i (−A) = s_i (A)`. -/
private theorem dist_singularValue_neg (A : Matrix n n ℝ) (i : n) :
    singularValue (-A) i = singularValue A i := by
  unfold singularValue
  rw [eigenvalues_eq_of_eq _ (Matrix.isHermitian_conjTranspose_mul_self A) (by simp)]

theorem ncDistribution_neg (s : ℝ) (x : Ω → Matrix n n ℝ) :
    ncDistribution μ s (fun ω => -x ω) = ncDistribution μ s x := by
  simp only [ncDistribution, countAbove, dist_singularValue_neg]

theorem ncDistribution_anti [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ} (hx : AEMeasurable x μ)
    {s t : ℝ} (hst : s ≤ t) : ncDistribution μ t x ≤ ncDistribution μ s x :=
  integral_mono (integrable_countAbove hx t) (integrable_countAbove hx s) fun ω => by
    exact_mod_cast countAbove_anti hst (x ω)

/-- Subadditivity: `λ_{s+t} (x + y) ≤ λ_s (x) + λ_t (y)`. -/
theorem ncDistribution_add_add_le [IsFiniteMeasure μ] {x y : Ω → Matrix n n ℝ}
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ) (s t : ℝ) :
    ncDistribution μ (s + t) (x + y) ≤ ncDistribution μ s x + ncDistribution μ t y := by
  unfold ncDistribution
  rw [← integral_add (integrable_countAbove hx s) (integrable_countAbove hy t)]
  refine integral_mono (integrable_countAbove (hx.add hy) _)
    ((integrable_countAbove hx s).add (integrable_countAbove hy t)) fun ω => ?_
  exact_mod_cast countAbove_add_add_le s t (x ω) (y ω)

/-- Chebyshev's inequality `λ_s (x) s^r ≤ ‖x‖_{L^r}^r`. -/
theorem ncDistribution_mul_rpow_le [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ}
    (hx : AEMeasurable x μ) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hint : Integrable (fun ω => schattenNorm (ENNReal.ofReal r) (x ω) ^ r) μ) :
    ncDistribution μ s x * s ^ r ≤ ∫ ω, schattenNorm (ENNReal.ofReal r) (x ω) ^ r ∂μ := by
  unfold ncDistribution
  rw [← integral_mul_const]
  exact integral_mono ((integrable_countAbove hx s).mul_const _) hint fun ω =>
    countAbove_mul_rpow_le hs hr (x ω)

/-- The layer-cake formula `‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`, in `ℝ≥0∞`. -/
theorem lintegral_schattenNorm_rpow_eq [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ}
    (hx : AEMeasurable x μ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * s ^ (r - 1) * ncDistribution μ s x) := by
  -- reduce to a measurable `x`
  wlog hxm : Measurable x generalizing x with H
  · rw [lintegral_congr_ae (hx.ae_eq_mk.mono fun ω hω => by rw [hω]),
      H hx.measurable_mk.aemeasurable hx.measurable_mk]
    simp only [ncDistribution_congr_ae hx.ae_eq_mk]
  have hpos : ∀ s : ℝ, 0 < s → ∀ A : Matrix n n ℝ, 0 ≤ r * s ^ (r - 1) * (countAbove s A : ℝ) :=
    fun s hs A => mul_nonneg (mul_nonneg hr.le (Real.rpow_nonneg hs.le _)) (Nat.cast_nonneg _)
  -- `(s, ω) ↦ r s^{r−1} #{i : s_i (x ω) > s}` is measurable (Tonelli)
  have hF : Measurable fun q : ℝ × Ω =>
      ENNReal.ofReal (r * q.1 ^ (r - 1) * (countAbove q.1 (x q.2) : ℝ)) := by
    have h1 := (measurable_countAbove_uncurry (m := n) (n := n)).comp
      (measurable_fst.prodMk (hxm.comp measurable_snd))
    have h2 : Measurable fun q : ℝ × Ω => r * q.1 ^ (r - 1) :=
      measurable_const.mul (measurable_fst.pow_const _)
    exact ENNReal.measurable_ofReal.comp (h2.mul h1)
  calc ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ
      = ∫⁻ ω, (∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r * s ^ (r - 1) * (countAbove s (x ω) : ℝ))) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [← mcd_integral_countAbove hr (x ω), ofReal_integral_eq_lintegral_ofReal
          (mcd_integrableOn_countAbove hr (x ω))
          ((ae_restrict_iff' measurableSet_Ioi).2
            (Filter.Eventually.of_forall fun s hs => hpos s hs (x ω)))]
    _ = ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ ω,
          ENNReal.ofReal (r * s ^ (r - 1) * (countAbove s (x ω) : ℝ)) ∂μ :=
        (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * s ^ (r - 1) * ncDistribution μ s x) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [ncDistribution, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
          ((integrable_countAbove hx s).const_mul _)
          (Filter.Eventually.of_forall fun ω => hpos s hs (x ω))]

/-- The part `A 1_{(s, ∞)} (|A|)` of a symmetric matrix with the eigenvalues of absolute value
larger than `s`. -/
noncomputable def truncAbove (s : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => if s < |t| then t else 0) A

/-- The part `A 1_{[0, s]} (|A|)` of a symmetric matrix with the eigenvalues of absolute value at
most `s`. -/
noncomputable def truncBelow (s : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => if s < |t| then 0 else t) A

theorem truncAbove_add_truncBelow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) :
    truncAbove s A + truncBelow s A = A := by
  rw [truncAbove, truncBelow, ← cfc_add (R := ℝ) A _ _ (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _)]
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  congr 1
  funext t
  split_ifs <;> simp

theorem isHermitian_truncAbove (s : ℝ) (A : Matrix n n ℝ) : (truncAbove s A).IsHermitian :=
  isHermitian_cfc _ A

theorem isHermitian_truncBelow (s : ℝ) (A : Matrix n n ℝ) : (truncBelow s A).IsHermitian :=
  isHermitian_cfc _ A

/-- `t 1_{(s, ∞)} (|t|)` is the pointwise limit of the continuous functions
`t min (1, max (0, k (|t| − s)))`. -/
private theorem dist_tendsto_truncAbove (s t : ℝ) :
    Filter.Tendsto (fun k : ℕ => t * min 1 (max 0 (k * (|t| - s)))) Filter.atTop
      (nhds (if s < |t| then t else 0)) := by
  split_ifs with h
  · have hpos : 0 < |t| - s := sub_pos.2 h
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (1 / (|t| - s))
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    dsimp only
    have h1 : 1 ≤ (k : ℝ) * (|t| - s) := by
      calc (1 : ℝ) = 1 / (|t| - s) * (|t| - s) := by field_simp
        _ ≤ k * (|t| - s) :=
          mul_le_mul_of_nonneg_right (hk₀.trans (by exact_mod_cast hk)) hpos.le
    rw [min_eq_left (h1.trans (le_max_right _ _)), mul_one]
  · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    have h1 : (k : ℝ) * (|t| - s) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith [not_lt.1 h])
    rw [max_eq_left h1, min_eq_right zero_le_one, mul_zero]

theorem measurable_truncAbove (s : ℝ) : Measurable fun A : Matrix n n ℝ => truncAbove s A :=
  measurable_cfc_of_tendsto_continuous (F := fun k t => t * min 1 (max 0 (k * (|t| - s))))
    (fun _ => by fun_prop) (dist_tendsto_truncAbove s)

theorem measurable_truncBelow (s : ℝ) : Measurable fun A : Matrix n n ℝ => truncBelow s A := by
  refine measurable_cfc_of_tendsto_continuous
    (F := fun k t => t - t * min 1 (max 0 (k * (|t| - s)))) (fun _ => by fun_prop) fun t => ?_
  convert tendsto_const_nhds.sub (dist_tendsto_truncAbove s t) using 2
  split_ifs <;> simp

open scoped Classical in
theorem schattenNorm_truncAbove_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncAbove s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => s < |hA.eigenvalues i|), |hA.eigenvalues i| ^ r := by
  rw [truncAbove, schattenNorm_cfc_rpow hA _ hr, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Real.zero_rpow hr.ne']

open scoped Classical in
theorem schattenNorm_truncBelow_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncBelow s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => |hA.eigenvalues i| ≤ s), |hA.eigenvalues i| ^ r := by
  rw [truncBelow, schattenNorm_cfc_rpow hA _ hr, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : s < |hA.eigenvalues i|
  · simp [h, not_le.mpr h, Real.zero_rpow hr.ne']
  · simp [h, not_lt.mp h]

end BanachProbability
