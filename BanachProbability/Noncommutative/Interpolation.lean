module

public import BanachProbability.Noncommutative.Distribution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Marcinkiewicz interpolation on `L^r (L^∞ (Ω) ⊗ M_n)`

An a.e.-additive map `T` on matrix-valued functions on a probability space that is of weak type
`(p_j, p_j)` with constant `K_j` on the symmetric `m`-measurable functions, `j = 0, 1`,
`1 ≤ p₀ < p₁`, is of strong type `(r, r)` for `p₀ < r < p₁`:
`‖T x‖_{L^r}^r ≤ 2^r r (K₀^{p₀} / (r − p₀) + K₁^{p₁} / (p₁ − r)) ‖x‖_{L^r}^r`
(`marcinkiewicz`; J. Marcinkiewicz, C. R. Acad. Sci. Paris 208 (1939); the interpolation step of
Theorem 4.3 of N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194
(2002)). The proof is the classical one, with the spectral truncations: to bound `λ_s (T x)`, split
`x` at level `s / 2` into `x 1_{(s/2, ∞)} (|x|)` and `x 1_{[0, s/2]} (|x|)` pointwise
(`truncAbove`, `truncBelow`, both `m`-measurable), use the subadditivity of the distribution
function (`ncDistribution_add_add_le`) and the two weak type bounds, and integrate with the
layer-cake formula (`lintegral_schattenNorm_rpow_eq`): each eigenvalue modulus `a = |λ_i (x ω)|`
contributes `∫_0^{2a} r s^{r−1} (s/2)^{−p₀} a^{p₀} ds = 2^r r a^r / (r − p₀)` and
`∫_{2a}^∞ r s^{r−1} (s/2)^{−p₁} a^{p₁} ds = 2^r r a^r / (p₁ − r)`; the eigenvalues of `x ω` are
measurable in `ω` (`measurable_hermitianEigenvalue`), so Tonelli's theorem applies.

`IsWeakTypeNC` and `IsStrongTypeNC` are the weak and strong type `(p, p)` conditions on the
symmetric `m`-measurable functions; a strong type bound gives the weak type bound with the same
constant (Chebyshev, `IsStrongTypeNC.isWeakTypeNC`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- `∫_0^{2a} s^{r−1−p} ds = (2a)^{r−p} / (r − p)` for `p < r`, `a ≥ 0`, as an integral over
`(0, ∞)` of an indicator. -/
private theorem ipd_integral_large {p r a : ℝ} (hpr : p < r) (ha : 0 ≤ a) :
    IntegrableOn ((Iio (2 * a)).indicator fun s : ℝ => s ^ (r - 1 - p)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), (Iio (2 * a)).indicator (fun s : ℝ => s ^ (r - 1 - p)) s =
        (2 * a) ^ (r - p) / (r - p) := by
  have he : -1 < r - 1 - p := by linarith
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have hOn : IntegrableOn (fun s : ℝ => s ^ (r - 1 - p)) (Ioo 0 (2 * a)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h2a).1
      (intervalIntegral.intervalIntegrable_rpow' he)).mono_set Ioo_subset_Ioc_self
  constructor
  · rw [integrableOn_indicator_iff measurableSet_Iio.nullMeasurableSet, Iio_inter_Ioi]
    exact hOn
  · rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h2a, integral_rpow (Or.inl he),
      show r - 1 - p + 1 = r - p by ring, Real.zero_rpow (by linarith)]
    ring

/-- `∫_{2a}^∞ s^{r−1−p} ds = (2a)^{r−p} / (p − r)` for `r < p`, `a > 0`, as an integral over
`(0, ∞)` of an indicator. -/
private theorem ipd_integral_small {p r a : ℝ} (hrp : r < p) (ha : 0 < a) :
    IntegrableOn ((Ici (2 * a)).indicator fun s : ℝ => s ^ (r - 1 - p)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), (Ici (2 * a)).indicator (fun s : ℝ => s ^ (r - 1 - p)) s =
        (2 * a) ^ (r - p) / (p - r) := by
  have he : r - 1 - p < -1 := by linarith
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have hsub : Ici (2 * a) ∩ Ioi 0 = Ici (2 * a) := inter_eq_left.2 (Ici_subset_Ioi.2 h2a)
  constructor
  · rw [integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet, hsub,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt he h2a
  · rw [setIntegral_indicator measurableSet_Ici, inter_comm, hsub, integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt he h2a, show r - 1 - p + 1 = r - p by ring]
    have : p - r ≠ 0 := by linarith
    have : r - p ≠ 0 := by linarith
    field_simp
    ring

/-- The bound for the contribution of one eigenvalue modulus `a` to `r s^{r−1} λ_s (T x)`. -/
private noncomputable def ipdBound (p₀ p₁ K₀ K₁ r a s : ℝ) : ℝ :=
  K₀ ^ p₀ * r * 2 ^ p₀ * a ^ p₀ * (Iio (2 * a)).indicator (fun s : ℝ => s ^ (r - 1 - p₀)) s +
    K₁ ^ p₁ * r * 2 ^ p₁ * a ^ p₁ * (Ici (2 * a)).indicator (fun s : ℝ => s ^ (r - 1 - p₁)) s

private theorem ipdBound_integral {p₀ p₁ K₀ K₁ r a : ℝ} (hp₀ : 0 < p₀) (hp₀r : p₀ < r)
    (hrp₁ : r < p₁) (ha : 0 ≤ a) :
    IntegrableOn (ipdBound p₀ p₁ K₀ K₁ r a) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), ipdBound p₀ p₁ K₀ K₁ r a s =
        2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r)) * a ^ r := by
  have hp₁ : 0 < p₁ := by linarith
  have hr : 0 < r := by linarith
  rcases ha.eq_or_lt with rfl | ha'
  · have h0 : ipdBound p₀ p₁ K₀ K₁ r 0 = fun _ => 0 := by
      funext s
      simp [ipdBound, Real.zero_rpow hp₀.ne', Real.zero_rpow hp₁.ne']
    rw [h0, Real.zero_rpow hr.ne']
    simp
  · obtain ⟨hi₀, he₀⟩ := ipd_integral_large hp₀r ha
    obtain ⟨hi₁, he₁⟩ := ipd_integral_small hrp₁ ha'
    have hi₀' := hi₀.const_mul (K₀ ^ p₀ * r * 2 ^ p₀ * a ^ p₀)
    have hi₁' := hi₁.const_mul (K₁ ^ p₁ * r * 2 ^ p₁ * a ^ p₁)
    refine ⟨hi₀'.add hi₁', ?_⟩
    unfold ipdBound
    rw [integral_add hi₀' hi₁', integral_const_mul, integral_const_mul, he₀, he₁,
      Real.mul_rpow (by norm_num) ha, Real.mul_rpow (by norm_num) ha]
    have h2 : ∀ q : ℝ, (2 : ℝ) ^ q * 2 ^ (r - q) = 2 ^ r := fun q => by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have ha2 : ∀ q : ℝ, a ^ q * a ^ (r - q) = a ^ r := fun q => by
      rw [← Real.rpow_add ha']; ring_nf
    have e₀ : K₀ ^ p₀ * r * 2 ^ p₀ * a ^ p₀ * (2 ^ (r - p₀) * a ^ (r - p₀) / (r - p₀)) =
        K₀ ^ p₀ * r * (2 ^ p₀ * 2 ^ (r - p₀)) * (a ^ p₀ * a ^ (r - p₀)) / (r - p₀) := by ring
    have e₁ : K₁ ^ p₁ * r * 2 ^ p₁ * a ^ p₁ * (2 ^ (r - p₁) * a ^ (r - p₁) / (p₁ - r)) =
        K₁ ^ p₁ * r * (2 ^ p₁ * 2 ^ (r - p₁)) * (a ^ p₁ * a ^ (r - p₁)) / (p₁ - r) := by ring
    rw [e₀, e₁, h2, h2, ha2, ha2]
    ring

/-- The bound on `(0, ∞)` when `a` is above the level `s / 2`. -/
private theorem ipdBound_of_lt {p₀ p₁ K₀ K₁ r a s : ℝ} (hs : 0 < s) (h : s / 2 < a) :
    ipdBound p₀ p₁ K₀ K₁ r a s =
      r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ * a ^ p₀ + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ * 0) := by
  have h1 : s ∈ Iio (2 * a) := by rw [mem_Iio]; linarith
  have h2 : s ∉ Ici (2 * a) := by rw [mem_Ici]; linarith
  rw [ipdBound, indicator_of_mem h1, indicator_of_notMem h2, Real.div_rpow hs.le zero_le_two,
    Real.div_rpow hs.le zero_le_two, Real.rpow_sub hs (r - 1) p₀]
  have : 0 < s ^ p₀ := Real.rpow_pos_of_pos hs _
  field_simp
  ring

/-- The bound on `(0, ∞)` when `a` is at most the level `s / 2`. -/
private theorem ipdBound_of_le {p₀ p₁ K₀ K₁ r a s : ℝ} (hs : 0 < s) (h : a ≤ s / 2) :
    ipdBound p₀ p₁ K₀ K₁ r a s =
      r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ * 0 + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ * a ^ p₁) := by
  have h1 : s ∉ Iio (2 * a) := by rw [mem_Iio]; linarith
  have h2 : s ∈ Ici (2 * a) := by rw [mem_Ici]; linarith
  rw [ipdBound, indicator_of_notMem h1, indicator_of_mem h2, Real.div_rpow hs.le zero_le_two,
    Real.div_rpow hs.le zero_le_two, Real.rpow_sub hs (r - 1) p₁]
  have : 0 < s ^ p₁ := Real.rpow_pos_of_pos hs _
  field_simp
  ring

/-- The bound is nonnegative for nonnegative constants, modulus and level. -/
private theorem ipdBound_nonneg {p₀ p₁ K₀ K₁ r a s : ℝ} (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hs : 0 ≤ s) : 0 ≤ ipdBound p₀ p₁ K₀ K₁ r a s := by
  have hi : ∀ (S : Set ℝ) (q : ℝ), 0 ≤ S.indicator (fun t : ℝ => t ^ q) s := fun S q => by
    by_cases h : s ∈ S
    · rw [indicator_of_mem h]
      exact Real.rpow_nonneg hs _
    · rw [indicator_of_notMem h]
  have hc : ∀ {K p : ℝ}, 0 ≤ K → 0 ≤ K ^ p * r * 2 ^ p * a ^ p := fun hK =>
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hK _) hr) (by positivity))
      (Real.rpow_nonneg ha _)
  exact add_nonneg (mul_nonneg (hc hK₀) (hi _ _)) (mul_nonneg (hc hK₁) (hi _ _))

/-- The bound is jointly measurable in the eigenvalue modulus `a` and the level `s`. -/
private theorem measurable_ipdBound (p₀ p₁ K₀ K₁ r : ℝ) :
    Measurable fun q : ℝ × ℝ => ipdBound p₀ p₁ K₀ K₁ r q.1 q.2 := by
  have h₀ : ∀ e : ℝ,
      Measurable fun q : ℝ × ℝ => (Iio (2 * q.1)).indicator (fun s => s ^ e) q.2 := by
    intro e
    have h : (fun q : ℝ × ℝ => (Iio (2 * q.1)).indicator (fun s => s ^ e) q.2) =
        {q : ℝ × ℝ | q.2 < 2 * q.1}.indicator fun q => q.2 ^ e := by
      funext q
      simp only [indicator_apply, mem_Iio, mem_ofPred_eq]
    rw [h]
    exact (measurable_snd.pow_const e).indicator
      (measurableSet_lt measurable_snd (measurable_fst.const_mul 2))
  have h₁ : ∀ e : ℝ,
      Measurable fun q : ℝ × ℝ => (Ici (2 * q.1)).indicator (fun s => s ^ e) q.2 := by
    intro e
    have h : (fun q : ℝ × ℝ => (Ici (2 * q.1)).indicator (fun s => s ^ e) q.2) =
        {q : ℝ × ℝ | 2 * q.1 ≤ q.2}.indicator fun q => q.2 ^ e := by
      funext q
      simp only [indicator_apply, mem_Ici, mem_ofPred_eq]
    rw [h]
    exact (measurable_snd.pow_const e).indicator
      (measurableSet_le (measurable_fst.const_mul 2) measurable_snd)
  unfold ipdBound
  exact ((measurable_const.mul (measurable_fst.pow_const p₀)).mul (h₀ _)).add
    ((measurable_const.mul (measurable_fst.pow_const p₁)).mul (h₁ _))

/-- `‖ ‖f‖_{S_r} ‖_{L^r} = (∫ ‖f‖_{S_r}^r dμ)^{1/r}`, in `ℝ≥0∞`. -/
private theorem ipd_eLpNorm_eq {f : Ω → Matrix n n ℝ} (hf : AEMeasurable f μ) {r : ℝ}
    (hr : 0 < r) :
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (f ω)) (ENNReal.ofReal r) μ =
      (∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (f ω) ^ r) ∂μ) ^ (1 / r) := by
  have hm : AEStronglyMeasurable (fun ω => schattenNorm (ENNReal.ofReal r) (f ω)) μ :=
    ((measurable_schattenNorm _).comp_aemeasurable hf).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hr.le]
  congr 2
  funext ω
  rw [Real.enorm_eq_ofReal (schattenNorm_nonneg _ _),
    ENNReal.ofReal_rpow_of_nonneg (schattenNorm_nonneg _ _) hr.le]

/-- `‖f‖_{S_r} ∈ L^r` gives the integrability of `‖f‖_{S_r}^r`. -/
private theorem ipd_integrable_rpow {f : Ω → Matrix n n ℝ} {r : ℝ} (hr : 0 < r)
    (hf : MemLp (fun ω => schattenNorm (ENNReal.ofReal r) (f ω)) (ENNReal.ofReal r) μ) :
    Integrable (fun ω => schattenNorm (ENNReal.ofReal r) (f ω) ^ r) μ := by
  refine (hf.integrable_norm_rpow (by simpa using hr) ENNReal.ofReal_ne_top).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _), ENNReal.toReal_ofReal hr.le]

/-- The integrability of `‖f‖_{S_r}^r` puts the entries of `f` in `L^r`. -/
private theorem ipd_matrixMemLp {f : Ω → Matrix n n ℝ} (hf : AEMeasurable f μ) {r : ℝ}
    (hr : 0 < r) (h : Integrable (fun ω => schattenNorm (ENNReal.ofReal r) (f ω) ^ r) μ) :
    MatrixMemLp f (ENNReal.ofReal r) μ := by
  have hm : AEStronglyMeasurable (fun ω => schattenNorm (ENNReal.ofReal r) (f ω)) μ :=
    ((measurable_schattenNorm _).comp_aemeasurable hf).aestronglyMeasurable
  refine matrixMemLp_of_memLp_schattenNorm hf (q := ENNReal.ofReal r) (by simpa using hr) ?_
  refine (integrable_norm_rpow_iff hm (by simpa using hr) ENNReal.ofReal_ne_top).1
    (h.congr (Filter.Eventually.of_forall fun ω => ?_))
  simp only
  rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _), ENNReal.toReal_ofReal hr.le]

/-- `T` is of weak type `(p, p)` with constant `K` on the symmetric `m`-measurable functions:
`s^p λ_s (T x) ≤ K^p ‖x‖_{L^p}^p`. -/
def IsWeakTypeNC (μ : Measure Ω) (m : MeasurableSpace Ω)
    (T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ) (p K : ℝ) : Prop :=
  ∀ x : Ω → Matrix n n ℝ, Measurable[m] x → (∀ ω, (x ω).IsHermitian) →
    MatrixMemLp x (ENNReal.ofReal p) μ → ∀ s : ℝ, 0 < s →
      s ^ p * ncDistribution μ s (T x) ≤
        K ^ p * ∫ ω, schattenNorm (ENNReal.ofReal p) (x ω) ^ p ∂μ

/-- `T` is of strong type `(r, r)` with constant `K` on the symmetric `m`-measurable functions
in `L^r`: `‖T x‖_{L^r (S_r)} ≤ K ‖x‖_{L^r (S_r)}`. -/
def IsStrongTypeNC (μ : Measure Ω) (m : MeasurableSpace Ω)
    (T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ) (r K : ℝ) : Prop :=
  ∀ x : Ω → Matrix n n ℝ, Measurable[m] x → (∀ ω, (x ω).IsHermitian) →
    MatrixMemLp x (ENNReal.ofReal r) μ →
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (T x ω)) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal K *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ

/-- A strong type `(p, p)` bound gives the weak type `(p, p)` bound with the same constant
(Chebyshev). -/
theorem IsStrongTypeNC.isWeakTypeNC [IsFiniteMeasure μ]
    {T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ} (hT : ∀ x, Measurable (T x)) {p K : ℝ}
    (hp : 1 ≤ p) (hK : 0 ≤ K) (h : IsStrongTypeNC μ m T p K) : IsWeakTypeNC μ m T p K := by
  intro x hxm hx hxp s hs
  have hp0 : 0 < p := by linarith
  have hxL := hxp.memLp_schattenNorm (ENNReal.one_le_ofReal.2 hp)
  have h1 := h x hxm hx hxp
  have hTL : MemLp (fun ω => schattenNorm (ENNReal.ofReal p) (T x ω)) (ENNReal.ofReal p) μ :=
    h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxL.eLpNorm_lt_top)
  have hA : 0 ≤ ∫ ω, schattenNorm (ENNReal.ofReal p) (T x ω) ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (schattenNorm_nonneg _ _) p
  have hB : 0 ≤ ∫ ω, schattenNorm (ENNReal.ofReal p) (x ω) ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (schattenNorm_nonneg _ _) p
  rw [hTL.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top,
    hxL.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top] at h1
  simp only [Real.norm_of_nonneg (schattenNorm_nonneg _ _), ENNReal.toReal_ofReal hp0.le] at h1
  rw [← ENNReal.ofReal_mul hK,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (Real.rpow_nonneg hB _))] at h1
  calc s ^ p * ncDistribution μ s (T x) = ncDistribution μ s (T x) * s ^ p := mul_comm _ _
    _ ≤ ∫ ω, schattenNorm (ENNReal.ofReal p) (T x ω) ^ p ∂μ :=
        ncDistribution_mul_rpow_le (hT x).aemeasurable hs hp0 (ipd_integrable_rpow hp0 hTL)
    _ = ((∫ ω, schattenNorm (ENNReal.ofReal p) (T x ω) ^ p ∂μ) ^ p⁻¹) ^ p := by
        rw [← Real.rpow_mul hA, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ (K * (∫ ω, schattenNorm (ENNReal.ofReal p) (x ω) ^ p ∂μ) ^ p⁻¹) ^ p :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA _) h1 hp0.le
    _ = K ^ p * ∫ ω, schattenNorm (ENNReal.ofReal p) (x ω) ^ p ∂μ := by
        rw [Real.mul_rpow hK (Real.rpow_nonneg hB _), ← Real.rpow_mul hB,
          inv_mul_cancel₀ hp0.ne', Real.rpow_one]

/-- **Marcinkiewicz interpolation** on `L^r (L^∞ (Ω) ⊗ M_n)`, with two endpoints
`1 ≤ p₀ < r < p₁`. -/
theorem marcinkiewicz [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ} (hT : ∀ x, Measurable (T x))
    (hadd : ∀ x y, MatrixMemLp x 1 μ → MatrixMemLp y 1 μ → T (x + y) =ᵐ[μ] T x + T y)
    {p₀ p₁ K₀ K₁ r : ℝ} (hp₀ : 1 ≤ p₀) (hp₀r : p₀ < r) (hrp₁ : r < p₁) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (h₀ : IsWeakTypeNC μ m T p₀ K₀) (h₁ : IsWeakTypeNC μ m T p₁ K₁) :
    IsStrongTypeNC μ m T r ((2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r))) ^ (1 / r)) := by
  intro x hxm hx hxr
  have hp₀' : 0 < p₀ := by linarith
  have hr : 0 < r := by linarith
  have hp₁ : 0 < p₁ := by linarith
  set C := 2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r))
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) hr.le)
    (add_nonneg (div_nonneg (Real.rpow_nonneg hK₀ _) (sub_pos.2 hp₀r).le)
      (div_nonneg (Real.rpow_nonneg hK₁ _) (sub_pos.2 hrp₁).le))
  have hxΩ : Measurable x := hxm.mono hm le_rfl
  -- the eigenvalue moduli `|λ_i (x ω)|` are measurable in `ω`
  have hev : ∀ i, Measurable fun ω => |(hx ω).eigenvalues i| := fun i => by
    have h := continuous_abs.measurable.comp ((measurable_hermitianEigenvalue i).comp hxΩ)
    convert h using 2 with ω
    simp [hermitianEigenvalue_of_isHermitian (hx ω)]
  have hxint : Integrable (fun ω => schattenNorm (ENNReal.ofReal r) (x ω) ^ r) μ :=
    ipd_integrable_rpow hr (hxr.memLp_schattenNorm (ENNReal.one_le_ofReal.2 (by linarith)))
  -- the pointwise bound `r s^{r−1} λ_s (T x) ≤ G (s) = ∫ Σ_i φ (|λ_i (x ω)|) (s) dμ`: split `x`
  -- at level `s / 2`, subadditivity, the two weak type bounds
  have hbound : ∀ s : ℝ, 0 < s →
      Integrable (fun ω => ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s) μ ∧
        r * s ^ (r - 1) * ncDistribution μ s (T x) ≤
          ∫ ω, ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s ∂μ := by
    intro s hs
    have hs2 : 0 < s / 2 := half_pos hs
    set xa : Ω → Matrix n n ℝ := fun ω => truncAbove (s / 2) (x ω)
    set xb : Ω → Matrix n n ℝ := fun ω => truncBelow (s / 2) (x ω)
    have hxam : Measurable[m] xa := (measurable_truncAbove (s / 2)).comp hxm
    have hxbm : Measurable[m] xb := (measurable_truncBelow (s / 2)).comp hxm
    have hxaΩ : Measurable xa := (measurable_truncAbove (s / 2)).comp hxΩ
    have hxbΩ : Measurable xb := (measurable_truncBelow (s / 2)).comp hxΩ
    have hXa : ∀ ω, schattenNorm (ENNReal.ofReal p₀) (xa ω) ^ p₀ =
        ∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ω).eigenvalues i|),
          |(hx ω).eigenvalues i| ^ p₀ := fun ω =>
      schattenNorm_truncAbove_rpow (hx ω) (s / 2) hp₀'
    have hXb : ∀ ω, schattenNorm (ENNReal.ofReal p₁) (xb ω) ^ p₁ =
        ∑ i ∈ Finset.univ.filter (fun i => |(hx ω).eigenvalues i| ≤ s / 2),
          |(hx ω).eigenvalues i| ^ p₁ := fun ω =>
      schattenNorm_truncBelow_rpow (hx ω) (s / 2) hp₁
    -- `x 1_{(s/2, ∞)} (|x|) ∈ L^{p₀}`: `|t|^{p₀} 1_{|t| > s/2} ≤ (s/2)^{p₀−r} |t|^r`
    have hIa : Integrable (fun ω => schattenNorm (ENNReal.ofReal p₀) (xa ω) ^ p₀) μ := by
      have hm' := ((measurable_schattenNorm (m := n) (n := n) (ENNReal.ofReal p₀)).comp
        hxaΩ).pow_const p₀
      refine (hxint.const_mul ((s / 2) ^ (p₀ - r))).mono' hm'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (schattenNorm_nonneg _ _) _), hXa,
        schattenNorm_rpow_of_isHermitian (hx ω) hr, Finset.mul_sum]
      refine (Finset.sum_le_sum fun i hi => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
          mul_nonneg (Real.rpow_nonneg hs2.le _) (Real.rpow_nonneg (abs_nonneg _) _))
      have hlt := (Finset.mem_filter.1 hi).2
      have hpos : 0 < |(hx ω).eigenvalues i| := hs2.trans hlt
      calc |(hx ω).eigenvalues i| ^ p₀
          = |(hx ω).eigenvalues i| ^ (p₀ - r) * |(hx ω).eigenvalues i| ^ r := by
            rw [← Real.rpow_add hpos, sub_add_cancel]
        _ ≤ (s / 2) ^ (p₀ - r) * |(hx ω).eigenvalues i| ^ r :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hs2 hlt.le (by linarith))
              (Real.rpow_nonneg (abs_nonneg _) _)
    -- `x 1_{[0, s/2]} (|x|)` is bounded
    have hIb : Integrable (fun ω => schattenNorm (ENNReal.ofReal p₁) (xb ω) ^ p₁) μ := by
      have hm' := ((measurable_schattenNorm (m := n) (n := n) (ENNReal.ofReal p₁)).comp
        hxbΩ).pow_const p₁
      refine Integrable.of_bound hm'.aestronglyMeasurable (Fintype.card n * (s / 2) ^ p₁)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (schattenNorm_nonneg _ _) _), hXb]
      calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => |(hx ω).eigenvalues i| ≤ s / 2),
            (s / 2) ^ p₁ :=
            Finset.sum_le_sum fun i hi =>
              Real.rpow_le_rpow (abs_nonneg _) (Finset.mem_filter.1 hi).2 hp₁.le
        _ ≤ ∑ _i : n, (s / 2) ^ p₁ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
              Real.rpow_nonneg hs2.le _
        _ = Fintype.card n * (s / 2) ^ p₁ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hxaL := ipd_matrixMemLp hxaΩ.aemeasurable hp₀' hIa
    have hxbL := ipd_matrixMemLp hxbΩ.aemeasurable hp₁ hIb
    have hIa' : Integrable (fun ω => ∑ i ∈ Finset.univ.filter
        (fun i => s / 2 < |(hx ω).eigenvalues i|), |(hx ω).eigenvalues i| ^ p₀) μ := by
      simpa only [hXa] using hIa
    have hIb' : Integrable (fun ω => ∑ i ∈ Finset.univ.filter
        (fun i => |(hx ω).eigenvalues i| ≤ s / 2), |(hx ω).eigenvalues i| ^ p₁) μ := by
      simpa only [hXb] using hIb
    -- `T x = T (x 1_{(s/2, ∞)} (|x|)) + T (x 1_{[0, s/2]} (|x|))` a.e.
    have hTab : T x =ᵐ[μ] T xa + T xb := by
      have hxab : x = xa + xb := funext fun ω => (truncAbove_add_truncBelow (hx ω) (s / 2)).symm
      have h := hadd xa xb (hxaL.mono_exponent (ENNReal.one_le_ofReal.2 hp₀))
        (hxbL.mono_exponent (ENNReal.one_le_ofReal.2 (by linarith)))
      rwa [← hxab] at h
    have h1 : ncDistribution μ s (T x) ≤
        ncDistribution μ (s / 2) (T xa) + ncDistribution μ (s / 2) (T xb) := by
      have h := ncDistribution_add_add_le (μ := μ) (hT xa).aemeasurable (hT xb).aemeasurable
        (s / 2) (s / 2)
      rwa [add_halves, ← ncDistribution_congr_ae hTab] at h
    have h2 : ncDistribution μ (s / 2) (T xa) ≤ ((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ *
        ∫ ω, ∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ω).eigenvalues i|),
          |(hx ω).eigenvalues i| ^ p₀ ∂μ := by
      have h := h₀ xa hxam (fun ω => isHermitian_truncAbove _ _) hxaL (s / 2) hs2
      simp only [hXa] at h
      rw [mul_assoc, le_inv_mul_iff₀ (Real.rpow_pos_of_pos hs2 _)]
      exact h
    have h3 : ncDistribution μ (s / 2) (T xb) ≤ ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ *
        ∫ ω, ∑ i ∈ Finset.univ.filter (fun i => |(hx ω).eigenvalues i| ≤ s / 2),
          |(hx ω).eigenvalues i| ^ p₁ ∂μ := by
      have h := h₁ xb hxbm (fun ω => isHermitian_truncBelow _ _) hxbL (s / 2) hs2
      simp only [hXb] at h
      rw [mul_assoc, le_inv_mul_iff₀ (Real.rpow_pos_of_pos hs2 _)]
      exact h
    have key : ∀ ω, r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ *
          (∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ω).eigenvalues i|),
            |(hx ω).eigenvalues i| ^ p₀) + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ *
          ∑ i ∈ Finset.univ.filter (fun i => |(hx ω).eigenvalues i| ≤ s / 2),
            |(hx ω).eigenvalues i| ^ p₁) =
        ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s := by
      intro ω
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : s / 2 < |(hx ω).eigenvalues i|
      · rw [ite_eq_left hi, ite_eq_right (not_le.2 hi), ipdBound_of_lt hs hi]
      · rw [ite_eq_right hi, ite_eq_left (not_lt.1 hi), ipdBound_of_le hs (not_lt.1 hi)]
    have hI := ((hIa'.const_mul (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀)).add
      (hIb'.const_mul (((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁))).const_mul (r * s ^ (r - 1))
    refine ⟨hI.congr (Filter.Eventually.of_forall fun ω => key ω), ?_⟩
    calc r * s ^ (r - 1) * ncDistribution μ s (T x)
        ≤ r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ *
            (∫ ω, ∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ω).eigenvalues i|),
              |(hx ω).eigenvalues i| ^ p₀ ∂μ) + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ *
            ∫ ω, ∑ i ∈ Finset.univ.filter (fun i => |(hx ω).eigenvalues i| ≤ s / 2),
              |(hx ω).eigenvalues i| ^ p₁ ∂μ) :=
          mul_le_mul_of_nonneg_left (h1.trans (add_le_add h2 h3))
            (mul_nonneg hr.le (Real.rpow_nonneg hs.le _))
      _ = ∫ ω, ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s ∂μ := by
          rw [← integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul,
            integral_add (hIa'.const_mul _) (hIb'.const_mul _), integral_const_mul,
            integral_const_mul]
  -- the layer-cake formula, the pointwise bound, Tonelli and the integral of the bound
  have hmeas : Measurable fun q : ℝ × Ω =>
      ENNReal.ofReal (∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx q.2).eigenvalues i| q.1) := by
    have h : ∀ i, Measurable fun q : ℝ × Ω => ipdBound p₀ p₁ K₀ K₁ r |(hx q.2).eigenvalues i| q.1 :=
      fun i => (measurable_ipdBound p₀ p₁ K₀ K₁ r).comp
        (((hev i).comp measurable_snd).prodMk measurable_fst)
    exact ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => h i)
  have hmain : ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (T x ω) ^ r) ∂μ ≤
      ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ := by
    rw [lintegral_schattenNorm_rpow_eq (hT x).aemeasurable hr]
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (r * s ^ (r - 1) * ncDistribution μ s (T x))
        ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ω,
            ENNReal.ofReal (∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s) ∂μ := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
          obtain ⟨hi, hb⟩ := hbound s hs
          rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω =>
            Finset.sum_nonneg fun i _ =>
              ipdBound_nonneg hK₀ hK₁ hr.le (abs_nonneg _) (le_of_lt hs))]
          exact ENNReal.ofReal_le_ofReal hb
      _ = ∫⁻ ω, (∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i| s)) ∂μ :=
          lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ ω, ENNReal.ofReal C *
            ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ := by
          refine lintegral_congr fun ω => ?_
          have hint : ∀ i, IntegrableOn
              (ipdBound p₀ p₁ K₀ K₁ r |(hx ω).eigenvalues i|) (Ioi 0) := fun i =>
            (ipdBound_integral hp₀' hp₀r hrp₁ (abs_nonneg _)).1
          rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun i _ => hint i)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
              Finset.sum_nonneg fun i _ =>
                ipdBound_nonneg hK₀ hK₁ hr.le (abs_nonneg _) (le_of_lt hs))),
            integral_finsetSum _ fun i _ => hint i, ← ENNReal.ofReal_mul hC,
            schattenNorm_rpow_of_isHermitian (hx ω) hr, Finset.mul_sum]
          exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun i _ =>
            (ipdBound_integral hp₀' hp₀r hrp₁ (abs_nonneg _)).2)
      _ = ENNReal.ofReal C *
            ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (((measurable_schattenNorm (m := n) (n := n) _).comp hxΩ).pow_const r))
  -- back to the `eLpNorm` form
  rw [ipd_eLpNorm_eq (hT x).aemeasurable hr, ipd_eLpNorm_eq hxΩ.aemeasurable hr]
  calc (∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (T x ω) ^ r) ∂μ) ^ (1 / r)
      ≤ (ENNReal.ofReal C *
          ∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hmain (one_div_nonneg.2 hr.le)
    _ = ENNReal.ofReal (C ^ (1 / r)) *
          (∫⁻ ω, ENNReal.ofReal (schattenNorm (ENNReal.ofReal r) (x ω) ^ r) ∂μ) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr.le),
          ENNReal.ofReal_rpow_of_nonneg hC (one_div_nonneg.2 hr.le)]

end BanachProbability
