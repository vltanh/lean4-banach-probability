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
      ENNReal.ofReal K * eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ

/-- A strong type `(p, p)` bound gives the weak type `(p, p)` bound with the same constant
(Chebyshev). -/
theorem IsStrongTypeNC.isWeakTypeNC [IsFiniteMeasure μ]
    {T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ} (hT : ∀ x, Measurable (T x)) {p K : ℝ}
    (hp : 1 ≤ p) (hK : 0 ≤ K) (h : IsStrongTypeNC μ m T p K) : IsWeakTypeNC μ m T p K := by
  sorry

/-- **Marcinkiewicz interpolation** on `L^r (L^∞ (Ω) ⊗ M_n)`, with two endpoints
`1 ≤ p₀ < r < p₁`. -/
theorem marcinkiewicz [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ} (hT : ∀ x, Measurable (T x))
    (hadd : ∀ x y, MatrixMemLp x 1 μ → MatrixMemLp y 1 μ → T (x + y) =ᵐ[μ] T x + T y)
    {p₀ p₁ K₀ K₁ r : ℝ} (hp₀ : 1 ≤ p₀) (hp₀r : p₀ < r) (hrp₁ : r < p₁) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (h₀ : IsWeakTypeNC μ m T p₀ K₀) (h₁ : IsWeakTypeNC μ m T p₁ K₁) :
    IsStrongTypeNC μ m T r ((2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r))) ^ (1 / r)) := by
  sorry

end BanachProbability
