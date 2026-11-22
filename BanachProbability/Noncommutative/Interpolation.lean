module

public import BanachProbability.Noncommutative.Distribution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Marcinkiewicz interpolation on the matrix cube

A linear map `T` on matrix-valued functions on the sign cube that is of weak type `(p_j, p_j)`
with constant `K_j` on symmetric-matrix-valued functions, `j = 0, 1`, `p₀ < p₁`, is of strong
type `(r, r)` for `p₀ < r < p₁`:
`‖T x‖_{L^r}^r ≤ 2^r r (K₀^{p₀} / (r − p₀) + K₁^{p₁} / (p₁ − r)) ‖x‖_{L^r}^r`
(`marcinkiewicz`; J. Marcinkiewicz, C. R. Acad. Sci. Paris 208 (1939); for noncommutative `L^p`
spaces, e.g. Randrianantoanina (2002), the interpolation step of Theorem 4.3). The proof is the
classical one, with the spectral truncations: to bound `λ_s (T x)`, split `x` at level `s / 2`
into `x 1_{(s/2, ∞)} (|x|)` and `x 1_{[0, s/2]} (|x|)` pointwise (`truncAbove`, `truncBelow`), use
the subadditivity of the distribution function (`distribution_add_add_le`) and the two weak type
bounds, and integrate with the layer-cake formula (`avg_schattenNorm_rpow_eq_integral`): each
eigenvalue modulus `a = |λ_i (x ε)|` contributes
`∫_0^{2a} r s^{r−1} (s/2)^{−p₀} a^{p₀} ds = 2^r r a^r / (r − p₀)` and
`∫_{2a}^∞ r s^{r−1} (s/2)^{−p₁} a^{p₁} ds = 2^r r a^r / (p₁ − r)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

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

/-- `T` is of weak type `(p, p)` with constant `K` on symmetric-matrix-valued functions:
`s^p λ_s (T x) ≤ K^p ‖x‖_{L^p}^p`. -/
def IsWeakType (T : ((Fin N → Bool) → Matrix n n ℝ) → ((Fin N → Bool) → Matrix n n ℝ))
    (p K : ℝ) : Prop :=
  ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) → ∀ s : ℝ, 0 < s →
    s ^ p * distribution s (T x) ≤ K ^ p * avg fun ε => schattenNorm (ENNReal.ofReal p) (x ε) ^ p

/-- A strong type `(p, p)` bound gives the weak type `(p, p)` bound with the same constant
(Chebyshev). -/
theorem isWeakType_of_lpNorm_le
    {T : ((Fin N → Bool) → Matrix n n ℝ) → ((Fin N → Bool) → Matrix n n ℝ)} {p K : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K)
    (h : ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) →
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p (T x) ≤
        K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p x) :
    IsWeakType T p K := by
  intro x hx s hs
  have hS : ∀ A : Matrix n n ℝ, 0 ≤ schattenNorm (ENNReal.ofReal p) A :=
    fun A => schattenNorm_nonneg _ A
  have hpow : ∀ y : (Fin N → Bool) → Matrix n n ℝ,
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p y ^ p =
        avg fun ε => schattenNorm (ENNReal.ofReal p) (y ε) ^ p := by
    intro y
    unfold SignCube.lpNorm
    rw [← Real.rpow_mul (avg_nonneg fun ε => Real.rpow_nonneg (hS _) p),
      one_div_mul_cancel hp.ne', Real.rpow_one]
  calc s ^ p * distribution s (T x) = distribution s (T x) * s ^ p := mul_comm _ _
    _ ≤ avg fun ε => schattenNorm (ENNReal.ofReal p) (T x ε) ^ p :=
        distribution_mul_rpow_le hs hp (T x)
    _ = SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p (T x) ^ p := (hpow _).symm
    _ ≤ (K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p x) ^ p :=
        Real.rpow_le_rpow (lpNorm_nonneg hS _ _) (h x hx) hp.le
    _ = K ^ p * avg fun ε => schattenNorm (ENNReal.ofReal p) (x ε) ^ p := by
        rw [Real.mul_rpow hK (lpNorm_nonneg hS _ _), hpow]

set_option linter.unusedVariables false in
/-- **Marcinkiewicz interpolation** on the matrix cube, with two endpoints `p₀ < r < p₁`. -/
theorem marcinkiewicz (T : ((Fin N → Bool) → Matrix n n ℝ) →ₗ[ℝ] ((Fin N → Bool) → Matrix n n ℝ))
    {p₀ p₁ K₀ K₁ r : ℝ} (hp₀ : 0 < p₀) (hp₀r : p₀ < r) (hrp₁ : r < p₁) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (h₀ : IsWeakType T p₀ K₀) (h₁ : IsWeakType T p₁ K₁)
    (x : (Fin N → Bool) → Matrix n n ℝ) (hx : ∀ ε, (x ε).IsHermitian) :
    (avg fun ε => schattenNorm (ENNReal.ofReal r) (T x ε) ^ r) ≤
      2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r)) *
        avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
  -- the constants `K₀, K₁` enter only through `K₀^{p₀}, K₁^{p₁}`: their signs are not used
  have hr : 0 < r := by linarith
  have hint : ∀ ε i, IntegrableOn (ipdBound p₀ p₁ K₀ K₁ r |(hx ε).eigenvalues i|) (Ioi 0) :=
    fun ε i => (ipdBound_integral hp₀ hp₀r hrp₁ (abs_nonneg _)).1
  -- the bound `G (s) = E Σ_i φ (|λ_i (x ε)|) (s)` for `r s^{r−1} λ_s (T x)`
  let G : ℝ → ℝ := fun s => avg fun ε => ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ε).eigenvalues i| s
  have hGi : IntegrableOn G (Ioi 0) :=
    (integrable_finsetSum _ fun ε _ => integrable_finsetSum _ fun i _ => hint ε i).div_const _
  have hGint : ∫ s in Ioi (0 : ℝ), G s = 2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r)) *
      avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
    simp only [G, avg]
    rw [integral_div, integral_finsetSum _ fun ε _ => integrable_finsetSum _ fun i _ => hint ε i,
      mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [integral_finsetSum _ fun i _ => hint ε i, schattenNorm_rpow_of_isHermitian (hx ε) hr,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (ipdBound_integral hp₀ hp₀r hrp₁ (abs_nonneg _)).2
  -- the pointwise bound: split `x` at level `s / 2`, subadditivity, the two weak type bounds
  have hbound : ∀ s : ℝ, 0 < s → r * s ^ (r - 1) * distribution s (T x) ≤ G s := by
    intro s hs
    have hs2 : 0 < s / 2 := half_pos hs
    have hxab : x = (fun ε => truncAbove (s / 2) (x ε)) + fun ε => truncBelow (s / 2) (x ε) :=
      funext fun ε => (truncAbove_add_truncBelow (hx ε) (s / 2)).symm
    have h1 : distribution s (T x) ≤ distribution (s / 2) (T fun ε => truncAbove (s / 2) (x ε)) +
        distribution (s / 2) (T fun ε => truncBelow (s / 2) (x ε)) := by
      have := distribution_add_add_le (s / 2) (s / 2) (T fun ε => truncAbove (s / 2) (x ε))
        (T fun ε => truncBelow (s / 2) (x ε))
      rwa [add_halves, ← map_add, ← hxab] at this
    have h2 : distribution (s / 2) (T fun ε => truncAbove (s / 2) (x ε)) ≤
        ((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ * avg fun ε =>
          ∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ε).eigenvalues i|),
            |(hx ε).eigenvalues i| ^ p₀ := by
      have := h₀ (fun ε => truncAbove (s / 2) (x ε)) (fun ε => isHermitian_truncAbove _ _)
        (s / 2) hs2
      simp only [fun ε => schattenNorm_truncAbove_rpow (hx ε) (s / 2) hp₀] at this
      rw [mul_assoc, le_inv_mul_iff₀ (Real.rpow_pos_of_pos hs2 _)]
      exact this
    have h3 : distribution (s / 2) (T fun ε => truncBelow (s / 2) (x ε)) ≤
        ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ * avg fun ε =>
          ∑ i ∈ Finset.univ.filter (fun i => |(hx ε).eigenvalues i| ≤ s / 2),
            |(hx ε).eigenvalues i| ^ p₁ := by
      have := h₁ (fun ε => truncBelow (s / 2) (x ε)) (fun ε => isHermitian_truncBelow _ _)
        (s / 2) hs2
      simp only [fun ε => schattenNorm_truncBelow_rpow (hx ε) (s / 2) (hr.trans hrp₁)] at this
      rw [mul_assoc, le_inv_mul_iff₀ (Real.rpow_pos_of_pos hs2 _)]
      exact this
    have key : ∀ ε, r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ *
          (∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ε).eigenvalues i|),
            |(hx ε).eigenvalues i| ^ p₀) + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ *
          ∑ i ∈ Finset.univ.filter (fun i => |(hx ε).eigenvalues i| ≤ s / 2),
            |(hx ε).eigenvalues i| ^ p₁) =
        ∑ i, ipdBound p₀ p₁ K₀ K₁ r |(hx ε).eigenvalues i| s := by
      intro ε
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : s / 2 < |(hx ε).eigenvalues i|
      · rw [ite_eq_left hi, ite_eq_right (not_le.2 hi), ipdBound_of_lt hs hi]
      · rw [ite_eq_right hi, ite_eq_left (not_lt.1 hi), ipdBound_of_le hs (not_lt.1 hi)]
    calc r * s ^ (r - 1) * distribution s (T x)
        ≤ r * s ^ (r - 1) * (((s / 2) ^ p₀)⁻¹ * K₀ ^ p₀ * (avg fun ε =>
            ∑ i ∈ Finset.univ.filter (fun i => s / 2 < |(hx ε).eigenvalues i|),
              |(hx ε).eigenvalues i| ^ p₀) + ((s / 2) ^ p₁)⁻¹ * K₁ ^ p₁ * avg fun ε =>
            ∑ i ∈ Finset.univ.filter (fun i => |(hx ε).eigenvalues i| ≤ s / 2),
              |(hx ε).eigenvalues i| ^ p₁) :=
          mul_le_mul_of_nonneg_left (h1.trans (add_le_add h2 h3)) (by positivity)
      _ = G s := by
          simp only [G, ← key]
          rw [avg_const_mul, avg_add, avg_const_mul, avg_const_mul]
  -- the layer-cake formula and the integral of the bound
  rw [avg_schattenNorm_rpow_eq_integral hr (T x), ← hGint]
  refine integral_mono_of_nonneg ?_ hGi ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
      mul_nonneg (mul_nonneg hr.le (Real.rpow_nonneg (le_of_lt hs) _))
        (avg_nonneg fun ε => Nat.cast_nonneg _))
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound)

end BanachProbability
