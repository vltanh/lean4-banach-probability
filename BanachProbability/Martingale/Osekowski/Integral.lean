module

public import BanachProbability.Martingale.Burkholder.Function
public import BanachProbability.Martingale.Osekowski.SimpleFunctions
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Burkholder's function as an integral of the simple functions

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012, p. 54 and 58: Burkholder's function `U_p` is the integral of `U₁` (for `1 < p < 2`)
or of `U_∞` (for `p > 2`) against a power of `t`, which the source states without proof.

The functions depend on the norms only: `s = |x|` (the position of the dominating martingale) and
`r = |y|` (that of the subordinate one), so `U_p (x, y)` is `burkholderU p r s`, and
`U₁ (x / t, y / t)` is `uOne (s / t) (r / t)`.

## Main results

* `burkholderU_eq_integral_uOne`: for `1 < p < 2`,
  `U_p (x, y) = (p^{3−p} (2 − p) / 2) ∫_0^∞ t^{p−1} U₁ (x / t, y / t) dt`. (The source has a
  factor `p − 1` in the constant, which does not belong there.)
* `integral_abs_uOne_le`: `∫_0^∞ t^{p−1} |U₁ (x / t, y / t)| dt ≤ c (|y|^p + |x|^p / (p − 1))`, by
  (3.14).
* `burkholderU_eq_integral_uInfty`: for `p > 2`,
  `U_p (x, y) = (p^{3−p} (p − 1)^p (p − 2) / 2) ∫_0^∞ t^{p−1} U_∞ (x / t, y / t) dt`.
* `integral_abs_uInfty_le`: `∫_0^∞ t^{p−1} |U_∞ (x / t, y / t)| dt ≤ c (|x| + |y|)^p`, by (3.15).
-/

@[expose] public section

open MeasureTheory Set

namespace BanachProbability.Osekowski

/-! ### Integrals of powers -/

private theorem integrableOn_Ioc_rpow {a q : ℝ} (hq : -1 < q) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t ^ q) (Ioc 0 a) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).1
    (intervalIntegral.intervalIntegrable_rpow' hq)

/-- `∫_0^a t^q dt = a^{q+1} / (q + 1)` for `q > −1`. -/
private theorem integral_Ioc_rpow {a q : ℝ} (hq : -1 < q) (ha : 0 ≤ a) :
    ∫ t in Ioc 0 a, t ^ q = a ^ (q + 1) / (q + 1) := by
  rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hq),
    Real.zero_rpow (by linarith), sub_zero]

/-- Splitting an integral over `(0, ∞)` at `a ≥ 0`. -/
private theorem integrableOn_and_integral_split {a : ℝ} (ha : 0 ≤ a) {F G K : ℝ → ℝ}
    (hFG : ∀ t ∈ Ioc 0 a, F t = G t) (hFK : ∀ t ∈ Ioi a, F t = K t)
    (hG : IntegrableOn G (Ioc 0 a)) (hK : IntegrableOn K (Ioi a)) :
    IntegrableOn F (Ioi 0) ∧
      ∫ t in Ioi 0, F t = (∫ t in Ioc 0 a, G t) + ∫ t in Ioi a, K t := by
  have h1 : IntegrableOn F (Ioc 0 a) := hG.congr_fun (fun t ht => (hFG t ht).symm) measurableSet_Ioc
  have h2 : IntegrableOn F (Ioi a) := hK.congr_fun (fun t ht => (hFK t ht).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi ha]
  refine ⟨h1.union h2, ?_⟩
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2,
    setIntegral_congr_fun measurableSet_Ioc hFG, setIntegral_congr_fun measurableSet_Ioi hFK]

/-! ### The case `1 < p < 2` -/

/-- The integral of `U₁`, `1 < p < 2`: with `a = |x| + |y|`, `t^{p−1} U₁ (x / t, y / t)` is
`t^{p−1} − 2 |x| t^{p−2}` for `t ≤ a` and `(|y|² − |x|²) t^{p−3}` for `t > a`. -/
theorem integrableOn_and_integral_uOne {p s r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 ≤ s)
    (hr : 0 ≤ r) : IntegrableOn (fun t : ℝ => t ^ (p - 1) * uOne (s / t) (r / t)) (Ioi 0) ∧
      ∫ t in Ioi 0, t ^ (p - 1) * uOne (s / t) (r / t) =
        2 / (p * (2 - p)) * ((r - s / (p - 1)) * (s + r) ^ (p - 1)) := by
  have hp1' : p - 1 ≠ 0 := by linarith
  rcases (add_nonneg hs hr).eq_or_lt with ha | ha
  · obtain rfl : s = 0 := by linarith
    obtain rfl : r = 0 := by linarith
    simp [uOne, Real.zero_rpow hp1']
  set a := s + r with ha_def
  have hG : ∀ t ∈ Ioc 0 a, t ^ (p - 1) * uOne (s / t) (r / t) =
      t ^ (p - 1) - 2 * s * t ^ (p - 2) := fun t ht => by
    have h : ¬ s / t + r / t < 1 := by
      rw [← add_div, not_lt, le_div_iff₀ ht.1, one_mul]; exact ht.2
    rw [uOne, ite_eq_right h, show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one ht.1.ne' (p - 1)]
    field_simp
  have hK : ∀ t ∈ Ioi a, t ^ (p - 1) * uOne (s / t) (r / t) = (r ^ 2 - s ^ 2) * t ^ (p - 3) :=
    fun t ht => by
      have ht0 : 0 < t := ha.trans ht
      have h : s / t + r / t < 1 := by rw [← add_div, div_lt_one ht0]; exact ht
      rw [uOne, ite_eq_left h, show p - 3 = p - 1 - 1 - 1 by ring,
        Real.rpow_sub_one ht0.ne' (p - 1 - 1), Real.rpow_sub_one ht0.ne' (p - 1)]
      field_simp
  have hi1 := integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 1) ha.le
  have hi2 := (integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 2) ha.le).const_mul (2 * s)
  have hi3 := (integrableOn_Ioi_rpow_of_lt (by linarith : p - 3 < -1) ha).const_mul (r ^ 2 - s ^ 2)
  obtain ⟨h1, h2⟩ := integrableOn_and_integral_split ha.le hG hK (hi1.sub hi2) hi3
  refine ⟨h1, ?_⟩
  rw [h2, integral_sub hi1 hi2, integral_const_mul, integral_const_mul,
    integral_Ioc_rpow (by linarith) ha.le, integral_Ioc_rpow (by linarith) ha.le,
    integral_Ioi_rpow_of_lt (by linarith) ha]
  have e1 : a ^ (p - 1 + 1) = a ^ (p - 1) * a := Real.rpow_add_one ha.ne' _
  have e2 : a ^ (p - 2 + 1) = a ^ (p - 1) := by ring_nf
  have e3 : a ^ (p - 3 + 1) = a ^ (p - 1) / a := by
    rw [← Real.rpow_sub_one ha.ne']; ring_nf
  have hp0 : p ≠ 0 := by linarith
  have hp2' : 2 - p ≠ 0 := by linarith
  have hp2'' : p - 3 + 1 ≠ 0 := by linarith
  have hp1'' : p - 2 + 1 ≠ 0 := by linarith
  rw [e1, e2, e3, show r ^ 2 - s ^ 2 = (r - s) * a by rw [ha_def]; ring]
  rw [show p - 1 + 1 = p by ring, show p - 2 + 1 = p - 1 by ring,
    show p - 3 + 1 = -(2 - p) by ring]
  field_simp
  rw [ha_def]
  ring

/-- `p^{2−p} = p (1 − 1 / p*)^{p−1}` for `1 < p ≤ 2`, the constant of `U_p` (3.60). -/
private theorem burkholderU_of_le_two {p s r : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    Burkholder.burkholderU p r s =
      p ^ (2 - p) * ((r - s / (p - 1)) * (s + r) ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1' : p - 1 ≠ 0 := by linarith
  have hP : max p (p / (p - 1)) = p / (p - 1) :=
    max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)
  have e1 : p * (1 - 1 / (p / (p - 1))) ^ (p - 1) = p ^ (2 - p) := by
    rw [show 1 - 1 / (p / (p - 1)) = p⁻¹ by field_simp; ring, Real.inv_rpow hp0.le,
      ← Real.rpow_neg hp0.le, show (2 : ℝ) - p = 1 + -(p - 1) by ring, Real.rpow_add hp0,
      Real.rpow_one]
  rw [Burkholder.burkholderU, hP, e1, add_comm r s]
  field_simp
  ring

/-- **The integral formula for `1 < p < 2`** (p. 54):
`U_p (x, y) = (p^{3−p} (2 − p) / 2) ∫_0^∞ t^{p−1} U₁ (x / t, y / t) dt`. The source has a factor
`p − 1` in the constant, which does not belong there. -/
theorem burkholderU_eq_integral_uOne {p s r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 ≤ s)
    (hr : 0 ≤ r) : Burkholder.burkholderU p r s =
      p ^ (3 - p) * (2 - p) / 2 * ∫ t in Ioi 0, t ^ (p - 1) * uOne (s / t) (r / t) := by
  have hp0 : p ≠ 0 := by linarith
  have hp2' : 2 - p ≠ 0 := by linarith
  rw [burkholderU_of_le_two hp1 hp2.le, (integrableOn_and_integral_uOne hp1 hp2 hs hr).2,
    show (3 : ℝ) - p = 2 - p + 1 by ring, Real.rpow_add_one hp0]
  field_simp

/-- The absolute integrability for `1 < p < 2` (p. 54), by (3.14):
`∫_0^∞ t^{p−1} |U₁ (x / t, y / t)| dt ≤ ∫_0^∞ t^{p−1} (U₁ (0, y / t) − U₁ (x / t, 0)) dt =
c (|y|^p + |x|^p / (p − 1))`, `c = 2 / (p (2 − p))`. (The middle term is `U_p (0, y) − U_p (x, 0)`
up to the constant of the integral formula, which the book omits.) -/
theorem integral_abs_uOne_le {p s r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ∫ t in Ioi 0, |t ^ (p - 1) * uOne (s / t) (r / t)| ≤
      2 / (p * (2 - p)) * (r ^ p + s ^ p / (p - 1)) := by
  obtain ⟨hi, -⟩ := integrableOn_and_integral_uOne hp1 hp2 hs hr
  obtain ⟨hir, hr'⟩ := integrableOn_and_integral_uOne hp1 hp2 le_rfl hr
  obtain ⟨his, hs'⟩ := integrableOn_and_integral_uOne hp1 hp2 hs le_rfl
  have hpow : ∀ z : ℝ, 0 ≤ z → z * z ^ (p - 1) = z ^ p := fun z hz => by
    rw [← Real.rpow_one_add' hz (by linarith), add_sub_cancel]
  calc ∫ t in Ioi 0, |t ^ (p - 1) * uOne (s / t) (r / t)|
      ≤ ∫ t in Ioi 0,
          (t ^ (p - 1) * uOne (0 / t) (r / t) - t ^ (p - 1) * uOne (s / t) (0 / t)) := by
        refine setIntegral_mono_on hi.abs (hir.sub his) measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _), zero_div, ← mul_sub]
        exact mul_le_mul_of_nonneg_left (abs_uOne_le (div_nonneg hs ht0.le) (div_nonneg hr ht0.le))
          (Real.rpow_nonneg ht0.le _)
    _ = 2 / (p * (2 - p)) * (r ^ p + s ^ p / (p - 1)) := by
        rw [integral_sub hir his, hr', hs', ← hpow r hr, ← hpow s hs]
        simp only [zero_div, zero_add, add_zero, sub_zero, zero_sub]
        ring

/-! ### The case `p > 2` -/

/-- `U_∞ (x, y) = (|y| − 1)² − |x|²` for `|x| + |y| ≥ 1`. -/
private theorem uInfty_of_one_le {s r : ℝ} (h : 1 ≤ s + r) : uInfty s r = (r - 1) ^ 2 - s ^ 2 := by
  unfold uInfty
  split_ifs with h2
  · rw [show r = 1 - s by linarith]
    ring
  · rfl

/-- The integral of `U_∞`, `p > 2`: with `a = |x| + |y|`, `t^{p−1} U_∞ (x / t, y / t)` is
`(|y|² − |x|²) t^{p−3} − 2 |y| t^{p−2} + t^{p−1}` for `t ≤ a` and `0` for `t > a`. -/
theorem integrableOn_and_integral_uInfty {p s r : ℝ} (hp2 : 2 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * uInfty (s / t) (r / t)) (Ioi 0) ∧
      ∫ t in Ioi 0, t ^ (p - 1) * uInfty (s / t) (r / t) =
        2 / (p * (p - 1) * (p - 2)) * ((r - (p - 1) * s) * (s + r) ^ (p - 1)) := by
  have hp1' : p - 1 ≠ 0 := by linarith
  rcases (add_nonneg hs hr).eq_or_lt with ha | ha
  · obtain rfl : s = 0 := by linarith
    obtain rfl : r = 0 := by linarith
    simp [uInfty, Real.zero_rpow hp1']
  set a := s + r with ha_def
  have hG : ∀ t ∈ Ioc 0 a, t ^ (p - 1) * uInfty (s / t) (r / t) =
      (r ^ 2 - s ^ 2) * t ^ (p - 3) - 2 * r * t ^ (p - 2) + t ^ (p - 1) := fun t ht => by
    have h : 1 ≤ s / t + r / t := by rw [← add_div, le_div_iff₀ ht.1, one_mul]; exact ht.2
    rw [uInfty_of_one_le h, show p - 3 = p - 1 - 1 - 1 by ring, show p - 2 = p - 1 - 1 by ring,
      Real.rpow_sub_one ht.1.ne' (p - 1 - 1), Real.rpow_sub_one ht.1.ne' (p - 1)]
    have := ht.1.ne'
    field_simp
    ring
  have hK : ∀ t ∈ Ioi a, t ^ (p - 1) * uInfty (s / t) (r / t) = 0 := fun t ht => by
    have ht0 : 0 < t := ha.trans ht
    have h : s / t + r / t ≤ 1 := by rw [← add_div, div_le_one ht0]; exact (mem_Ioi.1 ht).le
    rw [uInfty, ite_eq_left h, mul_zero]
  have hi1 := integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 1) ha.le
  have hi2 := (integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 2) ha.le).const_mul (2 * r)
  have hi3 := (integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 3) ha.le).const_mul
    (r ^ 2 - s ^ 2)
  obtain ⟨h1, h2⟩ := integrableOn_and_integral_split ha.le hG hK ((hi3.sub hi2).add hi1)
    integrableOn_zero
  refine ⟨h1, ?_⟩
  have h3 : ∫ t in Ioc 0 a, ((r ^ 2 - s ^ 2) * t ^ (p - 3) - 2 * r * t ^ (p - 2) + t ^ (p - 1)) =
      (∫ t in Ioc 0 a, ((r ^ 2 - s ^ 2) * t ^ (p - 3) - 2 * r * t ^ (p - 2))) +
        ∫ t in Ioc 0 a, t ^ (p - 1) := integral_add (hi3.sub hi2) hi1
  rw [h2, integral_zero, add_zero, h3, integral_sub hi3 hi2, integral_const_mul,
    integral_const_mul, integral_Ioc_rpow (by linarith) ha.le,
    integral_Ioc_rpow (by linarith) ha.le, integral_Ioc_rpow (by linarith) ha.le]
  have e1 : a ^ (p - 1 + 1) = a ^ (p - 1) * a := Real.rpow_add_one ha.ne' _
  have e2 : a ^ (p - 2 + 1) = a ^ (p - 1) := by ring_nf
  have e3 : a ^ (p - 3 + 1) = a ^ (p - 1) / a := by
    rw [← Real.rpow_sub_one ha.ne']; ring_nf
  have hp0 : p ≠ 0 := by linarith
  have hp2' : p - 2 ≠ 0 := by linarith
  rw [e1, e2, e3, show r ^ 2 - s ^ 2 = (r - s) * a by rw [ha_def]; ring,
    show p - 1 + 1 = p by ring, show p - 2 + 1 = p - 1 by ring, show p - 3 + 1 = p - 2 by ring]
  field_simp
  rw [ha_def]
  ring

/-- `p^{2−p} (p − 1)^{p−1} = p (1 − 1 / p)^{p−1}` for `p ≥ 2`, the constant of `U_p` (p. 58). -/
private theorem burkholderU_of_two_le {p s r : ℝ} (hp2 : 2 ≤ p) :
    Burkholder.burkholderU p r s =
      p ^ (2 - p) * (p - 1) ^ (p - 1) * ((r - (p - 1) * s) * (s + r) ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have e1 : p * (1 - 1 / p) ^ (p - 1) = p ^ (2 - p) * (p - 1) ^ (p - 1) := by
    rw [show 1 - 1 / p = (p - 1) / p by field_simp, Real.div_rpow (by linarith) hp0.le,
      show (2 : ℝ) - p = 1 - (p - 1) by ring, Real.rpow_sub hp0 1, Real.rpow_one]
    ring
  rw [Burkholder.burkholderU, Burkholder.max_div_sub_one_eq_self hp2, e1, add_comm r s]
  ring

/-- **The integral formula for `p > 2`** (p. 58):
`U_p (x, y) = (p^{3−p} (p − 1)^p (p − 2) / 2) ∫_0^∞ t^{p−1} U_∞ (x / t, y / t) dt`. -/
theorem burkholderU_eq_integral_uInfty {p s r : ℝ} (hp2 : 2 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    Burkholder.burkholderU p r s = p ^ (3 - p) * (p - 1) ^ p * (p - 2) / 2 *
      ∫ t in Ioi 0, t ^ (p - 1) * uInfty (s / t) (r / t) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1' : p - 1 ≠ 0 := by linarith
  have hp2' : p - 2 ≠ 0 := by linarith
  have e : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    rw [← Real.rpow_add_one hp1', sub_add_cancel]
  rw [burkholderU_of_two_le hp2.le, (integrableOn_and_integral_uInfty hp2 hs hr).2,
    show (3 : ℝ) - p = 2 - p + 1 by ring, Real.rpow_add_one hp0, e]
  field_simp

/-- The absolute integrability for `p > 2` (p. 58), by (3.15): with `a = |x| + |y|`,
`∫_0^∞ t^{p−1} |U_∞ (x / t, y / t)| dt ≤ ∫_0^a t^{p−1} (1 + (|x|² + |y|²) / t²) dt ≤ c a^p`,
`c = 1 / p + 1 / (p − 2)`. -/
theorem integral_abs_uInfty_le {p s r : ℝ} (hp2 : 2 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ∫ t in Ioi 0, |t ^ (p - 1) * uInfty (s / t) (r / t)| ≤
      (1 / p + 1 / (p - 2)) * (s + r) ^ p := by
  obtain ⟨hi, -⟩ := integrableOn_and_integral_uInfty hp2 hs hr
  have ha : 0 ≤ s + r := add_nonneg hs hr
  set a := s + r with ha_def
  have hi1 := integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 1) ha
  have hi2 := (integrableOn_Ioc_rpow (a := a) (by linarith : -1 < p - 3) ha).const_mul
    (s ^ 2 + r ^ 2)
  have h0 : ∀ t ∈ Ioi a, |t ^ (p - 1) * uInfty (s / t) (r / t)| = 0 := fun t ht => by
    have ht0 : 0 < t := ha.trans_lt ht
    have h : s / t + r / t ≤ 1 := by rw [← add_div, div_le_one ht0]; exact (mem_Ioi.1 ht).le
    rw [uInfty, ite_eq_left h, mul_zero, abs_zero]
  have hi0 : IntegrableOn (fun t : ℝ => |t ^ (p - 1) * uInfty (s / t) (r / t)|) (Ioi 0) := hi.abs
  have hia := hi0.mono_set (fun t (ht : t ∈ Ioc 0 a) => mem_Ioi.2 ht.1)
  rw [← Ioc_union_Ioi_eq_Ioi ha, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hia
    (hi0.mono_set (Ioi_subset_Ioi ha)), setIntegral_congr_fun measurableSet_Ioi h0, integral_zero,
    add_zero]
  calc ∫ t in Ioc 0 a, |t ^ (p - 1) * uInfty (s / t) (r / t)|
      ≤ ∫ t in Ioc 0 a, (t ^ (p - 1) + (s ^ 2 + r ^ 2) * t ^ (p - 3)) := by
        refine setIntegral_mono_on hia (hi1.add hi2) measurableSet_Ioc fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht.1
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        refine (mul_le_mul_of_nonneg_left (abs_uInfty_le (div_nonneg hr ht0.le))
          (Real.rpow_nonneg ht0.le _)).trans_eq ?_
        rw [show p - 3 = p - 1 - 1 - 1 by ring, Real.rpow_sub_one ht0.ne' (p - 1 - 1),
          Real.rpow_sub_one ht0.ne' (p - 1)]
        field_simp
        ring
    _ = a ^ p / p + (s ^ 2 + r ^ 2) * (a ^ (p - 2) / (p - 2)) := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_Ioc_rpow (by linarith) ha,
          integral_Ioc_rpow (by linarith) ha, show p - 1 + 1 = p by ring,
          show p - 3 + 1 = p - 2 by ring]
    _ ≤ a ^ p / p + a ^ 2 * (a ^ (p - 2) / (p - 2)) := by
        have h1 : s ^ 2 + r ^ 2 ≤ a ^ 2 := by rw [ha_def]; nlinarith [mul_nonneg hs hr]
        have h2 : 0 ≤ a ^ (p - 2) / (p - 2) :=
          div_nonneg (Real.rpow_nonneg ha _) (by linarith)
        linarith [mul_le_mul_of_nonneg_right h1 h2]
    _ = (1 / p + 1 / (p - 2)) * a ^ p := by
        have e : a ^ 2 * a ^ (p - 2) = a ^ p := by
          rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg ha (by norm_num) (by linarith)]
          ring_nf
        rw [← mul_div_assoc, e]
        ring

end BanachProbability.Osekowski
