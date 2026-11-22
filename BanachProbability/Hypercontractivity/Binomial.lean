module

public import Mathlib.Analysis.Analytic.Binomial

/-!
# The even binomial series

For `|x| < 1` and real `r`, `((1 + x)^r + (1 − x)^r) / 2 = Σ_k C(r, 2k) x^{2k}`
(`hasSum_two_point_binomial`, the even part of Mathlib's binomial series
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, whose coefficients are `Ring.choose r k`). For
`1 ≤ r ≤ 2` every even coefficient is nonnegative (`ringChoose_two_mul_nonneg`: an even number of
negative factors), and for `1 < p ≤ q ≤ 2` the coefficients compare term by term,
`(p / q) ((p − 1) / (q − 1))^k C(q, 2k) ≤ C(p, 2k)` (`ringChoose_two_mul_le`), because
`r ↦ (j − r) / √(r − 1)` decreases on `(1, 2]` for `j ≥ 2`. These are the ingredients of the
two-point inequality for `1 < p ≤ q ≤ 2` (R. O'Donnell, *Analysis of Boolean Functions* (2014),
§10.1, following S. Janson).

The coefficients are handled through the product formula
`C(r, 2k + 2) = r (r − 1) Π_{j < 2k} (j + 2 − r) / (2k + 2)!`, in which the signs of the `2k`
factors `r − j`, `2 ≤ j ≤ 2k + 1`, have been reversed (an even number of them), as in O'Donnell's
proof.
-/

open Finset Polynomial

@[expose] public section

namespace BanachProbability

/-- The even part of the binomial series:
`((1 + x)^r + (1 − x)^r) / 2 = Σ_k C(r, 2k) x^{2k}` for `|x| < 1`. -/
theorem hasSum_two_point_binomial (r : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose r (2 * k) * x ^ (2 * k))
      (((1 + x) ^ r + (1 - x) ^ r) / 2) := by
  have hball : ∀ y : ℝ, |y| < 1 → y ∈ Metric.eball (0 : ℝ) 1 := fun y hy => by
    simpa [enorm_eq_nnnorm, ← NNReal.coe_lt_one] using hy
  -- the binomial series at `x` and at `−x`
  have h₁ := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := r)).hasSum (hball x hx)
  have h₂ := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := r)).hasSum
    (hball (-x) (by rwa [abs_neg]))
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, zero_add,
    smul_eq_mul] at h₁ h₂
  -- their average, whose odd terms vanish
  have h := (h₁.add h₂).div_const 2
  rw [← sub_eq_add_neg] at h
  have h' := ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff ?_).mpr h
  · convert h' using 2 with k
    simp only [Function.comp_apply, pow_mul, neg_sq]
    ring
  · rintro n hn
    have hodd : Odd n := by
      rw [Nat.odd_iff]
      by_contra h'
      exact hn ⟨n / 2, by simp only; omega⟩
    rw [hodd.neg_pow]
    ring

/-- `C(r, n) = r (r − 1) ⋯ (r − n + 1) / n!`. -/
private theorem ringChoose_eq_prod_div (r : ℝ) (n : ℕ) :
    Ring.choose r n = (∏ j ∈ range n, (r - j)) / n.factorial := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← descPochhammer_eval_eq_prod_range, inv_mul_eq_div,
    ← descPochhammer_map (Int.castRingHom ℝ), eval_map, ← aeval_eq_smeval, aeval_def,
    algebraMap_int_eq]

/-- Reversing an even number of signs:
`Π_{j < 2k + 2} (r − j) = r (r − 1) Π_{j < 2k} (j + 2 − r)`. -/
private theorem prod_range_two_mul_add_two (r : ℝ) (k : ℕ) :
    ∏ j ∈ range (2 * k + 2), (r - j) =
      r * (r - 1) * ∏ j ∈ range (2 * k), ((j : ℝ) + 2 - r) := by
  induction k with
  | zero => simp [prod_range_succ]
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 by ring, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      prod_range_succ, prod_range_succ, ih, prod_range_succ, prod_range_succ]
    push_cast
    ring

/-- `C(r, 2k + 2) = r (r − 1) Π_{j < 2k} (j + 2 − r) / (2k + 2)!`. -/
private theorem ringChoose_two_mul_succ (r : ℝ) (k : ℕ) :
    Ring.choose r (2 * (k + 1)) =
      r * (r - 1) * (∏ j ∈ range (2 * k), ((j : ℝ) + 2 - r)) / (2 * (k + 1)).factorial := by
  rw [ringChoose_eq_prod_div, show 2 * (k + 1) = 2 * k + 2 by ring, prod_range_two_mul_add_two]

/-- The factor-by-factor comparison: for `1 < p ≤ q ≤ 2` and `t ≥ 2`,
`√((p − 1) / (q − 1)) (t − q) ≤ t − p`, that is `(t − q) / √(q − 1) ≤ (t − p) / √(p − 1)`:
`r ↦ (t − r) / √(r − 1)` decreases on `(1, 2]` (numerator decreasing and nonnegative,
denominator increasing and positive). -/
private theorem sqrt_div_mul_sub_le {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2)
    (ht : 2 ≤ t) : √((p - 1) / (q - 1)) * (t - q) ≤ t - p := by
  have hp1 : 0 < √(p - 1) := Real.sqrt_pos.2 (by linarith)
  have hmono : (t - q) / √(q - 1) ≤ (t - p) / √(p - 1) :=
    calc (t - q) / √(q - 1) ≤ (t - p) / √(q - 1) :=
          div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      _ ≤ (t - p) / √(p - 1) :=
          div_le_div_of_nonneg_left (by linarith) hp1 (Real.sqrt_le_sqrt (by linarith))
  calc √((p - 1) / (q - 1)) * (t - q) = √(p - 1) * ((t - q) / √(q - 1)) := by
        rw [Real.sqrt_div (by linarith)]; ring
    _ ≤ √(p - 1) * ((t - p) / √(p - 1)) := mul_le_mul_of_nonneg_left hmono hp1.le
    _ = t - p := by field_simp

/-- For `1 ≤ r ≤ 2`, the even binomial coefficients `C(r, 2k)` are nonnegative. -/
theorem ringChoose_two_mul_nonneg {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) (k : ℕ) :
    0 ≤ Ring.choose r (2 * k) := by
  cases k with
  | zero => simp
  | succ m =>
    -- two nonnegative factors `r`, `r − 1`, and `2m` factors `j + 2 − r ≥ 0`
    rw [ringChoose_two_mul_succ]
    have hprod : 0 ≤ ∏ j ∈ range (2 * m), ((j : ℝ) + 2 - r) :=
      prod_nonneg fun j _ => by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hprod)
      (Nat.cast_nonneg _)

/-- The term-by-term comparison: for `1 < p ≤ q ≤ 2`,
`(p / q) ((p − 1) / (q − 1))^k C(q, 2k) ≤ C(p, 2k)`. -/
theorem ringChoose_two_mul_le {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2) (k : ℕ) :
    p / q * ((p - 1) / (q - 1)) ^ k * Ring.choose q (2 * k) ≤ Ring.choose p (2 * k) := by
  cases k with
  | zero =>
    simpa [Ring.choose_zero_right] using div_le_one_of_le₀ hpq (by linarith)
  | succ m =>
    rw [ringChoose_two_mul_succ, ringChoose_two_mul_succ]
    set s := √((p - 1) / (q - 1))
    have hs : s ^ 2 = (p - 1) / (q - 1) := Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
    -- pair each of the `2m` factors `j + 2 − q` with one `s`
    have hprod : ((p - 1) / (q - 1)) ^ m * ∏ j ∈ range (2 * m), ((j : ℝ) + 2 - q) =
        ∏ j ∈ range (2 * m), (s * ((j : ℝ) + 2 - q)) := by
      rw [prod_mul_distrib, prod_const, card_range, pow_mul, hs]
    have key : ∏ j ∈ range (2 * m), (s * ((j : ℝ) + 2 - q)) ≤
        ∏ j ∈ range (2 * m), ((j : ℝ) + 2 - p) :=
      prod_le_prod₀
        (fun j _ => mul_nonneg (Real.sqrt_nonneg _)
          (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
        (fun j _ => sqrt_div_mul_sub_le hp hpq hq
          (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
    have hq0 : q ≠ 0 := by linarith
    have hq1 : q - 1 ≠ 0 := by linarith
    -- cancel `p (p − 1)` against `(p / q) ((p − 1) / (q − 1)) q (q − 1)`
    calc p / q * ((p - 1) / (q - 1)) ^ (m + 1) *
          (q * (q - 1) * (∏ j ∈ range (2 * m), ((j : ℝ) + 2 - q)) / (2 * (m + 1)).factorial)
        = p * (p - 1) * (((p - 1) / (q - 1)) ^ m * ∏ j ∈ range (2 * m), ((j : ℝ) + 2 - q)) /
            (2 * (m + 1)).factorial := by
          rw [pow_succ]
          generalize ((p - 1) / (q - 1)) ^ m = X
          field_simp
      _ ≤ p * (p - 1) * (∏ j ∈ range (2 * m), ((j : ℝ) + 2 - p)) / (2 * (m + 1)).factorial := by
          rw [hprod]
          gcongr

end BanachProbability
