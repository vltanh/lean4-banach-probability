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
-/

@[expose] public section

namespace BanachProbability

/-- The even part of the binomial series:
`((1 + x)^r + (1 − x)^r) / 2 = Σ_k C(r, 2k) x^{2k}` for `|x| < 1`. -/
theorem hasSum_two_point_binomial (r : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose r (2 * k) * x ^ (2 * k))
      (((1 + x) ^ r + (1 - x) ^ r) / 2) := by
  sorry

/-- For `1 ≤ r ≤ 2`, the even binomial coefficients `C(r, 2k)` are nonnegative. -/
theorem ringChoose_two_mul_nonneg {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) (k : ℕ) :
    0 ≤ Ring.choose r (2 * k) := by
  sorry

/-- The term-by-term comparison: for `1 < p ≤ q ≤ 2`,
`(p / q) ((p − 1) / (q − 1))^k C(q, 2k) ≤ C(p, 2k)`. -/
theorem ringChoose_two_mul_le {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2) (k : ℕ) :
    p / q * ((p - 1) / (q - 1)) ^ k * Ring.choose q (2 * k) ≤ Ring.choose p (2 * k) := by
  sorry

end BanachProbability
