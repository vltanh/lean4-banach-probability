module

public import BanachProbability.Noncommutative.MatrixCube
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Distribution functions on the matrix cube

For a matrix-valued function `x` on the sign cube, the distribution function
`λ_s (x) = τ (1_{(s, ∞)} (|x|)) = E #{i : s_i (x (ε)) > s}` (`distribution`). It is subadditive,
`λ_{s+t} (x + y) ≤ λ_s (x) + λ_t (y)` (from `countAbove_add_add_le`), satisfies Chebyshev's
inequality `s^r λ_s (x) ≤ ‖x‖_{L^r}^r`, and gives the layer-cake formula
`‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`. The spectral truncations of a symmetric matrix at level
`s`, `A 1_{(s, ∞)} (|A|)` and `A 1_{[0, s]} (|A|)` (`truncAbove`, `truncBelow`), split it into its
large and small eigenvalues.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The distribution function `λ_s (x) = E #{i : s_i (x (ε)) > s}`. -/
noncomputable def distribution (s : ℝ) (x : (Fin N → Bool) → Matrix n n ℝ) : ℝ :=
  avg fun ε => (countAbove s (x ε) : ℝ)

theorem distribution_add_add_le (s t : ℝ) (x y : (Fin N → Bool) → Matrix n n ℝ) :
    distribution (s + t) (x + y) ≤ distribution s x + distribution t y := by
  sorry

theorem distribution_mul_rpow_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    distribution s x * s ^ r ≤ avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
  sorry

/-- The layer-cake formula `‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`. -/
theorem avg_schattenNorm_rpow_eq_integral {r : ℝ} (hr : 0 < r)
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    (avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r) =
      ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * distribution s x := by
  sorry

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
  sorry

theorem isHermitian_truncAbove (s : ℝ) (A : Matrix n n ℝ) : (truncAbove s A).IsHermitian := by
  sorry

theorem isHermitian_truncBelow (s : ℝ) (A : Matrix n n ℝ) : (truncBelow s A).IsHermitian := by
  sorry

open scoped Classical in
theorem schattenNorm_truncAbove_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncAbove s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => s < |hA.eigenvalues i|), |hA.eigenvalues i| ^ r := by
  sorry

open scoped Classical in
theorem schattenNorm_truncBelow_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncBelow s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => |hA.eigenvalues i| ≤ s), |hA.eigenvalues i| ^ r := by
  sorry

end BanachProbability
