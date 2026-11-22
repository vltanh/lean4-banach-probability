module

public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Basic

/-!
# Kahane's contraction principle

For vectors `x_k` in a normed space, independent fair signs `ε_k`, `1 ≤ p < ∞` and scalars
`|c_k| ≤ 1`, `‖Σ ε_k c_k x_k‖_{L^p} ≤ ‖Σ ε_k x_k‖_{L^p}` for real `c_k` (`lpNorm_sum_coin_smul_le`),
and the same with the factor `2` for complex `c_k` (`lpNorm_sum_coin_smul_le_two_mul`, by real and
imaginary parts). Source: Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016),
Proposition 3.2.10, and *II* (2017), Theorem 6.1.13, p. 9; the sharp factor for complex scalars and
real signs, `π/2`, is not needed here.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- **Kahane's contraction principle**, real scalars. -/
theorem lpNorm_sum_coin_smul_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℝ}
    (hc : ∀ k, |c k| ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  sorry

/-- **Kahane's contraction principle**, complex scalars and real signs, with the factor `2`. -/
theorem lpNorm_sum_coin_smul_le_two_mul [NormedSpace ℂ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℂ}
    (hc : ∀ k, ‖c k‖ ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      2 * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  sorry

end BanachProbability
