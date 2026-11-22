module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Hadamard

/-!
# The three lines theorem for Schatten norms

* `complexSchattenNorm_le_of_verticalStrip`: if `Ψ` is a bounded continuous function on the strip
  `0 ≤ Re z ≤ 1` with values in the complex `n × n` matrices, analytic inside, with
  `‖Ψ (iy)‖_{S_{p₀}} ≤ M₀` and `‖Ψ (1 + iy)‖_{S_{p₁}} ≤ M₁`, then
  `‖Ψ (z)‖_{S_r} ≤ M₀^{1 − Re z} M₁^{Re z}`, `1/r = (1 − Re z)/p₀ + Re z/p₁`.
* `lpNorm_complexSchattenNorm_le_of_verticalStrip`: the same for functions on the sign cube and the
  norms of `L^p (Ω; S_p)`.

Sources: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p`*, Studia Math. 50 (1974), pp. 166–167: the first statement is quoted there
from I. C. Gohberg and M. G. Krein, *Introduction to the theory of linear nonselfadjoint operators*
(1965), §13; the second is Proposition 1.2, deduced from the first by block diagonal operators. The
boundedness of `Ψ`, which the statement needs, is not mentioned there. The first statement is proved
by the argument of D. Sutter, M. Berta and M. Tomamichel, *Multivariate trace inequalities*, Comm.
Math. Phys. 352 (2017), arXiv:1604.03023, Theorem 3.1 and Appendix D, pp. 15–16, with Hadamard's
three lines theorem in place of Hirschman's sharper form: the polar decomposition of `Ψ (θ)` gives
an analytic family of norming operators `X (z)`, and the three lines theorem is applied to
`tr (X (z) Ψ (z))`.
-/

@[expose] public section

open Complex Complex.HadamardThreeLines
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **The three lines theorem for Schatten norms** (Gohberg–Krein (1965), §13;
Sutter–Berta–Tomamichel (2017), Theorem 3.1). -/
theorem complexSchattenNorm_le_of_verticalStrip {p₀ p₁ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    {Ψ : ℂ → Matrix n n ℂ} (hΨ : ∀ i j, DiffContOnCl ℂ (fun z => Ψ z i j) (verticalStrip 0 1))
    (hb : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ∀ i j, ‖Ψ z i j‖ ≤ C) {M₀ M₁ : ℝ}
    (h₀ : ∀ y : ℝ, complexSchattenNorm (ENNReal.ofReal p₀) (Ψ (y * I)) ≤ M₀)
    (h₁ : ∀ y : ℝ, complexSchattenNorm (ENNReal.ofReal p₁) (Ψ (1 + y * I)) ≤ M₁) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) {r : ℝ} (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    complexSchattenNorm (ENNReal.ofReal r) (Ψ z) ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  sorry

/-- Tomczak-Jaegermann (1974), Proposition 1.2, p. 166: the three lines theorem for the norms of
`L^p (Ω; S_p)`, `Ω` the sign cube. (Every function on the cube is a combination of Walsh functions,
so the functions `Σ φ_n (z) w_n` of the source are arbitrary functions on the cube.) -/
theorem lpNorm_complexSchattenNorm_le_of_verticalStrip {p₀ p₁ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    {Φ : ℂ → (Fin N → Bool) → Matrix n n ℂ}
    (hΦ : ∀ ε i j, DiffContOnCl ℂ (fun z => Φ z ε i j) (verticalStrip 0 1))
    (hb : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ∀ ε i j, ‖Φ z ε i j‖ ≤ C) {M₀ M₁ : ℝ}
    (h₀ : ∀ y : ℝ, SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₀)) p₀ (Φ (y * I)) ≤ M₀)
    (h₁ : ∀ y : ℝ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₁)) p₁ (Φ (1 + y * I)) ≤ M₁) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) {r : ℝ} (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal r)) r (Φ z) ≤
      M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  sorry

end BanachProbability
