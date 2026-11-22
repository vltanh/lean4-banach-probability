module

public import BanachProbability.Hypercontractivity.TwoPoint
public import BanachProbability.SignCube.LpSeminorm

/-!
# Hypercontractivity of Rademacher sums in seminormed spaces

For a seminorm `S` on a real vector space `E` (no completeness, no quotient), `1 < p ≤ q` and
`ρ = √((p − 1) / (q − 1))`:

* the vector two-point inequality `‖a + ρ b ε‖_{L^q (S)} ≤ ‖a + b ε‖_{L^p (S)}`
  (`twoPoint_seminorm`): with `α = S (a + b)`, `β = S (a − b)`, the triangle inequality applied to
  `a ± ρ b = ((1 ± ρ)/2)(a + b) + ((1 ∓ ρ)/2)(a − b)` gives `S (a ± ρ b) ≤ A ± ρ B` with
  `A = (α + β)/2`, `B = (α − β)/2`, `|B| ≤ A`, and the scalar inequality (`twoPoint`) for
  `A + B ε` concludes;
* the affine hypercontractive inequality
  `‖c + ρ Σ_i ε_i x_i‖_{L^q (S)} ≤ ‖c + Σ_i ε_i x_i‖_{L^p (S)}` (`hypercontractive_affine`), by
  induction on the number of signs: split off the first sign, bound the inner `L^q` norm by the
  induction hypothesis with the constant `c + ρ η x₀`, and close the step with the vector
  two-point inequality in the space of functions of the remaining signs with the seminorm
  `L^p` (`SignCube.lpSeminorm`; Minkowski's inequality).

This is vector-valued hypercontractivity, due to C. Borell, *On the integrability of Banach space
valued Walsh polynomials*, Séminaire de Probabilités XIII (1979). The scalar two-point inequality
is that of R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1 (real-valued functions
only); its passage to seminormed spaces through the triangle inequality and the tensorisation on
affine Rademacher sums are the standard argument, with no noise operator.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The vector two-point inequality** for a seminorm `S`:
`((S (a + ρb)^q + S (a − ρb)^q) / 2)^{1/q} ≤ ((S (a + b)^p + S (a − b)^p) / 2)^{1/p}`. -/
theorem twoPoint_seminorm (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (a b : E) :
    ((S (a + √((p - 1) / (q - 1)) • b) ^ q + S (a - √((p - 1) / (q - 1)) • b) ^ q) / 2) ^ (1 / q) ≤
      ((S (a + b) ^ p + S (a - b) ^ p) / 2) ^ (1 / p) := by
  sorry

/-- **Affine hypercontractivity** of Rademacher sums in a seminormed space:
`‖c + ρ Σ_i ε_i x_i‖_{L^q} ≤ ‖c + Σ_i ε_i x_i‖_{L^p}`, `ρ = √((p − 1) / (q − 1))`. -/
theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) := by
  sorry

end BanachProbability
