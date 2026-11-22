module

public import BanachProbability.Hypercontractivity.Binomial

/-!
# The two-point hypercontractive inequality

For `1 < p ≤ q < ∞`, `ρ = √((p − 1) / (q − 1))` and `a ≥ |b|`,
`‖a + ρ b ε‖_{L^q} ≤ ‖a + b ε‖_{L^p}` for one fair sign `ε`, that is
`(((a + ρb)^q + (a − ρb)^q) / 2)^{1/q} ≤ (((a + b)^p + (a − b)^p) / 2)^{1/p}` (`twoPoint`;
A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst. Fourier 20
(1970); R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1, "Two-Point Inequality", after
S. Janson). The proof follows O'Donnell:

* `1 < p ≤ q ≤ 2` (`twoPoint_of_le_two`): normalise to `a = 1`, `|b| < 1`, expand both sides in
  the even binomial series (`hasSum_two_point_binomial`), apply `(1 + t)^θ ≤ 1 + θ t` with
  `θ = p / q`, and compare term by term (`ringChoose_two_mul_le`); the boundary `|b| = a` by
  continuity;
* `2 ≤ p ≤ q` (`twoPoint_of_two_le`): by duality for nonnegative two-point functions
  (O'Donnell, Proposition 9.19), from the first case at `(q', p')`, since
  `(q' − 1) / (p' − 1) = (p − 1) / (q − 1)`;
* `p < 2 < q`: by the semigroup property `T_{ρ₁ ρ₂} = T_{ρ₂} T_{ρ₁}`, through `L²`.
-/

@[expose] public section

namespace BanachProbability

/-- The `L^r` norm `(((a + b)^r + (a − b)^r) / 2)^{1/r}` of the two-point function `a + b ε`
(for `a ≥ |b|`). -/
noncomputable def twoPointNorm (r a b : ℝ) : ℝ :=
  (((a + b) ^ r + (a - b) ^ r) / 2) ^ (1 / r)

/-- The two-point inequality for `1 < p ≤ q ≤ 2`. -/
theorem twoPoint_of_le_two {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2) {a b : ℝ}
    (hab : |b| ≤ a) : twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  sorry

/-- The two-point inequality for `2 ≤ p ≤ q`, by duality. -/
theorem twoPoint_of_two_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) {a b : ℝ} (hab : |b| ≤ a) :
    twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  sorry

/-- **The two-point hypercontractive inequality** (Bonami 1970; O'Donnell 2014, §10.1): for
`1 < p ≤ q` and `a ≥ |b|`, `‖a + ρ b ε‖_q ≤ ‖a + b ε‖_p`, `ρ = √((p − 1) / (q − 1))`. -/
theorem twoPoint {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {a b : ℝ} (hab : |b| ≤ a) :
    twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  sorry

end BanachProbability
