module

public import BanachProbability.Schatten.Holder
public import BanachProbability.SignCube.LpSeminorm

/-!
# The lower noncommutative Khintchine inequality

For real `n × n` matrices `x_1, …, x_k` and `q ≥ 2`, with `S (ε) = Σ_i ε_i x_i`,
`‖(Σ_i x_iᵀ x_i)^{1/2}‖_{S_q} ≤ (E ‖S‖_{S_q}^q)^{1/q}` and the same with `x_i x_iᵀ`, with
constant `1` and no normality assumption (`ncKhintchine_lower_col`, `ncKhintchine_lower_row`;
F. Lust-Piquard, *Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303
(1986); G. Pisier and Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach
Spaces 2 (2003), Theorem 6.1).

The proof is the standard convexity argument: `‖S‖_q^q = ‖Sᵀ S‖_{q/2}^{q/2}`; Jensen's inequality
for `t ↦ t^{q/2}`, then the convexity of the `S_{q/2}` norm on positive semidefinite matrices
(`schattenNorm_sum_le_of_posSemidef`), give `E ‖Sᵀ S‖_{q/2}^{q/2} ≥ ‖E Sᵀ S‖_{q/2}^{q/2}`; and
`E Sᵀ S = Σ_i x_iᵀ x_i` by the orthonormality of the signs.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lower noncommutative Khintchine inequality** (column square function):
`‖Σ_i x_iᵀ x_i‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}`, `q ≥ 2`. -/
theorem ncKhintchine_lower_col {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

/-- **Lower noncommutative Khintchine inequality** (row square function):
`‖Σ_i x_i x_iᵀ‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}`, `q ≥ 2`. -/
theorem ncKhintchine_lower_row {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

end BanachProbability
