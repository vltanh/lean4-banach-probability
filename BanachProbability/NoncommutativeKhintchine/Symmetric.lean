module

public import BanachProbability.Schatten.Holder
public import BanachProbability.SignCube.LpSeminorm

/-!
# The noncommutative Khintchine inequality for symmetric matrices

For real symmetric `n × n` matrices `A_1, …, A_k`, `q ≥ 2` and `Y (ε) = Σ_i ε_i A_i`,
`(E ‖Y‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖(Σ_i A_i²)^{1/2}‖_{S_q}`, where
`‖(Σ_i A_i²)^{1/2}‖_{S_q} = ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}` (`ncKhintchine_symmetric_upper`), with a
constant independent of the dimension.

The proof is the method of exchangeable pairs of L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell
and J. A. Tropp, *Matrix concentration inequalities via the method of exchangeable pairs*, Ann.
Probab. 42 (2014), §7 (matrix Burkholder–Davis–Gundy and Khintchine inequalities, Corollary 7.3):

* `E ‖Y‖_q^q = E tr (Y h (Y)) = Σ_i E [ε_i tr (A_i h (Y))]` with `h (t) = t |t|^{q−2}`; pairing
  `ε` with its flip in the `i`-th sign, `Y − Y^{(i)} = 2 ε_i A_i`, and the mean-value trace
  inequality (`trace_mean_value`) with flip invariance give
  `E ‖Y‖_q^q ≤ 2 (q − 1) E tr (V g (Y))`, `V = Σ_i A_i²`, `g (t) = |t|^{q−2}`
  (`avg_schattenNorm_rpow_le`);
* the trace Hölder inequality with `r = q / 2` (`trace_mul_le_of_posSemidef`) and Jensen's
  inequality for `t ↦ t^{1−2/q}` give `E ‖Y‖_q^q ≤ 2 (q − 1) ‖V‖_{q/2} (E ‖Y‖_q^q)^{1−2/q}`.

The constant `√(2 (q − 1))` is that of the cruder mean-value inequality valid for every `q ≥ 2`;
Mackey et al. obtain `√(q − 1)` for `q = 2` and `q ≥ 3` (Corollary 7.3), and `√(2 (q − 1))` for
`2 < q < 3` (Remark 7.2).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exchangeable-pair estimate: `E ‖Y‖_{S_q}^q ≤ 2 (q − 1) E tr (V |Y|^{q−2})`,
`Y = Σ_i ε_i A_i`, `V = Σ_i A_i²`. -/
theorem avg_schattenNorm_rpow_le {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (avg fun ε => schattenNorm (ENNReal.ofReal q) (∑ i, coin (ε i) • A i) ^ q) ≤
      2 * (q - 1) * avg fun ε =>
        ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (∑ i, coin (ε i) • A i)).trace := by
  sorry

/-- **Noncommutative Khintchine inequality, symmetric case, upper bound** (Mackey et al. 2014,
§7): `(E ‖Σ_i ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}`, `q ≥ 2`. -/
theorem ncKhintchine_symmetric_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    lpNorm (schattenNorm (ENNReal.ofReal q)) q (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(2 * (q - 1)) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  sorry

end BanachProbability
