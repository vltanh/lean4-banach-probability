module

public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Burkholder's function in Burkholder's notation

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy sur les processus stochastiques, Astérisque 157–158 (1988), (1.6), (1.10) and Remark 1.2;
D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*, Ann.
Probab. 12 (1984) (not obtained).

For `p > 1`, `p* = max (p, p / (p − 1))` and `x`, `y` in a normed group, Burkholder's function is
`u_p (x, y) = α_p (|y| − (p* − 1) |x|) (|x| + |y|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`
(`burkholderFun`, Burkholder's (1.6)), where, in Burkholder's notation, `x` is the position of the
dominating martingale and `y` that of the subordinate one. It is the function `burkholderU` of
`Martingale/Burkholder/Inequality.lean` with its arguments exchanged
(`burkholderFun_eq_burkholderU`).

## Main results

* `burkholderFun_ge`: `u_p ≥ v_p`, `v_p (x, y) = |y|^p − (p* − 1)^p |x|^p` (Burkholder's (1.10)).
* `burkholderFun_concaveOn_line`: in a real inner product space, if `|k| ≤ |h|`, then
  `t ↦ u_p (x + t h, y + t k)` is concave on `ℝ` (Burkholder's Remark 1.2, (1.17)).
* `burkholderFun_of_two_le`: for `p ≥ 2`, `p* = p` and
  `u_p (x, y) = p (1 − 1/p)^{p−1} (|y| − (p − 1) |x|) (|x| + |y|)^{p−1}`.

These are the two properties of `u_p` on which Burkholder's proof of Theorem 1.1 rests; both are
`burkholderU_ge` and `burkholderU_concaveOn_line` with the arguments exchanged, proved there by the
argument of the paper: (1.10) through (1.11) and the function `F`, and Remark 1.2, which the paper
states without proof, from its proof of (1.12) (the lines on which neither coordinate vanishes)
and the shift by an orthogonal vector of its proof of (1.8).
-/

@[expose] public section

open Set

namespace BanachProbability.Burkholder

variable {H : Type*} [NormedAddCommGroup H]

/-- **Burkholder's function** (Burkholder 1988, (1.6)):
`u_p (x, y) = α_p (|y| − (p* − 1) |x|) (|x| + |y|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`,
`p* = max (p, p / (p − 1))`; `x` is the position of the dominating martingale and `y` that of the
subordinate one. -/
noncomputable def burkholderFun (p : ℝ) (x y : H) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (‖y‖ - (max p (p / (p - 1)) - 1) * ‖x‖) *
    (‖x‖ + ‖y‖) ^ (p - 1)

/-- `u_p (x, y) = U (|y|, |x|)`, `U = burkholderU`. -/
theorem burkholderFun_eq_burkholderU (p : ℝ) (x y : H) :
    burkholderFun p x y = burkholderU p ‖y‖ ‖x‖ := by
  rw [burkholderFun, burkholderU, add_comm ‖x‖]

/-- **Majorization** (Burkholder 1988, (1.10)): `v_p ≤ u_p`, that is
`|y|^p − (p* − 1)^p |x|^p ≤ u_p (x, y)` (`burkholderU_ge`). -/
theorem burkholderFun_ge {p : ℝ} (hp : 1 < p) (x y : H) :
    ‖y‖ ^ p - (max p (p / (p - 1)) - 1) ^ p * ‖x‖ ^ p ≤ burkholderFun p x y := by
  rw [burkholderFun_eq_burkholderU]
  exact burkholderU_ge hp (norm_nonneg y) (norm_nonneg x)

/-- **Concavity along lines** (Burkholder 1988, Remark 1.2, (1.17)): in a real inner product
space, if `|k| ≤ |h|`, then `t ↦ u_p (x + t h, y + t k)` is concave on `ℝ`
(`burkholderU_concaveOn_line`). -/
theorem burkholderFun_concaveOn_line [InnerProductSpace ℝ H] {p : ℝ} (hp : 1 < p) (x y h k : H)
    (hk : ‖k‖ ≤ ‖h‖) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderFun p (x + t • h) (y + t • k) := by
  simp only [burkholderFun_eq_burkholderU]
  exact burkholderU_concaveOn_line hp y x k h hk

/-- For `p ≥ 2`, `p* = p`. -/
theorem max_div_sub_one_eq_self {p : ℝ} (hp : 2 ≤ p) : max p (p / (p - 1)) = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

/-- For `p ≥ 2`: `u_p (x, y) = p (1 − 1/p)^{p−1} (|y| − (p − 1) |x|) (|x| + |y|)^{p−1}`. -/
theorem burkholderFun_of_two_le {p : ℝ} (hp : 2 ≤ p) (x y : H) :
    burkholderFun p x y =
      p * (1 - 1 / p) ^ (p - 1) * (‖y‖ - (p - 1) * ‖x‖) * (‖x‖ + ‖y‖) ^ (p - 1) := by
  rw [burkholderFun, max_div_sub_one_eq_self hp]

end BanachProbability.Burkholder
