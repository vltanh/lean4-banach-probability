module

public import BanachProbability.Hypercontractivity.Vector

/-!
# The Kahane–Khintchine inequality

For a seminorm `S` on a real vector space (in particular for every normed space), vectors
`x₁, …, x_n` and independent fair signs `ε_i`:

* the hypercontractive form: for `1 < p ≤ q < ∞`,
  `‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`
  (`kahaneKhintchine_hypercontractive`; C. Borell (1979), Theorem 1.1 for `d = 1`), the case
  `c = 0` of `hypercontractive_affine`;
* the Kahane–Khintchine inequality: for all `p, q ∈ (1, ∞)`,
  `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}` with
  `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` (`kahaneKhintchine`; J.-P. Kahane, *Sur les sommes
  vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964); Hytönen–van Neerven–Veraar–Weis,
  *Analysis in Banach spaces II* (2017), Theorem 6.2.4), from the hypercontractive form when
  `p > q` and from the monotonicity of `L^p` norms (`SignCube.lpNorm_mono_exponent`) when
  `p ≤ q`.

The proof is Borell's (§2 of his paper; `Hypercontractivity/Vector.lean`): the elementary
two-point inequality, tensorised by the Segal lemma and carried to seminormed spaces by the
positivity of the kernel, applied to the Walsh polynomials of degree `1`; not Kahane's original
argument through Lévy's inequality, which gives no growth rate of the constants.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The Kahane–Khintchine inequalities -/

/-- **The hypercontractive Kahane–Khintchine inequality**: for `1 < p ≤ q`,
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`. -/
theorem kahaneKhintchine_hypercontractive (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p)
    (hpq : p ≤ q) {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  have hq0 : 0 < q := by linarith
  have hρ : 0 < √((p - 1) / (q - 1)) := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  -- the case `c = 0` of the affine inequality: `ρ ‖S‖_q ≤ ‖S‖_p`
  have h := hypercontractive_affine S hp hpq 0 x
  simp only [zero_add] at h
  rw [show (fun ε : Fin n → Bool => √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) =
      √((p - 1) / (q - 1)) • (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) from rfl,
    lpNorm_smul S hq0, Real.norm_of_nonneg hρ.le] at h
  rw [show √((q - 1) / (p - 1)) = (√((p - 1) / (q - 1)))⁻¹ by rw [← Real.sqrt_inv, inv_div],
    ← div_eq_inv_mul, le_div_iff₀ hρ, mul_comm]
  exact h

/-- The Kahane–Khintchine constant `κ_{p,q} = max (1, √((p − 1) / (q − 1)))`. -/
noncomputable def kahaneKhintchineConst (p q : ℝ) : ℝ :=
  max 1 √((p - 1) / (q - 1))

theorem one_le_kahaneKhintchineConst (p q : ℝ) : 1 ≤ kahaneKhintchineConst p q :=
  le_max_left _ _

theorem kahaneKhintchineConst_pos (p q : ℝ) : 0 < kahaneKhintchineConst p q :=
  zero_lt_one.trans_le (one_le_kahaneKhintchineConst p q)

/-- **The Kahane–Khintchine inequality** (Kahane 1964; HNVW II, Theorem 6.2.4): for
`p, q ∈ (1, ∞)`, `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}`. -/
theorem kahaneKhintchine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n : ℕ}
    (x : Fin n → E) :
    SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      kahaneKhintchineConst p q *
        SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  rcases le_total p q with hpq | hqp
  · -- `p ≤ q`: monotonicity of `L^p` norms, and `κ_{p,q} ≥ 1`
    exact (lpNorm_mono_exponent (apply_nonneg S) (by linarith) hpq _).trans
      (le_mul_of_one_le_left (lpNorm_nonneg (apply_nonneg S) q _)
        (one_le_kahaneKhintchineConst p q))
  · -- `q ≤ p`: the hypercontractive form, and `κ_{p,q} ≥ √((p − 1) / (q − 1))`
    exact (kahaneKhintchine_hypercontractive S hq hqp x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (lpNorm_nonneg (apply_nonneg S) q _))

end BanachProbability
