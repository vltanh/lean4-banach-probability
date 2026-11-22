module

public import BanachProbability.Hypercontractivity.Vector

/-!
# The Kahane–Khintchine inequality

For a seminorm `S` on a real vector space (in particular for every normed space), vectors
`x₁, …, x_n` and independent fair signs `ε_i`:

* the hypercontractive form: for `1 < p ≤ q < ∞`,
  `‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`
  (`kahaneKhintchine_hypercontractive`; C. Borell (1979); R. O'Donnell, *Analysis of Boolean
  Functions* (2014), §10.1), the case `c = 0` of `hypercontractive_affine`;
* the Kahane–Khintchine inequality: for all `p, q ∈ (1, ∞)`,
  `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}` with
  `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` (`kahaneKhintchine`; J.-P. Kahane, *Sur les sommes
  vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964); Hytönen–van Neerven–Veraar–Weis,
  *Analysis in Banach spaces II* (2017), Theorem 6.2.4), from the hypercontractive form when
  `p > q` and from the monotonicity of `L^p` norms when `p ≤ q`.

The proof is hypercontractivity (Bonami's two-point inequality, carried to seminormed spaces by
the triangle inequality and tensorised), not Kahane's original argument through Lévy's
inequality, which gives no growth rate of the constants.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The hypercontractive Kahane–Khintchine inequality**: for `1 < p ≤ q`,
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`. -/
theorem kahaneKhintchine_hypercontractive (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p)
    (hpq : p ≤ q) {n : ℕ} (x : Fin n → E) :
    lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) * lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

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
    lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      kahaneKhintchineConst p q * lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

end BanachProbability
