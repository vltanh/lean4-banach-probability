module

public import BanachProbability.Hypercontractivity.Vector
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The Kahane–Khintchine inequality

For a seminorm `S` on a real vector space (in particular for every normed space), vectors
`x₁, …, x_n` and independent fair signs `ε_i`:

* the hypercontractive form: for `1 < p ≤ q < ∞`,
  `‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`
  (`kahaneKhintchine_hypercontractive`; C. Borell (1979), with the scalar two-point inequality of
  R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1), the case `c = 0` of
  `hypercontractive_affine`;
* the Kahane–Khintchine inequality: for all `p, q ∈ (1, ∞)`,
  `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}` with
  `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` (`kahaneKhintchine`; J.-P. Kahane, *Sur les sommes
  vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964); Hytönen–van Neerven–Veraar–Weis,
  *Analysis in Banach spaces II* (2017), Theorem 6.2.4), from the hypercontractive form when
  `p > q` and from the monotonicity of `L^p` norms when `p ≤ q`.

The proof is hypercontractivity (Bonami's two-point inequality, carried to seminormed spaces by
the triangle inequality and tensorised, the standard argument), not Kahane's original argument
through Lévy's inequality, which gives no growth rate of the constants.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### `L^p` norms on the cube -/

private theorem avg_eq_sum_mul {N : ℕ} (g : (Fin N → Bool) → ℝ) :
    avg g = ∑ ε, ((2 : ℝ) ^ N)⁻¹ * g ε := by
  rw [avg, div_eq_inv_mul, Finset.mul_sum]

private theorem sum_inv_two_pow {N : ℕ} : ∑ _ε : Fin N → Bool, ((2 : ℝ) ^ N)⁻¹ = 1 := by
  simp [Finset.card_univ, Fintype.card_bool]

private theorem lpNorm_nonneg' (S : Seminorm ℝ E) (p : ℝ) {N : ℕ} (X : (Fin N → Bool) → E) :
    0 ≤ SignCube.lpNorm S p X :=
  Real.rpow_nonneg (avg_nonneg fun _ => Real.rpow_nonneg (apply_nonneg S _) _) _

private theorem lpNorm_smul' (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) {N : ℕ} (c : ℝ)
    (X : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (c • X) = ‖c‖ * SignCube.lpNorm S p X := by
  have e : ∀ ε, S ((c • X) ε) ^ p = ‖c‖ ^ p * S (X ε) ^ p := fun ε => by
    rw [Pi.smul_apply, map_smul_eq_mul, Real.mul_rpow (norm_nonneg c) (apply_nonneg S _)]
  simp only [SignCube.lpNorm, e, avg_const_mul]
  rw [Real.mul_rpow (by positivity) (avg_nonneg fun _ => Real.rpow_nonneg (apply_nonneg S _) _),
    ← Real.rpow_mul (norm_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The power-mean inequality on the cube: `‖X‖_p ≤ ‖X‖_q` for `0 < p ≤ q` (Jensen's inequality
for `t ↦ t^{q/p}`). -/
private theorem lpNorm_mono' (S : Seminorm ℝ E) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) {N : ℕ}
    (X : (Fin N → Bool) → E) : SignCube.lpNorm S p X ≤ SignCube.lpNorm S q X := by
  have hq : 0 < q := hp.trans_le hpq
  have hf : ∀ ε, 0 ≤ S (X ε) := fun ε => apply_nonneg S _
  have hA : 0 ≤ avg (fun ε => S (X ε) ^ p) := avg_nonneg fun ε => Real.rpow_nonneg (hf ε) _
  have hJ : avg (fun ε => S (X ε) ^ p) ^ (q / p) ≤ avg (fun ε => S (X ε) ^ q) := by
    rw [avg_eq_sum_mul, avg_eq_sum_mul]
    calc (∑ ε, ((2 : ℝ) ^ N)⁻¹ * S (X ε) ^ p) ^ (q / p)
        ≤ ∑ ε, ((2 : ℝ) ^ N)⁻¹ * (S (X ε) ^ p) ^ (q / p) :=
          Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ _ _ (fun _ _ => by positivity)
            sum_inv_two_pow (fun ε _ => Real.rpow_nonneg (hf ε) _) ((one_le_div hp).2 hpq)
      _ = ∑ ε, ((2 : ℝ) ^ N)⁻¹ * S (X ε) ^ q := by
          refine Finset.sum_congr rfl fun ε _ => ?_
          rw [← Real.rpow_mul (hf ε), mul_div_cancel₀ _ hp.ne']
  calc SignCube.lpNorm S p X = (avg (fun ε => S (X ε) ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [SignCube.lpNorm, ← Real.rpow_mul hA]
        congr 1
        field_simp
    _ ≤ avg (fun ε => S (X ε) ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA _) hJ (div_nonneg zero_le_one hq.le)

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
    lpNorm_smul' S hq0, Real.norm_of_nonneg hρ.le] at h
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
    exact (lpNorm_mono' S (by linarith) hpq _).trans
      (le_mul_of_one_le_left (lpNorm_nonneg' S q _) (one_le_kahaneKhintchineConst p q))
  · -- `q ≤ p`: the hypercontractive form, and `κ_{p,q} ≥ √((p − 1) / (q − 1))`
    exact (kahaneKhintchine_hypercontractive S hq hqp x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (lpNorm_nonneg' S q _))

end BanachProbability
