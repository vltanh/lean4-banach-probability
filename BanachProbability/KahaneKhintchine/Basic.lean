module

public import BanachProbability.Hypercontractivity.HeatSemigroup

/-!
# The Kahane–Khintchine inequality

For a seminorm `S` on a real vector space (in particular for every normed space), vectors
`x₁, …, x_n` and independent fair signs `ε_i`, for all `0 < p, q < ∞`,
`‖Σ ε_i x_i‖_{L^q} ≤ κ_{q,p} ‖Σ ε_i x_i‖_{L^p}` with a constant that depends only on `p` and `q`
(J.-P. Kahane, *Sur les sommes vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964);
Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces II* (2017), Theorem 6.2.4,
p. 21–22, the real case):

* for `1 < p ≤ q < ∞`, `κ_{q,p} ≤ √((q − 1) / (p − 1))` (`kahaneKhintchine_hypercontractive`);
* for all `p, q ∈ (1, ∞)`, with `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` in
  `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}` (`kahaneKhintchine`);
* for all `p, q ∈ (0, ∞)`, some constant (`exists_kahaneKhintchine`).

The proof is HNVW's, p. 22. For `1 < p ≤ q` it is hypercontractivity (Theorem 6.2.2,
`heatSemigroup_lpNorm_le`): the discrete heat semigroup satisfies `T (t) f = e^{−t} f` for the
Rademacher sum `f = Σ ε_i x_i`, and one takes `e^{−t} = √((p − 1) / (q − 1))`. For
`0 < p ≤ 1 < q`, take `r > q`, `1/q = θ/p + (1 − θ)/r`; then
`‖f‖_q ≤ ‖f‖_p^θ ‖f‖_r^{1−θ} ≤ ‖f‖_p^θ (κ_{r,q} ‖f‖_q)^{1−θ}`, so
`κ_{q,p} ≤ κ_{r,q}^{(1−θ)/θ}`. For `0 < p ≤ q ≤ 1` (the book: `q < 1`) take `r > 1`:
`‖f‖_q ≤ ‖f‖_r ≤ κ_{r,p} ‖f‖_p`. For `q ≤ p` the norms are monotone
(`SignCube.lpNorm_mono_exponent`). The complex case of the theorem (complex Rademacher variables) is
not treated.

The hypercontractive bound is also C. Borell's (*On the integrability of Banach space valued Walsh
polynomials*, Séminaire de Probabilités XIII (1979), Theorem 1.1 for `d = 1`); his proof, by a
tensorisation on the scalar level, is in `Hypercontractivity/Vector.lean`
(`hypercontractive_affine`).
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Exponents greater than one -/

/-- **The Kahane–Khintchine inequality, `1 < p ≤ q`** (HNVW II, Theorem 6.2.4, p. 21–22,
`κ_{q,p} ≤ √((q − 1) / (p − 1))`): `‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`. By
hypercontractivity (Theorem 6.2.2), `T (t) f = e^{−t} f` for `f = Σ ε_i x_i` and
`e^{−t} = √((p − 1) / (q − 1))`. -/
theorem kahaneKhintchine_hypercontractive (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p)
    (hpq : p ≤ q) {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  have hq0 : 0 < q := by linarith
  have hρ : 0 < √((p - 1) / (q - 1)) := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  -- `e^{−t} = √((p − 1) / (q − 1))`
  set t : ℝ := -Real.log √((p - 1) / (q - 1)) with ht_def
  have ht : Real.exp (-t) = √((p - 1) / (q - 1)) := by rw [ht_def, neg_neg, Real.exp_log hρ]
  set f : (Fin n → Bool) → E := fun ε => ∑ i, coin (ε i) • x i with hf
  -- `T (t) f = e^{−t} f`
  have hT : heatSemigroup t f = Real.exp (-t) • f := by
    have h := heatSemigroup_affine t 0 x
    simp only [zero_add] at h
    exact h
  have h := heatSemigroup_lpNorm_le S hp hpq ht.le f
  rw [hT, ht, lpNorm_smul S hq0, Real.norm_of_nonneg hρ.le] at h
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

/-! ### All exponents -/

omit [AddCommGroup E] [Module ℝ E] in
/-- Interpolation of `L^p` norms (Hölder's inequality): `‖f‖_q ≤ ‖f‖_p^θ ‖f‖_r^{1−θ}` for
`1/q = θ/p + (1 − θ)/r`, `0 < θ < 1`. -/
private theorem kkh_interpolation {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {p q r θ : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθ : 1 / q = θ / p + (1 - θ) / r)
    {n : ℕ} (f : (Fin n → Bool) → E) :
    SignCube.lpNorm nrm q f ≤ SignCube.lpNorm nrm p f ^ θ * SignCube.lpNorm nrm r f ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  -- the conjugate exponents `s = p / (q θ)`, `s' = r / (q (1 − θ))`
  have hqq : q * (θ / p + (1 - θ) / r) = 1 := by rw [← hθ, mul_one_div_cancel hq.ne']
  have hs : (p / (q * θ)).HolderConjugate (r / (q * (1 - θ))) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ (by positivity), one_mul]
      have h2 : 0 < (1 - θ) / r := by positivity
      have h3 : q * (θ / p) < 1 := by nlinarith
      rw [mul_div_assoc', div_lt_one hp] at h3
      exact h3
    · have e : q * θ / p + q * (1 - θ) / r = q * (θ / p + (1 - θ) / r) := by ring
      rw [inv_div, inv_div, e, hqq]
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hp' : 0 ≤ avg fun ε => nrm (f ε) ^ p := avg_nonneg fun ε => Real.rpow_nonneg (hnrm _) p
  have hr' : 0 ≤ avg fun ε => nrm (f ε) ^ r := avg_nonneg fun ε => Real.rpow_nonneg (hnrm _) r
  have hq' : 0 ≤ avg fun ε => nrm (f ε) ^ q := avg_nonneg fun ε => Real.rpow_nonneg (hnrm _) q
  -- Hölder's inequality for the averages
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin n → Bool))
    (f := fun ε => nrm (f ε) ^ (q * θ)) (g := fun ε => nrm (f ε) ^ (q * (1 - θ))) hs
    (fun ε _ => Real.rpow_nonneg (hnrm _) _) (fun ε _ => Real.rpow_nonneg (hnrm _) _)
  have e1 : ∀ ε, nrm (f ε) ^ (q * θ) * nrm (f ε) ^ (q * (1 - θ)) = nrm (f ε) ^ q := fun ε => by
    rw [← Real.rpow_add_of_nonneg (hnrm _) (by positivity) (by positivity)]
    congr 1
    ring
  have e2 : ∀ ε, (nrm (f ε) ^ (q * θ)) ^ (p / (q * θ)) = nrm (f ε) ^ p := fun ε => by
    rw [← Real.rpow_mul (hnrm _), mul_div_cancel₀ _ (by positivity)]
  have e3 : ∀ ε, (nrm (f ε) ^ (q * (1 - θ))) ^ (r / (q * (1 - θ))) = nrm (f ε) ^ r := fun ε => by
    rw [← Real.rpow_mul (hnrm _), mul_div_cancel₀ _ (by positivity)]
  simp only [e1, e2, e3] at hH
  have hsum : ∀ s : ℝ, ∑ ε, nrm (f ε) ^ s = 2 ^ n * avg fun ε => nrm (f ε) ^ s := fun s => by
    rw [avg, mul_div_cancel₀ _ hN.ne']
  rw [hsum, hsum, hsum, Real.mul_rpow hN.le hp', Real.mul_rpow hN.le hr', mul_mul_mul_comm,
    ← Real.rpow_add hN, hs.one_div_add_one_div, div_one, Real.rpow_one] at hH
  have hH' := le_of_mul_le_mul_left hH hN
  -- take the root of order `q`
  have e4 : 1 / (p / (q * θ)) = θ / p * q := by field_simp
  have e5 : 1 / (r / (q * (1 - θ))) = (1 - θ) / r * q := by field_simp
  rw [e4, e5] at hH'
  have hroot := Real.rpow_le_rpow hq' hH' (by positivity : 0 ≤ 1 / q)
  rw [Real.mul_rpow (Real.rpow_nonneg hp' _) (Real.rpow_nonneg hr' _), ← Real.rpow_mul hp',
    ← Real.rpow_mul hr', mul_assoc, mul_one_div_cancel hq.ne', mul_one, mul_assoc,
    mul_one_div_cancel hq.ne', mul_one] at hroot
  simp only [SignCube.lpNorm]
  rw [← Real.rpow_mul hp', ← Real.rpow_mul hr', one_div_mul_eq_div, one_div_mul_eq_div]
  exact hroot

/-- The case `0 < p ≤ 1 < q` of HNVW II, Theorem 6.2.4 (p. 22), with `r = 2 q`: by interpolation
between `L^p` and `L^r` and the case `1 < q < r`. -/
private theorem kkh_of_le_one (S : Seminorm ℝ E) {p q : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hq : 1 < q)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((2 * q - 1) / (q - 1)) ^ (2 * (q - p) / p) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  set f : (Fin n → Bool) → E := fun ε => ∑ i, coin (ε i) • x i
  have hS : ∀ z, 0 ≤ S z := apply_nonneg S
  set K : ℝ := √((2 * q - 1) / (q - 1))
  have hK : 0 < K := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  set A := SignCube.lpNorm S q f
  set B := SignCube.lpNorm S p f
  have hA : 0 ≤ A := lpNorm_nonneg hS q f
  have hB : 0 ≤ B := lpNorm_nonneg hS p f
  -- `θ = p / (2 q − p)`, `1 / q = θ / p + (1 − θ) / (2 q)`
  have h2qp : 0 < 2 * q - p := by linarith
  set θ : ℝ := p / (2 * q - p) with hθ_def
  have hθ0 : 0 < θ := div_pos hp h2qp
  have hθ1 : θ < 1 := (div_lt_one h2qp).2 (by linarith)
  have h1θ : 1 - θ = 2 * (q - p) / (2 * q - p) := by
    rw [hθ_def, eq_div_iff h2qp.ne', sub_mul, div_mul_cancel₀ _ h2qp.ne']
    ring
  have hθ : 1 / q = θ / p + (1 - θ) / (2 * q) := by
    have e1 : θ / p = (2 * q - p)⁻¹ := by rw [hθ_def, div_div_cancel_left' hp.ne']
    have e2 : 2 * (q - p) / (2 * q - p) / (2 * q) = (q - p) * (2 * q - p)⁻¹ * q⁻¹ := by
      rw [div_div, mul_left_comm, mul_div_mul_left _ _ two_ne_zero, div_eq_mul_inv, mul_inv,
        mul_assoc]
    rw [h1θ, e1, e2, one_div]
    linear_combination (-q⁻¹) * mul_inv_cancel₀ h2qp.ne' +
      (2 * q - p)⁻¹ * mul_inv_cancel₀ (by linarith : q ≠ 0)
  have h1 := kkh_interpolation hS hp (by linarith) (by linarith : 0 < 2 * q) hθ0 hθ1 hθ f
  have h2 := kahaneKhintchine_hypercontractive S hq (by linarith : q ≤ 2 * q) x
  rcases hA.eq_or_lt with hA0 | hA0
  · rw [← hA0]
    exact mul_nonneg (Real.rpow_nonneg hK.le _) hB
  -- `A ≤ B^θ (K A)^{1−θ}`, so `A^θ ≤ K^{1−θ} B^θ`
  have h3 : A ≤ B ^ θ * (K * A) ^ (1 - θ) := h1.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (lpNorm_nonneg hS _ f) h2 (by linarith)) (Real.rpow_nonneg hB θ))
  rw [Real.mul_rpow hK.le hA] at h3
  have h4 : A ^ θ * A ^ (1 - θ) ≤ (K ^ (1 - θ) * B ^ θ) * A ^ (1 - θ) := by
    rw [← Real.rpow_add hA0, add_sub_cancel, Real.rpow_one]
    linarith
  have h5 : A ^ θ ≤ K ^ (1 - θ) * B ^ θ :=
    le_of_mul_le_mul_right h4 (Real.rpow_pos_of_pos hA0 _)
  have h6 : (K ^ (1 - θ) * B ^ θ) = (K ^ (2 * (q - p) / p) * B) ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hK.le _) hB, ← Real.rpow_mul hK.le]
    congr 2
    have h3 : (2 * q - p) ≠ 0 := h2qp.ne'
    rw [h1θ, hθ_def]
    field_simp
  rw [h6] at h5
  exact (Real.rpow_le_rpow_iff hA (mul_nonneg (Real.rpow_nonneg hK.le _) hB) hθ0).1 h5

/-- **The Kahane–Khintchine inequality** for all exponents (Kahane 1964; HNVW II, Theorem 6.2.4,
p. 21–22, real case): for `p, q ∈ (0, ∞)` there is a constant `κ`, depending only on `p` and `q`,
such that `‖Σ ε_i x_i‖_{L^q} ≤ κ ‖Σ ε_i x_i‖_{L^p}`. -/
theorem exists_kahaneKhintchine {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Seminorm ℝ E) {n : ℕ}
      (x : Fin n → E),
      SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
        κ * SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  rcases le_or_gt q p with hqp | hqp
  · -- `q ≤ p`: monotonicity
    refine ⟨1, one_pos, fun S n x => ?_⟩
    rw [one_mul]
    exact lpNorm_mono_exponent (apply_nonneg S) hq hqp _
  rcases lt_or_ge 1 p with hp1 | hp1
  · -- `1 < p ≤ q`
    exact ⟨√((q - 1) / (p - 1)), Real.sqrt_pos.2 (div_pos (by linarith) (by linarith)),
      fun S n x => kahaneKhintchine_hypercontractive S hp1 hqp.le x⟩
  rcases lt_or_ge 1 q with hq1 | hq1
  · -- `p ≤ 1 < q`
    exact ⟨_, Real.rpow_pos_of_pos (Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))) _,
      fun S n x => kkh_of_le_one S hp hp1 hq1 x⟩
  · -- `p ≤ q ≤ 1`: `‖f‖_q ≤ ‖f‖_2 ≤ κ_{2,p} ‖f‖_p`
    refine ⟨√((2 * 2 - 1) / (2 - 1)) ^ (2 * (2 - p) / p), Real.rpow_pos_of_pos
      (Real.sqrt_pos.2 (by norm_num)) _, fun S n x => ?_⟩
    exact (lpNorm_mono_exponent (apply_nonneg S) hq (by linarith : q ≤ 2) _).trans
      (kkh_of_le_one S hp hp1 one_lt_two x)

end BanachProbability
