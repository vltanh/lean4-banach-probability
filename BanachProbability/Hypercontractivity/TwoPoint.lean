module

public import BanachProbability.Hypercontractivity.Binomial

/-!
# The two-point hypercontractive inequality

For `1 < p ≤ q < ∞`, `ρ = √((p − 1) / (q − 1))` and `a ≥ |b|`,
`‖a + ρ b ε‖_{L^q} ≤ ‖a + b ε‖_{L^p}` for one fair sign `ε`, that is
`(((a + ρb)^q + (a − ρb)^q) / 2)^{1/q} ≤ (((a + b)^p + (a − b)^p) / 2)^{1/p}` (`twoPoint`): the
case `a ≥ |b|` (nonnegative two-point functions, all that the vector-valued extension needs) of
the two-point inequality of A. Bonami, *Étude des coefficients de Fourier des fonctions de
`L^p (G)`*, Ann. Inst. Fourier 20 (1970), and R. O'Donnell, *Analysis of Boolean Functions*
(2014), §10.1, "Two-Point Inequality", after S. Janson, which holds for all real `a`, `b`. The
proof follows O'Donnell:

* `1 < p ≤ q ≤ 2` (`twoPoint_of_le_two`): normalise to `a = 1`, `|b| < 1`, expand both sides in
  the even binomial series (`hasSum_two_point_binomial`), apply `(1 + t)^θ ≤ 1 + θ t` with
  `θ = p / q`, and compare term by term (`ringChoose_two_mul_le`); the boundary `|b| = a` by
  continuity;
* `2 ≤ p ≤ q` (`twoPoint_of_two_le`): by duality for nonnegative two-point functions
  (O'Donnell, Proposition 9.19), from the first case at `(q', p')`, since
  `(q' − 1) / (p' − 1) = (p − 1) / (q − 1)`;
* `p < 2 < q`: by the semigroup property `T_{ρ₁ ρ₂} = T_{ρ₂} T_{ρ₁}`, through `L²`, with
  `ρ₁ = √(p − 1)` (the first case at `(p, 2)`) and `ρ₂ = 1 / √(q − 1)` (the second case at
  `(2, q)`).
-/

open Filter Topology

@[expose] public section

namespace BanachProbability

/-- The `L^r` norm `(((a + b)^r + (a − b)^r) / 2)^{1/r}` of the two-point function `a + b ε`
(for `a ≥ |b|`). -/
noncomputable def twoPointNorm (r a b : ℝ) : ℝ :=
  (((a + b) ^ r + (a - b) ^ r) / 2) ^ (1 / r)

/-- The two-point norm is nonnegative. -/
private theorem twoPointNorm_nonneg (r : ℝ) {a b : ℝ} (hab : |b| ≤ a) : 0 ≤ twoPointNorm r a b :=
  Real.rpow_nonneg (div_nonneg (add_nonneg
    (Real.rpow_nonneg (by linarith [neg_abs_le b]) _)
    (Real.rpow_nonneg (by linarith [le_abs_self b]) _)) zero_le_two) _

/-- Homogeneity: `‖a + b ε‖_r = a ‖1 + (b / a) ε‖_r` for `a > 0`. -/
private theorem twoPointNorm_eq_mul {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hab : |b| ≤ a) :
    twoPointNorm r a b = a * twoPointNorm r 1 (b / a) := by
  have hb : |b / a| ≤ 1 := by rw [abs_div, abs_of_pos ha]; exact (div_le_one ha).2 hab
  have h1 : 0 ≤ 1 + b / a := by linarith [neg_abs_le (b / a)]
  have h2 : 0 ≤ 1 - b / a := by linarith [le_abs_self (b / a)]
  have e1 : a + b = a * (1 + b / a) := by field_simp
  have e2 : a - b = a * (1 - b / a) := by field_simp
  unfold twoPointNorm
  rw [e1, e2, Real.mul_rpow ha.le h1, Real.mul_rpow ha.le h2, ← mul_add, mul_div_assoc,
    Real.mul_rpow (Real.rpow_nonneg ha.le _)
      (div_nonneg (add_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) zero_le_two),
    ← Real.rpow_mul ha.le, mul_one_div_cancel hr.ne', Real.rpow_one]

/-- `ρ = √((p − 1) / (q − 1)) ∈ [0, 1]` for `1 < p ≤ q`. -/
private theorem sqrt_div_le_one {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    √((p - 1) / (q - 1)) ≤ 1 :=
  Real.sqrt_le_one.2 ((div_le_one (by linarith)).2 (by linarith))

/-- The strict case `|ε| < 1` of the normalised inequality for `1 < p ≤ q ≤ 2`
(O'Donnell, (10.4)). -/
private theorem twoPointNorm_one_le_of_abs_lt {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2)
    {ε : ℝ} (hε : |ε| < 1) :
    twoPointNorm q 1 (√((p - 1) / (q - 1)) * ε) ≤ twoPointNorm p 1 ε := by
  set ρ := √((p - 1) / (q - 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := sqrt_div_le_one hp hpq
  have hρ2 : ρ ^ 2 = (p - 1) / (q - 1) := Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have hρε : |ρ * ε| < 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg ε]
  set A := ((1 + ρ * ε) ^ q + (1 - ρ * ε) ^ q) / 2 with hA_def
  set B := ((1 + ε) ^ p + (1 - ε) ^ p) / 2 with hB_def
  -- the expansions `A = 1 + Σ_{k ≥ 1} C(q, 2k) (ρ ε)^{2k}`, `B = 1 + Σ_{k ≥ 1} C(p, 2k) ε^{2k}`
  have hA := (hasSum_nat_add_iff' 1).2 (hasSum_two_point_binomial q hρε)
  have hB := (hasSum_nat_add_iff' 1).2 (hasSum_two_point_binomial p hε)
  simp only [Finset.sum_range_one, mul_zero, pow_zero, Ring.choose_zero_right, mul_one]
    at hA hB
  -- `t = A − 1 ≥ 0`
  have ht : 0 ≤ A - 1 := hA.nonneg fun k =>
    mul_nonneg (ringChoose_two_mul_nonneg (by linarith) hq _) ((even_two_mul _).pow_nonneg _)
  -- the term-by-term comparison
  have hθt : p / q * (A - 1) ≤ B - 1 := by
    refine hasSum_le (fun k => ?_) (hA.mul_left (p / q)) hB
    rw [mul_pow, pow_mul ρ, hρ2, ← mul_assoc, ← mul_assoc, mul_right_comm (p / q)]
    exact mul_le_mul_of_nonneg_right (ringChoose_two_mul_le hp hpq hq (k + 1))
      ((even_two_mul _).pow_nonneg _)
  -- `A^{p/q} = (1 + t)^θ ≤ 1 + θ t ≤ B`
  have hAθ : A ^ (p / q) ≤ B := by
    have := rpow_one_add_le_one_add_mul_self (s := A - 1) (by linarith)
      (div_nonneg (by linarith) (by linarith)) ((div_le_one (by linarith)).2 hpq)
    rw [add_sub_cancel] at this
    linarith
  have hA0 : 0 ≤ A := by linarith
  calc twoPointNorm q 1 (ρ * ε) = (A ^ (p / q)) ^ (1 / p) := by
        rw [twoPointNorm, ← Real.rpow_mul hA0]
        congr 1
        field_simp
    _ ≤ B ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hAθ (div_nonneg zero_le_one (by linarith))
    _ = twoPointNorm p 1 ε := rfl


/-- For `r > 0`, `c ↦ ‖1 + c x ε‖_r` is continuous. -/
private theorem continuous_twoPointNorm_one {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Continuous fun c : ℝ => twoPointNorm r 1 (c * x) := by
  unfold twoPointNorm
  exact ((((Real.continuous_rpow_const hr.le).comp (by fun_prop)).add
    ((Real.continuous_rpow_const hr.le).comp (by fun_prop))).div_const 2).rpow_const
    fun _ => Or.inr (div_nonneg zero_le_one hr.le)

/-- The normalised inequality for `1 < p ≤ q ≤ 2` and `|ε| ≤ 1`; the boundary `|ε| = 1` by
continuity (O'Donnell), as the limit of the strict case at `c ε`, `c → 1⁻`. -/
private theorem twoPointNorm_one_le {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    twoPointNorm q 1 (√((p - 1) / (q - 1)) * ε) ≤ twoPointNorm p 1 ε := by
  set ρ := √((p - 1) / (q - 1))
  have hF : Tendsto (fun c : ℝ => twoPointNorm q 1 (c * (ρ * ε))) (𝓝[<] 1)
      (𝓝 (twoPointNorm q 1 (ρ * ε))) := by
    simpa using ((continuous_twoPointNorm_one (by linarith) (ρ * ε)).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hG : Tendsto (fun c : ℝ => twoPointNorm p 1 (c * ε)) (𝓝[<] 1)
      (𝓝 (twoPointNorm p 1 ε)) := by
    simpa using ((continuous_twoPointNorm_one (by linarith) ε).tendsto 1).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hF hG ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with c hc
  have hcε : |c * ε| < 1 := by
    rw [abs_mul, abs_of_pos hc.1]
    calc c * |ε| ≤ c * 1 := mul_le_mul_of_nonneg_left hε hc.1.le
      _ < 1 := by linarith [hc.2]
  simpa [mul_left_comm c] using twoPointNorm_one_le_of_abs_lt hp hpq hq hcε

/-- The two-point inequality for `1 < p ≤ q ≤ 2`. -/
theorem twoPoint_of_le_two {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2) {a b : ℝ}
    (hab : |b| ≤ a) : twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  set ρ := √((p - 1) / (q - 1))
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := sqrt_div_le_one hp hpq
  rcases ((abs_nonneg b).trans hab).eq_or_lt with ha | ha
  · -- `a = 0` forces `b = 0`
    subst ha
    have hb : b = 0 := abs_nonpos_iff.1 hab
    subst hb
    have hp0 : p ≠ 0 := by linarith
    have hq0 : q ≠ 0 := by linarith
    simp [twoPointNorm, Real.zero_rpow, hp0, hq0]
  · -- normalise to `a = 1`
    have hρb : |ρ * b| ≤ a := by
      rw [abs_mul, abs_of_nonneg hρ0]
      nlinarith [abs_nonneg b]
    rw [twoPointNorm_eq_mul (by linarith) ha hρb, twoPointNorm_eq_mul (by linarith) ha hab,
      mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (twoPointNorm_one_le hp hpq hq ?_) ha.le
    rw [abs_div, abs_of_pos ha]
    exact (div_le_one ha).2 hab


/-- Hölder's inequality on two points with equal weights `1/2`: for `X₁, X₂, Y₁, Y₂ ≥ 0` and
conjugate exponents `s`, `t`, `E[X Y] ≤ ‖X‖_s ‖Y‖_t`. -/
private theorem two_point_holder {s t : ℝ} (hst : s.HolderConjugate t) {X₁ X₂ Y₁ Y₂ : ℝ}
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    (X₁ * Y₁ + X₂ * Y₂) / 2 ≤
      ((X₁ ^ s + X₂ ^ s) / 2) ^ (1 / s) * ((Y₁ ^ t + Y₂ ^ t) / 2) ^ (1 / t) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin 2)) (f := ![X₁, X₂])
    (g := ![Y₁, Y₂]) hst (by simp [Fin.forall_fin_two, hX₁, hX₂])
    (by simp [Fin.forall_fin_two, hY₁, hY₂])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hXs : 0 ≤ X₁ ^ s + X₂ ^ s := add_nonneg (Real.rpow_nonneg hX₁ _) (Real.rpow_nonneg hX₂ _)
  have hYt : 0 ≤ Y₁ ^ t + Y₂ ^ t := add_nonneg (Real.rpow_nonneg hY₁ _) (Real.rpow_nonneg hY₂ _)
  rw [Real.div_rpow hXs zero_le_two, Real.div_rpow hYt zero_le_two, div_mul_div_comm,
    ← Real.rpow_add two_pos, hst.one_div_add_one_div, div_one, Real.rpow_one]
  exact div_le_div_of_nonneg_right h zero_le_two

/-- The two-point inequality for `2 ≤ p ≤ q`, by duality. -/
theorem twoPoint_of_two_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) {a b : ℝ} (hab : |b| ≤ a) :
    twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  set ρ := √((p - 1) / (q - 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := sqrt_div_le_one (by linarith) hpq
  have hp1 : 0 < p - 1 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : q ≠ 0 := by linarith
  -- `u = T_ρ f = a + ρ b x ≥ 0`, with values `a ± ρ b`
  have hρb : |ρ * b| ≤ a := by
    rw [abs_mul, abs_of_nonneg hρ0]
    exact (mul_le_of_le_one_left (abs_nonneg b) hρ1).trans hab
  have hUp : 0 ≤ a + ρ * b := by linarith [neg_abs_le (ρ * b)]
  have hUm : 0 ≤ a - ρ * b := by linarith [le_abs_self (ρ * b)]
  set M := ((a + ρ * b) ^ q + (a - ρ * b) ^ q) / 2 with hM
  have hM0 : 0 ≤ M := div_nonneg (add_nonneg (Real.rpow_nonneg hUp _)
    (Real.rpow_nonneg hUm _)) zero_le_two
  -- `g = u^{q − 1} = c + d x`, a nonnegative two-point function
  set c := ((a + ρ * b) ^ (q - 1) + (a - ρ * b) ^ (q - 1)) / 2 with hc
  set d := ((a + ρ * b) ^ (q - 1) - (a - ρ * b) ^ (q - 1)) / 2 with hd
  have hgp : c + d = (a + ρ * b) ^ (q - 1) := by rw [hc, hd]; ring
  have hgm : c - d = (a - ρ * b) ^ (q - 1) := by rw [hc, hd]; ring
  have hgp0 := Real.rpow_nonneg hUp (q - 1)
  have hgm0 := Real.rpow_nonneg hUm (q - 1)
  have hdc : |d| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  have hρd : |ρ * d| ≤ c := by
    rw [abs_mul, abs_of_nonneg hρ0]
    exact (mul_le_of_le_one_left (abs_nonneg d) hρ1).trans hdc
  -- `‖u‖_q^q = E[g u] = E[(T_ρ g) f]` (`T_ρ` is self-adjoint: both are `c a + ρ d b`)
  have hself : M = ((c + ρ * d) * (a + b) + (c - ρ * d) * (a - b)) / 2 := by
    have e : ∀ U : ℝ, 0 ≤ U → U ^ q = U ^ (q - 1) * U := fun U hU => by
      conv_lhs => rw [show q = (q - 1) + 1 by ring]
      rw [Real.rpow_add' hU (by linarith), Real.rpow_one]
    rw [hM, e _ hUp, e _ hUm, ← hgp, ← hgm]
    ring
  -- the conjugate exponents `p' = p / (p − 1)`, `q' = q / (q − 1)`
  set p' := p / (p - 1) with hp'
  set q' := q / (q - 1) with hq'
  have hpp' : p'.HolderConjugate p :=
    ((Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl).symm
  -- Hölder: `E[(T_ρ g) f] ≤ ‖T_ρ g‖_{p'} ‖f‖_p`
  have hH : M ≤ twoPointNorm p' c (ρ * d) * twoPointNorm p a b := by
    rw [hself]
    exact two_point_holder hpp' (by linarith [neg_abs_le (ρ * d)])
      (by linarith [le_abs_self (ρ * d)]) (by linarith [neg_abs_le b])
      (by linarith [le_abs_self b])
  -- the first case at `(q', p')`: `‖T_ρ g‖_{p'} ≤ ‖g‖_{q'}`
  have hρ' : √((q' - 1) / (p' - 1)) = ρ := by
    rw [hρ, hp', hq']
    congr 1
    field_simp
    ring
  have h1 : twoPointNorm p' c (ρ * d) ≤ twoPointNorm q' c d := by
    have := twoPoint_of_le_two (p := q') (q := p') ((one_lt_div hq1).2 (by linarith))
      ((div_le_div_iff₀ hq1 hp1).2 (by nlinarith)) ((div_le_iff₀ hp1).2 (by linarith)) hdc
    rwa [hρ'] at this
  -- `‖g‖_{q'} = ‖u‖_q^{q − 1} = M^{1 / q'}`
  have hg : twoPointNorm q' c d = M ^ (1 / q') := by
    have e : (q - 1) * q' = q := by rw [hq']; field_simp
    rw [twoPointNorm, hgp, hgm, ← Real.rpow_mul hUp, ← Real.rpow_mul hUm, e]
  have key : M ≤ M ^ (1 / q') * twoPointNorm p a b := by
    calc M ≤ twoPointNorm p' c (ρ * d) * twoPointNorm p a b := hH
      _ ≤ twoPointNorm q' c d * twoPointNorm p a b :=
          mul_le_mul_of_nonneg_right h1 (twoPointNorm_nonneg _ hab)
      _ = M ^ (1 / q') * twoPointNorm p a b := by rw [hg]
  -- divide by `‖u‖_q^{q − 1} = M^{1 / q'}`
  change M ^ (1 / q) ≤ twoPointNorm p a b
  rcases hM0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (one_div_ne_zero (by linarith))]
    exact twoPointNorm_nonneg _ hab
  · have hsplit : M ^ (1 / q) * M ^ (1 / q') = M := by
      rw [← Real.rpow_add hpos, show 1 / q + 1 / q' = 1 by rw [hq']; field_simp; ring,
        Real.rpow_one]
    refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hpos (1 / q'))
    rw [hsplit, mul_comm]
    exact key

/-- **The two-point hypercontractive inequality** (Bonami 1970; O'Donnell 2014, §10.1): for
`1 < p ≤ q` and `a ≥ |b|`, `‖a + ρ b ε‖_q ≤ ‖a + b ε‖_p`, `ρ = √((p − 1) / (q − 1))`. -/
theorem twoPoint {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {a b : ℝ} (hab : |b| ≤ a) :
    twoPointNorm q a (√((p - 1) / (q - 1)) * b) ≤ twoPointNorm p a b := by
  rcases le_total q 2 with hq | hq
  · exact twoPoint_of_le_two hp hpq hq hab
  rcases le_total 2 p with hp2 | hp2
  · exact twoPoint_of_two_le hp2 hpq hab
  -- `p ≤ 2 ≤ q`: the semigroup property, `ρ = ρ₂ ρ₁` through `L²`
  set ρ₁ := √((p - 1) / (2 - 1))
  set ρ₂ := √((2 - 1) / (q - 1))
  have hρ₁ : |ρ₁ * b| ≤ a := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_of_le_one_left (abs_nonneg b) (sqrt_div_le_one hp hp2)).trans hab
  have hρ : √((p - 1) / (q - 1)) * b = ρ₂ * (ρ₁ * b) := by
    rw [← mul_assoc, ← Real.sqrt_mul (div_nonneg (by norm_num) (by linarith))]
    congr 2
    field_simp
  rw [hρ]
  exact (twoPoint_of_two_le le_rfl hq hρ₁).trans (twoPoint_of_le_two hp hp2 le_rfl hab)

end BanachProbability
