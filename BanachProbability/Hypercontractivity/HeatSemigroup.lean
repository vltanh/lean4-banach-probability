module

public import BanachProbability.Hypercontractivity.Vector
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The discrete heat semigroup

Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces II* (2017), §6.2.a, p. 18–21: on
the cube `D^n = {−1, 1}^n` the discrete heat semigroup `T (t)`, `t ≥ 0`, multiplies the Walsh
function `w_α = Π_{i ∈ α} ε_i` by `e^{−t #α}`, (6.6) (`heatSemigroup_walsh`), that is,
`T (t) = Π_i T_i (t)`, (6.7), where `T_i (t) (x + ε_i y) = x + e^{−t} ε_i y` acts on the `i`-th
sign. This product is the definition here (`heatSemigroup`): it is the operator `⊗ⁿ K̄` of
`Hypercontractivity/Vector.lean` with `ρ = e^{−t}`. The values of the functions are in a real vector
space with a seminorm `S` (the book: in a Banach space).

* **Lemma 6.2.1** (p. 19): `T (t)` is positive and contractive on `L^p`
  (`seminorm_kBar_le`, `lpNorm_kBar_le`, for one sign), because of
  `T (t) f = e^{−t} f + (1 − e^{−t}) E f`, (6.8) (`kBar_eq`).
* **Lemma 6.2.3** (p. 20–21, Bonami's inequality; the proof is Beckner's): for `1 < p ≤ q` and
  `0 ≤ θ ≤ √((p − 1) / (q − 1))`, `‖x + θ ε y‖_q ≤ ‖x + ε y‖_p` for one sign `ε`
  (`bonami_seminorm`). As `T (t)` is positive, it suffices to consider real `x`, `y`:
  - `1 < p ≤ q ≤ 2`: for `x = 1`, `|y| ≤ 1` by the binomial series
    (`twoPoint_of_le_two`), for `|y| > 1` from `|1 ± θ y| ≤ |y| (1 ± θ y^{−1})` and the first case
    at `y^{−1}`;
  - `2 ≤ p ≤ q`: by duality, `T (t)` being self-adjoint and
    `(q' − 1) / (p' − 1) = (p − 1) / (q − 1)`;
  - `p < 2 < q`: through `L²`, `T (t) = T (t_1) T (t_2)`.
* **Theorem 6.2.2** (p. 19, 21), the "if" part (`heatSemigroup_lpNorm_le`):
  `‖T (t)‖_{L^p (D^n) → L^q (D^n)} ≤ 1` for `1 < p ≤ q` and `e^{−t} ≤ √((p − 1) / (q − 1))`. By
  induction on `n`, writing `D^{n+1} = D × D^n`: Lemma 6.2.3 *with values in `L^q (D^n)`*, then the
  induction hypothesis on each fibre,
  `‖T f‖_{L^q (D; L^q (D^n))} ≤ ‖T^n f‖_{L^p (D; L^q (D^n))} ≤ ‖f‖_{L^p (D; L^p (D^n))}`.

Details: the edge `|y| = 1` of the first case, where the book uses the binomial series at the
boundary of its disc, is obtained by continuity (`twoPoint_of_le_two`). The "only if" part of
Lemma 6.2.3 and Theorem 6.2.2 (the necessity of the condition on `θ`) is not formalized.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### One sign -/

/-- **(6.8)** (HNVW II, p. 19): `T (t) g = e^{−t} g + (1 − e^{−t}) E g` for functions of one sign,
`ρ = e^{−t}`. -/
theorem kBar_eq (ρ : ℝ) (g : Bool → E) (x : Bool) :
    kBar ρ g x = ρ • g x + (1 - ρ) • ((1 / 2 : ℝ) • (g true + g false)) := by
  cases x <;> simp only [kBar, coin_true, coin_false] <;> module

/-- **Lemma 6.2.1** (HNVW II, p. 19), positivity, for one sign: `‖T (t) g‖ ≤ T (t) ‖g‖`, from
(6.8). -/
theorem seminorm_kBar_le (S : Seminorm ℝ E) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (g : Bool → E)
    (x : Bool) : S (kBar ρ g x) ≤ kBar ρ (fun y => S (g y)) x := by
  rw [kBar_eq, kBar_eq]
  have h1 : 0 ≤ 1 - ρ := by linarith
  calc S (ρ • g x + (1 - ρ) • ((1 / 2 : ℝ) • (g true + g false)))
      ≤ S (ρ • g x) + S ((1 - ρ) • ((1 / 2 : ℝ) • (g true + g false))) := map_add_le_add S _ _
    _ = ρ * S (g x) + (1 - ρ) * (1 / 2 * S (g true + g false)) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg hρ0,
          Real.norm_of_nonneg h1, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ ρ * S (g x) + (1 - ρ) * (1 / 2 * (S (g true) + S (g false))) := by
        gcongr
        exact map_add_le_add S _ _
    _ = _ := by simp only [smul_eq_mul]

/-- The `L^r` norm `((|x + y|^r + |x − y|^r) / 2)^{1/r}` of the real two-point function
`x + ε y`. -/
private noncomputable def hsNorm (r x y : ℝ) : ℝ :=
  ((|x + y| ^ r + |x - y| ^ r) / 2) ^ (1 / r)

private theorem hsNorm_base_nonneg (r x y : ℝ) : 0 ≤ (|x + y| ^ r + |x - y| ^ r) / 2 := by
  positivity

private theorem hsNorm_nonneg (r x y : ℝ) : 0 ≤ hsNorm r x y :=
  Real.rpow_nonneg (hsNorm_base_nonneg r x y) _

private theorem hsNorm_neg_left (r x y : ℝ) : hsNorm r (-x) y = hsNorm r x y := by
  rw [hsNorm, hsNorm, show -x + y = -(x - y) by ring, show -x - y = -(x + y) by ring, abs_neg,
    abs_neg, add_comm]

private theorem hsNorm_comm (r x y : ℝ) : hsNorm r x y = hsNorm r y x := by
  rw [hsNorm, hsNorm, add_comm x y, abs_sub_comm x y]

private theorem hsNorm_of_abs_le {r x y : ℝ} (h : |y| ≤ x) : hsNorm r x y = twoPointNorm r x y := by
  rw [hsNorm, twoPointNorm, abs_of_nonneg (by linarith [neg_abs_le y]),
    abs_of_nonneg (by linarith [le_abs_self y])]

/-- Monotonicity of the norm in the absolute values. -/
private theorem hsNorm_le_of_abs_le {r x y x' y' : ℝ} (hr : 0 < r) (hp : |x + y| ≤ |x' + y'|)
    (hm : |x - y| ≤ |x' - y'|) : hsNorm r x y ≤ hsNorm r x' y' := by
  unfold hsNorm
  gcongr

private theorem hs_sqrt_le_one {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) : √((p - 1) / (q - 1)) ≤ 1 :=
  Real.sqrt_le_one.2 ((div_le_one (by linarith)).2 (by linarith))

/-- **Lemma 6.2.3** (HNVW II, p. 20), the case `1 < p ≤ q ≤ 2`, for real `x`, `y` and
`θ = √((p − 1) / (q − 1))`. If `|y| ≤ |x|` (the book: `x = 1`, `|y| ≤ 1`) this is
`twoPoint_of_le_two`, the binomial series and the comparison of its even terms. If `|y| > |x|`, then
`|x ± θ y| ≤ |y ± θ x|` (the book: `|1 ± θ y| ≤ |y| (1 ± θ y^{−1})`, from
`(1 − a) (1 − b) ≥ 0` for `a, b ≤ 1`), and the first case applies with `x`, `y` exchanged. -/
private theorem bonami_of_le_two {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2) (x y : ℝ) :
    hsNorm q x (√((p - 1) / (q - 1)) * y) ≤ hsNorm p x y := by
  set θ := √((p - 1) / (q - 1)) with hθ
  have hθ0 : 0 ≤ θ := Real.sqrt_nonneg _
  have hθ1 : θ ≤ 1 := hs_sqrt_le_one hp hpq
  -- the case `|y| ≤ |x|`
  have key : ∀ a b : ℝ, |b| ≤ |a| → hsNorm q a (θ * b) ≤ hsNorm p a b := by
    intro a b hab
    have hθb : |θ * b| ≤ |a| := by
      rw [abs_mul, abs_of_nonneg hθ0]
      exact (mul_le_of_le_one_left (abs_nonneg b) hθ1).trans hab
    have hflip : ∀ r c, hsNorm r a c = hsNorm r |a| c := fun r c => by
      rcases abs_choice a with h | h
      · rw [h]
      · rw [h, hsNorm_neg_left]
    rw [hflip, hflip p, hsNorm_of_abs_le hθb, hsNorm_of_abs_le hab]
    exact twoPoint_of_le_two hp hpq hq hab
  rcases le_or_gt |y| |x| with h | h
  · exact key x y h
  · -- the case `|y| > |x|`
    have hsq : x ^ 2 ≤ y ^ 2 := sq_le_sq.2 h.le
    have hθ2 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0 hθ1
    have hstep : hsNorm q x (θ * y) ≤ hsNorm q y (θ * x) := by
      refine hsNorm_le_of_abs_le (by linarith) (sq_le_sq.1 ?_) ?_
      · nlinarith [mul_nonneg (sub_nonneg.2 hθ2) (sub_nonneg.2 hsq)]
      · rw [← abs_neg (y - θ * x)]
        refine sq_le_sq.1 ?_
        nlinarith [mul_nonneg (sub_nonneg.2 hθ2) (sub_nonneg.2 hsq)]
    exact hstep.trans ((key y x h.le).trans_eq (hsNorm_comm p y x))

/-- Hölder's inequality for real two-point functions, `E [f g] ≤ ‖f‖_s ‖g‖_t`. -/
private theorem hs_holder {s t : ℝ} (hst : s.HolderConjugate t) (a b c d : ℝ) :
    ((a + b) * (c + d) + (a - b) * (c - d)) / 2 ≤ hsNorm s a b * hsNorm t c d := by
  have h := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin 2)) (f := ![a + b, a - b])
    (g := ![c + d, c - d]) hst
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hX : 0 ≤ |a + b| ^ s + |a - b| ^ s := by positivity
  have hY : 0 ≤ |c + d| ^ t + |c - d| ^ t := by positivity
  rw [hsNorm, hsNorm, Real.div_rpow hX zero_le_two, Real.div_rpow hY zero_le_two, div_mul_div_comm,
    ← Real.rpow_add two_pos, hst.one_div_add_one_div, div_one, Real.rpow_one]
  exact div_le_div_of_nonneg_right h zero_le_two

/-- **Lemma 6.2.3** (HNVW II, p. 21), the case `2 ≤ p ≤ q`, for real `x`, `y` and
`θ = √((p − 1) / (q − 1))`, by duality: `T (t)` is self-adjoint, the conjugate exponents satisfy
`1 < q' ≤ p' ≤ 2` and `(q' − 1) / (p' − 1) = (p − 1) / (q − 1)`, so that
`‖T (t)‖_{L^p → L^q} = ‖T (t)‖_{L^{q'} → L^{p'}} ≤ 1`. The duality is applied to the function
`g = sgn (u) |u|^{q−1}` that norms `u = T (t) f`. -/
private theorem bonami_of_two_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (x y : ℝ) :
    hsNorm q x (√((p - 1) / (q - 1)) * y) ≤ hsNorm p x y := by
  set θ := √((p - 1) / (q - 1)) with hθ
  have hp1 : 0 < p - 1 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : q ≠ 0 := by linarith
  -- `g = sgn (u) |u|^{q−1} = c + ε d`
  set G : ℝ → ℝ := fun u => SignType.sign u * |u| ^ (q - 1) with hG
  have hGu : ∀ u, G u * u = |u| ^ q := fun u => by
    simp only [hG]
    rw [mul_right_comm, sign_mul_self]
    rcases eq_or_ne u 0 with rfl | hu
    · rw [abs_zero, zero_mul, Real.zero_rpow (by linarith)]
    · rw [← Real.rpow_one_add' (abs_nonneg u) (by linarith)]
      congr 1
      ring
  set q' := q / (q - 1) with hq'
  have hGabs : ∀ u, |G u| ^ q' = |u| ^ q := fun u => by
    have e : (q - 1) * q' = q := by rw [hq']; field_simp
    rcases eq_or_ne u 0 with rfl | hu
    · have h0 : q' ≠ 0 := div_ne_zero hq0 hq1.ne'
      simp [hG, Real.zero_rpow (by linarith : q ≠ 0), Real.zero_rpow h0]
    · have hs : |((SignType.sign u : SignType) : ℝ)| = 1 := by
        rcases lt_or_gt_of_ne hu with h | h
        · rw [sign_neg h]; simp
        · rw [sign_pos h]; simp
      simp only [hG, abs_mul, hs, one_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _), ← Real.rpow_mul (abs_nonneg u), e]
  set c := (G (x + θ * y) + G (x - θ * y)) / 2 with hc
  set d := (G (x + θ * y) - G (x - θ * y)) / 2 with hd
  have hgp : c + d = G (x + θ * y) := by rw [hc, hd]; ring
  have hgm : c - d = G (x - θ * y) := by rw [hc, hd]; ring
  set M := (|x + θ * y| ^ q + |x - θ * y| ^ q) / 2 with hM
  have hM0 : 0 ≤ M := hsNorm_base_nonneg q x (θ * y)
  -- `‖u‖_q^q = E [g T f] = E [(T g) f]`, `T` being self-adjoint
  have hself : M = ((c + θ * d) * (x + y) + (c - θ * d) * (x - y)) / 2 := by
    rw [hM, ← hGu, ← hGu, ← hgp, ← hgm]
    ring
  set p' := p / (p - 1) with hp'
  have hpp' : p'.HolderConjugate p :=
    ((Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl).symm
  have hH : M ≤ hsNorm p' c (θ * d) * hsNorm p x y := by
    rw [hself]
    exact hs_holder hpp' c (θ * d) x y
  -- the first case at `(q', p')`
  have hθ' : √((q' - 1) / (p' - 1)) = θ := by
    rw [hθ, hp', hq']
    congr 1
    field_simp
    ring
  have h1 : hsNorm p' c (θ * d) ≤ hsNorm q' c d := by
    have := bonami_of_le_two (p := q') (q := p') ((one_lt_div hq1).2 (by linarith))
      ((div_le_div_iff₀ hq1 hp1).2 (by nlinarith)) ((div_le_iff₀ hp1).2 (by linarith)) c d
    rwa [hθ'] at this
  -- `‖g‖_{q'} = ‖u‖_q^{q − 1}`
  have hg : hsNorm q' c d = M ^ (1 / q') := by
    rw [hsNorm, hgp, hgm, hGabs, hGabs]
  have key : M ≤ M ^ (1 / q') * hsNorm p x y := by
    refine hH.trans ?_
    rw [← hg]
    exact mul_le_mul_of_nonneg_right h1 (hsNorm_nonneg p x y)
  change M ^ (1 / q) ≤ hsNorm p x y
  rcases hM0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (one_div_ne_zero (by linarith))]
    exact hsNorm_nonneg p x y
  · have hsplit : M ^ (1 / q) * M ^ (1 / q') = M := by
      rw [← Real.rpow_add hpos, show 1 / q + 1 / q' = 1 by rw [hq']; field_simp; ring,
        Real.rpow_one]
    refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hpos (1 / q'))
    rw [hsplit, mul_comm]
    exact key

/-- **Lemma 6.2.3** (HNVW II, p. 20–21) for real `x`, `y` and `θ = √((p − 1) / (q − 1))`: the two
cases above and, for `p < 2 < q`, `‖T (t)‖_{L^p → L^q} ≤ ‖T (t_1)‖_{L² → L^q} ‖T (t_2)‖_{L^p → L²}`
with `e^{−t_2} = √(p − 1)`, `e^{−t_1} = √(1 / (q − 1))`. -/
private theorem bonami_real {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (x y : ℝ) :
    hsNorm q x (√((p - 1) / (q - 1)) * y) ≤ hsNorm p x y := by
  rcases le_total q 2 with hq | hq
  · exact bonami_of_le_two hp hpq hq x y
  rcases le_total 2 p with hp2 | hp2
  · exact bonami_of_two_le hp2 hpq x y
  have hρ : √((p - 1) / (q - 1)) * y = √((2 - 1) / (q - 1)) * (√((p - 1) / (2 - 1)) * y) := by
    rw [← mul_assoc, ← Real.sqrt_mul (div_nonneg (by norm_num) (by linarith))]
    congr 2
    field_simp
  rw [hρ]
  exact (bonami_of_two_le le_rfl hq x _).trans (bonami_of_le_two hp hp2 le_rfl x y)

/-- **Lemma 6.2.1** (HNVW II, p. 19), contractivity, for one sign: `‖T (t) g‖_{L^p} ≤ ‖g‖_{L^p}`,
as `T (t) g` is a convex combination of `g` and `E g`, (6.8); on two points it is the convexity of
`S^p`. -/
theorem lpNorm_kBar_le (S : Seminorm ℝ E) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {p : ℝ}
    (hp : 1 ≤ p) (g : Bool → E) :
    ((S (kBar ρ g true) ^ p + S (kBar ρ g false) ^ p) / 2) ^ (1 / p) ≤
      ((S (g true) ^ p + S (g false) ^ p) / 2) ^ (1 / p) := by
  have hconv := convexOn_rpow hp
  have hS : ∀ z, 0 ≤ S z := apply_nonneg S
  have h : ∀ x y : Bool, ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ 1 →
      (ρ' * S (g x) + (1 - ρ') * S (g y)) ^ p ≤ ρ' * S (g x) ^ p + (1 - ρ') * S (g y) ^ p :=
    fun x y ρ' h0 h1 => by
      simpa only [smul_eq_mul] using hconv.2 (Set.mem_Ici.2 (hS (g x))) (Set.mem_Ici.2 (hS (g y)))
        h0 (by linarith : 0 ≤ 1 - ρ') (by ring)
  have e1 : kBar ρ (fun y => S (g y)) true =
      (1 + ρ) / 2 * S (g true) + (1 - (1 + ρ) / 2) * S (g false) := by
    simp only [kBar, coin_true, smul_eq_mul]; ring
  have e2 : kBar ρ (fun y => S (g y)) false =
      (1 + ρ) / 2 * S (g false) + (1 - (1 + ρ) / 2) * S (g true) := by
    simp only [kBar, coin_false, smul_eq_mul]; ring
  have h1 := (Real.rpow_le_rpow (hS _) (seminorm_kBar_le S hρ0 hρ1 g true) (by linarith)).trans
    (e1 ▸ h true false ((1 + ρ) / 2) (by linarith) (by linarith))
  have h2 := (Real.rpow_le_rpow (hS _) (seminorm_kBar_le S hρ0 hρ1 g false) (by linarith)).trans
    (e2 ▸ h false true ((1 + ρ) / 2) (by linarith) (by linarith))
  refine Real.rpow_le_rpow (div_nonneg (add_nonneg (Real.rpow_nonneg (hS _) _)
    (Real.rpow_nonneg (hS _) _)) zero_le_two) ?_ (by positivity)
  linarith

/-- **Lemma 6.2.3** (HNVW II, p. 20–21, Bonami's inequality), the "if" part, for functions of one
sign with values in a seminormed space: for `1 < p ≤ q` and `0 ≤ ρ ≤ √((p − 1) / (q − 1))`,
`‖T g‖_{L^q} ≤ ‖g‖_{L^p}`, where `T (x + ε y) = x + ρ ε y`. As `T` is positive,
`S (T g) ≤ T (S g)` (`seminorm_kBar_le`), it suffices to consider real functions; for
`ρ < √((p − 1) / (q − 1))` use contractivity first (`lpNorm_kBar_le`). -/
theorem bonami_seminorm (S : Seminorm ℝ E) {p q ρ : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ √((p - 1) / (q - 1))) (g : Bool → E) :
    ((S (kBar ρ g true) ^ q + S (kBar ρ g false) ^ q) / 2) ^ (1 / q) ≤
      ((S (g true) ^ p + S (g false) ^ p) / 2) ^ (1 / p) := by
  set θ := √((p - 1) / (q - 1)) with hθ
  have hθ1 : θ ≤ 1 := hs_sqrt_le_one hp hpq
  have hθ0 : 0 < θ := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  have hq0 : 0 ≤ q := by linarith
  have hS : ∀ z, 0 ≤ S z := apply_nonneg S
  -- the case `ρ = θ`
  have key : ∀ g : Bool → E, ((S (kBar θ g true) ^ q + S (kBar θ g false) ^ q) / 2) ^ (1 / q) ≤
      ((S (g true) ^ p + S (g false) ^ p) / 2) ^ (1 / p) := by
    intro g
    set x := (S (g true) + S (g false)) / 2 with hx
    set y := (S (g true) - S (g false)) / 2 with hy
    have h := bonami_real hp hpq x y
    rw [← hθ, hsNorm, hsNorm, show x + y = S (g true) by rw [hx, hy]; ring,
      show x - y = S (g false) by rw [hx, hy]; ring, abs_of_nonneg (hS _),
      abs_of_nonneg (hS _)] at h
    refine le_trans (Real.rpow_le_rpow ?_ ?_ (by positivity)) h
    · exact div_nonneg (add_nonneg (Real.rpow_nonneg (hS _) _) (Real.rpow_nonneg (hS _) _))
        zero_le_two
    · have e1 : kBar θ (fun y => S (g y)) true = x + θ * y := by
        simp only [kBar, coin_true, smul_eq_mul, hx, hy]; ring
      have e2 : kBar θ (fun y => S (g y)) false = x - θ * y := by
        simp only [kBar, coin_false, smul_eq_mul, hx, hy]; ring
      have h1 := seminorm_kBar_le S hθ0.le hθ1 g true
      have h2 := seminorm_kBar_le S hθ0.le hθ1 g false
      rw [e1] at h1
      rw [e2] at h2
      refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) zero_le_two
      · exact Real.rpow_le_rpow (hS _) (h1.trans (le_abs_self _)) hq0
      · exact Real.rpow_le_rpow (hS _) (h2.trans (le_abs_self _)) hq0
  -- `T (ρ) = T (θ) T (ρ / θ)`
  have hfac : kBar ρ g = kBar θ (kBar (ρ / θ) g) := by
    have e : ρ = θ * (ρ / θ) := (mul_div_cancel₀ ρ hθ0.ne').symm
    funext z
    conv_lhs => rw [e]
    cases z <;> simp only [kBar, coin_true, coin_false] <;> module
  rw [hfac]
  exact (key _).trans (lpNorm_kBar_le S (by positivity) ((div_le_one hθ0).2 hρ) hp.le g)

/-! ### The semigroup on `n` signs -/

/-- **The discrete heat semigroup** `T (t) = Π_i T_i (t)` on functions of `n` signs (HNVW II, (6.7),
p. 19), where `T_i (t) (x + ε_i y) = x + e^{−t} ε_i y`; see `heatSemigroup_walsh` for the form
(6.6). -/
noncomputable def heatSemigroup (t : ℝ) {n : ℕ} (f : (Fin n → Bool) → E) : (Fin n → Bool) → E :=
  kBarTensor (Real.exp (-t)) n f

/-- **(6.6)** (HNVW II, p. 19): `T (t) (w_α x) = e^{−t #α} w_α x` for the Walsh functions
`w_α = Π_{i ∈ α} ε_i`. -/
theorem heatSemigroup_walsh (t : ℝ) {n : ℕ} (α : Finset (Fin n)) (x : E) :
    heatSemigroup t (fun ε : Fin n → Bool => (∏ i ∈ α, coin (ε i)) • x) =
      fun ε => Real.exp (-t * α.card) • (∏ i ∈ α, coin (ε i)) • x := by
  -- the statement for the indicator of `α`, by induction on `n`
  have key : ∀ (n : ℕ) (a : Fin n → Prop) [DecidablePred a] (x : E),
      kBarTensor (Real.exp (-t)) n (fun ε : Fin n → Bool =>
        (∏ i, if a i then coin (ε i) else 1) • x) =
      fun ε => (∏ i, if a i then Real.exp (-t) else 1) •
        (∏ i, if a i then coin (ε i) else 1) • x := by
    intro n
    induction n with
    | zero => intro a _ x; funext ε; simp [kBarTensor_zero]
    | succ n ih =>
      intro a _ x
      funext ε
      have hT : ∀ η : Bool, kBarTensor (Real.exp (-t)) n (fun ε' : Fin n → Bool =>
          (∏ i, if a i then coin ((Fin.cons η ε' : Fin (n + 1) → Bool) i) else 1) • x)
            (Fin.tail ε) = (if a 0 then coin η else 1) •
          (∏ i : Fin n, if a i.succ then Real.exp (-t) else 1) •
            (∏ i : Fin n, if a i.succ then coin (ε i.succ) else 1) • x := by
        intro η
        have e : (fun ε' : Fin n → Bool =>
            (∏ i, if a i then coin ((Fin.cons η ε' : Fin (n + 1) → Bool) i) else 1) • x) =
            fun ε' => (∏ i : Fin n, if a i.succ then coin (ε' i) else 1) •
              ((if a 0 then coin η else 1) • x) := by
          funext ε'
          rw [Fin.prod_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]
          rw [mul_comm, mul_smul]
        rw [e, ih (fun i => a i.succ)]
        simp only [Fin.tail, smul_smul]
        congr 1
        ring
      rw [kBarTensor_succ]
      simp only [hT]
      simp only [kBar, coin_true, coin_false, Fin.prod_univ_succ]
      split_ifs <;> module
  classical
  have h := key n (fun i => i ∈ α) x
  have e1 : ∀ ε : Fin n → Bool, (∏ i, if i ∈ α then coin (ε i) else 1) = ∏ i ∈ α, coin (ε i) :=
    fun ε => by rw [Finset.prod_ite_mem, Finset.univ_inter]
  have e2 : (∏ i : Fin n, if i ∈ α then Real.exp (-t) else 1) = Real.exp (-t * α.card) := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [e1, e2] at h
  exact h

/-- `T (t) (c + Σ_i ε_i x_i) = c + e^{−t} Σ_i ε_i x_i`, (6.6) for `#α ≤ 1`. -/
theorem heatSemigroup_affine (t : ℝ) {n : ℕ} (c : E) (x : Fin n → E) :
    heatSemigroup t (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) =
      fun ε => c + Real.exp (-t) • ∑ i, coin (ε i) • x i :=
  kBarTensor_affine _ c x

/-- **Theorem 6.2.2** (HNVW II, p. 19, proof p. 21; hypercontractivity of the discrete heat
semigroup), the "if" part, for functions on the cube with values in a seminormed space:
`‖T (t) f‖_{L^q} ≤ ‖f‖_{L^p}` for `1 < p ≤ q` and `e^{−t} ≤ √((p − 1) / (q − 1))`. By induction on
the number of signs, `T = T_D T^n` on `D^{n+1} = D × D^n`:
`‖T f‖_{L^q (D; L^q (D^n))} ≤ ‖T^n f‖_{L^p (D; L^q (D^n))} ≤ ‖f‖_{L^p (D; L^p (D^n))}`, where the
first inequality is Lemma 6.2.3 with values in `L^q (D^n)`, that is, for the seminorm
`F ↦ ‖F‖_{L^q}` (`SignCube.lpSeminorm`), and the second the induction hypothesis for each value of
the sign in `D`. -/
theorem heatSemigroup_lpNorm_le (S : Seminorm ℝ E) {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (ht : Real.exp (-t) ≤ √((p - 1) / (q - 1))) {n : ℕ} (f : (Fin n → Bool) → E) :
    SignCube.lpNorm S q (heatSemigroup t f) ≤ SignCube.lpNorm S p f := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hS : ∀ z, 0 ≤ S z := apply_nonneg S
  unfold heatSemigroup
  set ρ := Real.exp (-t)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  induction n with
  | zero =>
    -- functions of no signs are constants
    have e : f = fun _ => f Fin.elim0 := funext fun ε => congrArg f (Subsingleton.elim _ _)
    rw [kBarTensor_zero, e, lpNorm_const (hS _) hq0, lpNorm_const (hS _) hp0]
  | succ n ih =>
    -- `h (η) = T^n f (η, ·)`, a function on `D` with values in `L^q (D^n)`
    set h : Bool → (Fin n → Bool) → E := fun η => kBarTensor ρ n fun ε' => f (Fin.cons η ε')
    have hfib : ∀ η, (fun ε => kBarTensor ρ (n + 1) f (Fin.cons η ε)) = kBar ρ h η := by
      intro η
      funext ε
      rw [kBarTensor_succ, Fin.cons_zero, Fin.tail_cons]
      simp only [kBar, h, Pi.smul_apply, Pi.add_apply]
    rw [lpNorm_succ hS hq0, lpNorm_succ hS hp0, hfib, hfib]
    -- Lemma 6.2.3 in `L^q (D^n)`, then the induction hypothesis
    refine (bonami_seminorm (lpSeminorm S q hq1) hp hpq hρ0 ht h).trans ?_
    simp only [lpSeminorm_apply]
    have h0 : ∀ η, 0 ≤ SignCube.lpNorm S q (h η) := fun η => lpNorm_nonneg hS q _
    refine Real.rpow_le_rpow (div_nonneg (add_nonneg (Real.rpow_nonneg (h0 _) _)
      (Real.rpow_nonneg (h0 _) _)) zero_le_two) ?_ (by positivity)
    exact div_le_div_of_nonneg_right (add_le_add
      (Real.rpow_le_rpow (h0 _) (ih _) hp0.le) (Real.rpow_le_rpow (h0 _) (ih _) hp0.le)) zero_le_two

end BanachProbability
