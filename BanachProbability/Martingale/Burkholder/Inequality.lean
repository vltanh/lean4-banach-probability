module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy sur les processus stochastiques, Astérisque 157–158 (1988), 75–94: the inequality (1.2) of
Theorem 1.1, for real Hilbert spaces, and the inequality (3.1) of Theorem 3.1, by the arguments of
the paper (§1 and §3); the concavity (1.17) of Remark 1.2, which the paper states without proof,
completed from the paper's own (1.12)–(1.14) and the shift of its proof of (1.8) (step 4 below).
The equality cases and the sharpness of the constants are not formalized. The same inequalities
are Theorems 3.5 and 8.6 of A. Osękowski, *Sharp martingale and semimartingale inequalities*
(2012), and the case `H = ℝ` of Theorem 1.1 is in D. L. Burkholder, *Boundary value problems and
sharp inequalities for martingale transforms*, Ann. Probab. 12 (1984); neither was obtained.

## Main results

* `inequality` (Burkholder 1988, Theorem 1.1; Osękowski, Theorem 3.5): for martingales `X`, `Y`
  with values in a separable real Hilbert space `H`, started at `0`, with
  `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` with `p* = max (p, p / (p − 1))`. The proof does not use
  the separability of `H`: `inequality_of_subordinate` is the same statement without it.
* `squareFunction` (Burkholder 1988, Theorem 3.1; Osękowski, Theorem 8.6):
  `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
  `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}` (`squareFunction_of_martingale` without
  separability).
* `burkholderU`: Burkholder's function (1.6),
  `U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, written as a function of
  `s = |x|`, `r = |y|`. Here `x` is the position of the subordinate martingale `X` and `y` that of
  the dominating one `Y`; Burkholder's `u (x, y)` takes them in the other order,
  `U (x, y) = u (y, x)` (`Martingale/Burkholder/Function.lean` restates it in his order).
  `burkholderU_ge`: `U ≥ V`, `V (x, y) = |x|^p − (p* − 1)^p |y|^p` (1.10).
  `burkholderU_concaveOn_line`:
  `t ↦ U (x + t h, y + t k)` is concave on `ℝ` if `|h| ≤ |k|` (Remark 1.2, (1.17)).

## The proof (Burkholder 1988, §1)

1. (1.11) `φ (p) = (p − 1)^{p−1} / p^{p−2}` is `≤ 1` for `1 < p ≤ 2` and `≥ 1` for `p ≥ 2`
   (`phi_le_one`, `one_le_phi`): `log φ` vanishes at `1` and `2`, is convex on `[1, 2]` and concave
   on `[2, ∞)` (its second derivative is `(2 − p) / (p² (p − 1))`), and tends to `∞` (it is at
   least `log p − 1`).
2. (1.10) `V ≤ U` (`burkholderU_ge`): by homogeneity, on `|x| + |y| = 1` and with `t` the norm
   of the dominating martingale's position, `U − V = F (t) = α_p (1 − p* t) − (1 − t)^p +
   (p* − 1)^p t^p` (`bF`). If `p = 2`, `F ≡ 0`. If `p > 2`, `F` is concave on `[0, s₀]` and convex
   on `[s₀, 1]` for some `s₀ ≤ 1/p*`, `F (1/p*) = F' (1/p*) = 0`, and `F (0) = α_p − 1 ≥ 0` by
   (1.11). If `p < 2`, `F` is convex on `[0, s₀]` for some `s₀ ≥ 1/p*` and concave on `[s₀, 1]`,
   and `F (1) ≥ 0` by (1.11) (`bF_nonneg`). Burkholder asserts that `s₀` exists; here it is
   `1/(1 + (p* − 1)^{p/(p−2)})`, read off from `F''`.
3. (1.12)–(1.14): if `x + t h` and `y + t k` never vanish, `G (t) = U (x + t h, y + t k)` is twice
   differentiable.
   For `p ≥ 2`, `U = α_p ψ (|x|, |y|)` with `ψ (s, r) = (s − (p − 1) r)(s + r)^{p−1}` (`psi`, not
   to be confused with Burkholder's gradient `ψ`), and the
   second derivative of `t ↦ ψ (S, R)`, `S = |x + t h|`, `R = |y + t k|`, is
   `p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S''
   − (p − 1)(S + R)(|k|² − |h|²))` (`psi_hasDerivAt_two`): its three terms are Burkholder's
   `−C`, `−B`, `−A` of (1.14), each `≤ 0` (`psi_two_sign`). For `p ≤ 2`, `(p − 1) U` is `−α_p ψ`
   with the arguments exchanged. So `G` is concave (`psi_line_of_ne`), and
   `G (1) ≤ G (0) + G' (0)` (1.13) is (1.12),
   `U (x + h, y + k) ≤ U (x, y) + ⟨∇_x U, h⟩ + ⟨∇_y U, k⟩`, with Burkholder's `ψ` and `φ` as the
   gradients (`gradX`, `gradY`, `burkholderU_zigzag_of_ne`).
4. Remark 1.2 (`burkholderU_concaveOn_line`) states the concavity on every line without proof. It
   follows from step 3 by the device of the proof of (1.8): in `H ⊕ ℝ` the lines through `(x, δ)`
   and `(y, δ)` with directions `(h, 0)` and `(k, 0)` never vanish for `δ ≠ 0`; let `δ → 0`.
5. (1.8) `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` (`integral_burkholderU_succ_le`): the values of
   `X`, `Y` lie in `H = H ⊕ 0`, a proper closed subspace of `H ⊕ ℝ` (Burkholder: "otherwise
   enlarge `H` slightly"), and `a = (0, δ)` is orthogonal to it; `F_k = a + X_k` and
   `G_k = a + Y_k` are martingales that never vanish, (1.15) holds by (1.12), and the linear terms
   have zero expectation by the martingale property (`method_step`, `integral_inner_increment`:
   the pull-out property of `E [· | ℱ_k]`). Let `δ → 0` by dominated convergence
   (`tendsto_integral_burkholderU_shift`). Then (1.9): `U (X_0, Y_0) = U (0, 0) = 0`, so
   `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ 0` (`integral_burkholderU_nonpos`).
6. Integrability: if `‖Y_n‖_p = ∞` there is nothing to prove; otherwise `Y_k = E [Y_n | ℱ_k]` and
   `X_k = Σ_{j < k} dX_{j+1}` are in `L^p` for `k ≤ n` (Burkholder:
   `‖g_n‖_p ≤ Σ_k ‖e_k‖_p ≤ Σ_k ‖d_k‖_p`), and every term in step 5 is dominated by
   `C (|X_k| + |Y_k| + |dX_{k+1}| + |dY_{k+1}| + 2)^p`.
7. Theorem 3.1, the square function (proof of Theorem 3.1): in `K = ℓ²_H`, the martingale
   `F_m = (X_m, 0, 0, …)` and `G_m = (dX_1, …, dX_m, 0, …)` have increments of equal norm, so each
   is differentially subordinate to the other, `|F_n| = |X_n|` and `|G_n| = 𝒮_n X`; Theorem 1.1
   applies to `(G, F)` and to `(F, G)`.

The statements are the ones cited (Cassese, Theorem 2.3): the martingales start at `0`
(`d_0 = e_0 = 0`), so (1.9) is `U (0, 0) = 0` and (1.16) is not needed, and the inequality is at
a fixed time `n` rather than for `sup_n ‖·‖_p`. In step 7, up to time `n` the values of
Burkholder's `F` and `G` lie in the first `n + 1` coordinates of `ℓ²_H`; the proof works in that
subspace, `H^{n+1}` (`PiLp 2`), with `X` in the last coordinate and its increments in the first
`n`, and with both martingales stopped at `n`, which does not change them up to time `n`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace RealInnerProductSpace

namespace BanachProbability.Burkholder

/-! ### Gluing concave functions through one-sided derivatives -/

/-- **Gluing concave functions through one-sided derivatives.** If `f : ℝ → ℝ` is concave on the
two parts `s ∩ Iic a` and `s ∩ Ici a` of a convex set `s`, and its left derivative `dl` and right
derivative `dr` at `a` satisfy `dr ≤ dl`, then `f` is concave on `s`. (With `s = univ`: concave on
`Iic a` and on `Ici a`. The convex case follows by applying this to `-f`.) -/
theorem bkh_concaveOn_glue {s : Set ℝ} {f : ℝ → ℝ} {a dl dr : ℝ} (hs : Convex ℝ s)
    (hl : ConcaveOn ℝ (s ∩ Iic a) f) (hr : ConcaveOn ℝ (s ∩ Ici a) f)
    (hdl : HasDerivWithinAt f dl (Iic a) a) (hdr : HasDerivWithinAt f dr (Ici a) a)
    (hd : dr ≤ dl) : ConcaveOn ℝ s f := by
  refine concaveOn_of_slope_anti_adjacent hs ?_
  intro x y z hx hz hxy hyz
  rcases le_or_gt z a with hza | haz
  · exact hl.slope_anti_adjacent ⟨hx, (hxy.trans hyz).le.trans hza⟩ ⟨hz, hza⟩ hxy hyz
  rcases le_or_gt a x with hax | hxa
  · exact hr.slope_anti_adjacent ⟨hx, hax⟩ ⟨hz, hax.trans (hxy.trans hyz).le⟩ hxy hyz
  -- `x < a < z`: the slopes of chords ending at `a` are `≥ dl`, those starting at `a` are `≤ dr`
  have ha : a ∈ s := hs.ordConnected.out hx hz ⟨hxa.le, haz.le⟩
  have hL : ∀ u ∈ s, u < a → dl * (a - u) ≤ f a - f u := fun u hu hua => by
    have := hl.le_slope_of_hasDerivWithinAt_Iio ⟨hu, hua.le⟩ ⟨ha, self_mem_Iic⟩ hua
      (hdl.mono Iio_subset_Iic_self)
    rwa [slope_def_field, le_div_iff₀ (sub_pos.2 hua)] at this
  have hR : ∀ v ∈ s, a < v → f v - f a ≤ dr * (v - a) := fun v hv hav => by
    have := hr.slope_le_of_hasDerivWithinAt_Ioi ⟨ha, self_mem_Ici⟩ ⟨hv, hav.le⟩ hav
      (hdr.mono Ioi_subset_Ici_self)
    rwa [slope_def_field, div_le_iff₀ (sub_pos.2 hav)] at this
  rcases lt_trichotomy y a with hya | rfl | hay
  · -- `x < y < a < z`
    have h1 := hl.slope_anti_adjacent ⟨hx, hxa.le⟩ ⟨ha, self_mem_Iic⟩ hxy hya
    have h2 := hL y (hs.ordConnected.out hx ha ⟨hxy.le, hya.le⟩) hya
    have h3 := hR z hz haz
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (sub_pos.2 hyz) (sub_pos.2 hya)]
    nlinarith [mul_le_mul_of_nonneg_right h3 (sub_pos.2 hya).le,
      mul_le_mul_of_nonneg_right hd (mul_pos (sub_pos.2 haz) (sub_pos.2 hya)).le,
      mul_le_mul_of_nonneg_right h2 (sub_pos.2 haz).le]
  · -- `y = a`
    have h2 := hL x hx hxa
    have h3 := hR z hz haz
    rw [div_le_div_iff₀ (sub_pos.2 hyz) (sub_pos.2 hxa)]
    nlinarith [mul_le_mul_of_nonneg_right h3 (sub_pos.2 hxa).le,
      mul_le_mul_of_nonneg_right hd (mul_pos (sub_pos.2 hyz) (sub_pos.2 hxa)).le,
      mul_le_mul_of_nonneg_right h2 (sub_pos.2 hyz).le]
  · -- `x < a < y < z`
    have h1 := hr.slope_anti_adjacent ⟨ha, self_mem_Ici⟩ ⟨hz, haz.le⟩ hay hyz
    have h2 := hL x hx hxa
    have h3 := hR y (hs.ordConnected.out ha hz ⟨hay.le, hyz.le⟩) hay
    refine h1.trans ?_
    rw [div_le_div_iff₀ (sub_pos.2 hay) (sub_pos.2 hxy)]
    nlinarith [mul_le_mul_of_nonneg_right h3 (sub_pos.2 hxa).le,
      mul_le_mul_of_nonneg_right hd (mul_pos (sub_pos.2 hay) (sub_pos.2 hxa)).le,
      mul_le_mul_of_nonneg_right h2 (sub_pos.2 hay).le]

/-! ### The function `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}` and its derivatives -/

/-- `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}`; Burkholder's function in the argument order of
`burkholderU` (subordinate first) is `α ψ (|x|, |y|)` for `p ≥ 2` and `−α (p − 1)⁻¹ ψ (|y|, |x|)`
for `p ≤ 2`. Not Burkholder's `ψ`, which is a gradient (`gradX`). -/
private noncomputable def psi (p s r : ℝ) : ℝ := (s - (p - 1) * r) * (s + r) ^ (p - 1)

/-- `∂ψ/∂s = p (s + r)^{p−2} (s − (p − 2) r)`. -/
private noncomputable def psiS (p s r : ℝ) : ℝ := p * (s + r) ^ (p - 2) * (s - (p - 2) * r)

/-- `∂ψ/∂r = −p (p − 1) r (s + r)^{p−2}`. -/
private noncomputable def psiR (p s r : ℝ) : ℝ := -(p * (p - 1)) * r * (s + r) ^ (p - 2)

/-- The (one-sided) derivative of `ψ` along a curve `(S, R)`: `ψ_s S' + ψ_r R'`. -/
private theorem psi_hasDerivWithinAt {p : ℝ} {S R : ℝ → ℝ} {S1 R1 t : ℝ} {s : Set ℝ}
    (hS : HasDerivWithinAt S S1 s t) (hR : HasDerivWithinAt R R1 s t) (hpos : 0 < S t + R t) :
    HasDerivWithinAt (fun u => psi p (S u) (R u))
      (psiS p (S t) (R t) * S1 + psiR p (S t) (R t) * R1) s t := by
  have h := (hS.sub (hR.const_mul (p - 1))).mul
    ((hS.add hR).rpow_const (p := p - 1) (Or.inl hpos.ne'))
  have e : (S t + R t) ^ (p - 1) = (S t + R t) ^ (p - 2) * (S t + R t) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 1 - 1 = p - 2 := by ring
  unfold psi psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [e2, e]; ring

private theorem psi_hasDerivAt {p : ℝ} {S R : ℝ → ℝ} {S1 R1 t : ℝ}
    (hS : HasDerivAt S S1 t) (hR : HasDerivAt R R1 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psi p (S u) (R u))
      (psiS p (S t) (R t) * S1 + psiR p (S t) (R t) * R1) t := by
  rw [← hasDerivWithinAt_univ] at *
  exact psi_hasDerivWithinAt hS hR hpos

/-- The second derivative of `ψ` along a curve `(S, R)`:
`p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S'' − (p − 1)(S + R)(K − H))`
with `H = S'² + S S''`, `K = R'² + R R''`. -/
private theorem psi_hasDerivAt_two {p : ℝ} {S R S1 R1 : ℝ → ℝ} {S2 R2 t : ℝ}
    (hS : HasDerivAt S (S1 t) t) (hR : HasDerivAt R (R1 t) t)
    (hS1 : HasDerivAt S1 S2 t) (hR1 : HasDerivAt R1 R2 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psiS p (S u) (R u) * S1 u + psiR p (S u) (R u) * R1 u)
      (p * (S t + R t) ^ (p - 3) * (-(p - 1) * (p - 2) * R t * (S1 t + R1 t) ^ 2
        - (p - 2) * (S t + R t) ^ 2 * S2
        - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2) - (S1 t ^ 2 + S t * S2)))) t := by
  have hP := (hS.add hR).rpow_const (p := p - 2) (Or.inl hpos.ne')
  have h1 := ((hP.const_mul p).mul (hS.sub (hR.const_mul (p - 2)))).mul hS1
  have h2 := (((hR.const_mul (-(p * (p - 1)))).mul hP)).mul hR1
  have h := h1.add h2
  have e : (S t + R t) ^ (p - 2) = (S t + R t) ^ (p - 3) * (S t + R t) := by
    rw [show p - 2 = p - 3 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 2 - 1 = p - 3 := by ring
  unfold psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [e2, e]; ring

/-- The sign of the second derivative of `ψ` along a curve (`psi_hasDerivAt_two`): with
`S, R ≥ 0`, `S'' ≥ 0`, `H = S'² + S S''` and `K = R'² + R R''`, it is `≤ 0` if `p ≥ 2` and `H ≤ K`,
and `≥ 0` if `p ≤ 2` and `K ≤ H`. -/
private theorem psi_two_sign {p S R S1 R1 S2 R2 : ℝ} (hp : 1 < p) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hS2 : 0 ≤ S2) :
    ((2 ≤ p ∧ S1 ^ 2 + S * S2 ≤ R1 ^ 2 + R * R2) →
      p * (S + R) ^ (p - 3) * (-(p - 1) * (p - 2) * R * (S1 + R1) ^ 2
        - (p - 2) * (S + R) ^ 2 * S2 - (p - 1) * (S + R) * ((R1 ^ 2 + R * R2) - (S1 ^ 2 + S * S2)))
        ≤ 0) ∧
    ((p ≤ 2 ∧ R1 ^ 2 + R * R2 ≤ S1 ^ 2 + S * S2) →
      0 ≤ p * (S + R) ^ (p - 3) * (-(p - 1) * (p - 2) * R * (S1 + R1) ^ 2
        - (p - 2) * (S + R) ^ 2 * S2 - (p - 1) * (S + R) * ((R1 ^ 2 + R * R2) - (S1 ^ 2 + S * S2))))
    := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hW : 0 ≤ S + R := add_nonneg hS hR
  have hpow : 0 ≤ p * (S + R) ^ (p - 3) := mul_nonneg (by linarith) (Real.rpow_nonneg hW _)
  refine ⟨fun ⟨hp2, hHK⟩ => mul_nonpos_of_nonneg_of_nonpos hpow ?_,
    fun ⟨hp2, hHK⟩ => mul_nonneg hpow ?_⟩
  · have h2 : 0 ≤ p - 2 := by linarith
    have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) hR) (sq_nonneg (S1 + R1))
    have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S + R))) hS2
    have := mul_nonneg (mul_nonneg hp1 hW) (sub_nonneg.2 hHK)
    nlinarith
  · have h2 : 0 ≤ 2 - p := by linarith
    have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) hR) (sq_nonneg (S1 + R1))
    have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S + R))) hS2
    have := mul_nonneg (mul_nonneg hp1 hW) (sub_nonneg.2 hHK)
    nlinarith

/-! ### The concavity property of `ψ` along lines in a Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `S' (t) = ⟨x + t h, h⟩ / |x + t h|`, the derivative of `S (t) = |x + t h|` where
`x + t h ≠ 0`. -/
private noncomputable def lineD (x h : H) (t : ℝ) : ℝ := ⟪x + t • h, h⟫ / ‖x + t • h‖

/-- `S'' (t) = (|h|² − S' (t)²) / S (t)`. -/
private noncomputable def lineD2 (x h : H) (t : ℝ) : ℝ :=
  (‖h‖ ^ 2 - lineD x h t ^ 2) / ‖x + t • h‖

/-- `S (t) = |x + t h|` is smooth where `x + t h ≠ 0` (and constant if `h = 0`), with `S'' ≥ 0` and
`S'² + S S'' = |h|²`. -/
private theorem line_facts (x h : H) {t : ℝ} (ht : x + t • h ≠ 0 ∨ h = 0) :
    HasDerivAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t) t ∧
      HasDerivAt (lineD x h) (lineD2 x h t) t ∧ 0 ≤ lineD2 x h t ∧
      lineD x h t ^ 2 + ‖x + t • h‖ * lineD2 x h t = ‖h‖ ^ 2 := by
  rcases ht with ht | rfl
  · have hN : 0 < ‖x + t • h‖ := norm_pos_iff.2 ht
    have hlin : HasDerivAt (fun u : ℝ => x + u • h) h t := by
      simpa using ((hasDerivAt_id' t).smul_const h).const_add x
    have dS : HasDerivAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t) t := by
      have h3 := hlin.norm_sq.sqrt (pow_pos hN 2).ne'
      simp only [Real.sqrt_sq_eq_abs, abs_norm] at h3
      convert h3 using 1
      unfold lineD; field_simp
    have dN : HasDerivAt (fun u : ℝ => ⟪x + u • h, h⟫) (‖h‖ ^ 2) t := by
      have e : ∀ u : ℝ, ⟪x + u • h, h⟫ = ⟪x, h⟫ + u * ‖h‖ ^ 2 := fun u => by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [e]
      simpa using ((hasDerivAt_id' t).mul_const (‖h‖ ^ 2)).const_add ⟪x, h⟫
    have hcs : lineD x h t ^ 2 ≤ ‖h‖ ^ 2 := by
      unfold lineD
      rw [div_pow, div_le_iff₀ (by positivity)]
      have h1 := abs_real_inner_le_norm (x + t • h) h
      have h2 : ⟪x + t • h, h⟫ ^ 2 ≤ (‖x + t • h‖ * ‖h‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith
    refine ⟨dS, ?_, div_nonneg (sub_nonneg.2 hcs) hN.le, ?_⟩
    · convert dN.div dS hN.ne' using 1
      · funext u; simp [lineD]
      · unfold lineD2 lineD
        field_simp
    · unfold lineD2; field_simp; ring
  · have e1 : (fun u : ℝ => ‖x + u • (0 : H)‖) = fun _ => ‖x‖ := by funext u; simp
    have e2 : lineD x (0 : H) = fun _ => 0 := by funext u; simp [lineD]
    have e3 : lineD2 x (0 : H) t = 0 := by simp [lineD2, lineD]
    rw [e1, e2, e3]
    exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _, le_rfl, by simp⟩

/-- `G (t) = ψ (|x + t h|, |y + t k|)`, `ψ` along the line through `(x, y)` with direction
`(h, k)`. -/
private noncomputable def psiLine (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psi p ‖x + t • h‖ ‖y + t • k‖

/-- `G' (t) = ψ_s S' + ψ_r R'`, the derivative of `G` where `x + t h ≠ 0` and `y + t k ≠ 0`. -/
private noncomputable def psiLineD (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psiS p ‖x + t • h‖ ‖y + t • k‖ * lineD x h t + psiR p ‖x + t • h‖ ‖y + t • k‖ * lineD y k t

/-- **(1.14)** at one point: where `x + t h ≠ 0` (or `h = 0`) and `y + t k ≠ 0` (or `k = 0`), `G`
is twice differentiable, with `G'' ≤ 0` if `p ≥ 2`, `|h| ≤ |k|`, and `G'' ≥ 0` if `p ≤ 2`,
`|k| ≤ |h|` (`psi_hasDerivAt_two`, `psi_two_sign`, with `H = |h|²`, `K = |k|²`). -/
private theorem psi_line_smooth {p : ℝ} (hp : 1 < p) (x y h k : H) {t : ℝ}
    (hx : x + t • h ≠ 0 ∨ h = 0) (hy : y + t • k ≠ 0 ∨ k = 0)
    (hW : 0 < ‖x + t • h‖ + ‖y + t • k‖) :
    HasDerivAt (psiLine p x y h k) (psiLineD p x y h k t) t ∧
      ∃ c, HasDerivAt (psiLineD p x y h k) c t ∧ ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → c ≤ 0) ∧
        ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → 0 ≤ c) := by
  obtain ⟨dS, dS1, hS2, hH⟩ := line_facts x h hx
  obtain ⟨dR, dR1, -, hK⟩ := line_facts y k hy
  have hsign := psi_two_sign hp (norm_nonneg (x + t • h)) (norm_nonneg (y + t • k)) hS2
    (S1 := lineD x h t) (R1 := lineD y k t) (R2 := lineD2 y k t)
  refine ⟨psi_hasDerivAt dS dR hW, _, psi_hasDerivAt_two (p := p) dS dR dS1 dR1 hW,
    fun ⟨hp2, hhk⟩ => hsign.1 ⟨hp2, ?_⟩, fun ⟨hp2, hhk⟩ => hsign.2 ⟨hp2, ?_⟩⟩
  · rw [hH, hK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2
  · rw [hH, hK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2

/-- **(1.13), (1.14)**: if `x + t h ≠ 0` and `y + t k ≠ 0` for every `t`,
`G (t) = ψ (|x + t h|, |y + t k|)` is twice differentiable on `ℝ` (`psi_line_smooth`), with
`G'' ≤ 0` if `p ≥ 2` and `|h| ≤ |k|` and `G'' ≥ 0` if `p ≤ 2` and `|k| ≤ |h|`: `G` is concave,
resp. convex, on `ℝ`. -/
private theorem psi_line_of_ne {p : ℝ} (hp : 1 < p) (x y h k : H)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → ConcaveOn ℝ univ (psiLine p x y h k)) ∧
      ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → ConvexOn ℝ univ (psiLine p x y h k)) := by
  have hcont : Continuous (psiLine p x y h k) := by
    have h1 : Continuous fun t : ℝ => ‖x + t • h‖ := by fun_prop
    have h2 : Continuous fun t : ℝ => ‖y + t • k‖ := by fun_prop
    unfold psiLine psi
    exact (h1.sub (h2.const_mul _)).mul ((h1.add h2).rpow_const fun _ => Or.inr (by linarith))
  have hs := fun t : ℝ => psi_line_smooth hp x y h k (Or.inl (hx t)) (Or.inl (hy t))
    (add_pos_of_pos_of_nonneg (norm_pos_iff.2 (hx t)) (norm_nonneg _))
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := psiLineD p x y h k)
      (f'' := deriv (psiLineD p x y h k)) convex_univ hcont.continuousOn
      (fun t _ => (hs t).1.hasDerivWithinAt) (fun t _ => ?_) (fun t _ => ?_)
    · obtain ⟨c, hc, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc.hasDerivWithinAt
    · obtain ⟨c, hc, hc0, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc0 hA
  · refine convexOn_of_hasDerivWithinAt2_nonneg (f' := psiLineD p x y h k)
      (f'' := deriv (psiLineD p x y h k)) convex_univ hcont.continuousOn
      (fun t _ => (hs t).1.hasDerivWithinAt) (fun t _ => ?_) (fun t _ => ?_)
    · obtain ⟨c, hc, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc.hasDerivWithinAt
    · obtain ⟨c, hc, -, hc0⟩ := (hs t).2
      rw [hc.deriv]; exact hc0 hB

/-- **(1.13)** for `ψ`: if `x + t h ≠ 0` and `y + t k ≠ 0` for every `t`, then
`G (1) ≤ G (0) + G' (0)` for `p ≥ 2`, `|h| ≤ |k|` (`G` concave), and the reverse for `p ≤ 2`,
`|k| ≤ |h|` (`G` convex), where
`G' (0) = ψ_s (|x|, |y|) ⟨x, h⟩ / |x| + ψ_r (|x|, |y|) ⟨y, k⟩ / |y|` (`psiLineD … 0`). -/
private theorem psi_zigzag_of_ne {p : ℝ} (hp : 1 < p) (x y h k : H)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) →
      psi p ‖x + h‖ ‖y + k‖ ≤ psi p ‖x‖ ‖y‖ + psiLineD p x y h k 0) ∧
    ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) →
      psi p ‖x‖ ‖y‖ + psiLineD p x y h k 0 ≤ psi p ‖x + h‖ ‖y + k‖) := by
  have e0 : psiLine p x y h k 0 = psi p ‖x‖ ‖y‖ := by simp [psiLine]
  have e1 : psiLine p x y h k 1 = psi p ‖x + h‖ ‖y + k‖ := by simp [psiLine]
  have hd := (psi_line_smooth hp x y h k (Or.inl (hx 0)) (Or.inl (hy 0))
    (add_pos_of_pos_of_nonneg (norm_pos_iff.2 (hx 0)) (norm_nonneg _))).1
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · have := ((psi_line_of_ne hp x y h k hx hy).1 hA).slope_le_of_hasDerivAt (mem_univ 0)
      (mem_univ 1) zero_lt_one hd
    rw [slope_def_field, e0, e1, sub_zero, div_one] at this
    linarith
  · have := ((psi_line_of_ne hp x y h k hx hy).2 hB).le_slope_of_hasDerivAt (mem_univ 0)
      (mem_univ 1) zero_lt_one hd
    rw [slope_def_field, e0, e1, sub_zero, div_one] at this
    linarith

end Hilbert

/-! ### Burkholder's function (1.6) -/

/-- **Burkholder's function** (Burkholder 1988, (1.6)), as a function of `s = |x|`, `r = |y|`:
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, `p* = max (p, p/(p − 1))`.
Here `x` is the position of the subordinate martingale and `y` that of the dominating one. -/
noncomputable def burkholderU (p s r : ℝ) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (s - (max p (p / (p - 1)) - 1) * r) *
    (s + r) ^ (p - 1)

private theorem max_eq_A {p : ℝ} (hp : 2 ≤ p) : max p (p / (p - 1)) = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

private theorem max_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) : max p (p / (p - 1)) = p / (p - 1) :=
  max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)

private theorem U_eq_A {p : ℝ} (hp : 2 ≤ p) (s r : ℝ) :
    burkholderU p s r = p * (1 - 1 / p) ^ (p - 1) * psi p s r := by
  unfold burkholderU psi; rw [max_eq_A hp]; ring

private theorem U_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (s r : ℝ) :
    burkholderU p s r = -(p * (1 / p) ^ (p - 1) / (p - 1)) * psi p r s := by
  unfold burkholderU psi; rw [max_eq_B hp1 hp]
  have hp0 : p - 1 ≠ 0 := by linarith
  have h1 : 1 - 1 / (p / (p - 1)) = 1 / p := by field_simp; ring
  rw [h1, add_comm r s]; field_simp; ring

/-! ### The elementary inequality (1.11) -/

/-- `log φ (p) = (p − 1) log (p − 1) − (p − 2) log p`, the logarithm of
`φ (p) = (p − 1)^{p−1} / p^{p−2}` (Burkholder's (1.11)); `log φ (1) = 0` (`0 · log 0 = 0`). -/
private noncomputable def logPhi (p : ℝ) : ℝ := (p - 1) * Real.log (p - 1) - (p - 2) * Real.log p

private theorem logPhi_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt logPhi (Real.log (p - 1) + 1 - (Real.log p + (p - 2) / p)) p := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 p := (hasDerivAt_id' p).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => x - 2) 1 p := (hasDerivAt_id' p).sub_const 2
  have hl1 := h1.log (by linarith : p - 1 ≠ 0)
  have hl2 := Real.hasDerivAt_log (by linarith : p ≠ 0)
  have h := (h1.mul hl1).sub (h2.mul hl2)
  change HasDerivAt (fun x => (x - 1) * Real.log (x - 1) - (x - 2) * Real.log x) _ p
  convert h using 1
  have : p - 1 ≠ 0 := by linarith
  field_simp

/-- `(log φ)'' (p) = 1/(p − 1) − 1/p − 2/p² = (2 − p) / (p² (p − 1))`. -/
private theorem logPhi_deriv_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      ((2 - p) / (p ^ 2 * (p - 1))) p := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 p := (hasDerivAt_id' p).sub_const 1
  have hl1 := h1.log (by linarith : p - 1 ≠ 0)
  have hl2 := Real.hasDerivAt_log (by linarith : p ≠ 0)
  have hq := ((hasDerivAt_id' p).sub_const 2).div (hasDerivAt_id' p) (by linarith : p ≠ 0)
  have h := (hl1.add_const 1).sub (hl2.add hq)
  convert h using 1
  have : p - 1 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  field_simp
  ring

private theorem logPhi_continuousOn : ContinuousOn logPhi (Ici 1) := by
  have h1 : Continuous fun x : ℝ => (x - 1) * Real.log (x - 1) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have h2 : ContinuousOn (fun x : ℝ => (x - 2) * Real.log x) (Ici 1) :=
    (continuous_id.sub continuous_const).continuousOn.mul (Real.continuousOn_log.mono
      fun x hx => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ici.1 hx])
  exact h1.continuousOn.sub h2

private theorem logPhi_two : logPhi 2 = 0 := by norm_num [logPhi]

/-- `log φ` is convex on `[1, 2]` and vanishes at both ends, so `log φ ≤ 0` there. -/
private theorem logPhi_nonpos {p : ℝ} (hp1 : 1 ≤ p) (hp : p ≤ 2) : logPhi p ≤ 0 := by
  have hconv : ConvexOn ℝ (Icc 1 2) logPhi := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      (f'' := fun x => (2 - x) / (x ^ 2 * (x - 1))) (convex_Icc 1 2)
      (logPhi_continuousOn.mono Icc_subset_Ici_self) (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact (logPhi_hasDerivAt hx.1).hasDerivWithinAt
    · exact (logPhi_deriv_hasDerivAt hx.1).hasDerivWithinAt
    · exact div_nonneg (by linarith [hx.2]) (mul_nonneg (sq_nonneg _) (by linarith [hx.1]))
  have h := hconv.le_on_segment (x := 1) (y := 2) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
    (by rw [segment_eq_Icc (by norm_num)]; exact ⟨hp1, hp⟩)
  have e1 : logPhi 1 = 0 := by simp [logPhi]
  rwa [e1, logPhi_two, max_self] at h

/-- `log φ (p) ≥ log p − 1`, so `log φ → ∞`: `log φ (p) = log p − (p − 1) log (p / (p − 1))` and
`log (p / (p − 1)) ≤ 1 / (p − 1)`. -/
private theorem logPhi_ge {p : ℝ} (hp : 1 < p) : Real.log p - 1 ≤ logPhi p := by
  have hp1 : 0 < p - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p) hp1)
  rw [Real.log_div (by linarith) hp1.ne'] at h
  have h' : (p - 1) * (Real.log p - Real.log (p - 1)) ≤ 1 :=
    calc (p - 1) * (Real.log p - Real.log (p - 1)) ≤ (p - 1) * (p / (p - 1) - 1) :=
          mul_le_mul_of_nonneg_left h hp1.le
      _ = 1 := by field_simp; ring
  unfold logPhi
  nlinarith [h']

/-- `log φ` is concave on `[2, ∞)`, vanishes at `2` and tends to `∞`, so `log φ ≥ 0` there. -/
private theorem logPhi_nonneg {p : ℝ} (hp : 2 ≤ p) : 0 ≤ logPhi p := by
  have hconc : ConcaveOn ℝ (Ici 2) logPhi := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      (f'' := fun x => (2 - x) / (x ^ 2 * (x - 1))) (convex_Ici 2)
      (logPhi_continuousOn.mono (Ici_subset_Ici.2 (by norm_num))) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx <;> have hx' := mem_Ioi.1 hx
    · exact (logPhi_hasDerivAt (by linarith)).hasDerivWithinAt
    · exact (logPhi_deriv_hasDerivAt (by linarith)).hasDerivWithinAt
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith)
        (mul_nonneg (sq_nonneg _) (by linarith))
  -- a point `p₂ ≥ p` with `log φ (p₂) ≥ 0`
  set p₂ := max p (Real.exp 1)
  have hp₂ : p ≤ p₂ := le_max_left _ _
  have h2 : 0 ≤ logPhi p₂ := by
    have h := logPhi_ge (p := p₂) (by linarith)
    have : 1 ≤ Real.log p₂ := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (le_max_right _ _)
    linarith
  have h := hconc.ge_on_segment (x := 2) (y := p₂) self_mem_Ici (mem_Ici.2 (hp.trans hp₂))
    (by rw [segment_eq_Icc (hp.trans hp₂)]; exact ⟨hp, hp₂⟩)
  rw [logPhi_two] at h
  exact (le_min le_rfl h2).trans h

private theorem phi_eq_exp {p : ℝ} (hp : 1 < p) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) = Real.exp (logPhi p) := by
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith), ← Real.exp_sub,
    logPhi]
  ring_nf

/-- **(1.11)**, `1 < p ≤ 2`: `(p − 1)^{p−1} / p^{p−2} ≤ 1`. -/
private theorem phi_le_one {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) ≤ 1 := by
  rw [phi_eq_exp hp1, Real.exp_le_one_iff]; exact logPhi_nonpos hp1.le hp

/-- **(1.11)**, `p ≥ 2`: `(p − 1)^{p−1} / p^{p−2} ≥ 1`. -/
private theorem one_le_phi {p : ℝ} (hp : 2 ≤ p) : 1 ≤ (p - 1) ^ (p - 1) / p ^ (p - 2) := by
  rw [phi_eq_exp (by linarith), Real.one_le_exp_iff]; exact logPhi_nonneg hp

/-! ### The majorization `v ≤ u` (1.10) -/

/-- Burkholder's `F (t) = α_p (1 − P t) − (1 − t)^p + (P − 1)^p t^p`, `α_p = p (1 − 1/P)^{p−1}`:
for `P = p*`, `U − V` on `|x| + |y| = 1`, as a function of the norm `t` of the dominating
martingale's position. -/
private noncomputable def bF (p P t : ℝ) : ℝ :=
  p * (1 - 1 / P) ^ (p - 1) * (1 - P * t) - (1 - t) ^ p + (P - 1) ^ p * t ^ p

/-- `F'`. -/
private noncomputable def bF1 (p P t : ℝ) : ℝ :=
  -(p * (1 - 1 / P) ^ (p - 1) * P) + p * (1 - t) ^ (p - 1) + p * (P - 1) ^ p * t ^ (p - 1)

/-- `F''`. -/
private noncomputable def bF2 (p P t : ℝ) : ℝ :=
  -(p * (p - 1) * (1 - t) ^ (p - 2)) + p * (p - 1) * (P - 1) ^ p * t ^ (p - 2)

private theorem bF_hasDerivAt (p P : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (bF p P) (bF1 p P t) t ∧ HasDerivAt (bF1 p P) (bF2 p P t) t := by
  have hl : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
    simpa using (hasDerivAt_id' t).const_sub 1
  have h1t : 1 - t ≠ 0 := by linarith
  constructor
  · have hA := (((hasDerivAt_id' t).const_mul P).const_sub 1).const_mul
      (p * (1 - 1 / P) ^ (p - 1))
    have hB := hl.rpow_const (p := p) (Or.inl h1t)
    have hC := (Real.hasDerivAt_rpow_const (p := p) (Or.inl ht0.ne')).const_mul ((P - 1) ^ p)
    change HasDerivAt (fun u => p * (1 - 1 / P) ^ (p - 1) * (1 - P * u) - (1 - u) ^ p +
      (P - 1) ^ p * u ^ p) _ t
    convert (hA.sub hB).add hC using 1
    unfold bF1; ring
  · have hB := hl.rpow_const (p := p - 1) (Or.inl h1t)
    have hC := (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht0.ne')).const_mul
      (p * (P - 1) ^ p)
    change HasDerivAt (fun u => -(p * (1 - 1 / P) ^ (p - 1) * P) + p * (1 - u) ^ (p - 1) +
      p * (P - 1) ^ p * u ^ (p - 1)) _ t
    convert ((hB.const_mul p).const_add (-(p * (1 - 1 / P) ^ (p - 1) * P))).add hC using 1
    rw [show p - 1 - 1 = p - 2 by ring]
    unfold bF2; ring

private theorem continuous_bF {p : ℝ} (hp : 0 < p) (P : ℝ) : Continuous (bF p P) := by
  unfold bF
  exact ((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).sub
    ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hp.le)).add
    (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hp.le))

/-- `F (1/P) = F' (1/P) = 0`. -/
private theorem bF_crit {p P : ℝ} (hP : 1 < P) : bF p P (1 / P) = 0 ∧ bF1 p P (1 / P) = 0 := by
  have hP0 : 0 < P := by linarith
  have hβ : 0 ≤ P - 1 := by linarith
  have e : 1 - 1 / P = (P - 1) * (1 / P) := by field_simp
  have hpow : ∀ a : ℝ, (P - 1) ^ a * (1 / P) ^ a = (1 - 1 / P) ^ a := fun a => by
    rw [e, Real.mul_rpow hβ (by positivity)]
  have e0 : 1 - P * (1 / P) = 0 := by field_simp; ring
  constructor
  · unfold bF
    rw [e0, hpow p]; ring
  · have hPp : (P - 1) ^ p = (P - 1) * (P - 1) ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    unfold bF1
    rw [hPp]
    linear_combination (p * (P - 1)) * hpow (p - 1)

/-- `F'' (t) = p (p − 1) ((d t)^{p−2} − (1 − t)^{p−2})` with `d = (P − 1)^{p/(p−2)}`
(`p ≠ 2`). -/
private theorem bF2_eq {p P t : ℝ} (hp2 : p ≠ 2) (hP : 1 < P) (ht : 0 < t) :
    bF2 p P t = p * (p - 1) * (((P - 1) ^ (p / (p - 2)) * t) ^ (p - 2) - (1 - t) ^ (p - 2)) := by
  have hβ : 0 ≤ P - 1 := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg hβ _) ht.le, ← Real.rpow_mul hβ,
    div_mul_cancel₀ _ (sub_ne_zero.2 hp2)]
  unfold bF2; ring

/-- A convex function on `[a, b]` with `F (c) = F' (c) = 0` at a point `c ∈ [a, b]` is `≥ 0` on
`[a, b]` (it lies above its tangent at `c`). -/
private theorem nonneg_of_convexOn_tangent {F : ℝ → ℝ} {a b c : ℝ} (hF : ConvexOn ℝ (Icc a b) F)
    (hc : c ∈ Icc a b) (hd : HasDerivAt F 0 c) (h0 : F c = 0) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ F t := by
  rcases lt_trichotomy t c with htc | rfl | htc
  · have := hF.slope_le_of_hasDerivAt ht hc htc hd
    rw [slope_def_field, h0, div_le_iff₀ (sub_pos.2 htc)] at this
    linarith
  · rw [h0]
  · have := hF.le_slope_of_hasDerivAt hc ht htc hd
    rw [slope_def_field, h0, le_div_iff₀ (sub_pos.2 htc)] at this
    linarith

/-- A concave function on `[a, b]` that is `≥ 0` at `a` and at `b` is `≥ 0` on `[a, b]`. -/
private theorem nonneg_of_concaveOn {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ConcaveOn ℝ (Icc a b) F) (ha : 0 ≤ F a) (hb : 0 ≤ F b) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ F t :=
  (le_min ha hb).trans (hF.ge_on_segment ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ (by rwa [segment_eq_Icc hab]))

/-- `F` is convex (resp. concave) on a subinterval `[a, b]` of `[0, 1]` on whose interior
`F'' ≥ 0` (resp. `≤ 0`). -/
private theorem bF_convexOn {p P a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : b ≤ 1)
    (h2 : ∀ t, a < t → t < b → 0 ≤ bF2 p P t) : ConvexOn ℝ (Icc a b) (bF p P) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := bF1 p P) (f'' := bF2 p P) (convex_Icc a b)
    (continuous_bF hp P).continuousOn (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) <;>
    rw [interior_Icc] at ht
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).1.hasDerivWithinAt
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).2.hasDerivWithinAt
  · exact h2 t ht.1 ht.2

private theorem bF_concaveOn {p P a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : b ≤ 1)
    (h2 : ∀ t, a < t → t < b → bF2 p P t ≤ 0) : ConcaveOn ℝ (Icc a b) (bF p P) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := bF1 p P) (f'' := bF2 p P) (convex_Icc a b)
    (continuous_bF hp P).continuousOn (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) <;>
    rw [interior_Icc] at ht
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).1.hasDerivWithinAt
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).2.hasDerivWithinAt
  · exact h2 t ht.1 ht.2

/-- `α_p = p (1 − 1/p)^{p−1} = (p − 1)^{p−1} / p^{p−2}`. -/
private theorem alpha_eq_phi {p : ℝ} (hp : 1 < p) :
    p * (1 - 1 / p) ^ (p - 1) = (p - 1) ^ (p - 1) / p ^ (p - 2) := by
  have hp0 : 0 < p := by linarith
  have e : 1 - 1 / p = (p - 1) / p := by field_simp
  have hpp : p ^ (p - 1) = p ^ (p - 2) * p := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hp0.ne']
  have hp2 : p ^ (p - 2) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [e, Real.div_rpow (by linarith) hp0.le, hpp]
  field_simp

/-- **`F ≥ 0` on `[0, 1]`** (Burkholder 1988, proof of (1.10)). If `p = 2`, `F ≡ 0`. With
`d = (p* − 1)^{p/(p−2)}` and `s₀ = 1/(1 + d)` (Burkholder asserts that such an `s₀` exists; this
value is read off from `F''`, `bF2_eq`): if `p > 2`, `F` is concave on `[0, s₀]` and convex on
`[s₀, 1]`, `s₀ ≤ 1/p*`; `F (1/p*) = F' (1/p*) = 0` gives `F ≥ 0` on `[s₀, 1]`, and `F (0) ≥ 0` by
(1.11) gives it on `[0, s₀]`. If `p < 2`, `F` is convex on `[0, s₀]`, `s₀ ≥ 1/p*`, and concave on
`[s₀, 1]`, and `F (1) ≥ 0` by (1.11). -/
private theorem bF_nonneg {p : ℝ} (hp : 1 < p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bF p (max p (p / (p - 1))) t := by
  have hp0 : 0 < p := by linarith
  set P := max p (p / (p - 1)) with hPdef
  have hP : 1 < P := lt_of_lt_of_le hp (le_max_left _ _)
  have hβ : 0 < P - 1 := by linarith
  have hpp : 0 < p * (p - 1) := mul_pos hp0 (by linarith)
  obtain ⟨hcrit, hcrit1⟩ := bF_crit (p := p) hP
  have hd1 : HasDerivAt (bF p P) 0 (1 / P) := by
    rw [← hcrit1]
    exact (bF_hasDerivAt p P (by positivity) ((div_lt_one (by linarith)).2 hP)).1
  have hcP : 1 / P ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, (div_lt_one (by linarith)).2 hP⟩
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · -- `1 < p < 2`: `P = p / (p − 1)`
    have hPe : P = p / (p - 1) := max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)
    set d := (P - 1) ^ (p / (p - 2)) with hd
    have hd0 : 0 < d := Real.rpow_pos_of_pos hβ _
    have hβ1 : 1 ≤ P - 1 := by
      rw [hPe, le_sub_iff_add_le, le_div_iff₀ (by linarith)]; linarith
    have hd1' : d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1
      (div_nonpos_of_nonneg_of_nonpos hp0.le (by linarith))
    set s₀ := 1 / (1 + d)
    have hs₀1 : s₀ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hPs₀ : 1 / P ≤ s₀ := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hdt : ∀ u, 0 < u → (u ≤ s₀ ↔ d * u ≤ 1 - u) := fun u hu => by
      rw [le_div_iff₀ (by linarith)]; constructor <;> intro h <;> linarith
    -- convex on `[0, s₀]`, concave on `[s₀, 1]`
    have hconv : ConvexOn ℝ (Icc 0 s₀) (bF p P) := bF_convexOn hp0 le_rfl hs₀1 fun u hu0 hu1 => by
      rw [bF2_eq hp2.ne hP hu0]
      refine mul_nonneg hpp.le (sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos (by positivity)
        ((hdt u hu0).1 hu1.le) (by linarith)))
    have hconc : ConcaveOn ℝ (Icc s₀ 1) (bF p P) := bF_concaveOn hp0 (by positivity) le_rfl
      fun u hu0 hu1 => by
        have hu : 0 < u := lt_of_le_of_lt (by positivity) hu0
        rw [bF2_eq hp2.ne hP hu]
        have : 1 - u ≤ d * u := by
          by_contra hc; exact absurd ((hdt u hu).2 (by linarith)) (not_le.2 hu0)
        exact mul_nonpos_of_nonneg_of_nonpos hpp.le (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos
          (by linarith) this (by linarith)))
    have hleft : ∀ u ∈ Icc 0 s₀, 0 ≤ bF p P u := fun u hu =>
      nonneg_of_convexOn_tangent hconv ⟨hcP.1.le, hPs₀⟩ hd1 hcrit hu
    -- `F (1) = (P − 1) ((P − 1)^{p−1} − α_p) ≥ 0` by (1.11)
    have hF1 : 0 ≤ bF p P 1 := by
      have hφ := phi_le_one hp hp2.le
      have hα : p * (1 - 1 / P) ^ (p - 1) = 1 / p ^ (p - 2) := by
        rw [hPe, show 1 - 1 / (p / (p - 1)) = 1 / p by field_simp; ring,
          Real.div_rpow zero_le_one hp0.le, Real.one_rpow,
          show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hp0.ne']
        field_simp
      have hb : (P - 1) ^ (p - 1) = 1 / (p - 1) ^ (p - 1) := by
        rw [hPe, show p / (p - 1) - 1 = 1 / (p - 1) by field_simp; ring,
          Real.div_rpow zero_le_one (by linarith), Real.one_rpow]
      have hPp : (P - 1) ^ p = (P - 1) * (P - 1) ^ (p - 1) := by
        conv_lhs => rw [show p = 1 + (p - 1) by ring]
        rw [Real.rpow_add hβ, Real.rpow_one]
      have hq : 1 / p ^ (p - 2) ≤ 1 / (p - 1) ^ (p - 1) := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hp0 _)] at hφ
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _) hφ |>.trans_eq'
          (by rw [one_mul])
      unfold bF
      rw [hα, hPp, hb, sub_self, Real.zero_rpow hp0.ne', Real.one_rpow]
      nlinarith [hq, hβ]
    rcases le_total t s₀ with hts | hts
    · exact hleft t ⟨ht0, hts⟩
    · exact nonneg_of_concaveOn hs₀1 hconc (hleft s₀ ⟨by positivity, le_rfl⟩) hF1 ⟨hts, ht1⟩
  · -- `p = 2`: `F ≡ 0`
    have hP2 : P = 2 := by rw [hPdef]; norm_num
    rw [hP2]
    unfold bF
    norm_num [Real.rpow_two]
    ring_nf
    exact le_rfl
  · -- `p > 2`: `P = p`
    have hPe : P = p := max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)
    set d := (P - 1) ^ (p / (p - 2)) with hd
    have hd0 : 0 < d := Real.rpow_pos_of_pos hβ _
    have hβ1 : 1 < P - 1 := by rw [hPe]; linarith
    have hdβ : P - 1 < d := by
      conv_lhs => rw [← Real.rpow_one (P - 1)]
      exact Real.rpow_lt_rpow_of_exponent_lt hβ1 (by rw [one_lt_div (by linarith)]; linarith)
    set s₀ := 1 / (1 + d)
    have hs₀0 : 0 ≤ s₀ := by positivity
    have hs₀P : s₀ ≤ 1 / P := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hdt : ∀ u, 0 < u → (u ≤ s₀ ↔ d * u ≤ 1 - u) := fun u hu => by
      rw [le_div_iff₀ (by linarith)]; constructor <;> intro h <;> linarith
    -- concave on `[0, s₀]`, convex on `[s₀, 1]`
    have hconc : ConcaveOn ℝ (Icc 0 s₀) (bF p P) := bF_concaveOn hp0 le_rfl
      (hs₀P.trans hcP.2.le) fun u hu0 hu1 => by
        rw [bF2_eq hp2.ne' hP hu0]
        exact mul_nonpos_of_nonneg_of_nonpos hpp.le (sub_nonpos.2 (Real.rpow_le_rpow
          (by positivity) ((hdt u hu0).1 hu1.le) (by linarith)))
    have hconv : ConvexOn ℝ (Icc s₀ 1) (bF p P) := bF_convexOn hp0 hs₀0 le_rfl fun u hu0 hu1 => by
      have hu : 0 < u := lt_of_le_of_lt hs₀0 hu0
      rw [bF2_eq hp2.ne' hP hu]
      have : 1 - u ≤ d * u := by
        by_contra hc; exact absurd ((hdt u hu).2 (by linarith)) (not_le.2 hu0)
      exact mul_nonneg hpp.le (sub_nonneg.2 (Real.rpow_le_rpow (by linarith) this (by linarith)))
    have hright : ∀ u ∈ Icc s₀ 1, 0 ≤ bF p P u := fun u hu =>
      nonneg_of_convexOn_tangent hconv ⟨hs₀P, hcP.2.le⟩ hd1 hcrit hu
    -- `F (0) = α_p − 1 ≥ 0` by (1.11)
    have hF0 : 0 ≤ bF p P 0 := by
      have hφ := one_le_phi hp2.le
      unfold bF
      rw [hPe, alpha_eq_phi hp, Real.zero_rpow hp0.ne', sub_zero, Real.one_rpow]
      linarith
    rcases le_total t s₀ with hts | hts
    · exact nonneg_of_concaveOn hs₀0 hconc hF0 (hright s₀ ⟨le_rfl, (hs₀P.trans hcP.2.le)⟩)
        ⟨ht0, hts⟩
    · exact hright t ⟨hts, ht1⟩

/-- **Majorization** (Burkholder 1988, (1.10)): `V ≤ U`, that is
`|x|^p − (p* − 1)^p |y|^p ≤ U (x, y)`, with `s = |x|` (subordinate), `r = |y|` (dominating). If
`s + r = 0` both sides vanish; otherwise, by homogeneity,
`U (s, r) − V (s, r) = (s + r)^p F (r / (s + r)) ≥ 0` (`bF_nonneg`). -/
theorem burkholderU_ge {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p ≤ burkholderU p s r := by
  have hp0 : 0 < p := by linarith
  rcases (add_nonneg hs hr).eq_or_lt with hw | hw
  · have hs0 : s = 0 := by linarith
    have hr0 : r = 0 := by linarith
    subst hs0 hr0
    simp [burkholderU, Real.zero_rpow hp0.ne']
  · have ht0 : 0 ≤ r / (s + r) := div_nonneg hr hw.le
    have ht1 : r / (s + r) ≤ 1 := (div_le_one hw).2 (by linarith)
    have hF := bF_nonneg hp ht0 ht1
    have hwp : 0 < (s + r) ^ p := Real.rpow_pos_of_pos hw p
    have key : burkholderU p s r - (s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p) =
        (s + r) ^ p * bF p (max p (p / (p - 1))) (r / (s + r)) := by
      unfold burkholderU bF
      have e1 : 1 - r / (s + r) = s / (s + r) := by field_simp; ring
      rw [e1, Real.div_rpow hs hw.le, Real.div_rpow hr hw.le, Real.rpow_sub_one hw.ne']
      field_simp
      ring
    nlinarith [mul_nonneg hwp.le hF]

/-! ### The concavity of `U` along lines: (1.12)–(1.14) and Remark 1.2 -/

/-- `α_p = p (1 − 1/p)^{p−1} ≥ 0`. -/
private theorem alpha_nonneg {p : ℝ} (hp : 1 < p) : 0 ≤ p * (1 - 1 / p) ^ (p - 1) := by
  have h : 0 ≤ 1 - 1 / p := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact mul_nonneg (by linarith) (Real.rpow_nonneg h _)

/-- Burkholder's `ψ`, the gradient of `U` in the subordinate variable, as a multiple of `x`:
`∇_x U (x, y) = gradX (|x|, |y|) x`,
`gradX (s, r) = α_p (p s + (p + p* − p p*) r) (s + r)^{p−2} / s`. -/
private noncomputable def gradX (p s r : ℝ) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) *
    (p * s + (p + max p (p / (p - 1)) - p * max p (p / (p - 1))) * r) * (s + r) ^ (p - 2) / s

/-- Burkholder's `φ`, the gradient of `U` in the dominating variable, as a multiple of `y`:
`∇_y U (x, y) = gradY (|x|, |y|) y`,
`gradY (s, r) = α_p ((p − p*) s − p (p* − 1) r) (s + r)^{p−2} / r`. -/
private noncomputable def gradY (p s r : ℝ) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) *
    ((p - max p (p / (p - 1))) * s - p * (max p (p / (p - 1)) - 1) * r) * (s + r) ^ (p - 2) / r

/-- **(1.12)**: if `x + t h ≠ 0` and `y + t k ≠ 0` for every `t` and `|h| ≤ |k|`,
`U (x + h, y + k) ≤ U (x, y) + gradX ⟨x, h⟩ + gradY ⟨y, k⟩`. For `p ≥ 2`, `U = α_p ψ (|x|, |y|)`;
for `p ≤ 2`, `U = −α_p (p − 1)⁻¹ ψ (|y|, |x|)`
(`(p − 1) u = −α_p (|x| − (p − 1)|y|)(|x| + |y|)^{p−1}` in Burkholder's notation); (1.13) for
`ψ` (`psi_zigzag_of_ne`), and `G' (0)` is the linear term. -/
private theorem burkholderU_zigzag_of_ne {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {p : ℝ} (hp : 1 < p) (x y h k : H) (hhk : ‖h‖ ≤ ‖k‖)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    burkholderU p ‖x + h‖ ‖y + k‖ ≤
      burkholderU p ‖x‖ ‖y‖ + gradX p ‖x‖ ‖y‖ * ⟪x, h⟫ + gradY p ‖x‖ ‖y‖ * ⟪y, k⟫ := by
  have hs : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hx 0)
  have hr : 0 < ‖y‖ := norm_pos_iff.2 (by simpa using hy 0)
  have hD : ∀ (a b : H) (u v : H), psiLineD p a b u v 0 =
      psiS p ‖a‖ ‖b‖ * (⟪a, u⟫ / ‖a‖) + psiR p ‖a‖ ‖b‖ * (⟪b, v⟫ / ‖b‖) := fun a b u v => by
    simp [psiLineD, lineD]
  rcases le_total 2 p with h2 | h2
  · have hz := (psi_zigzag_of_ne hp x y h k hx hy).1 ⟨h2, hhk⟩
    rw [hD] at hz
    have hα : 0 ≤ p * (1 - 1 / p) ^ (p - 1) := alpha_nonneg hp
    rw [U_eq_A h2, U_eq_A h2]
    have e : p * (1 - 1 / p) ^ (p - 1) * (psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) +
        psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖)) = gradX p ‖x‖ ‖y‖ * ⟪x, h⟫ + gradY p ‖x‖ ‖y‖ * ⟪y, k⟫ := by
      unfold gradX gradY psiS psiR
      rw [max_eq_A h2]
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hz hα]
  · have hz := (psi_zigzag_of_ne hp y x k h hy hx).2 ⟨h2, hhk⟩
    rw [hD] at hz
    set c := p * (1 / p) ^ (p - 1) / (p - 1) with hc
    have hc0 : 0 ≤ c := div_nonneg (by positivity) (by linarith)
    rw [U_eq_B hp h2, U_eq_B hp h2, ← hc]
    have hp1 : p - 1 ≠ 0 := by linarith
    have e : -c * (psiS p ‖y‖ ‖x‖ * (⟪y, k⟫ / ‖y‖) + psiR p ‖y‖ ‖x‖ * (⟪x, h⟫ / ‖x‖)) =
        gradX p ‖x‖ ‖y‖ * ⟪x, h⟫ + gradY p ‖x‖ ‖y‖ * ⟪y, k⟫ := by
      unfold gradX gradY psiS psiR
      rw [max_eq_B hp h2, hc, show 1 - 1 / (p / (p - 1)) = 1 / p by field_simp; ring,
        add_comm ‖y‖ ‖x‖]
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hz hc0]

/-- **(1.13), (1.14)** for `U`: if `x + t h ≠ 0`, `y + t k ≠ 0` for every `t` and `|h| ≤ |k|`,
`t ↦ U (x + t h, y + t k)` is concave on `ℝ` (`psi_line_of_ne`). -/
private theorem burkholderU_concaveOn_line_of_ne {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {p : ℝ} (hp : 1 < p) (x y h k : H) (hhk : ‖h‖ ≤ ‖k‖)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖ := by
  rcases le_total 2 p with h2 | h2
  · have e : (fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖) =
        fun t => (p * (1 - 1 / p) ^ (p - 1)) • psiLine p x y h k t := by
      funext t; rw [U_eq_A h2, psiLine, smul_eq_mul]
    rw [e]
    exact ((psi_line_of_ne hp x y h k hx hy).1 ⟨h2, hhk⟩).smul
      (alpha_nonneg hp)
  · have e : (fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖) =
        fun t => (p * (1 / p) ^ (p - 1) / (p - 1)) • (-psiLine p y x k h) t := by
      funext t; rw [U_eq_B hp h2, Pi.neg_apply, psiLine, smul_eq_mul]; ring
    rw [e]
    exact ((psi_line_of_ne hp y x k h hy hx).2 ⟨h2, hhk⟩).neg.smul
      (div_nonneg (by positivity) (by linarith))

/-- `‖(v, δ)‖ = √(‖v‖² + δ²)` in `H ⊕ ℝ` (`WithLp 2 (H × ℝ)`). -/
private theorem norm_toLp_shift {H : Type*} [NormedAddCommGroup H] (v : H) (δ : ℝ) :
    ‖(WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ))‖ = √(‖v‖ ^ 2 + δ ^ 2) := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- In `H ⊕ ℝ`, the line through `(v, δ)` with direction `(w, 0)`: `(v + t w, δ)`. -/
private theorem toLp_line {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (v w : H)
    (δ t : ℝ) : (WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ)) + t • WithLp.toLp 2 (w, 0) =
      WithLp.toLp 2 (v + t • w, δ) := by
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

private theorem toLp_ne_zero {H : Type*} [NormedAddCommGroup H] (v : H) {δ : ℝ} (hδ : δ ≠ 0) :
    (WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ)) ≠ 0 := fun h =>
  hδ (by simpa using congrArg (fun z : WithLp 2 (H × ℝ) => z.snd) h)

/-- A pointwise limit of concave functions on `ℝ` is concave. -/
private theorem concaveOn_univ_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ m, ConcaveOn ℝ univ (f m)) (hlim : ∀ t, Tendsto (fun m => f m t) atTop (𝓝 (g t))) :
    ConcaveOn ℝ univ g := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hlim a).const_smul μ).add ((hlim b).const_smul ν))
    (hlim _) fun m => (hf m).2 (mem_univ a) (mem_univ b) hμ hν hμν

private theorem continuous_burkholderU {p : ℝ} (hp : 1 < p) :
    Continuous fun z : ℝ × ℝ => burkholderU p z.1 z.2 := by
  unfold burkholderU
  exact (continuous_const.mul (continuous_fst.sub (continuous_const.mul continuous_snd))).mul
    ((continuous_fst.add continuous_snd).rpow_const fun _ => Or.inr (by linarith))

/-- `δ ↦ U (√(a² + δ²), √(b² + δ²))` is continuous, with value `U (a, b)` at `δ = 0` for
`a, b ≥ 0`. -/
private theorem tendsto_burkholderU_shift {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun m : ℕ => burkholderU p √(a ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
      √(b ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)) atTop (𝓝 (burkholderU p a b)) := by
  have hc : Continuous fun δ : ℝ => burkholderU p √(a ^ 2 + δ ^ 2) √(b ^ 2 + δ ^ 2) :=
    (continuous_burkholderU hp).comp
      ((Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).prodMk
        (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))))
  have := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [Function.comp_def, Real.sqrt_sq ha, Real.sqrt_sq hb] using this

/-- **Concavity of Burkholder's function along lines** (Burkholder 1988, Remark 1.2, (1.17)):
for `x, y, h, k` in a real inner product space with `|h| ≤ |k|`,
`t ↦ U (x + t h, y + t k)` is concave on `ℝ` (`x` the position of the subordinate martingale,
`y` that of the dominating one). Gap of the source: the paper states this without proof. It is
completed here from two steps of the paper, an assembly of the formalization: the proof of (1.12)
covers the lines on which `x + t h` and `y + t k` never vanish
(`burkholderU_concaveOn_line_of_ne`), and the other lines are reached by the device of the proof of
(1.8): in `H ⊕ ℝ` (`WithLp 2 (H × ℝ)`),
the lines through `(x, δ)` and `(y, δ)` with directions `(h, 0)` and `(k, 0)` never vanish for
`δ ≠ 0`, so `t ↦ U (√(|x + t h|² + δ²), √(|y + t k|² + δ²))` is concave, and these functions tend
to `t ↦ U (|x + t h|, |y + t k|)` as `δ → 0` (`concaveOn_univ_of_tendsto`). -/
theorem burkholderU_concaveOn_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p : ℝ} (hp : 1 < p) (x y h k : H) (hhk : ‖h‖ ≤ ‖k‖) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖ := by
  have hδ : ∀ m : ℕ, ConcaveOn ℝ univ fun t : ℝ =>
      burkholderU p √(‖x + t • h‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
        √(‖y + t • k‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) := fun m => by
    have hδ0 : (1 / ((m : ℝ) + 1)) ≠ 0 := by positivity
    have := burkholderU_concaveOn_line_of_ne hp (WithLp.toLp 2 (x, 1 / ((m : ℝ) + 1)))
      (WithLp.toLp 2 (y, 1 / ((m : ℝ) + 1))) (WithLp.toLp 2 (h, (0 : ℝ)))
      (WithLp.toLp 2 (k, (0 : ℝ))) (by rwa [WithLp.norm_toLp_fst, WithLp.norm_toLp_fst])
      (fun t => by rw [toLp_line]; exact toLp_ne_zero _ hδ0)
      (fun t => by rw [toLp_line]; exact toLp_ne_zero _ hδ0)
    simpa only [toLp_line, norm_toLp_shift] using this
  exact concaveOn_univ_of_tendsto hδ fun t =>
    tendsto_burkholderU_shift hp (norm_nonneg _) (norm_nonneg _)

/-! ### Bounds and measurability of Burkholder's function and of its gradient -/

private theorem abs_burkholderU_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    |burkholderU p s r| ≤
      p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * max p (p / (p - 1)) * (s + r) ^ p := by
  set P := max p (p / (p - 1)) with hP
  have hP1 : 1 < P := lt_of_lt_of_le hp (le_max_left _ _)
  have hα : 0 ≤ p * (1 - 1 / P) ^ (p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)
  unfold burkholderU
  rw [← hP]
  have e : (s + r) ^ p = (s + r) * (s + r) ^ (p - 1) := by
    rw [show (s + r) ^ p = (s + r) ^ (1 + (p - 1)) by ring_nf, Real.rpow_add' (by linarith)
      (by linarith), Real.rpow_one]
  have h2 : 0 ≤ (s + r) ^ (p - 1) := Real.rpow_nonneg (by linarith) _
  have h1 : |s - (P - 1) * r| ≤ P * (s + r) := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg h2, e]
  calc p * (1 - 1 / P) ^ (p - 1) * |s - (P - 1) * r| * (s + r) ^ (p - 1)
      ≤ p * (1 - 1 / P) ^ (p - 1) * (P * (s + r)) * (s + r) ^ (p - 1) := by gcongr
    _ = _ := by ring

private theorem measurable_burkholderU (p : ℝ) : Measurable (Function.uncurry (burkholderU p)) := by
  change Measurable fun z : ℝ × ℝ => burkholderU p z.1 z.2
  unfold burkholderU
  fun_prop

private theorem burkholderU_zero (p : ℝ) : burkholderU p 0 0 = 0 := by
  simp [burkholderU]

/-- `|c L W^{p−2} / u| u ≤ |c| K W^{p−1}` for `W = s + r ≥ u ≥ 0` and `|L| ≤ K W`. -/
private theorem abs_grad_mul_le {p c L K s r u : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u)
    (hus : u ≤ s + r) (hK : 0 ≤ K) (hL : |L| ≤ K * (s + r)) :
    |c * L * (s + r) ^ (p - 2) / u| * u ≤ |c| * K * (s + r) ^ (p - 1) := by
  have hW : 0 ≤ s + r := add_nonneg hs hr
  rcases hu.eq_or_lt with rfl | hu
  · simp only [div_zero, abs_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg c) hK) (Real.rpow_nonneg hW _)
  · have hW0 : 0 < s + r := hu.trans_le hus
    rw [abs_div, abs_of_pos hu, div_mul_cancel₀ _ hu.ne', abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hW _),
      show (s + r) ^ (p - 1) = (s + r) * (s + r) ^ (p - 2) by
        rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add hW0, Real.rpow_one]]
    have := mul_le_mul_of_nonneg_left hL (abs_nonneg c)
    have h2 := Real.rpow_nonneg hW (p - 2)
    nlinarith [mul_le_mul_of_nonneg_right this h2]

/-! ### Burkholder's method: `E U (X_n, Y_n) ≤ E U (X_{n−1}, Y_{n−1}) ≤ … ≤ U (0, 0) = 0` -/

section Method

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [IsProbabilityMeasure μ] in
/-- The image of a martingale under a continuous linear map is a martingale. -/
private theorem martingale_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {M : ℕ → Ω → E} (hM : Martingale M ℱ μ) (T : E →L[ℝ] F) :
    Martingale (fun m ω => T (M m ω)) ℱ μ := by
  refine ⟨fun m => T.continuous.comp_stronglyMeasurable (hM.stronglyAdapted m),
    fun i j hij => ?_⟩
  filter_upwards [T.comp_condExp_comm (m := ℱ i) (hM.integrable j), hM.condExp_ae_eq hij]
    with ω h1 h2
  change μ[T ∘ M j | ℱ i] ω = T (M i ω)
  rw [← h1, Function.comp_apply, h2]

/-- `E ⟨Z, X_{k+1} − X_k⟩ = 0` for an `ℱ_k`-measurable `Z`, by the pull-out property of the
conditional expectation: `E [⟨Z, dX_{k+1}⟩ | ℱ_k] = ⟨Z, E [dX_{k+1} | ℱ_k]⟩ = 0`. -/
private theorem integral_inner_increment {X : ℕ → Ω → H} (hX : Martingale X ℱ μ) {k : ℕ}
    {Z : Ω → H} (hZ : StronglyMeasurable[ℱ k] Z)
    (hint : Integrable (fun ω => ⟪Z ω, X (k + 1) ω - X k ω⟫) μ) :
    ∫ ω, ⟪Z ω, X (k + 1) ω - X k ω⟫ ∂μ = 0 := by
  have hd : Integrable (X (k + 1) - X k) μ := (hX.integrable _).sub (hX.integrable _)
  have hB : ∀ v w : H, (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) v w = ⟪v, w⟫ :=
    fun v w => innerSL_apply_apply ℝ v w
  have hint' :
      Integrable (fun ω => (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) (Z ω) ((X (k + 1) - X k) ω)) μ := by
    simpa only [hB, Pi.sub_apply] using hint
  have h1 := condExp_bilin_of_aestronglyMeasurable_left (m := ℱ k) (innerSL ℝ)
    hZ.aestronglyMeasurable hint' hd
  simp only [hB, Pi.sub_apply] at h1
  have h2 : μ[X (k + 1) - X k | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hX.integrable (k + 1)) (hX.integrable k) (ℱ k),
      hX.condExp_ae_eq (Nat.le_succ k)] with ω h3 h4
    rw [h3, Pi.sub_apply, h4, condExp_of_stronglyMeasurable (ℱ.le k) (hX.stronglyAdapted k)
      (hX.integrable k)]
    simp
  calc ∫ ω, ⟪Z ω, X (k + 1) ω - X k ω⟫ ∂μ
      = ∫ ω, (μ[fun ω => ⟪Z ω, X (k + 1) ω - X k ω⟫ | ℱ k]) ω ∂μ :=
        (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, ⟪Z ω, μ[X (k + 1) - X k | ℱ k] ω⟫ ∂μ := integral_congr_ae h1
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h2] with ω hω
        rw [hω, Pi.zero_apply, inner_zero_right]
    _ = 0 := integral_zero _ _

omit [IsProbabilityMeasure μ] in
private theorem integrable_rpow_of_memLp {W : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hW : MemLp W (ENNReal.ofReal p) μ) (hWnn : ∀ ω, 0 ≤ W ω) :
    Integrable (fun ω => W ω ^ p) μ := by
  have h := hW.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at h
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_of_nonneg (hWnn ω)]

private theorem rpow_sub_one_mul_le {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {W : ℝ} (haW : a ≤ W) (hbW : b ≤ W) : a ^ (p - 1) * b ≤ W ^ p := by
  have hW : 0 ≤ W := ha.trans haW
  calc a ^ (p - 1) * b ≤ W ^ (p - 1) * W :=
        mul_le_mul (Real.rpow_le_rpow ha haW (by linarith)) hbW hb (Real.rpow_nonneg hW _)
    _ = W ^ p := by
        rw [← Real.rpow_add_one' hW (by linarith)]; ring_nf

omit [IsProbabilityMeasure μ] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem integrable_of_bound {F : ℝ → ℝ → ℝ} {C p : ℝ} (hp : 0 < p)
    (hF : Measurable (Function.uncurry F))
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p) {U V : Ω → H}
    (hU : MemLp U (ENNReal.ofReal p) μ) (hV : MemLp V (ENNReal.ofReal p) μ) :
    Integrable (fun ω => F ‖U ω‖ ‖V ω‖) μ := by
  have hW := integrable_rpow_of_memLp hp (hU.norm.add hV.norm)
    (fun ω => add_nonneg (norm_nonneg (U ω)) (norm_nonneg (V ω)))
  refine (hW.const_mul C).mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact (hF.comp_aemeasurable (hU.aestronglyMeasurable.norm.aemeasurable.prodMk
      hV.aestronglyMeasurable.norm.aemeasurable)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hFb _ _ (norm_nonneg _) (norm_nonneg _)

/-- One step of Burkholder's method, (1.15) integrated: if
`F (|x + h|, |y + k|) ≤ F (|x|, |y|) + f (|x|, |y|) ⟨x, h⟩ + g (|x|, |y|) ⟨y, k⟩` whenever
`|h| ≤ |k|` and the lines `x + t h`, `y + t k` never vanish, and the lines through `(X_k, Y_k)` in
the direction of the increments never vanish, then `E F (X_{k+1}, Y_{k+1}) ≤ E F (X_k, Y_k)`: the
linear terms have zero expectation by the martingale property (`integral_inner_increment`). -/
private theorem method_step {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ)
    {F f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hzig : ∀ x y h k : H, ‖h‖ ≤ ‖k‖ → (∀ t : ℝ, x + t • h ≠ 0) → (∀ t : ℝ, y + t • k ≠ 0) →
      F ‖x + h‖ ‖y + k‖ ≤ F ‖x‖ ‖y‖ + f ‖x‖ ‖y‖ * ⟪x, h⟫ + g ‖x‖ ‖y‖ * ⟪y, k⟫)
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p)
    (hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |f s r| * s ≤ C * (s + r) ^ (p - 1))
    (hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |g s r| * r ≤ C * (s + r) ^ (p - 1)) {k : ℕ}
    (hsub : ∀ᵐ ω ∂μ, ‖X (k + 1) ω - X k ω‖ ≤ ‖Y (k + 1) ω - Y k ω‖)
    (hXne : ∀ ω (t : ℝ), X k ω + t • (X (k + 1) ω - X k ω) ≠ 0)
    (hYne : ∀ ω (t : ℝ), Y k ω + t • (Y (k + 1) ω - Y k ω) ≠ 0)
    (hXk : MemLp (X k) (ENNReal.ofReal p) μ) (hYk : MemLp (Y k) (ENNReal.ofReal p) μ)
    (hXk1 : MemLp (X (k + 1)) (ENNReal.ofReal p) μ)
    (hYk1 : MemLp (Y (k + 1)) (ENNReal.ofReal p) μ) :
    ∫ ω, F ‖X (k + 1) ω‖ ‖Y (k + 1) ω‖ ∂μ ≤ ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ := by
  have hp0 : 0 < p := by linarith
  have hdX := hXk1.sub hXk
  have hdY := hYk1.sub hYk
  -- the dominating function `C W^p`, `W = |X_k| + |Y_k| + |dX| + |dY|`
  set W : Ω → ℝ := fun ω => ‖X k ω‖ + ‖Y k ω‖ + ‖X (k + 1) ω - X k ω‖ + ‖Y (k + 1) ω - Y k ω‖
    with hWdef
  have hWnn : ∀ ω, 0 ≤ W ω := fun ω => by positivity
  have hWint : Integrable (fun ω => C * W ω ^ p) μ :=
    (integrable_rpow_of_memLp hp0 (((hXk.norm.add hYk.norm).add hdX.norm).add hdY.norm)
      hWnn).const_mul C
  have hI1 := integrable_of_bound hp0 hF hFb hXk1 hYk1
  have hI0 := integrable_of_bound hp0 hF hFb hXk hYk
  -- the two linear terms
  have mXk : Measurable[ℱ k] fun ω => ‖X k ω‖ := (hX.stronglyAdapted k).norm.measurable
  have mYk : Measurable[ℱ k] fun ω => ‖Y k ω‖ := (hY.stronglyAdapted k).norm.measurable
  set ZX : Ω → H := fun ω => f ‖X k ω‖ ‖Y k ω‖ • X k ω with hZX
  set ZY : Ω → H := fun ω => g ‖X k ω‖ ‖Y k ω‖ • Y k ω with hZY
  have sZX : StronglyMeasurable[ℱ k] ZX :=
    (hf.comp (mXk.prodMk mYk)).stronglyMeasurable.smul (hX.stronglyAdapted k)
  have sZY : StronglyMeasurable[ℱ k] ZY :=
    (hg.comp (mXk.prodMk mYk)).stronglyMeasurable.smul (hY.stronglyAdapted k)
  have eZX : ∀ ω, ⟪ZX ω, X (k + 1) ω - X k ω⟫ =
      f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫ := fun ω => real_inner_smul_left _ _ _
  have eZY : ∀ ω, ⟪ZY ω, Y (k + 1) ω - Y k ω⟫ =
      g ‖X k ω‖ ‖Y k ω‖ * ⟪Y k ω, Y (k + 1) ω - Y k ω⟫ := fun ω => real_inner_smul_left _ _ _
  have hIX : Integrable (fun ω => ⟪ZX ω, X (k + 1) ω - X k ω⟫) μ := by
    refine hWint.mono' ((sZX.mono (ℱ.le k)).aestronglyMeasurable.inner hdX.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [eZX, Real.norm_eq_abs, abs_mul]
    calc |f ‖X k ω‖ ‖Y k ω‖| * |⟪X k ω, X (k + 1) ω - X k ω⟫|
        ≤ |f ‖X k ω‖ ‖Y k ω‖| * (‖X k ω‖ * ‖X (k + 1) ω - X k ω‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ = |f ‖X k ω‖ ‖Y k ω‖| * ‖X k ω‖ * ‖X (k + 1) ω - X k ω‖ := by ring
      _ ≤ C * (‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖X (k + 1) ω - X k ω‖ :=
          mul_le_mul_of_nonneg_right (hfb _ _ (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = C * ((‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖X (k + 1) ω - X k ω‖) := by ring
      _ ≤ C * W ω ^ p := by
          gcongr
          refine rpow_sub_one_mul_le hp (by positivity) (norm_nonneg _) ?_ ?_
          · simp only [hWdef]
            linarith [norm_nonneg (X (k + 1) ω - X k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
          · simp only [hWdef]
            linarith [norm_nonneg (X k ω), norm_nonneg (Y k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
  have hIY : Integrable (fun ω => ⟪ZY ω, Y (k + 1) ω - Y k ω⟫) μ := by
    refine hWint.mono' ((sZY.mono (ℱ.le k)).aestronglyMeasurable.inner hdY.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [eZY, Real.norm_eq_abs, abs_mul]
    calc |g ‖X k ω‖ ‖Y k ω‖| * |⟪Y k ω, Y (k + 1) ω - Y k ω⟫|
        ≤ |g ‖X k ω‖ ‖Y k ω‖| * (‖Y k ω‖ * ‖Y (k + 1) ω - Y k ω‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ = |g ‖X k ω‖ ‖Y k ω‖| * ‖Y k ω‖ * ‖Y (k + 1) ω - Y k ω‖ := by ring
      _ ≤ C * (‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖Y (k + 1) ω - Y k ω‖ :=
          mul_le_mul_of_nonneg_right (hgb _ _ (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = C * ((‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖Y (k + 1) ω - Y k ω‖) := by ring
      _ ≤ C * W ω ^ p := by
          gcongr
          refine rpow_sub_one_mul_le hp (by positivity) (norm_nonneg _) ?_ ?_
          · simp only [hWdef]
            linarith [norm_nonneg (X (k + 1) ω - X k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
          · simp only [hWdef]
            linarith [norm_nonneg (X k ω), norm_nonneg (Y k ω), norm_nonneg (X (k + 1) ω - X k ω)]
  have h0X := integral_inner_increment hX sZX hIX
  have h0Y := integral_inner_increment hY sZY hIY
  simp only [eZX] at hIX h0X
  simp only [eZY] at hIY h0Y
  calc ∫ ω, F ‖X (k + 1) ω‖ ‖Y (k + 1) ω‖ ∂μ
      ≤ ∫ ω, (F ‖X k ω‖ ‖Y k ω‖ + f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫ +
          g ‖X k ω‖ ‖Y k ω‖ * ⟪Y k ω, Y (k + 1) ω - Y k ω⟫) ∂μ := by
        refine integral_mono_ae hI1 ((hI0.add hIX).add hIY) ?_
        filter_upwards [hsub] with ω hω
        have := hzig (X k ω) (Y k ω) (X (k + 1) ω - X k ω) (Y (k + 1) ω - Y k ω) hω
          (hXne ω) (hYne ω)
        simpa only [add_sub_cancel] using this
    _ = ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ := by
        have hI01 : Integrable (fun ω => F ‖X k ω‖ ‖Y k ω‖ +
            f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫) μ := hI0.add hIX
        rw [integral_add hI01 hIY, integral_add hI0 hIX, h0X, h0Y]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Dominated convergence for the shift `δ = 1/(m + 1) → 0`: for `X, Y ∈ L^p`,
`E U (√(|X|² + δ²), √(|Y|² + δ²)) → E U (|X|, |Y|)`, the integrands being dominated by
`K (|X| + |Y| + 2)^p` (`abs_burkholderU_le`). -/
private theorem tendsto_integral_burkholderU_shift {X Y : Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : MemLp X (ENNReal.ofReal p) μ) (hY : MemLp Y (ENNReal.ofReal p) μ) :
    Tendsto (fun m : ℕ => ∫ ω, burkholderU p √(‖X ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
      √(‖Y ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) ∂μ) atTop
      (𝓝 (∫ ω, burkholderU p ‖X ω‖ ‖Y ω‖ ∂μ)) := by
  have hp0 : 0 < p := by linarith
  set K := p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * max p (p / (p - 1)) with hK
  have hP1 : 1 < max p (p / (p - 1)) := lt_of_lt_of_le hp (le_max_left _ _)
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hp0.le (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)) (by linarith)
  -- `√(a² + δ²) ≤ a + 1` for `a ≥ 0`, `0 ≤ δ ≤ 1`
  have hsq : ∀ a δ : ℝ, 0 ≤ a → 0 ≤ δ → δ ≤ 1 → √(a ^ 2 + δ ^ 2) ≤ a + 1 := fun a δ ha hδ hδ1 =>
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  refine tendsto_integral_of_dominated_convergence (fun ω => K * (‖X ω‖ + ‖Y ω‖ + 2) ^ p)
    (fun m => ?_) ?_ (fun m => ?_) ?_
  · have hc : Continuous fun z : ℝ × ℝ => burkholderU p √(z.1 ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
        √(z.2 ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) :=
      (continuous_burkholderU hp).comp
        ((Real.continuous_sqrt.comp ((continuous_fst.pow 2).add continuous_const)).prodMk
          (Real.continuous_sqrt.comp ((continuous_snd.pow 2).add continuous_const)))
    exact (hc.measurable.comp_aemeasurable (hX.aestronglyMeasurable.norm.aemeasurable.prodMk
      hY.aestronglyMeasurable.norm.aemeasurable)).aestronglyMeasurable
  · have h2 : MemLp (fun ω => ‖X ω‖ + ‖Y ω‖ + 2) (ENNReal.ofReal p) μ :=
      (hX.norm.add hY.norm).add (memLp_const 2)
    exact (integrable_rpow_of_memLp hp0 h2 fun ω => by positivity).const_mul K
  · filter_upwards with ω
    have hδ0 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    have hδ1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [Real.norm_eq_abs]
    refine (abs_burkholderU_le hp (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hp0.le) hK0
    linarith [hsq _ _ (norm_nonneg (X ω)) hδ0 hδ1, hsq _ _ (norm_nonneg (Y ω)) hδ0 hδ1]
  · filter_upwards with ω
    exact tendsto_burkholderU_shift hp (norm_nonneg _) (norm_nonneg _)

/-- **(1.8)**: for martingales in `L^p` with `‖X_{k+1} − X_k‖ ≤ ‖Y_{k+1} − Y_k‖`,
`E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` (Burkholder 1988, proof of Theorem 1.1). In
`H ⊕ ℝ` (`WithLp 2 (H × ℝ)`, the enlargement of `H`), `a = (0, δ)`, `δ ≠ 0`, is orthogonal to the
values of `X` and `Y`; `F_k = a + X_k` and `G_k = a + Y_k` are martingales with the same increments,
and the lines through `(F_k, G_k)` in the direction of the increments never vanish, so (1.12)
(`burkholderU_zigzag_of_ne`) gives (1.15), whose linear terms have zero expectation
(`method_step`): `E U (F_{k+1}, G_{k+1}) ≤ E U (F_k, G_k)`, where `|F_k| = √(|X_k|² + δ²)`. Let
`δ → 0` (`tendsto_integral_burkholderU_shift`). -/
private theorem integral_burkholderU_succ_le {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) {k : ℕ}
    (hsub : ∀ᵐ ω ∂μ, ‖X (k + 1) ω - X k ω‖ ≤ ‖Y (k + 1) ω - Y k ω‖)
    (hXk : MemLp (X k) (ENNReal.ofReal p) μ) (hYk : MemLp (Y k) (ENNReal.ofReal p) μ)
    (hXk1 : MemLp (X (k + 1)) (ENNReal.ofReal p) μ)
    (hYk1 : MemLp (Y (k + 1)) (ENNReal.ofReal p) μ) :
    ∫ ω, burkholderU p ‖X (k + 1) ω‖ ‖Y (k + 1) ω‖ ∂μ ≤
      ∫ ω, burkholderU p ‖X k ω‖ ‖Y k ω‖ ∂μ := by
  have hp0 : 0 < p := by linarith
  -- the constants of `method_step`
  set P := max p (p / (p - 1)) with hPdef
  have hP1 : 1 < P := lt_of_lt_of_le hp (le_max_left _ _)
  set α := p * (1 - 1 / P) ^ (p - 1) with hα
  have hα0 : 0 ≤ α := mul_nonneg hp0.le (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)
  set Kx := p + |p + P - p * P|
  set Ky := |p - P| + p * (P - 1)
  set C := α * P + |α| * Kx + |α| * Ky with hC
  have hKx : 0 ≤ Kx := by positivity
  have hKy : 0 ≤ Ky := add_nonneg (abs_nonneg _) (mul_nonneg hp0.le (by linarith))
  have hC0 : 0 ≤ C := by positivity
  have hpow : ∀ s r : ℝ, 0 ≤ s → 0 ≤ r → 0 ≤ (s + r) ^ (p - 1) :=
    fun s r hs hr => Real.rpow_nonneg (by linarith) _
  have hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |burkholderU p s r| ≤ C * (s + r) ^ p := fun s r hs hr => by
    refine (abs_burkholderU_le hp hs hr).trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (by linarith) _))
    have := mul_nonneg (abs_nonneg α) hKx; have := mul_nonneg (abs_nonneg α) hKy; linarith
  have hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |gradX p s r| * s ≤ C * (s + r) ^ (p - 1) :=
    fun s r hs hr => by
      refine (abs_grad_mul_le hs hr hs (by linarith) hKx ?_).trans
        (mul_le_mul_of_nonneg_right ?_ (hpow s r hs hr))
      · refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hp0.le, abs_of_nonneg hs, abs_of_nonneg hr]
        nlinarith [abs_nonneg (p + P - p * P)]
      · have := mul_nonneg (abs_nonneg α) hKy; nlinarith [abs_nonneg α]
  have hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |gradY p s r| * r ≤ C * (s + r) ^ (p - 1) :=
    fun s r hs hr => by
      refine (abs_grad_mul_le hs hr hr (by linarith) hKy ?_).trans
        (mul_le_mul_of_nonneg_right ?_ (hpow s r hs hr))
      · refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hp0.le (by linarith) : 0 ≤ p * (P - 1)),
          abs_of_nonneg hs, abs_of_nonneg hr]
        nlinarith [abs_nonneg (p - P), mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ P - 1)]
      · have := mul_nonneg (abs_nonneg α) hKx; nlinarith [abs_nonneg α]
  have hmX : Measurable (Function.uncurry (gradX p)) := by
    change Measurable fun z : ℝ × ℝ => gradX p z.1 z.2
    unfold gradX; fun_prop
  have hmY : Measurable (Function.uncurry (gradY p)) := by
    change Measurable fun z : ℝ × ℝ => gradY p z.1 z.2
    unfold gradY; fun_prop
  -- the shifted martingales in `H ⊕ ℝ`, and (1.15) integrated
  have hshift : ∀ m : ℕ,
      ∫ ω, burkholderU p √(‖X (k + 1) ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
        √(‖Y (k + 1) ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) ∂μ ≤
      ∫ ω, burkholderU p √(‖X k ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
        √(‖Y k ω‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) ∂μ := by
    intro m
    set δ : ℝ := 1 / ((m : ℝ) + 1)
    have hδ : δ ≠ 0 := by positivity
    let ι : H →L[ℝ] WithLp 2 (H × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ H ℝ)
    set a : WithLp 2 (H × ℝ) := WithLp.toLp 2 (0, δ)
    have hcomb : ∀ v : H, ι v + a = WithLp.toLp 2 (v, δ) := fun v => by
      change WithLp.toLp 2 (v, (0 : ℝ)) + WithLp.toLp 2 ((0 : H), δ) = _
      rw [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    have hdiff : ∀ v w : H, (ι v + a) - (ι w + a) = WithLp.toLp 2 (v - w, (0 : ℝ)) :=
      fun v w => by
        rw [add_sub_add_right_eq_sub, ← map_sub]; rfl
    have hne : ∀ v w : H, ∀ t : ℝ, (ι v + a) + t • ((ι w + a) - (ι v + a)) ≠ 0 :=
      fun v w t => by rw [hdiff, hcomb, toLp_line]; exact toLp_ne_zero _ hδ
    have hX' : Martingale (fun j ω => ι (X j ω) + a) ℱ μ :=
      (martingale_clm hX ι).add (martingale_const ℱ μ a)
    have hY' : Martingale (fun j ω => ι (Y j ω) + a) ℱ μ :=
      (martingale_clm hY ι).add (martingale_const ℱ μ a)
    have hmem : ∀ {Z : Ω → H}, MemLp Z (ENNReal.ofReal p) μ →
        MemLp (fun ω => ι (Z ω) + a) (ENNReal.ofReal p) μ := fun hZ =>
      (ι.comp_memLp' hZ).add (memLp_const a)
    have h := method_step hp hX' hY' (F := burkholderU p) (f := gradX p) (g := gradY p) hC0
      (measurable_burkholderU p) hmX hmY
      (fun x y h k hhk hx hy => burkholderU_zigzag_of_ne hp x y h k hhk hx hy) hFb hfb hgb
      (k := k) (by
        filter_upwards [hsub] with ω hω
        rwa [hdiff, hdiff, WithLp.norm_toLp_fst, WithLp.norm_toLp_fst])
      (fun ω t => hne _ _ t) (fun ω t => hne _ _ t) (hmem hXk) (hmem hYk) (hmem hXk1)
      (hmem hYk1)
    simpa only [hcomb, norm_toLp_shift] using h
  exact le_of_tendsto_of_tendsto' (tendsto_integral_burkholderU_shift hp hXk1 hYk1)
    (tendsto_integral_burkholderU_shift hp hXk hYk) hshift

/-- `E U (X_n, Y_n) ≤ 0` for differentially subordinate martingales in `L^p` started at `0`:
(1.8) at each step (`integral_burkholderU_succ_le`) and (1.9), `U (X_0, Y_0) = U (0, 0) = 0`. -/
private theorem integral_burkholderU_nonpos {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ)
    (hXn : ∀ k ≤ n, MemLp (X k) (ENNReal.ofReal p) μ)
    (hYn : ∀ k ≤ n, MemLp (Y k) (ENNReal.ofReal p) μ) :
    ∫ ω, burkholderU p ‖X n ω‖ ‖Y n ω‖ ∂μ ≤ 0 := by
  suffices ∀ k ≤ n, ∫ ω, burkholderU p ‖X k ω‖ ‖Y k ω‖ ∂μ ≤ 0 from this n le_rfl
  intro k
  induction k with
  | zero => intro _; simp [hX0, hY0, burkholderU_zero]
  | succ k ih =>
    intro hk
    exact (integral_burkholderU_succ_le hp hX hY (hsub k) (hXn k (by omega)) (hYn k (by omega))
      (hXn (k + 1) hk) (hYn (k + 1) hk)).trans (ih (by omega))

end Method

/-! ### Burkholder's inequality -/

/-- Burkholder's inequality without the separability of `H` (which the proof does not use). -/
theorem inequality_of_subordinate {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hq0 : q ≠ 0 := by rw [hq, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  set β := max p (p / (p - 1)) - 1 with hβdef
  have hβ : 0 < β := by have := le_max_left p (p / (p - 1)); linarith
  by_cases hYt : eLpNorm (Y n) q μ = ⊤
  · rw [hYt, ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hβ)]
    exact le_top
  -- if `Y_n ∈ L^p`, then `Y_k = E [Y_n | ℱ_k] ∈ L^p` and `X_k = Σ dX_j ∈ L^p` for `k ≤ n`
  have hYn : MemLp (Y n) q μ := memLp_iff.2 (lt_top_iff_ne_top.2 hYt)
  have hYk : ∀ k ≤ n, MemLp (Y k) q μ := fun k hk =>
    (hYn.condExp (m := ℱ k) hq1).ae_eq (hY.condExp_ae_eq hk)
  have hXk : ∀ k ≤ n, MemLp (X k) q μ := by
    intro k
    induction k with
    | zero => intro _; rw [show X 0 = 0 from funext hX0]; exact MemLp.zero
    | succ k ih =>
      intro hk
      have hd : MemLp (X (k + 1) - X k) q μ :=
        ((hYk (k + 1) hk).sub (hYk k (by omega))).of_le
          ((((hX.stronglyAdapted (k + 1)).mono (ℱ.le _)).aestronglyMeasurable).sub
            (((hX.stronglyAdapted k).mono (ℱ.le _)).aestronglyMeasurable))
          (by filter_upwards [hsub k] with ω hω; simpa only [Pi.sub_apply] using hω)
      have := (ih (by omega)).add hd
      rwa [add_sub_cancel] at this
  -- `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ 0`
  have hEU := integral_burkholderU_nonpos hp hX hY hX0 hY0 hsub n hXk hYk
  have hIX := integrable_rpow_of_memLp hp0 (hXk n le_rfl).norm (fun _ => norm_nonneg _)
  have hIY := integrable_rpow_of_memLp hp0 hYn.norm (fun _ => norm_nonneg _)
  have hIU := integrable_of_bound hp0 (measurable_burkholderU p)
    (fun s r hs hr => abs_burkholderU_le hp hs hr) (hXk n le_rfl) hYn
  have hV : ∫ ω, ‖X n ω‖ ^ p ∂μ - β ^ p * ∫ ω, ‖Y n ω‖ ^ p ∂μ ≤ 0 := by
    rw [← integral_const_mul, ← integral_sub hIX (hIY.const_mul _)]
    exact (integral_mono (hIX.sub (hIY.const_mul _)) hIU
      fun ω => burkholderU_ge hp (norm_nonneg _) (norm_nonneg _)).trans hEU
  -- back to `L^p` norms
  rw [(hXk n le_rfl).eLpNorm_eq_integral_rpow_norm hq0 hqt,
    hYn.eLpNorm_eq_integral_rpow_norm hq0 hqt, hqr, ← ENNReal.ofReal_mul hβ.le]
  apply ENNReal.ofReal_le_ofReal
  have hIXnn : 0 ≤ ∫ ω, ‖X n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hIYnn : 0 ≤ ∫ ω, ‖Y n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ ω, ‖X n ω‖ ^ p ∂μ) ^ p⁻¹ ≤ (β ^ p * ∫ ω, ‖Y n ω‖ ^ p ∂μ) ^ p⁻¹ :=
        Real.rpow_le_rpow hIXnn (by linarith) (inv_nonneg.2 hp0.le)
    _ = β * (∫ ω, ‖Y n ω‖ ^ p ∂μ) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hβ.le _) hIYnn, Real.rpow_rpow_inv hβ.le hp0.ne']

/-- **Burkholder's inequality** (Burkholder 1988, Theorem 1.1; Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 3.5): for martingales `X`, `Y` with values in a
separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`.
(Burkholder's Theorem 1.1 covers real and complex `H`, with no separability, and martingales from
any start; the statement here is the one cited.)

The argument of Burkholder 1988, proof of Theorem 1.1: Burkholder's function
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}` (`burkholderU`, (1.6))
majorizes `V (x, y) = |x|^p − (p* − 1)^p |y|^p` ((1.10), `burkholderU_ge`), and
`E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` ((1.8), `integral_burkholderU_succ_le`: (1.12) for the
martingales shifted by a vector `a` orthogonal to `H`, integrated, then `a → 0`), so
`E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`. If `‖Y_n‖_p = ∞` the right side is `∞`; otherwise
every `Y_k`, `X_k` (`k ≤ n`) is in `L^p`, which makes every term integrable. The separability of
`H` is not used. -/
theorem inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  inequality_of_subordinate hp hX hY hX0 hY0 hsub n

/-! ### Burkholder's square function inequality -/

section SquareFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

/-- A martingale stopped at the deterministic time `j`. -/
private theorem martingale_stopped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {X : ℕ → Ω → E} (hX : Martingale X ℱ μ) (j : ℕ) :
    Martingale (fun m => X (min j m)) ℱ μ := by
  refine martingale_nat (fun m => (hX.stronglyAdapted (min j m)).mono (ℱ.mono (min_le_right _ _)))
    (fun m => hX.integrable _) fun m => ?_
  rcases le_or_gt j m with h | h
  · simp only [min_eq_left h, min_eq_left (h.trans (Nat.le_succ m))]
    rw [condExp_of_stronglyMeasurable (ℱ.le m) ((hX.stronglyAdapted j).mono (ℱ.mono h))
      (hX.integrable j)]
  · simp only [min_eq_right h.le, min_eq_right (Nat.succ_le_of_lt h)]
    exact (hX.condExp_ae_eq (Nat.le_succ m)).symm

omit [IsProbabilityMeasure μ] in
private theorem martingale_finset_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Finset ι) {M : ι → ℕ → Ω → E}
    (hM : ∀ i ∈ s, Martingale (M i) ℱ μ) :
    Martingale (fun m ω => ∑ i ∈ s, M i m ω) ℱ μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert martingale_zero E ℱ μ using 1
    funext m ω; simp
  | insert a s ha ih =>
    have := (hM a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hM i (Finset.mem_insert_of_mem hi))
    convert this using 1
    funext m ω; simp [Finset.sum_insert ha]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem norm_sum_single {n : ℕ} (v : Fin n → H) :
    ‖∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H) (Fin.castSucc i) (v i)‖ =
      √(∑ i : Fin n, ‖v i‖ ^ 2) := by
  classical
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_castSucc]
  congr 1
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply,
    Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [(Fin.castSucc_ne_last _).symm]

/-- Burkholder's square function inequality without the separability of `H`. -/
theorem squareFunction_of_martingale {X : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ := by
  classical
  -- the Hilbert space `H^{n+1}` with the `ℓ²` norm, and its coordinate embeddings
  let L : Fin (n + 1) → H →L[ℝ] PiLp 2 (fun _ : Fin (n + 1) => H) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => H)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => H) i)
  have hL : ∀ i x, L i x = PiLp.single 2 (β := fun _ : Fin (n + 1) => H) i x := fun _ _ => rfl
  -- `A_m = X_{n ∧ m} e_n` and `Z_m = Σ_{i < n} (X_{(i+1) ∧ m} − X_{i ∧ m}) e_i`
  set A : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) :=
    fun m ω => L (Fin.last n) (X (min n m) ω) with hAdef
  set Z : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) := fun m ω =>
    ∑ i : Fin n, L (Fin.castSucc i) (X (min ((i : ℕ) + 1) m) ω - X (min (i : ℕ) m) ω) with hZdef
  have hA : Martingale A ℱ μ := martingale_clm (martingale_stopped hX n) _
  have hZ : Martingale Z ℱ μ := martingale_finset_sum Finset.univ fun i _ =>
    martingale_clm ((martingale_stopped hX ((i : ℕ) + 1)).sub (martingale_stopped hX i)) _
  have hA0 : ∀ ω, A 0 ω = 0 := fun ω => by simp [hAdef, hX0]
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by simp [hZdef]
  -- the increments: `‖dZ_m‖ = ‖dA_m‖ = 1_{m < n} ‖dX_m‖`
  have hinc : ∀ m ω, ‖Z (m + 1) ω - Z m ω‖ = ‖A (m + 1) ω - A m ω‖ := by
    intro m ω
    have hw : ∀ i : ℕ, (X (min (i + 1) (m + 1)) ω - X (min i (m + 1)) ω) -
        (X (min (i + 1) m) ω - X (min i m) ω) = if i = m then X (m + 1) ω - X m ω else 0 := by
      intro i
      rcases lt_trichotomy i m with h | rfl | h
      · rw [ite_eq_right h.ne, min_eq_left (by omega : i + 1 ≤ m + 1),
          min_eq_left (by omega : i ≤ m + 1),
          min_eq_left (by omega : i + 1 ≤ m), min_eq_left (by omega : i ≤ m)]
        simp
      · rw [ite_eq_left rfl, min_self, min_eq_left (by omega : i ≤ i + 1),
          min_eq_right (by omega : i ≤ i + 1), min_self]
        simp
      · rw [ite_eq_right h.ne', min_eq_right (by omega : m + 1 ≤ i + 1),
          min_eq_right (by omega : m + 1 ≤ i), min_eq_right (by omega : m ≤ i + 1),
          min_eq_right (by omega : m ≤ i)]
        simp
    have hZd : Z (m + 1) ω - Z m ω = ∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H)
        (Fin.castSucc i) (if (i : ℕ) = m then X (m + 1) ω - X m ω else 0) := by
      simp only [hZdef, ← Finset.sum_sub_distrib, hL, ← PiLp.single_sub, hw]
    rw [hZd, norm_sum_single]
    simp only [hAdef, hL, ← PiLp.single_sub, PiLp.norm_single]
    rcases lt_or_ge m n with h | h
    · rw [min_eq_right (by omega : m + 1 ≤ n), min_eq_right h.le]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 =
          ‖X (m + 1) ω - X m ω‖ ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => ‖(if i = m then X (m + 1) ω - X m ω else 0)‖ ^ 2) n,
          Finset.sum_eq_single m (fun b _ hb => by simp [hb])
            (fun hm => absurd (Finset.mem_range.2 h) hm)]
        simp
      rw [this, Real.sqrt_sq (norm_nonneg _)]
    · rw [min_eq_left (by omega : n ≤ m + 1), min_eq_left h]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have := i.isLt
          simp [show (i : ℕ) ≠ m by omega]
      rw [this]; simp
  -- at time `n`: `‖A_n‖ = ‖X_n‖` and `‖Z_n‖ = 𝒮_n X`
  have hAn : ∀ ω, ‖A n ω‖ = ‖X n ω‖ := fun ω => by simp [hAdef, hL, PiLp.norm_single]
  have hZn : ∀ ω, ‖Z n ω‖ = √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2) := by
    intro ω
    simp only [hZdef, hL]
    rw [norm_sum_single, ← Fin.sum_univ_eq_sum_range (fun k => ‖X (k + 1) ω - X k ω‖ ^ 2) n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have := i.isLt
    rw [min_eq_left (by omega : (i : ℕ) + 1 ≤ n), min_eq_left (by omega : (i : ℕ) ≤ n)]
  have eA : eLpNorm (A n) (ENNReal.ofReal p) μ = eLpNorm (X n) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (A n) (hA.integrable n).aestronglyMeasurable,
      ← eLpNorm_norm (X n) (hX.integrable n).aestronglyMeasurable]
    simp only [hAn]
  have eZ : eLpNorm (Z n) (ENNReal.ofReal p) μ = eLpNorm
      (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (Z n) (hZ.integrable n).aestronglyMeasurable]
    simp only [hZn]
  refine ⟨?_, ?_⟩
  · have := inequality_of_subordinate hp hZ hA hZ0 hA0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).le) n
    rwa [eZ, eA] at this
  · have := inequality_of_subordinate hp hA hZ hA0 hZ0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).ge) n
    rwa [eZ, eA] at this

/-- **Burkholder's square function inequality** (Burkholder 1988, Theorem 3.1; Osękowski, *Sharp
martingale and semimartingale inequalities* (2012), Theorem 8.6): for a martingale `X` with values
in a separable real Hilbert space, started at `0`, `p > 1` and
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`,
`‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.

The argument of Burkholder 1988, proof of Theorem 3.1: in the Hilbert space `H^{n+1}` with the
`ℓ²` norm, the martingale `Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k` (Burkholder's `G`) has
`‖Z_n‖ = 𝒮_n X` and `‖dZ_m‖ = ‖dX_{m+1}‖ 1_{m < n}`, which is also the norm of the increments of
`A_m = X_{n ∧ m} e_n` (Burkholder's `F`); each of the two martingales is differentially subordinate
to the other, and Theorem 1.1 (`inequality_of_subordinate`) applies to both pairs.

Up to time `n`, Burkholder's `F` and `G` take values in the first `n + 1` coordinates of `ℓ²_H`;
the proof works in that subspace, `H^{n+1}` (`PiLp 2`), with `X` in the last coordinate rather
than the first and both martingales stopped at `n`, which leaves them unchanged up to time `n`.
The separability of `H` is not used. -/
theorem squareFunction {X : ℕ → Ω → H} [TopologicalSpace.SeparableSpace H] {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  squareFunction_of_martingale hp hX hX0 n

end SquareFunction

end BanachProbability.Burkholder
