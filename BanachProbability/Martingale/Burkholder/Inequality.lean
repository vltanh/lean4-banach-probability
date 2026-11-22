module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
Ann. Probab. 12 (1984); A. Osękowski, *Sharp martingale and semimartingale inequalities* (2012),
Theorems 3.5 and 8.6. Both are proved here by Burkholder's method, the sources' standard
argument.

## Main results

* `inequality` (Burkholder 1984; Osękowski 2012, Theorem 3.5): for martingales `X`, `Y` with
  values in a separable real Hilbert space `H`, started at `0`, with
  `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` with `p* = max (p, p / (p − 1))`. The proof does not use
  the separability of `H`: `inequality_of_subordinate` is the same statement without it.
* `squareFunction` (Osękowski 2012, Theorem 8.6): `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`, `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`
  (`squareFunction_of_martingale` without separability).
* `burkholderU`: Burkholder's function
  `U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, written as a function of
  `s = |x|`, `r = |y|`; here `x` is the position of the subordinate martingale `X` and `y` that of
  the dominating one `Y`. `burkholderU_ge`: `U ≥ V`, `V (x, y) = |x|^p − (p* − 1)^p |y|^p`.

## The proof

1. `U ≥ V` (`burkholderU_ge`): for `r > 0`, `s ↦ U (s, r) − V (s, r)` vanishes at `s = (p* − 1) r`
   and its derivative is `≤ 0` before and `≥ 0` after that point (`sign_A`, `sign_B`); at `r = 0`,
   `U − V = (α − 1) s^p ≥ 0`.
2. The concavity property: for `|h| ≤ |k|`,
   `U (x + h, y + k) ≤ U (x, y) + ⟨U_x (x, y), h⟩ + ⟨U_y (x, y), k⟩` with
   `U_x (x, y) = (∂_s U (|x|, |y|) / |x|) x` (`0` if `x = 0`) and similarly `U_y`, because
   `t ↦ U (x + t h, y + t k)` is concave. For `p ≥ 2`, `U = α ψ (|x|, |y|)` with
   `ψ (s, r) = (s − (p − 1) r)(s + r)^{p−1}`; for `p ≤ 2`, `U = −α (p − 1)⁻¹ ψ (|y|, |x|)`. Let
   `G (t) = ψ (S (t), R (t))`, `S (t) = |x + t h|`, `R (t) = |y + t k|`. Off the (at most two)
   kinks `t₁`, `t₂` (`x + t₁ h = 0 ≠ h`, `y + t₂ k = 0 ≠ k`), `G` is twice differentiable with
   `G'' = p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S'' −
   (p − 1)(S + R)(K − H))`, `H = S'² + S S'' = |h|²`, `K = R'² + R R'' = |k|²`, `S'' ≥ 0`
   (`psi_hasDerivAt_two`, `line_facts`), which is `≤ 0` if `p ≥ 2`, `|h| ≤ |k|` and `≥ 0` if
   `p ≤ 2`, `|k| ≤ |h|` (`psi_two_sign`, `psi_line_smooth`): `G` is concave (resp. convex) on
   each of the at most three closed intervals cut out by `t₁`, `t₂`. At `t₁`, where
   `S (t) = |h| |t − t₁|`, the one-sided derivatives are `G'(t₁±) = ±ψ_s (0, R) |h| + ψ_r (0, R) R'`
   with `ψ_s (0, r) = −p (p − 2) r^{p−1}`, so `G'(t₁−) − G'(t₁+) = 2 p (p − 2) R^{p−1} |h|`, which
   is `≥ 0` for `p ≥ 2` and `≤ 0` for `p ≤ 2`; at `t₂`, `ψ_r (s, 0) = 0` and `G` is
   differentiable; if `t₁ = t₂`, `G (t) = |t − t₁|^p ψ (|h|, |k|)` and both one-sided derivatives
   vanish there (`psi_line_oneSided`). So the pieces glue into a function concave (resp. convex)
   on `ℝ` (`bkh_concaveOn_glue`, `psi_line`), and `G (1) − G (0) ≤ G'(0+) ≤ (G'(0−) + G'(0+)) / 2`
   (resp. `≥`), where the average is `ψ_s (|x|, |y|) ⟨x, h⟩ / |x| + ψ_r (|x|, |y|) ⟨y, k⟩ / |y|`
   (`psi_zigzag`).
3. `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` (`method_step`): integrate the concavity property at
   `(X_k, Y_k)` with increments `(dX_{k+1}, dY_{k+1})`; the linear terms
   `E ⟨U_x (X_k, Y_k), dX_{k+1}⟩` vanish by the pull-out property of `E [· | ℱ_k]`
   (`integral_inner_increment`). Hence `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`
   (`method`, `integral_burkholderU_nonpos`).
4. Integrability: if `‖Y_n‖_p = ∞` there is nothing to prove; otherwise `Y_k = E [Y_n | ℱ_k]` and
   `X_k = Σ_{j < k} dX_{j+1}` are in `L^p` for `k ≤ n`, and every term in step 3 is dominated by
   `C (|X_k| + |Y_k| + |dX_{k+1}| + |dY_{k+1}|)^p`.
5. The square function inequality, by the standard derivation from (1) (the `ℓ²(H)`-valued
   martingale `Σ_k dX_k e_k` and `X` are differentially subordinate to each other): in `H^{n+1}`
   with the `ℓ²` norm, `Z_m = Σ_{k < n} (X_{(k+1) ∧ m} − X_{k ∧ m}) e_k` and
   `A_m = X_{n ∧ m} e_n` are martingales started at `0` with
   `‖dZ_m‖ = ‖dA_m‖ = 1_{m < n} ‖dX_{m+1}‖`, `‖Z_n‖ = 𝒮_n X` and `‖A_n‖ = ‖X_n‖`; apply (1) to
   `(Z, A)` and to `(A, Z)`.

The method is Burkholder's standard special-function argument: `U ≥ V`, the zig-zag concavity of
`U`, the integration of the concavity along the martingale, and, for the square function, the
`ℓ²(H)`-valued martingale; the proof here follows it step by step, including the kinks of
`t ↦ U (x + t h, y + t k)` (where `x + t h = 0 ≠ h` or `y + t k = 0 ≠ k`), at which the concave
pieces are glued through their one-sided derivatives (`bkh_concaveOn_glue`, `psi_line`). One
point of mechanics: for the square function, the finite-dimensional `H^{n+1}` replaces `ℓ²(H)`
(`n` is fixed), the same argument.
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

/-- A continuous `f : ℝ → ℝ` that is twice differentiable with `f'' ≤ 0` off two points `a`, `b`,
and whose left derivative at `a` and at `b` is at least its right derivative there, is concave:
for `a ≤ b`, it is concave on `Iic a`, `Icc a b` and `Ici b` (`f'' ≤ 0` on their interiors), and
these pieces glue at `b`, then at `a` (`bkh_concaveOn_glue`). -/
private theorem concaveOn_univ_of_kinks {f f' : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hd : ∀ t, t ≠ a → t ≠ b → HasDerivAt f (f' t) t ∧ ∃ c, HasDerivAt f' c t ∧ c ≤ 0)
    (hk : ∀ t₀, t₀ = a ∨ t₀ = b → ∃ dl dr, HasDerivWithinAt f dl (Iic t₀) t₀ ∧
      HasDerivWithinAt f dr (Ici t₀) t₀ ∧ dr ≤ dl) :
    ConcaveOn ℝ univ f := by
  wlog hab : a ≤ b generalizing a b
  · exact this (fun t h1 h2 => hd t h2 h1) (fun t₀ ht => hk t₀ ht.symm) (not_le.1 hab).le
  have piece : ∀ D : Set ℝ, Convex ℝ D → (∀ t ∈ interior D, t ≠ a ∧ t ≠ b) →
      ConcaveOn ℝ D f := by
    intro D hD hint
    refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := deriv f') hD hf.continuousOn
      (fun t ht => (hd t (hint t ht).1 (hint t ht).2).1.hasDerivWithinAt) (fun t ht => ?_)
      (fun t ht => ?_)
    · obtain ⟨c, hc, -⟩ := (hd t (hint t ht).1 (hint t ht).2).2
      rw [hc.deriv]; exact hc.hasDerivWithinAt
    · obtain ⟨c, hc, hc0⟩ := (hd t (hint t ht).1 (hint t ht).2).2
      rwa [hc.deriv]
  have h1 := piece (Iic a) (convex_Iic a) (by
    rw [interior_Iic]; exact fun t ht => ⟨ht.ne, (ht.trans_le hab).ne⟩)
  have h2 := piece (Icc a b) (convex_Icc a b) (by
    rw [interior_Icc]; exact fun t ht => ⟨ht.1.ne', ht.2.ne⟩)
  have h3 := piece (Ici b) (convex_Ici b) (by
    rw [interior_Ici]; exact fun t ht => ⟨(hab.trans_lt ht).ne', ht.ne'⟩)
  obtain ⟨dla, dra, hla, hra, hda⟩ := hk a (Or.inl rfl)
  obtain ⟨dlb, drb, hlb, hrb, hdb⟩ := hk b (Or.inr rfl)
  have h23 : ConcaveOn ℝ (Ici a) f := bkh_concaveOn_glue (convex_Ici a)
    (by rwa [Ici_inter_Iic]) (by rwa [Ici_inter_Ici, sup_eq_right.2 hab]) hlb hrb hdb
  exact bkh_concaveOn_glue convex_univ (by rwa [univ_inter]) (by rwa [univ_inter]) hla hra hda

/-! ### The function `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}` and its derivatives -/

/-- `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}`; Burkholder's function is `α ψ (|x|, |y|)` for
`p ≥ 2` and `−α (p − 1)⁻¹ ψ (|y|, |x|)` for `p ≤ 2`. -/
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

/-- `∂ψ/∂s (0, r) = −p (p − 2) r^{p−1}`: `≤ 0` for `p ≥ 2`, `≥ 0` for `p ≤ 2`. -/
private theorem psiS_zero_sign {p r : ℝ} (hp : 1 < p) (hr : 0 ≤ r) :
    (2 ≤ p → psiS p 0 r ≤ 0) ∧ (p ≤ 2 → 0 ≤ psiS p 0 r) := by
  unfold psiS
  rw [zero_add, zero_sub]
  have h0 : 0 ≤ p * r ^ (p - 2) := mul_nonneg (by linarith) (Real.rpow_nonneg hr _)
  exact ⟨fun hp2 => mul_nonpos_of_nonneg_of_nonpos h0 (by nlinarith),
    fun hp2 => mul_nonneg h0 (by nlinarith)⟩

/-- `ψ` is homogeneous of degree `p`. -/
private theorem psi_mul {p c s r : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hsr : 0 ≤ s + r) :
    psi p (c * s) (c * r) = c ^ p * psi p s r := by
  unfold psi
  rw [show c * s + c * r = c * (s + r) by ring, Real.mul_rpow hc hsr,
    show c ^ p = c ^ (1 + (p - 1)) by ring_nf, Real.rpow_add' hc (by linarith), Real.rpow_one]
  ring

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

/-- The kink of `t ↦ |x + t h|`: at most one `t₁` with `x + t₁ h = 0` if `h ≠ 0`. -/
private theorem exists_kink (x h : H) : ∃ t₁ : ℝ, ∀ t : ℝ, x + t • h = 0 → h ≠ 0 → t = t₁ := by
  by_cases hk : ∃ t₁ : ℝ, x + t₁ • h = 0 ∧ h ≠ 0
  · obtain ⟨t₁, e₁, hh⟩ := hk
    refine ⟨t₁, fun t e _ => ?_⟩
    have : (t - t₁) • h = 0 := by
      rw [sub_smul, show t • h - t₁ • h = (x + t • h) - (x + t₁ • h) by abel, e, e₁, sub_zero]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hh)
  · exact ⟨0, fun t e hh => absurd ⟨t, e, hh⟩ hk⟩

/-- At a kink `t₀` of `t ↦ |x + t h|`, `x + u h = (u − t₀) h`. -/
private theorem line_eq_of_kink {x h : H} {t₀ : ℝ} (hz : x + t₀ • h = 0) (u : ℝ) :
    x + u • h = (u - t₀) • h := by
  rw [sub_smul, ← sub_eq_zero, show x + u • h - (u • h - t₀ • h) = x + t₀ • h by abel, hz]

/-- One-sided derivatives of `S (t) = |x + t h|` at any `t₀`: `S' (t₀) ∓ e`, `e ≥ 0`, with
`e = |h|` at a kink (`x + t₀ h = 0`, where `S' (t₀) = 0`) and `e = 0` elsewhere. -/
private theorem norm_line_oneSided (x h : H) (t₀ : ℝ) :
    ∃ e : ℝ, 0 ≤ e ∧ (x + t₀ • h ≠ 0 → e = 0) ∧
      HasDerivWithinAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t₀ - e) (Iic t₀) t₀ ∧
      HasDerivWithinAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t₀ + e) (Ici t₀) t₀ := by
  by_cases hz : x + t₀ • h = 0
  · have hS : ∀ u : ℝ, ‖x + u • h‖ = |u - t₀| * ‖h‖ := fun u => by
      rw [line_eq_of_kink hz u, norm_smul, Real.norm_eq_abs]
    have hD : lineD x h t₀ = 0 := by simp [lineD, hz]
    refine ⟨‖h‖, norm_nonneg _, fun h' => absurd hz h', ?_, ?_⟩
    · rw [hD, zero_sub]
      have hd : HasDerivAt (fun u : ℝ => (t₀ - u) * ‖h‖) (-‖h‖) t₀ := by
        simpa using ((hasDerivAt_id' t₀).const_sub t₀).mul_const ‖h‖
      refine hd.hasDerivWithinAt.congr (fun u hu => ?_) (by simp [hS])
      rw [hS, abs_of_nonpos (sub_nonpos.2 hu), neg_sub]
    · rw [hD, zero_add]
      have hd : HasDerivAt (fun u : ℝ => (u - t₀) * ‖h‖) ‖h‖ t₀ := by
        simpa using ((hasDerivAt_id' t₀).sub_const t₀).mul_const ‖h‖
      refine hd.hasDerivWithinAt.congr (fun u hu => ?_) (by simp [hS])
      rw [hS, abs_of_nonneg (sub_nonneg.2 hu)]
  · have hd := (line_facts x h (Or.inl hz)).1
    exact ⟨0, le_rfl, fun _ => rfl, by rw [sub_zero]; exact hd.hasDerivWithinAt,
      by rw [add_zero]; exact hd.hasDerivWithinAt⟩

/-- `G (t) = ψ (|x + t h|, |y + t k|)`, `ψ` along the line through `(x, y)` with direction
`(h, k)`. -/
private noncomputable def psiLine (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psi p ‖x + t • h‖ ‖y + t • k‖

/-- `G' (t) = ψ_s S' + ψ_r R'`, the derivative of `G` away from the kinks. -/
private noncomputable def psiLineD (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psiS p ‖x + t • h‖ ‖y + t • k‖ * lineD x h t + psiR p ‖x + t • h‖ ‖y + t • k‖ * lineD y k t

/-- Off the kinks (where `x + t h = 0` with `h ≠ 0`, or `y + t k = 0` with `k ≠ 0`), `G` is twice
differentiable, with `G'' ≤ 0` if `p ≥ 2`, `|h| ≤ |k|`, and `G'' ≥ 0` if `p ≤ 2`, `|k| ≤ |h|`
(`psi_hasDerivAt_two`, `psi_two_sign`, with `H = |h|²`, `K = |k|²`). -/
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

/-- **The one-sided derivatives of `G` at any point `t₀`** are `G' (t₀) ∓ e` (left, right), with
`e ≤ 0` if `p ≥ 2` and `e ≥ 0` if `p ≤ 2`: so `G' (t₀−) ≥ G' (t₀+)` for `p ≥ 2` and
`G' (t₀−) ≤ G' (t₀+)` for `p ≤ 2`, and their average is `G' (t₀) = ψ_s S' + ψ_r R'` (`psiLineD`,
with `S' (t₀) = 0` at a kink of `S`). At a kink of `S = |x + t h|` only, where
`S (t) = |h| |t − t₀|`, `e = ψ_s (0, R) |h|` with `ψ_s (0, r) = −p (p − 2) r^{p−1}`; at a kink of
`R = |y + t k|` only, `e = 0` since `ψ_r (s, 0) = 0`; at a common kink,
`G (t) = |t − t₀|^p ψ (|h|, |k|)` has both one-sided derivatives `0 = G' (t₀)`; elsewhere `G` is
differentiable. -/
private theorem psi_line_oneSided {p : ℝ} (hp : 1 < p) (x y h k : H) (t₀ : ℝ) :
    ∃ e : ℝ, HasDerivWithinAt (psiLine p x y h k) (psiLineD p x y h k t₀ - e) (Iic t₀) t₀ ∧
      HasDerivWithinAt (psiLine p x y h k) (psiLineD p x y h k t₀ + e) (Ici t₀) t₀ ∧
      (2 ≤ p → e ≤ 0) ∧ (p ≤ 2 → 0 ≤ e) := by
  by_cases h0 : x + t₀ • h = 0 ∧ y + t₀ • k = 0
  · -- both kinks at `t₀`: `G (t) = |t − t₀|^p ψ (|h|, |k|)`, whose one-sided derivatives are `0`
    have hG : ∀ u, psiLine p x y h k u = |u - t₀| ^ p * psi p ‖h‖ ‖k‖ := fun u => by
      rw [psiLine, line_eq_of_kink h0.1, line_eq_of_kink h0.2, norm_smul, norm_smul,
        Real.norm_eq_abs, psi_mul hp (abs_nonneg _) (by positivity)]
    have hD : psiLineD p x y h k t₀ = 0 := by simp [psiLineD, lineD, h0.1, h0.2]
    have hz : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (sub_pos.2 hp).ne'
    refine ⟨0, ?_, ?_, fun _ => le_rfl, fun _ => le_rfl⟩ <;> rw [hD]
    · have hd : HasDerivAt (fun u : ℝ => (t₀ - u) ^ p * psi p ‖h‖ ‖k‖) (0 - 0) t₀ := by
        convert (((hasDerivAt_id' t₀).const_sub t₀).rpow_const (p := p)
          (Or.inr hp.le)).mul_const (psi p ‖h‖ ‖k‖) using 1
        simp [hz]
      refine hd.hasDerivWithinAt.congr (fun u hu => ?_) (by simp [hG])
      rw [hG, abs_of_nonpos (sub_nonpos.2 hu), neg_sub]
    · have hd : HasDerivAt (fun u : ℝ => (u - t₀) ^ p * psi p ‖h‖ ‖k‖) (0 + 0) t₀ := by
        convert (((hasDerivAt_id' t₀).sub_const t₀).rpow_const (p := p)
          (Or.inr hp.le)).mul_const (psi p ‖h‖ ‖k‖) using 1
        simp [hz]
      refine hd.hasDerivWithinAt.congr (fun u hu => ?_) (by simp [hG])
      rw [hG, abs_of_nonneg (sub_nonneg.2 hu)]
  · have hW : 0 < ‖x + t₀ • h‖ + ‖y + t₀ • k‖ := by
      rcases not_and_or.1 h0 with h1 | h1
      · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 h1) (norm_nonneg _)
      · exact add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 h1)
    obtain ⟨ex, hex, hex0, hSl, hSr⟩ := norm_line_oneSided x h t₀
    obtain ⟨ey, -, hey0, hRl, hRr⟩ := norm_line_oneSided y k t₀
    -- `ψ_r (s, 0) = 0`: no jump at a kink of `|y + t k|`
    have hRe : psiR p ‖x + t₀ • h‖ ‖y + t₀ • k‖ * ey = 0 := by
      by_cases hy0 : y + t₀ • k = 0
      · simp [psiR, hy0]
      · rw [hey0 hy0, mul_zero]
    -- the jump `2 ψ_s (0, r) |h|` at a kink of `|x + t h|`
    have hSe : (2 ≤ p → psiS p ‖x + t₀ • h‖ ‖y + t₀ • k‖ * ex ≤ 0) ∧
        (p ≤ 2 → 0 ≤ psiS p ‖x + t₀ • h‖ ‖y + t₀ • k‖ * ex) := by
      by_cases hx0 : x + t₀ • h = 0
      · rw [hx0, norm_zero]
        have := psiS_zero_sign hp (norm_nonneg (y + t₀ • k))
        exact ⟨fun hp2 => mul_nonpos_of_nonpos_of_nonneg (this.1 hp2) hex,
          fun hp2 => mul_nonneg (this.2 hp2) hex⟩
      · rw [hex0 hx0, mul_zero]; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    refine ⟨psiS p ‖x + t₀ • h‖ ‖y + t₀ • k‖ * ex + psiR p ‖x + t₀ • h‖ ‖y + t₀ • k‖ * ey,
      ?_, ?_, fun hp2 => by rw [hRe, add_zero]; exact hSe.1 hp2,
      fun hp2 => by rw [hRe, add_zero]; exact hSe.2 hp2⟩
    · convert psi_hasDerivWithinAt (p := p) hSl hRl hW using 1
      · rfl
      · unfold psiLineD; ring
    · convert psi_hasDerivWithinAt (p := p) hSr hRr hW using 1
      · rfl
      · unfold psiLineD; ring

/-- **Concavity of `ψ` along lines** (Burkholder's method): `G (t) = ψ (|x + t h|, |y + t k|)` is
concave on `ℝ` if `p ≥ 2` and `|h| ≤ |k|`, and convex if `p ≤ 2` and `|k| ≤ |h|`. `G` is concave
(resp. convex) on each of the at most three intervals cut out by the kinks of `|x + t h|` and
`|y + t k|` (`psi_line_smooth`), and these pieces glue since the left derivative of `G` is at least
(resp. at most) its right derivative at the kinks (`psi_line_oneSided`,
`concaveOn_univ_of_kinks`). If `h = k = 0`, `G` is constant. -/
private theorem psi_line {p : ℝ} (hp : 1 < p) (x y h k : H) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → ConcaveOn ℝ univ (psiLine p x y h k)) ∧
      ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → ConvexOn ℝ univ (psiLine p x y h k)) := by
  by_cases h0 : h = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have e : psiLine p x y (0 : H) 0 = fun _ => psi p ‖x‖ ‖y‖ := by funext t; simp [psiLine]
    rw [e]
    exact ⟨fun _ => concaveOn_const _ convex_univ, fun _ => convexOn_const _ convex_univ⟩
  have hcont : Continuous (psiLine p x y h k) := by
    have h1 : Continuous fun t : ℝ => ‖x + t • h‖ := by fun_prop
    have h2 : Continuous fun t : ℝ => ‖y + t • k‖ := by fun_prop
    unfold psiLine psi
    exact (h1.sub (h2.const_mul _)).mul ((h1.add h2).rpow_const fun _ => Or.inr (by linarith))
  obtain ⟨t₁, ht₁⟩ := exists_kink x h
  obtain ⟨t₂, ht₂⟩ := exists_kink y k
  have off : ∀ t, t ≠ t₁ → t ≠ t₂ → (x + t • h ≠ 0 ∨ h = 0) ∧ (y + t • k ≠ 0 ∨ k = 0) ∧
      0 < ‖x + t • h‖ + ‖y + t • k‖ := fun t h1 h2 => by
    have hx : x + t • h ≠ 0 ∨ h = 0 := by
      by_cases hh : h = 0
      · exact Or.inr hh
      · exact Or.inl fun e => h1 (ht₁ t e hh)
    have hy : y + t • k ≠ 0 ∨ k = 0 := by
      by_cases hk : k = 0
      · exact Or.inr hk
      · exact Or.inl fun e => h2 (ht₂ t e hk)
    refine ⟨hx, hy, ?_⟩
    rcases not_and_or.1 h0 with hh | hk
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 (hx.resolve_right hh)) (norm_nonneg _)
    · exact add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 (hy.resolve_right hk))
  refine ⟨fun hA => concaveOn_univ_of_kinks (f' := psiLineD p x y h k) (a := t₁) (b := t₂) hcont
    (fun t h1 h2 => ?_) (fun t₀ _ => ?_), fun hB => ?_⟩
  · obtain ⟨hx, hy, hW⟩ := off t h1 h2
    obtain ⟨hd, c, hc, hc0, -⟩ := psi_line_smooth hp x y h k hx hy hW
    exact ⟨hd, c, hc, hc0 hA⟩
  · obtain ⟨e, hl, hr, he, -⟩ := psi_line_oneSided hp x y h k t₀
    exact ⟨_, _, hl, hr, by linarith [he hA.1]⟩
  · rw [← neg_concaveOn_iff]
    refine concaveOn_univ_of_kinks (f' := -psiLineD p x y h k) (a := t₁) (b := t₂) hcont.neg
      (fun t h1 h2 => ?_) (fun t₀ _ => ?_)
    · obtain ⟨hx, hy, hW⟩ := off t h1 h2
      obtain ⟨hd, c, hc, -, hc0⟩ := psi_line_smooth hp x y h k hx hy hW
      exact ⟨hd.neg, -c, hc.neg, by linarith [hc0 hB]⟩
    · obtain ⟨e, hl, hr, -, he⟩ := psi_line_oneSided hp x y h k t₀
      exact ⟨_, _, hl.neg, hr.neg, by linarith [he hB.1]⟩

/-- **The concavity property of Burkholder's function along lines** (for `ψ`), with the
"gradient" `(ψ_s (|x|, |y|) x / |x|, ψ_r (|x|, |y|) y / |y|)` (`0` where `x = 0`, resp. `y = 0`):
for `p ≥ 2` and `|h| ≤ |k|`, `ψ (|x + h|, |y + k|) ≤ ψ (|x|, |y|) + ⟨∇ψ, (h, k)⟩`; for `p ≤ 2` and
`|k| ≤ |h|`, the reverse inequality. `G (t) = ψ (|x + t h|, |y + t k|)` is concave (resp. convex)
on `ℝ`, glued from its smooth pieces at the kinks (`psi_line`), so
`G (1) − G (0) ≤ G' (0+) ≤ (G' (0−) + G' (0+)) / 2` (resp. `≥`), and the average of the one-sided
derivatives at `0` is `⟨∇ψ, (h, k)⟩` (`psi_line_oneSided`). -/
private theorem psi_zigzag {p : ℝ} (hp : 1 < p) (x y h k : H) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → psi p ‖x + h‖ ‖y + k‖ ≤
        psi p ‖x‖ ‖y‖ + (psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) + psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖))) ∧
    ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → psi p ‖x‖ ‖y‖ + (psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) +
        psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖)) ≤ psi p ‖x + h‖ ‖y + k‖) := by
  have e0 : psiLine p x y h k 0 = psi p ‖x‖ ‖y‖ := by simp [psiLine]
  have e1 : psiLine p x y h k 1 = psi p ‖x + h‖ ‖y + k‖ := by simp [psiLine]
  have eL : psiLineD p x y h k 0 =
      psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) + psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖) := by
    simp [psiLineD, lineD]
  obtain ⟨e, -, hr, he1, he2⟩ := psi_line_oneSided hp x y h k 0
  have hr' := hr.mono Ioi_subset_Ici_self
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · have := ((psi_line hp x y h k).1 hA).slope_le_of_hasDerivWithinAt_Ioi (mem_univ 0)
      (mem_univ 1) zero_lt_one hr'
    rw [slope_def_field, e0, e1, eL, sub_zero, div_one] at this
    linarith [he1 hA.1]
  · have := ((psi_line hp x y h k).2 hB).le_slope_of_hasDerivWithinAt_Ioi (mem_univ 0)
      (mem_univ 1) zero_lt_one hr'
    rw [slope_def_field, e0, e1, eL, sub_zero, div_one] at this
    linarith [he2 hB.1]

end Hilbert

/-! ### Burkholder's function and its majorization of `V (x, y) = |x|^p − (p* − 1)^p |y|^p` -/

/-- **Burkholder's function** (Osękowski 2012, (3.2)), as a function of `s = |x|`, `r = |y|`:
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

private theorem alpha_A {p : ℝ} (hp : 2 ≤ p) : 1 ≤ p * (1 - 1 / p) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := -(1 / p)) (by
    rw [neg_le_neg_iff, div_le_one hp0]; linarith) (p := p - 1) (by linarith)
  have e : 1 + (p - 1) * -(1 / p) = 1 / p := by field_simp; ring
  rw [e, ← sub_eq_add_neg] at h
  calc (1 : ℝ) = p * (1 / p) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp0.le

private theorem alpha_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) : 1 ≤ p * (1 / p) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h : (1 / p) ^ (1 : ℝ) ≤ (1 / p) ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hp0]; linarith)
      (by linarith)
  rw [Real.rpow_one] at h
  calc (1 : ℝ) = p * (1 / p) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp0.le

private theorem nonneg_of_deriv_sign {g g' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hcont : Continuous g) (hd : ∀ s, 0 < s → HasDerivAt g (g' s) s)
    (h1 : ∀ s, 0 < s → s < c → g' s ≤ 0) (h2 : ∀ s, c < s → 0 ≤ g' s) (hgc : g c = 0)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ g s := by
  rcases le_total s c with hsc | hsc
  · have hanti : AntitoneOn g (Icc 0 c) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
      hcont.continuousOn (fun x hx => by
        rw [interior_Icc] at hx; exact (hd x hx.1).hasDerivWithinAt)
      (fun x hx => by rw [interior_Icc] at hx; exact h1 x hx.1 hx.2)
    have := hanti ⟨hs, hsc⟩ ⟨hc.le, le_rfl⟩ hsc
    linarith
  · have hmono : MonotoneOn g (Ici c) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici c)
      hcont.continuousOn (fun x hx => by
        rw [interior_Ici] at hx; exact (hd x (hc.trans hx)).hasDerivWithinAt)
      (fun x hx => by rw [interior_Ici] at hx; exact h2 x hx)
    have := hmono self_mem_Ici hsc hsc
    linarith

private theorem continuous_psi_left {p : ℝ} (hp : 1 < p) (r : ℝ) :
    Continuous fun s => psi p s r := by
  unfold psi
  exact (continuous_id.sub continuous_const).mul
    ((continuous_id.add continuous_const).rpow_const fun _ => Or.inr (by linarith))

private theorem continuous_psi_right {p : ℝ} (hp : 1 < p) (r : ℝ) :
    Continuous fun s => psi p r s := by
  unfold psi
  exact (continuous_const.sub (continuous_const.mul continuous_id)).mul
    ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr (by linarith))

private theorem psi_self_zero {p r : ℝ} (hr : 0 ≤ r) (hp : 1 < p) :
    psi p 0 r = -(p - 1) * r ^ p := by
  unfold psi
  rw [zero_add, show r ^ p = r ^ ((p - 1) + 1) by ring_nf, Real.rpow_add' hr (by linarith),
    Real.rpow_one]
  ring

private theorem psi_zero_right {p s : ℝ} (hs : 0 ≤ s) (hp : 1 < p) : psi p s 0 = s ^ p := by
  unfold psi
  rw [add_zero, show s ^ p = s ^ ((p - 1) + 1) by ring_nf, Real.rpow_add' hs (by linarith),
    Real.rpow_one]
  ring

/-- The sign of `∂_s (U − V)` for `p ≥ 2`: with `W = s + r`, `v = s / W`, it is
`p W^{p−1} (α ((p − 1) v − (p − 2)) − v^{p−1})`, and the concave function
`v ↦ α ((p − 1) v − (p − 2)) − v^{p−1}` vanishes at `v = 1 − 1/p` and is `≥ 0` at `v = 1`. -/
private theorem sign_A {p s r : ℝ} (hp : 2 ≤ p) (hs : 0 < s) (hr : 0 < r) :
    (s < (p - 1) * r → p * (1 - 1 / p) ^ (p - 1) * psiS p s r - p * s ^ (p - 1) ≤ 0) ∧
    ((p - 1) * r < s → 0 ≤ p * (1 - 1 / p) ^ (p - 1) * psiS p s r - p * s ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hq : 1 ≤ p - 1 := by linarith
  have hα := alpha_A hp
  set A := (1 - 1 / p) ^ (p - 1) with hA
  have hA' : A = ((p - 1) / p) ^ (p - 1) := by rw [hA]; congr 1; field_simp
  set W := s + r with hW
  have hWpos : 0 < W := by linarith
  set v := s / W with hv
  have hv0 : 0 < v := div_pos hs hWpos
  have hv1 : v < 1 := by rw [hv, div_lt_one hWpos]; linarith
  have hsv : s = v * W := by rw [hv]; field_simp
  -- `∂_s (U − V) = p W^{p−1} m (v)`
  have key : p * A * psiS p s r - p * s ^ (p - 1) =
      p * W ^ (p - 1) * (p * A * ((p - 1) * v - (p - 2)) - v ^ (p - 1)) := by
    unfold psiS
    have e1 : (s + r) ^ (p - 2) = W ^ (p - 1) / W := by
      rw [← hW, show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one hWpos.ne']
    have e2 : s ^ (p - 1) = v ^ (p - 1) * W ^ (p - 1) := by
      rw [hsv, Real.mul_rpow hv0.le hWpos.le]
    rw [e1, e2]
    have hr' : r = W - v * W := by rw [← hsv]; ring
    rw [hr', hsv]
    field_simp
    ring
  have hφ := convexOn_rpow hq
  have hv₀ : (p - 1) / p < 1 := by rw [div_lt_one hp0]; linarith
  have hv₀pos : 0 < (p - 1) / p := div_pos (by linarith) hp0
  have hpW : 0 < p * W ^ (p - 1) := mul_pos hp0 (Real.rpow_pos_of_pos hWpos _)
  have e1 : p * (1 - (p - 1) / p) = 1 := by field_simp; ring
  have e2 : p * ((p - 1) / p - v) = p - 1 - p * v := by field_simp
  have e3 : p * (v - (p - 1) / p) = p * v - (p - 1) := by field_simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hvv : v < (p - 1) / p := by
      rw [hv, div_lt_div_iff₀ hWpos hp0]; linarith
    have sec := hφ.secant_mono_aux1 (x := v) (y := (p - 1) / p) (z := 1) (mem_Ici.2 hv0.le)
      (mem_Ici.2 zero_le_one) hvv hv₀
    simp only [Real.one_rpow, mul_one, ← hA'] at sec
    have key' : p * (1 - v) * A ≤ v ^ (p - 1) + (p - 1 - p * v) := by
      have := mul_le_mul_of_nonneg_left sec hp0.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2, one_mul] at this
      linarith
    have h3 : 0 ≤ (p - 1 - p * v) * (p * A - 1) := by
      apply mul_nonneg
      · have := mul_lt_mul_of_pos_left hvv hp0
        rw [mul_div_cancel₀ _ hp0.ne'] at this; linarith
      · linarith
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos hpW.le (by nlinarith)
  · have hvv : (p - 1) / p < v := by
      rw [hv, div_lt_div_iff₀ hp0 hWpos]; linarith
    have sec := hφ.secant_mono_aux1 (x := (p - 1) / p) (y := v) (z := 1) (mem_Ici.2 hv₀pos.le)
      (mem_Ici.2 zero_le_one) hvv hv1
    simp only [Real.one_rpow, mul_one, ← hA'] at sec
    have key' : v ^ (p - 1) ≤ p * (1 - v) * A + (p * v - (p - 1)) := by
      have := mul_le_mul_of_nonneg_left sec hp0.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e3, one_mul] at this
      linarith
    have h3 : 0 ≤ (p * v - (p - 1)) * (p * A - 1) := by
      apply mul_nonneg
      · have := mul_lt_mul_of_pos_left hvv hp0
        rw [mul_div_cancel₀ _ hp0.ne'] at this; linarith
      · linarith
    rw [key]
    exact mul_nonneg hpW.le (by nlinarith)

/-- The sign of `∂_s (U − V)` for `p ≤ 2`: it is `p s (((r + s)/p)^{p−2} − s^{p−2})`. -/
private theorem sign_B {p s r : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (hs : 0 < s) (hr : 0 < r) :
    (s < r / (p - 1) →
      -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1) ≤ 0) ∧
    (r / (p - 1) < s →
      0 ≤ -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have key : -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1) =
      p * s * (((r + s) / p) ^ (p - 2) - s ^ (p - 2)) := by
    unfold psiR
    have e1 : (1 / p) ^ (p - 1) = (1 / p) ^ (p - 2) * (1 / p) := by
      rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one (by positivity)]
    have e2 : ((r + s) / p) ^ (p - 2) = (1 / p) ^ (p - 2) * (r + s) ^ (p - 2) := by
      rw [div_eq_mul_one_div (r + s) p, mul_comm (r + s),
        Real.mul_rpow (by positivity) (by linarith)]
    have e3 : s ^ (p - 1) = s ^ (p - 2) * s := by
      rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hs.ne']
    rw [e1, e2, e3]
    field_simp
  have hrs : 0 < (r + s) / p := by positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : s ≤ (r + s) / p := by
      rw [le_div_iff₀ hp0]; rw [lt_div_iff₀ hq0] at h; linarith
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hs h' (by linarith)))
  · have h' : (r + s) / p ≤ s := by
      rw [div_le_iff₀ hp0]; rw [div_lt_iff₀ hq0] at h; linarith
    rw [key]
    exact mul_nonneg (by positivity)
      (sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos hrs h' (by linarith)))

/-- `U ≥ V` for `p ≥ 2`, in terms of `ψ`. -/
private theorem V_le_U_A {p s r : ℝ} (hp : 2 ≤ p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (p - 1) ^ p * r ^ p ≤ p * (1 - 1 / p) ^ (p - 1) * psi p s r := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hα := alpha_A hp
  set A := (1 - 1 / p) ^ (p - 1) with hA
  rcases hr.eq_or_lt with rfl | hr
  · rw [psi_zero_right hs hp1, Real.zero_rpow hp0.ne']
    nlinarith [Real.rpow_nonneg hs p]
  set g : ℝ → ℝ := fun s => p * A * psi p s r - s ^ p + (p - 1) ^ p * r ^ p with hg
  suffices 0 ≤ g s by simp only [hg] at this; linarith
  have hq : 1 ≤ p - 1 := by linarith
  set c := (p - 1) * r with hc
  have hcpos : 0 < c := mul_pos (by linarith) hr
  refine nonneg_of_deriv_sign (g' := fun s => p * A * psiS p s r - p * s ^ (p - 1)) hcpos
    ?_ ?_ ?_ ?_ ?_ hs
  · exact ((continuous_const.mul (continuous_psi_left hp1 r)).sub
      (continuous_id.rpow_const fun _ => Or.inr hp0.le)).add continuous_const
  · intro s hs
    have h := (((psi_hasDerivAt (p := p) (hasDerivAt_id' (x := s)) (hasDerivAt_const s r)
      (show 0 < s + r by linarith)).const_mul (p * A)).sub
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne'))).add_const ((p - 1) ^ p * r ^ p)
    convert h using 1; ring
  · intro s hs hsc
    exact (sign_A hp hs hr).1 hsc
  · intro s hsc
    exact (sign_A hp (hcpos.trans hsc) hr).2 hsc
  · simp only [hg, hc]
    unfold psi
    rw [Real.mul_rpow (by linarith) hr.le]; ring

/-- `U ≥ V` for `p ≤ 2`, in terms of `ψ`. -/
private theorem V_le_U_B {p s r : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (1 / (p - 1)) ^ p * r ^ p ≤ -(p * (1 / p) ^ (p - 1) / (p - 1)) * psi p r s := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have hα := alpha_B hp1 hp
  set α := p * (1 / p) ^ (p - 1) with hαdef
  rcases hr.eq_or_lt with rfl | hr
  · rw [psi_self_zero hs hp1, Real.zero_rpow hp0.ne']
    have e : -(α / (p - 1)) * (-(p - 1) * s ^ p) = α * s ^ p := by field_simp
    rw [e]
    nlinarith [Real.rpow_nonneg hs p]
  set g : ℝ → ℝ := fun s => -(α / (p - 1)) * psi p r s - s ^ p + (1 / (p - 1)) ^ p * r ^ p
    with hg
  suffices 0 ≤ g s by simp only [hg] at this; linarith
  set c := r / (p - 1) with hc
  have hcpos : 0 < c := div_pos hr hq0
  refine nonneg_of_deriv_sign (g' := fun s => -(α / (p - 1)) * psiR p r s - p * s ^ (p - 1))
    hcpos ?_ ?_ ?_ ?_ ?_ hs
  · exact ((continuous_const.mul (continuous_psi_right hp1 r)).sub
      (continuous_id.rpow_const fun _ => Or.inr hp0.le)).add continuous_const
  · intro s hs
    have h := (((psi_hasDerivAt (p := p) (hasDerivAt_const s r) (hasDerivAt_id' (x := s))
      (show 0 < r + s by linarith)).const_mul (-(α / (p - 1)))).sub
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne'))).add_const ((1 / (p - 1)) ^ p * r ^ p)
    convert h using 1; ring
  · intro s hs hsc
    exact (sign_B hp1 hp hs hr).1 hsc
  · intro s hsc
    exact (sign_B hp1 hp (hcpos.trans hsc) hr).2 hsc
  · simp only [hg, hc]
    unfold psi
    rw [Real.div_rpow hr.le hq0.le, Real.div_rpow zero_le_one hq0.le, Real.one_rpow]
    field_simp
    ring

/-- **Majorization** (Burkholder; Osękowski 2012, proof of Theorem 3.5): `V ≤ U`, that is
`|x|^p − (p* − 1)^p |y|^p ≤ U (x, y)`, with `s = |x|`, `r = |y|`. -/
theorem burkholderU_ge {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p ≤ burkholderU p s r := by
  rcases le_total 2 p with h2 | h2
  · rw [U_eq_A h2, max_eq_A h2]; exact V_le_U_A h2 hs hr
  · have hp0 : p - 1 ≠ 0 := by linarith
    rw [U_eq_B hp h2, max_eq_B hp h2, show p / (p - 1) - 1 = 1 / (p - 1) by field_simp; ring]
    exact V_le_U_B hp h2 hs hr

/-! ### Burkholder's method: `E U (X_n, Y_n) ≤ E U (X_{n−1}, Y_{n−1}) ≤ … ≤ U (0, 0) = 0` -/

section Method

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

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

/-- One step of Burkholder's method: `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)`. -/
private theorem method_step {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ)
    {F f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hzig : ∀ x y h k : H, ‖h‖ ≤ ‖k‖ →
      F ‖x + h‖ ‖y + k‖ ≤ F ‖x‖ ‖y‖ + f ‖x‖ ‖y‖ * ⟪x, h⟫ + g ‖x‖ ‖y‖ * ⟪y, k⟫)
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p)
    (hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |f s r| * s ≤ C * (s + r) ^ (p - 1))
    (hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |g s r| * r ≤ C * (s + r) ^ (p - 1)) {k : ℕ}
    (hsub : ∀ᵐ ω ∂μ, ‖X (k + 1) ω - X k ω‖ ≤ ‖Y (k + 1) ω - Y k ω‖)
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
        simpa only [add_sub_cancel] using this
    _ = ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ := by
        have hI01 : Integrable (fun ω => F ‖X k ω‖ ‖Y k ω‖ +
            f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫) μ := hI0.add hIX
        rw [integral_add hI01 hIY, integral_add hI0 hIX, h0X, h0Y]; ring

/-- Burkholder's method: `E U (X_n, Y_n) ≤ U (0, 0) = 0`. -/
private theorem method {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖)
    {F f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hzig : ∀ x y h k : H, ‖h‖ ≤ ‖k‖ →
      F ‖x + h‖ ‖y + k‖ ≤ F ‖x‖ ‖y‖ + f ‖x‖ ‖y‖ * ⟪x, h⟫ + g ‖x‖ ‖y‖ * ⟪y, k⟫)
    (hF0 : F 0 0 = 0)
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p)
    (hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |f s r| * s ≤ C * (s + r) ^ (p - 1))
    (hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |g s r| * r ≤ C * (s + r) ^ (p - 1)) (n : ℕ)
    (hXn : ∀ k ≤ n, MemLp (X k) (ENNReal.ofReal p) μ)
    (hYn : ∀ k ≤ n, MemLp (Y k) (ENNReal.ofReal p) μ) :
    ∫ ω, F ‖X n ω‖ ‖Y n ω‖ ∂μ ≤ 0 := by
  suffices ∀ k ≤ n, ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ ≤ 0 from this n le_rfl
  intro k
  induction k with
  | zero => intro _; simp [hX0, hY0, hF0]
  | succ k ih =>
    intro hk
    exact (method_step hp hX hY hC hF hf hg hzig hFb hfb hgb (hsub k) (hXn k (by omega))
      (hYn k (by omega)) (hXn (k + 1) hk) (hYn (k + 1) hk)).trans (ih (by omega))

end Method

/-! ### Bounds and measurability of Burkholder's function and of its gradient -/

private theorem abs_psiS_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : 0 < s + r) :
    |psiS p s r| ≤ p * (1 + |p - 2|) * (s + r) ^ (p - 1) := by
  unfold psiS
  have e : (s + r) ^ (p - 1) = (s + r) ^ (p - 2) * (s + r) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hsr.ne']
  have h1 : |s - (p - 2) * r| ≤ (1 + |p - 2|) * (s + r) := by
    have := abs_sub (s) ((p - 2) * r)
    rw [abs_mul, abs_of_nonneg hs, abs_of_nonneg hr] at this
    nlinarith [abs_nonneg (p - 2)]
  have h2 : 0 ≤ (s + r) ^ (p - 2) := Real.rpow_nonneg hsr.le _
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p), abs_of_nonneg h2, e]
  calc p * (s + r) ^ (p - 2) * |s - (p - 2) * r|
        ≤ p * (s + r) ^ (p - 2) * ((1 + |p - 2|) * (s + r)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) h2)
    _ = _ := by ring

private theorem abs_psiR_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : 0 < s + r) :
    |psiR p s r| ≤ p * (p - 1) * (s + r) ^ (p - 1) := by
  unfold psiR
  have e : (s + r) ^ (p - 1) = (s + r) ^ (p - 2) * (s + r) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hsr.ne']
  have h2 : 0 ≤ (s + r) ^ (p - 2) := Real.rpow_nonneg hsr.le _
  have hpp : 0 ≤ p * (p - 1) := mul_nonneg (by linarith) (by linarith)
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hpp, abs_of_nonneg hr, abs_of_nonneg h2, e]
  calc p * (p - 1) * r * (s + r) ^ (p - 2) ≤ p * (p - 1) * (s + r) * (s + r) ^ (p - 2) := by
        gcongr; linarith
    _ = _ := by ring

private theorem coef_bound {c a s B : ℝ} (hs : 0 ≤ s) (hB : 0 < s → |a| ≤ B) (hB0 : 0 ≤ B) :
    |c * (a / s)| * s ≤ |c| * B := by
  rcases hs.eq_or_lt with rfl | hs
  · simp only [div_zero, mul_zero, abs_zero]; exact mul_nonneg (abs_nonneg _) hB0
  · rw [abs_mul, abs_div, abs_of_pos hs, mul_assoc, div_mul_cancel₀ _ hs.ne']
    exact mul_le_mul_of_nonneg_left (hB hs) (abs_nonneg _)

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

/-! ### Burkholder's inequality -/

/-- `E U (X_n, Y_n) ≤ 0` for differentially subordinate martingales in `L^p`. -/
private theorem integral_burkholderU_nonpos {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ)
    (hXn : ∀ k ≤ n, MemLp (X k) (ENNReal.ofReal p) μ)
    (hYn : ∀ k ≤ n, MemLp (Y k) (ENNReal.ofReal p) μ) :
    ∫ ω, burkholderU p ‖X n ω‖ ‖Y n ω‖ ∂μ ≤ 0 := by
  set KU := p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * max p (p / (p - 1)) with hKU
  have hP1 : 1 < max p (p / (p - 1)) := lt_of_lt_of_le hp (le_max_left _ _)
  have hKU0 : 0 ≤ KU := mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)) (by linarith)
  have hS : 0 ≤ p * (1 + |p - 2|) := mul_nonneg (by linarith) (by positivity)
  have hR : 0 ≤ p * (p - 1) := mul_nonneg (by linarith) (by linarith)
  have hpow : ∀ s r : ℝ, 0 ≤ s → 0 ≤ r → 0 ≤ (s + r) ^ (p - 1) :=
    fun s r hs hr => Real.rpow_nonneg (by linarith) _
  rcases le_total 2 p with h2 | h2
  · -- `p ≥ 2`: `U = α ψ (|x|, |y|)`
    set α := p * (1 - 1 / p) ^ (p - 1) with hα
    have hα1 := alpha_A h2
    set C := KU + |α| * (p * (1 + |p - 2|)) + |α| * (p * (p - 1)) with hC
    have hCf : |α| * (p * (1 + |p - 2|)) ≤ C := by
      have := mul_nonneg (abs_nonneg α) hR; linarith
    have hCg : |α| * (p * (p - 1)) ≤ C := by
      have := mul_nonneg (abs_nonneg α) hS; linarith
    refine method hp hX hY hX0 hY0 hsub (F := burkholderU p)
      (f := fun s r => α * (psiS p s r / s)) (g := fun s r => α * (psiR p s r / r)) (C := C)
      (by have := mul_nonneg (abs_nonneg α) hS; have := mul_nonneg (abs_nonneg α) hR; linarith)
      (measurable_burkholderU p) ?_ ?_ ?_ (burkholderU_zero p) ?_ ?_ ?_ n hXn hYn
    · change Measurable fun z : ℝ × ℝ => α * (psiS p z.1 z.2 / z.1)
      unfold psiS; fun_prop
    · change Measurable fun z : ℝ × ℝ => α * (psiR p z.1 z.2 / z.2)
      unfold psiR; fun_prop
    · intro x y h k hhk
      have := (psi_zigzag hp x y h k).1 ⟨h2, hhk⟩
      rw [U_eq_A h2, U_eq_A h2]
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ α)
      calc α * psi p ‖x + h‖ ‖y + k‖ ≤ _ := this
        _ = _ := by ring
    · intro s r hs hr
      have := abs_burkholderU_le hp hs hr
      have h0 : 0 ≤ (s + r) ^ p := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg α) hS) h0,
        mul_nonneg (mul_nonneg (abs_nonneg α) hR) h0]
    · intro s r hs hr
      calc |α * (psiS p s r / s)| * s ≤ |α| * (p * (1 + |p - 2|) * (s + r) ^ (p - 1)) :=
            coef_bound hs (fun hs' => abs_psiS_le hp hs hr (by linarith))
              (mul_nonneg hS (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCf (hpow s r hs hr)
    · intro s r hs hr
      calc |α * (psiR p s r / r)| * r ≤ |α| * (p * (p - 1) * (s + r) ^ (p - 1)) :=
            coef_bound hr (fun hr' => abs_psiR_le hp hs hr (by linarith))
              (mul_nonneg hR (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCg (hpow s r hs hr)
  · -- `p ≤ 2`: `U = −c ψ (|y|, |x|)`
    set c := p * (1 / p) ^ (p - 1) / (p - 1) with hc
    have hc0 : 0 < c := div_pos (by linarith [alpha_B hp h2]) (by linarith)
    set C := KU + |-c| * (p * (p - 1)) + |-c| * (p * (1 + |p - 2|)) with hC
    have hCf : |-c| * (p * (p - 1)) ≤ C := by
      have := mul_nonneg (abs_nonneg (-c)) hS; linarith
    have hCg : |-c| * (p * (1 + |p - 2|)) ≤ C := by
      have := mul_nonneg (abs_nonneg (-c)) hR; linarith
    refine method hp hX hY hX0 hY0 hsub (F := burkholderU p)
      (f := fun s r => -c * (psiR p r s / s)) (g := fun s r => -c * (psiS p r s / r)) (C := C)
      (by have := mul_nonneg (abs_nonneg (-c)) hS; have := mul_nonneg (abs_nonneg (-c)) hR
          linarith)
      (measurable_burkholderU p) ?_ ?_ ?_ (burkholderU_zero p) ?_ ?_ ?_ n hXn hYn
    · change Measurable fun z : ℝ × ℝ => -c * (psiR p z.2 z.1 / z.1)
      unfold psiR; fun_prop
    · change Measurable fun z : ℝ × ℝ => -c * (psiS p z.2 z.1 / z.2)
      unfold psiS; fun_prop
    · intro x y h k hhk
      have h1 := (psi_zigzag hp y x k h).2 ⟨h2, hhk⟩
      rw [U_eq_B hp h2, U_eq_B hp h2, ← hc]
      have h3 := mul_le_mul_of_nonneg_left h1 hc0.le
      have e : -c * psi p ‖y‖ ‖x‖ + -c * (psiR p ‖y‖ ‖x‖ / ‖x‖) * ⟪x, h⟫ +
          -c * (psiS p ‖y‖ ‖x‖ / ‖y‖) * ⟪y, k⟫ = -(c * (psi p ‖y‖ ‖x‖ +
            (psiS p ‖y‖ ‖x‖ * (⟪y, k⟫ / ‖y‖) + psiR p ‖y‖ ‖x‖ * (⟪x, h⟫ / ‖x‖)))) := by ring
      rw [e]; linarith
    · intro s r hs hr
      have := abs_burkholderU_le hp hs hr
      have h0 : 0 ≤ (s + r) ^ p := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (-c)) hS) h0,
        mul_nonneg (mul_nonneg (abs_nonneg (-c)) hR) h0]
    · intro s r hs hr
      calc |-c * (psiR p r s / s)| * s ≤ |-c| * (p * (p - 1) * (s + r) ^ (p - 1)) :=
            coef_bound hs (fun hs' => by
              rw [add_comm s r]; exact abs_psiR_le hp hr hs (by linarith))
              (mul_nonneg hR (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCf (hpow s r hs hr)
    · intro s r hs hr
      calc |-c * (psiS p r s / r)| * r ≤ |-c| * (p * (1 + |p - 2|) * (s + r) ^ (p - 1)) :=
            coef_bound hr (fun hr' => by
              rw [add_comm s r]; exact abs_psiS_le hp hr hs (by linarith))
              (mul_nonneg hS (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCg (hpow s r hs hr)

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

/-- **Burkholder's inequality** (Burkholder 1984; Osękowski, *Sharp martingale and semimartingale
inequalities* (2012), Theorem 3.5): for martingales `X`, `Y` with values
in a separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`.

Proved by Burkholder's method, as in Osękowski's proof: Burkholder's function
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}` (`burkholderU`) majorizes
`V (x, y) = |x|^p − (p* − 1)^p |y|^p` (`burkholderU_ge`), and satisfies
`U (x + h, y + k) ≤ U (x, y) + ⟨U_x (x, y), h⟩ + ⟨U_y (x, y), k⟩` whenever `|h| ≤ |k|`, because
`t ↦ U (x + t h, y + t k)` is concave (computed through `ψ`: concave between the at most two
kinks, where `x + t h = 0 ≠ h` or `y + t k = 0 ≠ k`, by the sign of its second derivative, and the
pieces glue into a concave function at the kinks, where the left derivative is at least the right
derivative). Taking expectations and conditioning on
`ℱ_{n−1}` (pull-out property) gives `E U (X_n, Y_n) ≤ E U (X_{n−1}, Y_{n−1}) ≤ … ≤ U (0, 0) = 0`,
hence `E V (X_n, Y_n) ≤ 0`. If `‖Y_n‖_p = ∞` the right side is `∞`; otherwise every `Y_k`, `X_k`
(`k ≤ n`) is in `L^p`, which makes every term integrable. The separability of `H` is not used. -/
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

/-- **Burkholder's square function inequality** (Burkholder; Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 8.6): for a martingale `X`
with values in a separable real Hilbert space, started at `0`, `p > 1` and
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`,
`‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.

Proved by the standard derivation from Burkholder's inequality (`inequality`): in the
Hilbert space `H^{n+1}` with the `ℓ²` norm, the martingale `Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k`
has `‖Z_n‖ = 𝒮_n X` and `‖dZ_m‖ = ‖dX_{m+1}‖ 1_{m < n}`, which is also the norm of the increments
of `A_m = X_{n ∧ m} e_n`; each of the two martingales is differentially subordinate to the other.

Representation: the `ℓ²(H)`-valued martingale
`Σ_k dX_k e_k` is replaced by its truncation to `H^{n+1}` (`PiLp 2`), since `n` is fixed; the
argument is the same. The separability of `H` is not used. -/
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
