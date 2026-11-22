module

public import BanachProbability.Martingale.Osekowski.Integral
public import BanachProbability.Martingale.Osekowski.Method

/-!
# The moment inequality for differentially subordinate martingales

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012: the inequality (3.59) of Theorem 3.5 (ii), `‖g‖_p ≤ (p* − 1) ‖f‖_p` for a
martingale `g` differentially subordinate to `f`, by the integration method (p. 53–54 for
`1 < p ≤ 2`, p. 58 for `p > 2`).

## Main results

* `integrable_and_integral_burkholderU_nonpos`: `E U_p (f_n, g_n) ≤ 0` for `p ≠ 2`.
* `integral_rpow_le_of_subordinate`: `E |g_n|^p ≤ (p* − 1)^p E |f_n|^p` for `f` in `L^p`.
* `eLpNorm_le_of_subordinate` (Theorem 3.5 (ii)): `‖g_n‖_{L^p} ≤ (p* − 1) ‖f_n‖_{L^p}`.

## The proof

For `p = 2` the inequality is the orthogonality of the martingale differences
(`integral_sq_sub_sq_nonpos`). For `p ≠ 2` let `V_p (x, y) = |y|^p − (p* − 1)^p |x|^p` and let `U_p`
be Burkholder's function.

1. 1° `U_p ≥ V_p` is `Burkholder.burkholderU_ge`: by homogeneity, for `|x| + |y| = 1` and as a
   function `F` of `s = |x|`. (For `1 < p < 2` the book has the convex and the concave part of `F`
   exchanged; with the right order, `F ≥ 0` also needs `F (1) ≥ 0`, which is
   `(p − 1)^{p−1} p^{2−p} ≤ 1`, and for `p > 2` it needs `F (0) ≥ 0`, the reverse inequality: both
   are proved there.)
2. `U_p (x, y) = ∫_0^∞ k (t) u (x / t, y / t) dt` with `k (t) = c t^{p−1}` and `u = U₁` (3.6) for
   `1 < p < 2`, `u = U_∞` (3.12) for `p > 2` (`Martingale/Osekowski/Integral.lean`). Theorem 2.7
   gives `E u (f_n / t, g_n / t) ≤ 0` (`integral_uOne_nonpos`, `integral_uInfty_nonpos`), so
   `E U_p (f_n, g_n) ≤ 0` by Fubini's theorem, which (3.14) and (3.15) justify, since
   `f_n, g_n ∈ L^p`.

As in the book, `g` may start anywhere with `‖g_0‖ ≤ ‖f_0‖`. The inequality is stated at a fixed
time `n`, rather than for `‖·‖_p = sup_n ‖·‖_{L^p}`, which is equivalent; the separability of the
Hilbert space is not used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace RealInnerProductSpace

namespace BanachProbability.Osekowski

/-! ### Martingales stopped at a deterministic time, and their moments -/

section Moments

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A martingale stopped at the deterministic time `j`. -/
theorem martingale_min [IsFiniteMeasure μ] {X : ℕ → Ω → E} (hX : Martingale X ℱ μ) (j : ℕ) :
    Martingale (fun m => X (min j m)) ℱ μ := by
  refine martingale_nat (fun m => (hX.stronglyAdapted (min j m)).mono (ℱ.mono (min_le_right _ _)))
    (fun m => hX.integrable _) fun m => ?_
  rcases le_or_gt j m with h | h
  · simp only [min_eq_left h, min_eq_left (h.trans (Nat.le_succ m))]
    rw [condExp_of_stronglyMeasurable (ℱ.le m) ((hX.stronglyAdapted j).mono (ℱ.mono h))
      (hX.integrable j)]
  · simp only [min_eq_right h.le, min_eq_right (Nat.succ_le_of_lt h)]
    exact (hX.condExp_ae_eq (Nat.le_succ m)).symm

end Moments

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [NormedAddCommGroup H]

/-- If `g` is differentially subordinate to `f` and `f_n ∈ L^p` for every `n`, then `g_n ∈ L^p`:
`|g_n| ≤ Σ |dg_k| ≤ Σ |df_k|`. -/
private theorem memLp_of_subordinate {f g : ℕ → Ω → H} {q : ℝ≥0∞}
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (hf : ∀ n, MemLp (f n) q μ) (n : ℕ) : MemLp (g n) q μ := by
  induction n with
  | zero => exact (hf 0).of_le (hgm 0) hsub0
  | succ n ih =>
    have hd : MemLp (g (n + 1) - g n) q μ := ((hf (n + 1)).sub (hf n)).of_le
      ((hgm (n + 1)).sub (hgm n)) (by simpa only [Pi.sub_apply] using hsub n)
    simpa only [add_sub_cancel] using ih.add hd

private theorem integrable_rpow_of_memLp {W : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hW : MemLp W (ENNReal.ofReal p) μ) (hWnn : ∀ ω, 0 ≤ W ω) :
    Integrable (fun ω => W ω ^ p) μ := by
  have h := hW.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at h
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_of_nonneg (hWnn ω)]

variable [InnerProductSpace ℝ H] [CompleteSpace H] [IsProbabilityMeasure μ] {f g : ℕ → Ω → H}

/-! ### Theorem 2.7 for `U₁`, for `U_∞` and for `|y|² − |x|²` -/

/-- **Theorem 2.7 for `U₁`**: `E U₁ (f_n, g_n) ≤ 0` if `g` is differentially subordinate to `f`.
The integrability (2.10) holds since `|U₁ (x, y)| ≤ 1 + 2 |x|` and `A`, `B` are bounded. -/
private theorem integral_uOne_nonpos (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖) (n : ℕ) :
    ∫ ω, uOne ‖f n ω‖ ‖g n ω‖ ∂μ ≤ 0 := by
  have hU : StronglyAdapted ℱ fun n ω => uOne ‖f n ω‖ ‖g n ω‖ := fun n =>
    (measurable_uOne.comp ((hf.stronglyAdapted n).norm.measurable.prodMk
      (hg.stronglyAdapted n).norm.measurable)).stronglyMeasurable
  have hA : StronglyAdapted ℱ fun n ω => innerSL ℝ (uOneA (f n ω) (g n ω)) := fun n =>
    (innerSL ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uOneA (hf.stronglyAdapted n) (hg.stronglyAdapted n))
  have hB : StronglyAdapted ℱ fun n ω => innerSL ℝ (uOneB (f n ω) (g n ω)) := fun n =>
    (innerSL ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uOneB (hf.stronglyAdapted n) (hg.stronglyAdapted n))
  have hUi : ∀ n, Integrable (fun ω => uOne ‖f n ω‖ ‖g n ω‖) μ := fun n =>
    ((integrable_const 1).add ((hf.integrable n).norm.const_mul 2)).mono'
      ((hU n).mono (ℱ.le n)).aestronglyMeasurable
      (Eventually.of_forall fun ω => abs_uOne_le_one_add (norm_nonneg _) (norm_nonneg _))
  refine integral_nonpos_of_subordinate hf hg hsub0 hsub (V := fun x y => uOne ‖x‖ ‖y‖)
    (U := fun x y => uOne ‖x‖ ‖y‖) (A := fun x y => innerSL ℝ (uOneA x y))
    (B := fun x y => innerSL ℝ (uOneB x y)) (fun _ _ => le_rfl) (fun x y h k hk => uOne_le hk)
    (fun x y hxy => uOne_nonpos (norm_nonneg y) hxy) hU hA hB hUi hUi (fun n => ?_) (fun n => ?_) n
  · refine (((hf.integrable (n + 1)).sub (hf.integrable n)).norm.const_mul 2).mono'
      (((hA n).mono (ℱ.le n)).norm.aestronglyMeasurable.mul
        ((hf.integrable (n + 1)).sub (hf.integrable n)).norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_right (norm_uOneA_le _ _) (norm_nonneg _)
  · refine (((hg.integrable (n + 1)).sub (hg.integrable n)).norm.const_mul 2).mono'
      (((hB n).mono (ℱ.le n)).norm.aestronglyMeasurable.mul
        ((hg.integrable (n + 1)).sub (hg.integrable n)).norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_right (norm_uOneB_le _ _) (norm_nonneg _)

/-- **Theorem 2.7 for `U_∞`**: `E U_∞ (f_n, g_n) ≤ 0` if `f_n ∈ L²` for every `n` and `g` is
differentially subordinate to `f`. The integrability (2.10) follows from (3.15), `|A| ≤ 2 |x|` and
`|B| ≤ 2 |y| + 2`. -/
private theorem integral_uInfty_nonpos (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (hf2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) : ∫ ω, uInfty ‖f n ω‖ ‖g n ω‖ ∂μ ≤ 0 := by
  have hg2 := memLp_of_subordinate (fun n => (hg.integrable n).aestronglyMeasurable) hsub0 hsub hf2
  have hU : StronglyAdapted ℱ fun n ω => uInfty ‖f n ω‖ ‖g n ω‖ := fun n =>
    (measurable_uInfty.comp ((hf.stronglyAdapted n).norm.measurable.prodMk
      (hg.stronglyAdapted n).norm.measurable)).stronglyMeasurable
  have hA : StronglyAdapted ℱ fun n ω => innerSL ℝ (uInftyA (f n ω) (g n ω)) := fun n =>
    (innerSL ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uInftyA (hf.stronglyAdapted n) (hg.stronglyAdapted n))
  have hB : StronglyAdapted ℱ fun n ω => innerSL ℝ (uInftyB (f n ω) (g n ω)) := fun n =>
    (innerSL ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uInftyB (hf.stronglyAdapted n) (hg.stronglyAdapted n))
  have hUi : ∀ n, Integrable (fun ω => uInfty ‖f n ω‖ ‖g n ω‖) μ := fun n =>
    (((integrable_const 1).add (hf2 n).norm.integrable_sq).add (hg2 n).norm.integrable_sq).mono'
      ((hU n).mono (ℱ.le n)).aestronglyMeasurable
      (Eventually.of_forall fun ω => abs_uInfty_le (norm_nonneg _))
  refine integral_nonpos_of_subordinate hf hg hsub0 hsub (V := fun x y => uInfty ‖x‖ ‖y‖)
    (U := fun x y => uInfty ‖x‖ ‖y‖) (A := fun x y => innerSL ℝ (uInftyA x y))
    (B := fun x y => innerSL ℝ (uInftyB x y)) (fun _ _ => le_rfl) (fun x y h k hk => uInfty_le hk)
    (fun x y hxy => uInfty_nonpos hxy) hU hA hB hUi hUi (fun n => ?_) (fun n => ?_) n
  · refine ((hf2 n).norm.integrable_sq.add ((hf2 (n + 1)).sub (hf2 n)).norm.integrable_sq).mono'
      (((hA n).mono (ℱ.le n)).norm.aestronglyMeasurable.mul
        ((hf2 (n + 1)).sub (hf2 n)).norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
    simp only [Pi.add_apply, Pi.sub_apply]
    nlinarith [norm_uInftyA_le (f n ω) (g n ω), norm_nonneg (f (n + 1) ω - f n ω),
      sq_nonneg (‖f n ω‖ - ‖f (n + 1) ω - f n ω‖)]
  · refine (((hg2 n).norm.integrable_sq.const_mul 2).add
      (((hg2 (n + 1)).sub (hg2 n)).norm.integrable_sq.add (integrable_const 2))).mono'
      (((hB n).mono (ℱ.le n)).norm.aestronglyMeasurable.mul
        ((hg2 (n + 1)).sub (hg2 n)).norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity), innerSL_apply_norm]
    simp only [Pi.add_apply, Pi.sub_apply]
    nlinarith [norm_uInftyB_le (f n ω) (g n ω), norm_nonneg (g (n + 1) ω - g n ω),
      sq_nonneg (‖g n ω‖ + 1 - ‖g (n + 1) ω - g n ω‖), sq_nonneg (‖g n ω‖ - 1)]

/-- The case `p = 2` (p. 25): `E |g_n|² ≤ E |f_n|²` if `f_n ∈ L²` for every `n` and `g` is
differentially subordinate to `f`, by the orthogonality of the martingale differences: Theorem 2.7
for `|y|² − |x|²`, with `A = −2 x`, `B = 2 y`. -/
private theorem integral_sq_sub_sq_nonpos (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (hf2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) : ∫ ω, (‖g n ω‖ ^ 2 - ‖f n ω‖ ^ 2) ∂μ ≤ 0 := by
  have hg2 := memLp_of_subordinate (fun n => (hg.integrable n).aestronglyMeasurable) hsub0 hsub hf2
  have hUi : ∀ n, Integrable (fun ω => ‖g n ω‖ ^ 2 - ‖f n ω‖ ^ 2) μ := fun n =>
    (hg2 n).norm.integrable_sq.sub (hf2 n).norm.integrable_sq
  have hi : ∀ {X : ℕ → Ω → H}, (∀ n, MemLp (X n) 2 μ) → ∀ (c : ℝ) n,
      Integrable (fun ω => ‖innerSL ℝ (c • X n ω)‖ * ‖X (n + 1) ω - X n ω‖) μ :=
    fun hX c n => by
      simp only [innerSL_apply_norm, norm_smul, mul_assoc]
      exact ((hX n).norm.integrable_mul ((hX (n + 1)).sub (hX n)).norm).const_mul ‖c‖
  refine integral_nonpos_of_subordinate hf hg hsub0 hsub (V := fun x y => ‖y‖ ^ 2 - ‖x‖ ^ 2)
    (U := fun x y => ‖y‖ ^ 2 - ‖x‖ ^ 2) (A := fun x _ => innerSL ℝ ((-2 : ℝ) • x))
    (B := fun _ y => innerSL ℝ ((2 : ℝ) • y)) (fun _ _ => le_rfl) (fun x y h k hk => ?_)
    (fun x y hxy => sub_nonpos.2 (pow_le_pow_left₀ (norm_nonneg y) hxy 2))
    (fun n => ((hg.stronglyAdapted n).norm.pow 2).sub ((hf.stronglyAdapted n).norm.pow 2))
    (fun n => (innerSL ℝ).continuous.comp_stronglyMeasurable ((hf.stronglyAdapted n).const_smul _))
    (fun n => (innerSL ℝ).continuous.comp_stronglyMeasurable ((hg.stronglyAdapted n).const_smul _))
    hUi hUi (hi hf2 _) (hi hg2 _) n
  have hk2 : ‖k‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg k) hk 2
  rw [norm_add_sq_real, norm_add_sq_real, innerSL_apply_apply, innerSL_apply_apply,
    real_inner_smul_left, real_inner_smul_left]
  linarith

/-! ### The integration method -/

/-- **The integration method for `U_p`** (p. 54, 58): for `p ≠ 2`, if `f_n ∈ L^p` for every `n` and
`g` is differentially subordinate to `f`, then `U_p (f_n, g_n)` is integrable and
`E U_p (f_n, g_n) ≤ 0`. For `1 < p < 2`, `U_p (x, y) = c ∫_0^∞ t^{p−1} U₁ (x / t, y / t) dt`, and
`E U₁ (f_n / t, g_n / t) ≤ 0` (Theorem 2.7 for `U₁` and the martingales `f / t`, `g / t`), so
`E U_p (f_n, g_n) ≤ 0` by Fubini's theorem, which (3.14) justifies; for `p > 2` it is the same with
`U_∞` and (3.15). -/
theorem integrable_and_integral_burkholderU_nonpos {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2)
    (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (hfp : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ) (n : ℕ) :
    Integrable (fun ω => Burkholder.burkholderU p ‖g n ω‖ ‖f n ω‖) μ ∧
      ∫ ω, Burkholder.burkholderU p ‖g n ω‖ ‖f n ω‖ ∂μ ≤ 0 := by
  have hp0 : 0 < p := by linarith
  have hgp := memLp_of_subordinate (fun n => (hg.integrable n).aestronglyMeasurable) hsub0 hsub hfp
  have ha : Measurable fun ω => ‖f n ω‖ := ((hf.stronglyAdapted n).mono (ℱ.le n)).norm.measurable
  have hb : Measurable fun ω => ‖g n ω‖ := ((hg.stronglyAdapted n).mono (ℱ.le n)).norm.measurable
  have hk : Measurable fun t : ℝ => t ^ (p - 1) := by fun_prop
  have hk0 : ∀ t : ℝ, 0 < t → 0 ≤ t ^ (p - 1) := fun t ht => Real.rpow_nonneg ht.le _
  -- the martingales `f / t`, `g / t`
  have hnorm : ∀ (X : ℕ → Ω → H) (t : ℝ), 0 < t → ∀ m ω, ‖(t⁻¹ • X) m ω‖ = ‖X m ω‖ / t :=
    fun X t ht m ω => by
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, norm_inv, Real.norm_of_nonneg ht.le,
        inv_mul_eq_div]
  have hsub0' : ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂μ, ‖(t⁻¹ • g) 0 ω‖ ≤ ‖(t⁻¹ • f) 0 ω‖ := fun t ht => by
    filter_upwards [hsub0] with ω hω
    rw [hnorm g t ht, hnorm f t ht]
    exact div_le_div_of_nonneg_right hω ht.le
  have hsub' : ∀ t : ℝ, ∀ m, ∀ᵐ ω ∂μ, ‖(t⁻¹ • g) (m + 1) ω - (t⁻¹ • g) m ω‖ ≤
      ‖(t⁻¹ • f) (m + 1) ω - (t⁻¹ • f) m ω‖ := fun t m => by
    filter_upwards [hsub m] with ω hω
    simp only [Pi.smul_apply, ← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)
  rcases lt_or_gt_of_ne hp2 with hp2 | hp2
  · -- `1 < p < 2`
    have hE : ∀ t : ℝ, 0 < t → ∫ ω, uOne (‖f n ω‖ / t) (‖g n ω‖ / t) ∂μ ≤ 0 := fun t ht => by
      simpa only [hnorm f t ht, hnorm g t ht] using
        integral_uOne_nonpos (hf.smul t⁻¹) (hg.smul t⁻¹) (hsub0' t ht) (hsub' t) n
    have hIf := integrable_rpow_of_memLp hp0 (hfp n).norm fun ω => norm_nonneg _
    have hIg := integrable_rpow_of_memLp hp0 (hgp n).norm fun ω => norm_nonneg _
    have hC : Integrable (fun ω => 2 / (p * (2 - p)) * (‖g n ω‖ ^ p + ‖f n ω‖ ^ p / (p - 1))) μ :=
      (hIg.add (hIf.div_const _)).const_mul _
    obtain ⟨h1, h2⟩ := integrable_and_integral_setIntegral_nonpos ha hb measurable_uOne hk hk0 hE
      (fun ω => (integrableOn_and_integral_uOne hp hp2 (norm_nonneg _) (norm_nonneg _)).1) hC
      fun ω => integral_abs_uOne_le hp hp2 (norm_nonneg _) (norm_nonneg _)
    simp only [burkholderU_eq_integral_uOne hp hp2 (norm_nonneg _) (norm_nonneg _)]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    refine mul_nonpos_of_nonneg_of_nonpos ?_ h2
    have : 0 ≤ 2 - p := by linarith
    positivity
  · -- `p > 2`
    have hle : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_ofNat 2]
      exact ENNReal.ofReal_le_ofReal hp2.le
    have hE : ∀ t : ℝ, 0 < t → ∫ ω, uInfty (‖f n ω‖ / t) (‖g n ω‖ / t) ∂μ ≤ 0 := fun t ht => by
      simpa only [hnorm f t ht, hnorm g t ht] using
        integral_uInfty_nonpos (hf.smul t⁻¹) (hg.smul t⁻¹) (hsub0' t ht) (hsub' t)
          (fun m => ((hfp m).mono_exponent hle).const_smul t⁻¹) n
    have hC : Integrable (fun ω => (1 / p + 1 / (p - 2)) * (‖f n ω‖ + ‖g n ω‖) ^ p) μ :=
      (integrable_rpow_of_memLp hp0 ((hfp n).norm.add (hgp n).norm) fun ω =>
        add_nonneg (norm_nonneg (f n ω)) (norm_nonneg (g n ω))).const_mul _
    obtain ⟨h1, h2⟩ := integrable_and_integral_setIntegral_nonpos ha hb measurable_uInfty hk hk0 hE
      (fun ω => (integrableOn_and_integral_uInfty hp2 (norm_nonneg _) (norm_nonneg _)).1) hC
      fun ω => integral_abs_uInfty_le hp2 (norm_nonneg _) (norm_nonneg _)
    simp only [burkholderU_eq_integral_uInfty hp2 (norm_nonneg _) (norm_nonneg _)]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    refine mul_nonpos_of_nonneg_of_nonpos ?_ h2
    have h3 : 0 ≤ p - 2 := by linarith
    have h4 : 0 ≤ p - 1 := by linarith
    positivity

/-- **`E V_p (f_n, g_n) ≤ 0`**, `V_p (x, y) = |y|^p − (p* − 1)^p |x|^p` (p. 53–54, 58): if
`f_n ∈ L^p` for every `n` and `g` is differentially subordinate to `f`. For `p ≠ 2`, by 1°
`V_p ≤ U_p` (`Burkholder.burkholderU_ge`) and `E U_p (f_n, g_n) ≤ 0`; for `p = 2`, by
orthogonality. -/
theorem integral_rpow_le_of_subordinate {p : ℝ} (hp : 1 < p) (hf : Martingale f ℱ μ)
    (hg : Martingale g ℱ μ) (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (hfp : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ) (n : ℕ) :
    ∫ ω, ‖g n ω‖ ^ p ∂μ ≤ (max p (p / (p - 1)) - 1) ^ p * ∫ ω, ‖f n ω‖ ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hgp := memLp_of_subordinate (fun n => (hg.integrable n).aestronglyMeasurable) hsub0 hsub hfp
  have hIf := integrable_rpow_of_memLp hp0 (hfp n).norm fun ω => norm_nonneg _
  have hIg := integrable_rpow_of_memLp hp0 (hgp n).norm fun ω => norm_nonneg _
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [ENNReal.ofReal_ofNat] at hfp
    have h := integral_sq_sub_sq_nonpos hf hg hsub0 hsub hfp n
    simp only [Real.rpow_two] at hIf hIg ⊢
    rw [integral_sub hIg hIf] at h
    norm_num
    linarith
  · obtain ⟨h1, h2⟩ := integrable_and_integral_burkholderU_nonpos hp hp2 hf hg hsub0 hsub hfp n
    have h3 := integral_mono (hIg.sub (hIf.const_mul ((max p (p / (p - 1)) - 1) ^ p))) h1
      fun ω => Burkholder.burkholderU_ge hp (norm_nonneg (g n ω)) (norm_nonneg (f n ω))
    rw [integral_sub' hIg (hIf.const_mul _), integral_const_mul] at h3
    linarith

/-- **Theorem 3.5 (ii)**, the inequality (3.59): if the martingale `g` is differentially subordinate
to the martingale `f` (values in a real Hilbert space) and `1 < p < ∞`, then
`‖g_n‖_{L^p} ≤ (p* − 1) ‖f_n‖_{L^p}`, `p* = max (p, p / (p − 1))`, for every `n`. If `‖f_n‖_p = ∞`
there is nothing to prove; otherwise `f` and `g` stopped at the time `n` are in `L^p`
(`f_k = E [f_n | ℱ_k]`), and `E V_p (f_n, g_n) ≤ 0` (`integral_rpow_le_of_subordinate`). That the
constant is the best possible is in `Martingale/Osekowski/Sharpness.lean`. -/
theorem eLpNorm_le_of_subordinate {p : ℝ} (hp : 1 < p) (hf : Martingale f ℱ μ)
    (hg : Martingale g ℱ μ) (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖) (n : ℕ) :
    eLpNorm (g n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hq0 : q ≠ 0 := by rw [hq, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  have hβ : 0 < max p (p / (p - 1)) - 1 := by have := le_max_left p (p / (p - 1)); linarith
  by_cases hft : eLpNorm (f n) q μ = ⊤
  · rw [hft, ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hβ)]
    exact le_top
  -- `f` and `g` stopped at the time `n`
  have hfn : MemLp (f n) q μ := memLp_iff.2 (lt_top_iff_ne_top.2 hft)
  have hfp : ∀ m, MemLp (f (min n m)) q μ := fun m =>
    (hfn.condExp (m := ℱ (min n m)) hq1).ae_eq (hf.condExp_ae_eq (min_le_left n m))
  have hsub' : ∀ m, ∀ᵐ ω ∂μ, ‖g (min n (m + 1)) ω - g (min n m) ω‖ ≤
      ‖f (min n (m + 1)) ω - f (min n m) ω‖ := fun m => by
    rcases le_or_gt n m with h | h
    · simp [min_eq_left h, min_eq_left (h.trans m.le_succ)]
    · simpa only [min_eq_right h.le, min_eq_right (Nat.succ_le_of_lt h)] using hsub m
  have hgn : MemLp (g n) q μ := by
    simpa only [min_self] using memLp_of_subordinate (f := fun m => f (min n m))
      (g := fun m => g (min n m)) (fun m => (hg.integrable _).aestronglyMeasurable)
      (by simpa using hsub0) hsub' hfp n
  have h := integral_rpow_le_of_subordinate hp (martingale_min hf n) (martingale_min hg n)
    (by simpa using hsub0) hsub' hfp n
  simp only [min_self] at h
  -- back to `L^p` norms
  rw [hgn.eLpNorm_eq_integral_rpow_norm hq0 hqt, hfn.eLpNorm_eq_integral_rpow_norm hq0 hqt, hqr,
    ← ENNReal.ofReal_mul hβ.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hf0 : 0 ≤ ∫ ω, ‖f n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hg0 : 0 ≤ ∫ ω, ‖g n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ ω, ‖g n ω‖ ^ p ∂μ) ^ p⁻¹
      ≤ ((max p (p / (p - 1)) - 1) ^ p * ∫ ω, ‖f n ω‖ ^ p ∂μ) ^ p⁻¹ :=
        Real.rpow_le_rpow hg0 h (inv_nonneg.2 hp0.le)
    _ = (max p (p / (p - 1)) - 1) * (∫ ω, ‖f n ω‖ ^ p ∂μ) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hβ.le _) hf0, Real.rpow_rpow_inv hβ.le hp0.ne']

end BanachProbability.Osekowski
