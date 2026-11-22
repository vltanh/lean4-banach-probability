module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Martingale.Basic

/-!
# Burkholder's method for differentially subordinate martingales, and the integration method

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012: Theorem 2.7 (p. 16–17) and the integration method of Section 2.3 (p. 21–22).

A martingale `g` is differentially subordinate to a martingale `f` if `|dg_n| ≤ |df_n|` almost
surely for `n ≥ 0`, with `df_0 = f_0`, `dg_0 = g_0` (Definition 2.1). To prove `E V (f_n, g_n) ≤ 0`
for such pairs it is enough to have a function `U` and, for every `(x, y)`, continuous linear
functionals `A (x, y)`, `B (x, y)` with

* 1° `U ≥ V`,
* 2° `U (x + h, y + k) ≤ U (x, y) + ⟨A (x, y), h⟩ + ⟨B (x, y), k⟩` for `|k| ≤ |h|`,
* 3° `U (x, y) ≤ 0` for `|y| ≤ |x|`,

and the integrability (2.10).

## Main results

* `supermartingale_of_subordinate`: by 2°, `U (f_n, g_n)` is a supermartingale.
* `integral_nonpos_of_subordinate` (Theorem 2.7): `E V (f_n, g_n) ≤ 0`.
* `integrable_and_integral_setIntegral_nonpos` (the integration method): if
  `U (x, y) = ∫_0^∞ k (t) u (x / t, y / t) dt` with a kernel `k ≥ 0`, if
  `E u (f_n / t, g_n / t) ≤ 0` for every `t > 0` (Theorem 2.7 for `u`) and
  `E ∫_0^∞ k (t) |u (f_n / t, g_n / t)| dt < ∞`, then `E U (f_n, g_n) ≤ 0`, by Fubini's theorem.

The space `E` is any real Banach space. The source takes it separable and `U`, `A`, `B` Borel, which
makes `U (f_n, g_n)`, `A (f_n, g_n)`, `B (f_n, g_n)` adapted; here the adaptedness is the
hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BanachProbability.Osekowski

section Method

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : ℕ → Ω → E} {U V : E → E → ℝ}
  {A B : E → E → E →L[ℝ] ℝ}

/-- `⟨T, X_{n+1} − X_n⟩` is integrable if `|T| |X_{n+1} − X_n|` is, as in (2.10). -/
private theorem integrable_apply_increment {X : ℕ → Ω → E} (hX : Martingale X ℱ μ) {n : ℕ}
    {T : Ω → E →L[ℝ] ℝ} (hT : StronglyMeasurable[ℱ n] T)
    (hint : Integrable (fun ω => ‖T ω‖ * ‖X (n + 1) ω - X n ω‖) μ) :
    Integrable (fun ω => T ω (X (n + 1) ω - X n ω)) μ :=
  hint.mono' ((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (hT.mono (ℱ.le n)).aestronglyMeasurable
    ((hX.integrable (n + 1)).sub (hX.integrable n)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => (T ω).le_opNorm _)

/-- `E [⟨T, X_{n+1} − X_n⟩ | ℱ_n] = ⟨T, E [X_{n+1} − X_n | ℱ_n]⟩ = 0` for an `ℱ_n`-measurable `T`
(the pull-out property of the conditional expectation). -/
private theorem condExp_apply_increment {X : ℕ → Ω → E} (hX : Martingale X ℱ μ) {n : ℕ}
    [SigmaFinite (μ.trim (ℱ.le n))] {T : Ω → E →L[ℝ] ℝ} (hT : StronglyMeasurable[ℱ n] T)
    (hint : Integrable (fun ω => T ω (X (n + 1) ω - X n ω)) μ) :
    μ[fun ω => T ω (X (n + 1) ω - X n ω) | ℱ n] =ᵐ[μ] 0 := by
  have h1 := condExp_bilin_of_aestronglyMeasurable_left (m := ℱ n) (μ := μ)
    (g := X (n + 1) - X n) (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hT.aestronglyMeasurable hint
    ((hX.integrable (n + 1)).sub (hX.integrable n))
  filter_upwards [h1, condExp_sub (hX.integrable (n + 1)) (hX.integrable n) (ℱ n),
    hX.condExp_ae_eq n.le_succ] with ω h1 h2 h3
  simp only [ContinuousLinearMap.id_apply, Pi.sub_apply] at h1
  rw [h1, h2, Pi.sub_apply, h3, condExp_of_stronglyMeasurable (ℱ.le n) (hX.stronglyAdapted n)
    (hX.integrable n), sub_self, map_zero, Pi.zero_apply]

variable [IsFiniteMeasure μ]

/-- The supermartingale property (the proof of Theorem 2.7): if `U` satisfies 2° and `g` is
differentially subordinate to `f`, then `U (f_n, g_n)` is a supermartingale. By 2°,
`U (f_{n+1}, g_{n+1}) ≤ U (f_n, g_n) + ⟨A (f_n, g_n), df_{n+1}⟩ + ⟨B (f_n, g_n), dg_{n+1}⟩`, and the
conditional expectations of the linear terms vanish. The integrability is (2.10). -/
theorem supermartingale_of_subordinate (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (h2 : ∀ x y h k : E, ‖k‖ ≤ ‖h‖ → U (x + h) (y + k) ≤ U x y + A x y h + B x y k)
    (hU : StronglyAdapted ℱ fun n ω => U (f n ω) (g n ω))
    (hA : StronglyAdapted ℱ fun n ω => A (f n ω) (g n ω))
    (hB : StronglyAdapted ℱ fun n ω => B (f n ω) (g n ω))
    (hUi : ∀ n, Integrable (fun ω => U (f n ω) (g n ω)) μ)
    (hAi : ∀ n, Integrable (fun ω => ‖A (f n ω) (g n ω)‖ * ‖f (n + 1) ω - f n ω‖) μ)
    (hBi : ∀ n, Integrable (fun ω => ‖B (f n ω) (g n ω)‖ * ‖g (n + 1) ω - g n ω‖) μ) :
    Supermartingale (fun n ω => U (f n ω) (g n ω)) ℱ μ := by
  refine supermartingale_nat hU hUi fun n => ?_
  have hIA := integrable_apply_increment hf (hA n) (hAi n)
  have hIB := integrable_apply_increment hg (hB n) (hBi n)
  have hmono : μ[fun ω => U (f (n + 1) ω) (g (n + 1) ω) | ℱ n] ≤ᵐ[μ]
      μ[((fun ω => U (f n ω) (g n ω)) + fun ω => A (f n ω) (g n ω) (f (n + 1) ω - f n ω)) +
        fun ω => B (f n ω) (g n ω) (g (n + 1) ω - g n ω) | ℱ n] := by
    refine condExp_mono (hUi (n + 1)) (((hUi n).add hIA).add hIB) ?_
    filter_upwards [hsub n] with ω hω
    simpa only [add_sub_cancel, Pi.add_apply] using
      h2 (f n ω) (g n ω) (f (n + 1) ω - f n ω) (g (n + 1) ω - g n ω) hω
  filter_upwards [hmono, condExp_add ((hUi n).add hIA) hIB (ℱ n), condExp_add (hUi n) hIA (ℱ n),
    condExp_apply_increment hf (hA n) hIA, condExp_apply_increment hg (hB n) hIB]
    with ω h h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, condExp_of_stronglyMeasurable (ℱ.le n) (hU n)
    (hUi n)] at h
  simpa using h

/-- **Burkholder's method for differentially subordinate martingales** (Theorem 2.7): if `U` and
`V` satisfy 1°, 2°, 3°, and `g` is differentially subordinate to `f`, with the integrability (2.10),
then `E V (f_n, g_n) ≤ E U (f_n, g_n) ≤ E U (f_0, g_0) ≤ 0`. -/
theorem integral_nonpos_of_subordinate (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖)
    (h1 : ∀ x y, V x y ≤ U x y)
    (h2 : ∀ x y h k : E, ‖k‖ ≤ ‖h‖ → U (x + h) (y + k) ≤ U x y + A x y h + B x y k)
    (h3 : ∀ x y, ‖y‖ ≤ ‖x‖ → U x y ≤ 0)
    (hU : StronglyAdapted ℱ fun n ω => U (f n ω) (g n ω))
    (hA : StronglyAdapted ℱ fun n ω => A (f n ω) (g n ω))
    (hB : StronglyAdapted ℱ fun n ω => B (f n ω) (g n ω))
    (hVi : ∀ n, Integrable (fun ω => V (f n ω) (g n ω)) μ)
    (hUi : ∀ n, Integrable (fun ω => U (f n ω) (g n ω)) μ)
    (hAi : ∀ n, Integrable (fun ω => ‖A (f n ω) (g n ω)‖ * ‖f (n + 1) ω - f n ω‖) μ)
    (hBi : ∀ n, Integrable (fun ω => ‖B (f n ω) (g n ω)‖ * ‖g (n + 1) ω - g n ω‖) μ) (n : ℕ) :
    ∫ ω, V (f n ω) (g n ω) ∂μ ≤ 0 := by
  have hS := supermartingale_of_subordinate hf hg hsub h2 hU hA hB hUi hAi hBi
  have h0 : ∫ ω, U (f n ω) (g n ω) ∂μ ≤ ∫ ω, U (f 0 ω) (g 0 ω) ∂μ := by
    simpa only [setIntegral_univ] using hS.setIntegral_le n.zero_le MeasurableSet.univ
  calc ∫ ω, V (f n ω) (g n ω) ∂μ ≤ ∫ ω, U (f n ω) (g n ω) ∂μ :=
        integral_mono (hVi n) (hUi n) fun ω => h1 _ _
    _ ≤ ∫ ω, U (f 0 ω) (g 0 ω) ∂μ := h0
    _ ≤ 0 := integral_nonpos_of_ae (hsub0.mono fun ω hω => h3 _ _ hω)

end Method

section Integration

/-- **The integration method** (Section 2.3), for functions of the norms `a = |f_n|`, `b = |g_n|`:
let `u` be a Borel function and `k ≥ 0` a Borel kernel, with `E u (a / t, b / t) ≤ 0` for every
`t > 0` and `E ∫_0^∞ |k (t) u (a / t, b / t)| dt < ∞`. Then
`U (a, b) = ∫_0^∞ k (t) u (a / t, b / t) dt` is integrable and `E U (a, b) ≤ 0`, by Fubini's
theorem. -/
theorem integrable_and_integral_setIntegral_nonpos {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [SFinite μ] {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    {u : ℝ → ℝ → ℝ} (hu : Measurable (Function.uncurry u)) {k : ℝ → ℝ} (hk : Measurable k)
    (hk0 : ∀ t, 0 < t → 0 ≤ k t) (hE : ∀ t, 0 < t → ∫ ω, u (a ω / t) (b ω / t) ∂μ ≤ 0)
    (hint : ∀ ω, IntegrableOn (fun t => k t * u (a ω / t) (b ω / t)) (Ioi 0))
    {C : Ω → ℝ} (hC : Integrable C μ)
    (hle : ∀ ω, ∫ t in Ioi 0, |k t * u (a ω / t) (b ω / t)| ≤ C ω) :
    Integrable (fun ω => ∫ t in Ioi 0, k t * u (a ω / t) (b ω / t)) μ ∧
      ∫ ω, (∫ t in Ioi 0, k t * u (a ω / t) (b ω / t)) ∂μ ≤ 0 := by
  have hmeas : Measurable fun z : Ω × ℝ => k z.2 * u (a z.1 / z.2) (b z.1 / z.2) :=
    (hk.comp measurable_snd).mul (hu.comp (((ha.comp measurable_fst).div measurable_snd).prodMk
      ((hb.comp measurable_fst).div measurable_snd)))
  have hprod : Integrable (fun z : Ω × ℝ => k z.2 * u (a z.1 / z.2) (b z.1 / z.2))
      (μ.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2
      ⟨Eventually.of_forall hint, hC.mono' ?_ (Eventually.of_forall fun ω => ?_)⟩
    · exact hmeas.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact hle ω
  refine ⟨hprod.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun ω (t : ℝ) => k t * u (a ω / t) (b ω / t)) hprod]
  refine setIntegral_nonpos measurableSet_Ioi fun t ht => ?_
  rw [integral_const_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (hk0 t ht) (hE t ht)

end Integration

end BanachProbability.Osekowski
