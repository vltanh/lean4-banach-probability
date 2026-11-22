module

public import BanachProbability.UMD.Hilbert
public import BanachProbability.UMD.Maurey.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `L^p` spaces of UMD spaces are UMD

For any measure space `(S, μ)`, any Banach space `B` and `p ∈ (1, ∞)`,
`UMD_p (L^p (μ; B)) ≤ UMD_p (B)`; in particular `UMD_p (L^p (μ; ℂ)) ≤ p* − 1` and the complex
`L^p (μ)` is UMD (Pisier, *Martingales in Banach spaces* (2016), Corollary 5.22, "by Fubini").

The proof is the dyadic one, which needs neither σ-finiteness nor joint measurability. A
Paley–Walsh martingale with values in `L^p (μ; B)` takes finitely many values; for every `s` the
evaluations `ε ↦ ξ_k (ε) (s)` of the representatives form a predictable `B`-valued family, and the
finitely many linear relations defining the Paley–Walsh sums and their transform hold off one null
set (`ulp_coeFn_paleyWalsh`), so for almost every `s` the transform commutes with evaluation. The
finite averages commute with the (lower) integral:
`E_ε ‖F (ε)‖_{L^p}^p = ∫ E_ε ‖F (ε) (s)‖^p dμ (s)`, and the dyadic bound of `B` applied pointwise
in `s` gives `UMD_p^Δ (L^p (μ; B)) ≤ UMD_p^Δ (B)` (`dyadicUMDConst_Lp_le`). Maurey's theorem gives
the full constants.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

section Helpers

/-- The `r`-th power of the cube `L^r` norm is the normalised sum of the `r`-th powers of the
extended norms: `(‖f‖_{L^r})^r = 2^{-N} Σ_ε ‖f (ε)‖ₑ^r`. -/
private theorem ulp_ofReal_lpNorm_rpow {E : Type*} [SeminormedAddCommGroup E] {N : ℕ}
    (f : (Fin N → Bool) → E) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) r f) ^ r =
      ((2 : ℝ≥0∞) ^ N)⁻¹ * ∑ ε, ‖f ε‖ₑ ^ r := by
  have hnn : ∀ ε, 0 ≤ ‖f ε‖ ^ r := fun ε => Real.rpow_nonneg (norm_nonneg _) _
  have havg : 0 ≤ avg fun ε => ‖f ε‖ ^ r := avg_nonneg hnn
  rw [SignCube.lpNorm, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg havg _) hr.le,
    ← Real.rpow_mul havg, one_div_mul_cancel hr.ne', Real.rpow_one, avg,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_sum_of_nonneg fun ε _ => hnn ε,
    ENNReal.div_eq_inv_mul, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  congr 1
  · refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le, ofReal_norm]

/-- The dyadic inequality `‖F‖_{L^r} ≤ β ‖G‖_{L^r}` on the cube, in terms of `r`-th powers:
`Σ_ε ‖F (ε)‖ₑ^r ≤ β^r Σ_ε ‖G (ε)‖ₑ^r`. -/
private theorem ulp_ofReal_lpNorm_le_iff {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {N : ℕ} (f : (Fin N → Bool) → E) (g : (Fin N → Bool) → F)
    {r : ℝ} (hr : 0 < r) (β : ℝ≥0∞) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) r f) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) r g) ↔
      ∑ ε, ‖f ε‖ₑ ^ r ≤ β ^ r * ∑ ε, ‖g ε‖ₑ ^ r := by
  rw [← ENNReal.rpow_le_rpow_iff hr, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ulp_ofReal_lpNorm_rpow f hr, ulp_ofReal_lpNorm_rpow g hr, mul_left_comm,
    ENNReal.mul_le_mul_iff_right (by simp) (by simp)]

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- The `p`-th power of the norm of `L^p (μ; E)`: `‖f‖ₑ^p = ∫ ‖f (s)‖ₑ^p dμ (s)`. -/
private theorem ulp_enorm_rpow (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (f : Lp E p μ) :
    ‖f‖ₑ ^ p.toReal = ∫⁻ s, ‖f s‖ₑ ^ p.toReal ∂μ := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (Lp.aestronglyMeasurable f),
    ← ENNReal.rpow_mul, one_div_mul_cancel (ENNReal.toReal_pos hp0 hpt).ne', ENNReal.rpow_one]

/-- A finite sum in `L^p (μ; E)` has, almost everywhere, the sum of the representatives as
representative. -/
private theorem ulp_coeFn_finsetSum {ι : Type*} (t : Finset ι) (g : ι → Lp E p μ) :
    ⇑(∑ i ∈ t, g i) =ᵐ[μ] ∑ i ∈ t, ⇑(g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero E p μ
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.rfl.add ih)

variable [NormedSpace ℝ E]

/-- Off one null set, evaluation commutes with the Paley–Walsh sums of an `L^p (μ; E)`-valued
family: `(Σ_{k<n} ε_k ζ_k (ε)) (s) = Σ_{k<n} ε_k ζ_k (ε) (s)` for every `ε`. -/
private theorem ulp_coeFn_paleyWalsh {N : ℕ} (ζ : Fin N → (Fin N → Bool) → Lp E p μ) (n : ℕ) :
    ∀ᵐ s ∂μ, ∀ ε, ((paleyWalsh ζ n ε : Lp E p μ) : S → E) s =
      paleyWalsh (fun k ε => (ζ k ε : S → E) s) n ε := by
  rw [ae_all_iff]
  intro ε
  have hsmul : ∀ᵐ s ∂μ, ∀ k : Fin N,
      (⇑(coin (ε k) • ζ k ε) : S → E) s = coin (ε k) • (ζ k ε : S → E) s := by
    rw [ae_all_iff]
    exact fun k => Lp.coeFn_smul _ _
  filter_upwards [ulp_coeFn_finsetSum μ _ fun k => coin (ε k) • ζ k ε, hsmul] with s h1 h2
  rw [paleyWalsh, h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => h2 k

end Helpers

/-- The dyadic Fubini step: a dyadic `UMD_p` constant of `B` is one of `L^p (μ; B)`
(`r = p.toReal`). -/
private theorem ulp_isDyadicUMDBound_Lp {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound B p.toReal β) : IsDyadicUMDBound (Lp B p μ) p.toReal β := by
  intro N ξ σ hξ hσ hσ1 n
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [ulp_ofReal_lpNorm_le_iff _ _ hr]
  simp_rw [ulp_enorm_rpow μ hp0 hpt]
  have hm : ∀ F : Lp B p μ, AEMeasurable (fun s => ‖F s‖ₑ ^ p.toReal) μ :=
    fun F => (Lp.aestronglyMeasurable F).enorm.pow_const _
  rw [← lintegral_finsetSum' _ fun ε _ => hm _, ← lintegral_finsetSum' _ fun ε _ => hm _,
    ← lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun ε _ => hm _)]
  have hsmul : ∀ᵐ s ∂μ, ∀ k ε, (⇑(σ k ε • ξ k ε) : S → B) s = σ k ε • (ξ k ε : S → B) s := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact fun ε => Lp.coeFn_smul _ _
  refine lintegral_mono_ae ?_
  filter_upwards [ulp_coeFn_paleyWalsh μ (fun k ε => σ k ε • ξ k ε) n,
    ulp_coeFn_paleyWalsh μ ξ n, hsmul] with s h1 h2 h3
  simp only [h1, h2, h3]
  -- pointwise in `s`, the dyadic bound of `B` for the representatives `ε ↦ ξ_k (ε) (s)`
  have hξs : IsPredictable fun k ε => (ξ k ε : S → B) s :=
    fun k ε ε' hk => congrArg (fun F : Lp B p μ => (F : S → B) s) (hξ k ε ε' hk)
  exact (ulp_ofReal_lpNorm_le_iff _ _ hr β).mp (h N _ σ hξs hσ hσ1 n)

/-- `UMD_p^Δ (L^p (μ; B)) ≤ UMD_p^Δ (B)`, for every measure `μ`. -/
theorem dyadicUMDConst_Lp_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    dyadicUMDConst (Lp B p μ) p.toReal ≤ dyadicUMDConst B p.toReal :=
  sInf_le_sInf fun _ hβ => ulp_isDyadicUMDBound_Lp μ p hp hpt hβ

/-- `1 < p.toReal` for `1 < p < ∞`. -/
private theorem ulp_one_lt_toReal {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ⊤) : 1 < p.toReal := by
  simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr hp

/-- `UMD_p (L^p (μ; B)) ≤ UMD_p (B)`, for every measure `μ` and every Banach space `B`. -/
theorem umdConst_Lp_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp B p μ) p.toReal ≤ umdConst B p.toReal := by
  have hr := ulp_one_lt_toReal hp hpt
  rw [← dyadicUMDConst_eq_umdConst hr, ← dyadicUMDConst_eq_umdConst hr]
  exact dyadicUMDConst_Lp_le μ p hp hpt

/-- The complex `L^p (μ)` is UMD with `UMD_p (L^p (μ; ℂ)) ≤ p* − 1`, for every measure `μ`. -/
theorem umdConst_Lp_complex_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp ℂ p μ) p.toReal ≤ ENNReal.ofReal (pStar p.toReal - 1) :=
  (umdConst_Lp_le μ p hp hpt).trans
    (umdConst_le_of_innerProductSpace (H := ℂ) (ulp_one_lt_toReal hp hpt))

/-- **`L^p` is UMD** (Pisier 2016, Corollary 5.22): for every measure space and `p ∈ (1, ∞)`, the
complex `L^p (μ)` has `UMD_p (L^p (μ)) < ∞`. -/
theorem umdConst_Lp_complex_lt_top (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ⊤) :
    umdConst (Lp ℂ p μ) p.toReal < ⊤ :=
  (umdConst_Lp_complex_le μ p hp hpt).trans_lt ENNReal.ofReal_lt_top

end BanachProbability
