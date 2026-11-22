module

public import BanachProbability.UMD.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Complex UMD constants

For a complex Banach space `X` and `p ∈ (1, ∞)`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)` (Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Proposition 4.2.10; Yaroslavtsev, *Even Fourier multipliers and
martingale transforms in infinite dimensions*, Indag. Math. 29 (2018), Lemma 3.2), for general
filtrations.

The first inequality holds because real signs are unimodular complex numbers. The second is the
standard averaging argument: for `|λ| = 1`, `λ = e^{iθ}`,
`(1 / 2π) ∫₀^{2π} sgn cos (θ − φ) e^{iφ} dφ = (2 / π) e^{iθ}` (`integral_signOf_cos`), and for
each fixed `φ` the signs `σ_k^φ = sgn cos (θ_k − φ)` are predictable. The integral is replaced by
Riemann sums over `M` equally spaced angles, with a uniform error `O (1 / M)`
(`riemannSum_signOf_cos`), so that no joint measurability in `(φ, ω)` is needed:
`‖Σ λ_k dY_k‖_p ≤ (π / 2) max_φ ‖Σ σ_k^φ dY_k‖_p + O (1 / M) · 2n ‖Y_n‖_p`, and `M → ∞`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

/-- The sign of a real number, with `0 ↦ 1`: a `±1`-valued function. -/
noncomputable def signOf (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem signOf_eq_one_or_eq_neg_one (t : ℝ) : signOf t = 1 ∨ signOf t = -1 := by
  unfold signOf
  split_ifs <;> simp

private theorem cpx_measurable_signOf : Measurable signOf :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

private theorem cpx_norm_signOf (t : ℝ) : ‖(signOf t : ℂ)‖ = 1 := by
  unfold signOf
  split_ifs <;> simp

private theorem cpx_signOf_of_nonneg {t : ℝ} (ht : 0 ≤ t) : signOf t = 1 :=
  ite_eq_left_iff.2 fun h => absurd ht h

private theorem cpx_signOf_of_neg {t : ℝ} (ht : t < 0) : signOf t = -1 :=
  ite_eq_right_iff.2 fun h => absurd h (not_le.2 ht)

private theorem cpx_measurable_integrand (θ : ℝ) :
    Measurable fun φ : ℝ => (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I) :=
  (Complex.measurable_ofReal.comp (cpx_measurable_signOf.comp
    (Real.measurable_cos.comp (measurable_const.sub measurable_id)))).mul
    (Complex.measurable_exp.comp (Complex.measurable_ofReal.mul_const _))

private theorem cpx_norm_integrand (θ φ : ℝ) :
    ‖(signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I)‖ = 1 := by
  rw [norm_mul, cpx_norm_signOf, Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem cpx_intervalIntegrable (θ a b : ℝ) :
    IntervalIntegrable
      (fun φ : ℝ => (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I)) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (cpx_measurable_integrand θ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => by simp only [cpx_norm_integrand, norm_one, le_refl])

private theorem cpx_integral_exp (a b : ℝ) :
    ∫ φ in a..b, Complex.exp (φ * Complex.I) =
      (Complex.exp (b * Complex.I) - Complex.exp (a * Complex.I)) / Complex.I := by
  simp_rw [mul_comm _ Complex.I]
  exact integral_exp_mul_complex Complex.I_ne_zero

/-- `(1 / 2π) ∫₀^{2π} sgn cos (θ − φ) e^{iφ} dφ = (2 / π) e^{iθ}`. -/
theorem integral_signOf_cos (θ : ℝ) :
    ((2 * Real.pi)⁻¹ : ℂ) * ∫ φ in (0 : ℝ)..2 * Real.pi,
        (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I) =
      (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I) := by
  set F : ℝ → ℂ := fun φ => (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I)
    with hF
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro φ
    simp only [hF]
    rw [show θ - (φ + 2 * Real.pi) = θ - φ - 2 * Real.pi by ring, Real.cos_sub_two_pi]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h1 : ∫ φ in (θ - Real.pi / 2)..(θ + Real.pi / 2), F φ =
      ∫ φ in (θ - Real.pi / 2)..(θ + Real.pi / 2), Complex.exp (φ * Complex.I) := by
    refine intervalIntegral.integral_congr fun φ hφ => ?_
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hφ
    simp only [hF]
    rw [cpx_signOf_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.2], by linarith [hφ.1]⟩)]
    simp
  have h2 : ∫ φ in (θ + Real.pi / 2)..(θ + 3 * Real.pi / 2), F φ =
      ∫ φ in (θ + Real.pi / 2)..(θ + 3 * Real.pi / 2), -Complex.exp (φ * Complex.I) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (θ + 3 * Real.pi / 2)).ae_notMem volume] with φ hne hφ
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hφ
    have hlt : φ < θ + 3 * Real.pi / 2 := lt_of_le_of_ne hφ.2 hne
    simp only [hF]
    rw [← Real.cos_neg, neg_sub, cpx_signOf_of_neg
      (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hφ.1]) (by linarith))]
    simp
  have hsplit : ∫ φ in (0 : ℝ)..2 * Real.pi, F φ =
      (∫ φ in (θ - Real.pi / 2)..(θ + Real.pi / 2), F φ) +
        ∫ φ in (θ + Real.pi / 2)..(θ + 3 * Real.pi / 2), F φ := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (cpx_intervalIntegrable θ _ _ : IntervalIntegrable F volume _ _)
      (cpx_intervalIntegrable θ _ _ : IntervalIntegrable F volume _ _)]
    have := hper.intervalIntegral_add_eq 0 (θ - Real.pi / 2)
    rw [zero_add] at this
    rw [this]
    congr 1
    ring
  rw [hsplit, h1, h2, intervalIntegral.integral_neg, cpx_integral_exp, cpx_integral_exp]
  have e1 : Complex.exp (↑(θ + Real.pi / 2) * Complex.I) =
      Complex.exp (θ * Complex.I) * Complex.I := by
    rw [show (↑(θ + Real.pi / 2) : ℂ) * Complex.I = θ * Complex.I + Real.pi / 2 * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have e2 : Complex.exp (↑(θ - Real.pi / 2) * Complex.I) =
      Complex.exp (θ * Complex.I) * -Complex.I := by
    rw [show (↑(θ - Real.pi / 2) : ℂ) * Complex.I = θ * Complex.I + -Real.pi / 2 * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  have e3 : Complex.exp (↑(θ + 3 * Real.pi / 2) * Complex.I) =
      Complex.exp (θ * Complex.I) * -Complex.I := by
    rw [show (↑(θ + 3 * Real.pi / 2) : ℂ) * Complex.I =
        θ * Complex.I + -Real.pi / 2 * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I, Complex.exp_two_pi_mul_I,
      mul_one]
  rw [e1, e2, e3]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring_nf

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
private theorem cpx_norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add,
      show (b : ℂ) * Complex.I + Complex.I * ↑(a - b) = a * Complex.I by push_cast; ring]
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The sign of `cos (θ − ·)` is constant on `[x, y]` when the floor and the ceiling of
`a (φ) = (φ − θ) / π + 1 / 2` agree at `x < y`: the zeros of `cos (θ − ·)` are the points where
`a` is an integer, and by the intermediate value theorem a change of sign forces such a zero in
`[x, y]`, that is, an integer in `[a x, a y]`. -/
private theorem cpx_signOf_cos_eq {θ x y : ℝ} (hxy : x < y)
    (hfl : ⌊(x - θ) / Real.pi + 1 / 2⌋ = ⌊(y - θ) / Real.pi + 1 / 2⌋)
    (hce : ⌈(x - θ) / Real.pi + 1 / 2⌉ = ⌈(y - θ) / Real.pi + 1 / 2⌉)
    {φ : ℝ} (hφ : φ ∈ Set.Icc x y) :
    signOf (Real.cos (θ - φ)) = signOf (Real.cos (θ - x)) := by
  by_contra hne
  have h0 : (0 : ℝ) ∈ Set.uIcc (Real.cos (θ - x)) (Real.cos (θ - φ)) := by
    rcases le_or_gt 0 (Real.cos (θ - x)) with h1 | h1 <;>
      rcases le_or_gt 0 (Real.cos (θ - φ)) with h2 | h2
    · exact absurd (by rw [cpx_signOf_of_nonneg h1, cpx_signOf_of_nonneg h2]) hne
    · exact Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2⟩)
    · exact absurd (by rw [cpx_signOf_of_neg h1, cpx_signOf_of_neg h2]) hne
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc
    (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn h0
  rw [Set.uIcc_of_le hφ.1] at hz
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 hz0
  have hk' : θ - z = (2 * k + 1) * Real.pi / 2 := hk
  have hπ := Real.pi_pos
  have haz : (z - θ) / Real.pi + 1 / 2 = ((-k : ℤ) : ℝ) := by
    push_cast
    field_simp
    linarith
  have hxz : (x - θ) / Real.pi + 1 / 2 ≤ ((-k : ℤ) : ℝ) := by
    rw [← haz]
    gcongr
    exact hz.1
  have hzy : ((-k : ℤ) : ℝ) ≤ (y - θ) / Real.pi + 1 / 2 := by
    rw [← haz]
    gcongr
    exact hz.2.trans hφ.2
  have hxy' : (x - θ) / Real.pi + 1 / 2 < (y - θ) / Real.pi + 1 / 2 := by gcongr
  have h1 : ((-k : ℤ) : ℝ) ≤ (x - θ) / Real.pi + 1 / 2 :=
    (Int.cast_le.2 (hfl ▸ Int.le_floor.2 hzy)).trans (Int.floor_le _)
  have h2 : ⌈(y - θ) / Real.pi + 1 / 2⌉ = -k := by
    rw [← hce, le_antisymm hxz h1, Int.ceil_intCast]
  have h3 := Int.le_ceil ((y - θ) / Real.pi + 1 / 2)
  rw [h2] at h3
  linarith

/-- The Riemann sums of `φ ↦ sgn cos (θ − φ) e^{iφ}` over `M` equally spaced angles converge to
`(2 / π) e^{iθ}` uniformly in `θ`, with error `O (1 / M)` (both `|cos|` and `sgn · sin` are of
bounded variation).

The proof gives `C = 2π + 8`. With `h = 2π / M` and `I_j = [jh, (j + 1) h]`, the sum is compared
with `(1 / 2π) Σ_j ∫_{I_j}` of the integrand (`integral_signOf_cos`): on `I_j` the integrand
differs from its value at `jh` by at most `h` when `cos (θ − ·)` keeps its sign on `I_j`, and by
at most `2` in any case. The sign can change on `I_j` only if `a (φ) = (φ − θ) / π + 1 / 2` takes
an integer value on `I_j`, which happens for at most
`Σ_j ((⌊a⌋ + ⌈a⌉) ((j + 1) h) − (⌊a⌋ + ⌈a⌉) (jh)) = 4` indices `j`. -/
theorem riemannSum_signOf_cos : ∃ C : ℝ, ∀ M : ℕ, 0 < M → ∀ θ : ℝ,
    ‖(M : ℂ)⁻¹ * ∑ j : Fin M, (signOf (Real.cos (θ - 2 * Real.pi * j / M)) : ℂ) *
        Complex.exp ((2 * Real.pi * j / M : ℝ) * Complex.I) -
      (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ C / M := by
  refine ⟨2 * Real.pi + 8, fun M hM θ => ?_⟩
  set F : ℝ → ℂ := fun φ => (signOf (Real.cos (θ - φ)) : ℂ) * Complex.exp (φ * Complex.I)
    with hF
  set φ : ℕ → ℝ := fun j => 2 * Real.pi * j / M with hφ
  set h : ℝ := 2 * Real.pi / M with hh
  set a : ℝ → ℝ := fun t => (t - θ) / Real.pi + 1 / 2 with ha
  set g : ℕ → ℤ := fun j => ⌊a (φ j)⌋ + ⌈a (φ j)⌉ with hg
  have hπ := Real.pi_pos
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hh0 : 0 < h := by positivity
  have hφs : ∀ j, φ (j + 1) = φ j + h := by
    intro j
    simp only [hφ, hh]
    push_cast
    field_simp
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have hφM : φ M = 2 * Real.pi := by
    simp only [hφ]
    field_simp
  have hFint : ∀ u v, IntervalIntegrable F volume u v := cpx_intervalIntegrable θ
  have hsum : ∑ j : Fin M, (signOf (Real.cos (θ - 2 * Real.pi * j / M)) : ℂ) *
        Complex.exp ((2 * Real.pi * j / M : ℝ) * Complex.I) =
      ∑ j ∈ Finset.range M, F (φ j) :=
    Fin.sum_univ_eq_sum_range (fun j => F (φ j)) M
  have hint : (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I) =
      ((2 * Real.pi)⁻¹ : ℂ) * ∑ j ∈ Finset.range M, ∫ t in φ j..φ (j + 1), F t := by
    rw [← integral_signOf_cos θ, intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hFint _ _), hφ0, hφM]
  have hconst : ∀ j, (M : ℂ)⁻¹ * F (φ j) =
      ((2 * Real.pi)⁻¹ : ℂ) * ∫ _ in φ j..φ (j + 1), F (φ j) := by
    intro j
    rw [intervalIntegral.integral_const, hφs, add_sub_cancel_left, Complex.real_smul]
    simp only [hh]
    push_cast
    field_simp
  have hdiff : (M : ℂ)⁻¹ * ∑ j ∈ Finset.range M, F (φ j) -
        (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I) =
      ((2 * Real.pi)⁻¹ : ℂ) *
        ∑ j ∈ Finset.range M, ∫ t in φ j..φ (j + 1), (F (φ j) - F t) := by
    rw [hint, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconst, ← mul_sub, intervalIntegral.integral_sub intervalIntegrable_const (hFint _ _)]
  have hamono : ∀ j, a (φ j) < a (φ (j + 1)) := by
    intro j
    simp only [ha, hφs j]
    gcongr
    linarith
  have hgmono : ∀ j, g j ≤ g (j + 1) := fun j =>
    add_le_add (Int.floor_le_floor (hamono j).le) (Int.ceil_le_ceil (hamono j).le)
  have hpt : ∀ j, ∀ t ∈ Set.uIoc (φ j) (φ (j + 1)),
      ‖F (φ j) - F t‖ ≤ h + 2 * ((g (j + 1) - g j : ℤ) : ℝ) := by
    intro j t ht
    rw [Set.uIoc_of_le (hφs j ▸ by linarith : φ j ≤ φ (j + 1))] at ht
    by_cases hgj : g j = g (j + 1)
    · have hfl := Int.floor_le_floor (hamono j).le
      have hce := Int.ceil_le_ceil (hamono j).le
      have hg' : ⌊a (φ j)⌋ + ⌈a (φ j)⌉ = ⌊a (φ (j + 1))⌋ + ⌈a (φ (j + 1))⌉ := hgj
      have hfl' : ⌊a (φ j)⌋ = ⌊a (φ (j + 1))⌋ := by omega
      have hce' : ⌈a (φ j)⌉ = ⌈a (φ (j + 1))⌉ := by omega
      have hs := cpx_signOf_cos_eq (θ := θ) (hφs j ▸ by linarith : φ j < φ (j + 1))
        hfl' hce' ⟨ht.1.le, ht.2⟩
      have hF' : F (φ j) - F t = (signOf (Real.cos (θ - φ j)) : ℂ) *
          (Complex.exp (φ j * Complex.I) - Complex.exp (t * Complex.I)) := by
        simp only [hF, hs]
        ring
      rw [hF', norm_mul, cpx_norm_signOf, one_mul, hgj, sub_self, Int.cast_zero, mul_zero,
        add_zero]
      refine (cpx_norm_exp_sub_exp_le _ _).trans ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.2, hφs j]
    · have := hgmono j
      have h1 : (1 : ℝ) ≤ ((g (j + 1) - g j : ℤ) : ℝ) := by
        exact_mod_cast (by omega : (1 : ℤ) ≤ g (j + 1) - g j)
      calc ‖F (φ j) - F t‖ ≤ ‖F (φ j)‖ + ‖F t‖ := norm_sub_le _ _
        _ = 2 := by simp only [hF, cpx_norm_integrand]; norm_num
        _ ≤ h + 2 * ((g (j + 1) - g j : ℤ) : ℝ) := by linarith
  have hgsum : ∑ j ∈ Finset.range M, ((g (j + 1) - g j : ℤ) : ℝ) = 4 := by
    rw [← Int.cast_sum, Finset.sum_range_sub]
    have hM2 : a (φ M) = a (φ 0) + 2 := by
      simp only [ha, hφM, hφ0]
      field_simp
      ring
    simp only [hg, hM2, Int.floor_add_ofNat, Int.ceil_add_ofNat]
    push_cast
    ring
  rw [hsum, hdiff]
  calc ‖((2 * Real.pi)⁻¹ : ℂ) *
        ∑ j ∈ Finset.range M, ∫ t in φ j..φ (j + 1), (F (φ j) - F t)‖
      ≤ (2 * Real.pi)⁻¹ * ∑ j ∈ Finset.range M, ‖∫ t in φ j..φ (j + 1), (F (φ j) - F t)‖ := by
        rw [norm_mul]
        gcongr
        · exact le_of_eq (by simp [abs_of_pos hπ])
        · exact norm_sum_le _ _
    _ ≤ (2 * Real.pi)⁻¹ * ∑ j ∈ Finset.range M,
          (h + 2 * ((g (j + 1) - g j : ℤ) : ℝ)) * |φ (j + 1) - φ j| := by
        gcongr with j hj
        exact intervalIntegral.norm_integral_le_of_norm_le_const (hpt j)
    _ = (2 * Real.pi)⁻¹ * (M * h * h + 2 * h * 4) := by
        congr 1
        simp only [hφs, add_sub_cancel_left, abs_of_pos hh0, add_mul, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum,
          hgsum]
        ring
    _ = (2 * Real.pi + 8) / M := by
        simp only [hh]
        field_simp
        ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every complex `UMD_p` bound is a real one: signs `σ_k = ±1` are unimodular complex multipliers,
and `(σ_k : ℂ) • v = σ_k • v`. -/
private theorem cpx_isUMDBound_of_isComplexUMDBound {p : ℝ} {β : ℝ≥0∞}
    (h : IsComplexUMDBound X p β) : IsUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
  have key := h Ω mΩ μ ℱ Y (fun k ω => (σ k ω : ℂ)) hY hY0
    (fun k ω => by rcases hσ k ω with h1 | h1 <;> simp [h1])
    (fun k => Complex.continuous_ofReal.comp_stronglyMeasurable (hσm k)) n
  simp only [Complex.coe_smul] at key
  have hT : AEStronglyMeasurable
      (fun ω => ∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)) μ :=
    (Finset.stronglyMeasurable_fun_sum _ fun k _ => ((hσm k).mono (ℱ.le k)).smul
      (((hY.stronglyAdapted (k + 1)).mono (ℱ.le _)).sub
        ((hY.stronglyAdapted k).mono (ℱ.le _)))).aestronglyMeasurable
  rwa [eLpNorm_norm _ hT,
    eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]

/-- The averaging step for a fixed number `M` of equally spaced angles `φ_j = 2πj / M`: with
`θ_k = arg c_k`, the signs `σ^j_k = sgn cos (θ_k − φ_j)` are predictable, and
`c_k = (π / 2) (1 / M) Σ_j σ^j_k e^{iφ_j} − ρ_k` with `|ρ_k| ≤ (π / 2) C / M`, so that
`‖Σ_{k<n} c_{k+1} dY_{k+1}‖_p ≤ (π / 2) UMD_p (X) ‖Y_n‖_p + n (π / 2) (C / M) 2 ‖Y_n‖_p`. -/
private theorem cpx_eLpNorm_transform_le {C : ℝ} (hC : ∀ M : ℕ, 0 < M → ∀ θ : ℝ,
    ‖(M : ℂ)⁻¹ * ∑ j : Fin M, (signOf (Real.cos (θ - 2 * Real.pi * j / M)) : ℂ) *
        Complex.exp ((2 * Real.pi * j / M : ℝ) * Complex.I) -
      (2 / Real.pi : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ C / M)
    {p : ℝ} (hp : 1 < p) {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} {c : ℕ → Ω → ℂ}
    (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0) (hc : ∀ n ω, ‖c n ω‖ = 1)
    (hcm : ∀ k, StronglyMeasurable[ℱ k] (c (k + 1))) (n M : ℕ) (hM : 0 < M) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Y (k + 1) ω - Y k ω))
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.pi / 2) * umdConst X p * eLpNorm (Y n) (ENNReal.ofReal p) μ +
        n * (ENNReal.ofReal (Real.pi / 2 * C / M) *
          (2 * eLpNorm (Y n) (ENNReal.ofReal p) μ)) := by
  have hP : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hπ := Real.pi_pos
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  -- the angles `φ_j`, the signs `σ^j_k`, the remainders `ρ_k`
  set e : ℕ → ℂ := fun j => Complex.exp ((2 * Real.pi * j / M : ℝ) * Complex.I) with he
  set S : ℕ → ℝ → ℝ := fun j r => signOf (Real.cos (r - 2 * Real.pi * j / M)) with hS
  set R : ℝ → ℂ := fun r => (Real.pi / 2 : ℂ) *
      ((M : ℂ)⁻¹ * ∑ j ∈ Finset.range M, (S j r : ℂ) * e j) - Complex.exp (r * Complex.I)
    with hR
  set σ : ℕ → ℕ → Ω → ℝ := fun j k ω => S j (Complex.arg (c k ω)) with hσ
  set ρ : ℕ → Ω → ℂ := fun k ω => R (Complex.arg (c k ω)) with hρ
  set T : ℕ → Ω → X := fun j ω => ∑ k ∈ Finset.range n, σ j (k + 1) ω • (Y (k + 1) ω - Y k ω)
    with hT
  -- measurability
  have hmS : ∀ j, Measurable (S j) := fun j =>
    cpx_measurable_signOf.comp (Real.measurable_cos.comp (measurable_id.sub_const _))
  have hmR : Measurable R :=
    (measurable_const.mul (measurable_const.mul (Finset.measurable_fun_sum _ fun j _ =>
      (Complex.measurable_ofReal.comp (hmS j)).mul_const _))).sub
      (Complex.measurable_exp.comp (Complex.measurable_ofReal.mul_const _))
  have hmarg : ∀ k, Measurable[ℱ k] fun ω => Complex.arg (c (k + 1) ω) := fun k =>
    Complex.measurable_arg.comp (hcm k).measurable
  have hσm : ∀ j k, StronglyMeasurable[ℱ k] (σ j (k + 1)) := fun j k =>
    ((hmS j).comp (hmarg k)).stronglyMeasurable
  have hρm : ∀ k, StronglyMeasurable[ℱ k] (ρ (k + 1)) := fun k =>
    (hmR.comp (hmarg k)).stronglyMeasurable
  have hdYm : ∀ k, StronglyMeasurable (fun ω => Y (k + 1) ω - Y k ω) := fun k =>
    ((hY.stronglyAdapted (k + 1)).mono (ℱ.le _)).sub ((hY.stronglyAdapted k).mono (ℱ.le _))
  have hTm : ∀ j, StronglyMeasurable (T j) := fun j =>
    Finset.stronglyMeasurable_fun_sum _ fun k _ => ((hσm j k).mono (ℱ.le k)).smul (hdYm k)
  -- the real UMD bound for the signs `σ^j`
  have hTb : ∀ j, eLpNorm (T j) (ENNReal.ofReal p) μ ≤
      umdConst X p * eLpNorm (Y n) (ENNReal.ofReal p) μ := by
    intro j
    have key := isUMDBound_umdConst (X := X) hp Ω mΩ μ ℱ Y (σ j) hY hY0
      (fun k ω => signOf_eq_one_or_eq_neg_one _) (hσm j) n
    rwa [eLpNorm_norm _ (hTm j).aestronglyMeasurable,
      eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable] at key
  -- the Riemann sum error
  have hRb : ∀ r, ‖R r‖ ≤ Real.pi / 2 * C / M := by
    intro r
    have h1 := hC M hM r
    rw [Fin.sum_univ_eq_sum_range (fun j => (S j r : ℂ) * e j) M] at h1
    have h2 : R r = (Real.pi / 2 : ℂ) * ((M : ℂ)⁻¹ * ∑ j ∈ Finset.range M, (S j r : ℂ) * e j -
        (2 / Real.pi : ℂ) * Complex.exp (r * Complex.I)) := by
      have hπ' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
      simp only [hR]
      rw [mul_sub, show (Real.pi / 2 : ℂ) * (2 / Real.pi * Complex.exp (r * Complex.I)) =
        Complex.exp (r * Complex.I) by field_simp]
    rw [h2, norm_mul, show ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 by simp [abs_of_pos hπ]]
    calc Real.pi / 2 * ‖(M : ℂ)⁻¹ * ∑ j ∈ Finset.range M, (S j r : ℂ) * e j -
          (2 / Real.pi : ℂ) * Complex.exp (r * Complex.I)‖ ≤ Real.pi / 2 * (C / M) := by
          gcongr
      _ = Real.pi / 2 * C / M := by ring
  -- the decomposition `c_k = (π / 2) (1 / M) Σ_j σ^j_k e^{iφ_j} − ρ_k`
  have hdecomp : ∀ k ω, c k ω = (Real.pi / 2 : ℂ) *
      ((M : ℂ)⁻¹ * ∑ j ∈ Finset.range M, (σ j k ω : ℂ) * e j) - ρ k ω := by
    intro k ω
    have h1 := Complex.norm_mul_exp_arg_mul_I (c k ω)
    rw [hc k ω, Complex.ofReal_one, one_mul] at h1
    simp only [hρ, hR, hσ]
    rw [h1, sub_sub_cancel]
  have hfun : (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Y (k + 1) ω - Y k ω)) =
      (∑ j ∈ Finset.range M, ((Real.pi / 2 : ℂ) * (M : ℂ)⁻¹ * e j) • T j) -
        ∑ k ∈ Finset.range n, fun ω => ρ (k + 1) ω • (Y (k + 1) ω - Y k ω) := by
    funext ω
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, hT, Finset.smul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdecomp (k + 1) ω, sub_smul, Finset.mul_sum, Finset.mul_sum, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    ring
  have hna : ∀ j, ‖(Real.pi / 2 : ℂ) * (M : ℂ)⁻¹ * e j‖ₑ = ENNReal.ofReal (Real.pi / 2 / M) := by
    intro j
    rw [← ofReal_norm, norm_mul, norm_mul, he, Complex.norm_exp_ofReal_mul_I, mul_one,
      norm_inv, Complex.norm_natCast, show ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 by
        simp [abs_of_pos hπ], div_eq_mul_inv (Real.pi / 2)]
  rw [hfun]
  calc eLpNorm ((∑ j ∈ Finset.range M, ((Real.pi / 2 : ℂ) * (M : ℂ)⁻¹ * e j) • T j) -
        ∑ k ∈ Finset.range n, fun ω => ρ (k + 1) ω • (Y (k + 1) ω - Y k ω)) (ENNReal.ofReal p) μ
      ≤ eLpNorm (∑ j ∈ Finset.range M, ((Real.pi / 2 : ℂ) * (M : ℂ)⁻¹ * e j) • T j)
          (ENNReal.ofReal p) μ +
        eLpNorm (∑ k ∈ Finset.range n, fun ω => ρ (k + 1) ω • (Y (k + 1) ω - Y k ω))
          (ENNReal.ofReal p) μ := eLpNorm_sub_le hP
    _ ≤ ∑ j ∈ Finset.range M,
          eLpNorm (((Real.pi / 2 : ℂ) * (M : ℂ)⁻¹ * e j) • T j) (ENNReal.ofReal p) μ +
        ∑ k ∈ Finset.range n,
          eLpNorm (fun ω => ρ (k + 1) ω • (Y (k + 1) ω - Y k ω)) (ENNReal.ofReal p) μ :=
        add_le_add (eLpNorm_sum_le hP) (eLpNorm_sum_le hP)
    _ ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal (Real.pi / 2 / M) *
          (umdConst X p * eLpNorm (Y n) (ENNReal.ofReal p) μ) +
        ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.pi / 2 * C / M) *
          (2 * eLpNorm (Y n) (ENNReal.ofReal p) μ) := by
        gcongr with j hj k hk
        · rw [eLpNorm_const_smul, hna]
          exact mul_le_mul_of_nonneg_left (hTb j) zero_le
        · refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            (((hρm k).mono (ℱ.le k)).smul (hdYm k)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun ω => ?_) _).trans
            (mul_le_mul_of_nonneg_left (eLpNorm_sub_le_two_mul hY hP (Finset.mem_range.1 hk))
              zero_le)
          change ‖ρ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖ ≤ _
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (hRb _) (norm_nonneg _)
    _ = ENNReal.ofReal (Real.pi / 2) * umdConst X p * eLpNorm (Y n) (ENNReal.ofReal p) μ +
        n * (ENNReal.ofReal (Real.pi / 2 * C / M) *
          (2 * eLpNorm (Y n) (ENNReal.ofReal p) μ)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
          nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul hMpos.le]
        congr 3
        field_simp

/-- `UMD_p (X) ≤ UMD_{ℂ,p} (X)`: real signs are unimodular complex multipliers. -/
theorem umdConst_le_complexUMDConst {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p := by
  exact umdConst_le_of_isUMDBound
    (cpx_isUMDBound_of_isComplexUMDBound (isComplexUMDBound_complexUMDConst hp))

/-- `UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`, by averaging over the signs `sgn cos (θ_k − φ)`. -/
theorem complexUMDConst_le_pi_div_two_mul {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p := by
  obtain ⟨C, hC⟩ := riemannSum_signOf_cos
  refine complexUMDConst_le_of_isComplexUMDBound fun Ω mΩ μ _ ℱ Y c hY hY0 hc hcm n => ?_
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hπ : ENNReal.ofReal (Real.pi / 2) ≠ 0 := by simp [Real.pi_pos]
  by_cases hA0 : eLpNorm (Y n) (ENNReal.ofReal p) μ = 0
  · rw [umdd_eLpNorm_transform_eq_zero hY hp0 hA0 c]
    exact zero_le
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact absurd (by rw [Subsingleton.elim (Y n) 0, eLpNorm_zero]) hA0
  have hu0 : umdConst X p ≠ 0 := (zero_lt_one.trans_le (one_le_umdConst hp)).ne'
  by_cases hu : umdConst X p = ⊤
  · rw [hu, ENNReal.mul_top hπ, ENNReal.top_mul hA0]
    exact le_top
  by_cases hA : eLpNorm (Y n) (ENNReal.ofReal p) μ = ⊤
  · rw [hA, ENNReal.mul_top (mul_ne_zero hπ hu0)]
    exact le_top
  -- let `M → ∞` in the averaging step
  have h1 : Filter.Tendsto (fun M : ℕ => ENNReal.ofReal (Real.pi / 2 * C / M)) Filter.atTop
      (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2 * C))
    rwa [ENNReal.ofReal_zero] at this
  have h2 := tendsto_const_nhds (x := ENNReal.ofReal (Real.pi / 2) * umdConst X p *
      eLpNorm (Y n) (ENNReal.ofReal p) μ) (f := Filter.atTop) |>.add
    (ENNReal.Tendsto.const_mul (a := (n : ℝ≥0∞))
      (ENNReal.Tendsto.mul_const (b := 2 * eLpNorm (Y n) (ENNReal.ofReal p) μ) h1
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hA)))
      (Or.inr (ENNReal.natCast_ne_top n)))
  rw [zero_mul, mul_zero, add_zero] at h2
  exact ge_of_tendsto h2 (Filter.eventually_atTop.2
    ⟨1, fun M hM => cpx_eLpNorm_transform_le hC hp hY hY0 hc hcm n M hM⟩)

/-- **Complex UMD constants** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.10;
Yaroslavtsev 2018, Lemma 3.2): `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
theorem umdConst_le_complexUMDConst_le {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  ⟨umdConst_le_complexUMDConst hp, complexUMDConst_le_pi_div_two_mul hp⟩

end BanachProbability
