module

public import BanachProbability.SignCube.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Convex hulls of sign vectors

Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach Spaces I* (2016), Section 3.2.b,
p. 183–185: the multipliers of modulus at most one are combinations of sign vectors. With
`B_𝕜 = {c ∈ 𝕜 : |c| ≤ 1}` and `S_𝕜 = {c ∈ 𝕜 : |c| = 1}`, Proposition 3.2.14, (3.20) reads

`conv (S_ℝ^n) = B_ℝ^n = abco_ℝ {−1, 1}^n`,   `conv (S_ℂ^n) = B_ℂ^n ⊆ (π / 2) abco_ℂ {−1, 1}^n`,

where `conv` is the convex hull and `abco_𝕜` the set of the combinations `Σ λ_j x_j` with
`Σ |λ_j| ≤ 1`, `λ_j ∈ 𝕜` (Definition 3.2.12). The steps are those of the book:

* Lemma 3.2.13, the convex hull of a product is the product of the convex hulls, is Mathlib's
  `convexHull_pi`; with `B_𝕜 = conv S_𝕜` (Mathlib's `convexHull_sphere_eq_closedBall`) it gives
  `B_𝕜^n = conv (S_𝕜^n)` for `𝕜 = ℝ, ℂ` (`convexHull_pi_sphere`), and for `𝕜 = ℝ`, as
  `S_ℝ = {−1, 1}`, the real case of (3.20) (`exists_weights_sum_coin`);
* Lemma 3.2.15 is the functional analytic observation behind the complex case: if
  `‖T x‖ ≥ δ ‖x‖`, then `δ B_{X*} ⊆ T* B_{Y*}`, by the Hahn–Banach theorem
  (`exists_dual_apply_eq_mul`);
* it is applied to `T : ℓ¹_n → ℓ^∞ ({−1, 1}^n)`, `(T x) (ε) = Σ_j ε_j x_j` (`signSum`), for which
  `‖T x‖_∞ ≥ (2 / π) ‖x‖_1`, (3.21) (`two_div_pi_mul_norm_le_norm_signSum`). This is the
  computation (3.22): the supremum over the signs of `|ℜ (e^{2πit} Σ_j ε_j x_j)|` is
  `Σ_j |x_j| |cos (2π (t_j + t))|`, with `x_j = |x_j| e^{2πit_j}`
  (`cvh_sum_norm_mul_abs_cos_le`), and `∫_0^1 |cos (2π (s + t))| dt = 2 / π`
  (`integral_abs_cos_two_pi_mul`);
* the adjoint of `T` is `λ ↦ (Σ_ε λ (ε) ε_j)_j` on `ℓ¹ ({−1, 1}^n)`, the dual of
  `ℓ^∞ ({−1, 1}^n)` (`cvh_sum_norm_apply_single_le`), whence the complex case of (3.20)
  (`exists_sum_coin_complex`).
-/

@[expose] public section

open MeasureTheory
open scoped Real

namespace BanachProbability

open SignCube

/-! ### HNVW I, Lemma 3.2.15 -/

section HahnBanach

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **HNVW I, Lemma 3.2.15** (p. 184). If `T` is bounded from below, `‖T x‖ ≥ δ ‖x‖` with
`δ > 0`, then `δ B_{X*} ⊆ T* B_{Y*}`: for `‖x*‖ ≤ 1` there is `y*` with `‖y*‖ ≤ 1` and
`⟨T x, y*⟩ = δ ⟨x, x*⟩`. As in the book: `⟨T x, y₀*⟩ = ⟨x, x*⟩` defines a functional of norm at
most `δ⁻¹` on the range `Y₀` of `T`, which has an extension of norm at most `δ⁻¹` by the
Hahn–Banach theorem; `y*` is `δ` times the extension. -/
theorem exists_dual_apply_eq_mul (T : X →L[𝕜] Y) {δ : ℝ} (hδ : 0 < δ)
    (hT : ∀ x, δ * ‖x‖ ≤ ‖T x‖) (x' : StrongDual 𝕜 X) (hx' : ‖x'‖ ≤ 1) :
    ∃ y' : StrongDual 𝕜 Y, ‖y'‖ ≤ 1 ∧ ∀ x, y' (T x) = (δ : 𝕜) * x' x := by
  have hinj : Function.Injective T.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := hT x
    rw [show T x = 0 from hx, norm_zero] at h
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h hδ)
  -- the functional `y₀*` on the range of `T`
  let e := LinearEquiv.ofInjective T.toLinearMap hinj
  have he : ∀ y, T (e.symm y) = y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hb : ∀ y, ‖(x'.toLinearMap ∘ₗ e.symm.toLinearMap) y‖ ≤ δ⁻¹ * ‖y‖ := by
    intro y
    have h1 : ‖x' (e.symm y)‖ ≤ ‖e.symm y‖ := by
      simpa using (x'.le_opNorm (e.symm y)).trans
        (mul_le_mul_of_nonneg_right hx' (norm_nonneg _))
    have h2 : ‖e.symm y‖ ≤ δ⁻¹ * ‖T (e.symm y)‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm]
      exact hT _
    rw [he] at h2
    exact h1.trans h2
  let y₀ : StrongDual 𝕜 T.toLinearMap.range :=
    (x'.toLinearMap ∘ₗ e.symm.toLinearMap).mkContinuous δ⁻¹ hb
  have hy₀ : ‖y₀‖ ≤ δ⁻¹ := LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 hδ.le) hb
  -- its Hahn–Banach extension
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq T.toLinearMap.range y₀
  refine ⟨(δ : 𝕜) • g, ?_, fun x => ?_⟩
  · rw [norm_smul, hgn, RCLike.norm_ofReal, abs_of_pos hδ]
    calc δ * ‖y₀‖ ≤ δ * δ⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hδ.ne'
  · have h1 : g (T x) = x' x := by
      have h2 : e.symm (e x) = x := e.symm_apply_apply x
      calc g (T x) = y₀ (e x) := hg (e x)
        _ = x' (e.symm (e x)) := rfl
        _ = x' x := by rw [h2]
    rw [smul_apply, h1, smul_eq_mul]

end HahnBanach

/-! ### HNVW I, Proposition 3.2.14: convex hulls, and the real case -/

section ConvexHull

/-- **HNVW I, Proposition 3.2.14** (p. 184), `conv (S_𝕜^n) = B_𝕜^n`: it follows from Lemma 3.2.13
(`convexHull_pi`: the convex hull of a product is the product of the convex hulls) and
`B_𝕜 = conv S_𝕜`. -/
theorem convexHull_pi_sphere (𝕜 ι : Type*) [RCLike 𝕜] [Finite ι] :
    convexHull ℝ (Set.univ.pi fun _ : ι => Metric.sphere (0 : 𝕜) 1) =
      Set.univ.pi fun _ : ι => Metric.closedBall (0 : 𝕜) 1 := by
  rw [convexHull_pi]
  simp only [convexHull_sphere_eq_closedBall (0 : 𝕜) zero_le_one]

/-- **HNVW I, Proposition 3.2.14** (p. 184), real case of (3.20), `B_ℝ^n = conv {−1, 1}^n`: a
vector of real multipliers of modulus at most one is a convex combination of sign vectors. -/
theorem exists_weights_sum_coin {n : ℕ} (α : Fin n → ℝ) (hα : ∀ j, |α j| ≤ 1) :
    ∃ w : (Fin n → Bool) → ℝ, (∀ ε, 0 ≤ w ε) ∧ ∑ ε, w ε = 1 ∧
      ∀ j, α j = ∑ ε, w ε * coin (ε j) := by
  have hS : (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : ℝ) 1) =
      Set.range fun (ε : Fin n → Bool) (j : Fin n) => coin (ε j) := by
    ext u
    simp only [Set.mem_univ_pi, mem_sphere_zero_iff_norm, Real.norm_eq_abs, Set.mem_range]
    constructor
    · intro hu
      refine ⟨fun j => decide (u j = 1), funext fun j => ?_⟩
      rcases eq_or_eq_neg_of_abs_eq (hu j) with h | h <;> simp [h, coin]
      norm_num
    · rintro ⟨ε, rfl⟩ j
      exact abs_coin _
  have hmem : α ∈ convexHull ℝ (Set.range fun (ε : Fin n → Bool) (j : Fin n) => coin (ε j)) := by
    rw [← hS, convexHull_pi_sphere]
    simpa [Set.mem_univ_pi] using hα
  rw [convexHull_range_eq_exists_affineCombination] at hmem
  obtain ⟨s, w, hw0, hw1, hw⟩ := hmem
  classical
  refine ⟨fun ε => if ε ∈ s then w ε else 0, fun ε => ?_, ?_, fun j => ?_⟩
  · dsimp only
    split_ifs with h
    exacts [hw0 ε h, le_rfl]
  · rw [← hw1, Finset.sum_ite_mem, Finset.univ_inter]
  · rw [s.affineCombination_eq_linear_combination _ _ hw1] at hw
    rw [← hw, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

end ConvexHull

/-! ### HNVW I, Proposition 3.2.14: the complex case -/

section SignSum

/-- `∫_0^1 |cos (2π (s + t))| dt = 2 / π` (HNVW I, (3.22), p. 185). -/
theorem integral_abs_cos_two_pi_mul (s : ℝ) :
    ∫ t in (0 : ℝ)..1, |Real.cos (2 * π * (s + t))| = 2 / π := by
  have hper : Function.Periodic (fun u => |Real.cos u|) π := fun u => by
    simp only [Real.cos_add_pi, abs_neg]
  have hint : ∀ a b, IntervalIntegrable (fun u => |Real.cos u|) volume a b := fun a b =>
    Real.continuous_cos.abs.intervalIntegrable a b
  have h1 : ∫ u in (-(π / 2))..(π / 2), |Real.cos u| = 2 := by
    rw [intervalIntegral.integral_congr (g := Real.cos) fun u hu => ?_]
    · rw [integral_cos, Real.sin_neg, Real.sin_pi_div_two]
      norm_num
    · rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hu
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hu)
  have h2 : ∫ u in (2 * π * s)..(2 * π * s + 2 * π), |Real.cos u| = 4 := by
    have h3 := hper.intervalIntegral_add_zsmul_eq 2 (2 * π * s) hint
    have h4 := hper.intervalIntegral_add_eq (2 * π * s) (-(π / 2))
    rw [show -(π / 2) + π = π / 2 by ring, h1] at h4
    rw [h4] at h3
    have e : (2 : ℤ) • π = 2 * π := by simp
    rw [e] at h3
    rw [h3]
    norm_num
  have h5 : ∀ t : ℝ, 2 * π * (s + t) = 2 * π * t + 2 * π * s := fun t => by ring
  simp only [h5]
  rw [intervalIntegral.integral_comp_mul_add (fun u => |Real.cos u|) (by positivity) _]
  rw [show 2 * π * 0 + 2 * π * s = 2 * π * s by ring,
    show 2 * π * 1 + 2 * π * s = 2 * π * s + 2 * π by ring, h2, smul_eq_mul]
  field_simp
  norm_num

/-- The operator `T : ℓ¹_n → ℓ^∞ ({−1, 1}^n)`, `(T x) (ε) = Σ_j ε_j x_j`, of the proof of the
complex case of (3.20) (HNVW I, p. 184). -/
noncomputable def signSum (n : ℕ) : PiLp 1 (fun _ : Fin n => ℂ) →L[ℂ] ((Fin n → Bool) → ℂ) :=
  ContinuousLinearMap.pi fun ε => ∑ j, (coin (ε j) : ℂ) • PiLp.proj 1 (fun _ : Fin n => ℂ) j

theorem signSum_apply {n : ℕ} (x : PiLp 1 (fun _ : Fin n => ℂ)) (ε : Fin n → Bool) :
    signSum n x ε = ∑ j, (coin (ε j) : ℂ) * x j := by
  simp [signSum]

/-- The lines of (3.22) before the integral (HNVW I, p. 185): with `x_j = |x_j| e^{2πit_j}` and, for
a given `t`, the signs `ε_j` of `cos (2π (t_j + t))`,
`Σ_j |x_j| |cos (2π (t_j + t))| = Σ_j ε_j |x_j| cos (2π (t_j + t)) = ℜ (e^{2πit} Σ_j ε_j x_j)
≤ ‖T x‖_∞`. In the book these are equalities after taking suprema over the signs and over `t`; only
this inequality is used. -/
private theorem cvh_sum_norm_mul_abs_cos_le {n : ℕ} (x : PiLp 1 (fun _ : Fin n => ℂ)) (t : ℝ) :
    ∑ j, ‖x j‖ * |Real.cos (2 * π * (Complex.arg (x j) / (2 * π) + t))| ≤ ‖signSum n x‖ := by
  set c : Fin n → ℝ := fun j => Real.cos (2 * π * (Complex.arg (x j) / (2 * π) + t)) with hc
  set ε : Fin n → Bool := fun j => decide (0 ≤ c j) with hε
  have hsgn : ∀ j, coin (ε j) * c j = |c j| := by
    intro j
    by_cases h : 0 ≤ c j
    · simp [hε, h, abs_of_nonneg h]
    · simp [hε, h, abs_of_neg (not_le.1 h)]
  -- `ℜ (e^{2πit} x_j) = |x_j| cos (2π (t_j + t))`
  have hre : ∀ j, (Complex.exp (↑(2 * π * t) * Complex.I) * x j).re = ‖x j‖ * c j := by
    intro j
    have h1 : Complex.exp (↑(2 * π * t) * Complex.I) * x j =
        ↑‖x j‖ * Complex.exp (↑(2 * π * (Complex.arg (x j) / (2 * π) + t)) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (x j)]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast
      field_simp
      ring
    rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  calc ∑ j, ‖x j‖ * |c j| = (Complex.exp (↑(2 * π * t) * Complex.I) * signSum n x ε).re := by
        rw [signSum_apply, Finset.mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, Complex.re_ofReal_mul, hre, ← hsgn]
        ring
    _ ≤ ‖Complex.exp (↑(2 * π * t) * Complex.I) * signSum n x ε‖ := Complex.re_le_norm _
    _ = ‖signSum n x ε‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ ‖signSum n x‖ := norm_le_pi_norm _ ε

/-- **HNVW I, (3.21)** (p. 184–185): `‖T x‖_∞ ≥ (2 / π) ‖x‖_1`. As in (3.22), integrate
`Σ_j |x_j| |cos (2π (t_j + t))| ≤ ‖T x‖_∞` (`cvh_sum_norm_mul_abs_cos_le`) over `t ∈ [0, 1]`, with
`∫_0^1 |cos (2π (t_j + t))| dt = 2 / π`. -/
theorem two_div_pi_mul_norm_le_norm_signSum {n : ℕ} (x : PiLp 1 (fun _ : Fin n => ℂ)) :
    2 / π * ‖x‖ ≤ ‖signSum n x‖ := by
  have hcont : ∀ j, Continuous fun t : ℝ =>
      ‖x j‖ * |Real.cos (2 * π * (Complex.arg (x j) / (2 * π) + t))| := fun j => by fun_prop
  calc 2 / π * ‖x‖ = ∑ j, ∫ t in (0 : ℝ)..1,
        ‖x j‖ * |Real.cos (2 * π * (Complex.arg (x j) / (2 * π) + t))| := by
        simp only [intervalIntegral.integral_const_mul, integral_abs_cos_two_pi_mul]
        rw [PiLp.norm_eq_of_L1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ∫ t in (0 : ℝ)..1, ∑ j,
        ‖x j‖ * |Real.cos (2 * π * (Complex.arg (x j) / (2 * π) + t))| :=
        (intervalIntegral.integral_finsetSum fun j _ => (hcont j).intervalIntegrable _ _).symm
    _ ≤ ∫ _ in (0 : ℝ)..1, ‖signSum n x‖ :=
        intervalIntegral.integral_mono_on zero_le_one
          ((continuous_finsetSum _ fun j _ => hcont j).intervalIntegrable _ _)
          intervalIntegrable_const fun t _ => cvh_sum_norm_mul_abs_cos_le x t
    _ = ‖signSum n x‖ := by simp

/-- A functional on `ℓ^∞` of a finite set is given by an `ℓ¹` vector:
`Σ_i |y* (e_i)| ≤ ‖y*‖` (evaluate `y*` at a vector of unimodular entries). -/
private theorem cvh_sum_norm_apply_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y' : StrongDual ℂ (ι → ℂ)) : ∑ i, ‖y' (Pi.single i 1)‖ ≤ ‖y'‖ := by
  set u : ι → ℂ := fun i =>
    Complex.exp (-(Complex.arg (y' (Pi.single i 1)) : ℂ) * Complex.I) with hu
  have hu1 : ‖u‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    simp only [hu]
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have h1 : y' u = ∑ i, (‖y' (Pi.single i 1)‖ : ℂ) := by
    have h2 : u = ∑ i, u i • (Pi.single i 1 : ι → ℂ) := by
      rw [← pi_eq_sum_univ' u]
    rw [h2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (y' (Pi.single i 1))]
    rw [hu, mul_left_comm, ← Complex.exp_add]
    simp
  calc ∑ i, ‖y' (Pi.single i 1)‖ = ‖y' u‖ := by
        rw [h1, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    _ ≤ ‖y'‖ * ‖u‖ := y'.le_opNorm u
    _ ≤ ‖y'‖ := mul_le_of_le_one_right (norm_nonneg _) hu1

/-- **HNVW I, Proposition 3.2.14** (p. 184–185), complex case of (3.20),
`B_ℂ^n ⊆ (π / 2) abco_ℂ {−1, 1}^n`: a vector of complex multipliers of modulus at most one is
`Σ_ε c (ε) ε` with `Σ_ε |c (ε)| ≤ π / 2`. Lemma 3.2.15 with `δ = 2 / π`, for the operator `T` of
(3.21) and the functional `x ↦ Σ_j α_j x_j` of norm at most one on `ℓ¹_n`, gives a functional `λ`
of norm at most one on `ℓ^∞ ({−1, 1}^n)` with `T* λ = (2 / π) α`, that is,
`Σ_ε λ (ε) ε_j = (2 / π) α_j`. -/
theorem exists_sum_coin_complex {n : ℕ} (α : Fin n → ℂ) (hα : ∀ j, ‖α j‖ ≤ 1) :
    ∃ c : (Fin n → Bool) → ℂ, ∑ ε, ‖c ε‖ ≤ π / 2 ∧ ∀ j, α j = ∑ ε, c ε * (coin (ε j) : ℂ) := by
  have hπ := Real.pi_pos
  have hπ' : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
  -- the functional `x ↦ Σ_j α_j x_j` on `ℓ¹_n`
  let a : StrongDual ℂ (PiLp 1 (fun _ : Fin n => ℂ)) :=
    ∑ j, α j • PiLp.proj 1 (fun _ : Fin n => ℂ) j
  have ha : ∀ x, a x = ∑ j, α j * x j := fun x => by simp [a]
  have ha1 : ‖a‖ ≤ 1 := by
    refine a.opNorm_le_bound zero_le_one fun x => ?_
    rw [ha, one_mul, PiLp.norm_eq_of_L1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hα j)
  obtain ⟨y', hy', hyT⟩ := exists_dual_apply_eq_mul (signSum n) (δ := 2 / π) (by positivity)
    two_div_pi_mul_norm_le_norm_signSum a ha1
  refine ⟨fun ε => (π / 2 : ℂ) * y' (Pi.single ε 1), ?_, fun j => ?_⟩
  · calc ∑ ε, ‖(π / 2 : ℂ) * y' (Pi.single ε 1)‖ = π / 2 * ∑ ε, ‖y' (Pi.single ε 1)‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ε _ => ?_
          rw [norm_mul]
          simp [abs_of_pos hπ]
      _ ≤ π / 2 * 1 := by
          gcongr
          exact (cvh_sum_norm_apply_single_le y').trans hy'
      _ = π / 2 := mul_one _
  · -- evaluate `T* λ = (2 / π) α` at `e_j`
    have h1 := hyT (PiLp.single 1 j 1)
    have h2 : a (PiLp.single 1 j 1) = α j := by
      rw [ha]
      simp
    have h3 : signSum n (PiLp.single 1 j 1) =
        ∑ ε : Fin n → Bool, (coin (ε j) : ℂ) • (Pi.single ε 1 : (Fin n → Bool) → ℂ) := by
      rw [← pi_eq_sum_univ' (fun ε : Fin n → Bool => (coin (ε j) : ℂ))]
      funext ε
      rw [signSum_apply]
      simp
    rw [h2, h3, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    have h4 : α j = (π / 2 : ℂ) * ∑ ε : Fin n → Bool, (coin (ε j) : ℂ) * y' (Pi.single ε 1) := by
      rw [h1]
      simp only [RCLike.ofReal_div, RCLike.ofReal_ofNat, Complex.coe_algebraMap]
      field_simp
    rw [h4, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ε _ => by ring

end SignSum

end BanachProbability
