module

public import BanachProbability.TypeTwo.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# K-convexity and type 2

The Rademacher projection of `f : {±1}^N → X` is `π_N f = Σ_k ε_k E (ε_k f)` (`rademacherProj f`),
with real signs `ε_k`. A normed space `X` is K-convex with constant `K` in `L^p` when
`‖π_N f‖_{L^p} ≤ K ‖f‖_{L^p}` for all `N` and `f` (`IsKConvexBound X p K`; Hytönen–van
Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces II* (2017): the least such `K ≥ 0` is
`K^ℝ_{p,X} = sup_N ‖π_N‖`, p. 124, line 1, which is the K-convexity constant of Definition 7.4.1, p.
109, for a real space, by Definition 7.4.4 and Proposition 7.4.5, p. 111).

`IsTypeTwoBound.isKConvexBound`: a space of type 2 with constant `τ` is K-convex in `L²`, with
constant `√(π/2) τ` (HNVW II, Proposition 7.4.22, p. 124, with Proposition 7.1.18; B. Maurey and G.
Pisier, *Séries de variables aléatoires vectorielles indépendantes et propriétés géométriques des
espaces de Banach*, Studia Math. 58 (1976), Remark 2.10, as quoted by G. Pisier, Astérisque 247
(1998), p. 106). The steps are HNVW's:

* type 2 gives Gaussian type 2 with the same constant (Proposition 7.1.18 from Proposition 7.1.16,
  pp. 66–68): `IsTypeTwoBound.integral_stdGaussian_le`;
* Rademacher sums are dominated by Gaussian sums, with the factor `1 / E |g| = √(π/2)` (Proposition
  6.1.15, pp. 10–11): `avg_norm_sq_le_integral_stdGaussian`;
* the Gaussian sum over the signs is dominated by the Gaussian sum over a complete orthonormal
  system, `integral_stdGaussian_rademacherCoeff_le`: the contraction principle in the proof of
  Proposition 7.4.22 and the rotation in the proof of Theorem 7.1.20, pp. 69–71.

Departure from the source, in form: Proposition 7.4.22 expands `f = Σ_α w_α x_α` in Walsh functions,
drops those of degree `≠ 1` from the Gaussian sum `Σ_α g_α x_α` by the contraction principle, and
passes from the Walsh functions to the indicators of the points of the cube by a rotation. Here the
two steps are one, by the reflection `2P − 1`, where `P` is the orthogonal projection on the span of
the signs; the Walsh functions of degree `≠ 1` are not introduced. The resulting inequality is the
covariance domination (Theorem 6.1.25, p. 16) as used in the proof of Proposition 7.4.21, p. 123.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BanachProbability

open SignCube

section Projection

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The expectation `E (ε_k f)` of a function on the sign cube with values in a vector space. -/
noncomputable def rademacherCoeff (f : (Fin N → Bool) → V) (k : Fin N) : V :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η

/-- The Rademacher projection `Σ_k ε_k E (ε_k f)`. -/
noncomputable def rademacherProj (f : (Fin N → Bool) → V) (ε : Fin N → Bool) : V :=
  ∑ k, coin (ε k) • rademacherCoeff f k

end Projection

variable {N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (X) in
/-- `X` is K-convex in `L^p` with constant `K`: `‖Σ_k ε_k E (ε_k f)‖_{L^p} ≤ K ‖f‖_{L^p}`, for real
signs `ε_k` (the least `K ≥ 0` is `K^ℝ_{p,X}` of HNVW II, p. 124, line 1). -/
def IsKConvexBound (p K : ℝ) : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → X),
    SignCube.lpNorm (fun y => ‖y‖) p (rademacherProj f) ≤ K * SignCube.lpNorm (fun y => ‖y‖) p f

/-! ### Gaussian vectors -/

section Gaussian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]

/-- The linear map `g ↦ Σ g_i y_i`. -/
private noncomputable def kcSum (y : ι → X) : EuclideanSpace ℝ ι →L[ℝ] X :=
  ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).smulRight (y i)

private theorem kcSum_apply (y : ι → X) (g : EuclideanSpace ℝ ι) :
    kcSum y g = ∑ i, g i • y i := by
  simp [kcSum]

/-- Gaussian sums have finite second moments. -/
private theorem kc_integrable_norm_sq (T : E →L[ℝ] X) :
    Integrable (fun g => ‖T g‖ ^ 2) (stdGaussian E) := by
  have h : Integrable (fun g : E => ‖T‖ ^ 2 * ‖g‖ ^ 2) (stdGaussian E) :=
    (IsGaussian.memLp_two_id.integrable_norm_pow two_ne_zero).const_mul _
  refine h.mono' (T.continuous.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm g) 2

/-- The rotation invariance of the standard Gaussian measure. -/
private theorem kc_integral_comp (R : E ≃ₗᵢ[ℝ] F) (φ : F → ℝ) :
    ∫ g, φ (R g) ∂stdGaussian E = ∫ g, φ g ∂stdGaussian F := by
  rw [← stdGaussian_map R]
  exact (R.toHomeomorph.measurableEmbedding.integral_map φ).symm

/-- The symmetry of the standard Gaussian measure: `(ε_i g_i)` and `(g_i)` have the same law. -/
private theorem kc_integral_sign (s : ι → Bool) (φ : EuclideanSpace ℝ ι → ℝ) :
    ∫ g, φ (WithLp.toLp 2 fun i => coin (s i) * g i) ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, φ g ∂stdGaussian (EuclideanSpace ℝ ι) := by
  rw [← kc_integral_comp (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    if s i then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ) φ]
  refine integral_congr_ae (ae_of_all _ fun g => congrArg φ ?_)
  ext i
  cases h : s i <;> simp [h]

/-- The coordinates of a standard Gaussian vector are standard Gaussian. -/
private theorem kc_measurePreserving_eval (i : ι) :
    MeasurePreserving (fun g : EuclideanSpace ℝ ι => g i) (stdGaussian (EuclideanSpace ℝ ι))
      (gaussianReal 0 1) := by
  classical
  simpa using measurePreserving_eval_multivariateGaussian (μ := 0) (S := (1 : Matrix ι ι ℝ))
    Matrix.PosSemidef.one (i := i)

/-- `E g_i² = 1`. -/
private theorem kc_integral_sq (i : ι) :
    ∫ g : EuclideanSpace ℝ ι, g i ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) = 1 := by
  have h := kc_measurePreserving_eval i
  have e : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h1 := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id)
      measurable_id.aemeasurable (by simp)
    rw [variance_id_gaussianReal] at h1
    simpa using h1.symm
  rw [← e, ← h.map_eq, integral_map h.measurable.aemeasurable (by fun_prop)]

/-- `E |g| = √(2/π)`. -/
private theorem kc_integral_abs : ∫ x, |x| ∂gaussianReal 0 1 = √(2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x| = (fun t : ℝ =>
      (√(2 * Real.pi))⁻¹ * (t ^ (1 : ℝ) * Real.exp (-(1 / 2) * t ^ (2 : ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, Real.rpow_one,
      Real.rpow_two, sq_abs]
    rw [show -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by ring]
    ring
  simp only [e]
  rw [integral_comp_abs (f := fun t : ℝ => (√(2 * Real.pi))⁻¹ *
    (t ^ (1 : ℝ) * Real.exp (-(1 / 2) * t ^ (2 : ℝ)))), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by norm_num) (by norm_num)]
  norm_num
  have h2 : 2 * (√2)⁻¹ = √(2 : ℝ) := by rw [← div_eq_mul_inv, Real.div_sqrt]
  rw [mul_left_comm, h2, mul_comm, div_eq_mul_inv]

/-- If `e_1, …, e_N` are orthonormal then `(⟨g, e_k⟩)_k` is a standard Gaussian vector, for a
standard Gaussian vector `g`. -/
private theorem kc_map_adjoint (L : F →ₗᵢ[ℝ] E) :
    (stdGaussian E).map (ContinuousLinearMap.adjoint L.toContinuousLinearMap) = stdGaussian F := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_stdGaussian, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.adjoint_inner_left]
  have h := charFun_stdGaussian (L t)
  rw [charFun_apply, L.norm_map] at h
  exact h

/-- The contraction principle and the rotation in the proofs of HNVW II, Proposition 7.4.22, p. 124,
and Theorem 7.1.20, p. 71, in one step: for orthonormal `e_1, …, e_N` in `E`,
`E ‖Σ_k g_k T (e_k)‖² ≤ E ‖T g‖²`. The vector `(⟨g, e_k⟩)_k` is standard Gaussian,
`Σ_k ⟨g, e_k⟩ e_k = P g` is the projection of `g`, and `P g = (g + R g) / 2`, where the reflection
`R = 2P − 1` changes the signs of the coordinates of `g` in the orthogonal complement of the `e_k`.
-/
private theorem kc_integral_orthonormal_le (T : E →L[ℝ] X) {e : Fin N → E}
    (he : Orthonormal ℝ e) :
    ∫ g, ‖∑ k, g k • T (e k)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      ∫ g, ‖T g‖ ^ 2 ∂stdGaussian E := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hb : ∀ k, kcSum e (b k) = e k := fun k => by
    rw [kcSum_apply]
    simp [b, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  set L : EuclideanSpace ℝ (Fin N) →ₗᵢ[ℝ] E :=
    (kcSum e).toLinearMap.isometryOfOrthonormal (v := b.toBasis) (by simp)
      (by simpa [Function.comp_def, hb] using he) with hL
  have hLs : ∀ g : EuclideanSpace ℝ (Fin N), T (L g) = ∑ k, g k • T (e k) := fun g => by
    have : L g = kcSum e g := rfl
    rw [this, kcSum_apply, map_sum]
    simp only [map_smul]
  set A := ContinuousLinearMap.adjoint L.toContinuousLinearMap with hA
  have hAi : ∀ x y, inner ℝ (L x) y = inner ℝ x (A y) := fun x y =>
    (ContinuousLinearMap.adjoint_inner_right L.toContinuousLinearMap x y).symm
  -- the reflection
  set R₀ : E →ₗᵢ[ℝ] E :=
    { toLinearMap := (2 : ℝ) • (L.toLinearMap ∘ₗ A.toLinearMap) - LinearMap.id
      norm_map' := fun g => by
        have h1 : ‖(2 : ℝ) • L (A g) - g‖ ^ 2 = ‖g‖ ^ 2 := by
          rw [norm_sub_sq_real, norm_smul, mul_pow, L.norm_map, real_inner_smul_left, hAi,
            real_inner_self_eq_norm_sq]
          norm_num
          ring
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1 }
  set R : E ≃ₗᵢ[ℝ] E := R₀.toLinearIsometryEquiv rfl
  have hR : ∀ g, T (L (A g)) = (2 : ℝ)⁻¹ • (T g + T (R g)) := fun g => by
    have : R g = (2 : ℝ) • L (A g) - g := rfl
    rw [← map_add, this, add_sub_cancel, map_smul, smul_smul]
    norm_num
  have hint := kc_integrable_norm_sq T
  have hintR : Integrable (fun g => ‖T (R g)‖ ^ 2) (stdGaussian E) :=
    kc_integrable_norm_sq (T ∘L R.toContinuousLinearEquiv.toContinuousLinearMap)
  calc ∫ g, ‖∑ k, g k • T (e k)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N))
      = ∫ g, ‖T (L (A g))‖ ^ 2 ∂stdGaussian E := by
        simp only [← hLs]
        rw [← kc_map_adjoint L, integral_map (by fun_prop)
          (Continuous.aestronglyMeasurable (by fun_prop))]
    _ ≤ ∫ g, (2 : ℝ)⁻¹ * (‖T g‖ ^ 2 + ‖T (R g)‖ ^ 2) ∂stdGaussian E := by
        refine integral_mono ?_ ((hint.add hintR).const_mul _) fun g => ?_
        · exact kc_integrable_norm_sq (T ∘L L.toContinuousLinearMap ∘L A)
        · rw [hR, norm_smul, mul_pow]
          have h1 := norm_add_le (T g) (T (R g))
          have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          norm_num
          nlinarith [sq_nonneg (‖T g‖ - ‖T (R g)‖)]
    _ = ∫ g, ‖T g‖ ^ 2 ∂stdGaussian E := by
        rw [integral_const_mul, integral_add hint hintR,
          kc_integral_comp R fun g => ‖T g‖ ^ 2]
        ring

end Gaussian

/-! ### Type 2 and K-convexity -/

/-- The second moments in the definition of type 2. -/
private theorem kc_avg_norm_sq_le {τ : ℝ} (h : IsTypeTwoBound X τ) (x : Fin N → X) :
    (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • x k‖ ^ 2) ≤ τ ^ 2 * ∑ k, ‖x k‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (lpNorm_nonneg (fun _ => norm_nonneg _) _ _) (h N x) 2
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), ← Real.rpow_two,
    lpNorm_rpow (fun _ => norm_nonneg _) two_pos] at h1
  simpa only [Real.rpow_two] using h1

/-- The average over the signs may be put inside: `E_g φ (g) = E_g E_ε φ (ε g)`. -/
private theorem kc_integral_eq_integral_avg (y : Fin N → X) :
    ∫ g, ‖∑ k, g k • y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) =
      ∫ g, (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • g k • y k‖ ^ 2)
        ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  have hε : ∀ ε : Fin N → Bool, (∫ g, ‖∑ k, coin (ε k) • g k • y k‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin N))) =
      ∫ g, ‖∑ k, g k • y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := fun ε => by
    rw [← kc_integral_sign ε fun g => ‖∑ k, g k • y k‖ ^ 2]
    simp only [smul_smul]
  have hi : ∀ ε : Fin N → Bool, Integrable (fun g : EuclideanSpace ℝ (Fin N) =>
      ‖∑ k, coin (ε k) • g k • y k‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin N))) := fun ε => by
    have := kc_integrable_norm_sq (kcSum fun k => coin (ε k) • y k)
    simpa only [kcSum_apply, smul_comm (coin _)] using this
  simp only [avg]
  rw [integral_div, integral_finsetSum _ fun ε _ => hi ε]
  simp only [hε]
  rw [← avg, avg_const]

private theorem kc_integrable_avg (y : Fin N → X) :
    Integrable (fun g : EuclideanSpace ℝ (Fin N) =>
      avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • g k • y k‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  refine (integrable_finsetSum _ fun ε _ => ?_).div_const _
  have := kc_integrable_norm_sq (kcSum fun k => coin (ε k) • y k)
  simpa only [kcSum_apply, smul_comm (coin _)] using this

/-- Type 2 implies Gaussian type 2, finite sequences. -/
private theorem kc_integral_fin_le {τ : ℝ} (h : IsTypeTwoBound X τ) (y : Fin N → X) :
    ∫ g, ‖∑ k, g k • y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      τ ^ 2 * ∑ k, ‖y k‖ ^ 2 := by
  have hi : ∀ k, Integrable (fun g : EuclideanSpace ℝ (Fin N) => g k ^ 2 * ‖y k‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := fun k => by
    have := kc_integrable_norm_sq (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    simp only [PiLp.proj_apply, Real.norm_eq_abs, sq_abs] at this
    exact this.mul_const _
  rw [kc_integral_eq_integral_avg]
  calc ∫ g, (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • g k • y k‖ ^ 2)
        ∂stdGaussian (EuclideanSpace ℝ (Fin N))
      ≤ ∫ g, τ ^ 2 * ∑ k, g k ^ 2 * ‖y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
        refine integral_mono (kc_integrable_avg y)
          ((integrable_finsetSum _ fun k _ => hi k).const_mul _) fun g => ?_
        refine (kc_avg_norm_sq_le h fun k => g k • y k).trans_eq ?_
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ = τ ^ 2 * ∑ k, ‖y k‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun k _ => hi k]
        simp only [integral_mul_const, kc_integral_sq, one_mul]

/-- Type 2 implies Gaussian type 2, with the same constant (HNVW II, Proposition 7.1.18 (1) from
Proposition 7.1.16 (1), pp. 66–68, for real Gaussian variables):
`E ‖Σ g_i y_i‖² ≤ τ² Σ ‖y_i‖²` for independent standard Gaussian `g_i`. -/
theorem IsTypeTwoBound.integral_stdGaussian_le {τ : ℝ} (h : IsTypeTwoBound X τ) {ι : Type*}
    [Fintype ι] (y : ι → X) :
    ∫ g, ‖∑ i, g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤ τ ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
  set e := Fintype.equivFin ι
  have h1 := kc_integral_fin_le h fun k => y (e.symm k)
  rw [e.symm.sum_comp fun i => ‖y i‖ ^ 2] at h1
  refine le_trans (le_of_eq ?_) h1
  rw [← kc_integral_comp (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)]
  refine integral_congr_ae (ae_of_all _ fun g => congrArg (fun z => ‖z‖ ^ 2) ?_)
  rw [← e.symm.sum_comp]
  exact Finset.sum_congr rfl fun k _ => by simp [Equiv.piCongrLeft']

/-- `E |g_k| = √(2/π)`. -/
private theorem kc_integral_abs_eval (k : Fin N) :
    ∫ g : EuclideanSpace ℝ (Fin N), |g k| ∂stdGaussian (EuclideanSpace ℝ (Fin N)) =
      √(2 / Real.pi) := by
  have h := kc_measurePreserving_eval k
  rw [← kc_integral_abs, ← h.map_eq, integral_map h.measurable.aemeasurable (by fun_prop)]

/-- The sums with the coefficients `ε_k |g_k|` are the sums with the coefficients `g_k`, up to
signs. -/
private theorem kc_norm_sum_abs (x : Fin N → X) (ε : Fin N → Bool) (g : EuclideanSpace ℝ (Fin N)) :
    ‖∑ k, (coin (ε k) * |g k|) • x k‖ =
      ‖∑ k, coin (mul (fun j => decide (0 ≤ g j)) ε k) • g k • x k‖ := by
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, coin_mul_apply]
  congr 1
  by_cases hk : 0 ≤ g k
  · simp [hk, abs_of_nonneg hk]
  · simp [hk, abs_of_neg (not_le.1 hk)]

private theorem kc_integrable_abs (x : Fin N → X) (ε : Fin N → Bool) :
    Integrable (fun g : EuclideanSpace ℝ (Fin N) => ‖∑ k, (coin (ε k) * |g k|) • x k‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  refine ((kc_integrable_avg x).const_mul (2 ^ N)).mono' ?_ (ae_of_all _ fun g => ?_)
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · rw [Real.norm_of_nonneg (by positivity), kc_norm_sum_abs]
    exact le_two_pow_mul_avg (g := fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • g k • x k‖ ^ 2)
      (fun _ => by positivity) _

/-- The map `t ↦ ‖Σ ε_k t_k x_k‖²` is convex. -/
private theorem kc_convexOn (x : Fin N → X) (ε : Fin N → Bool) :
    ConvexOn ℝ Set.univ fun t : Fin N → ℝ => ‖∑ k, (coin (ε k) * t k) • x k‖ ^ 2 := by
  have h : ConvexOn ℝ Set.univ fun t : Fin N → ℝ => ‖∑ k, (coin (ε k) * t k) • x k‖ := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb _ => ?_⟩
    have e : ∑ k, (coin (ε k) * (a • s + b • t) k) • x k =
        a • ∑ k, (coin (ε k) * s k) • x k + b • ∑ k, (coin (ε k) * t k) • x k := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    beta_reduce
    rw [e]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, smul_eq_mul,
      smul_eq_mul]
  exact h.pow (fun _ _ => norm_nonneg _) 2

/-- The step of Jensen's inequality in the proof of HNVW II, Proposition 6.1.15:
`(E |g|)² ‖Σ ε_k x_k‖² ≤ E ‖Σ ε_k |g_k| x_k‖²` for fixed signs `ε_k`. -/
private theorem kc_jensen (x : Fin N → X) (ε : Fin N → Bool) :
    2 / Real.pi * ‖∑ k, coin (ε k) • x k‖ ^ 2 ≤
      ∫ g, ‖∑ k, (coin (ε k) * |g k|) • x k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  have hgi : ∀ k, Integrable (fun g : EuclideanSpace ℝ (Fin N) => |g k|)
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := fun k =>
    ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).integrable_comp
      IsGaussian.integrable_id).abs
  have hc : Continuous fun t : Fin N → ℝ => ‖∑ k, (coin (ε k) * t k) • x k‖ ^ 2 := by fun_prop
  have h := (kc_convexOn x ε).map_integral_le (μ := stdGaussian (EuclideanSpace ℝ (Fin N)))
    (f := fun g k => |g k|) hc.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
    (Integrable.of_eval hgi) (kc_integrable_abs x ε)
  refine le_trans (le_of_eq ?_) h
  have he : (∫ g, (fun k => |g k|) ∂stdGaussian (EuclideanSpace ℝ (Fin N))) =
      fun _ : Fin N => √(2 / Real.pi) := by
    funext k
    rw [eval_integral hgi, kc_integral_abs_eval]
  rw [he]
  simp only [mul_comm _ √(2 / Real.pi), ← smul_smul, ← Finset.smul_sum]
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- Rademacher sums are dominated by Gaussian sums (HNVW II, Proposition 6.1.15, pp. 10–11, `p = 2`,
real Gaussian variables): `E ‖Σ ε_k x_k‖² ≤ (π/2) E ‖Σ g_k x_k‖²`. -/
theorem avg_norm_sq_le_integral_stdGaussian (x : Fin N → X) :
    (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • x k‖ ^ 2) ≤
      Real.pi / 2 * ∫ g, ‖∑ k, g k • x k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  have hπ := Real.pi_pos
  calc (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • x k‖ ^ 2)
      = Real.pi / 2 * avg fun ε : Fin N → Bool =>
          2 / Real.pi * ‖∑ k, coin (ε k) • x k‖ ^ 2 := by
        rw [avg_const_mul, ← mul_assoc, div_mul_div_cancel₀ two_ne_zero, div_self hπ.ne', one_mul]
    _ ≤ Real.pi / 2 * avg fun ε : Fin N → Bool => ∫ g, ‖∑ k, (coin (ε k) * |g k|) • x k‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin N)) :=
        mul_le_mul_of_nonneg_left (avg_mono (kc_jensen x)) (by positivity)
    _ = Real.pi / 2 * ∫ g, (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • g k • x k‖ ^ 2)
          ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
        congr 1
        simp only [avg]
        rw [← integral_finsetSum _ fun ε _ => kc_integrable_abs x ε, ← integral_div]
        refine integral_congr_ae (ae_of_all _ fun g => ?_)
        simp only [kc_norm_sum_abs]
        exact avg_mul_left (fun j => decide (0 ≤ g j)) fun ε => ‖∑ k, coin (ε k) • g k • x k‖ ^ 2
    _ = Real.pi / 2 * ∫ g, ‖∑ k, g k • x k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
        rw [← kc_integral_eq_integral_avg]

/-- With `x_k = E (ε_k f)`, `E ‖Σ_k g_k x_k‖² ≤ E ‖Σ_η g_η 2^{−N/2} f (η)‖²`. The statement is the
instance of the covariance domination, HNVW II, Theorem 6.1.25, p. 16, used in the proof of
Proposition 7.4.21, p. 123, for the orthonormal system of the signs. Departure from the source, in
form: the proof does not go through Theorem 6.1.25, nor through the Walsh functions, as that of
Proposition 7.4.22 does; it is the contraction principle of the proof of Proposition 7.4.22, p. 124,
and the rotation of the proof of Theorem 7.1.20, p. 71, merged into one step by the reflection
`2P − 1`, `P` the orthogonal projection on the span of the signs (`kc_integral_orthonormal_le`). -/
theorem integral_stdGaussian_rademacherCoeff_le (f : (Fin N → Bool) → X) :
    ∫ g, ‖∑ k, g k • rademacherCoeff f k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      ∫ g, ‖∑ η, g η • √((2 : ℝ) ^ N)⁻¹ • f η‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin N → Bool)) := by
  set E := EuclideanSpace ℝ (Fin N → Bool)
  set c : ℝ := √((2 : ℝ) ^ N)⁻¹ with hc
  have hc2 : c * c = ((2 : ℝ) ^ N)⁻¹ := Real.mul_self_sqrt (by positivity)
  -- the orthonormal system `e_k = 2^{-N/2} ε_k`
  set e : Fin N → E := fun k => WithLp.toLp 2 fun η => c * coin (η k) with he
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← avg_coin_mul_coin i j, PiLp.inner_apply, avg, div_eq_inv_mul, Finset.mul_sum, ← hc2]
    refine Finset.sum_congr rfl fun η _ => ?_
    simp only [he, RCLike.inner_apply, conj_trivial]
    ring
  have hT : ∀ k, kcSum (fun η => c • f η) (e k) = rademacherCoeff f k := fun k => by
    rw [kcSum_apply, rademacherCoeff, Finset.smul_sum, ← hc2]
    refine Finset.sum_congr rfl fun η _ => ?_
    simp only [he, smul_smul]
    congr 1
    ring
  have h := kc_integral_orthonormal_le (kcSum fun η => c • f η) hon
  simpa only [hT, kcSum_apply] using h

/-- **Type 2 implies K-convexity** in `L²`, with the constant `√(π/2) τ` (HNVW II, Proposition
7.4.22, p. 124, with Proposition 7.1.18, p. 67; Maurey–Pisier (1976), Remark 2.10, as quoted by
Pisier (1998), p. 106). -/
theorem IsTypeTwoBound.isKConvexBound {τ : ℝ} (h : IsTypeTwoBound X τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) := by
  intro N f
  -- a negative `τ` is possible only if `X = 0`
  rcases lt_or_ge τ 0 with hτ | hτ
  · have hX : ∀ x : X, ‖x‖ = 0 := fun x => by
      have h1 := (lpNorm_nonneg (fun _ => norm_nonneg _) _ _).trans (h 1 fun _ => x)
      rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg x)] at h1
      exact le_antisymm (nonpos_of_mul_nonneg_right h1 hτ) (norm_nonneg x)
    simp [SignCube.lpNorm, hX]
  have h0 : ∀ g : (Fin N → Bool) → X, SignCube.lpNorm (fun y => ‖y‖) 2 g =
      √(avg fun ε => ‖g ε‖ ^ 2) := fun g => by
    rw [SignCube.lpNorm, ← Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
  have h1 : (avg fun ε => ‖rademacherProj f ε‖ ^ 2) ≤
      Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2) := by
    calc (avg fun ε => ‖rademacherProj f ε‖ ^ 2)
        ≤ Real.pi / 2 * ∫ g, ‖∑ k, g k • rademacherCoeff f k‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ (Fin N)) :=
          avg_norm_sq_le_integral_stdGaussian (rademacherCoeff f)
      _ ≤ Real.pi / 2 * ∫ g, ‖∑ η, g η • √((2 : ℝ) ^ N)⁻¹ • f η‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ (Fin N → Bool)) :=
          mul_le_mul_of_nonneg_left (integral_stdGaussian_rademacherCoeff_le f) (by positivity)
      _ ≤ Real.pi / 2 * (τ ^ 2 * ∑ η, ‖√((2 : ℝ) ^ N)⁻¹ • f η‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (h.integral_stdGaussian_le fun η => √((2 : ℝ) ^ N)⁻¹ • f η) (by positivity)
      _ = Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2) := by
          congr 2
          simp only [avg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          rw [← Finset.mul_sum, Real.sq_sqrt (by positivity), div_eq_inv_mul]
  rw [h0, h0]
  calc √(avg fun ε => ‖rademacherProj f ε‖ ^ 2)
      ≤ √(Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2)) := Real.sqrt_le_sqrt h1
    _ = √(Real.pi / 2) * τ * √(avg fun ε => ‖f ε‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hτ,
          mul_assoc]

end BanachProbability
