module

public import BanachProbability.SignCube.Walsh
public import BanachProbability.TypeTwo.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import BanachProbability.RandomSums.Contraction
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
constant `√(π/2) τ`. B. Maurey and G. Pisier, *Séries de variables aléatoires vectorielles
indépendantes et propriétés géométriques des espaces de Banach*, Studia Math. 58 (1976), Remark
2.10, p. 88, state it without constant and without proof: "On peut montrer facilement que tout
espace de type 2-Rademacher est K-convexe". The proof is that of HNVW II, Proposition 7.4.22, p.
124, with the results it cites, for `p = 2` and real Gaussian variables:

* Proposition 7.1.18 (1) from Proposition 7.1.16 (1), pp. 66–68: type 2 gives Gaussian type 2 with
  the same constant (`IsTypeTwoBound.integral_stdGaussian_le`);
* Proposition 6.1.15, pp. 10–11: Rademacher sums are dominated by Gaussian sums, with the factor
  `1 / E |g| = √(π/2)` (`avg_norm_sq_le_integral_stdGaussian`);
* Theorem 6.1.13 (i), pp. 9–10: Kahane's contraction principle for Gaussian sums
  (`integral_stdGaussian_smul_le`);
* Theorem 7.1.20 (2), pp. 69–71, for an orthonormal system on a finite set with a measure: in a
  space of type 2 the Gaussian sums are dominated by the sums over the system
  (`IsTypeTwoBound.integral_stdGaussian_le_of_orthonormal`).

With the Walsh expansion `f = Σ_α w_α x_α` of (7.35), p. 123, `π_N f = Σ_n w_{n} x_{n}`
(`rademacherProj_eq_sum_walsh`), and the chain of the proof of Proposition 7.4.22 is, in `L²`,
`‖Σ_n w_{n} x_{n}‖ ≤ √(π/2) ‖Σ_n g_{n} x_{n}‖ ≤ √(π/2) ‖Σ_α g_α x_α‖ ≤ √(π/2) τ ‖Σ_α w_α x_α‖`.

A shorter argument, not used here: the contraction principle and the rotation in Theorem 7.1.20 are
one step, without Walsh functions, by the reflection `2P − 1`, `P` the orthogonal projection on the
span of the signs.
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

/-- `E (ε_k f)` is the Walsh coefficient `x_{k}` of `f`. -/
theorem rademacherCoeff_eq_walshCoeff (f : (Fin N → Bool) → V) (k : Fin N) :
    rademacherCoeff f k = walshCoeff f {k} := by
  simp only [rademacherCoeff, walshCoeff, walsh_singleton]

/-- `π_N f = Σ_n w_{n} x_{n}` for `f = Σ_α w_α x_α` (HNVW II, (7.35), p. 123). -/
theorem rademacherProj_eq_sum_walsh (f : (Fin N → Bool) → V) (ε : Fin N → Bool) :
    rademacherProj f ε = ∑ k, walsh {k} ε • walshCoeff f {k} := by
  simp only [rademacherProj, rademacherCoeff_eq_walshCoeff, walsh_singleton]

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
standard Gaussian vector `g`: the adjoint of an isometry preserves standard Gaussian vectors. -/
private theorem kc_map_adjoint (L : F →ₗᵢ[ℝ] E) :
    (stdGaussian E).map (ContinuousLinearMap.adjoint L.toContinuousLinearMap) = stdGaussian F := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_stdGaussian, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.adjoint_inner_left]
  have h := charFun_stdGaussian (L t)
  rw [charFun_apply, L.norm_map] at h
  exact h

/-- The transformed sequence in the proof of HNVW II, Theorem 7.1.20, p. 71: if the rows of
`(q_{is})` are orthonormal then `γ̃_i = Σ_s q_{is} γ_s` is another standard Gaussian sequence. -/
private theorem kc_integral_orthonormal [DecidableEq ι] {κ : Type*} [Fintype κ] {q : ι → κ → ℝ}
    (hq : ∀ i j, ∑ s, q i s * q j s = if i = j then 1 else 0) (x : ι → X) :
    ∫ g, ‖∑ i, (∑ s, q i s * g s) • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ κ) =
      ∫ g, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
  set b := EuclideanSpace.basisFun ι ℝ
  set e : ι → EuclideanSpace ℝ κ := fun i => WithLp.toLp 2 (q i)
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← hq i j, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [e, RCLike.inner_apply, conj_trivial, mul_comm]
  have hb : ∀ i, kcSum e (b i) = e i := fun i => by
    rw [kcSum_apply]
    simp [b, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  -- the isometry `b_i ↦ q_i`, whose adjoint is `γ ↦ γ̃`
  set L : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
    (kcSum e).toLinearMap.isometryOfOrthonormal (v := b.toBasis) (by simp)
      (by simpa [Function.comp_def, hb] using he)
  have hL : ∀ (g : EuclideanSpace ℝ κ) (i : ι),
      ContinuousLinearMap.adjoint L.toContinuousLinearMap g i = ∑ s, q i s * g s := fun g i => by
    have h1 : L (b i) = e i := hb i
    have h2 := ContinuousLinearMap.adjoint_inner_right L.toContinuousLinearMap (b i) g
    rw [EuclideanSpace.basisFun_inner, LinearIsometry.coe_toContinuousLinearMap, h1,
      PiLp.inner_apply] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [e, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [← kc_map_adjoint L, integral_map (by fun_prop)
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [hL]

/-- Gaussian sums do not depend on the enumeration of the index set. -/
private theorem kc_integral_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) (y : ι → X) :
    ∫ g, ‖∑ i, g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, ‖∑ k, g k • y (e.symm k)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← kc_integral_comp (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)]
  refine integral_congr_ae (ae_of_all _ fun g => congrArg (fun z => ‖z‖ ^ 2) ?_)
  rw [← e.symm.sum_comp]
  exact Finset.sum_congr rfl fun k _ => by simp [Equiv.piCongrLeft']

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
  rw [kc_integral_equiv e y]
  refine (kc_integral_fin_le h fun k => y (e.symm k)).trans_eq ?_
  rw [e.symm.sum_comp fun i => ‖y i‖ ^ 2]

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

/-- Kahane's contraction principle for Gaussian sums, finite sequences. -/
private theorem kc_integral_smul_fin_le {c : Fin N → ℝ} (hc : ∀ k, |c k| ≤ 1) (y : Fin N → X) :
    ∫ g, ‖∑ k, g k • c k • y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      ∫ g, ‖∑ k, g k • y k‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  -- randomisation
  rw [kc_integral_eq_integral_avg, kc_integral_eq_integral_avg]
  refine integral_mono (kc_integrable_avg _) (kc_integrable_avg _) fun g => ?_
  -- the contraction principle for the Rademacher sums of the `g_k y_k`
  have h := lpNorm_sum_coin_smul_le one_le_two hc fun k => g k • y k
  have h2 := pow_le_pow_left₀ (lpNorm_nonneg (fun _ => norm_nonneg _) _ _) h 2
  rw [← Real.rpow_two, ← Real.rpow_two, lpNorm_rpow (fun _ => norm_nonneg _) two_pos,
    lpNorm_rpow (fun _ => norm_nonneg _) two_pos] at h2
  simpa only [Real.rpow_two, smul_comm (c _)] using h2

/-- **Kahane's contraction principle** for Gaussian sums (HNVW II, Theorem 6.1.13 (i), pp. 9–10, for
`ξ_i = g_i y_i`, `p = 2`): `E ‖Σ g_i c_i y_i‖² ≤ E ‖Σ g_i y_i‖²` for real `|c_i| ≤ 1`, by
randomisation from the case of Rademacher sums. -/
theorem integral_stdGaussian_smul_le {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, |c i| ≤ 1)
    (y : ι → X) :
    ∫ g, ‖∑ i, g i • c i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ∫ g, ‖∑ i, g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
  set e := Fintype.equivFin ι
  rw [kc_integral_equiv e fun i => c i • y i, kc_integral_equiv e y]
  exact kc_integral_smul_fin_le (fun k => hc (e.symm k)) fun k => y (e.symm k)

/-- HNVW II, Theorem 7.1.20 (2), pp. 69–71, for an orthonormal system `(f_i)` of functions on a
finite set `S` with a measure `μ`: in a space of type 2,
`E ‖Σ_i g_i x_i‖² ≤ τ² Σ_s μ (s) ‖Σ_i f_i (s) x_i‖²`. These are the simple functions of the proof in
the book, p. 71, which reduces to them a general orthogonal system in `L²`, by normalisation and by
Lemma 7.1.21; neither step is needed here. -/
theorem IsTypeTwoBound.integral_stdGaussian_le_of_orthonormal {τ : ℝ} (h : IsTypeTwoBound X τ)
    {S ι : Type*} [Fintype S] [Fintype ι] [DecidableEq ι] (μ : S → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (f : ι → S → ℝ) (hf : ∀ i j, ∑ s, μ s * f i s * f j s = if i = j then 1 else 0) (x : ι → X) :
    ∫ g, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      τ ^ 2 * ∑ s, μ s * ‖∑ i, f i s • x i‖ ^ 2 := by
  -- `q_{is} = μ(s)^{1/2} f_i (s)` satisfies `Σ_s q_{is} q_{js} = δ_{ij}`
  have hq : ∀ i j, ∑ s, (√(μ s) * f i s) * (√(μ s) * f j s) = if i = j then 1 else 0 :=
    fun i j => by
      rw [← hf i j]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hμ s), mul_assoc]
  calc ∫ g, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)
      = ∫ g, ‖∑ i, (∑ s, √(μ s) * f i s * g s) • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ S) :=
        (kc_integral_orthonormal hq x).symm
    _ = ∫ g, ‖∑ s, g s • √(μ s) • ∑ i, f i s • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ S) := by
        refine integral_congr_ae (ae_of_all _ fun g => congrArg (fun z => ‖z‖ ^ 2) ?_)
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
    _ ≤ τ ^ 2 * ∑ s, ‖√(μ s) • ∑ i, f i s • x i‖ ^ 2 :=
        h.integral_stdGaussian_le fun s => √(μ s) • ∑ i, f i s • x i
    _ = τ ^ 2 * ∑ s, μ s * ‖∑ i, f i s • x i‖ ^ 2 := by
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hμ _)]

/-- The second inequality in the proof of HNVW II, Proposition 7.4.22, p. 124,
`‖Σ_n g_{n} x_{n}‖ ≤ ‖Σ_α g_α x_α‖` in `L²`: the contraction principle with the coefficients `1` at
the singletons and `0` at the other `α`. -/
private theorem kc_integral_singleton_le (x : Finset (Fin N) → X) :
    ∫ g, ‖∑ k, g k • x {k}‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      ∫ g, ‖∑ α, g α • x α‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Finset (Fin N))) := by
  set s : Finset (Finset (Fin N)) := Finset.univ.image fun k => {k} with hs
  set c : Finset (Fin N) → ℝ := fun α => if α ∈ s then 1 else 0
  have hc : ∀ α, |c α| ≤ 1 := fun α => by
    by_cases h : α ∈ s <;> simp [c, h]
  -- `(g_{n})_n` is a standard Gaussian sequence
  have hq : ∀ i j : Fin N, ∑ α : Finset (Fin N), (if α = {i} then (1 : ℝ) else 0) *
      (if α = {j} then 1 else 0) = if i = j then 1 else 0 := fun i j => by
    simp [Finset.singleton_inj, eq_comm (a := j)]
  rw [← kc_integral_orthonormal hq fun k => x {k}]
  refine (le_of_eq ?_).trans (integral_stdGaussian_smul_le hc x)
  refine integral_congr_ae (ae_of_all _ fun g => congrArg (fun z => ‖z‖ ^ 2) ?_)
  have h1 : ∀ α, g α • c α • x α = if α ∈ s then g α • x α else 0 := fun α => by
    by_cases h : α ∈ s <;> simp [c, h]
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter, hs,
    Finset.sum_image fun _ _ _ _ h => Finset.singleton_injective h]
  simp

/-- **Type 2 implies K-convexity** in `L²`, with the constant `√(π/2) τ` (HNVW II, Proposition
7.4.22, p. 124, with Proposition 7.1.18, p. 67; without proof, Maurey–Pisier (1976), Remark 2.10,
p. 88). (In the proof in the book, "cotype 2 implies Gaussian cotype 2" is a misprint for type 2.)
-/
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
  have hw : ∀ α β : Finset (Fin N), ∑ ε, ((2 : ℝ) ^ N)⁻¹ * walsh α ε * walsh β ε =
      if α = β then 1 else 0 := fun α β => by
    simp only [← avg_walsh_mul_walsh α β, avg, mul_assoc, ← Finset.mul_sum, div_eq_inv_mul]
  have h1 : (avg fun ε => ‖rademacherProj f ε‖ ^ 2) ≤
      Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2) := by
    calc (avg fun ε => ‖rademacherProj f ε‖ ^ 2)
        ≤ Real.pi / 2 * ∫ g, ‖∑ k, g k • walshCoeff f {k}‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ (Fin N)) := by
          simp only [rademacherProj_eq_sum_walsh, walsh_singleton]
          exact avg_norm_sq_le_integral_stdGaussian fun k => walshCoeff f {k}
      _ ≤ Real.pi / 2 * ∫ g, ‖∑ α, g α • walshCoeff f α‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ (Finset (Fin N))) :=
          mul_le_mul_of_nonneg_left (kc_integral_singleton_le (walshCoeff f)) (by positivity)
      _ ≤ Real.pi / 2 * (τ ^ 2 * ∑ ε, ((2 : ℝ) ^ N)⁻¹ * ‖∑ α, walsh α ε • walshCoeff f α‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h.integral_stdGaussian_le_of_orthonormal
            (fun _ => ((2 : ℝ) ^ N)⁻¹) (fun _ => by positivity) walsh hw _) (by positivity)
      _ = Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2) := by
          simp only [sum_walsh_smul_walshCoeff, avg, ← Finset.mul_sum, div_eq_inv_mul]
  rw [h0, h0]
  calc √(avg fun ε => ‖rademacherProj f ε‖ ^ 2)
      ≤ √(Real.pi / 2 * (τ ^ 2 * avg fun ε => ‖f ε‖ ^ 2)) := Real.sqrt_le_sqrt h1
    _ = √(Real.pi / 2) * τ * √(avg fun ε => ‖f ε‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hτ,
          mul_assoc]

end BanachProbability
