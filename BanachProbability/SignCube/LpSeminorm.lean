module

public import BanachProbability.SignCube.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# `L^p` norms of functions on the sign cube

For a function `nrm : E → ℝ` (a norm or seminorm of the values) and `p > 0`,
`SignCube.lpNorm nrm p X = (E nrm (X ε)^p)^{1/p}` is the `L^p` norm of a random variable `X` on
the sign cube. For a seminorm `N` on a real vector space and `p ≥ 1` it is a seminorm on
`(Fin n → Bool) → E` (Minkowski's inequality), `lpSeminorm N p`; it is nondecreasing in `p`
(the power-mean inequality).
-/

@[expose] public section

namespace BanachProbability.SignCube

variable {N : ℕ} {E : Type*}

/-- The `L^p` norm `(E nrm (X ε)^p)^{1/p}` of a random variable `X` on the sign cube, the values
measured with `nrm`. -/
protected noncomputable def lpNorm (nrm : E → ℝ) (p : ℝ) (X : (Fin N → Bool) → E) : ℝ :=
  avg (fun ε => nrm (X ε) ^ p) ^ (1 / p)

theorem lpNorm_nonneg {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) (p : ℝ) (X : (Fin N → Bool) → E) :
    0 ≤ SignCube.lpNorm nrm p X :=
  Real.rpow_nonneg (avg_nonneg fun _ => Real.rpow_nonneg (hnrm _) p) _

/-- The `L^p` norm as a normalised `ℓ^p` sum: `(Σ_ε nrm (X ε)^p)^{1/p} / (2^N)^{1/p}`. -/
theorem scb_lpNorm_eq_sum {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) (p : ℝ)
    (X : (Fin N → Bool) → E) :
    SignCube.lpNorm nrm p X = (∑ ε, nrm (X ε) ^ p) ^ (1 / p) / ((2 : ℝ) ^ N) ^ (1 / p) :=
  Real.div_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (hnrm _) p) (by positivity) _

/-- The power-mean inequality: `‖X‖_p ≤ ‖X‖_q` for `0 < p ≤ q`. -/
theorem lpNorm_mono_exponent {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (X : (Fin N → Bool) → E) : SignCube.lpNorm nrm p X ≤ SignCube.lpNorm nrm q X := by
  have hq : 0 < q := hp.trans_le hpq
  have ha : ∀ ε, 0 ≤ nrm (X ε) ^ p := fun ε => Real.rpow_nonneg (hnrm _) p
  have hA : 0 ≤ avg fun ε => nrm (X ε) ^ p := avg_nonneg ha
  have e : ∀ g : (Fin N → Bool) → ℝ, avg g = ∑ ε, ((2 : ℝ) ^ N)⁻¹ * g ε := fun g => by
    rw [avg, div_eq_inv_mul, Finset.mul_sum]
  -- Jensen's inequality for the convex map `t ↦ t^{q/p}` and the weights `2^{-N}`
  have hJ : (avg fun ε => nrm (X ε) ^ p) ^ (q / p) ≤ avg fun ε => nrm (X ε) ^ q := by
    have hw : ∑ _ε : Fin N → Bool, ((2 : ℝ) ^ N)⁻¹ = 1 := by
      simp
    rw [e, e]
    refine (Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => ((2 : ℝ) ^ N)⁻¹)
      (fun ε => nrm (X ε) ^ p) (fun _ _ => by positivity) hw (fun ε _ => ha ε)
      ((one_le_div hp).2 hpq)).trans_eq (Finset.sum_congr rfl fun ε _ => ?_)
    rw [← Real.rpow_mul (hnrm _), mul_div_cancel₀ _ hp.ne']
  unfold SignCube.lpNorm
  calc (avg fun ε => nrm (X ε) ^ p) ^ (1 / p)
      = ((avg fun ε => nrm (X ε) ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [← Real.rpow_mul hA]
        congr 1
        field_simp
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hJ (by positivity)

/-- Every value is bounded by `2^{N/p}` times the `L^p` norm. -/
theorem le_lpNorm {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {p : ℝ} (hp : 0 < p)
    (X : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    nrm (X ε) ≤ (2 : ℝ) ^ ((N : ℝ) / p) * SignCube.lpNorm nrm p X := by
  have ha : ∀ ε, 0 ≤ nrm (X ε) ^ p := fun ε => Real.rpow_nonneg (hnrm _) p
  unfold SignCube.lpNorm
  calc nrm (X ε) = (nrm (X ε) ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (hnrm _), mul_one_div_cancel hp.ne', Real.rpow_one]
    _ ≤ (2 ^ N * avg fun ε => nrm (X ε) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (ha ε) (le_two_pow_mul_avg ha ε) (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (avg_nonneg ha), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), mul_one_div]

section Seminorm

variable [AddCommGroup E] [Module ℝ E]

/-- Minkowski's inequality on the sign cube. -/
theorem lpNorm_add_le (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p) (X Y : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (X + Y) ≤ SignCube.lpNorm S p X + SignCube.lpNorm S p Y := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hS : ∀ x, 0 ≤ S x := apply_nonneg S
  rw [scb_lpNorm_eq_sum hS, scb_lpNorm_eq_sum hS, scb_lpNorm_eq_sum hS, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc (∑ ε, S ((X + Y) ε) ^ p) ^ (1 / p) ≤ (∑ ε, (S (X ε) + S (Y ε)) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (hS _) p)
          (Finset.sum_le_sum fun ε _ =>
            Real.rpow_le_rpow (hS _) (map_add_le_add S (X ε) (Y ε)) hp0.le)
          (by positivity)
    _ ≤ _ := Real.Lp_add_le_of_nonneg _ hp (fun _ _ => hS _) (fun _ _ => hS _)

theorem lpNorm_smul (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) (c : ℝ) (X : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (c • X) = ‖c‖ * SignCube.lpNorm S p X := by
  have hS : ∀ x, 0 ≤ S x := apply_nonneg S
  unfold SignCube.lpNorm
  simp only [Pi.smul_apply, map_smul_eq_mul, Real.mul_rpow (norm_nonneg c) (hS _), avg_const_mul]
  rw [Real.mul_rpow (by positivity) (avg_nonneg fun _ => Real.rpow_nonneg (hS _) p),
    ← Real.rpow_mul (norm_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `L^p` seminorm `X ↦ (E S (X ε)^p)^{1/p}` on `E`-valued functions on the sign cube, for a
seminorm `S` on `E` and `p ≥ 1`. -/
noncomputable def lpSeminorm (S : Seminorm ℝ E) (p : ℝ) (hp : 1 ≤ p) :
    Seminorm ℝ ((Fin N → Bool) → E) :=
  Seminorm.of (SignCube.lpNorm S p) (lpNorm_add_le S hp)
    (fun c X => lpNorm_smul S (zero_lt_one.trans_le hp) c X)

@[simp] theorem lpSeminorm_apply (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p)
    (X : (Fin N → Bool) → E) : lpSeminorm S p hp X = SignCube.lpNorm S p X :=
  rfl

end Seminorm

end BanachProbability.SignCube
