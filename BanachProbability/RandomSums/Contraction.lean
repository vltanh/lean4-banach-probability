module

public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Basic
import BanachProbability.UMD.ConvexHull

/-!
# Kahane's contraction principle

For vectors `x_k` in a normed space, independent fair signs `ε_k`, `1 ≤ p < ∞` and scalars
`|c_k| ≤ 1`, `‖Σ ε_k c_k x_k‖_{L^p} ≤ ‖Σ ε_k x_k‖_{L^p}` for real `c_k` (`lpNorm_sum_coin_smul_le`),
and the same with the factor `2` for complex `c_k` (`lpNorm_sum_coin_smul_le_two_mul`, by real and
imaginary parts). Source: Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016),
Proposition 3.2.10, and *II* (2017), Theorem 6.1.13, p. 9; the sharp factor for complex scalars and
real signs, `π/2`, is not needed here.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- **Kahane's contraction principle**, real scalars. -/
theorem lpNorm_sum_coin_smul_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℝ}
    (hc : ∀ k, |c k| ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  -- Proposition 3.2.14: `c` is a convex combination of sign vectors `η`
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weights_sum_coin c hc
  have hS : ∀ X : (Fin N → Bool) → E,
      SignCube.lpNorm (fun y => ‖y‖) p X = lpSeminorm (normSeminorm ℝ E) p hp X := fun X => by
    rw [lpSeminorm_apply, coe_normSeminorm]
  -- `(η_k ε_k)_k` and `(ε_k)_k` have the same law
  have hη : ∀ η : Fin N → Bool, SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin N → Bool => ∑ k, coin (mul η ε k) • x k) =
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
    intro η
    unfold SignCube.lpNorm
    rw [avg_mul_left η fun ε => ‖∑ k, coin (ε k) • x k‖ ^ p]
  have hsum : (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) =
      ∑ η, w η • fun ε : Fin N → Bool => ∑ k, coin (mul η ε k) • x k := by
    funext ε
    simp only [Finset.sum_apply, Pi.smul_apply, coin_mul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, hw k, Finset.mul_sum]
    exact congrArg (· • x k) (Finset.sum_congr rfl fun η _ => by ring)
  calc SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k)
      = lpSeminorm (normSeminorm ℝ E) p hp
          (∑ η, w η • fun ε : Fin N → Bool => ∑ k, coin (mul η ε k) • x k) := by rw [hS, hsum]
    _ ≤ ∑ η, lpSeminorm (normSeminorm ℝ E) p hp
          (w η • fun ε : Fin N → Bool => ∑ k, coin (mul η ε k) • x k) :=
        Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
    _ = ∑ η, w η * SignCube.lpNorm (fun y => ‖y‖) p
          (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) :=
        Finset.sum_congr rfl fun η _ => by
          rw [map_smul_eq_mul, ← hS, hη, Real.norm_of_nonneg (hw0 η)]
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Kahane's contraction principle**, complex scalars and real signs, with the factor `2`. -/
theorem lpNorm_sum_coin_smul_le_two_mul [NormedSpace ℂ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℂ}
    (hc : ∀ k, ‖c k‖ ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      2 * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  have hS : ∀ X : (Fin N → Bool) → E,
      SignCube.lpNorm (fun y => ‖y‖) p X = lpSeminorm (normSeminorm ℝ E) p hp X := fun X => by
    rw [lpSeminorm_apply, coe_normSeminorm]
  -- real and imaginary parts
  have hsum : (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) =
      (fun ε : Fin N → Bool => ∑ k, coin (ε k) • (c k).re • x k) +
        fun ε : Fin N → Bool => ∑ k, coin (ε k) • (c k).im • Complex.I • x k := by
    funext ε
    rw [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im (c k), add_smul, mul_smul]
    simp only [Complex.coe_smul]
  have hI : ∀ y : E, ‖Complex.I • y‖ = ‖y‖ := fun y => by simp [norm_smul]
  have him : SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin N → Bool => ∑ k, coin (ε k) • Complex.I • x k) =
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
    unfold SignCube.lpNorm
    simp only [smul_comm _ Complex.I, ← Finset.smul_sum, hI]
  rw [hsum, hS, two_mul]
  refine (map_add_le_add _ _ _).trans (add_le_add ?_ ?_)
  · rw [← hS]
    exact lpNorm_sum_coin_smul_le hp (fun k => (Complex.abs_re_le_norm _).trans (hc k)) x
  · rw [← hS, ← him]
    exact lpNorm_sum_coin_smul_le hp (fun k => (Complex.abs_im_le_norm _).trans (hc k)) _

end BanachProbability
