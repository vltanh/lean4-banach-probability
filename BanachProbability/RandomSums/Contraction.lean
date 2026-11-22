module

public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Basic
import BanachProbability.UMD.ConvexHull

/-!
# Kahane's contraction principle

For vectors `x_k` in a normed space, independent real signs `ε_k`, `1 ≤ p < ∞` and scalars
`|c_k| ≤ 1`, `‖Σ ε_k c_k x_k‖_{L^p} ≤ ‖Σ ε_k x_k‖_{L^p}` for real `c_k` (`lpNorm_sum_coin_smul_le`),
and the same with the factor `π/2` for complex `c_k` (`lpNorm_sum_coin_smul_le_pi_div_two_mul`).
Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Proposition
3.2.10, pp. 181–182, with its proof from Lemma 3.2.11, pp. 182 and 185–186, and Proposition 3.2.14,
pp. 184–185; this is also the case `ξ_k = ε_k x_k` of Theorem 6.1.13 of *II* (2017), pp. 9–10, for
independent symmetric random variables `ξ_k`. Here the signs are real and `p < ∞`; complex signs and
the sharpness of `π/2` are not treated. Theorem 6.1.13 (i) for Gaussian sums, `ξ_k = g_k x_k`, with
`p = 2` and real scalars, is `integral_stdGaussian_smul_le` in `BanachProbability.KConvexity.Basic`.

The proof: the vector `(c_k)` is a combination `Σ_η w_η η` of sign vectors `η`, with `Σ |w_η| ≤ 1`
for real and `Σ |w_η| ≤ π/2` for complex `c_k` (Proposition 3.2.14); then the triangle inequality,
as `(η_k ε_k)_k` and `(ε_k)_k` have the same law.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- Lemma 3.2.11 in `L^p` and the equality of the laws of `(η_k ε_k)_k` and `(ε_k)_k`: if
`c = Σ_η w_η η` with sign vectors `η`, then
`‖Σ ε_k c_k x_k‖_{L^p} ≤ Σ_η |w_η| ‖Σ ε_k x_k‖_{L^p}`. -/
private theorem lpNorm_sum_coin_smul_le_sum_norm_mul {𝕜 : Type*} [NormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] {p : ℝ}
    (hp : 1 ≤ p) {c : Fin N → 𝕜} {w : (Fin N → Bool) → 𝕜}
    (hw : ∀ k, c k = ∑ η, coin (η k) • w η) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      (∑ η, ‖w η‖) *
        SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hS : ∀ X : (Fin N → Bool) → E,
      SignCube.lpNorm (fun y => ‖y‖) p X = lpSeminorm (normSeminorm ℝ E) p hp X := fun X => by
    rw [lpSeminorm_apply, coe_normSeminorm]
  -- `(η_k ε_k)_k` and `(ε_k)_k` have the same law
  have hη : ∀ η : Fin N → Bool, SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin N → Bool => w η • ∑ k, coin (mul η ε k) • x k) = ‖w η‖ *
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
    intro η
    unfold SignCube.lpNorm
    simp only [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [avg_const_mul, avg_mul_left η fun ε => ‖∑ k, coin (ε k) • x k‖ ^ p,
      Real.mul_rpow (by positivity) (avg_nonneg fun _ => by positivity),
      ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hsum : (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) =
      ∑ η, fun ε : Fin N → Bool => w η • ∑ k, coin (mul η ε k) • x k := by
    funext ε
    simp only [Finset.sum_apply, coin_mul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw k, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [smul_assoc, smul_smul, mul_comm, smul_comm]
  rw [hsum, hS, Finset.sum_mul]
  refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans_eq
    (Finset.sum_congr rfl fun η _ => ?_)
  rw [← hS, hη]

/-- **Kahane's contraction principle**, real scalars (HNVW I, Proposition 3.2.10, p. 181; II,
Theorem 6.1.13 (i), p. 9, for `ξ_k = ε_k x_k`). -/
theorem lpNorm_sum_coin_smul_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℝ}
    (hc : ∀ k, |c k| ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  -- Proposition 3.2.14: `c` is a convex combination of sign vectors `η`
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weights_sum_coin c hc
  refine (lpNorm_sum_coin_smul_le_sum_norm_mul hp (w := w) (fun k => ?_) x).trans_eq ?_
  · simp only [hw k, smul_eq_mul, mul_comm]
  · simp only [Real.norm_of_nonneg (hw0 _), hw1, one_mul]

/-- **Kahane's contraction principle**, complex scalars and real signs, with the factor `π/2`
(HNVW I, Proposition 3.2.10, (3.15), pp. 181–182; II, Theorem 6.1.13 (ii), p. 9, for
`ξ_k = ε_k x_k`). -/
theorem lpNorm_sum_coin_smul_le_pi_div_two_mul [NormedSpace ℂ E] {p : ℝ} (hp : 1 ≤ p)
    {c : Fin N → ℂ} (hc : ∀ k, ‖c k‖ ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      Real.pi / 2 *
        SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  -- Proposition 3.2.14: `c = Σ_η w_η η` with sign vectors `η` and `Σ_η |w_η| ≤ π/2`
  obtain ⟨w, hw1, hw⟩ := exists_sum_coin_complex c hc
  refine (lpNorm_sum_coin_smul_le_sum_norm_mul hp (w := w) (fun k => ?_) x).trans
    (mul_le_mul_of_nonneg_right hw1 (lpNorm_nonneg (fun _ => norm_nonneg _) _ _))
  simp only [hw k, Complex.real_smul, mul_comm]

/-- The homogeneous form of a contraction principle: an inequality with the constant `C` for
coefficients of modulus at most `1` gives one with `C M` for coefficients of modulus at most `M`. -/
private theorem lpNorm_sum_coin_smul_le_mul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] {p C M : ℝ} (hp : 1 ≤ p)
    (h : ∀ c : Fin N → 𝕜, (∀ k, ‖c k‖ ≤ 1) → ∀ x : Fin N → E,
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
        C * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k))
    {c : Fin N → 𝕜} (hc : ∀ k, ‖c k‖ ≤ M) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      C * M * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  have hp0 : 0 < p := by linarith
  have hS : ∀ X : (Fin N → Bool) → E,
      SignCube.lpNorm (fun y => ‖y‖) p X = lpSeminorm (normSeminorm ℝ E) p hp X := fun X => by
    rw [lpSeminorm_apply, coe_normSeminorm]
  have h0 : SignCube.lpNorm (fun y => ‖y‖) p (fun _ : Fin N → Bool => (0 : E)) = 0 := by
    rw [hS]
    exact map_zero _
  rcases lt_or_ge 0 M with hM | hM
  · -- the case `M = 1` for `c_k / M` and `M x_k`
    have h1 := h (fun k => M⁻¹ • c k) (fun k => by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hM.le, inv_mul_le_iff₀ hM, mul_one]
      exact hc k) fun k => M • x k
    have e1 : ∀ ε : Fin N → Bool, ∑ k, coin (ε k) • (M⁻¹ • c k) • M • x k =
        ∑ k, coin (ε k) • c k • x k := fun ε => Finset.sum_congr rfl fun k _ => by
      rw [smul_assoc, smul_comm (c k) M, inv_smul_smul₀ hM.ne']
    have e2 : (fun ε : Fin N → Bool => ∑ k, coin (ε k) • M • x k) =
        M • fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k := by
      funext ε
      rw [Pi.smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    simp only [e1] at h1
    rw [e2, hS (M • _), map_smul_eq_mul, ← hS, Real.norm_of_nonneg hM.le, ← mul_assoc] at h1
    exact h1
  · -- all `c_k = 0`
    have hc0 : ∀ k, c k = 0 := fun k => norm_le_zero_iff.1 ((hc k).trans hM)
    simp only [hc0, zero_smul, smul_zero, Finset.sum_const_zero, h0]
    rcases isEmpty_or_nonempty (Fin N) with hN | ⟨⟨k⟩⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, h0, mul_zero, le_refl]
    · rw [le_antisymm hM ((norm_nonneg _).trans (hc k)), mul_zero, zero_mul]

/-- **Kahane's contraction principle**, real scalars, with `max |c_k|` (HNVW I, Proposition 3.2.10,
p. 181). -/
theorem lpNorm_sum_coin_smul_le_max_mul [NormedSpace ℝ E] {p M : ℝ} (hp : 1 ≤ p) {c : Fin N → ℝ}
    (hc : ∀ k, |c k| ≤ M) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      M * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  have h := lpNorm_sum_coin_smul_le_mul (C := 1) hp (fun c hc x => by
    rw [one_mul]
    exact lpNorm_sum_coin_smul_le hp hc x) hc x
  rwa [one_mul] at h

/-- **Kahane's contraction principle**, complex scalars and real signs, with `(π/2) max |c_k|`
(HNVW I, Proposition 3.2.10, (3.15), pp. 181–182). -/
theorem lpNorm_sum_coin_smul_le_pi_div_two_mul_max_mul [NormedSpace ℂ E] {p M : ℝ} (hp : 1 ≤ p)
    {c : Fin N → ℂ} (hc : ∀ k, ‖c k‖ ≤ M) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      Real.pi / 2 * M *
        SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) :=
  lpNorm_sum_coin_smul_le_mul hp (fun _ hc x => lpNorm_sum_coin_smul_le_pi_div_two_mul hp hc x) hc x

/-- The contraction principle for complex scalars and real signs with the factor `2 ≥ π/2`. -/
theorem lpNorm_sum_coin_smul_le_two_mul [NormedSpace ℂ E] {p : ℝ} (hp : 1 ≤ p) {c : Fin N → ℂ}
    (hc : ∀ k, ‖c k‖ ≤ 1) (x : Fin N → E) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      2 * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) :=
  (lpNorm_sum_coin_smul_le_pi_div_two_mul hp hc x).trans (mul_le_mul_of_nonneg_right
    (by linarith [Real.pi_le_four]) (lpNorm_nonneg (fun _ => norm_nonneg _) _ _))

end BanachProbability
