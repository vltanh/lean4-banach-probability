module

public import BanachProbability.UMD.Maurey.Basic
public import BanachProbability.Martingale.Doob

/-!
# Extrapolation of the UMD property

A Banach space that is `UMD_{p₀}` for one `p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`, and
`UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)` (Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Theorem 4.2.7).

The proof is Burkholder's good-λ method (D. L. Burkholder, *Distribution function inequalities
for martingales*, Ann. Probab. 1 (1973); *A geometrical characterization of Banach spaces in which
martingale difference sequences are unconditional*, Ann. Probab. 9 (1981); for dyadic martingales
Pisier, *Martingales in Banach spaces* (2016), the second proof of the extrapolation theorem),
run on Paley–Walsh martingales, then lifted by Maurey's theorem (`dyadicUMDConst_eq_umdConst`).

* `goodLambda`: for a Paley–Walsh martingale `f`, its transform `g` by predictable signs,
  `β > 1`, `δ > 0` with `a = β − 1 − 2δ > 0` and `λ > 0`,
  `P (g* > βλ, f* ≤ δλ) ≤ (4 u δ / a)^p P (g* > λ)`, `u` a dyadic `UMD_p` constant. The stopping
  times `μ = inf {n : ‖g_n‖ > λ}`, `ν = inf {n : ‖g_n‖ > βλ}` and
  `σ = inf {n : ‖f_n‖ > δλ or ‖ξ_n‖ > 2δλ}` (a stopping time because the jumps are predictable)
  cut out the Paley–Walsh martingale `h = Σ 1_{μ < k ≤ ν ∧ σ} df_k`, with `‖h‖ ≤ 4δλ 1_{μ < ∞}`
  and `‖T h‖ ≥ aλ` on `{g* > βλ, f* ≤ δλ}`; apply the `UMD_p` bound to `h` and Chebyshev.
* `isDyadicUMDBound_of_goodLambda`: the layer-cake formula, absorption (every quantity is finite
  on the cube) and Doob's inequality (`SignCube.lpNorm_runningMax_le`) give, for every
  `r ∈ (1, ∞)`, the dyadic `UMD_r` constant
  `r' (β / δ) (1 − β^r (4 u δ / a)^p)^{−1/r}` whenever `β^r (4 u δ / a)^p < 1`.
* With `β`, `δ` chosen as functions of the exponents: `UMD_r^Δ ≤ 100 r* UMD_2^Δ`,
  `UMD_2^Δ ≤ 200 UMD_p^Δ`, and finiteness for every pair of exponents.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

section Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Burkholder's good-λ inequality** for Paley–Walsh martingales: with `f = Σ ε_k ξ_k`,
`g = Σ σ_k ε_k ξ_k` and `u` a dyadic `UMD_p` constant,
`P (g*_n > β t, f*_n ≤ δ t) ≤ (4 u δ / (β − 1 − 2δ))^p P (g*_n > t)`. -/
theorem goodLambda {p u : ℝ} (hp : 0 < p) (hu0 : 0 ≤ u)
    (hu : IsDyadicUMDBound X p (ENNReal.ofReal u)) {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    {σ : Fin N → (Fin N → Bool) → ℝ} (hξ : IsPredictable ξ) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) {β δ t : ℝ} (hβ : 1 < β) (hδ : 0 < δ)
    (ha : 0 < β - 1 - 2 * δ) (ht : 0 < t) (n : ℕ) :
    prob {ε | β * t < runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) n ε ∧
        runningMax (fun k ε => ‖paleyWalsh ξ k ε‖) n ε ≤ δ * t} ≤
      (4 * u * δ / (β - 1 - 2 * δ)) ^ p *
        prob {ε | t < runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) n ε} := by
  sorry

/-- **Extrapolation by the good-λ inequality**: a dyadic `UMD_p` constant `u` gives, for every
`r ∈ (1, ∞)` and every `β > 1`, `δ > 0` with `a = β − 1 − 2δ > 0` and
`β^r (4 u δ / a)^p < 1`, the dyadic `UMD_r` constant
`(r / (r − 1)) (β / δ) (1 − β^r (4 u δ / a)^p)^{−1/r}`. -/
theorem isDyadicUMDBound_of_goodLambda {p r u β δ : ℝ} (hp : 0 < p) (hr : 1 < r) (hu0 : 0 ≤ u)
    (hu : IsDyadicUMDBound X p (ENNReal.ofReal u)) (hβ : 1 < β) (hδ : 0 < δ)
    (ha : 0 < β - 1 - 2 * δ) (hc : β ^ r * (4 * u * δ / (β - 1 - 2 * δ)) ^ p < 1) :
    IsDyadicUMDBound X r (ENNReal.ofReal (r / (r - 1) * (β / δ) *
      (1 - β ^ r * (4 * u * δ / (β - 1 - 2 * δ)) ^ p) ^ (-(1 / r)))) := by
  sorry

/-- Extrapolation of the dyadic UMD property: finiteness for one exponent gives it for all. -/
theorem dyadicUMDConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀)
    (h : dyadicUMDConst X p₀ < ⊤) (hp : 1 < p) : dyadicUMDConst X p < ⊤ := by
  sorry

/-- `UMD_p^Δ (X) ≤ 100 p* UMD_2^Δ (X)`, by the good-λ inequality from `L²` with `β`, `δ` chosen as
functions of `p`. -/
theorem dyadicUMDConst_le_mul_dyadicUMDConst_two {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X p ≤ ENNReal.ofReal (100 * pStar p) * dyadicUMDConst X 2 := by
  sorry

/-- `UMD_2^Δ (X) ≤ 200 UMD_p^Δ (X)`, by the good-λ inequality from `L^p` to `L²`. -/
theorem dyadicUMDConst_two_le_mul {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X 2 ≤ 200 * dyadicUMDConst X p := by
  sorry

end Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Extrapolation of the UMD property** (Hytönen–van Neerven–Veraar–Weis I, Theorem 4.2.7): a
Banach space that is `UMD_{p₀}` for some `p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`. -/
theorem umdConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀) (h : umdConst X p₀ < ⊤)
    (hp : 1 < p) : umdConst X p < ⊤ := by
  sorry

/-- **Extrapolation of the UMD property, constants** (Hytönen–van Neerven–Veraar–Weis I,
Theorem 4.2.7): `UMD_p (X) ≤ 100 p* UMD₂ (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_le_mul_umdConst_two {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ ENNReal.ofReal (100 * pStar p) * umdConst X 2 := by
  sorry

/-- **Extrapolation of the UMD property, constants** (Hytönen–van Neerven–Veraar–Weis I,
Theorem 4.2.7): `UMD₂ (X) ≤ 200 UMD_p (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_two_le_mul {p : ℝ} (hp : 1 < p) : umdConst X 2 ≤ 200 * umdConst X p := by
  sorry

end BanachProbability
