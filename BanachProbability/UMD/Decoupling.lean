module

public import BanachProbability.UMD.Defs

/-!
# Decoupling of Paley–Walsh martingales in UMD spaces

For a Paley–Walsh martingale `Y_n = Σ_{k<n} ε_k ξ_k (ε)` with predictable `ξ` and an independent
copy `ε̃` of the signs, the decoupled sum `Ỹ_n = Σ_{k<n} ε̃_k ξ_k (ε)` satisfies
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`
(Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016), Proposition 4.2.3;
Cox–Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*, Electron.
Commun. Probab. 12 (2007), with the constant `β_{p,X}`; McConnell (1989) for tangent sequences).

The proof is the standard one from the definition. With `η_k = ε_k ε̃_k`, the map
`(ε, ε̃) ↦ (ε, η)` preserves the uniform measure (`SignCube.avg_mul_left`) and
`Σ ε̃_k ξ_k (ε) = Σ η_k ε_k ξ_k (ε)`. In the interleaved order `η₀, ε₀, η₁, ε₁, …` of the doubled
cube (`SignCube.interleave`), `A = Σ ε_k ξ_k (ε)` and `B = Σ ε_k (η_k ξ_k (ε))` are Paley–Walsh
martingales with increments at the `ε_k` steps only, and `η_k` is a predictable sign for the
`ε_k` step: `B` is the transform of `A` by the signs `η`, and `A` that of `B`. Both inequalities
follow, with the dyadic constant `UMD_p^Δ (X)`, hence with `UMD_p (X)`.

Since the dyadic constant is that of the space in which the `ξ_k` take values, the statement for a
subspace `V` (with the constant `UMD_p^Δ (V)`) is the statement for the normed space `V`.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `L^p` norm `(E_ε E_{ε̃} ‖Σ_{k<n} ε̃_k ξ_k (ε)‖^p)^{1/p}` of the decoupled sum of a
predictable family `ξ`. -/
noncomputable def decoupledLpNorm {N : ℕ} (p : ℝ) (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) : ℝ :=
  avg (fun ε => avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) ^ (1 / p)

/-- **Decoupling** of Paley–Walsh martingales with the dyadic UMD constant:
`‖Ỹ_n‖_{L^p} ≤ UMD_p^Δ ‖Y_n‖_{L^p}` and `‖Y_n‖_{L^p} ≤ UMD_p^Δ ‖Ỹ_n‖_{L^p}`. -/
theorem decoupling_dyadic {p : ℝ} (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X)
    (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        dyadicUMDConst X p * ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        dyadicUMDConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  sorry

/-- **Decoupling** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.3; Cox–Veraar 2007) for
Paley–Walsh martingales in a Banach space, with the constant `UMD_p (X)`:
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`. -/
theorem decoupling [CompleteSpace X] {p : ℝ} (hp : 1 < p) {N : ℕ}
    (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  sorry

end BanachProbability
