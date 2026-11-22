module

public import BanachProbability.UMD.Maurey.FinitePaths

/-!
# Finite models with dyadic transitions are Paley–Walsh martingales

The realization step of Maurey's theorem (Pisier, *Martingales in Banach spaces* (2016), §5.6;
HNVW I, Theorem 4.2.5): a finite model whose transition probabilities are dyadic rationals with
denominator `2^m` (`HasDyadicTransitions`) is the image of a Paley–Walsh martingale on a sign cube
under a measure-preserving map. Each step `k → k + 1` of the filtration is split into a block of
`m` coin flips, whose `2^m` outcomes are partitioned into groups of sizes `j` (the numerators of
the transition probabilities); the intermediate values are the conditional expectations within
the block, so the process on the cube is a Paley–Walsh martingale whose values at the ends of the
blocks are those of `Y`, and the signs `σ_{k+1}`, constant on each block, are predictable. The
`L^p` norms of the martingale and of its transform are therefore those of the finite model
(`exists_paleyWalsh_realization`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Blocked realization**: a finite model with dyadic transition probabilities up to time `n` is
realized by a Paley–Walsh martingale with predictable signs on a sign cube, with the same `L^p`
norms of the martingale at time `n` and of its transform. -/
theorem exists_paleyWalsh_realization {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} {σ : ℕ → Ω → ℝ} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    (hσ : ∀ n ω, σ n ω = 1 ∨ σ n ω = -1) (hσm : ∀ k, StronglyMeasurable[ℱ k] (σ (k + 1)))
    {n : ℕ} (hdy : HasDyadicTransitions μ ℱ n) {p : ℝ} (hp : 0 < p) :
    ∃ (M : ℕ) (ξ : Fin M → (Fin M → Bool) → X) (s : Fin M → (Fin M → Bool) → ℝ),
      IsPredictable ξ ∧ IsPredictable s ∧ (∀ k ε, s k ε = 1 ∨ s k ε = -1) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ M)) =
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => s k ε • ξ k ε) M)) =
        eLpNorm (fun ω => ‖martingaleTransform σ Y n ω‖) (ENNReal.ofReal p) μ := by
  sorry

end BanachProbability
