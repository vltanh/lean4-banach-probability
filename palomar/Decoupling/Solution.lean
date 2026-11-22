module

public import BanachProbability.UMD.Decoupling

/-!
# Solution: the randomised UMD property and decoupling

The statements of `palomar/Decoupling/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DecouplingChallenge

open BanachProbability BanachProbability.SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ}

theorem randomisedUMD (hp : 1 < p) {β : ℝ≥0∞} (h : IsUMDBound X p β) :
    IsLowerRandomisedUMDBound X p β ∧ IsUpperRandomisedUMDBound X p β :=
  ⟨h.isLowerRandomisedUMDBound (by linarith), h.isUpperRandomisedUMDBound (by linarith)⟩

theorem umd_of_randomised (hp : 1 < p) {β₁ β₂ : ℝ≥0∞} (hl : IsLowerRandomisedUMDBound X p β₁)
    (hu : IsUpperRandomisedUMDBound X p β₂) : IsUMDBound X p (β₁ * β₂) :=
  isUMDBound_of_randomised (by linarith) hl hu

theorem decoupling (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ)
    (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) :=
  BanachProbability.decoupling hp ξ hξ n

omit [CompleteSpace X] in
theorem eLpNorm_uniformOn (hp : 0 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) :
    eLpNorm (paleyWalsh ξ n) (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
        ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      eLpNorm (fun z : (Fin N → Bool) × (Fin N → Bool) => paleyWalsh (fun k _ => ξ k z.1) n z.2)
          (ENNReal.ofReal p) ((ProbabilityTheory.uniformOn Set.univ).prod
            (ProbabilityTheory.uniformOn Set.univ)) =
        ENNReal.ofReal (decoupledLpNorm p ξ n) :=
  ⟨SignCube.eLpNorm_uniformOn _ hp, eLpNorm_prod_uniformOn hp ξ n⟩

end DecouplingChallenge
