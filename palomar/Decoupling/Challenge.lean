module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Challenge: the randomised UMD property and decoupling

For a real Banach space `X` and `1 < p < ∞`, the UMD inequality for martingale transforms by signs
compared with the inequalities for randomised martingale differences, after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Springer, 2016 (in the docstrings also HNVW I):
  Definition 4.2.1, Proposition 4.2.3, with the constants after it, p. 282.

## Conventions

* `p` is a real number, and `eLpNorm f (ENNReal.ofReal p) μ` is the `L^p` norm, in `[0, ∞]`.
* Martingales `Y_0, Y_1, …` are Mathlib's, for filtrations of probability spaces in the universe
  `Type`, and have `Y_0 = 0` (only their differences matter). [HNVW] has σ-finite filtrations of
  σ-finite measure spaces, and real or complex scalars; here the scalars, and so the signs, are
  real.
* `IsUMDBound X p β`: `‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p` for all martingales `Y` and
  all predictable signs `σ_k ∈ {±1}`; `UMD_p (X) = umdConst X p` is the least such `β`, or `∞`.
  [HNVW] has deterministic signs in Definition 4.2.1; for probability spaces their constant is the
  same ([HNVW, Theorem 4.2.25]), which is not part of this entry.
* The sign cube `Fin N → Bool`, with the uniform probability `uniformOn Set.univ`, stands for `N`
  independent fair signs `ε_k = coin (ε k)`. The randomised sum `Σ_{k<n} ε_k (Y_{k+1} − Y_k)` is a
  function on the product of `Ω` with the cube `{±1}^n` (`randomisedSum Y n`).
* A Paley–Walsh martingale is `Σ_{k<n} ε_k ξ_k` with a predictable family `ξ` (`ξ_k` depends on
  `ε_j`, `j < k`, only), `paleyWalsh ξ n`; its `L^p` norm is
  `SignCube.lpNorm (‖·‖) p (paleyWalsh ξ n)`, an average over the cube, and the one of the decoupled
  sum `Σ_{k<n} ε̃_k ξ_k (ε)`, with an independent copy `ε̃` of the signs, is the double average
  `decoupledLpNorm p ξ n`.

## Statements

* `randomisedUMD` ([HNVW, Proposition 4.2.3], `max (β⁻, β⁺) ≤ β`): a UMD constant `β` satisfies
  `β⁻¹ ‖Y_n‖_p ≤ ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`.
* `umd_of_randomised` ([HNVW, Proposition 4.2.3], `β ≤ β⁻ β⁺`): two such inequalities with constants
  `β⁻` and `β⁺` give the UMD constant `β⁻ β⁺`.
* `decoupling` (the two inequalities of [HNVW, Proposition 4.2.3] for Paley–Walsh martingales; the
  converse for them is not formalized): `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p` for a
  Paley–Walsh martingale `Y` and its decoupled sums `Ỹ`.
* `eLpNorm_uniformOn`: a check of the two norms on the sign cube.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/Decoupling/Solution.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

-- BEGIN SHARED DEFINITIONS: signs

namespace SignCube

/-- The sign `±1` of a fair coin: `coin true = 1` and `coin false = -1`. -/
def coin (b : Bool) : ℝ := if b then 1 else -1

section

variable {N : ℕ}

/-- The expectation over `N` independent fair signs:
`avg g = 2^{-N} Σ_{ε ∈ {±1}^N} g ε`. -/
noncomputable def avg (g : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ ε, g ε) / 2 ^ N

/-- The `L^p` norm `(E nrm (X ε)^p)^{1/p}` of a random variable `X` on the sign cube, the values
measured with `nrm`. -/
protected noncomputable def lpNorm {E : Type*} (nrm : E → ℝ) (p : ℝ) (X : (Fin N → Bool) → E) : ℝ :=
  avg (fun ε => nrm (X ε) ^ p) ^ (1 / p)

end

end SignCube

-- END SHARED DEFINITIONS: signs

-- BEGIN SHARED DEFINITIONS: paleyWalsh

namespace SignCube

section

variable {N : ℕ} {E : Type*}

/-- A family `ξ k` of functions of the signs is predictable: `ξ k` depends only on the signs
`ε j` with `j < k`. -/
def IsPredictable (ξ : Fin N → (Fin N → Bool) → E) : Prop :=
  ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) → ξ k ε = ξ k ε'

/-- The Paley–Walsh martingale `n ↦ Σ_{k < n} ε_k ξ_k` of a family `ξ` (predictable in the
applications), started at `0`, at time `n`. -/
noncomputable def paleyWalsh [AddCommGroup E] [Module ℝ E] (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ)
    (ε : Fin N → Bool) : E :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n), coin (ε k) • ξ k ε

end

end SignCube

-- END SHARED DEFINITIONS: paleyWalsh

-- BEGIN SHARED DEFINITIONS: umd

section

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `β` is a `UMD_p` constant of the Banach space `X`: for every probability space and filtration,
every `X`-valued martingale `Y` with `Y₀ = 0` and every sequence of predictable signs
`σ_k ∈ {±1}` (`σ_{k+1}` is `ℱ_k`-measurable),
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. The probability spaces range over
`Type`. -/
def IsUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (σ : ℕ → Ω → ℝ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, σ n ω = 1 ∨ σ n ω = -1) →
      (∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

/-- `UMD_p (X)`: the best `UMD_p` constant of `X` (`∞` if there is none). -/
noncomputable def umdConst [CompleteSpace X] (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsUMDBound X p β}

end

-- END SHARED DEFINITIONS: umd

-- BEGIN SHARED DEFINITIONS: randomisedUMD

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The randomised sum `Σ_{k<n} ε_k (Y_{k+1} − Y_k)` of the differences of a process `Y` on `Ω`, on
the product `Ω × {−1, 1}^n`. -/
noncomputable def randomisedSum {Ω : Type*} (Y : ℕ → Ω → X) (n : ℕ) (z : Ω × (Fin n → Bool)) : X :=
  ∑ k : Fin n, SignCube.coin (z.2 k) • (Y (k + 1) z.1 - Y k z.1)

variable (X) in
/-- The right-hand inequality of the randomised UMD property (HNVW I, (4.10), p. 282), with constant
`β⁺ = β`: `‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p` for all martingales `Y` started at `0`. -/
def IsUpperRandomisedUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X), Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) →
    ∀ n, eLpNorm (randomisedSum Y n) (ENNReal.ofReal p)
        (μ.prod (ProbabilityTheory.uniformOn Set.univ)) ≤
      β * eLpNorm (Y n) (ENNReal.ofReal p) μ

variable (X) in
/-- The left-hand inequality of the randomised UMD property (HNVW I, (4.10), p. 282), with constant
`β⁻ = β`: `‖Y_n‖_p ≤ β ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p` for all martingales `Y` started at `0`. -/
def IsLowerRandomisedUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X), Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) →
    ∀ n, eLpNorm (Y n) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (randomisedSum Y n) (ENNReal.ofReal p)
        (μ.prod (ProbabilityTheory.uniformOn Set.univ))

/-- The `L^p` norm `(E_ε E_{ε̃} ‖Σ_{k<n} ε̃_k ξ_k (ε)‖^p)^{1/p}` of the decoupled sum of a
predictable family `ξ`. -/
noncomputable def decoupledLpNorm {N : ℕ} (p : ℝ) (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) : ℝ :=
  SignCube.avg (fun ε => SignCube.avg fun ε' =>
    ‖SignCube.paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) ^ (1 / p)

end

-- END SHARED DEFINITIONS: randomisedUMD

end BanachProbability

namespace DecouplingChallenge

open BanachProbability BanachProbability.SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ}

/-- **The randomised UMD property** ([HNVW, Proposition 4.2.3], `β⁻ ≤ β` and `β⁺ ≤ β`): if `β` is a
`UMD_p` constant of `X`, then `‖Y_n‖_p ≤ β ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p` and
`‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p` for all martingales `Y`, with independent fair signs
`ε_k` on a further probability space. -/
theorem randomisedUMD (hp : 1 < p) {β : ℝ≥0∞} (h : IsUMDBound X p β) :
    IsLowerRandomisedUMDBound X p β ∧ IsUpperRandomisedUMDBound X p β := by
  sorry

/-- **The randomised UMD property**, the converse ([HNVW, Proposition 4.2.3], `β ≤ β⁻ β⁺`): the two
inequalities with constants `β⁻` and `β⁺` give the `UMD_p` constant `β⁻ β⁺`. -/
theorem umd_of_randomised (hp : 1 < p) {β₁ β₂ : ℝ≥0∞} (hl : IsLowerRandomisedUMDBound X p β₁)
    (hu : IsUpperRandomisedUMDBound X p β₂) : IsUMDBound X p (β₁ * β₂) := by
  sorry

/-- **Decoupling** of Paley–Walsh martingales (the two inequalities of [HNVW, Proposition 4.2.3] for
Paley–Walsh martingales, with the constant `UMD_p (X)`): for `Y_n = Σ_{k<n} ε_k ξ_k`, `ξ`
predictable, and `Ỹ_n = Σ_{k<n} ε̃_k ξ_k`, with an independent copy `ε̃` of the signs `ε`,
`‖Ỹ_n‖_p ≤ UMD_p (X) ‖Y_n‖_p` and `‖Y_n‖_p ≤ UMD_p (X) ‖Ỹ_n‖_p`. -/
theorem decoupling (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ)
    (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  sorry

omit [CompleteSpace X] in
/-- **What the two norms of `decoupling` are**: the `L^p` norms on the sign cube, and on the product
of two sign cubes, with the uniform probabilities. -/
theorem eLpNorm_uniformOn (hp : 0 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) :
    eLpNorm (paleyWalsh ξ n) (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
        ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      eLpNorm (fun z : (Fin N → Bool) × (Fin N → Bool) => paleyWalsh (fun k _ => ξ k z.1) n z.2)
          (ENNReal.ofReal p) ((ProbabilityTheory.uniformOn Set.univ).prod
            (ProbabilityTheory.uniformOn Set.univ)) =
        ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  sorry

end DecouplingChallenge
