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
# Challenge: UMD constants

The UMD property (unconditional martingale differences) of a Banach space `X` and its constants
`UMD_p (X) ∈ [0, ∞]`, `1 < p < ∞`, after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Springer, 2016 (in the docstrings also HNVW I):
  Definition 4.2.1, Propositions 4.2.10 and 4.2.15, Theorems 4.2.5, 4.2.7, 4.2.25, 4.5.7, Corollary
  4.5.15;
* [O] A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Birkhäuser, 2012: Theorem
  3.5, Remark 3.8, Section 3.11.2.

## Conventions

* `p`, `q` are real numbers, `p' = p / (p − 1)`, `p* = max (p, p')`, and
  `eLpNorm f (ENNReal.ofReal p) μ` is the `L^p` norm, in `[0, ∞]`.
* Martingales `Y_0, Y_1, …` are Mathlib's, for filtrations of probability spaces in the universe
  `Type`, and have `Y_0 = 0` (only their differences matter). [HNVW] has σ-finite filtrations of
  σ-finite measure spaces, so its constants are over more martingales.
* `UMD_p (X) = umdConst X p` is the best `β` in `‖Σ σ_{k+1} (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p` over the
  *predictable* signs `σ_k ∈ {±1}`, for a real Banach space, and
  `UMD_{ℂ,p} (X) = complexUMDConst X p` is the same for a complex one and predictable unimodular
  complex multipliers; they are `∞` if there is no such `β`, and `0` for `X = 0`. [HNVW, Definition
  4.2.1] has *deterministic* multipliers, `±1` for real and unimodular ones for complex scalars
  (`IsDeterministicUMDBound`); by `isUMDBound_iff_deterministic` and
  `isComplexUMDBound_iff_deterministic` this is the same.
* The sign cube `Fin N → Bool` stands for `N` independent fair signs `ε_k = coin (ε k)`; `avg` is
  the expectation and `SignCube.lpNorm` the `L^p` norm for the uniform probability. A Paley–Walsh
  martingale is `Σ_{k<n} ε_k ξ_k` with a predictable family `ξ` (`paleyWalsh ξ n`). The dyadic UMD
  property is the UMD inequality for these, with deterministic multipliers
  (`IsDeterministicDyadicUMDBound`).

## Statements

* `isUMDBound_iff_deterministic`, `isComplexUMDBound_iff_deterministic`,
  `deterministic_transform_le` ([HNVW, Theorem 4.2.25]): deterministic and predictable multipliers
  have the same UMD constants, which also bound the transforms by predictable multipliers of modulus
  at most `1`.
* `isUMDBound_iff_dyadic`, `isComplexUMDBound_iff_dyadic` ([HNVW, Theorem 4.2.5]): the dyadic
  constants are the same.
* `umdConst_extrapolation`, `umdConst_two_comparison` ([HNVW, Theorem 4.2.7], real scalars):
  `UMD_p ≤ 100 (p/q + p'/q') UMD_q`, and `(1/200) UMD₂ ≤ UMD_p ≤ 50 (p + p') UMD₂`.
* `umdConst_le_complexUMDConst_le` ([HNVW, Proposition 4.2.10]):
  `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π/2) UMD_p (X)`.
* `umdConst_Lp`, `complexUMDConst_Lp` ([HNVW, Proposition 4.2.15 (2)]):
  `UMD_p (L^p (μ; X)) ≤ UMD_p (X)`, with equality if there is a set of finite positive measure, over
  `ℝ` and `ℂ`.
* `umdConst_hilbert` ([O, Theorem 3.5, Remark 3.8, Section 3.11.2]; [HNVW, Corollary 4.5.15], and
  Theorem 4.5.7 for `ℝ`; real scalars): `UMD_p (H) = p* − 1` for a real Hilbert space `H ≠ 0`, also
  for dyadic martingales.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/UMD/Solution.lean`.
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

-- BEGIN SHARED DEFINITIONS: complexUMD

section

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `β` is a complex `UMD_p` constant of the complex Banach space `X`: for every `X`-valued
martingale `Y` with `Y₀ = 0` and every predictable sequence of unimodular `c_k ∈ ℂ`,
`‖Σ_{k<n} c_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. -/
def IsComplexUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (c : ℕ → Ω → ℂ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, ‖c n ω‖ = 1) →
      (∀ k, StronglyMeasurable[ℱ k] (c (k + 1))) →
      ∀ n, eLpNorm (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Y (k + 1) ω - Y k ω))
          (ENNReal.ofReal p) μ ≤ β * eLpNorm (Y n) (ENNReal.ofReal p) μ

/-- `UMD_{ℂ,p} (X)`: the best complex `UMD_p` constant (`∞` if there is none). -/
noncomputable def complexUMDConst [CompleteSpace X] (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexUMDBound X p β}

end

-- END SHARED DEFINITIONS: complexUMD

-- BEGIN SHARED DEFINITIONS: dyadicUMD

/-- `β` is a UMD constant of `X` for *deterministic* multipliers (HNVW I, Definition 4.2.1,
p. 281): for every `X`-valued martingale `Y` with `Y_0 = 0` on a probability space and all scalars
`ε_k ∈ 𝕜` with `|ε_k| = 1`, `‖Σ_{k<n} ε_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. In the book
the martingales are on σ-finite measure spaces, and do not have to start at `0`; but only their
increments enter the inequality, so this is the inequality for `f_n − f_0`. -/
def IsDeterministicUMDBound (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedSpace 𝕜 X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (ε : ℕ → 𝕜),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n, ‖ε n‖ = 1) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, ε (k + 1) • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

/-- `β` is a dyadic UMD constant of `X` (HNVW I, Definition 4.2.1, for Paley–Walsh martingales): for
every number of signs `N`, every predictable family `ξ` with values in `X` and all scalars `l_k ∈ 𝕜`
with `|l_k| = 1`, `‖Σ_{k<n} l_k ε_k ξ_k‖_{L^p} ≤ β ‖Σ_{k<n} ε_k ξ_k‖_{L^p}`. -/
def IsDeterministicDyadicUMDBound (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedSpace 𝕜 X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (l : Fin N → 𝕜),
    SignCube.IsPredictable ξ → (∀ k, ‖l k‖ = 1) → ∀ n : ℕ,
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
          (SignCube.paleyWalsh (fun k ε => l k • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (SignCube.paleyWalsh ξ n))

-- END SHARED DEFINITIONS: dyadicUMD

end BanachProbability

namespace UMDChallenge

open BanachProbability BanachProbability.SignCube

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Deterministic and predictable signs** ([HNVW, Theorem 4.2.25], real scalars): they have the
same UMD constants. -/
theorem isUMDBound_iff_deterministic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsUMDBound X p β ↔ IsDeterministicUMDBound ℝ X p β := by
  sorry

/-- **Dyadic UMD equals UMD** ([HNVW, Theorem 4.2.5], real scalars): the constants for Paley–Walsh
martingales and deterministic signs are the UMD constants, so that the least ones agree,
`UMD_p^Δ (X) = UMD_p (X)`. -/
theorem isUMDBound_iff_dyadic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsUMDBound X p β ↔ IsDeterministicDyadicUMDBound ℝ X p β := by
  sorry

/-- **Extrapolation** ([HNVW, Theorem 4.2.7], real scalars):
`UMD_p (X) ≤ 100 (p/q + p'/q') UMD_q (X)` for all `p, q ∈ (1, ∞)`; in particular, a space that is
UMD for one exponent is so for all. -/
theorem umdConst_extrapolation [CompleteSpace X] {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdConst X p ≤
      ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1)))) * umdConst X q := by
  sorry

/-- The exponent `2` ([HNVW, after Theorem 4.2.7], real scalars): `UMD₂ (X) ≤ 200 UMD_p (X)` and
`UMD_p (X) ≤ 50 (p + p') UMD₂ (X)`. -/
theorem umdConst_two_comparison [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    umdConst X 2 ≤ 200 * umdConst X p ∧
      umdConst X p ≤ ENNReal.ofReal (50 * (p + p / (p - 1))) * umdConst X 2 := by
  sorry

/-- **Fubini** ([HNVW, Proposition 4.2.15 (2)], real scalars): `UMD_p (L^p (μ; X)) ≤ UMD_p (X)` for
every measure `μ`, with equality if there is a set of finite positive measure. (For `L^p (μ) = 0`,
which the source does not exclude, the left side is the constant `0` of the space `0`.) -/
theorem umdConst_Lp {S : Type*} {mS : MeasurableSpace S} (μ : Measure S) [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ∞) :
    umdConst (Lp X p μ) p.toReal ≤ umdConst X p.toReal ∧
      ((∃ A, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞) →
        umdConst (Lp X p μ) p.toReal = umdConst X p.toReal) := by
  sorry

end Real

/-- **Hilbert spaces** ([O, Theorem 3.5, Remark 3.8, Section 3.11.2]; [HNVW, Corollary 4.5.15], and
Theorem 4.5.7 for `H = ℝ`; real scalars): `UMD_p (H) = p* − 1` for every real Hilbert space `H ≠ 0`
and `1 < p < ∞`, and this is also the least constant for dyadic martingales and deterministic
signs. -/
theorem umdConst_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Nontrivial H] {p : ℝ} (hp : 1 < p) :
    umdConst H p = ENNReal.ofReal (max p (p / (p - 1)) - 1) ∧
      sInf {β | IsDeterministicDyadicUMDBound ℝ H p β} =
        ENNReal.ofReal (max p (p / (p - 1)) - 1) := by
  sorry

/-- **Transforms by predictable multipliers** ([HNVW, Theorem 4.2.25], for real or complex scalars
`𝕜`): a UMD constant `β` for deterministic multipliers also bounds the transforms by predictable
multipliers `φ_k`, `‖φ_k‖ ≤ 1` everywhere: `‖Σ_{k<n} φ_{k+1} (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`. -/
theorem deterministic_transform_le {𝕜 : Type} {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] {p : ℝ}
    (hp : 1 < p) {β : ℝ≥0∞} (h : IsDeterministicUMDBound 𝕜 X p β) {Ω : Type}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0) {φ : ℕ → Ω → 𝕜}
    (hφ1 : ∀ n ω, ‖φ n ω‖ ≤ 1) (hφ : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
        (ENNReal.ofReal p) μ ≤ β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  sorry

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Deterministic and predictable multipliers** ([HNVW, Theorem 4.2.25], complex scalars): they
have the same UMD constants. -/
theorem isComplexUMDBound_iff_deterministic {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsComplexUMDBound X p β ↔ IsDeterministicUMDBound ℂ X p β := by
  sorry

/-- **Dyadic UMD equals UMD** ([HNVW, Theorem 4.2.5], complex scalars): the constants for
Paley–Walsh martingales and deterministic unimodular multipliers are the UMD constants. -/
theorem isComplexUMDBound_iff_dyadic {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsComplexUMDBound X p β ↔ IsDeterministicDyadicUMDBound ℂ X p β := by
  sorry

/-- **Real and complex constants** ([HNVW, Proposition 4.2.10]): for a complex Banach space `X`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π/2) UMD_p (X)`, where `UMD_p (X)` is that of the underlying real
space. -/
theorem umdConst_le_complexUMDConst_le {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p := by
  sorry

/-- **Fubini** ([HNVW, Proposition 4.2.15 (2)], complex scalars), as `umdConst_Lp`. -/
theorem complexUMDConst_Lp {S : Type*} {mS : MeasurableSpace S} (μ : Measure S) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ∞) :
    complexUMDConst (Lp X p μ) p.toReal ≤ complexUMDConst X p.toReal ∧
      ((∃ A, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞) →
        complexUMDConst (Lp X p μ) p.toReal = complexUMDConst X p.toReal) := by
  sorry

end Complex

end UMDChallenge
