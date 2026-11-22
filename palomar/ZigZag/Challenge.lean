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
# Challenge: Burkholder's characterization of UMD by zig-zag concave functions

A Banach space `X` is UMD if and only if there is a function on `X × X` that majorizes
`‖y‖^p − β^p ‖x‖^p` and is concave along the zig-zag lines, and the best `β` is the UMD constant,
after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Springer, 2016 (in the docstrings also HNVW I):
  Definitions 4.2.1 and 4.5.3, Theorem 4.5.6, which is due to D. L. Burkholder;
* [Y] I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite dimensions*,
  Indag. Math. 29 (2018), 1290–1309: Proposition 3.7 (complex scalars and the closed unit disc).

## Conventions

* `p` is a real number, `1 < p < ∞`, and `eLpNorm f (ENNReal.ofReal p) μ` is the `L^p` norm, in
  `[0, ∞]`.
* Martingales `Y_0, Y_1, …` are Mathlib's, for filtrations of probability spaces in the universe
  `Type`, and have `Y_0 = 0` (only their differences matter). [HNVW] has σ-finite filtrations of
  σ-finite measure spaces.
* `UMD_p (X) = umdConst X p` is the best `β` in `‖Σ σ_{k+1} (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p` over the
  predictable signs `σ_k ∈ {±1}`, and `UMD_{ℂ,p} (X) = complexUMDConst X p` is the same for a
  complex space and predictable unimodular complex multipliers; they are `∞` if there is no such
  `β`. [HNVW, Definition 4.2.1] has deterministic multipliers; for probability spaces the constants
  are the same ([HNVW, Theorem 4.2.25]), which is not part of this entry.
* The theorems hold for each `p` separately. ([HNVW, Theorem 4.5.6] has "for some (equivalently,
  all) `p`"; that finiteness does not depend on `p` is [HNVW, Theorem 4.2.7].)

## Statements

For real scalars, and in the second line of each item for complex ones:

* `umd_iff_signZigZag`, `complexUMD_iff_signZigZag` ([HNVW, Theorem 4.5.6, (1)⇔(3)]): the UMD
  constant is finite if and only if there are `β ≥ 1` and a function `u` such that
  `z ↦ u (x + z, y + ε z)` is concave for all `|ε| = 1` and `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`.
* `isLeast_signZigZag`, `isLeast_complexSignZigZag` ([HNVW, Theorem 4.5.6], last clause): for
  `X ≠ 0`, the least such `β ≥ 1` is the UMD constant; it is attained.
* `umd_iff_zigZag`, `complexUMD_iff_zigZag`, `isLeast_zigZag`, `isLeast_complexZigZag` (for complex
  scalars, [Y, Proposition 3.7]): the same with functions `U` that are concave along the lines for
  all `|ε| ≤ 1` and satisfy `U (0, 0) = 0`, `β > 0` in the equivalence and the least `β ≥ 0`.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/ZigZag/Solution.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

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

-- BEGIN SHARED DEFINITIONS: zigZag

/-- **HNVW I, Definition 4.5.3** (p. 331): `u : X × X → ℝ` is zig-zag concave (for the signs of
`𝕜`) if `z ↦ u (x + z, y + ε z)` is concave for all `x`, `y` and all `ε ∈ 𝕜` with `‖ε‖ = 1`. -/
def IsSignZigZagConcave (𝕜 : Type*) {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] (u : X → X → ℝ) : Prop :=
  ∀ (x y : X) (ε : 𝕜), ‖ε‖ = 1 → ConcaveOn ℝ Set.univ fun z : X => u (x + z) (y + ε • z)

/-- `U : X × X → ℝ` is zig-zag concave for the obstacle `‖y‖^p − β^p ‖x‖^p` (real scalars):
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]`, `U (0, 0) = 0`, and
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
def IsZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℝ), |ε| ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- The complex version: `ε` ranges over the closed unit disc. -/
def IsComplexZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℂ), ‖ε‖ ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

-- END SHARED DEFINITIONS: zigZag

end BanachProbability

namespace ZigZagChallenge

open BanachProbability

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ}

/-- **Burkholder's characterization of UMD** ([HNVW, Theorem 4.5.6, (1)⇔(3)], real scalars):
`UMD_p (X) < ∞` if and only if there are `β ≥ 1` and a zig-zag concave function `u : X × X → ℝ` (for
the signs `ε = ±1`) with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem umd_iff_signZigZag (hp : 1 < p) :
    umdConst X p < ∞ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y := by
  sorry

/-- **The best constant** ([HNVW, Theorem 4.5.6], last clause, real scalars): for a UMD space
`X ≠ 0`, the infimum of the `β ≥ 1` of `umd_iff_signZigZag` is `UMD_p (X)`, and it is attained. -/
theorem isLeast_signZigZag [Nontrivial X] (hp : 1 < p) (h : umdConst X p < ∞) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (umdConst X p).toReal := by
  sorry

/-- The characterization with functions that are concave along `z ↦ (x + z, y + ε z)` for all
`ε ∈ [−1, 1]` and vanish at `(0, 0)`. -/
theorem umd_iff_zigZag (hp : 1 < p) :
    umdConst X p < ∞ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U := by
  sorry

/-- The least `β ≥ 0` for which there is a function as in `umd_iff_zigZag` is `UMD_p (X)` (it is `0`
for `X = 0`). -/
theorem isLeast_zigZag (hp : 1 < p) (h : umdConst X p < ∞) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U} (umdConst X p).toReal := by
  sorry

end Real

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {p : ℝ}

/-- **Burkholder's characterization of UMD** ([HNVW, Theorem 4.5.6, (1)⇔(3)], complex scalars):
`UMD_{ℂ,p} (X) < ∞` if and only if there are `β ≥ 1` and a zig-zag concave function `u : X × X → ℝ`
(for the signs `ε ∈ ℂ`, `|ε| = 1`) with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem complexUMD_iff_signZigZag (hp : 1 < p) :
    complexUMDConst X p < ∞ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y := by
  sorry

/-- **The best constant** ([HNVW, Theorem 4.5.6], last clause, complex scalars): for a UMD space
`X ≠ 0`, the infimum of the `β ≥ 1` of `complexUMD_iff_signZigZag` is `UMD_{ℂ,p} (X)`, and it is
attained. -/
theorem isLeast_complexSignZigZag [Nontrivial X] (hp : 1 < p) (h : complexUMDConst X p < ∞) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (complexUMDConst X p).toReal := by
  sorry

/-- The characterization with functions that are concave along `z ↦ (x + z, y + ε z)` for all `ε` in
the closed unit disc and vanish at `(0, 0)` ([Y, Proposition 3.7]). -/
theorem complexUMD_iff_zigZag (hp : 1 < p) :
    complexUMDConst X p < ∞ ↔
      ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsComplexZigZagConcave p β U := by
  sorry

/-- The least `β ≥ 0` for which there is a function as in `complexUMD_iff_zigZag` is `UMD_{ℂ,p} (X)`
([Y, Proposition 3.7]; it is `0` for `X = 0`). -/
theorem isLeast_complexZigZag (hp : 1 < p) (h : complexUMDConst X p < ∞) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsComplexZigZagConcave p β U}
      (complexUMDConst X p).toReal := by
  sorry

end Complex

end ZigZagChallenge
