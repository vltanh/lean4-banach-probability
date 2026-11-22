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
# The definitions of the main statements

The definitions that the statements of `palomar/` use, in marked blocks that
`scripts/sync_challenge_defs.py` copies word for word into the Challenges. A Challenge declares them
again and imports only Mathlib, so this module imports only Mathlib, the same modules as every
Challenge, and the blocks of a Challenge follow one another here as they do there. Their theory is
in the modules named with each block.

* `signs`: the sign cube `{−1, 1}^N`, averages and `L^p` norms on it (`SignCube/`);
* `paleyWalsh`: predictable families and Paley–Walsh martingales (`SignCube/PaleyWalsh.lean`);
* `burkholder`: Burkholder's function (`Martingale/Burkholder/Function.lean`);
* `umd`: the UMD constants, over real and complex scalars (`UMD/Defs.lean`);
* `umdForms`: the dyadic, deterministic and randomised forms of the UMD property (`UMD/`);
* `zigZag`: zig-zag concave functions (`ZigZag/`);
* `hypercontractivity`: the discrete heat semigroup (`Hypercontractivity/`);
* `schatten`: Schatten norms of real and complex matrices (`Schatten/`);
* `typeTwo`: type 2, Gaussian type 2, the Rademacher projection, K-convexity (`TypeTwo/`,
  `KConvexity/`);
* `noncommutative`: martingale transforms on `L^∞ (Ω) ⊗ M_n` (`Noncommutative/`).
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

-- BEGIN SHARED DEFINITIONS: burkholder

/-- **Burkholder's function** (Burkholder 1988, (1.6)):
`u_p (x, y) = α_p (|y| − (p* − 1) |x|) (|x| + |y|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`,
`p* = max (p, p / (p − 1))`; `x` is the position of the dominating martingale and `y` that of the
subordinate one. -/
noncomputable def Burkholder.burkholderFun {H : Type*} [NormedAddCommGroup H] (p : ℝ) (x y : H) :
    ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (‖y‖ - (max p (p / (p - 1)) - 1) * ‖x‖) *
    (‖x‖ + ‖y‖) ^ (p - 1)

-- END SHARED DEFINITIONS: burkholder

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

-- END SHARED DEFINITIONS: umd

-- BEGIN SHARED DEFINITIONS: umdForms

/-! The same constants for Paley–Walsh martingales on the sign cubes. -/

section

open SignCube

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `β` bounds the `±1`-transforms of Paley–Walsh martingales with values in `X`:
`‖Σ_{k<n} σ_k ε_k ξ_k‖_{L^p} ≤ β ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` for predictable `ξ_k` and predictable
signs `σ_k`. -/
def IsDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ n : ℕ,
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic `UMD_p` constant `UMD_p^Δ (X)`. -/
noncomputable def dyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsDyadicUMDBound X p β}

end

section

open SignCube

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The dyadic complex `UMD_p` bound: predictable unimodular complex multipliers of Paley–Walsh
martingales. -/
def IsComplexDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (c : Fin N → (Fin N → Bool) → ℂ),
    IsPredictable ξ → IsPredictable c → (∀ k ε, ‖c k ε‖ = 1) → ∀ n : ℕ,
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => c k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic complex `UMD_p` constant `UMD_{ℂ,p}^Δ (X)`. -/
noncomputable def complexDyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexDyadicUMDBound X p β}

end

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

-- END SHARED DEFINITIONS: umdForms

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

-- BEGIN SHARED DEFINITIONS: hypercontractivity

section

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Borell's operator** on functions of one sign, with the kernel `K (x, y) = 1 + ρ x y`:
`K̄ g (x) = E_y [K (x, y) g (y)] = ((1 + ρ x) g (1) + (1 − ρ x) g (−1)) / 2`. -/
noncomputable def kBar (ρ : ℝ) (g : Bool → E) (x : Bool) : E :=
  (1 / 2 : ℝ) • ((1 + ρ * coin x) • g true + (1 - ρ * coin x) • g false)

/-- **The tensor power `⊗ⁿ K̄`**, the operator with the kernel `Π_i (1 + ρ x_i y_i)` on functions
of `n` signs: `(⊗ⁿ⁺¹ K̄) f (x₀, x) = K̄ [y₀ ↦ (⊗ⁿ K̄) (f (y₀, ·)) (x)] (x₀)`. -/
noncomputable def kBarTensor (ρ : ℝ) : (n : ℕ) → ((Fin n → Bool) → E) → (Fin n → Bool) → E
  | 0, f => f
  | n + 1, f => fun ε =>
      kBar ρ (fun η => kBarTensor ρ n (fun ε' => f (Fin.cons η ε')) (Fin.tail ε)) (ε 0)

/-- **The discrete heat semigroup** `T (t) = Π_i T_i (t)` on functions of `n` signs (HNVW II, (6.7),
p. 19), where `T_i (t) (x + ε_i y) = x + e^{−t} ε_i y`; see `heatSemigroup_walsh` for the form
(6.6). -/
noncomputable def heatSemigroup (t : ℝ) {n : ℕ} (f : (Fin n → Bool) → E) : (Fin n → Bool) → E :=
  kBarTensor (Real.exp (-t)) n f

end

-- END SHARED DEFINITIONS: hypercontractivity

-- BEGIN SHARED DEFINITIONS: schatten

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The singular values of `A ∈ ℝ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᵀ A)`. -/
noncomputable def singularValue (A : Matrix m n ℝ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`, `‖A‖_{S_∞} = max_i s_i`. -/
noncomputable def schattenNorm (q : ℝ≥0∞) (A : Matrix m n ℝ) : ℝ :=
  if q = ⊤ then ⨆ i, singularValue A i else (∑ i, singularValue A i ^ q.toReal) ^ (1 / q.toReal)

/-- The singular values of `A ∈ ℂ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᴴ A)`. -/
noncomputable def complexSingularValue (A : Matrix m n ℂ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm of a complex matrix: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`,
`‖A‖_{S_∞} = max_i s_i`. -/
noncomputable def complexSchattenNorm (q : ℝ≥0∞) (A : Matrix m n ℂ) : ℝ :=
  if q = ⊤ then ⨆ i, complexSingularValue A i
  else (∑ i, complexSingularValue A i ^ q.toReal) ^ (1 / q.toReal)

end

-- END SHARED DEFINITIONS: schatten

-- BEGIN SHARED DEFINITIONS: typeTwo

/-- `X` has type 2 with constant `τ`, for real signs:
`(E ‖Σ ε_k x_k‖²)^{1/2} ≤ τ (Σ ‖x_k‖²)^{1/2}`. -/
def IsTypeTwoBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (τ : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → X),
    SignCube.lpNorm (fun y => ‖y‖) 2
        (fun ε : Fin N → Bool => ∑ k, SignCube.coin (ε k) • x k) ≤
      τ * √(∑ k, ‖x k‖ ^ 2)

/-- `X` has Gaussian type 2 with constant `τ`: `E ‖Σ g_k x_k‖² ≤ τ² Σ ‖x_k‖²` for independent real
standard Gaussian variables `g_k` (HNVW II, Definition 7.1.17 (1), p. 67, with `p = 2` and `ξ = g`;
the least `τ ≥ 0` is `τ^g_{2,X}`). -/
def IsGaussianTypeTwoBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (τ : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → X),
    ∫ g, ‖∑ k, g k • x k‖ ^ 2 ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)) ≤
      τ ^ 2 * ∑ k, ‖x k‖ ^ 2

/-- The constant `M_{2k} = ((2k)! / (2^k k!))^{1/2k}` (Tomczak-Jaegermann (1974), p. 177). -/
noncomputable def evenKhintchineConst (k : ℕ) : ℝ :=
  (((2 * k).factorial : ℝ) / (2 ^ k * k.factorial)) ^ (1 / (2 * k : ℝ))

section

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The expectation `E (ε_k f)` of a function on the sign cube with values in a vector space. -/
noncomputable def rademacherCoeff (f : (Fin N → Bool) → V) (k : Fin N) : V :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ η, SignCube.coin (η k) • f η

/-- The Rademacher projection `Σ_k ε_k E (ε_k f)`. -/
noncomputable def rademacherProj (f : (Fin N → Bool) → V) (ε : Fin N → Bool) : V :=
  ∑ k, SignCube.coin (ε k) • rademacherCoeff f k

end

/-- `X` is K-convex in `L^p` with constant `K`: `‖Σ_k ε_k E (ε_k f)‖_{L^p} ≤ K ‖f‖_{L^p}`, for real
signs `ε_k` (for `1 < p < ∞` the least `K ≥ 0` is `K^ℝ_{p,X}` of HNVW II, p. 124, line 1). -/
def IsKConvexBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p K : ℝ) : Prop :=
  ∀ (N : ℕ) (f : (Fin N → Bool) → X),
    SignCube.lpNorm (fun y => ‖y‖) p (rademacherProj f) ≤ K * SignCube.lpNorm (fun y => ‖y‖) p f

-- END SHARED DEFINITIONS: typeTwo

-- BEGIN SHARED DEFINITIONS: noncommutative

/-- The number of singular values of `A` larger than `s`, `#{i : s_i (A) > s}`; for a symmetric
matrix, the number of eigenvalues with `|λ_i| > s`, the trace of `1_{(s, ∞)} (|A|)`. -/
noncomputable def countAbove {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (s : ℝ)
    (A : Matrix m n ℝ) : ℕ :=
  (Finset.univ.filter fun i => s < singularValue A i).card

section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : Type*}

/-- The distribution function `λ_s (x) = ∫ #{i : s_i (x ω) > s} dμ (ω)`. -/
noncomputable def ncDistribution [Fintype n] [DecidableEq n] (μ : Measure Ω) (s : ℝ)
    (x : Ω → Matrix n n ℝ) : ℝ :=
  ∫ ω, (countAbove s (x ω) : ℝ) ∂μ

/-- Every entry of the matrix-valued function `x` is in `L^p (μ)`. -/
def MatrixMemLp (x : Ω → Matrix n n ℝ) (p : ℝ≥0∞) (μ : Measure Ω) : Prop :=
  ∀ i j, MemLp (fun ω => x ω i j) p μ

/-- The conditional expectation `E_m = 𝔼 [· | m] ⊗ Id`, applied entrywise. -/
noncomputable def matrixCondExp (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω => Matrix.of fun i j => (μ[fun ω' => x ω' i j | m]) ω

/-- The trace `τ (x) = ∫ tr x dμ` of `L^∞ (Ω, μ) ⊗ M_n`. -/
noncomputable def matrixTrace [Fintype n] {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (x : Ω → Matrix n n ℝ) : ℝ :=
  ∫ ω, (x ω).trace ∂μ

/-- The martingale transform `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)`. -/
noncomputable def ncTransform (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) (c : ℕ → Ω → ℝ) (N : ℕ)
    (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω => matrixCondExp (ℱ 0) μ x ω +
    ∑ k ∈ Finset.range N, c k ω • (matrixCondExp (ℱ (k + 1)) μ x ω - matrixCondExp (ℱ k) μ x ω)

end

/-- The UMD inequality in `L^p` with constant `β` for real or complex `n × n` matrices with the norm
`nrm`: for every probability space and filtration, every matrix-valued martingale `Y` (each entry
is a martingale) with `Y₀ = 0` and all predictable signs `σ_k ∈ {±1}` (`σ_{k+1}` is
`ℱ_k`-measurable), `‖Σ_{k<N} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_N‖_{L^p}`. -/
def IsMatrixUMDBound {𝕜 n : Type*} [RCLike 𝕜] (nrm : Matrix n n 𝕜 → ℝ) (p : ℝ) (β : ℝ≥0∞) :
    Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → Matrix n n 𝕜) (σ : ℕ → Ω → ℝ),
    (∀ i j, Martingale (fun k ω => Y k ω i j) ℱ μ) → (∀ ω, Y 0 ω = 0) →
      (∀ k ω, σ k ω = 1 ∨ σ k ω = -1) → (∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) →
      ∀ N, eLpNorm (fun ω => nrm (∑ k ∈ Finset.range N, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)))
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => nrm (Y N ω)) (ENNReal.ofReal p) μ

-- END SHARED DEFINITIONS: noncommutative

end BanachProbability
