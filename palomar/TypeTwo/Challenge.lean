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
# Challenge: type 2, K-convexity and the Schatten classes

Type 2 of a normed space `X`, for signs and for Gaussian variables, and K-convexity, the boundedness
of the Rademacher projection; type 2 and K-convexity of the Schatten classes `S_q`, uniformly in the
size of the matrices. After

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume II:
  Probabilistic Methods and Operator Theory*, Springer, 2017 (in the docstrings also HNVW II):
  Definitions 7.1.1, 7.1.17, 7.4.1, 7.4.4, Example 7.1.2, Propositions 7.1.18 (1), 7.4.22;
* [MP] B. Maurey, G. Pisier, *Séries de variables aléatoires vectorielles indépendantes et
  propriétés géométriques des espaces de Banach*, Studia Math. 58 (1976), 45–90: Remark 2.10;
* [TJ] N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages of
  trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974), 163–182: Theorem 3.1 (ii);
* [P] G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*,
  Astérisque 247 (1998): p. 106.

## Conventions

* The sign cube `Fin N → Bool` stands for `N` independent fair signs `ε_k = coin (ε k) ∈ {±1}`;
  `avg` is the expectation, `E`, and `SignCube.lpNorm nrm p X = (E nrm (X)^p)^{1/p}`. The signs are
  real, also for complex spaces: the constants are those of the underlying real space ([HNVW], p.
  56).
* `g_1, …, g_N` are independent real standard Gaussian variables, the coordinates of Mathlib's
  `stdGaussian (EuclideanSpace ℝ (Fin N))`.
* `rademacherProj f = Σ_k ε_k E (ε_k f)` is the Rademacher projection of a function `f` on the cube.
  `IsKConvexBound X p K`: its norm on `L^p (X)` is at most `K`, for every number of signs. (The
  K-convexity constant of [HNVW, Definition 7.4.1] is the least `K` by [HNVW, Proposition 7.4.5],
  for a real space; this is not formalized.)
* `schattenNorm q A` and `complexSchattenNorm q A` are the Schatten norms `‖A‖_{S_q}` of real and
  complex matrices, `q ∈ [0, ∞]` in `ℝ≥0∞`; `ENNReal.ofReal q` is a real `q`.

## Statements

* `typeTwo_hilbert` ([HNVW, Example 7.1.2], type 2 only): a real Hilbert space has type 2 with
  constant `1`.
* `gaussianTypeTwo_of_typeTwo`, `typeTwo_of_gaussianTypeTwo` ([HNVW, Proposition 7.1.18 (1)],
  `p = 2` and real Gaussian variables): `√(2/π) τ₂ ≤ τ₂^g ≤ τ₂`.
* `kConvex_of_gaussianTypeTwo` ([HNVW, Proposition 7.4.22]), `kConvex_of_typeTwo` (the same with
  Proposition 7.1.18 (1); [MP, Remark 2.10], without constant and proof): a space of Gaussian type
  2, or of type 2, with constant `τ` is K-convex in `L²` with constant `√(π/2) τ`.
* `typeTwo_schatten_interp`, `typeTwo_schatten` ([TJ, Theorem 3.1 (ii)], for square matrices): for
  `q ≥ 2`, `(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ C (Σ ‖A_i‖_{S_q}²)^{1/2}` with
  `C = M_{2k}^{1−θ} M_{2k+2}^θ`, `2k ≤ q ≤ 2k + 2`, and with `C = √(q + 1)`; so `S_q` has type 2
  with these constants, as the norm of `L²` is at most that of `L^q`.
* `kConvex_of_piLp`, `rademacherProj_schatten`, `rademacherProj_schatten_conj` ([P], p. 106; the
  last one is implicit there): the Rademacher projection on `L^q (S_q)`, `q ≥ 2`, and on
  `L^{q'} (S_{q'})` has norm at most `√(π/2) √(q + 1)`, for real square matrices of every size.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/TypeTwo/Solution.lean`.
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

end BanachProbability

namespace TypeTwoChallenge

open BanachProbability BanachProbability.SignCube

/-- A real inner product space has type 2 with constant `1` ([HNVW, Example 7.1.2], type 2 only). -/
theorem typeTwo_hilbert (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    IsTypeTwoBound H 1 := by
  sorry

section General

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Type 2 implies Gaussian type 2**, with the same constant ([HNVW, Proposition 7.1.18 (1)],
`p = 2`, real Gaussian variables). -/
theorem gaussianTypeTwo_of_typeTwo {τ : ℝ} (h : IsTypeTwoBound X τ) :
    IsGaussianTypeTwoBound X τ := by
  sorry

/-- **Gaussian type 2 implies type 2**, with the constant `√(π/2) τ` ([HNVW, Proposition 7.1.18
(1)], `p = 2`, real Gaussian variables, `E |g| = √(2/π)`). -/
theorem typeTwo_of_gaussianTypeTwo {τ : ℝ} (h : IsGaussianTypeTwoBound X τ) (hτ : 0 ≤ τ) :
    IsTypeTwoBound X (√(Real.pi / 2) * τ) := by
  sorry

/-- **Gaussian type 2 implies K-convexity** ([HNVW, Proposition 7.4.22]):
`K^ℝ_{2,X} ≤ √(π/2) τ^g_{2,X}`. -/
theorem kConvex_of_gaussianTypeTwo {τ : ℝ} (h : IsGaussianTypeTwoBound X τ) (hτ : 0 ≤ τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) := by
  sorry

/-- **Type 2 implies K-convexity** ([HNVW, Proposition 7.4.22 with Proposition 7.1.18 (1)]; [MP,
Remark 2.10]): `K^ℝ_{2,X} ≤ √(π/2) τ_{2,X}`. -/
theorem kConvex_of_typeTwo {τ : ℝ} (h : IsTypeTwoBound X τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) := by
  sorry

/-- **Averaging** ([P], p. 106), `1 ≤ p < ∞`: if the spaces `ℓ_p ({±1}^M; X)` are K-convex in `L²`
with constant `K`, then `X` is K-convex in `L^p` with constant `K`. -/
theorem kConvex_of_piLp {p K : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (h : ∀ M : ℕ, IsKConvexBound (PiLp (ENNReal.ofReal p) fun _ : Fin M → Bool => X) 2 K) :
    IsKConvexBound X p K := by
  sorry

end General

section Schatten

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **Type 2 of `S_q`**, complex matrices, with the constant of the source ([TJ], proof of Theorem
3.1 (ii)): for `2k ≤ q ≤ 2k + 2`, `k ≥ 1`, and `θ = (2k + 2)(q − 2k)/(2q)`,
`(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ M_{2k}^{1−θ} M_{2k+2}^θ (Σ ‖A_i‖_{S_q}²)^{1/2}`. For `q = 2k` the
constant is `M_{2k}`. -/
theorem typeTwo_schatten_interp {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hkq : 2 * k ≤ q) (hqk : q ≤ 2 * k + 2)
    (A : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      evenKhintchineConst k ^ (1 - (2 * k + 2) * (q - 2 * k) / (2 * q)) *
        evenKhintchineConst (k + 1) ^ ((2 * k + 2) * (q - 2 * k) / (2 * q)) *
        √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (A i) ^ 2) := by
  sorry

/-- **Type 2 of `S_q`**, `q ≥ 2`, with the constant `√(q + 1)`, for complex and for real square
matrices of every size ([TJ, Theorem 3.1 (ii)]):
`(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(q + 1) (Σ ‖A_i‖_{S_q}²)^{1/2}`. -/
theorem typeTwo_schatten {q : ℝ} (hq : 2 ≤ q) :
    (∀ A : Fin N → Matrix n n ℂ, SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q + 1) * √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (A i) ^ 2)) ∧
    ∀ A : Fin N → Matrix n n ℝ, SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q + 1) * √(∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ 2) := by
  sorry

/-- **The Rademacher projection on `L^q (S_q)`**, `q ≥ 2` ([P], p. 106): its norm is at most
`√(π/2) √(q + 1)`, for real square matrices of every size. -/
theorem rademacherProj_schatten {q : ℝ} (hq : 2 ≤ q) (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q f := by
  sorry

/-- **The Rademacher projection on `L^{q'} (S_{q'})`**, `1/q + 1/q' = 1`, `q ≥ 2` (by duality;
implicit in [P], p. 106). -/
theorem rademacherProj_schatten_conj {q q' : ℝ} (hq : 2 ≤ q) (hqq' : q.HolderConjugate q')
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
  sorry

end Schatten

end TypeTwoChallenge
