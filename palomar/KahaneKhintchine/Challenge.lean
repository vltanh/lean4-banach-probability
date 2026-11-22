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
# Challenge: hypercontractivity on the cube and the Kahane–Khintchine inequality

Hypercontractivity of the discrete heat semigroup on functions of independent fair signs with values
in a seminormed space, the Kahane–Khintchine inequality, and Kahane's contraction principle, after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume II:
  Probabilistic Methods and Operator Theory*, Springer, 2017 (in the docstrings also HNVW II):
  6.2.a, Lemma 6.2.3, Theorems 6.2.2 and 6.2.4;
* [HNVW I] *Volume I: Martingales and Littlewood–Paley Theory*, 2016: Proposition 3.2.10;
* [B] C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire de
  Probabilités XIII, Lecture Notes in Math. 721 (1979), 1–3: (2.1).

## Conventions

* The sign cube `Fin n → Bool` stands for `n` independent fair signs `ε_i = coin (ε i) ∈ {±1}` (a
  real Rademacher sequence); `SignCube.lpNorm nrm p X = (E nrm (X)^p)^{1/p}` with the average over
  the cube, for real `p > 0`; `lpNorm_eq_eLpNorm` says that this is the `L^p` norm for the uniform
  probability.
* In the first part the values are in a real vector space `E` with a seminorm `S`; [HNVW] has a
  Banach space, which is the case of its norm. No completeness is needed.
* `heatSemigroup t f` is the discrete heat semigroup `T (t) f`; `heatSemigroup_walsh` is its
  definition in [HNVW, (6.6)], `T (t) (Σ_α w_α x_α) = Σ_α e^{−t #α} w_α x_α` with the Walsh
  functions `w_α = Π_{i ∈ α} ε_i`, whose combinations are all functions on the cube. It is built
  from the operators `K̄` (`kBar`) and their tensor powers `⊗ⁿ K̄` (`kBarTensor`) of [B].

## Statements

* `heatSemigroup_walsh` ([HNVW, (6.6)]).
* `heatSemigroup_hypercontractive` ([HNVW, Theorem 6.2.2], the "if" part): for `1 < p ≤ q` and
  `e^{−t} ≤ √((p − 1)/(q − 1))`, `‖T (t) f‖_q ≤ ‖f‖_p`; `bonami` ([HNVW, Lemma 6.2.3], the "if"
  part): the same for one sign.
* `hypercontractive_affine` ([B, (2.1)] for polynomials of degree at most `1`):
  `‖c + ρ Σ ε_i x_i‖_q ≤ ‖c + Σ ε_i x_i‖_p`, `ρ = √((p − 1)/(q − 1))`.
* `kahaneKhintchine` ([HNVW, Theorem 6.2.4], real signs):
  `‖Σ ε_i x_i‖_q ≤ √((q − 1)/(p − 1)) ‖Σ ε_i x_i‖_p` for `1 < p ≤ q`; `exists_kahaneKhintchine`: for
  all `p, q ∈ (0, ∞)`, with some constant that depends only on `p` and `q`.
* `contraction_real`, `contraction_complex` ([HNVW I, Proposition 3.2.10], real signs, `p < ∞`):
  `‖Σ c_k ε_k x_k‖_p ≤ C max_k |c_k| ‖Σ ε_k x_k‖_p` with `C = 1` for real and `C = π/2` for complex
  coefficients `c_k`.

Not formalized: the "only if" parts of [HNVW, Lemma 6.2.3 and Theorem 6.2.2], complex Rademacher
variables, and the optimality of `π/2`.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/KahaneKhintchine/Solution.lean`.
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

end BanachProbability

namespace KahaneKhintchineChallenge

open BanachProbability BanachProbability.SignCube

/-- **What `SignCube.lpNorm` is**: the `L^p` norm for the uniform probability on the cube, `p > 0`.
-/
theorem lpNorm_eq_eLpNorm {X : Type*} [NormedAddCommGroup X] {n : ℕ} (f : (Fin n → Bool) → X)
    {p : ℝ} (hp : 0 < p) : eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) := by
  sorry

section Seminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The discrete heat semigroup** ([HNVW, (6.6)]): `T (t) (Σ_α w_α x_α) = Σ_α e^{−t #α} w_α x_α`,
with `w_α = Π_{i ∈ α} ε_i`, `α ⊆ {1, …, n}`. -/
theorem heatSemigroup_walsh (t : ℝ) {n : ℕ} (x : Finset (Fin n) → E) :
    heatSemigroup t (fun ε : Fin n → Bool => ∑ α, (∏ i ∈ α, coin (ε i)) • x α) =
      fun ε => ∑ α, Real.exp (-t * α.card) • (∏ i ∈ α, coin (ε i)) • x α := by
  sorry

/-- **Hypercontractivity** ([HNVW, Theorem 6.2.2], the "if" part): `‖T (t) f‖_q ≤ ‖f‖_p` for
`1 < p ≤ q < ∞` and `e^{−t} ≤ √((p − 1)/(q − 1))`. -/
theorem heatSemigroup_hypercontractive (S : Seminorm ℝ E) {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (ht : Real.exp (-t) ≤ √((p - 1) / (q - 1))) {n : ℕ} (f : (Fin n → Bool) → E) :
    SignCube.lpNorm S q (heatSemigroup t f) ≤ SignCube.lpNorm S p f := by
  sorry

/-- **Bonami's inequality** ([HNVW, Lemma 6.2.3], the "if" part): for `1 < p ≤ q < ∞` and
`0 ≤ θ ≤ √((p − 1)/(q − 1))`, `‖x + θ ε y‖_q ≤ ‖x + ε y‖_p` for one sign `ε`. -/
theorem bonami (S : Seminorm ℝ E) {p q θ : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ √((p - 1) / (q - 1))) (x y : E) :
    ((S (x + θ • y) ^ q + S (x - θ • y) ^ q) / 2) ^ (1 / q) ≤
      ((S (x + y) ^ p + S (x - y) ^ p) / 2) ^ (1 / p) := by
  sorry

/-- **Affine hypercontractivity** ([B, (2.1)] for polynomials of degree at most `1`): for
`1 < p ≤ q < ∞` and `ρ = √((p − 1)/(q − 1))`, `‖c + ρ Σ_i ε_i x_i‖_q ≤ ‖c + Σ_i ε_i x_i‖_p`. -/
theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) := by
  sorry

/-- **The Kahane–Khintchine inequality** ([HNVW, Theorem 6.2.4], real signs, `1 < p ≤ q < ∞`):
`‖Σ ε_i x_i‖_q ≤ √((q − 1)/(p − 1)) ‖Σ ε_i x_i‖_p`. -/
theorem kahaneKhintchine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {n : ℕ}
    (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

end Seminorm

/-- **The Kahane–Khintchine inequality**, all exponents ([HNVW, Theorem 6.2.4], real signs): for
`p, q ∈ (0, ∞)` there is a constant `κ`, which depends only on `p` and `q`, such that
`‖Σ ε_i x_i‖_q ≤ κ ‖Σ ε_i x_i‖_p` in every seminormed space. -/
theorem exists_kahaneKhintchine {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Seminorm ℝ E) {n : ℕ}
      (x : Fin n → E),
      SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
        κ * SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := by
  sorry

section Contraction

variable {X : Type*} [NormedAddCommGroup X] {p : ℝ} {N : ℕ}

/-- **Kahane's contraction principle**, real scalars ([HNVW I, Proposition 3.2.10], `p < ∞`):
`‖Σ c_k ε_k x_k‖_p ≤ M ‖Σ ε_k x_k‖_p` for real `|c_k| ≤ M`, `1 ≤ p < ∞`. -/
theorem contraction_real [NormedSpace ℝ X] (hp : 1 ≤ p) {c : Fin N → ℝ} {M : ℝ}
    (hc : ∀ k, |c k| ≤ M) (x : Fin N → X) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      M * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  sorry

/-- **Kahane's contraction principle**, complex scalars and real signs ([HNVW I, Proposition 3.2.10,
(3.15)], `p < ∞`): `‖Σ c_k ε_k x_k‖_p ≤ (π/2) M ‖Σ ε_k x_k‖_p` for complex `|c_k| ≤ M`, `1 ≤ p < ∞`.
-/
theorem contraction_complex [NormedSpace ℂ X] (hp : 1 ≤ p) {c : Fin N → ℂ} {M : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ M) (x : Fin N → X) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      Real.pi / 2 * M *
        SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) := by
  sorry

end Contraction

end KahaneKhintchineChallenge
