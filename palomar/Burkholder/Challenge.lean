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
# Challenge: Burkholder's inequality for martingales in a Hilbert space

The sharp `L^p` inequality for differentially subordinate martingales with values in a real Hilbert
space `H`, `1 < p < ∞`, and the square function inequality that follows from it, after

* [B] D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
  Lévy sur les processus stochastiques, Astérisque 157–158 (1988), 75–94: Theorems 1.1 and 3.1, the
  function (1.6), (1.10), Remark 1.2;
* [O] A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
  Birkhäuser, 2012: Theorem 3.5 (ii), Remark 3.8, Theorem 8.6.

## Conventions

* `p` is a real number, `p* = max (p, p / (p − 1))`, that is, `p* − 1 = max (p − 1, 1 / (p − 1))`.
* Martingales `f_0, f_1, …` are Mathlib's `MeasureTheory.Martingale`, for a filtration of a
  probability space, with values in `H` (complete, not assumed separable). In [B] `H` is a real or
  complex Hilbert space; a complex one is a real one, with the same norm.
* `eLpNorm f (ENNReal.ofReal p) μ` is the `L^p` norm `(E ‖f‖^p)^{1/p}`, in `[0, ∞]`. The sources
  have `‖f‖_p = sup_n ‖f_n‖_p`; the inequalities are stated here at every fixed time `n`, which
  gives theirs.
* The sign cube `Fin N → Bool` stands for `N` independent fair signs `ε_k = coin (ε k) ∈ {±1}`;
  `SignCube.lpNorm nrm p X = (2^{−N} Σ_ε nrm (X (ε))^p)^{1/p}`. The Paley–Walsh (dyadic) martingale
  of a family `φ_k`, where `φ_k` depends on `ε_j`, `j < k`, only (`IsPredictable φ`), is
  `n ↦ Σ_{k<n} ε_k φ_k` (`paleyWalsh φ n`), and its transform by signs `l_k` is
  `n ↦ Σ_{k<n} l_k ε_k φ_k`. `martingale_paleyWalsh` says that these are martingales on the cube
  with the uniform probability, and that `SignCube.lpNorm` is the `L^p` norm there.

## Statements

* `burkholder_inequality` ([B, Theorem 1.1], [O, Theorem 3.5 (ii)]): if `‖g_0‖ ≤ ‖f_0‖` and
  `‖g_{n+1} − g_n‖ ≤ ‖f_{n+1} − f_n‖` almost surely, then `‖g_n‖_p ≤ (p* − 1) ‖f_n‖_p`.
* `burkholder_sharp` ([O, Theorem 3.5 (ii), Remark 3.8]): no smaller constant will do, even for real
  dyadic martingales `f` started at `0` and their transforms `g` by deterministic signs `±1`. (The
  case of equality in [B, Theorem 1.1] is not formalized.)
* `squareFunction_inequality` ([O, Theorem 8.6, (8.28)], [B, Theorem 3.1]): for
  `S_n (f) = (‖f_0‖² + Σ_{k<n} ‖f_{k+1} − f_k‖²)^{1/2}`,
  `(p* − 1)⁻¹ ‖f_n‖_p ≤ ‖S_n (f)‖_p ≤ (p* − 1) ‖f_n‖_p`. (The sharpness clauses are not formalized.)
* `burkholderFun_majorizes`, `burkholderFun_concave` ([B, (1.10), Remark 1.2]): the properties of
  Burkholder's function `u_p` (`burkholderFun`).
* `martingale_paleyWalsh`: a check of the definitions on the sign cube.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/Burkholder/Solution.lean`.
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

end BanachProbability

namespace BurkholderChallenge

open BanachProbability BanachProbability.SignCube

section Hilbert

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {p : ℝ}

/-- **Burkholder's inequality** ([O, Theorem 3.5 (ii), (3.59)], [B, Theorem 1.1]): let `f` and `g`
be martingales with values in a real Hilbert space such that `g` is differentially subordinate to
`f`: `‖g_0‖ ≤ ‖f_0‖` and `‖g_{n+1} − g_n‖ ≤ ‖f_{n+1} − f_n‖` almost surely. Then
`‖g_n‖_p ≤ (p* − 1) ‖f_n‖_p` for `1 < p < ∞`. -/
theorem burkholder_inequality (hp : 1 < p) {f g : ℕ → Ω → H} (hf : Martingale f ℱ μ)
    (hg : Martingale g ℱ μ) (h0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (h : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖) (n : ℕ) :
    eLpNorm (g n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  sorry

/-- **The square function inequality** ([O, Theorem 8.6, (8.28)], [B, Theorem 3.1]): for a
martingale `f` in a real Hilbert space and `S_n (f) = (‖f_0‖² + Σ_{k<n} ‖f_{k+1} − f_k‖²)^{1/2}`,
`‖S_n (f)‖_p ≤ (p* − 1) ‖f_n‖_p` and `‖f_n‖_p ≤ (p* − 1) ‖S_n (f)‖_p`, `1 < p < ∞`. -/
theorem squareFunction_inequality (hp : 1 < p) {f : ℕ → Ω → H} (hf : Martingale f ℱ μ) (n : ℕ) :
    eLpNorm (fun ω => √(‖f 0 ω‖ ^ 2 + ∑ k ∈ Finset.range n, ‖f (k + 1) ω - f k ω‖ ^ 2))
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ ∧
      eLpNorm (f n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(‖f 0 ω‖ ^ 2 + ∑ k ∈ Finset.range n, ‖f (k + 1) ω - f k ω‖ ^ 2))
            (ENNReal.ofReal p) μ := by
  sorry

end Hilbert

/-- **The constant `p* − 1` is best possible**, even for real dyadic martingales and their
transforms by deterministic signs ([O, Theorem 3.5 (ii) and Remark 3.8]; for martingales, [B,
Theorem 1.1]): for `K < p* − 1` there are a number of signs `N`, a predictable family `φ` of real
functions and constants `l_k ∈ {±1}` such that the martingale `f = Σ ε_k φ_k` and its transform
`g = Σ l_k ε_k φ_k` satisfy `K ‖f‖_p < ‖g‖_p`. -/
theorem burkholder_sharp {p K : ℝ} (hp : 1 < p) (hK : K < max p (p / (p - 1)) - 1) :
    ∃ (N : ℕ) (φ : Fin N → (Fin N → Bool) → ℝ) (l : Fin N → ℝ), IsPredictable φ ∧
      (∀ k, l k = 1 ∨ l k = -1) ∧
        K * SignCube.lpNorm (fun x => |x|) p (paleyWalsh φ N) <
          SignCube.lpNorm (fun x => |x|) p (paleyWalsh (fun k ε => l k * φ k ε) N) := by
  sorry

/-- **What the Paley–Walsh martingales are.** On the cube `Fin N → Bool` with the uniform
probability there is a filtration `ℱ_0 ⊆ ℱ_1 ⊆ …` such that the `ℱ_k`-measurable functions are those
that depend on the first `k` signs only, and the Paley–Walsh process of every predictable family
with values in a Banach space `E` is a martingale for it; and the `L^p` norm is `SignCube.lpNorm`,
`p > 0`. -/
theorem martingale_paleyWalsh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (N : ℕ) :
    (∃ ℱ : Filtration ℕ (inferInstance : MeasurableSpace (Fin N → Bool)),
      (∀ (k : ℕ) (f : (Fin N → Bool) → E), StronglyMeasurable[ℱ k] f ↔
        ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε') ∧
      ∀ ξ : Fin N → (Fin N → Bool) → E, IsPredictable ξ →
        Martingale (fun n => paleyWalsh ξ n) ℱ (ProbabilityTheory.uniformOn Set.univ)) ∧
    ∀ (f : (Fin N → Bool) → E) (p : ℝ), 0 < p →
      eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
        ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) := by
  sorry

/-- **Majorization** ([B, (1.10)]): `‖y‖^p − (p* − 1)^p ‖x‖^p ≤ u_p (x, y)`. -/
theorem burkholderFun_majorizes {H : Type*} [NormedAddCommGroup H] {p : ℝ} (hp : 1 < p)
    (x y : H) :
    ‖y‖ ^ p - (max p (p / (p - 1)) - 1) ^ p * ‖x‖ ^ p ≤ Burkholder.burkholderFun p x y := by
  sorry

/-- **Concavity** ([B, Remark 1.2, (1.17)], there without proof): in a real inner product space, if
`‖k‖ ≤ ‖h‖`, then `t ↦ u_p (x + t h, y + t k)` is concave on `ℝ`. -/
theorem burkholderFun_concave {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {p : ℝ}
    (hp : 1 < p) (x y h k : H) (hk : ‖k‖ ≤ ‖h‖) :
    ConcaveOn ℝ Set.univ fun t : ℝ => Burkholder.burkholderFun p (x + t • h) (y + t • k) := by
  sorry

end BurkholderChallenge
