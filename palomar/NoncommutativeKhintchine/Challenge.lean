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
# Challenge: the noncommutative Khintchine inequality

The two-sided noncommutative Khintchine inequality in the Schatten classes `S_q`, `q ≥ 2`, for real
square matrices, with an explicit constant of the order `√q` that does not depend on the size of the
matrices ([PX, Remark (i) after Theorem 6.1]: this order is the best possible, which is not
formalized). After

* [MJCFT] L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration
  inequalities via the method of exchangeable pairs*, Ann. Probab. 42 (2014), 906–945,
  arXiv:1201.6002: Corollary 7.3 and Remark 7.2 (Hermitian matrices), Section 8 (the dilation);
* [PX] G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach Spaces 2
  (2003), 1459–1517: Theorem 6.1 (i). The inequality is due to F. Lust-Piquard (*Inégalités de
  Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303 (1986), 289–292) and F.
  Lust-Piquard and G. Pisier (*Non commutative Khintchine and Paley inequalities*, Ark. Mat. 29
  (1991), 241–260).

## Conventions

* The sign cube `Fin k → Bool` stands for `k` independent fair signs `ε_i = coin (ε i) ∈ {±1}`, and
  `SignCube.lpNorm nrm q X = (E nrm (X)^q)^{1/q}` is an average over the cube.
* `schattenNorm q A` is the Schatten norm `‖A‖_{S_q}` of a real matrix, `q` in `ℝ≥0∞`;
  `ENNReal.ofReal q` is a real `q`.
* The row and column square functions are `(Σ x_i x_iᵀ)^{1/2}` and `(Σ x_iᵀ x_i)^{1/2}`, and their
  `S_q` norms are written as `‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2}` and `‖Σ x_iᵀ x_i‖_{S_{q/2}}^{1/2}`: by
  `schattenNorm_transpose_mul_self`, `‖Bᵀ B‖_{S_{q/2}} = ‖B‖_{S_q}²` for every `B`, in particular
  for the positive semidefinite square roots `B`. Also `‖B‖_{S_2}² = Σ B_{ij}²`
  (`schattenNorm_two_sq`).

## Statements

* `khintchine` ([PX, Theorem 6.1 (i)] for real square matrices): for `q ≥ 2` and
  `m = max (‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}, ‖(Σ x_iᵀ x_i)^{1/2}‖_{S_q})`,
  `m ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) m`. The upper bound is proved by the method of
  [MJCFT], not by those of Lust-Piquard and Pisier.
* `khintchine_of_eq_two_or_three_le`: the upper bound with the constant `√(q − 1)` for `q = 2` and
  `q ≥ 3`, from the next theorem and [MJCFT, Section 8].
* `khintchine_symmetric` ([MJCFT, Corollary 7.3, (7.2)], real symmetric matrices, `q = 2p`): the
  constant `√(q − 1)` for `q = 2` and `q ≥ 3`.
* `schattenNorm_transpose_mul_self`, `schattenNorm_two_sq`: checks of the definitions.

Not formalized: complex and rectangular matrices, `q < 2`, general von Neumann algebras.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/NoncommutativeKhintchine/Solution.lean`.
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

end BanachProbability

namespace NoncommutativeKhintchineChallenge

open BanachProbability BanachProbability.SignCube
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The noncommutative Khintchine inequality** ([PX, Theorem 6.1 (i)], for real square matrices,
with an explicit constant): for `q ≥ 2`, real `n × n` matrices `x_1, …, x_k` and
`m = max (‖Σ x_i x_iᵀ‖_{S_{q/2}}, ‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`,
`m ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) m`. -/
theorem khintchine {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) := by
  sorry

/-- **The upper bound with the constant `√(q − 1)`** for `q = 2` and `q ≥ 3` ([MJCFT, Corollary 7.3,
(7.2)] and the dilation of [MJCFT, Section 8], real square matrices): with `m` as in `khintchine`,
`(E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(q − 1) m`. -/
theorem khintchine_of_eq_two_or_three_le {q : ℝ} (hq : q = 2 ∨ 3 ≤ q) {k : ℕ}
    (x : Fin k → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q - 1) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) := by
  sorry

/-- **Symmetric matrices** ([MJCFT, Corollary 7.3, (7.2)], real symmetric matrices, `q = 2p`): for
`q = 2` and `q ≥ 3`, `(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(q − 1) ‖Σ A_i²‖_{S_{q/2}}^{1/2}`. -/
theorem khintchine_symmetric {q : ℝ} (hq : q = 2 ∨ 3 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q - 1) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  sorry

/-- `‖Bᵀ B‖_{S_{q/2}} = ‖B‖_{S_q}²`, `q ≠ 0`. -/
theorem schattenNorm_transpose_mul_self {m : Type*} [Fintype m] {q : ℝ≥0∞} (hq : q ≠ 0)
    (B : Matrix m n ℝ) : schattenNorm (q / 2) (Bᵀ * B) = schattenNorm q B ^ 2 := by
  sorry

/-- `‖B‖_{S_2}² = Σ B_{ij}²`. -/
theorem schattenNorm_two_sq {m : Type*} [Fintype m] (B : Matrix m n ℝ) :
    schattenNorm 2 B ^ 2 = ∑ i, ∑ j, B i j ^ 2 := by
  sorry

end NoncommutativeKhintchineChallenge
