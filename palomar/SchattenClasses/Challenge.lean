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
# Challenge: Schatten classes and noncommutative martingale transforms

Inequalities for the singular values and the Schatten norms of real and complex matrices, and the
martingale transforms of matrix-valued martingales: their weak type `(1, 1)`, their boundedness in
`L^r (S_r)`, and the UMD property of the Schatten classes, with a constant of the order of `q*` in
`L^q`, uniformly in the size of the matrices. After

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Springer, 2016: Appendix D, Proposition D.2.3, Corollary
  D.2.4, Theorem D.2.6;
* [TJ] N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages of
  trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974), 163–182: Lemma 1.1;
* [BZ] J.-C. Bourin, T. Zhang, *Matrix triangle inequalities: past, present, and future*,
  arXiv:2610.30538 (2026): Proposition 3.13, Remark 3.14 (the triangle inequality);
* [R] N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002),
  181–212, arXiv:math/0111264: Theorems 3.1 and 4.3, Corollary 4.5, Remark 4.6 (1).

## Conventions

* `schattenNorm q A` and `complexSchattenNorm q A` are the Schatten norms `‖A‖_{S_q}`, `q` in `ℝ≥0∞`
  (`ENNReal.ofReal q` is a real `q`), from the eigenvalues of `Aᵀ A` and `Aᴴ A`;
  `schattenNorm_eq_singularValues` expresses them by Mathlib's singular values of a linear map,
  `s_0 ≥ s_1 ≥ …`, `s_k = 0` beyond the rank; in the docstrings `s_k (A)` are those of `A`.
* The von Neumann algebra of [R] is `𝒩 = L^∞ (Ω, μ) ⊗ M_n (ℝ)` here, `μ` a probability, with the
  trace `τ (x) = ∫ tr x dμ` (`matrixTrace`) and the filtration `L^∞ (ℱ_k) ⊗ M_n (ℝ)`, whose
  conditional expectations `E_k` act entrywise (`matrixCondExp`). `L^r (𝒩)` is `L^r (μ; S_r)`, and
  the weak `L¹` quasi-norm is `sup_λ λ τ (1_{(λ, ∞)} (|x|))`, where
  `τ (1_{(λ, ∞)} (|x|)) = ncDistribution μ λ x` is the integral of the number of singular values
  larger than `λ`.
* `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` (`ncTransform ℱ μ c N x`), with scalar
  multipliers `c_k`, `ℱ_k`-measurable and `|c_k| ≤ 1`. ([R, Theorem 3.1] has multipliers `ξ_k` in
  the algebra of time `k` that commute with the algebra of time `k + 1`, which for this `𝒩` are the
  real scalar functions; for the complex matrices of the source they are the complex scalar
  functions.)
* A matrix-valued martingale is a process whose entries are martingales; `IsMatrixUMDBound nrm p β`
  is the UMD inequality in `L^p` with constant `β` for the norm `nrm`, predictable signs, and
  probability spaces in the universe `Type`.

## Statements

* `schattenNorm_eq_singularValues`, `complexSchattenNorm_eq_singularValues`: checks of the
  definitions.
* `schattenNorm_triangle` ([BZ, Proposition 3.13], for square matrices): the triangle inequality,
  `1 ≤ q ≤ ∞`, for rectangular matrices.
* `horn_prod` ([HNVW, Proposition D.2.3]), `horn_sum` ([TJ, Lemma 1.1]): Horn's inequalities for the
  singular values of products.
* `schattenNorm_holder` ([HNVW, Corollary D.2.4]), `abs_trace_mul_le` ([HNVW, Theorem D.2.6]):
  Hölder's inequality, and for the trace.
* `weakType_posSemidef`, `weakType` ([R, Theorem 3.1]; there with `x_N = E_N x` for `x` on the
  right): `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ C ‖x‖_{L¹ (τ)}`, `C = 26` for `x ⪰ 0` and `C = 52` for all
  `x`.
* `transform_bounded` ([R, Theorem 4.3]): `‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}`, `1 < r < ∞`,
  `r* = max (r, r/(r − 1))`, `K = 192 · 864³`.
* `umd_schatten` ([R, Corollary 4.5]): `UMD_q (S_q) ≤ K q*`, real and complex `n × n` matrices;
  `umd_two_schatten` ([R, Remark 4.6 (1)]): `UMD₂ (S_q) ≤ C (q* − 1)`.

The definitions are copied word for word from `BanachProbability/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/SchattenClasses/Solution.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

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

namespace SchattenClassesChallenge

open BanachProbability
open scoped Matrix

section Norms

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq n]

/-- **What `schattenNorm` is**: `‖A‖_{S_q} = (Σ_k s_k (A)^q)^{1/q}` for `0 < q < ∞` and
`‖A‖_{S_∞} = s_0 (A)`, with Mathlib's singular values of the linear map of `A`. -/
theorem schattenNorm_eq_singularValues (A : Matrix m n ℝ) :
    (∀ q : ℝ, 0 < q → schattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), (Matrix.toEuclideanLin A).singularValues k ^ q) ^
        (1 / q)) ∧
    schattenNorm ∞ A = (Matrix.toEuclideanLin A).singularValues 0 := by
  sorry

/-- **What `complexSchattenNorm` is**, as `schattenNorm_eq_singularValues`. -/
theorem complexSchattenNorm_eq_singularValues (A : Matrix m n ℂ) :
    (∀ q : ℝ, 0 < q → complexSchattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), (Matrix.toEuclideanLin A).singularValues k ^ q) ^
        (1 / q)) ∧
    complexSchattenNorm ∞ A = (Matrix.toEuclideanLin A).singularValues 0 := by
  sorry

/-- **The triangle inequality** for the Schatten norms, `1 ≤ q ≤ ∞`, real and complex rectangular
matrices ([BZ, Proposition 3.13], for complex square ones). -/
theorem schattenNorm_triangle {q : ℝ≥0∞} (hq : 1 ≤ q) :
    (∀ A B : Matrix m n ℝ, schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B) ∧
    ∀ A B : Matrix m n ℂ,
      complexSchattenNorm q (A + B) ≤ complexSchattenNorm q A + complexSchattenNorm q B := by
  sorry

/-- **Horn's inequality** ([HNVW, Proposition D.2.3]): `Π_{k<N} s_k (A B) ≤ Π_{k<N} s_k (A) s_k (B)`
for real matrices. -/
theorem horn_prod [DecidableEq m] (A : Matrix l m ℝ) (B : Matrix m n ℝ) (N : ℕ) :
    ∏ k ∈ Finset.range N, (Matrix.toEuclideanLin (A * B)).singularValues k ≤
      ∏ k ∈ Finset.range N, (Matrix.toEuclideanLin A).singularValues k *
        (Matrix.toEuclideanLin B).singularValues k := by
  sorry

/-- **The general Horn inequality** ([TJ, Lemma 1.1]):
`Σ_{k<N} s_k (A_1 ⋯ A_r) ≤ Σ_{k<N} s_k (A_1) ⋯ s_k (A_r)` for real square matrices. -/
theorem horn_sum (L : List (Matrix n n ℝ)) (N : ℕ) :
    ∑ k ∈ Finset.range N, (Matrix.toEuclideanLin L.prod).singularValues k ≤
      ∑ k ∈ Finset.range N,
        (L.map fun A => (Matrix.toEuclideanLin A).singularValues k).prod := by
  sorry

/-- **Hölder's inequality** ([HNVW, Corollary D.2.4], there for exponents at least `1`):
`‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r`, `0 < q, r < ∞`, real and complex matrices.
-/
theorem schattenNorm_holder [DecidableEq m] {p q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / p = 1 / q + 1 / r) :
    (∀ (A : Matrix l m ℝ) (B : Matrix m n ℝ), schattenNorm (ENNReal.ofReal p) (A * B) ≤
      schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal r) B) ∧
    ∀ (A : Matrix l m ℂ) (B : Matrix m n ℂ), complexSchattenNorm (ENNReal.ofReal p) (A * B) ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal r) B := by
  sorry

/-- `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`, `1/q + 1/q' = 1`, real matrices ([HNVW, Theorem D.2.6],
one inequality of the duality). -/
theorem abs_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    |(A * B).trace| ≤ schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal q') B := by
  sorry

end Norms

section Transforms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ → Ω → ℝ} {N : ℕ}
  {x : Ω → Matrix n n ℝ}

/-- **Weak type `(1, 1)`**, positive semidefinite `x` ([R, Theorem 3.1]; its proof has, for `x ≥ 0`,
a larger constant): `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 26 τ (x)` for `x ∈ L¹`, `x ⪰ 0`, and `λ > 0`. -/
theorem weakType_posSemidef (hx : MatrixMemLp x 1 μ) (hx0 : ∀ ω, (x ω).PosSemidef)
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 26 * matrixTrace μ x := by
  sorry

/-- **Weak type `(1, 1)`** ([R, Theorem 3.1]): `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 52 ‖x‖_{L¹ (τ)}` for
`x ∈ L¹`, real matrices, and `λ > 0`. -/
theorem weakType (hx : MatrixMemLp x 1 μ) (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 52 * ∫ ω, schattenNorm 1 (x ω) ∂μ := by
  sorry

/-- **Martingale transforms on `L^r (S_r)`** ([R, Theorem 4.3]):
`‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}` for `1 < r < ∞`, `r* = max (r, r/(r − 1))`, and an
`ℱ_N`-measurable `x ∈ L^r`, with the absolute constant `K = 192 · 864³`. (As `r* ≤ r²/(r − 1)`, this
gives the source's `C r²/(r − 1)`.) -/
theorem transform_bounded (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1)
    {r : ℝ} (hr : 1 < r) (hxm : Measurable[ℱ N] x) (hx : MatrixMemLp x (ENNReal.ofReal r) μ) :
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (ncTransform ℱ μ c N x ω))
        (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (192 * 864 ^ 3 * max r (r / (r - 1))) *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ := by
  sorry

end Transforms

/-- **The Schatten classes are UMD**, uniformly in the size ([R, Corollary 4.5]): for `1 < q < ∞`,
`q* = max (q, q/(q − 1))`, the UMD inequality holds in `L^q (S_q)` with the constant `K q*`,
`K = 192 · 864³`, for real and for complex `n × n` matrices. -/
theorem umd_schatten {q : ℝ} (hq : 1 < q) (n : Type) [Fintype n] [DecidableEq n] :
    IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) q
        (ENNReal.ofReal (192 * 864 ^ 3 * max q (q / (q - 1)))) ∧
      IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) q
        (ENNReal.ofReal (192 * 864 ^ 3 * max q (q / (q - 1)))) := by
  sorry

/-- **The UMD constants of the Schatten classes in `L²`** ([R, Remark 4.6 (1)], for all
`1 < q < ∞`): there is an absolute `C` such that the UMD inequality holds in `L² (S_q)` with the
constant `C (q* − 1)`, for real and for complex `n × n` matrices of every size. -/
theorem umd_two_schatten : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℝ, 1 < q → ∀ (n : Type) [Fintype n] [DecidableEq n],
      IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) 2
          (ENNReal.ofReal (C * (max q (q / (q - 1)) - 1))) ∧
        IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) 2
          (ENNReal.ofReal (C * (max q (q / (q - 1)) - 1))) := by
  sorry

end SchattenClassesChallenge
