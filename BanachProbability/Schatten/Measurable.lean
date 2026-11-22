module

public import BanachProbability.Schatten.Spectral
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Measurability of the functional calculus of real symmetric matrices

Real matrices carry the product topology and the product (Borel) σ-algebra
(`Mathlib.Analysis.Matrix.MeasurableSpace`). This file proves that the maps of matrix analysis
that the noncommutative martingale inequalities apply pointwise to matrix-valued functions are
Borel measurable:

* `A ↦ cfc f A` for every `f : ℝ → ℝ` that is a pointwise limit of continuous functions
  (`measurable_cfc_of_tendsto_continuous`): for a polynomial `p`, `cfc p A = p (A)` on symmetric
  matrices (`cfc_polynomial`) and `0` elsewhere, a continuous function is the pointwise limit of
  polynomials (Weierstrass, `exists_polynomial_near_of_continuousOn`, on `[−k, k]`), and
  `cfc f A = U diag (f (λ_i)) Uᵀ` depends continuously on the finitely many values `f (λ_i)`, so
  pointwise limits pass through `cfc` (`measurable_cfc_of_tendsto`);
* spectral projections `1_{[a, b]} (A)` and `1_{(a, ∞)} (A)`;
* the eigenvalues of symmetric matrices (`hermitianEigenvalue`), since the `k`-th largest
  eigenvalue exceeds `t` exactly when `tr 1_{(t, ∞)} (A) > k`; hence the singular values, the
  Schatten norms and the counting function `countAbove`, jointly in the level and the matrix.

The instances `SecondCountableTopology (Matrix m n ℝ)` and `PseudoMetrizableSpace (Matrix m n ℝ)`
(those of `m → n → ℝ`) make products, sums and limits of measurable matrix-valued functions
measurable.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

namespace BanachProbability

instance {m n : Type*} [Countable m] [Countable n] : SecondCountableTopology (Matrix m n ℝ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℝ))

instance {m n : Type*} [Countable m] [Countable n] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → ℝ))

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The set of symmetric matrices is measurable. -/
theorem measurableSet_isHermitian : MeasurableSet {A : Matrix n n ℝ | A.IsHermitian} := by
  sorry

/-- Pointwise limits pass through the functional calculus: if `F k → f` pointwise and each
`A ↦ cfc (F k) A` is measurable, so is `A ↦ cfc f A`. -/
theorem measurable_cfc_of_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ k, Measurable fun A : Matrix n n ℝ => cfc (F k) A)
    (h : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Measurable fun A : Matrix n n ℝ => cfc f A := by
  sorry

/-- `A ↦ cfc f A` is measurable for a continuous `f`. -/
theorem measurable_cfc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun A : Matrix n n ℝ => cfc f A := by
  sorry

/-- `A ↦ cfc f A` is measurable when `f` is a pointwise limit of continuous functions. -/
theorem measurable_cfc_of_tendsto_continuous {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ k, Continuous (F k)) (h : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Measurable fun A : Matrix n n ℝ => cfc f A := by
  sorry

theorem measurable_spectralProj_Icc (a b : ℝ) :
    Measurable fun A : Matrix n n ℝ => spectralProj A (Set.Icc a b) := by
  sorry

theorem measurable_spectralProj_Ioi (a : ℝ) :
    Measurable fun A : Matrix n n ℝ => spectralProj A (Set.Ioi a) := by
  sorry

/-- The `i`-th eigenvalue of a symmetric matrix (in the order of `Matrix.IsHermitian.eigenvalues`),
extended by `0` to the other matrices. -/
noncomputable def hermitianEigenvalue (i : n) (A : Matrix n n ℝ) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues i else 0

theorem hermitianEigenvalue_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hermitianEigenvalue i A = hA.eigenvalues i := by
  rw [hermitianEigenvalue, dif_pos hA]

theorem measurable_hermitianEigenvalue (i : n) : Measurable (hermitianEigenvalue (n := n) i) := by
  sorry

variable {m : Type*} [Fintype m]

theorem measurable_singularValue (i : n) : Measurable fun A : Matrix m n ℝ => singularValue A i := by
  sorry

theorem measurable_schattenNorm (q : ℝ≥0∞) : Measurable fun A : Matrix m n ℝ => schattenNorm q A := by
  sorry

/-- The counting function `#{i : s_i (A) > s}` is measurable jointly in the level and the
matrix. -/
theorem measurable_countAbove_uncurry :
    Measurable fun p : ℝ × Matrix m n ℝ => (countAbove p.1 p.2 : ℝ) := by
  sorry

theorem measurable_countAbove (s : ℝ) : Measurable fun A : Matrix m n ℝ => (countAbove s A : ℝ) := by
  sorry

end BanachProbability
