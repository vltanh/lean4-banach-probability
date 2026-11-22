module

public import BanachProbability.Schatten.Basic
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Spectral tools for Schatten norms

Functional calculus on real symmetric matrices is Mathlib's `cfc`
(`Matrix.IsHermitian.instContinuousFunctionalCalculus`); since the spectrum is finite, every
function is continuous on it. This file collects what the Schatten-valued inequalities use:

* singular values of a symmetric matrix are the absolute values of its eigenvalues, so
  `‖A‖_{S_q}^q = Σ |λ_i (A)|^q = tr (A h (A))` with `h (t) = t |t|^{q−2}`
  (`schattenNorm_rpow_eq_trace`);
* spectral projections `spectralProj A S = 1_S (A)`;
* the counting function `countAbove s A = #{i : s_i (A) > s}` (the distribution function of the
  singular values), with the rank perturbation bound
  `countAbove s (A + R) ≤ countAbove s A + rank R` and the subadditivity
  `countAbove (s + t) (A + B) ≤ countAbove s A + countAbove t B` (Weyl's inequalities for singular
  values, by a Courant–Fischer dimension count), and Chebyshev's inequality;
* Loewner-order and trace lemmas: `A − P A P ⪰ 0` for a projection `P` commuting with `A ⪰ 0`,
  `tr (A B) ≥ 0` and `tr (A B) ≤ c tr B` for `0 ⪯ A ⪯ c` and `B ⪰ 0`, and monotonicity of the
  Hilbert–Schmidt norm on `0 ⪯ A ⪯ B`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

section Square

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The singular values of a symmetric matrix are the absolute values of its eigenvalues, up to
a permutation. -/
theorem exists_equiv_singularValue_eq_abs_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ e : n ≃ n, ∀ i, singularValue A (e i) = |hA.eigenvalues i| := by
  sorry

theorem schattenNorm_rpow_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) {q : ℝ}
    (hq : 0 < q) : schattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, |hA.eigenvalues i| ^ q := by
  sorry

/-- `‖A‖_{S_q}^q = tr (A h (A))` with `h (t) = t |t|^{q−2}`, for a symmetric `A`. -/
theorem schattenNorm_rpow_eq_trace {A : Matrix n n ℝ} (hA : A.IsHermitian) {q : ℝ} (hq : 0 < q) :
    schattenNorm (ENNReal.ofReal q) A ^ q = (A * cfc (fun t : ℝ => t * |t| ^ (q - 2)) A).trace := by
  sorry

/-- The spectral projection `1_S (A)` of a symmetric matrix. -/
noncomputable def spectralProj (A : Matrix n n ℝ) (S : Set ℝ) : Matrix n n ℝ :=
  cfc (S.indicator (1 : ℝ → ℝ)) A

theorem spectralProj_mul_self {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : Set ℝ) :
    spectralProj A S * spectralProj A S = spectralProj A S := by
  sorry

theorem spectralProj_transpose {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : Set ℝ) :
    (spectralProj A S)ᵀ = spectralProj A S := by
  sorry

theorem commute_spectralProj {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : Set ℝ) :
    Commute A (spectralProj A S) := by
  sorry

open scoped Classical in
theorem trace_spectralProj {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : Set ℝ) :
    (spectralProj A S).trace = ((Finset.univ.filter fun i => hA.eigenvalues i ∈ S).card : ℝ) := by
  sorry

omit [DecidableEq n] in
/-- `A − P A P ⪰ 0` for an orthogonal projection `P` commuting with `A ⪰ 0`. -/
theorem posSemidef_sub_mul_mul_of_commute {A P : Matrix n n ℝ} (hA : A.PosSemidef)
    (hP : P * P = P) (hPt : Pᵀ = P) (hc : Commute P A) : (A - P * A * P).PosSemidef := by
  sorry

omit [DecidableEq n] in
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  sorry

/-- `tr (A B) ≤ c tr B` for `0 ⪯ A ⪯ c` and `B ⪰ 0`. -/
theorem trace_mul_le_of_le_smul_one {A B : Matrix n n ℝ} {c : ℝ} (hA : A.PosSemidef)
    (hAc : (c • (1 : Matrix n n ℝ) - A).PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace ≤ c * B.trace := by
  sorry

omit [DecidableEq n] in
/-- The Hilbert–Schmidt norm is monotone on positive semidefinite matrices:
`tr (A²) ≤ tr (B²)` for `0 ⪯ A ⪯ B`. -/
theorem trace_mul_self_le_of_le {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hAB : (B - A).PosSemidef) : (A * A).trace ≤ (B * B).trace := by
  sorry

end Square

section Count

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The number of singular values of `A` larger than `s`, `#{i : s_i (A) > s}`; for a symmetric
matrix, the number of eigenvalues with `|λ_i| > s`, the trace of `1_{(s, ∞)} (|A|)`. -/
noncomputable def countAbove (s : ℝ) (A : Matrix m n ℝ) : ℕ :=
  (Finset.univ.filter fun i => s < singularValue A i).card

theorem countAbove_anti {s t : ℝ} (hst : s ≤ t) (A : Matrix m n ℝ) :
    countAbove t A ≤ countAbove s A := by
  sorry

theorem countAbove_le_card (s : ℝ) (A : Matrix m n ℝ) : countAbove s A ≤ Fintype.card n := by
  sorry

/-- **Rank perturbation**: `#{s_i (A + R) > s} ≤ #{s_i (A) > s} + rank R` (Weyl's inequality
`s_{i+k+1} (A + R) ≤ s_{i+1} (A)` for `rank R ≤ k`, by a Courant–Fischer dimension count). -/
theorem countAbove_add_le_add_rank (s : ℝ) (A R : Matrix m n ℝ) :
    countAbove s (A + R) ≤ countAbove s A + R.rank := by
  sorry

/-- **Subadditivity of the distribution function**:
`#{s_i (A + B) > s + t} ≤ #{s_i (A) > s} + #{s_i (B) > t}` (Weyl's inequality
`s_{i+j+1} (A + B) ≤ s_{i+1} (A) + s_{j+1} (B)`). -/
theorem countAbove_add_add_le (s t : ℝ) (A B : Matrix m n ℝ) :
    countAbove (s + t) (A + B) ≤ countAbove s A + countAbove t B := by
  sorry

/-- **Chebyshev's inequality** for singular values: `s^q #{s_i (A) > s} ≤ ‖A‖_{S_q}^q`. -/
theorem countAbove_mul_rpow_le {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (A : Matrix m n ℝ) :
    (countAbove s A : ℝ) * s ^ q ≤ schattenNorm (ENNReal.ofReal q) A ^ q := by
  sorry

theorem countAbove_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) :
    countAbove s A = (Finset.univ.filter fun i => s < |hA.eigenvalues i|).card := by
  sorry

end Count

end BanachProbability
