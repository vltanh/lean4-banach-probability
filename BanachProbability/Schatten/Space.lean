module

public import BanachProbability.Schatten.Triangle
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Schatten class as a normed space

`SchattenSpace q m n` is the space of real `m × n` matrices with the Schatten `q`-norm, for
`q ∈ [1, ∞]` (`[Fact (1 ≤ q)]`): a type synonym of `Matrix m n ℝ` carrying the normed-space
structure of `schattenNorm q` (and no other topology). It is finite-dimensional, hence complete.
`SchattenSpace.ofMatrix` is the identity, as a linear equivalence, and
`‖ofMatrix A‖ = schattenNorm q A` holds by definition.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

/-- The real `m × n` matrices with the Schatten `q`-norm. -/
def SchattenSpace (_q : ℝ≥0∞) (m n : Type*) : Type _ := Matrix m n ℝ

namespace SchattenSpace

variable {q : ℝ≥0∞} {m n : Type*}

instance : AddCommGroup (SchattenSpace q m n) := inferInstanceAs (AddCommGroup (Matrix m n ℝ))

instance : Module ℝ (SchattenSpace q m n) := inferInstanceAs (Module ℝ (Matrix m n ℝ))

/-- The identity map `Matrix m n ℝ → SchattenSpace q m n`, as a linear equivalence. -/
def ofMatrix : Matrix m n ℝ ≃ₗ[ℝ] SchattenSpace q m n := LinearEquiv.refl ℝ _

instance [Finite m] [Finite n] : FiniteDimensional ℝ (SchattenSpace q m n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix m n ℝ))

variable [Fintype m] [Fintype n] [DecidableEq n]

noncomputable instance : Norm (SchattenSpace q m n) :=
  ⟨fun A => schattenNorm q (ofMatrix.symm A)⟩

theorem norm_def (A : SchattenSpace q m n) : ‖A‖ = schattenNorm q (ofMatrix.symm A) := rfl

@[simp] theorem norm_ofMatrix (A : Matrix m n ℝ) :
    ‖(ofMatrix A : SchattenSpace q m n)‖ = schattenNorm q A := rfl

theorem normedSpaceCore [hq : Fact (1 ≤ q)] : NormedSpace.Core ℝ (SchattenSpace q m n) where
  norm_nonneg A := schattenNorm_nonneg q _
  norm_smul c A := by
    rw [norm_def, norm_def, map_smul, Real.norm_eq_abs,
      schattenNorm_smul (zero_lt_one.trans_le hq.out).ne']
  norm_triangle A B := by
    rw [norm_def, norm_def, norm_def, map_add]
    exact schattenNorm_add_le hq.out _ _
  norm_eq_zero_iff A := by
    rw [norm_def, schattenNorm_eq_zero_iff (zero_lt_one.trans_le hq.out).ne',
      LinearEquiv.map_eq_zero_iff]

noncomputable instance [Fact (1 ≤ q)] : NormedAddCommGroup (SchattenSpace q m n) :=
  NormedAddCommGroup.ofCore normedSpaceCore

noncomputable instance [Fact (1 ≤ q)] : NormedSpace ℝ (SchattenSpace q m n) :=
  NormedSpace.ofCore normedSpaceCore

instance [Fact (1 ≤ q)] : CompleteSpace (SchattenSpace q m n) :=
  FiniteDimensional.complete ℝ _

end SchattenSpace

end BanachProbability
