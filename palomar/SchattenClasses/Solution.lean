module

public import BanachProbability.Noncommutative.MatrixUMD

/-!
# Solution: Schatten classes and noncommutative martingale transforms

The statements of `palomar/SchattenClasses/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SchattenClassesChallenge

open BanachProbability
open scoped Matrix

section Norms

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq n]

theorem schattenNorm_eq_singularValues (A : Matrix m n ℝ) :
    (∀ q : ℝ, 0 < q → schattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), (Matrix.toEuclideanLin A).singularValues k ^ q) ^
        (1 / q)) ∧
    schattenNorm ∞ A = (Matrix.toEuclideanLin A).singularValues 0 :=
  ⟨fun _ hq => schattenNorm_eq_sum_singularValues hq A, schattenNorm_top_eq_singularValues A⟩

theorem complexSchattenNorm_eq_singularValues (A : Matrix m n ℂ) :
    (∀ q : ℝ, 0 < q → complexSchattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), (Matrix.toEuclideanLin A).singularValues k ^ q) ^
        (1 / q)) ∧
    complexSchattenNorm ∞ A = (Matrix.toEuclideanLin A).singularValues 0 :=
  ⟨fun _ hq => complexSchattenNorm_eq_sum_singularValues hq A,
    complexSchattenNorm_top_eq_singularValues A⟩

theorem schattenNorm_triangle {q : ℝ≥0∞} (hq : 1 ≤ q) :
    (∀ A B : Matrix m n ℝ, schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B) ∧
    ∀ A B : Matrix m n ℂ,
      complexSchattenNorm q (A + B) ≤ complexSchattenNorm q A + complexSchattenNorm q B :=
  ⟨schattenNorm_add_le hq, complexSchattenNorm_add_le hq⟩

theorem horn_prod [DecidableEq m] (A : Matrix l m ℝ) (B : Matrix m n ℝ) (N : ℕ) :
    ∏ k ∈ Finset.range N, (Matrix.toEuclideanLin (A * B)).singularValues k ≤
      ∏ k ∈ Finset.range N, (Matrix.toEuclideanLin A).singularValues k *
        (Matrix.toEuclideanLin B).singularValues k := by
  simpa only [singularValues_toEuclideanLin] using prod_sortedSingularValue_mul_le A B N

theorem horn_sum (L : List (Matrix n n ℝ)) (N : ℕ) :
    ∑ k ∈ Finset.range N, (Matrix.toEuclideanLin L.prod).singularValues k ≤
      ∑ k ∈ Finset.range N,
        (L.map fun A => (Matrix.toEuclideanLin A).singularValues k).prod := by
  simpa only [singularValues_toEuclideanLin] using sum_sortedSingularValue_prod_le L N

theorem schattenNorm_holder [DecidableEq m] {p q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / p = 1 / q + 1 / r) :
    (∀ (A : Matrix l m ℝ) (B : Matrix m n ℝ), schattenNorm (ENNReal.ofReal p) (A * B) ≤
      schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal r) B) ∧
    ∀ (A : Matrix l m ℂ) (B : Matrix m n ℂ), complexSchattenNorm (ENNReal.ofReal p) (A * B) ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal r) B :=
  ⟨schattenNorm_mul_le hq hr hpqr, complexSchattenNorm_mul_le hq hr hpqr⟩

theorem abs_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    |(A * B).trace| ≤ schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal q') B :=
  BanachProbability.abs_trace_mul_le hq A B

end Norms

section Transforms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ → Ω → ℝ} {N : ℕ}
  {x : Ω → Matrix n n ℝ}

theorem weakType_posSemidef (hx : MatrixMemLp x 1 μ) (hx0 : ∀ ω, (x ω).PosSemidef)
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 26 * matrixTrace μ x :=
  weakType_one_one_of_posSemidef hx hx0 hc hc1 hl

theorem weakType (hx : MatrixMemLp x 1 μ) (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 52 * ∫ ω, schattenNorm 1 (x ω) ∂μ :=
  weakType_one_one_of_memLp hx hc hc1 hl

theorem transform_bounded (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1)
    {r : ℝ} (hr : 1 < r) (hxm : Measurable[ℱ N] x) (hx : MatrixMemLp x (ENNReal.ofReal r) μ) :
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (ncTransform ℱ μ c N x ω))
        (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (192 * 864 ^ 3 * max r (r / (r - 1))) *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ :=
  eLpNorm_ncTransform_le hc hc1 hr hxm hx

end Transforms

theorem umd_schatten {q : ℝ} (hq : 1 < q) (n : Type) [Fintype n] [DecidableEq n] :
    IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) q
        (ENNReal.ofReal (192 * 864 ^ 3 * max q (q / (q - 1)))) ∧
      IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) q
        (ENNReal.ofReal (192 * 864 ^ 3 * max q (q / (q - 1)))) :=
  ⟨isMatrixUMDBound_schattenNorm hq n, isMatrixUMDBound_complexSchattenNorm hq n⟩

theorem umd_two_schatten : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℝ, 1 < q → ∀ (n : Type) [Fintype n] [DecidableEq n],
      IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) 2
          (ENNReal.ofReal (C * (max q (q / (q - 1)) - 1))) ∧
        IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) 2
          (ENNReal.ofReal (C * (max q (q / (q - 1)) - 1))) :=
  isMatrixUMDBound_two

end SchattenClassesChallenge
