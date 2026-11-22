module

public import BanachProbability.Noncommutative.MatrixCube
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Distribution functions on the matrix cube

For a matrix-valued function `x` on the sign cube, the distribution function
`λ_s (x) = τ (1_{(s, ∞)} (|x|)) = E #{i : s_i (x (ε)) > s}` (`distribution`). It is subadditive,
`λ_{s+t} (x + y) ≤ λ_s (x) + λ_t (y)` (from `countAbove_add_add_le`), satisfies Chebyshev's
inequality `s^r λ_s (x) ≤ ‖x‖_{L^r}^r`, and gives the layer-cake formula
`‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`. The spectral truncations of a symmetric matrix at level
`s`, `A 1_{(s, ∞)} (|A|)` and `A 1_{[0, s]} (|A|)` (`truncAbove`, `truncBelow`), split it into its
large and small eigenvalues.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The distribution function `λ_s (x) = E #{i : s_i (x (ε)) > s}`. -/
noncomputable def distribution (s : ℝ) (x : (Fin N → Bool) → Matrix n n ℝ) : ℝ :=
  avg fun ε => (countAbove s (x ε) : ℝ)

private theorem mcd_rpow_ite_eq_indicator (r a : ℝ) :
    (fun s : ℝ => r * s ^ (r - 1) * (if s < a then 1 else 0)) =
      (Set.Iio a).indicator fun s => r * s ^ (r - 1) := by
  funext s
  by_cases hs : s < a <;> simp [hs, Set.indicator]

/-- `∫_{(0, ∞)} r s^{r−1} 1_{s < a} ds = a^r` for `a ≥ 0`, `r > 0`. -/
private theorem mcd_integral_rpow_ite {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * (if s < a then 1 else 0) = a ^ r := by
  rw [mcd_rpow_ite_eq_indicator, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hr.ne', sub_zero, mul_div_cancel₀ _ hr.ne']

/-- `s ↦ r s^{r−1} 1_{s < a}` is integrable on `(0, ∞)` for `r > 0`. -/
private theorem mcd_integrableOn_rpow_ite {r : ℝ} (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun s : ℝ => r * s ^ (r - 1) * (if s < a then 1 else 0)) (Set.Ioi 0) := by
  rw [mcd_rpow_ite_eq_indicator, IntegrableOn, integrable_indicator_iff measurableSet_Iio,
    IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a)
    (r := r - 1) (by linarith)).const_mul r
  rw [intervalIntegrable_iff] at h
  refine h.mono_set fun s hs => ?_
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi] at hs
  simp only [Set.uIoc, Set.mem_Ioc, inf_lt_iff, le_sup_iff]
  exact ⟨Or.inl hs.2, Or.inr hs.1.le⟩

variable {m : Type*} [Fintype m] in
/-- `r s^{r−1} #{i : s_i (A) > s} = Σ_i r s^{r−1} 1_{s < s_i (A)}`. -/
private theorem mcd_mul_countAbove_eq_sum {r : ℝ} (A : Matrix m n ℝ) :
    (fun s : ℝ => r * s ^ (r - 1) * (countAbove s A : ℝ)) =
      fun s => ∑ i, r * s ^ (r - 1) * (if s < singularValue A i then 1 else 0) := by
  funext s
  rw [countAbove, Finset.natCast_card_filter, Finset.mul_sum]

variable {m : Type*} [Fintype m] in
/-- `s ↦ r s^{r−1} #{i : s_i (A) > s}` is integrable on `(0, ∞)` for `r > 0`. -/
theorem mcd_integrableOn_countAbove {r : ℝ} (hr : 0 < r) (A : Matrix m n ℝ) :
    IntegrableOn (fun s : ℝ => r * s ^ (r - 1) * (countAbove s A : ℝ)) (Set.Ioi 0) := by
  rw [mcd_mul_countAbove_eq_sum]
  exact integrable_finsetSum _ fun i _ => mcd_integrableOn_rpow_ite hr _

variable {m : Type*} [Fintype m] in
/-- The layer-cake formula for one matrix: `∫₀^∞ r s^{r−1} #{i : s_i (A) > s} ds = ‖A‖_{S_r}^r`. -/
theorem mcd_integral_countAbove {r : ℝ} (hr : 0 < r) (A : Matrix m n ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * (countAbove s A : ℝ) =
      schattenNorm (ENNReal.ofReal r) A ^ r := by
  have h := schattenNorm_rpow (q := ENNReal.ofReal r) (by simpa using hr) ENNReal.ofReal_ne_top A
  rw [ENNReal.toReal_ofReal hr.le] at h
  rw [h, mcd_mul_countAbove_eq_sum, integral_finsetSum _ fun i _ => mcd_integrableOn_rpow_ite hr _]
  exact Finset.sum_congr rfl fun i _ => mcd_integral_rpow_ite hr (singularValue_nonneg A i)

theorem distribution_add_add_le (s t : ℝ) (x y : (Fin N → Bool) → Matrix n n ℝ) :
    distribution (s + t) (x + y) ≤ distribution s x + distribution t y := by
  unfold distribution
  rw [← avg_add]
  refine avg_mono fun ε => ?_
  exact_mod_cast countAbove_add_add_le s t (x ε) (y ε)

theorem distribution_mul_rpow_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    distribution s x * s ^ r ≤ avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
  unfold distribution
  rw [mul_comm, ← avg_const_mul]
  refine avg_mono fun ε => ?_
  rw [mul_comm]
  exact countAbove_mul_rpow_le hs hr (x ε)

/-- The layer-cake formula `‖x‖_{L^r}^r = ∫₀^∞ r s^{r−1} λ_s (x) ds`. -/
theorem avg_schattenNorm_rpow_eq_integral {r : ℝ} (hr : 0 < r)
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    (avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r) =
      ∫ s in Set.Ioi (0 : ℝ), r * s ^ (r - 1) * distribution s x := by
  have hI : ∀ ε, IntegrableOn (fun s => r * s ^ (r - 1) * (countAbove s (x ε) : ℝ))
      (Set.Ioi 0) := fun ε => mcd_integrableOn_countAbove hr (x ε)
  simp only [distribution, avg, mul_div_assoc', Finset.mul_sum]
  rw [integral_div, integral_finsetSum _ fun ε _ => hI ε]
  simp only [mcd_integral_countAbove hr]

/-- The part `A 1_{(s, ∞)} (|A|)` of a symmetric matrix with the eigenvalues of absolute value
larger than `s`. -/
noncomputable def truncAbove (s : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => if s < |t| then t else 0) A

/-- The part `A 1_{[0, s]} (|A|)` of a symmetric matrix with the eigenvalues of absolute value at
most `s`. -/
noncomputable def truncBelow (s : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => if s < |t| then 0 else t) A

theorem truncAbove_add_truncBelow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) :
    truncAbove s A + truncBelow s A = A := by
  rw [truncAbove, truncBelow, ← cfc_add (R := ℝ) A _ _ (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _)]
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  congr 1
  funext t
  split_ifs <;> simp

theorem isHermitian_truncAbove (s : ℝ) (A : Matrix n n ℝ) : (truncAbove s A).IsHermitian := by
  exact cfc_predicate _ A

theorem isHermitian_truncBelow (s : ℝ) (A : Matrix n n ℝ) : (truncBelow s A).IsHermitian := by
  exact cfc_predicate _ A

/-- Two finite families with the same multiset of values differ by a bijection of the index
types. -/
theorem mcd_exists_equiv_apply_eq_of_map_univ_eq {ι κ γ : Type*} [Fintype ι] [Fintype κ]
    {f : ι → γ} {g : κ → γ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  classical
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq ?_),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
  have hc := congrArg (Multiset.count c) h
  rw [Multiset.count_map, Multiset.count_map] at hc
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa [Finset.card, Finset.filter_val, eq_comm] using hc

open Polynomial in
/-- The eigenvalues of `f (A)` are a permutation of the `f (λ_i (A))`, for a symmetric `A`. -/
theorem mcd_exists_equiv_eigenvalues_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hB : (cfc f A).IsHermitian) :
    ∃ e : n ≃ n, ∀ i, hB.eigenvalues (e i) = f (hA.eigenvalues i) := by
  apply mcd_exists_equiv_apply_eq_of_map_univ_eq
  have h1 := hB.roots_charpoly_eq_eigenvalues
  rw [hA.charpoly_cfc_eq f,
    Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])] at h1
  simpa using h1

/-- `‖f (A)‖_{S_r}^r = Σ_i |f (λ_i (A))|^r` for a symmetric `A` and `r > 0`. -/
theorem mcd_schattenNorm_cfc_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (cfc f A) ^ r = ∑ i, |f (hA.eigenvalues i)| ^ r := by
  have hB : (cfc f A).IsHermitian := cfc_predicate f A
  obtain ⟨e, he⟩ := mcd_exists_equiv_eigenvalues_cfc hA f hB
  rw [schattenNorm_rpow_of_isHermitian hB hr, ← e.sum_comp]
  simp [he]

open scoped Classical in
theorem schattenNorm_truncAbove_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncAbove s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => s < |hA.eigenvalues i|), |hA.eigenvalues i| ^ r := by
  rw [truncAbove, mcd_schattenNorm_cfc_rpow hA _ hr, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Real.zero_rpow hr.ne']

open scoped Classical in
theorem schattenNorm_truncBelow_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (truncBelow s A) ^ r =
      ∑ i ∈ Finset.univ.filter (fun i => |hA.eigenvalues i| ≤ s), |hA.eigenvalues i| ^ r := by
  rw [truncBelow, mcd_schattenNorm_cfc_rpow hA _ hr, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : s < |hA.eigenvalues i|
  · simp [h, not_le.mpr h, Real.zero_rpow hr.ne']
  · simp [h, not_lt.mp h]

end BanachProbability
