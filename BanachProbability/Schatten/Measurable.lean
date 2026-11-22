module

public import BanachProbability.Schatten.Spectral
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
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
  `cfc f A = U diag (f (λ_i)) Uᵀ` depends only on the finitely many values `f (λ_i)`: pointwise
  convergence is uniform on the finite spectrum, so pointwise limits pass through `cfc`
  (`tendsto_cfc_fun`, `measurable_cfc_of_tendsto`);
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

/-- The set of symmetric matrices is measurable. -/
theorem measurableSet_isHermitian {n : Type*} [Finite n] :
    MeasurableSet {A : Matrix n n ℝ | A.IsHermitian} :=
  (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pointwise limits pass through the functional calculus: if `F k → f` pointwise and each
`A ↦ cfc (F k) A` is measurable, so is `A ↦ cfc f A`. -/
theorem measurable_cfc_of_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ k, Measurable fun A : Matrix n n ℝ => cfc (F k) A)
    (h : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Measurable fun A : Matrix n n ℝ => cfc f A := by
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun A => ?_)
  -- The spectrum is finite, so pointwise convergence is uniform on it.
  have hu : TendstoUniformlyOn F f atTop (spectrum ℝ A) :=
    Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      (eventually_all_finite Matrix.finite_real_spectrum).2 fun t _ =>
        (Metric.tendsto_nhds.1 (h t) ε hε).mono fun k hk => by rwa [dist_comm]
  exact tendsto_cfc_fun hu (Eventually.of_forall fun k =>
    Matrix.finite_real_spectrum.continuousOn _)

/-- For a polynomial `p`, `cfc p A = p (A)` on the symmetric matrices and `0` elsewhere. -/
private theorem measurable_cfc_polynomial (p : Polynomial ℝ) :
    Measurable fun A : Matrix n n ℝ => cfc (fun t => p.eval t) A := by
  classical
  have h : (fun A : Matrix n n ℝ => cfc (fun t => p.eval t) A) =
      {A | A.IsHermitian}.piecewise (fun A => Polynomial.aeval A p) 0 := by
    funext A
    by_cases hA : A.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hA, cfc_polynomial p A hA.isSelfAdjoint]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hA, cfc_apply_of_not_predicate (p := IsSelfAdjoint) A hA,
        Pi.zero_apply]
  rw [h]
  exact (Polynomial.continuous_aeval p).measurable.piecewise measurableSet_isHermitian
    measurable_const

/-- `A ↦ cfc f A` is measurable for a continuous `f`. -/
theorem measurable_cfc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun A : Matrix n n ℝ => cfc f A := by
  -- Weierstrass: polynomials `p k` within `1 / (k + 1)` of `f` on `[-k, k]`; they converge to
  -- `f` pointwise on `ℝ`.
  have hp (k : ℕ) : ∃ p : Polynomial ℝ, ∀ t ∈ Set.Icc (-(k : ℝ)) k,
      |p.eval t - f t| < 1 / ((k : ℝ) + 1) :=
    exists_polynomial_near_of_continuousOn _ _ f hf.continuousOn _ (by positivity)
  choose p hp using hp
  refine measurable_cfc_of_tendsto (F := fun k t => (p k).eval t)
    (fun k => measurable_cfc_polynomial (p k)) fun t => ?_
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun k => dist_nonneg)
    ?_ tendsto_one_div_add_atTop_nhds_zero_nat)
  filter_upwards [eventually_ge_atTop ⌈|t|⌉₊] with k hk
  have hk := Nat.ceil_le.1 hk
  exact (hp k t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).le

/-- `A ↦ cfc f A` is measurable when `f` is a pointwise limit of continuous functions. -/
theorem measurable_cfc_of_tendsto_continuous {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ k, Continuous (F k)) (h : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Measurable fun A : Matrix n n ℝ => cfc f A :=
  measurable_cfc_of_tendsto (fun k => measurable_cfc_of_continuous (hF k)) h

theorem measurable_spectralProj_Icc (a b : ℝ) :
    Measurable fun A : Matrix n n ℝ => spectralProj A (Set.Icc a b) := by
  -- `d t = (a - t)⁺ + (t - b)⁺` vanishes exactly on `[a, b]`, and `(1 - k d)⁺ → 1_{[a, b]}`.
  let d : ℝ → ℝ := fun t => max (a - t) 0 + max (t - b) 0
  refine measurable_cfc_of_tendsto_continuous (F := fun k t => max 0 (1 - k * d t))
    (fun k => by fun_prop) fun t => tendsto_const_nhds.congr' ?_
  by_cases ht : t ∈ Set.Icc a b
  · have hd : d t = 0 := by simp [d, ht.1, ht.2]
    filter_upwards with k
    simp [hd, ht]
  · have hd : 0 < d t := by
      rcases not_and_or.1 ht with h | h
      · exact add_pos_of_pos_of_nonneg (lt_max_of_lt_left (by linarith [not_le.1 h]))
          (le_max_right _ _)
      · exact add_pos_of_nonneg_of_pos (le_max_right _ _)
          (lt_max_of_lt_left (by linarith [not_le.1 h]))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / d t)
    filter_upwards [eventually_ge_atTop N] with k hk
    have : 1 < k * d t := by
      rw [div_lt_iff₀ hd] at hN
      nlinarith [(Nat.cast_le (α := ℝ)).2 hk]
    rw [Set.indicator_of_notMem ht, max_eq_left (by linarith)]

theorem measurable_spectralProj_Ioi (a : ℝ) :
    Measurable fun A : Matrix n n ℝ => spectralProj A (Set.Ioi a) := by
  -- `min 1 (k (t - a))⁺ → 1_{(a, ∞)}`.
  refine measurable_cfc_of_tendsto_continuous (F := fun k t => min 1 (max 0 (k * (t - a))))
    (fun k => by fun_prop) fun t => tendsto_const_nhds.congr' ?_
  by_cases ht : a < t
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (t - a))
    filter_upwards [eventually_ge_atTop N] with k hk
    have : 1 < k * (t - a) := by
      rw [div_lt_iff₀ (sub_pos.2 ht)] at hN
      nlinarith [(Nat.cast_le (α := ℝ)).2 hk]
    rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht), Pi.one_apply,
      min_eq_left (le_max_of_le_right this.le)]
  · filter_upwards with k
    have : (k : ℝ) * (t - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg (by linarith [not_lt.1 ht])
    rw [Set.indicator_of_notMem ht, max_eq_left this, min_eq_right zero_le_one]

/-- The `i`-th eigenvalue of a symmetric matrix (in the order of `Matrix.IsHermitian.eigenvalues`),
extended by `0` to the other matrices. -/
noncomputable def hermitianEigenvalue (i : n) (A : Matrix n n ℝ) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues i else 0

theorem hermitianEigenvalue_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hermitianEigenvalue i A = hA.eigenvalues i := by
  simp only [hermitianEigenvalue, hA, ↓reduceDIte]

omit [Fintype n] [DecidableEq n] in
/-- For an antitone `g` on `Fin N`, `t < g j` iff `j < #{l | t < g l}`: the set
`{l | t < g l}` is an initial segment. -/
private theorem lt_iff_lt_card_filter_of_antitone {N : ℕ} {g : Fin N → ℝ} (hg : Antitone g)
    (t : ℝ) (j : Fin N) : t < g j ↔ (j : ℕ) < (Finset.univ.filter fun l => t < g l).card := by
  constructor
  · intro h
    have := Finset.card_le_card fun l (hl : l ∈ Finset.Iic j) =>
      Finset.mem_filter.2 ⟨Finset.mem_univ l, h.trans_le (hg (Finset.mem_Iic.1 hl))⟩
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra h'
    have := Finset.card_le_card fun l (hl : l ∈ Finset.univ.filter fun l => t < g l) =>
      Finset.mem_Iio.2 (lt_of_not_ge fun hjl =>
        (not_lt.2 ((hg hjl).trans (not_lt.1 h'))) (Finset.mem_filter.1 hl).2)
    rw [Fin.card_Iio] at this
    omega

theorem measurable_hermitianEigenvalue (i : n) :
    Measurable (hermitianEigenvalue (n := n) i) := by
  classical
  -- `λ_i (A) = λ₀_j (A)` for a fixed index `j`, with `λ₀` antitone; so `t < λ_i (A)` iff
  -- `j < #{l | t < λ_l (A)} = tr 1_{(t, ∞)} (A)`.
  let j := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
  refine measurable_of_Ioi fun t => ?_
  have hset : hermitianEigenvalue i ⁻¹' Set.Ioi t =
      {A | A.IsHermitian} ∩ {A | ((j : ℕ) : ℝ) < (spectralProj A (Set.Ioi t)).trace} ∪
        {A | A.IsHermitian}ᶜ ∩ {_A | t < 0} := by
    ext A
    by_cases hA : A.IsHermitian
    · have hcard : (Finset.univ.filter fun i' => t < hA.eigenvalues i').card =
          (Finset.univ.filter fun l => t < hA.eigenvalues₀ l).card :=
        Finset.card_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm fun i' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
      simp only [Set.mem_preimage, Set.mem_Ioi, hermitianEigenvalue_of_isHermitian hA,
        Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, hA, true_and, Set.mem_compl_iff,
        not_true_eq_false, false_and, or_false, trace_spectralProj hA, hcard, Nat.cast_lt]
      exact lt_iff_lt_card_filter_of_antitone hA.eigenvalues₀_antitone t j
    · simp only [Set.mem_preimage, Set.mem_Ioi, hermitianEigenvalue, hA, ↓reduceDIte,
        Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, false_and, Set.mem_compl_iff,
        not_false_eq_true, true_and, false_or]
  rw [hset]
  exact (measurableSet_isHermitian.inter (measurableSet_lt measurable_const
    (continuous_id.matrix_trace.measurable.comp (measurable_spectralProj_Ioi t)))).union
    (measurableSet_isHermitian.compl.inter (MeasurableSet.const _))

variable {m : Type*} [Fintype m]

theorem measurable_singularValue (i : n) :
    Measurable fun A : Matrix m n ℝ => singularValue A i := by
  -- `s_i (A) = √λ_i (Aᴴ A)`.
  have h : (fun A : Matrix m n ℝ => singularValue A i) =
      fun A => √(hermitianEigenvalue i (Aᴴ * A)) := by
    funext A
    rw [hermitianEigenvalue_of_isHermitian (Matrix.isHermitian_conjTranspose_mul_self A),
      singularValue]
  rw [h]
  exact Real.continuous_sqrt.measurable.comp ((measurable_hermitianEigenvalue i).comp
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable)

theorem measurable_schattenNorm (q : ℝ≥0∞) :
    Measurable fun A : Matrix m n ℝ => schattenNorm q A := by
  by_cases hq : q = ⊤
  · simp only [schattenNorm, hq, ite_true]
    exact Measurable.iSup fun i => measurable_singularValue i
  · simp only [schattenNorm, hq, ite_false]
    exact (Real.continuous_rpow_const (by positivity)).measurable.comp (Finset.measurable_sum _
      fun i _ => (Real.continuous_rpow_const ENNReal.toReal_nonneg).measurable.comp
        (measurable_singularValue i))

/-- The counting function `#{i : s_i (A) > s}` is measurable jointly in the level and the
matrix. -/
theorem measurable_countAbove_uncurry :
    Measurable fun p : ℝ × Matrix m n ℝ => (countAbove p.1 p.2 : ℝ) := by
  -- `countAbove s A = Σ_i 1{s < s_i (A)}`.
  simp only [countAbove, Finset.natCast_card_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_lt measurable_fst ((measurable_singularValue i).comp measurable_snd))
    measurable_const measurable_const

theorem measurable_countAbove (s : ℝ) :
    Measurable fun A : Matrix m n ℝ => (countAbove s A : ℝ) := by
  simp only [countAbove, Finset.natCast_card_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_lt measurable_const (measurable_singularValue i)) measurable_const
    measurable_const

end BanachProbability
