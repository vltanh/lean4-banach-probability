module

public import BanachProbability.Noncommutative.CondExp
public import Mathlib.Probability.Process.Filtration

/-!
# Martingale transforms on `L^∞ (Ω) ⊗ M_n`

For a filtration `ℱ` of a probability space and `x : Ω → M_n (ℝ)`, the martingale
`x_k = E_k x = 𝔼 [x | ℱ_k] ⊗ Id` has the differences `d_k x = E_{k+1} x − E_k x`, and its transform
by multipliers `c_k` is
`T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` (`ncTransform`), the source's
`x_1 + Σ_{k=2}^N ξ_{k−1} dx_k` (N. Randrianantoanina, *Non-commutative martingale transforms*,
J. Funct. Anal. 194 (2002), Theorem 3.1, with its `x_1, …, x_N` our `E_0 x, …, E_N x`).

The multipliers are scalar: `c_k : Ω → ℝ` is `ℱ_k`-measurable with `|c_k| ≤ 1`. In
`N = L^∞ (Ω) ⊗ M_n` an element commutes with `N_{k+1} = L^∞ (Ω, ℱ_{k+1}) ⊗ M_n` exactly when it
lies in `L^∞ (Ω) ⊗ 1`, so these are the multipliers of the source's Theorem 3.1 (its hypothesis
(i) that `ξ_{k−1}` commutes with `N_k`, and (ii) `‖ξ‖_∞ ≤ 1`), for real matrices.

Facts: `T_c x` is `ℱ_N`-measurable and in `L^p` with `x` (`MatrixMemLp.ncTransform`), `T_c` is
additive a.e. (`ncTransform_add`), it is a contraction of `L² (τ)` (`matrixTrace_ncTransform_le`,
by the orthogonality of the martingale differences, entrywise), and it is self-adjoint for the
trace pairing `τ (x y)` (`matrixTrace_ncTransform_mul`), since
`τ (T_c x · y) = τ (E_0 x E_0 y) + Σ_k τ (c_k d_k x d_k y)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : MeasureTheory.Filtration ℕ mΩ}
  {n : Type*}

/-- The martingale transform `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)`. -/
noncomputable def ncTransform (ℱ : MeasureTheory.Filtration ℕ mΩ) (μ : Measure Ω)
    (c : ℕ → Ω → ℝ) (N : ℕ) (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω => matrixCondExp (ℱ 0) μ x ω +
    ∑ k ∈ Finset.range N, c k ω • (matrixCondExp (ℱ (k + 1)) μ x ω - matrixCondExp (ℱ k) μ x ω)

variable {c : ℕ → Ω → ℝ} {N : ℕ}

/-! ### Entrywise description, measurability, `L^p` and linearity -/

/-- Since the multipliers are scalar, `T_c` acts entrywise:
`(T_c x)_{ij} = E_0 x_{ij} + Σ_k c_k (E_{k+1} x_{ij} − E_k x_{ij})`. -/
private theorem ncTransform_apply (x : Ω → Matrix n n ℝ) (ω : Ω) (i j : n) :
    ncTransform ℱ μ c N x ω i j = μ[fun ω' => x ω' i j | ℱ 0] ω +
      ∑ k ∈ Finset.range N,
        c k ω * (μ[fun ω' => x ω' i j | ℱ (k + 1)] ω - μ[fun ω' => x ω' i j | ℱ k] ω) := by
  simp [ncTransform, Matrix.sum_apply]

/-- A bounded measurable multiplier is in `L^∞`. -/
private theorem memLp_top_multiplier (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) (k : ℕ) : MemLp (c k) ∞ μ :=
  memLp_top_of_bound ((hc k).mono (ℱ.le k)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hc1 k ω)

theorem measurable_ncTransform (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (x : Ω → Matrix n n ℝ) :
    Measurable[ℱ N] (ncTransform ℱ μ c N x) := by
  -- `E_j x` is `ℱ_j`-measurable and `c_k` is `ℱ_k`-measurable, all `ℱ_N`-measurable for `j ≤ N`.
  have hE : ∀ {j} (i i' : n), j ≤ N → Measurable[ℱ N] (μ[fun ω' => x ω' i i' | ℱ j]) :=
    fun _ _ hj => stronglyMeasurable_condExp.measurable.mono (ℱ.mono hj) le_rfl
  refine @Measurable.of_eval_matrix n n ℝ _ Ω (ℱ N) _ fun i j => ?_
  simp_rw [ncTransform_apply]
  refine (hE i j (Nat.zero_le N)).add (Finset.measurable_sum _ fun k hk => ?_)
  have hk : k + 1 ≤ N := Finset.mem_range.1 hk
  exact ((hc k).measurable.mono (ℱ.mono (by omega)) le_rfl).mul
    ((hE i j hk).sub (hE i j (by omega)))

theorem MatrixMemLp.ncTransform [IsFiniteMeasure μ] (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hp : 1 ≤ p) : MatrixMemLp (ncTransform ℱ μ c N x) p μ := by
  intro i j
  simp_rw [ncTransform_apply]
  exact ((hx i j).condExp hp).add (memLp_finsetSum _ fun k _ =>
    (memLp_top_multiplier hc hc1 k).mul (((hx i j).condExp hp).sub ((hx i j).condExp hp)))

theorem ncTransform_add [Finite n] {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    ncTransform ℱ μ c N (x + y) =ᵐ[μ] ncTransform ℱ μ c N x + ncTransform ℱ μ c N y := by
  have h : ∀ᵐ ω ∂μ, ∀ k (i j : n), μ[fun ω' => x ω' i j + y ω' i j | ℱ k] ω =
      μ[fun ω' => x ω' i j | ℱ k] ω + μ[fun ω' => y ω' i j | ℱ k] ω := by
    simp only [ae_all_iff]
    exact fun k i j => condExp_add (memLp_one_iff_integrable.1 (hx i j))
      (memLp_one_iff_integrable.1 (hy i j)) _
  filter_upwards [h] with ω hω
  ext i j
  simp only [Pi.add_apply, Matrix.add_apply, ncTransform_apply, hω]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem ncTransform_sub [Finite n] {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    ncTransform ℱ μ c N (x - y) =ᵐ[μ] ncTransform ℱ μ c N x - ncTransform ℱ μ c N y := by
  have h : ∀ᵐ ω ∂μ, ∀ k (i j : n), μ[fun ω' => x ω' i j - y ω' i j | ℱ k] ω =
      μ[fun ω' => x ω' i j | ℱ k] ω - μ[fun ω' => y ω' i j | ℱ k] ω := by
    simp only [ae_all_iff]
    exact fun k i j => condExp_sub (memLp_one_iff_integrable.1 (hx i j))
      (memLp_one_iff_integrable.1 (hy i j)) _
  filter_upwards [h] with ω hω
  ext i j
  simp only [Pi.sub_apply, Matrix.sub_apply, ncTransform_apply, hω]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem ncTransform_neg [Finite n] (x : Ω → Matrix n n ℝ) :
    ncTransform ℱ μ c N (-x) =ᵐ[μ] -ncTransform ℱ μ c N x := by
  have h : ∀ᵐ ω ∂μ, ∀ k (i j : n), μ[fun ω' => -x ω' i j | ℱ k] ω =
      -μ[fun ω' => x ω' i j | ℱ k] ω := by
    simp only [ae_all_iff]
    exact fun k i j => condExp_neg _ _
  filter_upwards [h] with ω hω
  ext i j
  simp only [Pi.neg_apply, Matrix.neg_apply, ncTransform_apply, hω]
  simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

theorem ncTransform_smul [Finite n] (a : ℝ) (x : Ω → Matrix n n ℝ) :
    ncTransform ℱ μ c N (a • x) =ᵐ[μ] a • ncTransform ℱ μ c N x := by
  have h : ∀ᵐ ω ∂μ, ∀ k (i j : n), μ[fun ω' => a * x ω' i j | ℱ k] ω =
      a * μ[fun ω' => x ω' i j | ℱ k] ω := by
    simp only [ae_all_iff]
    exact fun k i j => condExp_smul a _ _
  filter_upwards [h] with ω hω
  ext i j
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ncTransform_apply, hω]
  simp only [mul_add, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => by ring)

/-- The transform of an (a.e.) symmetric function is (a.e.) symmetric. -/
theorem isHermitian_ncTransform [Finite n] {x : Ω → Matrix n n ℝ}
    (hx : ∀ᵐ ω ∂μ, (x ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (ncTransform ℱ μ c N x ω).IsHermitian := by
  -- `x_{ji} = x_{ij}` a.e., hence `E_k x_{ji} = E_k x_{ij}` a.e.
  have h : ∀ᵐ ω ∂μ, ∀ k (i j : n),
      μ[fun ω' => x ω' j i | ℱ k] ω = μ[fun ω' => x ω' i j | ℱ k] ω := by
    simp only [ae_all_iff]
    exact fun k i j => condExp_congr_ae (hx.mono fun ω hω => by simpa using hω.apply i j)
  filter_upwards [h] with ω hω
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [star_trivial, ncTransform_apply, hω]

/-! ### The `L²` contraction

Entrywise, `T_c` is the scalar transform `T_c f = E_0 f + Σ_{k<N} c_k d_k f` with
`d_k f = E_{k+1} f − E_k f`, and the martingale differences are orthogonal in `L² (μ)`:
`∫ (T_c f)² = ∫ (E_0 f)² + Σ_k ∫ (c_k d_k f)² ≤ ∫ (E_0 f)² + Σ_k ∫ (d_k f)² = ∫ (E_N f)²`. -/

section L2

/-- The scalar martingale transform `T_c f = E_0 f + Σ_{k<N} c_k (E_{k+1} f − E_k f)`. -/
private noncomputable def scalarTransform (ℱ : MeasureTheory.Filtration ℕ mΩ) (μ : Measure Ω)
    (c : ℕ → Ω → ℝ) (N : ℕ) (f : Ω → ℝ) : Ω → ℝ :=
  fun ω => μ[f | ℱ 0] ω + ∑ k ∈ Finset.range N, c k ω * (μ[f | ℱ (k + 1)] ω - μ[f | ℱ k] ω)

/-- With the multipliers `c_k = 1` the transform telescopes to `E_N f`. -/
private theorem scalarTransform_one (f : Ω → ℝ) (N : ℕ) :
    scalarTransform ℱ μ (fun _ _ => 1) N f = μ[f | ℱ N] := by
  funext ω
  simp only [scalarTransform, one_mul]
  rw [Finset.sum_range_sub (fun k => μ[f | ℱ k] ω)]
  ring

private theorem measurable_scalarTransform (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (f : Ω → ℝ) (N : ℕ) : Measurable[ℱ N] (scalarTransform ℱ μ c N f) := by
  have hE : ∀ {j}, j ≤ N → Measurable[ℱ N] (μ[f | ℱ j]) :=
    fun hj => stronglyMeasurable_condExp.measurable.mono (ℱ.mono hj) le_rfl
  refine (hE (Nat.zero_le N)).add (Finset.measurable_sum _ fun k hk => ?_)
  have hk : k + 1 ≤ N := Finset.mem_range.1 hk
  exact ((hc k).measurable.mono (ℱ.mono (by omega)) le_rfl).mul ((hE hk).sub (hE (by omega)))

private theorem memLp_mul_condExp_sub (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {f : Ω → ℝ} (hf2 : MemLp f 2 μ) (k : ℕ) :
    MemLp (fun ω => c k ω * (μ[f | ℱ (k + 1)] ω - μ[f | ℱ k] ω)) 2 μ :=
  (memLp_top_multiplier hc hc1 k).mul ((hf2.condExp one_le_two).sub (hf2.condExp one_le_two))

private theorem memLp_scalarTransform (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {f : Ω → ℝ} (hf2 : MemLp f 2 μ) (N : ℕ) :
    MemLp (scalarTransform ℱ μ c N f) 2 μ :=
  (hf2.condExp one_le_two).add (memLp_finsetSum _ fun k _ => memLp_mul_condExp_sub hc hc1 hf2 k)

variable [IsFiniteMeasure μ]

/-- The pull-out `∫ g E_m f = ∫ E_m (g f) = ∫ g f` for an `m`-measurable `g ∈ L²` and
`f ∈ L²`. -/
private theorem integral_mul_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) (hg2 : MemLp g 2 μ) (hf2 : MemLp f 2 μ) :
    ∫ ω, g ω * μ[f | m] ω ∂μ = ∫ ω, g ω * f ω ∂μ :=
  calc ∫ ω, g ω * μ[f | m] ω ∂μ = ∫ ω, μ[g * f | m] ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg (hg2.integrable_mul hf2)
          (hf2.integrable one_le_two)).symm
    _ = ∫ ω, g ω * f ω ∂μ := integral_condExp hm

/-- Orthogonality of the martingale differences: `∫ g (E_{k+1} f − E_k f) = 0` for an
`ℱ_k`-measurable `g ∈ L²` and `f ∈ L²`. -/
private theorem integral_mul_condExp_succ_sub {k : ℕ} {f g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ k] g) (hg2 : MemLp g 2 μ) (hf2 : MemLp f 2 μ) :
    ∫ ω, g ω * (μ[f | ℱ (k + 1)] ω - μ[f | ℱ k] ω) ∂μ = 0 := by
  have h1 : Integrable (fun ω => g ω * μ[f | ℱ (k + 1)] ω) μ :=
    hg2.integrable_mul (hf2.condExp one_le_two)
  have h2 : Integrable (fun ω => g ω * μ[f | ℱ k] ω) μ :=
    hg2.integrable_mul (hf2.condExp one_le_two)
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, integral_mul_condExp (ℱ.le _) (hg.mono (ℱ.mono k.le_succ)) hg2 hf2,
    integral_mul_condExp (ℱ.le k) hg hg2 hf2, sub_self]

/-- `∫ (T_c f)² = ∫ (E_0 f)² + Σ_{k<N} ∫ (c_k d_k f)²`: the cross terms vanish, since
`T_c f` is the sum of orthogonal martingale differences (by induction on `N`: `T_N f · c_N` is
`ℱ_N`-measurable, hence orthogonal to `d_N f`). -/
private theorem integral_sq_scalarTransform (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {f : Ω → ℝ} (hf2 : MemLp f 2 μ) (N : ℕ) :
    ∫ ω, scalarTransform ℱ μ c N f ω ^ 2 ∂μ = ∫ ω, μ[f | ℱ 0] ω ^ 2 ∂μ +
      ∑ k ∈ Finset.range N, ∫ ω, (c k ω * (μ[f | ℱ (k + 1)] ω - μ[f | ℱ k] ω)) ^ 2 ∂μ := by
  induction N with
  | zero => simp [scalarTransform]
  | succ N ih =>
    set T := scalarTransform ℱ μ c N f with hT
    set d : Ω → ℝ := fun ω => c N ω * (μ[f | ℱ (N + 1)] ω - μ[f | ℱ N] ω) with hd
    have hT1 : scalarTransform ℱ μ c (N + 1) f = fun ω => T ω + d ω := by
      funext ω
      simp only [hT, hd, scalarTransform, Finset.sum_range_succ, add_assoc]
    have hT2 : MemLp T 2 μ := memLp_scalarTransform hc hc1 hf2 N
    have hd2 : MemLp d 2 μ := memLp_mul_condExp_sub hc hc1 hf2 N
    -- the cross term vanishes: `2 T_N f · c_N` is `ℱ_N`-measurable
    have hcross : ∫ ω, 2 * T ω * d ω ∂μ = 0 := by
      have hg : StronglyMeasurable[ℱ N] (fun ω => 2 * T ω * c N ω) :=
        ((measurable_const.mul (measurable_scalarTransform hc f N)).mul
          (hc N).measurable).stronglyMeasurable
      have hg2 : MemLp (fun ω => 2 * T ω * c N ω) 2 μ :=
        (hT2.const_mul 2).mul (memLp_top_multiplier hc hc1 N)
      simpa only [hd, mul_assoc] using integral_mul_condExp_succ_sub hg hg2 hf2
    have i1 : Integrable (fun ω => T ω ^ 2) μ := hT2.integrable_sq
    have i2 : Integrable (fun ω => 2 * T ω * d ω) μ := (hT2.const_mul 2).integrable_mul hd2
    have i3 : Integrable (fun ω => d ω ^ 2) μ := hd2.integrable_sq
    have i12 : Integrable (fun ω => T ω ^ 2 + 2 * T ω * d ω) μ := i1.add i2
    rw [hT1, Finset.sum_range_succ, ← add_assoc, ← ih]
    simp_rw [add_sq]
    rw [integral_add i12 i3, integral_add i1 i2, hcross, add_zero]

/-- The scalar `L²` contraction `∫ (T_c f)² ≤ ∫ f²` for an `ℱ_N`-measurable `f ∈ L²`. -/
private theorem integral_sq_scalarTransform_le (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {f : Ω → ℝ} (hf : StronglyMeasurable[ℱ N] f) (hf2 : MemLp f 2 μ) :
    ∫ ω, scalarTransform ℱ μ c N f ω ^ 2 ∂μ ≤ ∫ ω, f ω ^ 2 ∂μ := by
  -- with `c = 1`: `∫ (E_N f)² = ∫ (E_0 f)² + Σ_k ∫ (d_k f)²`, and `E_N f = f`
  have h1 := integral_sq_scalarTransform (ℱ := ℱ) (c := fun _ _ => 1)
    (fun _ => stronglyMeasurable_const) (fun _ _ => by simp) hf2 N
  rw [scalarTransform_one, condExp_of_stronglyMeasurable (ℱ.le N) hf (hf2.integrable one_le_two)]
    at h1
  rw [integral_sq_scalarTransform hc hc1 hf2 N, h1]
  refine add_le_add le_rfl (Finset.sum_le_sum fun k _ => integral_mono
    (memLp_mul_condExp_sub hc hc1 hf2 k).integrable_sq
    (memLp_mul_condExp_sub (c := fun _ _ => 1) (fun _ => stronglyMeasurable_const)
      (fun _ _ => by simp) hf2 k).integrable_sq fun ω => ?_)
  have hc2 : c k ω ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hc1 k ω)
  simp only [one_mul, mul_pow]
  nlinarith [sq_nonneg (μ[f | ℱ (k + 1)] ω - μ[f | ℱ k] ω)]

end L2

/-- A transform by predictable multipliers with `|c_k| ≤ 1` is a contraction of `L² (τ)`:
`τ ((T_c x)ᵀ T_c x) ≤ τ (xᵀ x)` for `ℱ_N`-measurable `x`. -/
theorem matrixTrace_ncTransform_le [Fintype n] [IsFiniteMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1)
    {x : Ω → Matrix n n ℝ} (hx : Measurable[ℱ N] x) (hx2 : MatrixMemLp x 2 μ) :
    matrixTrace μ (fun ω => (ncTransform ℱ μ c N x ω)ᵀ * ncTransform ℱ μ c N x ω) ≤
      matrixTrace μ (fun ω => (x ω)ᵀ * x ω) := by
  -- `tr (Aᵀ A) = Σ_{ij} A_{ji}²`, and `(T_c x)_{ji} = T_c (x_{ji})`
  have htr (A : Matrix n n ℝ) : (Aᵀ * A).trace = ∑ i, ∑ j, A j i ^ 2 := by
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have hent (ω : Ω) (i j : n) : ncTransform ℱ μ c N x ω i j =
      scalarTransform ℱ μ c N (fun ω' => x ω' i j) ω :=
    ncTransform_apply x ω i j
  have hT2 (i j : n) := memLp_scalarTransform hc hc1 (hx2 i j) N
  unfold matrixTrace
  simp_rw [htr, hent]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hT2 j i).integrable_sq,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hx2 j i).integrable_sq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hT2 j i).integrable_sq,
    integral_finsetSum _ fun j _ => (hx2 j i).integrable_sq]
  exact Finset.sum_le_sum fun j _ => integral_sq_scalarTransform_le hc hc1
    (@Measurable.eval_matrix n n ℝ _ Ω (ℱ N) j i x hx).stronglyMeasurable (hx2 j i)

/-! ### Self-adjointness for the trace pairing -/

section SelfAdjoint

/-- The martingale difference `d_k x = E_{k+1} x − E_k x`. -/
private noncomputable def mdiff (ℱ : MeasureTheory.Filtration ℕ mΩ) (μ : Measure Ω) (k : ℕ)
    (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  matrixCondExp (ℱ (k + 1)) μ x - matrixCondExp (ℱ k) μ x

variable [Fintype n] [IsFiniteMeasure μ]

/-- Orthogonality to a martingale difference: `τ (a · d_k x) = 0` for an `ℱ_k`-measurable
`a ∈ L^q` and `x ∈ L^p`, `1/p + 1/q = 1`: `τ (a d_k x) = τ (a E_k (d_k x))` and
`E_k (d_k x) = E_k E_{k+1} x − E_k E_k x = 0` (tower property). -/
private theorem matrixTrace_mul_mdiff {p q : ℝ≥0∞} [p.HolderConjugate q] {k : ℕ}
    {a x : Ω → Matrix n n ℝ} (ha : Measurable[ℱ k] a) (ha' : MatrixMemLp a q μ)
    (hx : MatrixMemLp x p μ) : matrixTrace μ (fun ω => a ω * mdiff ℱ μ k x ω) = 0 := by
  classical
  have hp := ENNReal.HolderConjugate.one_le p q
  have hx1 : MatrixMemLp x 1 μ := hx.mono_exponent hp
  have hd : MatrixMemLp (mdiff ℱ μ k x) p μ := (hx.matrixCondExp hp).sub (hx.matrixCondExp hp)
  have hE0 : matrixCondExp (ℱ k) μ (mdiff ℱ μ k x) =ᵐ[μ] 0 := by
    filter_upwards [matrixCondExp_sub (m := ℱ k)
        (MatrixMemLp.matrixCondExp (m := ℱ (k + 1)) hx1 le_rfl)
        (MatrixMemLp.matrixCondExp (m := ℱ k) hx1 le_rfl),
      matrixCondExp_matrixCondExp_of_le (μ := μ) (ℱ.mono k.le_succ) (ℱ.le (k + 1)) x,
      matrixCondExp_matrixCondExp_of_le (μ := μ) le_rfl (ℱ.le k) x] with ω h1 h2 h3
    simp only [mdiff, h1, Pi.sub_apply, h2, h3, sub_self, Pi.zero_apply]
  rw [← matrixTrace_mul_matrixCondExp (ℱ.le k) ha ha' hd,
    matrixTrace_congr_ae (y := fun _ => 0) ?_]
  · simp [matrixTrace]
  · filter_upwards [hE0] with ω hω
    rw [hω, Pi.zero_apply, Matrix.mul_zero]

/-- The trace pairing with a transform:
`τ (T_c x · y) = τ (E_0 x E_0 y) + Σ_k τ (c_k d_k x d_k y)`, by the orthogonality of the
martingale differences. -/
private theorem matrixTrace_ncTransform_mul_eq (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {p q : ℝ≥0∞} [p.HolderConjugate q] {x y : Ω → Matrix n n ℝ}
    (hx : MatrixMemLp x p μ) (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => ncTransform ℱ μ c N x ω * y ω) =
      matrixTrace μ (fun ω => matrixCondExp (ℱ 0) μ x ω * matrixCondExp (ℱ 0) μ y ω) +
        ∑ k ∈ Finset.range N,
          matrixTrace μ (fun ω => c k ω • (mdiff ℱ μ k x ω * mdiff ℱ μ k y ω)) := by
  classical
  have hp := ENNReal.HolderConjugate.one_le p q
  have hq := ENNReal.HolderConjugate.one_le q p
  have hEx (k : ℕ) : MatrixMemLp (matrixCondExp (ℱ k) μ x) p μ := hx.matrixCondExp hp
  have hEy (k : ℕ) : MatrixMemLp (matrixCondExp (ℱ k) μ y) q μ := hy.matrixCondExp hq
  have hcdx (k : ℕ) : MatrixMemLp (fun ω => c k ω • mdiff ℱ μ k x ω) p μ :=
    MatrixMemLp.smul (memLp_top_multiplier hc hc1 k) ((hEx (k + 1)).sub (hEx k))
  have hcEy (k : ℕ) : MatrixMemLp (fun ω => c k ω • matrixCondExp (ℱ k) μ y ω) q μ :=
    MatrixMemLp.smul (memLp_top_multiplier hc hc1 k) (hEy k)
  -- `T_c x · y = E_0 x · y + Σ_k (c_k d_k x) · y`
  have e1 : (fun ω => ncTransform ℱ μ c N x ω * y ω) =
      (fun ω => matrixCondExp (ℱ 0) μ x ω * y ω) +
        ∑ k ∈ Finset.range N, fun ω => (c k ω • mdiff ℱ μ k x ω) * y ω := by
    funext ω
    simp [ncTransform, mdiff, add_mul, Finset.sum_mul, Finset.sum_apply]
  rw [e1, matrixTrace_add ((hEx 0).mul hy) (MatrixMemLp.sum _ fun k _ => (hcdx k).mul hy),
    matrixTrace_sum _ fun k _ => (hcdx k).mul hy,
    ← matrixTrace_mul_matrixCondExp (ℱ.le 0) (measurable_matrixCondExp x) (hEx 0) hy]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  -- `c_k d_k x` is `ℱ_{k+1}`-measurable, `c_k E_k y` is `ℱ_k`-measurable
  have hm1 : Measurable[ℱ (k + 1)] fun ω => c k ω • mdiff ℱ μ k x ω :=
    ((hc k).measurable.mono (ℱ.mono k.le_succ) le_rfl).smul ((measurable_matrixCondExp x).sub
      ((measurable_matrixCondExp x).mono (ℱ.mono k.le_succ) le_rfl))
  have hm0 : Measurable[ℱ k] fun ω => c k ω • matrixCondExp (ℱ k) μ y ω :=
    (hc k).measurable.smul (measurable_matrixCondExp y)
  -- `τ (c_k d_k x · E_k y) = τ (c_k E_k y · d_k x) = 0`
  have h0 : matrixTrace μ (fun ω => (c k ω • mdiff ℱ μ k x ω) * matrixCondExp (ℱ k) μ y ω) = 0 := by
    rw [matrixTrace_mul_comm]
    have e : (fun ω => matrixCondExp (ℱ k) μ y ω * (c k ω • mdiff ℱ μ k x ω)) =
        fun ω => (c k ω • matrixCondExp (ℱ k) μ y ω) * mdiff ℱ μ k x ω := by
      funext ω
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    exact matrixTrace_mul_mdiff hm0 (hcEy k) hx
  -- `τ (c_k d_k x · y) = τ (c_k d_k x · E_{k+1} y) − τ (c_k d_k x · E_k y) = τ (c_k d_k x · d_k y)`
  rw [← matrixTrace_mul_matrixCondExp (ℱ.le (k + 1)) hm1 (hcdx k) hy, ← sub_zero (matrixTrace μ _),
    ← h0, ← matrixTrace_sub ((hcdx k).mul (hEy (k + 1))) ((hcdx k).mul (hEy k))]
  congr 1
  funext ω
  simp only [Pi.sub_apply, mdiff, Matrix.smul_mul]
  rw [← smul_sub, ← Matrix.mul_sub]

end SelfAdjoint

/-- The transform is self-adjoint for the trace pairing: `τ (T_c x · y) = τ (x · T_c y)` for
`x ∈ L^p`, `y ∈ L^q`, `1/p + 1/q = 1`. -/
theorem matrixTrace_ncTransform_mul [Fintype n] [IsFiniteMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {p q : ℝ≥0∞}
    [p.HolderConjugate q] {x y : Ω → Matrix n n ℝ}
    (hx : MatrixMemLp x p μ) (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => ncTransform ℱ μ c N x ω * y ω) =
      matrixTrace μ (fun ω => x ω * ncTransform ℱ μ c N y ω) := by
  rw [matrixTrace_mul_comm x, matrixTrace_ncTransform_mul_eq hc hc1 hx hy,
    matrixTrace_ncTransform_mul_eq hc hc1 hy hx, matrixTrace_mul_comm (matrixCondExp (ℱ 0) μ x)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold matrixTrace
  simp_rw [Matrix.trace_smul, Matrix.trace_mul_comm (mdiff ℱ μ k x _)]

end BanachProbability
