module

public import BanachProbability.Schatten.Measurable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Matrix-valued functions on a probability space

The von Neumann algebra `N = L^∞ (Ω, μ) ⊗ M_n (ℝ)` of (essentially bounded) matrix-valued
functions on a probability space, with the trace `τ (x) = ∫ tr x dμ` (`matrixTrace`), and, for a
sub-σ-algebra `m`, the conditional expectation `E_m = 𝔼 [· | m] ⊗ Id` onto `L^∞ (Ω, m) ⊗ M_n`,
applied entrywise (`matrixCondExp`; N. Randrianantoanina, *Non-commutative martingale
transforms*, J. Funct. Anal. 194 (2002), proof of Corollary 4.5, where `E_n = 𝔼_n ⊗ Id`). The
noncommutative `L^p (N)` is `L^p (μ; S_p^n)`; `MatrixMemLp x p μ` says that every entry of `x` is
in `L^p (μ)`, equivalently (for measurable `x`) that `ω ↦ ‖x ω‖_{S_q}` is in `L^p (μ)` for any
`q` (`MatrixMemLp.memLp_schattenNorm`, `matrixMemLp_of_memLp_schattenNorm`).

The properties of conditional expectations that the source lists (§2): `E_m` is linear (a.e.),
`E_{m₁} E_{m₂} = E_{m₁}` for `m₁ ≤ m₂` (`matrixCondExp_matrixCondExp_of_le`), it is the identity
on `m`-measurable functions (`matrixCondExp_of_measurable`), it is a bimodule map over the
`m`-measurable bounded functions, `E_m (a x b) = a E_m (x) b` (`matrixCondExp_mul_mul`), it is
trace preserving, `τ ∘ E_m = τ` (`matrixTrace_matrixCondExp`), whence the pull-out
`τ (a E_m (y)) = τ (a y)` for `m`-measurable `a` (`matrixTrace_mul_matrixCondExp`), and it is
positive (`posSemidef_matrixCondExp`) and maps `L^p` to `L^p` (`MatrixMemLp.matrixCondExp`).

All of them are proved entrywise from the scalar conditional expectation `μ[· | m]`; the a.e.
statements combine finitely many entries, so they hold for any `Finite` index type.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- Every entry of the matrix-valued function `x` is in `L^p (μ)`. -/
def MatrixMemLp (x : Ω → Matrix n n ℝ) (p : ℝ≥0∞) (μ : Measure Ω) : Prop :=
  ∀ i j, MemLp (fun ω => x ω i j) p μ

/-- The conditional expectation `E_m = 𝔼 [· | m] ⊗ Id`, applied entrywise. -/
noncomputable def matrixCondExp (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (x : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω => Matrix.of fun i j => (μ[fun ω' => x ω' i j | m]) ω

/-- The trace `τ (x) = ∫ tr x dμ` of `L^∞ (Ω, μ) ⊗ M_n`. -/
noncomputable def matrixTrace {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (x : Ω → Matrix n n ℝ) :
    ℝ :=
  ∫ ω, (x ω).trace ∂μ

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem matrixCondExp_apply (x : Ω → Matrix n n ℝ) (ω : Ω) (i j : n) :
    matrixCondExp m μ x ω i j = (μ[fun ω' => x ω' i j | m]) ω :=
  rfl

omit [Fintype n] [DecidableEq n] in
/-- `Matrix.measurable_iff` for an arbitrary σ-algebra on `Ω`. -/
private theorem cexp_measurable_iff {m' : MeasurableSpace Ω} {x : Ω → Matrix n n ℝ} :
    Measurable[m'] x ↔ ∀ i j, Measurable[m'] fun ω => x ω i j :=
  @Matrix.measurable_iff n n ℝ _ Ω m' x

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- Two matrix-valued functions agree a.e. when their (finitely many) entries do. -/
private theorem cexp_ae_ext {x y : Ω → Matrix n n ℝ}
    (h : ∀ i j, (fun ω => x ω i j) =ᵐ[μ] fun ω => y ω i j) : x =ᵐ[μ] y := by
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (h i)] with ω hω
  exact Matrix.ext hω

omit [Fintype n] [DecidableEq n] in
private theorem cexp_integrable {x : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ) (i j : n) :
    Integrable (fun ω => x ω i j) μ :=
  memLp_one_iff_integrable.1 (hx i j)

/-! ### `L^p` membership -/

section MemLp

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.add {x y : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hy : MatrixMemLp y p μ) : MatrixMemLp (x + y) p μ :=
  fun i j => (hx i j).add (hy i j)

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.sub {x y : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hy : MatrixMemLp y p μ) : MatrixMemLp (x - y) p μ :=
  fun i j => (hx i j).sub (hy i j)

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.neg {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ) :
    MatrixMemLp (-x) p μ :=
  fun i j => (hx i j).neg

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.const_smul {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (c : ℝ) : MatrixMemLp (c • x) p μ :=
  fun i j => (hx i j).const_smul c

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ} {p : ℝ≥0∞}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) p μ) : MatrixMemLp (∑ i ∈ s, x i) p μ := fun i j => by
  simpa only [Finset.sum_apply, Matrix.sum_apply] using memLp_finsetSum s fun k hk => hx k hk i j

omit [Fintype n] [DecidableEq n] in
theorem matrixMemLp_const [IsFiniteMeasure μ] (A : Matrix n n ℝ) (p : ℝ≥0∞) :
    MatrixMemLp (fun _ => A) p μ :=
  fun i j => memLp_const (A i j)

omit [Fintype n] [DecidableEq n] in
/-- `L^p ⊂ L^q` for `q ≤ p` on a finite measure space. -/
theorem MatrixMemLp.mono_exponent [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ} {p q : ℝ≥0∞}
    (hx : MatrixMemLp x p μ) (hqp : q ≤ p) : MatrixMemLp x q μ :=
  fun i j => (hx i j).mono_exponent hqp

omit [Fintype n] [DecidableEq n] in
/-- A measurable matrix-valued function with entries bounded a.e. by `C` is in `L^∞`. -/
theorem MatrixMemLp.of_bound {x : Ω → Matrix n n ℝ} (hx : Measurable x) (C : ℝ)
    (h : ∀ᵐ ω ∂μ, ∀ i j, |x ω i j| ≤ C) : MatrixMemLp x ∞ μ :=
  fun i j => memLp_top_of_bound (cexp_measurable_iff.1 hx i j).aestronglyMeasurable C
    (h.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω i j)

omit [DecidableEq n] in
/-- Hölder: the product of an `L^p` and an `L^q` matrix-valued function is in `L^r`,
`1/r = 1/p + 1/q`. -/
theorem MatrixMemLp.mul {x y : Ω → Matrix n n ℝ} {p q r : ℝ≥0∞} [p.HolderTriple q r]
    (hx : MatrixMemLp x p μ) (hy : MatrixMemLp y q μ) :
    MatrixMemLp (fun ω => x ω * y ω) r μ := fun i j => by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun k _ => (hx i k).mul (hy k j)

omit [Fintype n] [DecidableEq n] in
/-- A real `L^p` function times an `L^q` matrix-valued function is in `L^r`. -/
theorem MatrixMemLp.smul {c : Ω → ℝ} {x : Ω → Matrix n n ℝ} {p q r : ℝ≥0∞} [p.HolderTriple q r]
    (hc : MemLp c p μ) (hx : MatrixMemLp x q μ) : MatrixMemLp (fun ω => c ω • x ω) r μ :=
  fun i j => hc.mul (hx i j)

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem MatrixMemLp.aemeasurable {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ) :
    AEMeasurable x μ :=
  aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j =>
    (hx i j).aestronglyMeasurable.aemeasurable

/-- `‖A‖_{S_q} ≤ ‖A‖_{S_1} ≤ √(#n) ‖A‖_{S_2} ≤ √(#n) Σ_{ij} |A_{ij}|` for `q ≥ 1`. -/
private theorem cexp_schattenNorm_le_sum {q : ℝ≥0∞} (hq : 1 ≤ q) (A : Matrix n n ℝ) :
    schattenNorm q A ≤ (Fintype.card n : ℝ) ^ ((1 : ℝ) / 1 - 1 / 2) * ∑ i, ∑ j, ‖A i j‖ := by
  have h2 : schattenNorm (ENNReal.ofReal 2) A ≤ ∑ i, ∑ j, ‖A i j‖ := by
    refine (pow_le_pow_iff_left₀ (schattenNorm_nonneg _ _) (by positivity) two_ne_zero).1 ?_
    rw [ENNReal.ofReal_ofNat, schattenNorm_two_sq]
    calc ∑ i, ∑ j, A i j ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ i, (∑ j, ‖A i j‖) ^ 2 := Finset.sum_le_sum fun i _ =>
          Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (∑ i, ∑ j, ‖A i j‖) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  calc schattenNorm q A ≤ schattenNorm (ENNReal.ofReal 1) A := by
        rw [ENNReal.ofReal_one]; exact schattenNorm_anti one_ne_zero hq A
    _ ≤ (Fintype.card n : ℝ) ^ ((1 : ℝ) / 1 - 1 / 2) * schattenNorm (ENNReal.ofReal 2) A :=
        schattenNorm_le_card_rpow_mul one_pos one_le_two A
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `|A_{ij}|² ≤ ‖A‖_{S_2}² = Σ_k s_k (A)² ≤ #n ‖A‖_{S_∞}² ≤ #n ‖A‖_{S_q}²`. -/
private theorem cexp_abs_apply_le_schattenNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix n n ℝ)
    (i j : n) : |A i j| ≤ √(Fintype.card n : ℝ) * schattenNorm q A := by
  have hS2 : schattenNorm 2 A ^ 2 = ∑ k, singularValue A k ^ 2 := by
    have h := schattenNorm_rpow two_ne_zero ENNReal.ofNat_ne_top A
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsv : ∀ k, singularValue A k ≤ schattenNorm ⊤ A := fun k => by
    rw [schattenNorm, ite_eq_left rfl]
    exact le_ciSup (Set.finite_range _).bddAbove k
  have hij : A i j ^ 2 ≤ schattenNorm 2 A ^ 2 := by
    rw [schattenNorm_two_sq]
    calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsum : ∑ k, singularValue A k ^ 2 ≤ (Fintype.card n : ℝ) * schattenNorm ⊤ A ^ 2 := by
    calc ∑ k, singularValue A k ^ 2 ≤ ∑ _k : n, schattenNorm ⊤ A ^ 2 :=
          Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (singularValue_nonneg A k) (hsv k) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htop : schattenNorm ⊤ A ≤ schattenNorm q A := schattenNorm_anti hq le_top A
  refine (pow_le_pow_iff_left₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (schattenNorm_nonneg _ _)) two_ne_zero).1 ?_
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc A i j ^ 2 ≤ (Fintype.card n : ℝ) * schattenNorm ⊤ A ^ 2 := hij.trans (hS2 ▸ hsum)
    _ ≤ (Fintype.card n : ℝ) * schattenNorm q A ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (schattenNorm_nonneg _ _) htop 2) (Nat.cast_nonneg _)

/-- `ω ↦ ‖x ω‖_{S_q}` is in `L^p` when the entries are (`q ≥ 1`). -/
theorem MatrixMemLp.memLp_schattenNorm {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) : MemLp (fun ω => schattenNorm q (x ω)) p μ := by
  refine MemLp.of_le
    ((memLp_finsetSum Finset.univ fun i _ =>
      memLp_finsetSum Finset.univ fun j _ => (hx i j).norm).const_mul
      ((Fintype.card n : ℝ) ^ ((1 : ℝ) / 1 - 1 / 2)))
    ((measurable_schattenNorm q).comp_aemeasurable hx.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _), Real.norm_of_nonneg (by positivity)]
  exact cexp_schattenNorm_le_sum hq (x ω)

/-- The entries are in `L^p` when `ω ↦ ‖x ω‖_{S_q}` is (`|A_{ij}| ≤ √(#n) ‖A‖_{S_q}`). -/
theorem matrixMemLp_of_memLp_schattenNorm {x : Ω → Matrix n n ℝ} (hx : AEMeasurable x μ)
    {p q : ℝ≥0∞} (hq : q ≠ 0) (h : MemLp (fun ω => schattenNorm q (x ω)) p μ) :
    MatrixMemLp x p μ := fun i j =>
  MemLp.of_le (h.const_mul √(Fintype.card n : ℝ))
    ((Matrix.measurable_apply (i := i) (j := j)).comp_aemeasurable hx).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (schattenNorm_nonneg _ _))]
      exact cexp_abs_apply_le_schattenNorm hq (x ω) i j)

end MemLp

/-! ### Entry bounds -/

section Bounds

omit [Fintype n] in
/-- The entries of `A` with `0 ⪯ A ⪯ C` are bounded by `C`: `A_{ii} ≤ C`, and the quadratic forms
of `A` on `e_i ± e_j` give `|A_{ij}| ≤ (A_{ii} + A_{jj}) / 2`. -/
theorem abs_apply_le_of_posSemidef {A : Matrix n n ℝ} {C : ℝ} (hA : A.PosSemidef)
    (hAC : (C • (1 : Matrix n n ℝ) - A).PosSemidef) (i j : n) : |A i j| ≤ C := by
  have hdiag : ∀ k, A k k ≤ C := fun k => by
    have h := hAC.diag_nonneg (i := k)
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at h
    linarith
  have hs : A j i = A i j := by simpa using hA.1.apply i j
  have h2 := Matrix.posSemidef_iff_dotProduct_mulVec.1 (hA.submatrix ![i, j])
  have hp := h2.2 ![1, 1]
  have hm := h2.2 ![1, -1]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply, star_trivial] at hp hm
  rw [abs_le]
  constructor <;> nlinarith [hdiag i, hdiag j]

omit [DecidableEq n] in
/-- The entries of an orthogonal projection are bounded by `1`. -/
theorem abs_apply_le_one_of_isProj {P : Matrix n n ℝ} (hP : P * P = P) (hPt : Pᵀ = P) (i j : n) :
    |P i j| ≤ 1 := by
  classical
  have hP' : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hPt, hP] at h
  have h1P : ((1 : ℝ) • (1 : Matrix n n ℝ) - P).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
    have e : (1 - P) * (1 - P) = 1 - P := by simp [sub_mul, mul_sub, hP]
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, hPt, e, ← one_smul ℝ (1 : Matrix n n ℝ)] at h
  exact abs_apply_le_of_posSemidef hP' h1P i j

end Bounds

/-! ### The conditional expectation -/

section CondExp

omit [Fintype n] [DecidableEq n] in
theorem measurable_matrixCondExp (x : Ω → Matrix n n ℝ) : Measurable[m] (matrixCondExp m μ x) :=
  cexp_measurable_iff.2 fun _ _ => stronglyMeasurable_condExp.measurable

omit [Fintype n] [DecidableEq n] in
theorem MatrixMemLp.matrixCondExp {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hp : 1 ≤ p) : MatrixMemLp (matrixCondExp m μ x) p μ :=
  fun i j => (hx i j).condExp hp

omit [Fintype n] [DecidableEq n] in
theorem matrixCondExp_of_measurable (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {x : Ω → Matrix n n ℝ} (hx : Measurable[m] x) (hxi : MatrixMemLp x 1 μ) :
    matrixCondExp m μ x = x := by
  funext ω
  ext i j
  exact congrFun (condExp_of_stronglyMeasurable hm
    (cexp_measurable_iff.1 hx i j).stronglyMeasurable (cexp_integrable hxi i j)) ω

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_congr_ae {x y : Ω → Matrix n n ℝ} (h : x =ᵐ[μ] y) :
    matrixCondExp m μ x =ᵐ[μ] matrixCondExp m μ y :=
  cexp_ae_ext fun i j => condExp_congr_ae (h.mono fun _ hω => congrArg (fun A => A i j) hω)

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_add {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    matrixCondExp m μ (x + y) =ᵐ[μ] matrixCondExp m μ x + matrixCondExp m μ y :=
  cexp_ae_ext fun i j => condExp_add (cexp_integrable hx i j) (cexp_integrable hy i j) m

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_sub {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    matrixCondExp m μ (x - y) =ᵐ[μ] matrixCondExp m μ x - matrixCondExp m μ y :=
  cexp_ae_ext fun i j => condExp_sub (cexp_integrable hx i j) (cexp_integrable hy i j) m

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_neg (x : Ω → Matrix n n ℝ) :
    matrixCondExp m μ (-x) =ᵐ[μ] -matrixCondExp m μ x :=
  cexp_ae_ext fun i j => condExp_neg (fun ω => x ω i j) m

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_smul (c : ℝ) (x : Ω → Matrix n n ℝ) :
    matrixCondExp m μ (c • x) =ᵐ[μ] c • matrixCondExp m μ x :=
  cexp_ae_ext fun i j => condExp_smul c (fun ω => x ω i j) m

omit [Fintype n] [DecidableEq n] in
theorem matrixCondExp_zero : matrixCondExp m μ (0 : Ω → Matrix n n ℝ) = 0 := by
  funext ω
  ext i j
  exact congrFun (condExp_zero (m := m) (μ := μ) (E := ℝ)) ω

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
theorem matrixCondExp_sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) 1 μ) :
    matrixCondExp m μ (∑ i ∈ s, x i) =ᵐ[μ] ∑ i ∈ s, matrixCondExp m μ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, matrixCondExp_zero]
  | insert k s hks ih =>
    have hx' := Finset.forall_of_forall_insert hx
    rw [Finset.sum_insert hks, Finset.sum_insert hks]
    exact (matrixCondExp_add (hx k (Finset.mem_insert_self k s)) (MatrixMemLp.sum s hx')).trans
      (Filter.EventuallyEq.rfl.add (ih hx'))

omit [Fintype n] [DecidableEq n] in
theorem matrixCondExp_const (hm : m ≤ mΩ) [IsFiniteMeasure μ] (A : Matrix n n ℝ) :
    matrixCondExp m μ (fun _ => A) = fun _ => A := by
  funext ω
  ext i j
  rw [matrixCondExp_apply, condExp_const hm]

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- The tower property `E_{m₁} E_{m₂} = E_{m₁}` for `m₁ ≤ m₂`. -/
theorem matrixCondExp_matrixCondExp_of_le {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ mΩ) [SigmaFinite (μ.trim h₂)] (x : Ω → Matrix n n ℝ) :
    matrixCondExp m₁ μ (matrixCondExp m₂ μ x) =ᵐ[μ] matrixCondExp m₁ μ x :=
  cexp_ae_ext fun i j => condExp_condExp_of_le (f := fun ω => x ω i j) h₁₂ h₂

omit [Fintype n] [DecidableEq n] in
/-- The pull-out property for a finite sum: `E_m (Σ_k c_k g_k) = Σ_k c_k E_m (g_k)` for bounded
`m`-measurable `c_k` and integrable `g_k`. -/
private theorem cexp_condExp_sum_mul {ι : Type*} (s : Finset ι) {c g : ι → Ω → ℝ}
    (hc : ∀ k ∈ s, StronglyMeasurable[m] (c k)) (hcb : ∀ k ∈ s, MemLp (c k) ∞ μ)
    (hg : ∀ k ∈ s, Integrable (g k) μ) :
    μ[fun ω => ∑ k ∈ s, c k ω * g k ω | m] =ᵐ[μ] fun ω => ∑ k ∈ s, c k ω * μ[g k | m] ω := by
  have h1 : ∀ k ∈ s, Integrable (c k * g k) μ := fun k hk =>
    (hcb k hk).integrable_mul (memLp_one_iff_integrable.2 (hg k hk))
  have h3 : ∀ k ∈ s, ∀ᵐ ω ∂μ, μ[c k * g k | m] ω = (c k * μ[g k | m]) ω := fun k hk =>
    condExp_mul_of_stronglyMeasurable_left (hc k hk) (h1 k hk) (hg k hk)
  have hfun : (fun ω => ∑ k ∈ s, c k ω * g k ω) = ∑ k ∈ s, c k * g k := by
    ext ω
    simp [Finset.sum_apply]
  rw [hfun]
  filter_upwards [condExp_finsetSum h1 m, (Filter.eventually_all_finset s).2 h3] with ω h2ω h3ω
  rw [h2ω, Finset.sum_apply]
  exact Finset.sum_congr rfl h3ω

omit [DecidableEq n] in
/-- The bimodule property `E_m (a x b) = a E_m (x) b` for bounded `m`-measurable `a`, `b`:
`(a x b)_{ij} = Σ_{l,k} a_{il} b_{kj} x_{lk}`, and the bounded `m`-measurable `a_{il} b_{kj}`
pull out. -/
theorem matrixCondExp_mul_mul {a b x : Ω → Matrix n n ℝ} (ha : Measurable[m] a)
    (hb : Measurable[m] b) (ha' : MatrixMemLp a ∞ μ) (hb' : MatrixMemLp b ∞ μ)
    (hx : MatrixMemLp x 1 μ) :
    matrixCondExp m μ (fun ω => a ω * x ω * b ω) =ᵐ[μ]
      fun ω => a ω * matrixCondExp m μ x ω * b ω := by
  refine cexp_ae_ext fun i j => ?_
  have key := cexp_condExp_sum_mul (m := m) (μ := μ) (Finset.univ : Finset (n × n))
    (c := fun p ω => a ω i p.1 * b ω p.2 j) (g := fun p ω => x ω p.1 p.2)
    (fun p _ => ((cexp_measurable_iff.1 ha i p.1).mul
      (cexp_measurable_iff.1 hb p.2 j)).stronglyMeasurable)
    (fun p _ => (ha' i p.1).mul (hb' p.2 j)) (fun p _ => cexp_integrable hx p.1 p.2)
  have e : ∀ (A X B : Matrix n n ℝ),
      (A * X * B) i j = ∑ p : n × n, A i p.1 * B p.2 j * X p.1 p.2 := fun A X B => by
    simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [matrixCondExp_apply, e]
  exact key

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- `E_m (c x) = c E_m (x)` for a bounded `m`-measurable scalar function `c`. -/
theorem matrixCondExp_smul_left {c : Ω → ℝ} {x : Ω → Matrix n n ℝ} (hc : StronglyMeasurable[m] c)
    (hc' : MemLp c ∞ μ) (hx : MatrixMemLp x 1 μ) :
    matrixCondExp m μ (fun ω => c ω • x ω) =ᵐ[μ] fun ω => c ω • matrixCondExp m μ x ω :=
  cexp_ae_ext fun i j => condExp_mul_of_stronglyMeasurable_left hc
    (hc'.integrable_mul (hx i j)) (cexp_integrable hx i j)

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- `E_m` maps (a.e.) symmetric functions to (a.e.) symmetric functions. -/
theorem isHermitian_matrixCondExp {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (matrixCondExp m μ x ω).IsHermitian := by
  have h : ∀ i j, μ[fun ω => x ω j i | m] =ᵐ[μ] μ[fun ω => x ω i j | m] := fun i j =>
    condExp_congr_ae (hx.mono fun ω hω => by simpa using hω.apply i j)
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (h i)] with ω hω
  exact Matrix.IsHermitian.ext fun i j => by simpa using hω i j

omit [DecidableEq n] in
/-- The quadratic form `vᵀ A v = Σ_{k,l} v_k v_l A_{kl}`. -/
private theorem cexp_dotProduct_mulVec (A : Matrix n n ℝ) (v : n → ℝ) :
    star v ⬝ᵥ (A *ᵥ v) = ∑ p : n × n, v p.1 * v p.2 * A p.1 p.2 := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, Pi.star_apply,
    star_trivial]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- `E_m` is positive: `vᵀ E_m (x) v = E_m (vᵀ x v) ≥ 0` a.e. for each `v` of a countable dense
set, and the quadratic form is continuous in `v`. -/
theorem posSemidef_matrixCondExp {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef)
    (hxi : MatrixMemLp x 1 μ) : ∀ᵐ ω ∂μ, (matrixCondExp m μ x ω).PosSemidef := by
  have := Fintype.ofFinite n
  have hq : ∀ v : n → ℝ, ∀ᵐ ω ∂μ, 0 ≤ star v ⬝ᵥ (matrixCondExp m μ x ω *ᵥ v) := fun v => by
    have key := cexp_condExp_sum_mul (m := m) (μ := μ) (Finset.univ : Finset (n × n))
      (c := fun p _ => v p.1 * v p.2) (g := fun p ω => x ω p.1 p.2)
      (fun p _ => stronglyMeasurable_const) (fun p _ => memLp_top_const _)
      (fun p _ => cexp_integrable hxi p.1 p.2)
    have hnn := condExp_nonneg (m := m) (μ := μ)
      (f := fun ω => ∑ p : n × n, v p.1 * v p.2 * x ω p.1 p.2)
      (hx.mono fun ω hω => by
        simpa only [cexp_dotProduct_mulVec, Pi.zero_apply] using hω.dotProduct_mulVec_nonneg v)
    filter_upwards [key, hnn] with ω h1 h2
    rw [cexp_dotProduct_mulVec]
    simpa only [matrixCondExp_apply, ← h1, Pi.zero_apply] using h2
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (n → ℝ)
  have := hDc.to_subtype
  filter_upwards [ae_all_iff.2 fun v : D => hq v,
    isHermitian_matrixCondExp (m := m) (hx.mono fun ω hω => hω.1)] with ω hω hH
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_
  have hcl : IsClosed {v : n → ℝ | 0 ≤ star v ⬝ᵥ (matrixCondExp m μ x ω *ᵥ v)} := by
    simp only [cexp_dotProduct_mulVec]
    exact isClosed_le continuous_const (continuous_finsetSum _ fun p _ =>
      ((continuous_apply p.1).mul (continuous_apply p.2)).mul continuous_const)
  exact hcl.closure_subset_iff.2 (fun w hw => hω ⟨w, hw⟩) (hDd.closure_eq ▸ Set.mem_univ v)

omit [Fintype n] [DecidableEq n] in
variable [Finite n] in
/-- `E_m` is order preserving. -/
theorem posSemidef_matrixCondExp_sub {x y : Ω → Matrix n n ℝ}
    (h : ∀ᵐ ω ∂μ, (y ω - x ω).PosSemidef) (hx : MatrixMemLp x 1 μ) (hy : MatrixMemLp y 1 μ) :
    ∀ᵐ ω ∂μ, (matrixCondExp m μ y ω - matrixCondExp m μ x ω).PosSemidef := by
  filter_upwards [posSemidef_matrixCondExp (m := m) (x := y - x) h (hy.sub hx),
    matrixCondExp_sub (m := m) hy hx] with ω h1 h2
  rw [h2] at h1
  exact h1

end CondExp

/-! ### The trace -/

section Trace

omit [DecidableEq n] in
private theorem cexp_integrable_trace {x : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ) :
    Integrable (fun ω => (x ω).trace) μ := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact integrable_finsetSum _ fun i _ => cexp_integrable hx i i

omit [DecidableEq n] in
theorem matrixTrace_add {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) : matrixTrace μ (x + y) = matrixTrace μ x + matrixTrace μ y := by
  simp only [matrixTrace, Pi.add_apply, Matrix.trace_add]
  exact integral_add (cexp_integrable_trace hx) (cexp_integrable_trace hy)

omit [DecidableEq n] in
theorem matrixTrace_sub {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) : matrixTrace μ (x - y) = matrixTrace μ x - matrixTrace μ y := by
  simp only [matrixTrace, Pi.sub_apply, Matrix.trace_sub]
  exact integral_sub (cexp_integrable_trace hx) (cexp_integrable_trace hy)

omit [DecidableEq n] in
theorem matrixTrace_sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) 1 μ) :
    matrixTrace μ (∑ i ∈ s, x i) = ∑ i ∈ s, matrixTrace μ (x i) := by
  simp only [matrixTrace, Finset.sum_apply, Matrix.trace_sum]
  exact integral_finsetSum s fun i hi => cexp_integrable_trace (hx i hi)

omit [DecidableEq n] in
theorem matrixTrace_smul (c : ℝ) (x : Ω → Matrix n n ℝ) :
    matrixTrace μ (c • x) = c * matrixTrace μ x := by
  simp only [matrixTrace, Pi.smul_apply, Matrix.trace_smul, smul_eq_mul]
  exact integral_const_mul c _

omit [DecidableEq n] in
theorem matrixTrace_congr_ae {x y : Ω → Matrix n n ℝ} (h : x =ᵐ[μ] y) :
    matrixTrace μ x = matrixTrace μ y :=
  integral_congr_ae (h.mono fun _ hω => congrArg Matrix.trace hω)

omit [DecidableEq n] in
/-- `τ (x y) = τ (y x)`. -/
theorem matrixTrace_mul_comm (x y : Ω → Matrix n n ℝ) :
    matrixTrace μ (fun ω => x ω * y ω) = matrixTrace μ (fun ω => y ω * x ω) := by
  unfold matrixTrace
  congr 1
  funext ω
  exact Matrix.trace_mul_comm _ _

omit [DecidableEq n] in
/-- `τ (x) ≥ 0` for (a.e.) positive semidefinite `x`. -/
theorem matrixTrace_nonneg {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) :
    0 ≤ matrixTrace μ x :=
  integral_nonneg_of_ae (hx.mono fun _ hω => hω.trace_nonneg)

omit [DecidableEq n] in
/-- `τ` is monotone on integrable functions. -/
theorem matrixTrace_mono {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) (h : ∀ᵐ ω ∂μ, (x ω).trace ≤ (y ω).trace) :
    matrixTrace μ x ≤ matrixTrace μ y :=
  integral_mono_ae (cexp_integrable_trace hx) (cexp_integrable_trace hy) h

omit [DecidableEq n] in
/-- `τ ∘ E_m = τ`. -/
theorem matrixTrace_matrixCondExp (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {x : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ) :
    matrixTrace μ (matrixCondExp m μ x) = matrixTrace μ x := by
  simp only [matrixTrace, Matrix.trace, Matrix.diag_apply, matrixCondExp_apply]
  rw [integral_finsetSum _ fun i _ => integrable_condExp (f := fun ω => x ω i i) (m := m),
    integral_finsetSum _ fun i _ => cexp_integrable hx i i]
  exact Finset.sum_congr rfl fun i _ => integral_condExp hm

omit [DecidableEq n] in
/-- The pull-out `τ (a E_m (y)) = τ (a y)` for an `m`-measurable `a ∈ L^p` and `y ∈ L^q`,
`1/p + 1/q = 1` (bimodule property and `τ ∘ E_m = τ`). -/
theorem matrixTrace_mul_matrixCondExp (hm : m ≤ mΩ) [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [p.HolderConjugate q] {a y : Ω → Matrix n n ℝ} (ha : Measurable[m] a) (ha' : MatrixMemLp a p μ)
    (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => a ω * matrixCondExp m μ y ω) = matrixTrace μ (fun ω => a ω * y ω) := by
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  have h1 : ∀ i l, Integrable (fun ω => a ω i l * y ω l i) μ := fun i l =>
    (ha' i l).integrable_mul (hy l i)
  have h2 : ∀ i l, Integrable (fun ω => a ω i l * μ[fun ω => y ω l i | m] ω) μ := fun i l =>
    (ha' i l).integrable_mul ((hy l i).condExp hq)
  -- `∫ a_{il} E_m (y_{li}) = ∫ E_m (a_{il} y_{li}) = ∫ a_{il} y_{li}`
  have h3 : ∀ i l, ∫ ω, a ω i l * μ[fun ω => y ω l i | m] ω ∂μ = ∫ ω, a ω i l * y ω l i ∂μ := by
    intro i l
    rw [← integral_condExp hm (f := fun ω => a ω i l * y ω l i)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
      (cexp_measurable_iff.1 ha i l).stronglyMeasurable (h1 i l) ((hy l i).integrable hq)).symm
  simp only [matrixTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, matrixCondExp_apply]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => h2 i l,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => h1 i l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun l _ => h2 i l, integral_finsetSum _ fun l _ => h1 i l]
  exact Finset.sum_congr rfl fun l _ => h3 i l

omit [DecidableEq n] in
/-- The pull-out `τ (E_m (y) a) = τ (y a)` for an `m`-measurable `a ∈ L^p` and `y ∈ L^q`,
`1/p + 1/q = 1`. -/
theorem matrixTrace_matrixCondExp_mul (hm : m ≤ mΩ) [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [p.HolderConjugate q] {a y : Ω → Matrix n n ℝ} (ha : Measurable[m] a) (ha' : MatrixMemLp a p μ)
    (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => matrixCondExp m μ y ω * a ω) = matrixTrace μ (fun ω => y ω * a ω) := by
  rw [matrixTrace_mul_comm (matrixCondExp m μ y) a, matrixTrace_mul_comm y a]
  exact matrixTrace_mul_matrixCondExp hm ha ha' hy

end Trace

end BanachProbability
