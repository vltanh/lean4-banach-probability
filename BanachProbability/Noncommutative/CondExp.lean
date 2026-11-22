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

/-! ### `L^p` membership -/

section MemLp

theorem MatrixMemLp.add {x y : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hy : MatrixMemLp y p μ) : MatrixMemLp (x + y) p μ := by
  sorry

theorem MatrixMemLp.sub {x y : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hy : MatrixMemLp y p μ) : MatrixMemLp (x - y) p μ := by
  sorry

theorem MatrixMemLp.neg {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ) :
    MatrixMemLp (-x) p μ := by
  sorry

theorem MatrixMemLp.const_smul {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (c : ℝ) : MatrixMemLp (c • x) p μ := by
  sorry

theorem MatrixMemLp.sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ} {p : ℝ≥0∞}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) p μ) : MatrixMemLp (∑ i ∈ s, x i) p μ := by
  sorry

theorem matrixMemLp_const [IsFiniteMeasure μ] (A : Matrix n n ℝ) (p : ℝ≥0∞) :
    MatrixMemLp (fun _ => A) p μ := by
  sorry

/-- `L^p ⊂ L^q` for `q ≤ p` on a finite measure space. -/
theorem MatrixMemLp.mono_exponent [IsFiniteMeasure μ] {x : Ω → Matrix n n ℝ} {p q : ℝ≥0∞}
    (hx : MatrixMemLp x p μ) (hqp : q ≤ p) : MatrixMemLp x q μ := by
  sorry

/-- A measurable matrix-valued function with entries bounded a.e. by `C` is in `L^∞`. -/
theorem MatrixMemLp.of_bound {x : Ω → Matrix n n ℝ} (hx : Measurable x) (C : ℝ)
    (h : ∀ᵐ ω ∂μ, ∀ i j, |x ω i j| ≤ C) : MatrixMemLp x ∞ μ := by
  sorry

/-- Hölder: the product of an `L^p` and an `L^q` matrix-valued function is in `L^r`,
`1/r = 1/p + 1/q`. -/
theorem MatrixMemLp.mul {x y : Ω → Matrix n n ℝ} {p q r : ℝ≥0∞} [p.HolderTriple q r]
    (hx : MatrixMemLp x p μ) (hy : MatrixMemLp y q μ) :
    MatrixMemLp (fun ω => x ω * y ω) r μ := by
  sorry

/-- A real `L^p` function times an `L^q` matrix-valued function is in `L^r`. -/
theorem MatrixMemLp.smul {c : Ω → ℝ} {x : Ω → Matrix n n ℝ} {p q r : ℝ≥0∞} [p.HolderTriple q r]
    (hc : MemLp c p μ) (hx : MatrixMemLp x q μ) : MatrixMemLp (fun ω => c ω • x ω) r μ := by
  sorry

theorem MatrixMemLp.aemeasurable {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ) :
    AEMeasurable x μ := by
  sorry

/-- `ω ↦ ‖x ω‖_{S_q}` is in `L^p` when the entries are (`q ≥ 1`). -/
theorem MatrixMemLp.memLp_schattenNorm {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) : MemLp (fun ω => schattenNorm q (x ω)) p μ := by
  sorry

/-- The entries are in `L^p` when `ω ↦ ‖x ω‖_{S_q}` is (`|A_{ij}| ≤ √(#n) ‖A‖_{S_q}`). -/
theorem matrixMemLp_of_memLp_schattenNorm {x : Ω → Matrix n n ℝ} (hx : AEMeasurable x μ)
    {p q : ℝ≥0∞} (hq : q ≠ 0) (h : MemLp (fun ω => schattenNorm q (x ω)) p μ) :
    MatrixMemLp x p μ := by
  sorry

end MemLp

/-! ### Entry bounds -/

section Bounds

/-- The entries of `A` with `0 ⪯ A ⪯ C` are bounded by `C`. -/
theorem abs_apply_le_of_posSemidef {A : Matrix n n ℝ} {C : ℝ} (hA : A.PosSemidef)
    (hAC : (C • (1 : Matrix n n ℝ) - A).PosSemidef) (i j : n) : |A i j| ≤ C := by
  sorry

omit [DecidableEq n] in
/-- The entries of an orthogonal projection are bounded by `1`. -/
theorem abs_apply_le_one_of_isProj {P : Matrix n n ℝ} (hP : P * P = P) (hPt : Pᵀ = P) (i j : n) :
    |P i j| ≤ 1 := by
  sorry

end Bounds

/-! ### The conditional expectation -/

section CondExp

theorem measurable_matrixCondExp (x : Ω → Matrix n n ℝ) : Measurable[m] (matrixCondExp m μ x) := by
  sorry

theorem MatrixMemLp.matrixCondExp {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞} (hx : MatrixMemLp x p μ)
    (hp : 1 ≤ p) : MatrixMemLp (matrixCondExp m μ x) p μ := by
  sorry

theorem matrixCondExp_of_measurable (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {x : Ω → Matrix n n ℝ} (hx : Measurable[m] x) (hxi : MatrixMemLp x 1 μ) :
    matrixCondExp m μ x = x := by
  sorry

theorem matrixCondExp_congr_ae {x y : Ω → Matrix n n ℝ} (h : x =ᵐ[μ] y) :
    matrixCondExp m μ x =ᵐ[μ] matrixCondExp m μ y := by
  sorry

theorem matrixCondExp_add {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    matrixCondExp m μ (x + y) =ᵐ[μ] matrixCondExp m μ x + matrixCondExp m μ y := by
  sorry

theorem matrixCondExp_sub {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) :
    matrixCondExp m μ (x - y) =ᵐ[μ] matrixCondExp m μ x - matrixCondExp m μ y := by
  sorry

theorem matrixCondExp_neg (x : Ω → Matrix n n ℝ) :
    matrixCondExp m μ (-x) =ᵐ[μ] -matrixCondExp m μ x := by
  sorry

theorem matrixCondExp_smul (c : ℝ) (x : Ω → Matrix n n ℝ) :
    matrixCondExp m μ (c • x) =ᵐ[μ] c • matrixCondExp m μ x := by
  sorry

theorem matrixCondExp_sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) 1 μ) :
    matrixCondExp m μ (∑ i ∈ s, x i) =ᵐ[μ] ∑ i ∈ s, matrixCondExp m μ (x i) := by
  sorry

theorem matrixCondExp_zero : matrixCondExp m μ (0 : Ω → Matrix n n ℝ) = 0 := by
  sorry

theorem matrixCondExp_const (hm : m ≤ mΩ) [IsFiniteMeasure μ] (A : Matrix n n ℝ) :
    matrixCondExp m μ (fun _ => A) = fun _ => A := by
  sorry

/-- The tower property `E_{m₁} E_{m₂} = E_{m₁}` for `m₁ ≤ m₂`. -/
theorem matrixCondExp_matrixCondExp_of_le {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ mΩ) [SigmaFinite (μ.trim h₂)] (x : Ω → Matrix n n ℝ) :
    matrixCondExp m₁ μ (matrixCondExp m₂ μ x) =ᵐ[μ] matrixCondExp m₁ μ x := by
  sorry

/-- The bimodule property `E_m (a x b) = a E_m (x) b` for bounded `m`-measurable `a`, `b`. -/
theorem matrixCondExp_mul_mul {a b x : Ω → Matrix n n ℝ} (ha : Measurable[m] a)
    (hb : Measurable[m] b) (ha' : MatrixMemLp a ∞ μ) (hb' : MatrixMemLp b ∞ μ)
    (hx : MatrixMemLp x 1 μ) :
    matrixCondExp m μ (fun ω => a ω * x ω * b ω) =ᵐ[μ] fun ω => a ω * matrixCondExp m μ x ω * b ω := by
  sorry

/-- `E_m (c x) = c E_m (x)` for a bounded `m`-measurable scalar function `c`. -/
theorem matrixCondExp_smul_left {c : Ω → ℝ} {x : Ω → Matrix n n ℝ} (hc : StronglyMeasurable[m] c)
    (hc' : MemLp c ∞ μ) (hx : MatrixMemLp x 1 μ) :
    matrixCondExp m μ (fun ω => c ω • x ω) =ᵐ[μ] fun ω => c ω • matrixCondExp m μ x ω := by
  sorry

/-- `E_m` maps (a.e.) symmetric functions to (a.e.) symmetric functions. -/
theorem isHermitian_matrixCondExp {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (matrixCondExp m μ x ω).IsHermitian := by
  sorry

/-- `E_m` is positive. -/
theorem posSemidef_matrixCondExp {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef)
    (hxi : MatrixMemLp x 1 μ) : ∀ᵐ ω ∂μ, (matrixCondExp m μ x ω).PosSemidef := by
  sorry

/-- `E_m` is order preserving. -/
theorem posSemidef_matrixCondExp_sub {x y : Ω → Matrix n n ℝ}
    (h : ∀ᵐ ω ∂μ, (y ω - x ω).PosSemidef) (hx : MatrixMemLp x 1 μ) (hy : MatrixMemLp y 1 μ) :
    ∀ᵐ ω ∂μ, (matrixCondExp m μ y ω - matrixCondExp m μ x ω).PosSemidef := by
  sorry

end CondExp

/-! ### The trace -/

section Trace

omit [DecidableEq n] in
theorem matrixTrace_add {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) : matrixTrace μ (x + y) = matrixTrace μ x + matrixTrace μ y := by
  sorry

omit [DecidableEq n] in
theorem matrixTrace_sub {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) : matrixTrace μ (x - y) = matrixTrace μ x - matrixTrace μ y := by
  sorry

omit [DecidableEq n] in
theorem matrixTrace_sum {ι : Type*} (s : Finset ι) {x : ι → Ω → Matrix n n ℝ}
    (hx : ∀ i ∈ s, MatrixMemLp (x i) 1 μ) :
    matrixTrace μ (∑ i ∈ s, x i) = ∑ i ∈ s, matrixTrace μ (x i) := by
  sorry

omit [DecidableEq n] in
theorem matrixTrace_smul (c : ℝ) (x : Ω → Matrix n n ℝ) :
    matrixTrace μ (c • x) = c * matrixTrace μ x := by
  sorry

omit [DecidableEq n] in
theorem matrixTrace_congr_ae {x y : Ω → Matrix n n ℝ} (h : x =ᵐ[μ] y) :
    matrixTrace μ x = matrixTrace μ y := by
  sorry

omit [DecidableEq n] in
/-- `τ (x y) = τ (y x)`. -/
theorem matrixTrace_mul_comm (x y : Ω → Matrix n n ℝ) :
    matrixTrace μ (fun ω => x ω * y ω) = matrixTrace μ (fun ω => y ω * x ω) := by
  sorry

omit [DecidableEq n] in
/-- `τ (x) ≥ 0` for (a.e.) positive semidefinite `x`. -/
theorem matrixTrace_nonneg {x : Ω → Matrix n n ℝ} (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) :
    0 ≤ matrixTrace μ x := by
  sorry

omit [DecidableEq n] in
/-- `τ` is monotone on integrable functions. -/
theorem matrixTrace_mono {x y : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ)
    (hy : MatrixMemLp y 1 μ) (h : ∀ᵐ ω ∂μ, (x ω).trace ≤ (y ω).trace) :
    matrixTrace μ x ≤ matrixTrace μ y := by
  sorry

/-- `τ ∘ E_m = τ`. -/
theorem matrixTrace_matrixCondExp (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {x : Ω → Matrix n n ℝ} (hx : MatrixMemLp x 1 μ) :
    matrixTrace μ (matrixCondExp m μ x) = matrixTrace μ x := by
  sorry

/-- The pull-out `τ (a E_m (y)) = τ (a y)` for an `m`-measurable `a ∈ L^p` and `y ∈ L^q`,
`1/p + 1/q = 1` (bimodule property and `τ ∘ E_m = τ`). -/
theorem matrixTrace_mul_matrixCondExp (hm : m ≤ mΩ) [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [p.HolderConjugate q] {a y : Ω → Matrix n n ℝ} (ha : Measurable[m] a) (ha' : MatrixMemLp a p μ)
    (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => a ω * matrixCondExp m μ y ω) = matrixTrace μ (fun ω => a ω * y ω) := by
  sorry

/-- The pull-out `τ (E_m (y) a) = τ (y a)` for an `m`-measurable `a ∈ L^p` and `y ∈ L^q`,
`1/p + 1/q = 1`. -/
theorem matrixTrace_matrixCondExp_mul (hm : m ≤ mΩ) [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [p.HolderConjugate q] {a y : Ω → Matrix n n ℝ} (ha : Measurable[m] a) (ha' : MatrixMemLp a p μ)
    (hy : MatrixMemLp y q μ) :
    matrixTrace μ (fun ω => matrixCondExp m μ y ω * a ω) = matrixTrace μ (fun ω => y ω * a ω) := by
  sorry

end Trace

end BanachProbability
