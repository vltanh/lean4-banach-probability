module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# The two simple functions of the integration method

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012, p. 26–30: the functions `U₁` (3.6) and `U_∞` (3.12) on a real inner product space
`H`, with the properties 2° and 3° of Burkholder's method for differentially subordinate martingales
(`Martingale/Osekowski/Method.lean`), and the bounds (3.14), (3.15).

Both functions depend on the norms only, and are written as functions of `s = |x|` (the position of
the dominating martingale) and `r = |y|` (that of the subordinate one).

## Main results

* `uOne`: `U₁ (x, y) = |y|² − |x|²` if `|x| + |y| < 1`, and `1 − 2 |x|` otherwise. `uOne_le` is 2°,
  that is (3.7), and `uOne_nonpos` is 3°.
* `uInfty`: `U_∞ (x, y) = 0` if `|x| + |y| ≤ 1`, and `(|y| − 1)² − |x|²` otherwise. `uInfty_le` is
  2°, that is (3.13), and `uInfty_nonpos` is 3° (Lemma 3.1).
* `abs_uOne_le`, `abs_uInfty_le` (Lemma 3.2): `|U₁ (x, y)| ≤ U₁ (0, y) − U₁ (x, 0)` (3.14) and
  `|U_∞ (x, y)| ≤ 1 + |x|² + |y|²` (3.15).
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace BanachProbability.Osekowski

/-- `U₁` (3.6), as a function of `s = |x|`, `r = |y|`: `|y|² − |x|²` if `|x| + |y| < 1`, and
`1 − 2 |x|` otherwise. -/
noncomputable def uOne (s r : ℝ) : ℝ := if s + r < 1 then r ^ 2 - s ^ 2 else 1 - 2 * s

/-- `U_∞` (3.12), as a function of `s = |x|`, `r = |y|`: `0` if `|x| + |y| ≤ 1`, and
`(|y| − 1)² − |x|²` otherwise. -/
noncomputable def uInfty (s r : ℝ) : ℝ := if s + r ≤ 1 then 0 else (r - 1) ^ 2 - s ^ 2

theorem measurable_uOne : Measurable (Function.uncurry uOne) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

theorem measurable_uInfty : Measurable (Function.uncurry uInfty) :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

/-- `U₁ (x, y) ≤ 1 − 2 |x|` everywhere (p. 26–27). -/
theorem uOne_le_one_sub {s r : ℝ} (hr : 0 ≤ r) : uOne s r ≤ 1 - 2 * s := by
  unfold uOne
  split_ifs with h
  · nlinarith
  · exact le_rfl

/-- The property 3° of `U₁`: `U₁ (x, y) ≤ 0` if `|y| ≤ |x|`, read off from (3.6). (The book calls it
obvious and, by the symmetry of `V` and Remark 2.1, asks only for `U₁ (0, 0) ≤ 0`.) -/
theorem uOne_nonpos {s r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : uOne s r ≤ 0 := by
  unfold uOne
  split_ifs with h
  · nlinarith
  · linarith

/-- `U_∞ (x, y) ≤ (|y| − 1)² − |x|²` everywhere (p. 29, where the sign is printed the other way). -/
theorem uInfty_le_sq_sub {s r : ℝ} (hs : 0 ≤ s) : uInfty s r ≤ (r - 1) ^ 2 - s ^ 2 := by
  unfold uInfty
  split_ifs with h
  · nlinarith
  · exact le_rfl

/-- **(3.14)** (Lemma 3.2): `|U₁ (x, y)| ≤ U₁ (0, y) − U₁ (x, 0)`. (The last `U₁ (x, y)` of the
proof in the book is `|U₁ (x, y)|`.) -/
theorem abs_uOne_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    |uOne s r| ≤ uOne 0 r - uOne s 0 := by
  unfold uOne
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- `|U₁ (x, y)| ≤ 1 + 2 |x|`. -/
theorem abs_uOne_le_one_add {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) : |uOne s r| ≤ 1 + 2 * s := by
  unfold uOne
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- **(3.15)** (Lemma 3.2): `|U_∞ (x, y)| ≤ 1 + |x|² + |y|²`. -/
theorem abs_uInfty_le {s r : ℝ} (hr : 0 ≤ r) : |uInfty s r| ≤ 1 + s ^ 2 + r ^ 2 := by
  unfold uInfty
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith [sq_nonneg s, sq_nonneg r]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `x' = x / |x|`, with `x' = 0` for `x = 0`. -/
private noncomputable def dir (x : H) : H := ‖x‖⁻¹ • x

private theorem norm_dir_le (x : H) : ‖dir x‖ ≤ 1 := by
  rw [dir, norm_smul, norm_inv, norm_norm]
  exact inv_mul_le_one

/-- `|x + h| ≥ |x| + ⟨x', h⟩`. -/
private theorem norm_add_ge (x h : H) : ‖x‖ + ⟪dir x, h⟫ ≤ ‖x + h‖ := by
  have h1 : ⟪dir x, x + h⟫ = ‖x‖ + ⟪dir x, h⟫ := by
    rw [inner_add_right, dir, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, ← mul_assoc,
      inv_mul_mul_self]
  rw [← h1]
  refine (real_inner_le_norm _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_dir_le x)

/-- The functional `A` of (3.7): `−2 x` if `|x| + |y| < 1`, and `−2 x'` otherwise. -/
noncomputable def uOneA (x y : H) : H :=
  if ‖x‖ + ‖y‖ < 1 then (-2 : ℝ) • x else (-2 : ℝ) • (‖x‖⁻¹ • x)

/-- The functional `B` of (3.7): `2 y` if `|x| + |y| < 1`, and `0` otherwise. -/
noncomputable def uOneB (x y : H) : H := if ‖x‖ + ‖y‖ < 1 then (2 : ℝ) • y else 0

/-- `A` of (3.7) is Borel, in the form used for martingales: `A (X, Y)` is strongly measurable if
`X` and `Y` are. -/
theorem stronglyMeasurable_uOneA {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → H}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable fun ω => uOneA (X ω) (Y ω) :=
  StronglyMeasurable.ite
    (measurableSet_lt (hX.norm.measurable.add hY.norm.measurable) measurable_const)
    (hX.const_smul _) ((hX.norm.measurable.inv.stronglyMeasurable.smul hX).const_smul _)

/-- `B` of (3.7) is Borel (see `stronglyMeasurable_uOneA`). -/
theorem stronglyMeasurable_uOneB {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → H}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable fun ω => uOneB (X ω) (Y ω) :=
  StronglyMeasurable.ite
    (measurableSet_lt (hX.norm.measurable.add hY.norm.measurable) measurable_const)
    (hY.const_smul _) stronglyMeasurable_const

/-- `|A| ≤ 2` in (3.7). -/
theorem norm_uOneA_le (x y : H) : ‖uOneA x y‖ ≤ 2 := by
  unfold uOneA
  split_ifs with h
  · rw [norm_smul]
    norm_num
    linarith [norm_nonneg y]
  · rw [norm_smul]
    have := norm_dir_le x
    rw [dir] at this
    norm_num
    linarith

/-- `|B| ≤ 2` in (3.7). -/
theorem norm_uOneB_le (x y : H) : ‖uOneB x y‖ ≤ 2 := by
  unfold uOneB
  split_ifs with h
  · rw [norm_smul]
    norm_num
    linarith [norm_nonneg x]
  · simp

/-- **(3.7)**, the property 2° of `U₁`: for `|k| ≤ |h|`,
`U₁ (x + h, y + k) ≤ U₁ (x, y) + ⟨A (x, y), h⟩ + ⟨B (x, y), k⟩`. If `|x| + |y| ≥ 1`, by
`U₁ ≤ 1 − 2 |x|`. If `|x| + |y| < 1` and `|x + h| + |y + k| < 1`, by `|k| ≤ |h|`. If
`|x| + |y| < 1` and `|x + h| + |y + k| ≥ 1`, it is (3.8)
`1 − 2 |x + h| ≤ |y|² + 2 ⟨y, k⟩ − |x|² − 2 ⟨x, h⟩` (printed with `≥` and the other signs of the
inner products): for `|x + h| ≤ 1` by `(1 − |x + h|)² ≤ |y + k|²`, and for `|x + h| > 1` by
`|h| > 1 − |x| ≥ |y|` and `(|x + h| − 1)² ≤ (|h| − |y|)² ≤ |y|² + 2 ⟨y, k⟩ + |h|²` (printed with the
other sign of `⟨y, k⟩`). -/
theorem uOne_le {x y h k : H} (hk : ‖k‖ ≤ ‖h‖) :
    uOne ‖x + h‖ ‖y + k‖ ≤ uOne ‖x‖ ‖y‖ + ⟪uOneA x y, h⟫ + ⟪uOneB x y, k⟫ := by
  have hx := norm_add_sq_real x h
  have hy := norm_add_sq_real y k
  have hk2 : ‖k‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg k) hk 2
  by_cases h1 : ‖x‖ + ‖y‖ < 1
  · rw [uOneA, uOneB, ite_eq_left h1, ite_eq_left h1, real_inner_smul_left, real_inner_smul_left]
    rw [show uOne ‖x‖ ‖y‖ = ‖y‖ ^ 2 - ‖x‖ ^ 2 from ite_eq_left h1]
    by_cases h2 : ‖x + h‖ + ‖y + k‖ < 1
    · rw [show uOne ‖x + h‖ ‖y + k‖ = ‖y + k‖ ^ 2 - ‖x + h‖ ^ 2 from ite_eq_left h2]
      linarith
    · rw [show uOne ‖x + h‖ ‖y + k‖ = 1 - 2 * ‖x + h‖ from ite_eq_right h2]
      rw [not_lt] at h2
      rcases le_or_gt ‖x + h‖ 1 with h3 | h3
      · have h4 : (1 - ‖x + h‖) ^ 2 ≤ ‖y + k‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      · have h4 := norm_add_le x h
        have h5 : (‖x + h‖ - 1) ^ 2 ≤ (‖h‖ - ‖y‖) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        have h6 : -(‖y‖ * ‖h‖) ≤ ⟪y, k⟫ := by
          have := neg_le_of_abs_le (abs_real_inner_le_norm y k)
          have := mul_le_mul_of_nonneg_left hk (norm_nonneg y)
          linarith
        linarith
  · rw [uOneA, uOneB, ite_eq_right h1, ite_eq_right h1, inner_zero_left, real_inner_smul_left]
    rw [show uOne ‖x‖ ‖y‖ = 1 - 2 * ‖x‖ from ite_eq_right h1]
    have := uOne_le_one_sub (s := ‖x + h‖) (norm_nonneg (y + k))
    have := norm_add_ge x h
    rw [dir] at this
    linarith

/-- The functional `A` of (3.13): `0` if `|x| + |y| < 1`, and `−2 x` otherwise. -/
noncomputable def uInftyA (x y : H) : H := if ‖x‖ + ‖y‖ < 1 then 0 else (-2 : ℝ) • x

/-- The functional `B` of (3.13): `0` if `|x| + |y| < 1`, and `2 y − 2 y'` otherwise. -/
noncomputable def uInftyB (x y : H) : H :=
  if ‖x‖ + ‖y‖ < 1 then 0 else (2 : ℝ) • y - (2 : ℝ) • (‖y‖⁻¹ • y)

/-- `A` of (3.13) is Borel (see `stronglyMeasurable_uOneA`). -/
theorem stronglyMeasurable_uInftyA {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → H}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable fun ω => uInftyA (X ω) (Y ω) :=
  StronglyMeasurable.ite
    (measurableSet_lt (hX.norm.measurable.add hY.norm.measurable) measurable_const)
    stronglyMeasurable_const (hX.const_smul _)

/-- `B` of (3.13) is Borel (see `stronglyMeasurable_uOneA`). -/
theorem stronglyMeasurable_uInftyB {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → H}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable fun ω => uInftyB (X ω) (Y ω) :=
  StronglyMeasurable.ite
    (measurableSet_lt (hX.norm.measurable.add hY.norm.measurable) measurable_const)
    stronglyMeasurable_const ((hY.const_smul _).sub
      ((hY.norm.measurable.inv.stronglyMeasurable.smul hY).const_smul _))

/-- `|A (x, y)| ≤ 2 |x|` in (3.13). -/
theorem norm_uInftyA_le (x y : H) : ‖uInftyA x y‖ ≤ 2 * ‖x‖ := by
  unfold uInftyA
  split_ifs with h
  · simp
  · rw [norm_smul]
    norm_num

/-- `|B (x, y)| ≤ 2 |y| + 2` in (3.13). -/
theorem norm_uInftyB_le (x y : H) : ‖uInftyB x y‖ ≤ 2 * ‖y‖ + 2 := by
  unfold uInftyB
  split_ifs with h
  · rw [norm_zero]
    positivity
  · refine (norm_sub_le _ _).trans ?_
    have := norm_dir_le y
    rw [dir] at this
    rw [norm_smul, norm_smul]
    norm_num
    linarith

/-- **(3.13)** (Lemma 3.1), the property 2° of `U_∞`: for `|k| ≤ |h|`,
`U_∞ (x + h, y + k) ≤ U_∞ (x, y) + ⟨A (x, y), h⟩ + ⟨B (x, y), k⟩`. If `|x| + |y| ≥ 1`, by
`U_∞ ≤ (|y| − 1)² − |x|²` and
`(|y + k| − 1)² − |x + h|² = (|y| − 1)² − |x|² − 2 [|y + k| − |y| − ⟨y, k⟩ + ⟨x, h⟩] + |k|² − |h|²`
(the signs of the inner products are printed the other way). If `|x| + |y| < 1` and
`|x + h| + |y + k| ≤ 1`, both sides vanish. If `|x| + |y| < 1` and `|x + h| + |y + k| > 1`, the
claim is `(|y + k| − 1)² ≤ |x + h|²`: for `|y + k| ≤ 1` it is the assumption, and for `|y + k| > 1`,
`|k| > 1 − |y| > |x|` and `|y + k| − 1 ≤ |k| − |x| ≤ |h| − |x| ≤ |x + h|`. -/
theorem uInfty_le {x y h k : H} (hk : ‖k‖ ≤ ‖h‖) :
    uInfty ‖x + h‖ ‖y + k‖ ≤ uInfty ‖x‖ ‖y‖ + ⟪uInftyA x y, h⟫ + ⟪uInftyB x y, k⟫ := by
  have hx := norm_add_sq_real x h
  have hy := norm_add_sq_real y k
  have hk2 : ‖k‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg k) hk 2
  by_cases h1 : ‖x‖ + ‖y‖ < 1
  · rw [uInftyA, uInftyB, ite_eq_left h1, ite_eq_left h1, inner_zero_left, inner_zero_left]
    rw [show uInfty ‖x‖ ‖y‖ = 0 from ite_eq_left h1.le, add_zero, add_zero]
    by_cases h2 : ‖x + h‖ + ‖y + k‖ ≤ 1
    · exact (ite_eq_left h2).le
    · rw [show uInfty ‖x + h‖ ‖y + k‖ = (‖y + k‖ - 1) ^ 2 - ‖x + h‖ ^ 2 from ite_eq_right h2]
      rw [not_le] at h2
      rcases le_or_gt ‖y + k‖ 1 with h3 | h3
      · have h4 : (1 - ‖y + k‖) ^ 2 ≤ ‖x + h‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith [sub_sq_comm 1 ‖y + k‖]
      · have h4 := norm_add_le y k
        have h5 : ‖h‖ - ‖x‖ ≤ ‖x + h‖ := by
          have := norm_sub_le (x + h) x
          rw [add_sub_cancel_left] at this
          linarith
        have h6 : (‖y + k‖ - 1) ^ 2 ≤ ‖x + h‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
  · rw [uInftyA, uInftyB, ite_eq_right h1, ite_eq_right h1, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left]
    have h2 : uInfty ‖x‖ ‖y‖ = (‖y‖ - 1) ^ 2 - ‖x‖ ^ 2 := by
      unfold uInfty
      split_ifs with h2
      · nlinarith [h2.antisymm (not_lt.1 h1)]
      · rfl
    have h3 := uInfty_le_sq_sub (r := ‖y + k‖) (norm_nonneg (x + h))
    have h4 := norm_add_ge y k
    rw [dir] at h4
    rw [h2]
    nlinarith

/-- The property 3° of `U_∞` (Lemma 3.1), by (3.13) at `(0, 0)`: `U_∞ (x, y) ≤ 0` if
`|y| ≤ |x|`. -/
theorem uInfty_nonpos {x y : H} (hxy : ‖y‖ ≤ ‖x‖) : uInfty ‖x‖ ‖y‖ ≤ 0 := by
  have := uInfty_le (x := 0) (y := 0) hxy
  simpa [uInftyA, uInftyB, uInfty] using this

end Hilbert

end BanachProbability.Osekowski
