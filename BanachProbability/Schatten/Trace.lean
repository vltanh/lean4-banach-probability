module

public import BanachProbability.Schatten.Spectral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Trace identities and the mean-value trace inequality

For symmetric `P = Σ_j λ_j u_j u_jᵀ` and `Q = Σ_k μ_k v_k v_kᵀ` (orthonormal eigenbases), the
overlaps `c_{jk} = ⟨u_j, v_k⟩²` form a doubly stochastic matrix (`sum_overlap_left`,
`sum_overlap_right`), and for all functions `f`, `g`,
`tr (f (P) g (Q)) = Σ_{j,k} c_{jk} f (λ_j) g (μ_k)` (`trace_cfc_mul_cfc`).

Mean-value trace inequalities (Mackey–Jordan–Chen–Farrell–Tropp, *Matrix concentration
inequalities via the method of exchangeable pairs*, Ann. Probab. 42 (2014), Lemma 3.4), with
`h (t) = t |t|^{q−2}` and `g (t) = |t|^{q−2}`:

* `q ≥ 3`, the source's Lemma 3.4: `h' (t) = (q − 1) |t|^{q−2}` is convex, and the source's scalar
  inequality (3.7), `(a − b)(h (a) − h (b)) ≤ ½ (a − b)² (h' (a) + h' (b))` for every `h` with a
  continuous convex derivative (`mul_sub_le_half_sq_mul_add_of_convexOn`, by the fundamental
  theorem of calculus along the segment and the convexity of `h'` under the integral;
  `mul_sub_le_half_sq_mul_add` for this `h`), gives
  `tr ((P − Q)(h (P) − h (Q))) ≤ ((q − 1) / 2) [tr ((P − Q)² g (P)) + tr ((P − Q)² g (Q))]`
  (`trace_mean_value_of_three_le`);
* `q ≥ 2`: the cruder scalar inequality
  `(a − b)(h (a) − h (b)) ≤ (q − 1)(a − b)² (|a|^{q−2} + |b|^{q−2})` (Bernoulli's inequality when
  `a`, `b` have the same sign, trivial otherwise; `mul_sub_le_sq_mul_add`) gives the same trace
  inequality with the constant `q − 1` (`trace_mean_value`). This is the variant of Lemma 3.4 that
  the source's Remark 7.2 requires for `2 < q < 3` (where `h'` is not convex) but does not prove.

Both trace inequalities come from their scalar forms by the expansion of the trace in the two
eigenbases behind the source's generalized Klein inequality (Proposition 3.5).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The overlap `⟨u_j, v_k⟩²` of the `j`-th eigenvector of `P` and the `k`-th eigenvector of
`Q`. -/
noncomputable def overlap {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (j k : n) : ℝ :=
  inner ℝ (hP.eigenvectorBasis j) (hQ.eigenvectorBasis k) ^ 2

theorem overlap_nonneg {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (j k : n) :
    0 ≤ overlap hP hQ j k :=
  sq_nonneg _

/-- The columns of the overlap matrix sum to `1`: `Σ_j ⟨u_j, v_k⟩² = ‖v_k‖² = 1` (Parseval). -/
theorem sum_overlap_left {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (k : n) :
    ∑ j, overlap hP hQ j k = 1 := by
  simp only [overlap]
  rw [hP.eigenvectorBasis.sum_sq_inner_right, hQ.eigenvectorBasis.orthonormal.1 k, one_pow]

/-- The rows of the overlap matrix sum to `1`: `Σ_k ⟨u_j, v_k⟩² = ‖u_j‖² = 1` (Parseval). -/
theorem sum_overlap_right {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (j : n) :
    ∑ k, overlap hP hQ j k = 1 := by
  simp only [overlap]
  rw [hQ.eigenvectorBasis.sum_sq_inner_left, hP.eigenvectorBasis.orthonormal.1 j, one_pow]

/-- Entries of `f (P)` in terms of an orthonormal eigenbasis: `f (P) = Σ_j f (λ_j) u_j u_jᵀ`. -/
private theorem cfc_apply_eq_sum {P : Matrix n n ℝ} (hP : P.IsHermitian) (f : ℝ → ℝ) (a b : n) :
    cfc f P a b =
      ∑ j, hP.eigenvectorBasis j a * f (hP.eigenvalues j) * hP.eigenvectorBasis j b := by
  rw [hP.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

private theorem inner_eigenvectorBasis {P Q : Matrix n n ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (j k : n) :
    inner ℝ (hP.eigenvectorBasis j) (hQ.eigenvectorBasis k) =
      ∑ a, hP.eigenvectorBasis j a * hQ.eigenvectorBasis k a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

private theorem sum_four_comm {α : Type*} [Fintype α] (F : α → α → α → α → ℝ) :
    ∑ a, ∑ b, ∑ j, ∑ k, F a b j k = ∑ j, ∑ k, ∑ a, ∑ b, F a b j k := by
  calc _ = ∑ a, ∑ j, ∑ b, ∑ k, F a b j k := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ k, ∑ b, F a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ k, ∑ b, F a b j k := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- The two-basis trace identity `tr (f (P) g (Q)) = Σ_{j,k} ⟨u_j, v_k⟩² f (λ_j) g (μ_k)`. -/
theorem trace_cfc_mul_cfc {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f P * cfc g Q).trace =
      ∑ j, ∑ k, overlap hP hQ j k * f (hP.eigenvalues j) * g (hQ.eigenvalues k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, cfc_apply_eq_sum hP,
    cfc_apply_eq_sum hQ, overlap, inner_eigenvectorBasis hP hQ, sq, Finset.sum_mul,
    Finset.mul_sum]
  rw [sum_four_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The tangent-line bound for `t ↦ t^{p+1}`, `p ≥ 0`, on `[0, ∞)` (Bernoulli's inequality):
`a^{p+1} − b^{p+1} ≤ (p + 1) a^p (a − b)` for `0 ≤ b ≤ a`. -/
private theorem mul_rpow_sub_mul_rpow_le {p a b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) (hba : b ≤ a) :
    a * a ^ p - b * b ^ p ≤ (p + 1) * a ^ p * (a - b) := by
  rcases hba.lt_or_eq with hlt | heq
  · have ha : 0 < a := hb.trans_lt hlt
    have hs : -1 ≤ b / a - 1 := by
      have : 0 ≤ b / a := div_nonneg hb ha.le
      linarith
    have hB := one_add_mul_self_le_rpow_one_add hs (p := p + 1) (by linarith)
    rw [add_sub_cancel, Real.div_rpow hb ha.le, Real.rpow_add_one' hb (by linarith),
      Real.rpow_add_one' ha.le (by linarith)] at hB
    have hap : 0 < a ^ p * a := mul_pos (Real.rpow_pos_of_pos ha p) ha
    rw [le_div_iff₀ hap] at hB
    have : (p + 1) * (b / a - 1) * (a ^ p * a) = (p + 1) * a ^ p * (b - a) := by
      field_simp
    nlinarith [this]
  · subst heq
    simp

/-- The scalar mean-value inequality: for `q ≥ 2`,
`(a − b)(a |a|^{q−2} − b |b|^{q−2}) ≤ (q − 1)(a − b)² (|a|^{q−2} + |b|^{q−2})`.

Departure from the source: Mackey et al., Remark 7.2, state that the range `2 < q < 3` requires a
variant of the mean value trace inequality, without proving it; this is the scalar form of such a
variant, proved by Bernoulli's inequality (same signs) and the elementary bound (opposite
signs). -/
theorem mul_sub_le_sq_mul_add {q : ℝ} (hq : 2 ≤ q) (a b : ℝ) :
    (a - b) * (a * |a| ^ (q - 2) - b * |b| ^ (q - 2)) ≤
      (q - 1) * (a - b) ^ 2 * (|a| ^ (q - 2) + |b| ^ (q - 2)) := by
  set p := q - 2 with hp_def
  have hp : 0 ≤ p := by linarith
  have hq1 : q - 1 = p + 1 := by ring
  rw [hq1]
  -- the case `b ≤ a`, `0 ≤ a`; the others follow by the symmetries `(a, b) ↦ (b, a)`,
  -- `(a, b) ↦ (−b, −a)`
  have key : ∀ a b : ℝ, b ≤ a → 0 ≤ a →
      (a - b) * (a * |a| ^ p - b * |b| ^ p) ≤ (p + 1) * (a - b) ^ 2 * (|a| ^ p + |b| ^ p) := by
    intro a b hba ha
    have hA : 0 ≤ |a| ^ p := Real.rpow_nonneg (abs_nonneg a) p
    have hB : 0 ≤ |b| ^ p := Real.rpow_nonneg (abs_nonneg b) p
    have hab : 0 ≤ a - b := by linarith
    rw [abs_of_nonneg ha] at hA ⊢
    rcases le_total 0 b with hb | hb
    · -- same sign: the tangent-line bound
      rw [abs_of_nonneg hb] at hB ⊢
      have h1 := mul_rpow_sub_mul_rpow_le hp hb hba
      have h2 := mul_le_mul_of_nonneg_left h1 hab
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ p + 1) (sq_nonneg (a - b))) hB]
    · -- opposite signs: `a − b = |a| + |b|`
      rw [abs_of_nonpos hb] at hB ⊢
      have h1 : a * a ^ p - b * (-b) ^ p ≤ (a - b) * (a ^ p + (-b) ^ p) := by
        nlinarith [mul_nonneg ha hB, mul_nonneg (by linarith : (0:ℝ) ≤ -b) hA]
      have h2 := mul_le_mul_of_nonneg_left h1 hab
      have h3 : 0 ≤ (a - b) * ((a - b) * (a ^ p + (-b) ^ p)) :=
        mul_nonneg hab (mul_nonneg hab (add_nonneg hA hB))
      nlinarith [mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ p + 1) h3]
  rcases le_total b a with hba | hab
  · rcases le_total 0 a with ha | ha
    · exact key a b hba ha
    · have := key (-b) (-a) (by linarith) (by linarith)
      simp only [abs_neg] at this
      nlinarith [this]
  · rcases le_total 0 b with hb | hb
    · have := key b a hab hb
      nlinarith [this]
    · have := key (-a) (-b) (by linarith) (by linarith)
      simp only [abs_neg] at this
      nlinarith [this]

/-- **The scalar mean-value inequality (3.7)** of Mackey–Jordan–Chen–Farrell–Tropp (proof of
Lemma 3.4, with `g = id`): if `h` has derivative `h'` everywhere and `h'` is continuous and
convex, then `(a − b)(h (a) − h (b)) ≤ ½ (a − b)² (h' (a) + h' (b))`. As in the source: by the
fundamental theorem of calculus along the segment, `h (a) − h (b) = (a − b) ∫₀¹ h' (τ a +
(1 − τ) b) dτ`, and the convexity of `h'` under the integral, `∫₀¹ τ dτ = ½`. -/
theorem mul_sub_le_half_sq_mul_add_of_convexOn {h h' : ℝ → ℝ} (hh : ∀ t, HasDerivAt h (h' t) t)
    (hc : Continuous h') (hconv : ConvexOn ℝ Set.univ h') (a b : ℝ) :
    (a - b) * (h a - h b) ≤ 1 / 2 * (a - b) ^ 2 * (h' a + h' b) := by
  have hseg : Continuous fun τ : ℝ => h' (τ * a + (1 - τ) * b) := hc.comp (by fun_prop)
  -- the fundamental theorem of calculus along the segment from `b` to `a`
  have hftc : h a - h b = (a - b) * ∫ τ in (0 : ℝ)..1, h' (τ * a + (1 - τ) * b) := by
    have hd : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun τ : ℝ => h (τ * a + (1 - τ) * b))
        ((a - b) * h' (τ * a + (1 - τ) * b)) τ := fun τ _ => by
      have h1 : HasDerivAt (fun τ : ℝ => τ * a + (1 - τ) * b) (a - b) τ := by
        have := ((hasDerivAt_id τ).mul_const (a - b)).const_add b
        convert this using 1
        · funext y
          simp only [id]
          ring
        · ring
      exact ((hh _).comp τ h1).congr_deriv (mul_comm _ _)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul hseg).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at this
    norm_num at this
    rw [this]
  -- the convexity of `h'` on the segment
  have hle : ∫ τ in (0 : ℝ)..1, h' (τ * a + (1 - τ) * b) ≤
      ∫ τ in (0 : ℝ)..1, (τ * h' a + (1 - τ) * h' b) := by
    refine intervalIntegral.integral_mono_on zero_le_one (hseg.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun τ : ℝ => τ * h' a + (1 - τ) * h' b).intervalIntegrable _ _)
      fun τ hτ => ?_
    have := hconv.2 (Set.mem_univ a) (Set.mem_univ b) hτ.1 (sub_nonneg.mpr hτ.2) (by ring)
    simpa only [smul_eq_mul] using this
  -- `∫₀¹ (τ h' (a) + (1 − τ) h' (b)) dτ = (h' (a) + h' (b)) / 2`
  have hval : ∫ τ in (0 : ℝ)..1, (τ * h' a + (1 - τ) * h' b) = (h' a + h' b) / 2 := by
    have e : (fun τ : ℝ => τ * h' a + (1 - τ) * h' b) = fun τ => h' b + τ * (h' a - h' b) := by
      funext τ
      ring
    rw [e, intervalIntegral.integral_add (f := fun _ => h' b)
      (g := fun τ : ℝ => τ * (h' a - h' b)) intervalIntegrable_const
      ((by fun_prop : Continuous fun τ : ℝ => τ * (h' a - h' b)).intervalIntegrable _ _),
      intervalIntegral.integral_mul_const, integral_id, intervalIntegral.integral_const]
    norm_num
    ring
  rw [hftc]
  calc (a - b) * ((a - b) * ∫ τ in (0 : ℝ)..1, h' (τ * a + (1 - τ) * b))
      = (a - b) ^ 2 * ∫ τ in (0 : ℝ)..1, h' (τ * a + (1 - τ) * b) := by ring
    _ ≤ (a - b) ^ 2 * ((h' a + h' b) / 2) := by
      rw [← hval]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    _ = 1 / 2 * (a - b) ^ 2 * (h' a + h' b) := by ring

/-- `h (t) = t |t|^s` has derivative `(s + 1) |t|^s`, `s > 0`. -/
private theorem hasDerivAt_mul_abs_rpow {s : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt (fun u : ℝ => u * |u| ^ s) ((s + 1) * |t| ^ s) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · -- `u |u|^s = −(−u)^{s+1}` near `t < 0`
    have h1 := ((Real.hasDerivAt_rpow_const (p := s + 1)
      (Or.inl (neg_ne_zero.mpr ht.ne))).comp t (hasDerivAt_neg t)).neg
    rw [abs_of_neg ht]
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Iio_mem_nhds ht] with u hu
      change u * |u| ^ s = -((-u) ^ (s + 1))
      rw [abs_of_neg hu, Real.rpow_add_one (neg_ne_zero.mpr hu.ne)]
      ring
    · rw [add_sub_cancel_right]
      ring
  · -- at `0` the slope `|u|^s` tends to `0`
    rw [hasDerivAt_iff_tendsto_slope, abs_zero, Real.zero_rpow hs.ne', mul_zero]
    have hcont : Filter.Tendsto (fun u : ℝ => |u| ^ s) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := (continuous_abs.rpow_const fun _ => Or.inr hs.le).tendsto (0 : ℝ)
      simp only [abs_zero, Real.zero_rpow hs.ne'] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [slope_def_field]
    have hu' : u ≠ 0 := hu
    field_simp
    simp
  · -- `u |u|^s = u^{s+1}` near `t > 0`
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := s + 1) (Or.inl ht.ne')
    rw [abs_of_pos ht]
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv (by rw [add_sub_cancel_right])
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [abs_of_pos hu, Real.rpow_add_one hu.ne']
    ring

/-- `t ↦ |t|^s` is convex for `s ≥ 1`. -/
private theorem convexOn_abs_rpow {s : ℝ} (hs : 1 ≤ s) :
    ConvexOn ℝ Set.univ fun t : ℝ => |t| ^ s := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  calc |a * x + b * y| ^ s ≤ (a * |x| + b * |y|) ^ s := by
        refine Real.rpow_le_rpow (abs_nonneg _) ?_ (by linarith)
        calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
          _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * |x| ^ s + b * |y| ^ s := by
        simpa only [smul_eq_mul] using
          (convexOn_rpow hs).2 (Set.mem_Ici.mpr (abs_nonneg x)) (Set.mem_Ici.mpr (abs_nonneg y))
            ha hb hab

/-- **The scalar mean-value inequality (3.7)** for `h (t) = t |t|^{q−2}`, `q ≥ 3`, whose derivative
`h' (t) = (q − 1) |t|^{q−2}` is convex:
`(a − b)(a |a|^{q−2} − b |b|^{q−2}) ≤ ((q − 1) / 2)(a − b)² (|a|^{q−2} + |b|^{q−2})`. -/
theorem mul_sub_le_half_sq_mul_add {q : ℝ} (hq : 3 ≤ q) (a b : ℝ) :
    (a - b) * (a * |a| ^ (q - 2) - b * |b| ^ (q - 2)) ≤
      (q - 1) / 2 * (a - b) ^ 2 * (|a| ^ (q - 2) + |b| ^ (q - 2)) := by
  have hs : 0 < q - 2 := by linarith
  have h := mul_sub_le_half_sq_mul_add_of_convexOn (h := fun t : ℝ => t * |t| ^ (q - 2))
    (h' := fun t : ℝ => (q - 1) * |t| ^ (q - 2))
    (fun t => (hasDerivAt_mul_abs_rpow hs t).congr_deriv (by ring))
    (continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr hs.le))
    ((convexOn_abs_rpow (by linarith)).smul (by linarith)) a b
  calc _ ≤ _ := h
    _ = _ := by ring

private theorem continuousOn_spectrum (P : Matrix n n ℝ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ P) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- The expansion behind the generalized Klein inequality, with a third factor on the `P` side:
`tr ((f₁ (P) − g₁ (Q))(f₂ (P) − g₂ (Q)) w (P)) =
Σ_{j,k} c_{jk} (f₁ (λ_j) − g₁ (μ_k))(f₂ (λ_j) − g₂ (μ_k)) w (λ_j)`. -/
private theorem trace_sub_mul_sub_mul_cfc_left {P Q : Matrix n n ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (f₁ g₁ f₂ g₂ w : ℝ → ℝ) :
    ((cfc f₁ P - cfc g₁ Q) * (cfc f₂ P - cfc g₂ Q) * cfc w P).trace =
      ∑ j, ∑ k, overlap hP hQ j k * (f₁ (hP.eigenvalues j) - g₁ (hQ.eigenvalues k)) *
        (f₂ (hP.eigenvalues j) - g₂ (hQ.eigenvalues k)) * w (hP.eigenvalues j) := by
  have hc := continuousOn_spectrum P
  have e1 : (cfc f₁ P * cfc f₂ P * cfc w P).trace =
      (cfc (fun t => f₁ t * f₂ t * w t) P * cfc (fun _ : ℝ => (1 : ℝ)) Q).trace := by
    rw [cfc_const_one ℝ Q (show IsSelfAdjoint Q from hQ), mul_one, cfc_mul _ _ P (hc _) (hc _),
      cfc_mul _ _ P (hc _) (hc _)]
  have e2 : (cfc f₁ P * cfc g₂ Q * cfc w P).trace =
      (cfc (fun t => w t * f₁ t) P * cfc g₂ Q).trace := by
    rw [Matrix.trace_mul_cycle, cfc_mul _ _ P (hc _) (hc _)]
  have e3 : (cfc g₁ Q * cfc f₂ P * cfc w P).trace =
      (cfc (fun t => f₂ t * w t) P * cfc g₁ Q).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm, cfc_mul _ _ P (hc _) (hc _)]
  have e4 : (cfc g₁ Q * cfc g₂ Q * cfc w P).trace =
      (cfc w P * cfc (fun t => g₁ t * g₂ t) Q).trace := by
    rw [Matrix.trace_mul_cycle, cfc_mul _ _ Q (continuousOn_spectrum Q _)
      (continuousOn_spectrum Q _), mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [e1, e2, e3, e4]
  simp only [trace_cfc_mul_cfc hP hQ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The same expansion with the third factor on the `Q` side. -/
private theorem trace_sub_mul_sub_mul_cfc_right {P Q : Matrix n n ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (f₁ g₁ f₂ g₂ w : ℝ → ℝ) :
    ((cfc f₁ P - cfc g₁ Q) * (cfc f₂ P - cfc g₂ Q) * cfc w Q).trace =
      ∑ j, ∑ k, overlap hP hQ j k * (f₁ (hP.eigenvalues j) - g₁ (hQ.eigenvalues k)) *
        (f₂ (hP.eigenvalues j) - g₂ (hQ.eigenvalues k)) * w (hQ.eigenvalues k) := by
  have h : (cfc f₁ P - cfc g₁ Q) * (cfc f₂ P - cfc g₂ Q) =
      (cfc g₁ Q - cfc f₁ P) * (cfc g₂ Q - cfc f₂ P) := by noncomm_ring
  rw [h, trace_sub_mul_sub_mul_cfc_left hQ hP, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [overlap, real_inner_comm]
  ring

/-- **The mean-value trace inequality**, `q ≥ 2`, `h (t) = t |t|^{q−2}`, `g (t) = |t|^{q−2}`:
`tr ((P − Q)(h (P) − h (Q))) ≤ (q − 1) [tr ((P − Q)² g (P)) + tr ((P − Q)² g (Q))]`.

The proof is that of Mackey–Jordan–Chen–Farrell–Tropp, Lemma 3.4: by cyclicity of the trace and
`trace_cfc_mul_cfc` (the expansion behind their generalized Klein inequality, Proposition 3.5),
the two sides are `Σ_{j,k} c_{jk} (λ_j − μ_k)(h (λ_j) − h (μ_k))` and
`(q − 1) Σ_{j,k} c_{jk} (λ_j − μ_k)² (g (λ_j) + g (μ_k))`, and the scalar inequality
`mul_sub_le_sq_mul_add` applies termwise, the weights `c_{jk}` being nonnegative. That scalar
inequality is cruder than the source's (3.7) (constant `q − 1` instead of `(q − 1) / 2`), and holds
for every `q ≥ 2`, whereas (3.7) needs the convexity of `h'`, that is `q ≥ 3`; for `q ≥ 3` see
`trace_mean_value_of_three_le`.

Departure from the source: for `2 < q < 3` this is the variant of Lemma 3.4 that Remark 7.2 of
Mackey et al. names but does not prove; it is proved here from `mul_sub_le_sq_mul_add`. -/
theorem trace_mean_value {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) {q : ℝ}
    (hq : 2 ≤ q) :
    ((P - Q) *
        (cfc (fun t : ℝ => t * |t| ^ (q - 2)) P - cfc (fun t : ℝ => t * |t| ^ (q - 2)) Q)).trace ≤
      (q - 1) * (((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) P).trace +
        ((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) Q).trace) := by
  have hPQ : P - Q = cfc (fun t : ℝ => t) P - cfc (fun t : ℝ => t) Q := by
    rw [cfc_id' ℝ P (show IsSelfAdjoint P from hP), cfc_id' ℝ Q (show IsSelfAdjoint Q from hQ)]
  rw [hPQ, ← mul_one ((cfc (fun t : ℝ => t) P - cfc (fun t : ℝ => t) Q) * _),
    ← cfc_const_one ℝ P (show IsSelfAdjoint P from hP), trace_sub_mul_sub_mul_cfc_left hP hQ,
    trace_sub_mul_sub_mul_cfc_left hP hQ, trace_sub_mul_sub_mul_cfc_right hP hQ,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := mul_le_mul_of_nonneg_left (mul_sub_le_sq_mul_add hq (hP.eigenvalues j)
    (hQ.eigenvalues k)) (overlap_nonneg hP hQ j k)
  linarith

/-- **The mean-value trace inequality**, the source's Lemma 3.4 for `q ≥ 3`:
`h (t) = t |t|^{q−2}` has the convex derivative `h' (t) = (q − 1) |t|^{q−2}`, and with
`g (t) = |t|^{q−2}`,
`tr ((P − Q)(h (P) − h (Q))) ≤ ((q − 1) / 2) [tr ((P − Q)² g (P)) + tr ((P − Q)² g (Q))]`.
The proof is the source's: the scalar inequality (3.7) (`mul_sub_le_half_sq_mul_add`) applied
termwise in the expansion of both sides in the two eigenbases (Proposition 3.5), the weights
`⟨u_j, v_k⟩²` being nonnegative. -/
theorem trace_mean_value_of_three_le {P Q : Matrix n n ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) {q : ℝ} (hq : 3 ≤ q) :
    ((P - Q) *
        (cfc (fun t : ℝ => t * |t| ^ (q - 2)) P - cfc (fun t : ℝ => t * |t| ^ (q - 2)) Q)).trace ≤
      (q - 1) / 2 * (((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) P).trace +
        ((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) Q).trace) := by
  have hPQ : P - Q = cfc (fun t : ℝ => t) P - cfc (fun t : ℝ => t) Q := by
    rw [cfc_id' ℝ P (show IsSelfAdjoint P from hP), cfc_id' ℝ Q (show IsSelfAdjoint Q from hQ)]
  rw [hPQ, ← mul_one ((cfc (fun t : ℝ => t) P - cfc (fun t : ℝ => t) Q) * _),
    ← cfc_const_one ℝ P (show IsSelfAdjoint P from hP), trace_sub_mul_sub_mul_cfc_left hP hQ,
    trace_sub_mul_sub_mul_cfc_left hP hQ, trace_sub_mul_sub_mul_cfc_right hP hQ,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := mul_le_mul_of_nonneg_left (mul_sub_le_half_sq_mul_add hq (hP.eigenvalues j)
    (hQ.eigenvalues k)) (overlap_nonneg hP hQ j k)
  linarith

end BanachProbability
