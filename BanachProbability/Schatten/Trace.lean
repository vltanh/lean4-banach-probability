module

public import BanachProbability.Schatten.Spectral

/-!
# Trace identities and the mean-value trace inequality

For symmetric `P = Σ_j λ_j u_j u_jᵀ` and `Q = Σ_k μ_k v_k v_kᵀ` (orthonormal eigenbases), the
overlaps `c_{jk} = ⟨u_j, v_k⟩²` form a doubly stochastic matrix (`sum_overlap_left`,
`sum_overlap_right`), and for all functions `f`, `g`,
`tr (f (P) g (Q)) = Σ_{j,k} c_{jk} f (λ_j) g (μ_k)` (`trace_cfc_mul_cfc`).

With `h (t) = t |t|^{q−2}` and `g (t) = |t|^{q−2}`, `q ≥ 2`, the scalar inequality
`(a − b)(h (a) − h (b)) ≤ (q − 1)(a − b)² (|a|^{q−2} + |b|^{q−2})` (Bernoulli's inequality when
`a`, `b` have the same sign, trivial otherwise; `mul_sub_le_sq_mul_add`) gives the mean-value trace
inequality `tr ((P − Q)(h (P) − h (Q))) ≤ (q − 1) [tr ((P − Q)² g (P)) + tr ((P − Q)² g (Q))]`
(`trace_mean_value`): a form, valid for every `q ≥ 2`, of Mackey–Jordan–Chen–Farrell–Tropp, *Matrix
concentration inequalities via the method of exchangeable pairs*, Ann. Probab. 42 (2014),
Lemma 3.4 (whose convex-derivative form needs `q ≥ 3`).
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
`(a − b)(a |a|^{q−2} − b |b|^{q−2}) ≤ (q − 1)(a − b)² (|a|^{q−2} + |b|^{q−2})`. -/
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
for every `q ≥ 2`, whereas (3.7) needs the convexity of `h'`, that is `q ≥ 3`. -/
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

end BanachProbability
