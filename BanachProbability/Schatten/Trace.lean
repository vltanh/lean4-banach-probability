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

theorem sum_overlap_left {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (k : n) :
    ∑ j, overlap hP hQ j k = 1 := by
  sorry

theorem sum_overlap_right {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (j : n) :
    ∑ k, overlap hP hQ j k = 1 := by
  sorry

/-- The two-basis trace identity `tr (f (P) g (Q)) = Σ_{j,k} ⟨u_j, v_k⟩² f (λ_j) g (μ_k)`. -/
theorem trace_cfc_mul_cfc {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f P * cfc g Q).trace =
      ∑ j, ∑ k, overlap hP hQ j k * f (hP.eigenvalues j) * g (hQ.eigenvalues k) := by
  sorry

/-- The scalar mean-value inequality: for `q ≥ 2`,
`(a − b)(a |a|^{q−2} − b |b|^{q−2}) ≤ (q − 1)(a − b)² (|a|^{q−2} + |b|^{q−2})`. -/
theorem mul_sub_le_sq_mul_add {q : ℝ} (hq : 2 ≤ q) (a b : ℝ) :
    (a - b) * (a * |a| ^ (q - 2) - b * |b| ^ (q - 2)) ≤
      (q - 1) * (a - b) ^ 2 * (|a| ^ (q - 2) + |b| ^ (q - 2)) := by
  sorry

/-- **The mean-value trace inequality**, `q ≥ 2`, `h (t) = t |t|^{q−2}`, `g (t) = |t|^{q−2}`:
`tr ((P − Q)(h (P) − h (Q))) ≤ (q − 1) [tr ((P − Q)² g (P)) + tr ((P − Q)² g (Q))]`. -/
theorem trace_mean_value {P Q : Matrix n n ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) {q : ℝ}
    (hq : 2 ≤ q) :
    ((P - Q) *
        (cfc (fun t : ℝ => t * |t| ^ (q - 2)) P - cfc (fun t : ℝ => t * |t| ^ (q - 2)) Q)).trace ≤
      (q - 1) * (((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) P).trace +
        ((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) Q).trace) := by
  sorry

end BanachProbability
