module

public import BanachProbability.Schatten.Trace
public import Mathlib.Basic.Real.Sign

/-!
# Trace Hölder inequality and duality for Schatten norms

* `trace_mul_le_of_posSemidef`, `abs_trace_mul_le_of_isHermitian`: the trace Hölder inequality
  `tr (A B) ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}`, `r' = r / (r − 1)`, for positive semidefinite, then
  symmetric, `A`, `B`. Writing `tr (A B) = Σ_{j,k} a_j b_k ⟨u_j, v_k⟩²` (`trace_cfc_mul_cfc`), the
  weights `⟨u_j, v_k⟩²` are doubly stochastic, and the weighted Hölder inequality on the pairs
  `(j, k)` applies; neither Birkhoff's theorem nor von Neumann's trace inequality is needed.
* `normingElement r A = Σ_i sgn (λ_i) |λ_i|^{r−1} v_i v_iᵀ`, with
  `tr (A · normingElement r A) = ‖A‖_{S_r}^r` and `‖normingElement r A‖_{S_{r'}} = ‖A‖_{S_r}^{r−1}`:
  the equality case of Hölder's inequality.
* For positive semidefinite matrices: the norming element is positive semidefinite
  (`exists_posSemidef_trace_mul_eq`), whence the triangle inequality on positive semidefinite
  matrices (`schattenNorm_sum_le_of_posSemidef`, Jensen's inequality for the `S_r` norm) without
  the general Schatten triangle inequality.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace Hölder inequality** for positive semidefinite matrices:
`tr (V W) ≤ ‖V‖_{S_r} ‖W‖_{S_{r'}}`, `r' = r / (r − 1)`. -/
theorem trace_mul_le_of_posSemidef {V W : Matrix n n ℝ} (hV : V.PosSemidef) (hW : W.PosSemidef)
    {r : ℝ} (hr : 1 < r) :
    (V * W).trace ≤
      schattenNorm (ENNReal.ofReal r) V * schattenNorm (ENNReal.ofReal (r / (r - 1))) W := by
  sorry

/-- **Trace Hölder inequality** for symmetric matrices:
`|tr (A B)| ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}`, `r' = r / (r − 1)`. -/
theorem abs_trace_mul_le_of_isHermitian {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℝ} (hr : 1 < r) :
    |(A * B).trace| ≤
      schattenNorm (ENNReal.ofReal r) A * schattenNorm (ENNReal.ofReal (r / (r - 1))) B := by
  sorry

/-- The norming element `Σ_i sgn (λ_i) |λ_i|^{r−1} v_i v_iᵀ` of a symmetric matrix `A` for the
duality between `S_r` and `S_{r'}`. -/
noncomputable def normingElement (r : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => Real.sign t * |t| ^ (r - 1)) A

theorem trace_mul_normingElement {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ} (hr : 1 < r) :
    (A * normingElement r A).trace = schattenNorm (ENNReal.ofReal r) A ^ r := by
  sorry

theorem schattenNorm_normingElement {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ}
    (hr : 1 < r) :
    schattenNorm (ENNReal.ofReal (r / (r - 1))) (normingElement r A) =
      schattenNorm (ENNReal.ofReal r) A ^ (r - 1) := by
  sorry

theorem isHermitian_normingElement (r : ℝ) (A : Matrix n n ℝ) :
    (normingElement r A).IsHermitian := by
  sorry

/-- Duality for positive semidefinite matrices: `‖W‖_{S_r} = tr (W Z)` for some positive
semidefinite `Z` with `‖Z‖_{S_{r'}} ≤ 1`. -/
theorem exists_posSemidef_trace_mul_eq {W : Matrix n n ℝ} (hW : W.PosSemidef) {r : ℝ}
    (hr : 1 < r) :
    ∃ Z : Matrix n n ℝ, Z.PosSemidef ∧ schattenNorm (ENNReal.ofReal (r / (r - 1))) Z ≤ 1 ∧
      (W * Z).trace = schattenNorm (ENNReal.ofReal r) W := by
  sorry

/-- The triangle inequality (Jensen's inequality) for the `S_r` norm on positive semidefinite
matrices, from duality: `‖Σ_i W_i‖_{S_r} ≤ Σ_i ‖W_i‖_{S_r}`, `r ≥ 1`. -/
theorem schattenNorm_sum_le_of_posSemidef {ι : Type*} (s : Finset ι) {W : ι → Matrix n n ℝ}
    (hW : ∀ i ∈ s, (W i).PosSemidef) {r : ℝ} (hr : 1 ≤ r) :
    schattenNorm (ENNReal.ofReal r) (∑ i ∈ s, W i) ≤
      ∑ i ∈ s, schattenNorm (ENNReal.ofReal r) (W i) := by
  sorry

end BanachProbability
