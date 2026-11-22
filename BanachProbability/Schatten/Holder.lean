module

public import BanachProbability.Schatten.Trace
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign

/-!
# Trace Hölder inequality and duality for Schatten norms

* `trace_mul_le_of_posSemidef`, `abs_trace_mul_le_of_isHermitian`: the trace Hölder inequality
  `tr (A B) ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}`, `r' = r / (r − 1)`, for positive semidefinite, then
  symmetric, `A`, `B` (Mackey–Jordan–Chen–Farrell–Tropp, *Matrix concentration inequalities via
  the method of exchangeable pairs*, Ann. Probab. 42 (2014), Proposition 7.5, there quoted from
  Bhatia's *Matrix Analysis*). Writing `tr (A B) = Σ_{j,k} a_j b_k ⟨u_j, v_k⟩²`
  (`trace_cfc_mul_cfc`), the weights `⟨u_j, v_k⟩²` are doubly stochastic, and the weighted Hölder
  inequality on the pairs `(j, k)` applies; neither Birkhoff's theorem nor von Neumann's trace
  inequality is needed.
* `normingElement r A = Σ_i sgn (λ_i) |λ_i|^{r−1} v_i v_iᵀ`, with
  `tr (A · normingElement r A) = ‖A‖_{S_r}^r` and `‖normingElement r A‖_{S_{r'}} = ‖A‖_{S_r}^{r−1}`:
  the equality case of Hölder's inequality.
* For positive semidefinite matrices: the norming element is positive semidefinite
  (`exists_posSemidef_trace_mul_eq`), whence the triangle inequality on positive semidefinite
  matrices (`schattenNorm_sum_le_of_posSemidef`, Jensen's inequality for the `S_r` norm) without
  the general Schatten triangle inequality.

Spectral facts used on the way, from `BanachProbability.Schatten.Spectral`:
`tr (f (A)) = Σ_i f (λ_i)` (`trace_cfc_eq_sum`), the eigenvalues of `f (A)` are the `f (λ_i)` up to
order (`sum_comp_eigenvalues_cfc`, from the characteristic polynomial), `f (A) ⪰ 0` when `f ≥ 0`
on the spectrum (`posSemidef_cfc`), `‖A‖_{S_q} = (Σ_i |λ_i|^q)^{1/q}` for symmetric `A`
(`schattenNorm_eq_of_isHermitian`) and `‖W‖_{S_1} = tr W` for `W ⪰ 0`
(`schattenNorm_one_of_posSemidef`).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The trace Hölder inequality -/

/-- The weighted Hölder inequality on the pairs `(j, k)` with the doubly stochastic weights
`c_{jk} = ⟨u_j, v_k⟩²`: `Σ_{j,k} c_{jk} |λ_j| |μ_k| ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}`. -/
private theorem sum_overlap_mul_abs_le {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℝ} (hr : 1 < r) :
    ∑ j, ∑ k, overlap hA hB j k * |hA.eigenvalues j| * |hB.eigenvalues k| ≤
      schattenNorm (ENNReal.ofReal r) A * schattenNorm (ENNReal.ofReal (r / (r - 1))) B := by
  set r' := r / (r - 1)
  have hrr' : r.HolderConjugate r' := Real.HolderConjugate.conjExponent hr
  set c := overlap hA hB
  have hc : ∀ p : n × n, 0 ≤ c p.1 p.2 := fun p => overlap_nonneg hA hB p.1 p.2
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (n × n)) hrr'
    (f := fun p => c p.1 p.2 ^ r⁻¹ * |hA.eigenvalues p.1|)
    (g := fun p => c p.1 p.2 ^ r'⁻¹ * |hB.eigenvalues p.2|)
    (fun p _ => mul_nonneg (Real.rpow_nonneg (hc p) _) (abs_nonneg _))
    (fun p _ => mul_nonneg (Real.rpow_nonneg (hc p) _) (abs_nonneg _))
  have e1 : ∀ p : n × n, c p.1 p.2 ^ r⁻¹ * |hA.eigenvalues p.1| *
      (c p.1 p.2 ^ r'⁻¹ * |hB.eigenvalues p.2|) =
        c p.1 p.2 * |hA.eigenvalues p.1| * |hB.eigenvalues p.2| := by
    intro p
    have : c p.1 p.2 ^ r⁻¹ * c p.1 p.2 ^ r'⁻¹ = c p.1 p.2 := by
      rw [← Real.rpow_add' (hc p) (by rw [hrr'.inv_add_inv_eq_one]; norm_num),
        hrr'.inv_add_inv_eq_one, Real.rpow_one]
    calc _ = (c p.1 p.2 ^ r⁻¹ * c p.1 p.2 ^ r'⁻¹) * |hA.eigenvalues p.1| *
          |hB.eigenvalues p.2| := by ring
      _ = _ := by rw [this]
  have e2 : ∀ p : n × n, (c p.1 p.2 ^ r⁻¹ * |hA.eigenvalues p.1|) ^ r =
      c p.1 p.2 * |hA.eigenvalues p.1| ^ r := by
    intro p
    rw [Real.mul_rpow (Real.rpow_nonneg (hc p) _) (abs_nonneg _),
      Real.rpow_inv_rpow (hc p) hrr'.ne_zero]
  have e3 : ∀ p : n × n, (c p.1 p.2 ^ r'⁻¹ * |hB.eigenvalues p.2|) ^ r' =
      c p.1 p.2 * |hB.eigenvalues p.2| ^ r' := by
    intro p
    rw [Real.mul_rpow (Real.rpow_nonneg (hc p) _) (abs_nonneg _),
      Real.rpow_inv_rpow (hc p) hrr'.symm.ne_zero]
  simp only [e1, e2, e3] at hH
  simp only [Fintype.sum_prod_type] at hH
  have s1 : ∑ j, ∑ k, c j k * |hA.eigenvalues j| ^ r = ∑ j, |hA.eigenvalues j| ^ r :=
    Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, sum_overlap_right, one_mul]
  have s2 : ∑ j, ∑ k, c j k * |hB.eigenvalues k| ^ r' = ∑ k, |hB.eigenvalues k| ^ r' := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul, sum_overlap_left, one_mul]
  rw [s1, s2] at hH
  rwa [schattenNorm_eq_of_isHermitian hA hrr'.pos,
    schattenNorm_eq_of_isHermitian hB hrr'.symm.pos]

/-- **Trace Hölder inequality** for positive semidefinite matrices:
`tr (V W) ≤ ‖V‖_{S_r} ‖W‖_{S_{r'}}`, `r' = r / (r − 1)`. -/
theorem trace_mul_le_of_posSemidef {V W : Matrix n n ℝ} (hV : V.PosSemidef) (hW : W.PosSemidef)
    {r : ℝ} (hr : 1 < r) :
    (V * W).trace ≤
      schattenNorm (ENNReal.ofReal r) V * schattenNorm (ENNReal.ofReal (r / (r - 1))) W := by
  have h := trace_cfc_mul_cfc hV.isHermitian hW.isHermitian id id
  rw [cfc_id ℝ V (show IsSelfAdjoint V from hV.isHermitian),
    cfc_id ℝ W (show IsSelfAdjoint W from hW.isHermitian)] at h
  rw [h]
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_)
    (sum_overlap_mul_abs_le hV.isHermitian hW.isHermitian hr)
  simp only [id, abs_of_nonneg (hV.eigenvalues_nonneg j), abs_of_nonneg (hW.eigenvalues_nonneg k),
    le_refl]

/-- **Trace Hölder inequality** for symmetric matrices:
`|tr (A B)| ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}`, `r' = r / (r − 1)`. -/
theorem abs_trace_mul_le_of_isHermitian {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℝ} (hr : 1 < r) :
    |(A * B).trace| ≤
      schattenNorm (ENNReal.ofReal r) A * schattenNorm (ENNReal.ofReal (r / (r - 1))) B := by
  have h := trace_cfc_mul_cfc hA hB id id
  rw [cfc_id ℝ A (show IsSelfAdjoint A from hA), cfc_id ℝ B (show IsSelfAdjoint B from hB)] at h
  rw [h]
  refine le_trans ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)) (le_trans (le_of_eq ?_)
      (sum_overlap_mul_abs_le hA hB hr))
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (overlap_nonneg hA hB j k), id, id]

/-- `t · sgn (t) |t|^{r−1} = |t|^r`. -/
private theorem mul_sign_mul_abs_rpow (t : ℝ) {r : ℝ} (hr : 1 < r) :
    t * (Real.sign t * |t| ^ (r - 1)) = |t| ^ r := by
  have hs : t * Real.sign t = |t| := by
    rcases lt_trichotomy t 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h, mul_neg_one]
    · rw [h, Real.sign_zero, mul_zero, abs_zero]
    · rw [Real.sign_of_pos h, abs_of_pos h, mul_one]
  rw [← mul_assoc, hs, ← Real.rpow_one_add' (abs_nonneg t) (by linarith), add_sub_cancel]

/-- `|sgn (t) |t|^{r−1}| = |t|^{r−1}` for `r > 1`. -/
private theorem abs_sign_mul_abs_rpow (t : ℝ) {r : ℝ} (hr : 1 < r) :
    |Real.sign t * |t| ^ (r - 1)| = |t| ^ (r - 1) := by
  rcases eq_or_ne t 0 with h | h
  · rw [h, Real.sign_zero, zero_mul, abs_zero, Real.zero_rpow (by linarith)]
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    rcases Real.sign_apply_eq_of_ne_zero t h with h' | h' <;> simp [h']

private theorem sign_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.sign t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, Real.sign_zero]
  · rw [Real.sign_of_pos h]
    exact zero_le_one

/-- The norming element `Σ_i sgn (λ_i) |λ_i|^{r−1} v_i v_iᵀ` of a symmetric matrix `A` for the
duality between `S_r` and `S_{r'}`. -/
noncomputable def normingElement (r : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => Real.sign t * |t| ^ (r - 1)) A

/-- `tr (A · normingElement r A) = Σ_i λ_i sgn (λ_i) |λ_i|^{r−1} = Σ_i |λ_i|^r = ‖A‖_{S_r}^r`. -/
theorem trace_mul_normingElement {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ} (hr : 1 < r) :
    (A * normingElement r A).trace = schattenNorm (ENNReal.ofReal r) A ^ r := by
  have h : cfc (fun t : ℝ => t * (Real.sign t * |t| ^ (r - 1))) A =
      cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => Real.sign t * |t| ^ (r - 1)) A :=
    cfc_mul _ _ A (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)
  rw [cfc_id' ℝ A (show IsSelfAdjoint A from hA)] at h
  rw [normingElement, ← h, trace_cfc_eq_sum hA, schattenNorm_rpow_of_isHermitian hA (by linarith)]
  exact Finset.sum_congr rfl fun i _ => mul_sign_mul_abs_rpow _ hr

/-- The eigenvalues of `normingElement r A` are the `sgn (λ_i) |λ_i|^{r−1}`, so
`‖normingElement r A‖_{S_{r'}}^{r'} = Σ_i |λ_i|^{(r−1) r'} = ‖A‖_{S_r}^r`. -/
theorem schattenNorm_normingElement {A : Matrix n n ℝ} (hA : A.IsHermitian) {r : ℝ}
    (hr : 1 < r) :
    schattenNorm (ENNReal.ofReal (r / (r - 1))) (normingElement r A) =
      schattenNorm (ENNReal.ofReal r) A ^ (r - 1) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr' : 0 < r / (r - 1) := div_pos hr0 hr1
  have hN : (cfc (fun t : ℝ => Real.sign t * |t| ^ (r - 1)) A).IsHermitian := isHermitian_cfc _ A
  rw [normingElement, schattenNorm_eq_of_isHermitian hN hr',
    sum_comp_eigenvalues_cfc hA _ hN fun t => |t| ^ (r / (r - 1))]
  have e : ∀ i, |Real.sign (hA.eigenvalues i) * |hA.eigenvalues i| ^ (r - 1)| ^ (r / (r - 1)) =
      |hA.eigenvalues i| ^ r := by
    intro i
    rw [abs_sign_mul_abs_rpow _ hr, ← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hr1.ne']
  simp only [e]
  rw [← schattenNorm_rpow_of_isHermitian hA hr0, ← Real.rpow_mul (schattenNorm_nonneg _ _)]
  congr 1
  field_simp

/-- The norming element is symmetric, for every `A` (for a non-symmetric `A` it is `0`). -/
theorem isHermitian_normingElement (r : ℝ) (A : Matrix n n ℝ) :
    (normingElement r A).IsHermitian :=
  isHermitian_cfc _ A

/-- Duality for positive semidefinite matrices: `‖W‖_{S_r} = tr (W Z)` for some positive
semidefinite `Z` with `‖Z‖_{S_{r'}} ≤ 1`. -/
theorem exists_posSemidef_trace_mul_eq {W : Matrix n n ℝ} (hW : W.PosSemidef) {r : ℝ}
    (hr : 1 < r) :
    ∃ Z : Matrix n n ℝ, Z.PosSemidef ∧ schattenNorm (ENNReal.ofReal (r / (r - 1))) Z ≤ 1 ∧
      (W * Z).trace = schattenNorm (ENNReal.ofReal r) W := by
  have hr' : ENNReal.ofReal (r / (r - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (div_pos (by linarith) (by linarith))).ne'
  set s := schattenNorm (ENNReal.ofReal r) W
  rcases (schattenNorm_nonneg (ENNReal.ofReal r) W).eq_or_lt with hs | hs
  · -- `‖W‖_{S_r} = 0`: take `Z = 0`
    refine ⟨0, Matrix.PosSemidef.zero, by rw [schattenNorm_zero hr']; exact zero_le_one, ?_⟩
    rw [Matrix.mul_zero, Matrix.trace_zero]
    exact hs
  · -- otherwise the normalized norming element `Z = normingElement r W / ‖W‖_{S_r}^{r−1}`
    have hN : (normingElement r W).PosSemidef :=
      posSemidef_cfc fun t ht =>
        mul_nonneg (sign_nonneg_of_nonneg (spectrum_nonneg_of_posSemidef hW ht))
          (Real.rpow_nonneg (abs_nonneg _) _)
    have hsr : 0 < s ^ (r - 1) := Real.rpow_pos_of_pos hs _
    refine ⟨(s ^ (r - 1))⁻¹ • normingElement r W, hN.smul (inv_nonneg.mpr hsr.le), ?_, ?_⟩
    · rw [schattenNorm_smul hr', schattenNorm_normingElement hW.isHermitian hr,
        abs_of_pos (inv_pos.mpr hsr), inv_mul_cancel₀ hsr.ne']
    · rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_normingElement hW.isHermitian hr,
        smul_eq_mul, ← div_eq_inv_mul, ← Real.rpow_sub hs, sub_sub_cancel, Real.rpow_one]

/-- The triangle inequality (Jensen's inequality) for the `S_r` norm on positive semidefinite
matrices, from duality: `‖Σ_i W_i‖_{S_r} ≤ Σ_i ‖W_i‖_{S_r}`, `r ≥ 1`. -/
theorem schattenNorm_sum_le_of_posSemidef {ι : Type*} (s : Finset ι) {W : ι → Matrix n n ℝ}
    (hW : ∀ i ∈ s, (W i).PosSemidef) {r : ℝ} (hr : 1 ≤ r) :
    schattenNorm (ENNReal.ofReal r) (∑ i ∈ s, W i) ≤
      ∑ i ∈ s, schattenNorm (ENNReal.ofReal r) (W i) := by
  have hS : (∑ i ∈ s, W i).PosSemidef := Matrix.posSemidef_sum s hW
  rcases hr.eq_or_lt with rfl | hr
  · -- `r = 1`: the `S_1` norm of a positive semidefinite matrix is its trace
    refine le_of_eq ?_
    rw [schattenNorm_one_of_posSemidef hS, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun i hi => (schattenNorm_one_of_posSemidef (hW i hi)).symm
  · -- `r > 1`: duality
    obtain ⟨Z, hZ, hZ1, hWZ⟩ := exists_posSemidef_trace_mul_eq hS hr
    rw [← hWZ, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact (trace_mul_le_of_posSemidef (hW i hi) hZ hr).trans
      (mul_le_of_le_one_right (schattenNorm_nonneg _ _) hZ1)

end BanachProbability
