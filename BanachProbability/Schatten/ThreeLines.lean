module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Hadamard
import BanachProbability.Schatten.Block
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The three lines theorem for Schatten norms

* `complexSchattenNorm_le_of_verticalStrip`: if `Ψ` is a bounded continuous function on the strip
  `0 ≤ Re z ≤ 1` with values in the complex `n × n` matrices, analytic inside, with
  `‖Ψ (iy)‖_{S_{p₀}} ≤ M₀` and `‖Ψ (1 + iy)‖_{S_{p₁}} ≤ M₁`, then
  `‖Ψ (z)‖_{S_r} ≤ M₀^{1 − Re z} M₁^{Re z}`, `1/r = (1 − Re z)/p₀ + Re z/p₁`.
* `lpNorm_complexSchattenNorm_le_of_verticalStrip`: the same for functions on the sign cube and the
  norms of `L^p (Ω; S_p)`.
* `polarPower r A w = U (Δ / ‖A‖_{S_r})^w`, `A = U Δ` the polar decomposition: an entire function of
  `w`, with norm at most one in `S_p` on the line `Re w = r/p`.

Sources: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, pp. 166–167: the first
statement is quoted there, p. 167, from I. C. Gohberg and M. G. Krein, *Introduction to the theory
of linear nonselfadjoint operators in Hilbert space* (Moscow, 1965), §13; the second is Proposition
1.2, deduced from the first by block diagonal operators. The first statement is proved by the
argument of D. Sutter, M. Berta and M. Tomamichel, *Multivariate trace inequalities*, Comm. Math.
Phys. 352 (2017) 37–58, Theorem 3.1 and its proof in Appendix D (p. 6 and pp. 15–16 of the arXiv
version, arXiv:1604.03023), with Hadamard's three lines theorem in place of Hirschman's sharper
form: the polar decomposition of `Ψ (θ)` gives an analytic family of norming operators `X (z)`, and
the three lines theorem is applied to `g (z) = tr (X (z)ᴴ Ψ (z))`.

Here the matrices have a fixed finite size, and the exponents `p₀`, `p₁` are finite, in either order
(Tomczak-Jaegermann has `1 ≤ p₀ < p₁ ≤ ∞`). Boundedness of `Ψ` is not among the hypotheses quoted by
Tomczak-Jaegermann, but it is needed: `Ψ (z) = exp (exp (iπ (z − 1/2)))` has modulus `1` on both
lines and `Ψ (1/2) = e`. Here `Ψ` is bounded in the sense that its entries are, and the boundedness
of `g` is obtained from bounds for the entries of `X` and `Ψ`; Sutter–Berta–Tomamichel assume that
`‖Ψ (z)‖_{S_{p_{Re z}}}` is bounded, and obtain it from Hölder's inequality (92). They consider a
point `θ ∈ (0, 1)`; for a point `θ + iy` of the closed strip the exponents of the norming operators
are translated by `iy`. The polar decomposition is written with a singular value decomposition, see
`polarPower`.
-/

@[expose] public section

open Complex Complex.HadamardThreeLines
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The interpolated exponents -/

/-- `1/p(z) = (1 − z)/p₀ + z/p₁` (Tomczak-Jaegermann (1974), pp. 166 and 178). -/
noncomputable def interpExponent (p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  (1 - z) / p₀ + z / p₁

/-- `Re (1/p(z)) = (1 − Re z)/p₀ + Re z/p₁`. -/
theorem re_interpExponent (p₀ p₁ : ℝ) (z : ℂ) :
    (interpExponent p₀ p₁ z).re = (1 - z.re) / p₀ + z.re / p₁ := by
  rw [interpExponent, Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sub_re,
    Complex.one_re]

/-- For real `z = θ` the number `1/p(θ)` is real. -/
theorem interpExponent_ofReal (p₀ p₁ θ : ℝ) :
    interpExponent p₀ p₁ θ = ((1 - θ) / p₀ + θ / p₁ : ℝ) := by
  rw [interpExponent]
  push_cast
  rfl

/-- `1/p(z)` is an affine function of `z`. -/
theorem differentiable_interpExponent (p₀ p₁ : ℝ) : Differentiable ℂ (interpExponent p₀ p₁) := by
  unfold interpExponent
  fun_prop

/-- `1/p(θ) > 0` for `0 ≤ θ ≤ 1`. -/
private theorem interp_pos {p₀ p₁ θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 < (1 - θ) / p₀ + θ / p₁ := by
  rcases h0.eq_or_lt with rfl | h
  · simpa using hp₀
  · exact add_pos_of_nonneg_of_pos (div_nonneg (sub_nonneg.2 h1) hp₀.le) (div_pos h hp₁)

/-- `1/p(θ) ≤ 1` for `0 ≤ θ ≤ 1`, if `p₀, p₁ ≥ 1`. -/
private theorem interp_le_one {p₀ p₁ θ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : (1 - θ) / p₀ + θ / p₁ ≤ 1 :=
  (add_le_add (div_le_self (sub_nonneg.2 h1) hp₀) (div_le_self h0 hp₁)).trans_eq
    (sub_add_cancel 1 θ)

/-! ### The powers of the polar decomposition -/

section PolarPower

/-- The numbers `(s_i / ‖A‖_{S_r})^w`, `0` for `s_i = 0`, where `s_i` are the singular values of
`A`. -/
noncomputable def polarPowerCoeff (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) (i : n) : ℂ :=
  if complexSingularValue A i = 0 then 0 else Complex.exp (w * (Real.log
    (complexSingularValue A i / complexSchattenNorm (ENNReal.ofReal r) A) : ℝ))

/-- If `A a_i = s_i a'_i` is a singular value decomposition of `A`, which is chosen, then
`polarPower r A w` is the operator `a_i ↦ (s_i / ‖A‖_{S_r})^w a'_i`, `0` on the kernel of `A`, for
`w ∈ ℂ`. In terms of the polar decomposition `A = U Δ` it is `U (Δ / ‖A‖_{S_r})^w`. -/
noncomputable def polarPower (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) : Matrix n n ℂ :=
  (exists_eq_unitary_mul_diagonal_mul A).choose * Matrix.diagonal (polarPowerCoeff r A w) *
    ((exists_eq_unitary_mul_diagonal_mul A).choose_spec.2.choose)ᴴ

/-- The singular value decomposition in the definition of `polarPower`. -/
private theorem exists_polarPower_eq (r : ℝ) (A : Matrix n n ℂ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ V ∈ Matrix.unitaryGroup n ℂ,
      A = U * Matrix.diagonal (fun i => (complexSingularValue A i : ℂ)) * Vᴴ ∧
      ∀ w, polarPower r A w = U * Matrix.diagonal (polarPowerCoeff r A w) * Vᴴ :=
  have h := (exists_eq_unitary_mul_diagonal_mul A).choose_spec
  ⟨_, h.1, _, h.2.choose_spec.1, h.2.choose_spec.2, fun _ => rfl⟩

/-- `s_i ≤ ‖A‖_{S_r}`. -/
private theorem complexSingularValue_le {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) (i : n) :
    complexSingularValue A i ≤ complexSchattenNorm (ENNReal.ofReal r) A := by
  rw [← Real.rpow_le_rpow_iff (complexSingularValue_nonneg A i) (complexSchattenNorm_nonneg _ _) hr,
    complexSchattenNorm_ofReal_rpow hr]
  exact Finset.single_le_sum (f := fun i => complexSingularValue A i ^ r)
    (fun i _ => Real.rpow_nonneg (complexSingularValue_nonneg A i) r) (Finset.mem_univ i)

/-- `|(s_i / ‖A‖_{S_r})^w| = (s_i / ‖A‖_{S_r})^{Re w}` if `s_i ≠ 0`. -/
private theorem norm_polarPowerCoeff {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) (w : ℂ) {i : n}
    (hi : complexSingularValue A i ≠ 0) : ‖polarPowerCoeff r A w i‖ =
      (complexSingularValue A i / complexSchattenNorm (ENNReal.ofReal r) A) ^ w.re := by
  have hs := (complexSingularValue_nonneg A i).lt_of_ne' hi
  rw [polarPowerCoeff, ite_eq_right hi, Complex.norm_exp, Complex.re_mul_ofReal,
    Real.rpow_def_of_pos (div_pos hs (hs.trans_le (complexSingularValue_le hr A i))), mul_comm]

/-- `|(s_i / ‖A‖_{S_r})^w| ≤ 1` on the half plane `Re w ≥ 0`. -/
private theorem norm_polarPowerCoeff_le_one {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) {w : ℂ}
    (hw : 0 ≤ w.re) (i : n) : ‖polarPowerCoeff r A w i‖ ≤ 1 := by
  by_cases hi : complexSingularValue A i = 0
  · rw [polarPowerCoeff, ite_eq_left hi, norm_zero]
    exact zero_le_one
  · have hC0 := complexSchattenNorm_nonneg (ENNReal.ofReal r) A
    rw [norm_polarPowerCoeff hr A w hi]
    exact Real.rpow_le_one (div_nonneg (complexSingularValue_nonneg A i) hC0)
      (div_le_one_of_le₀ (complexSingularValue_le hr A i) hC0) hw

/-- The singular values of `U (Δ / ‖A‖_{S_r})^w` are the numbers `|(s_i / ‖A‖_{S_r})^w|`. -/
private theorem complexSchattenNorm_polarPower {p : ℝ} (hp : 0 < p) (r : ℝ) (A : Matrix n n ℂ)
    (w : ℂ) : complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) =
      (∑ i, ‖polarPowerCoeff r A w i‖ ^ p) ^ (1 / p) := by
  obtain ⟨U, hU, V, hV, -, h⟩ := exists_polarPower_eq r A
  rw [h, complexSchattenNorm_unitary_mul_diagonal_mul hp hU hV]

/-- On the line `Re w = r / p` the norm is (at most, if `A = 0`) one:
`‖U (Δ / ‖A‖_{S_r})^w‖_{S_p} ≤ 1` (Sutter–Berta–Tomamichel (2017), (91)). -/
theorem complexSchattenNorm_polarPower_le_one {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (A : Matrix n n ℂ) {w : ℂ} (hw : w.re = r / p) :
    complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) ≤ 1 := by
  set C := complexSchattenNorm (ENNReal.ofReal r) A with hC
  have hC0 : 0 ≤ C := complexSchattenNorm_nonneg _ _
  have hi : ∀ i, ‖polarPowerCoeff r A w i‖ ^ p = complexSingularValue A i ^ r / C ^ r := fun i => by
    have hs := complexSingularValue_nonneg A i
    by_cases h : complexSingularValue A i = 0
    · rw [polarPowerCoeff, ite_eq_left h, norm_zero, h, Real.zero_rpow hp.ne',
        Real.zero_rpow hr.ne', zero_div]
    · rw [norm_polarPowerCoeff hr A w h, hw, ← hC, ← Real.rpow_mul (div_nonneg hs hC0),
        div_mul_cancel₀ _ hp.ne', Real.div_rpow hs hC0]
  rw [complexSchattenNorm_polarPower hp, Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_div,
    ← complexSchattenNorm_ofReal_rpow hr, ← hC]
  exact Real.rpow_le_one (div_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC0 _))
    (div_self_le_one _) (by positivity)

/-- `‖U (Δ / ‖A‖_{S_r})^w‖_{S_p} ≤ n^{1/p}` on the half plane `Re w ≥ 0`, for all `0 < p < ∞`, as
the `n` singular values are at most one. -/
private theorem complexSchattenNorm_polarPower_le_card {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (A : Matrix n n ℂ) {w : ℂ} (hw : 0 ≤ w.re) :
    complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) ≤
      (Fintype.card n : ℝ) ^ (1 / p) := by
  rw [complexSchattenNorm_polarPower hp]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) p) ?_
    (by positivity)
  exact (Finset.sum_le_sum fun i _ => Real.rpow_le_one (norm_nonneg _)
    (norm_polarPowerCoeff_le_one hr A hw i) hp.le).trans_eq (by simp)

/-- The entries of `U (Δ / ‖A‖_{S_r})^w` are entire functions of `w`. -/
theorem differentiable_polarPower (r : ℝ) (A : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun w => polarPower r A w i j := by
  obtain ⟨U, -, V, -, -, h⟩ := exists_polarPower_eq r A
  have hc : ∀ k, Differentiable ℂ fun w => polarPowerCoeff r A w k := fun k => by
    unfold polarPowerCoeff
    split_ifs <;> fun_prop
  simp only [h, Matrix.mul_apply (M := U * _), Matrix.mul_diagonal]
  fun_prop

/-- The entries of `U (Δ / ‖A‖_{S_r})^w` have modulus at most `n` on the half plane `Re w ≥ 0`. -/
theorem norm_polarPower_apply_le {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) {w : ℂ} (hw : 0 ≤ w.re)
    (i j : n) : ‖polarPower r A w i j‖ ≤ Fintype.card n := by
  obtain ⟨U, hU, V, hV, -, h⟩ := exists_polarPower_eq r A
  rw [h, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  refine (norm_sum_le _ _).trans
    ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun k _ => ?_).trans_eq (by simp))
  rw [norm_mul, norm_mul, norm_star]
  exact (mul_le_of_le_one_right (by positivity) (entry_norm_bound_of_unitary hV j k)).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (norm_polarPowerCoeff_le_one hr A hw k)).trans
      (entry_norm_bound_of_unitary hU i k))

/-- `tr ((U (Δ / ‖A‖_{S_r})^{r − 1})ᴴ A) = ‖A‖_{S_r}` (Sutter–Berta–Tomamichel (2017), (93)). -/
private theorem trace_conjTranspose_polarPower_mul {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    ((polarPower r A ((r - 1 : ℝ) : ℂ))ᴴ * A).trace =
      (complexSchattenNorm (ENNReal.ofReal r) A : ℂ) := by
  obtain ⟨U, hU, V, hV, hA, h⟩ := exists_polarPower_eq r A
  set C := complexSchattenNorm (ENNReal.ofReal r) A with hC
  have e : (polarPower r A ((r - 1 : ℝ) : ℂ))ᴴ * A =
      V * Matrix.diagonal (fun i => star (polarPowerCoeff r A ((r - 1 : ℝ) : ℂ) i) *
        (complexSingularValue A i : ℂ)) * Vᴴ := by
    rw [← conjTranspose_unitary_mul_diagonal_mul hU, ← h, ← hA]
  -- the terms of the trace are `(s_i / C)^{r − 1} s_i = C s_i^r / C^r`
  have hi : ∀ i, star (polarPowerCoeff r A ((r - 1 : ℝ) : ℂ) i) * (complexSingularValue A i : ℂ) =
      ((complexSingularValue A i ^ r * (C / C ^ r) : ℝ) : ℂ) := fun i => by
    by_cases h0 : complexSingularValue A i = 0
    · rw [h0, Real.zero_rpow hr.ne', zero_mul, Complex.ofReal_zero, mul_zero]
    · have hs := (complexSingularValue_nonneg A i).lt_of_ne' h0
      have hC0 : 0 < C := hs.trans_le (complexSingularValue_le hr A i)
      rw [polarPowerCoeff, ite_eq_right h0, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        ← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← hC, mul_comm (r - 1),
        ← Real.rpow_def_of_pos (div_pos hs hC0), Real.rpow_sub_one (div_pos hs hC0).ne',
        Real.div_rpow hs.le hC0.le]
      congr 1
      field_simp
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.1 hV, Matrix.one_mul, Matrix.trace_diagonal,
    Finset.sum_congr rfl fun i _ => hi i, ← Complex.ofReal_sum, ← Finset.sum_mul,
    ← complexSchattenNorm_ofReal_rpow hr, ← hC]
  congr 1
  rcases (complexSchattenNorm_nonneg (ENNReal.ofReal r) A).eq_or_lt with h0 | h0
  · rw [hC, ← h0, zero_div, mul_zero]
  · rw [mul_div_cancel₀ _ (Real.rpow_pos_of_pos h0 r).ne']

/-- `‖A‖_{S_r} U (Δ / ‖A‖_{S_r}) = A`. -/
theorem smul_polarPower_one {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    (complexSchattenNorm (ENNReal.ofReal r) A : ℂ) • polarPower r A 1 = A := by
  obtain ⟨U, -, V, -, hA, h⟩ := exists_polarPower_eq r A
  have hi : (complexSchattenNorm (ENNReal.ofReal r) A : ℂ) • polarPowerCoeff r A 1 =
      fun i => (complexSingularValue A i : ℂ) := funext fun i => by
    by_cases h0 : complexSingularValue A i = 0
    · rw [Pi.smul_apply, polarPowerCoeff, ite_eq_left h0, h0, smul_zero, Complex.ofReal_zero]
    · have hs := (complexSingularValue_nonneg A i).lt_of_ne' h0
      have hC0 := hs.trans_le (complexSingularValue_le hr A i)
      rw [Pi.smul_apply, polarPowerCoeff, ite_eq_right h0, one_mul, ← Complex.ofReal_exp,
        Real.exp_log (div_pos hs hC0), smul_eq_mul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hC0.ne']
  rw [h, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul, hi, ← hA]

end PolarPower

/-! ### The three lines theorem for Schatten norms -/

/-- `|tr (X B)| ≤ ‖B‖_{S_1}` if the singular values of `X` are at most one, in the form
`‖X‖_{S_q} ≤ K^{1/q}`, `0 < q < ∞`: the limit `q → ∞` of Hölder's inequality. -/
private theorem norm_trace_mul_le_one {K : ℝ} (hK : 0 < K) {X : Matrix n n ℂ}
    (hX : ∀ q : ℝ, 0 < q → complexSchattenNorm (ENNReal.ofReal q) X ≤ K ^ (1 / q))
    (B : Matrix n n ℂ) :
    ‖(X * B).trace‖ ≤ complexSchattenNorm (ENNReal.ofReal 1) B := by
  have hB : ∀ t : ℝ, 0 < t → complexSchattenNorm (ENNReal.ofReal t) B =
      (∑ i, complexSingularValue B i ^ t) ^ (1 / t) := fun t ht => by
    rw [← complexSchattenNorm_ofReal_rpow ht, one_div,
      Real.rpow_rpow_inv (complexSchattenNorm_nonneg _ _) ht.ne']
  have hc : ContinuousAt (fun t : ℝ =>
      K ^ (1 - 1 / t) * (∑ i, complexSingularValue B i ^ t) ^ (1 / t)) 1 := by
    have h1 : ContinuousAt (fun t : ℝ => 1 / t) 1 := by
      simpa only [one_div] using continuousAt_inv₀ (one_ne_zero (α := ℝ))
    refine (continuousAt_const.rpow (continuousAt_const.sub h1) (Or.inl hK.ne')).mul
      (ContinuousAt.rpow ?_ h1 (Or.inr (by norm_num)))
    exact tendsto_finsetSum _ fun i _ => Real.continuousAt_const_rpow' one_ne_zero
  have h := ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t (ht : 1 < t) => by
      have hq := (Real.HolderConjugate.conjExponent ht).symm
      refine (norm_trace_mul_le hq X B).trans ?_
      rw [← hB t (zero_lt_one.trans ht), one_div, hq.symm.one_sub_inv, ← one_div]
      exact mul_le_mul_of_nonneg_right (hX _ hq.pos) (complexSchattenNorm_nonneg _ _))
  rwa [← hB 1 one_pos, div_one, sub_self, Real.rpow_zero, one_mul] at h

/-- Hölder's inequality for the norming operators `X = U (Δ / ‖A‖_{S_r})^w`, `Re w = r (1 − 1/p)`:
`|tr (Xᴴ B)| ≤ ‖B‖_{S_p}` (Sutter–Berta–Tomamichel (2017), (92)). -/
private theorem norm_trace_conjTranspose_polarPower_mul_le {p r : ℝ} (hp : 1 ≤ p) (hr : 0 < r)
    (A B : Matrix n n ℂ) {w : ℂ} (hw : w.re = r * (1 - 1 / p)) :
    ‖((polarPower r A w)ᴴ * B).trace‖ ≤ complexSchattenNorm (ENNReal.ofReal p) B := by
  rcases hp.eq_or_lt with rfl | hp
  · -- the dual exponent is `∞`
    rcases isEmpty_or_nonempty n with hn | hn
    · simpa [Matrix.trace] using complexSchattenNorm_nonneg _ B
    · refine norm_trace_mul_le_one (K := Fintype.card n) (Nat.cast_pos.2 Fintype.card_pos)
        (fun q hq => ?_) B
      rw [complexSchattenNorm_conjTranspose]
      exact complexSchattenNorm_polarPower_le_card hq hr A (by rw [hw]; simp)
  · have hq := (Real.HolderConjugate.conjExponent hp).symm
    refine (norm_trace_mul_le hq _ B).trans
      (mul_le_of_le_one_left (complexSchattenNorm_nonneg _ _) ?_)
    rw [complexSchattenNorm_conjTranspose]
    refine complexSchattenNorm_polarPower_le_one hq.pos hr A ?_
    rw [hw, one_div, hq.symm.one_sub_inv, div_eq_mul_inv]

private theorem diffContOnCl_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {S : Set ℂ}
    (h : ∀ i, DiffContOnCl ℂ (f i) S) : DiffContOnCl ℂ (fun z => ∑ i ∈ s, f i z) S :=
  ⟨DifferentiableOn.fun_sum fun i _ => (h i).1, continuousOn_finsetSum _ fun i _ => (h i).2⟩

omit [DecidableEq n] in
/-- For analytic families `X̄`, `Ψ`, the function `z ↦ tr (X (z)ᴴ Ψ (z))` is analytic. -/
private theorem diffContOnCl_trace_conjTranspose_mul {X Ψ : ℂ → Matrix n n ℂ} {S : Set ℂ}
    (hX : ∀ i j, DiffContOnCl ℂ (fun z => star (X z i j)) S)
    (hΨ : ∀ i j, DiffContOnCl ℂ (fun z => Ψ z i j) S) :
    DiffContOnCl ℂ (fun z => ((X z)ᴴ * Ψ z).trace) S := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact diffContOnCl_sum _ fun i => diffContOnCl_sum _ fun j => (hX j i).smul (hΨ j i)

omit [DecidableEq n] in
private theorem norm_trace_conjTranspose_mul_le {X B : Matrix n n ℂ} {a b : ℝ}
    (hX : ∀ i j, ‖X i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) :
    ‖(Xᴴ * B).trace‖ ≤ ∑ _i : n, ∑ _j : n, a * b := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  rw [norm_mul, norm_star]
  exact mul_le_mul (hX j i) (hB j i) (norm_nonneg _) ((norm_nonneg _).trans (hX j i))

/-- The exponent `w (ζ) = r (1 − 1/p(ζ − iy)) = r ((1 − ζ + iy)/q₀ + (ζ − iy)/q₁)`,
`1/q_μ = 1 − 1/p_μ`, of the norming operators, translated by `i y`. -/
private noncomputable def normingExponent (r p₀ p₁ y : ℝ) (ζ : ℂ) : ℂ :=
  r * (1 - interpExponent p₀ p₁ (ζ - y * I))

private theorem re_star_normingExponent (r p₀ p₁ y : ℝ) (ζ : ℂ) :
    (star (normingExponent r p₀ p₁ y ζ)).re = r * (1 - ((1 - ζ.re) / p₀ + ζ.re / p₁)) := by
  rw [← starRingEnd_apply, conj_re, normingExponent, Complex.re_ofReal_mul, Complex.sub_re,
    re_interpExponent]
  simp

/-- The norming operators `X (ζ) = U (Δ / C)^{w̄ (ζ)}`, `C = ‖A‖_{S_r}`, are anti-analytic. -/
private theorem differentiable_star_polarPower (r p₀ p₁ y : ℝ) (A : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun ζ => star (polarPower r A (star (normingExponent r p₀ p₁ y ζ)) i j) := by
  have h : Differentiable ℂ fun v => star (polarPower r A (star v) i j) := fun v =>
    differentiableAt_conj_conj_iff.2 (differentiable_polarPower r A i j _)
  have hw : Differentiable ℂ (normingExponent r p₀ p₁ y) :=
    (((differentiable_interpExponent p₀ p₁).comp (by fun_prop)).const_sub 1).const_mul _
  exact h.comp hw

/-- `w (θ + i y) = r − 1` if `1/r = (1 − θ)/p₀ + θ/p₁`. -/
private theorem normingExponent_self {r p₀ p₁ : ℝ} (hr0 : 0 < r) {z : ℂ}
    (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    normingExponent r p₀ p₁ z.im z = ((r - 1 : ℝ) : ℂ) := by
  have h1 : z - z.im * I = z.re := by
    rw [sub_eq_iff_eq_add, Complex.re_add_im]
  rw [normingExponent, h1, interpExponent_ofReal, ← hr, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, mul_sub, mul_one, mul_one_div_cancel hr0.ne']

/-- **The three lines theorem for Schatten norms** (Gohberg–Krein (1965), §13, as quoted by
Tomczak-Jaegermann (1974), p. 167; Sutter–Berta–Tomamichel (2017), Theorem 3.1). -/
theorem complexSchattenNorm_le_of_verticalStrip {p₀ p₁ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    {Ψ : ℂ → Matrix n n ℂ} (hΨ : ∀ i j, DiffContOnCl ℂ (fun z => Ψ z i j) (verticalStrip 0 1))
    (hb : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ∀ i j, ‖Ψ z i j‖ ≤ C) {M₀ M₁ : ℝ}
    (h₀ : ∀ y : ℝ, complexSchattenNorm (ENNReal.ofReal p₀) (Ψ (y * I)) ≤ M₀)
    (h₁ : ∀ y : ℝ, complexSchattenNorm (ENNReal.ofReal p₁) (Ψ (1 + y * I)) ≤ M₁) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) {r : ℝ} (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    complexSchattenNorm (ENNReal.ofReal r) (Ψ z) ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  have hr0 : 0 < r := one_div_pos.1 (hr ▸ interp_pos (by linarith) (by linarith) hz.1 hz.2)
  -- the norming operators `X (ζ)` are anti-analytic, so `g (ζ) = tr (X (ζ)ᴴ Ψ (ζ))` is analytic
  set w : ℂ → ℂ := normingExponent r p₀ p₁ z.im with hw
  set X : ℂ → Matrix n n ℂ := fun ζ => polarPower r (Ψ z) (star (w ζ))
  have hd : DiffContOnCl ℂ (fun ζ => ((X ζ)ᴴ * Ψ ζ).trace) (verticalStrip 0 1) :=
    diffContOnCl_trace_conjTranspose_mul
      (fun i j => (differentiable_star_polarPower r p₀ p₁ z.im (Ψ z) i j).diffContOnCl) hΨ
  have hwre : ∀ ζ, (star (w ζ)).re = r * (1 - ((1 - ζ.re) / p₀ + ζ.re / p₁)) :=
    re_star_normingExponent r p₀ p₁ z.im
  -- `g` is bounded, as the entries of `X` and of `Ψ` are
  have hB : BddAbove ((norm ∘ fun ζ => ((X ζ)ᴴ * Ψ ζ).trace) '' verticalClosedStrip 0 1) := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨∑ _i : n, ∑ _j : n, Fintype.card n * C, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    have hwζ : 0 ≤ (star (w ζ)).re :=
      (hwre ζ).symm ▸ mul_nonneg hr0.le (sub_nonneg.2 (interp_le_one hp₀ hp₁ hζ.1 hζ.2))
    exact norm_trace_conjTranspose_mul_le (norm_polarPower_apply_le hr0 (Ψ z) hwζ) (hC ζ hζ)
  -- `g (z) = ‖Ψ (z)‖_{S_r}`
  have hgz : ((X z)ᴴ * Ψ z).trace = (complexSchattenNorm (ENNReal.ofReal r) (Ψ z) : ℂ) := by
    have hwz : star (w z) = ((r - 1 : ℝ) : ℂ) := by
      rw [hw, normingExponent_self hr0 hr, ← starRingEnd_apply, Complex.conj_ofReal]
    change ((polarPower r (Ψ z) (star (w z)))ᴴ * Ψ z).trace = _
    rw [hwz, trace_conjTranspose_polarPower_mul hr0]
  -- the three lines theorem, with `|g (μ + iy)| ≤ ‖Ψ (μ + iy)‖_{S_{p_μ}} ≤ M_μ`
  have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' _ hz hd hB (a := M₀) (b := M₁)
    (fun ζ (hζ : ζ.re = 0) => ?_) (fun ζ (hζ : ζ.re = 1) => ?_)
  · rwa [hgz, Complex.norm_real, Real.norm_of_nonneg (complexSchattenNorm_nonneg _ _)] at h
  · have e : ζ = ζ.im * I := by
      rw [← Complex.re_add_im ζ, hζ]
      simp
    refine (norm_trace_conjTranspose_polarPower_mul_le hp₀ hr0 _ _ ?_).trans (e ▸ h₀ ζ.im)
    rw [hwre, hζ]
    ring
  · have e : ζ = 1 + ζ.im * I := by
      rw [← Complex.re_add_im ζ, hζ]
      simp
    refine (norm_trace_conjTranspose_polarPower_mul_le hp₁ hr0 _ _ ?_).trans (e ▸ h₁ ζ.im)
    rw [hwre, hζ]
    ring

/-- `‖2^{−N/p} diag (X (ε))‖_{S_p} = ‖X‖_{L^p (Ω; S_p)}` (Tomczak-Jaegermann (1974), pp. 166–167),
for scalars of modulus `2^{−N/p}`. -/
private theorem complexSchattenNorm_smul_blockDiagonal {p : ℝ} (hp : 0 < p) {c : ℂ}
    (hc : ‖c‖ = (2 : ℝ) ^ (-(N * (1 / p)))) (X : (Fin N → Bool) → Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (c • Matrix.blockDiagonal X) =
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) p X := by
  rw [complexSchattenNorm_smul (ENNReal.ofReal_pos.2 hp).ne', complexSchattenNorm_blockDiagonal hp,
    scb_lpNorm_eq_sum (complexSchattenNorm_nonneg _), hc, Real.rpow_neg zero_le_two,
    Real.rpow_mul zero_le_two, Real.rpow_natCast, ← div_eq_inv_mul]

/-- `|2^{−N/p(z)}| = 2^{−N Re (1/p(z))}`. -/
private theorem norm_two_cpow (N : ℕ) (p₀ p₁ : ℝ) (z : ℂ) :
    ‖((2 : ℝ) : ℂ) ^ (-(N * interpExponent p₀ p₁ z))‖ =
      (2 : ℝ) ^ (-(N * ((1 - z.re) / p₀ + z.re / p₁))) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re, ← Complex.ofReal_natCast,
    Complex.re_ofReal_mul, re_interpExponent]

/-- Tomczak-Jaegermann (1974), Proposition 1.2, p. 166: the three lines theorem for the norms of
`L^p (Ω; S_p)`, `Ω` the sign cube. (Every function on the cube is a combination of Walsh functions,
so the functions `Σ φ_n (z) w_n` of the source are arbitrary functions on the cube.) -/
theorem lpNorm_complexSchattenNorm_le_of_verticalStrip {p₀ p₁ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    {Φ : ℂ → (Fin N → Bool) → Matrix n n ℂ}
    (hΦ : ∀ ε i j, DiffContOnCl ℂ (fun z => Φ z ε i j) (verticalStrip 0 1))
    (hb : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ∀ ε i j, ‖Φ z ε i j‖ ≤ C) {M₀ M₁ : ℝ}
    (h₀ : ∀ y : ℝ, SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₀)) p₀ (Φ (y * I)) ≤ M₀)
    (h₁ : ∀ y : ℝ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₁)) p₁ (Φ (1 + y * I)) ≤ M₁) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) {r : ℝ} (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal r)) r (Φ z) ≤
      M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  have hp₀' : 0 < p₀ := by linarith
  have hp₁' : 0 < p₁ := by linarith
  have hr0 : 0 < r := one_div_pos.1 (hr ▸ interp_pos hp₀' hp₁' hz.1 hz.2)
  -- the scalars `2^{−N/p(z)}`
  set c : ℂ → ℂ := fun ζ => ((2 : ℝ) : ℂ) ^ (-(N * interpExponent p₀ p₁ ζ)) with hc
  set Ψ : ℂ → Matrix (n × (Fin N → Bool)) (n × (Fin N → Bool)) ℂ := fun ζ =>
    c ζ • Matrix.blockDiagonal (Φ ζ) with hΨ
  have hΨa : ∀ ζ i j, Ψ ζ i j = c ζ * if i.2 = j.2 then Φ ζ i.2 i.1 j.1 else 0 := fun ζ i j => rfl
  rw [← complexSchattenNorm_smul_blockDiagonal hr0 (c := c z) (by rw [hc, norm_two_cpow, hr])]
  refine complexSchattenNorm_le_of_verticalStrip hp₀ hp₁ (Ψ := Ψ) (fun i j => ?_) ?_ (fun y => ?_)
    (fun y => ?_) hz hr
  · -- `Ψ` is analytic
    have hd : DiffContOnCl ℂ c (verticalStrip 0 1) := Differentiable.diffContOnCl
      ((((differentiable_interpExponent p₀ p₁).const_mul _).neg).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 two_ne_zero)))
    simp only [hΨa]
    by_cases h : i.2 = j.2
    · simp only [ite_eq_left h]
      exact hd.smul (hΦ _ _ _)
    · simp only [ite_eq_right h, mul_zero]
      exact diffContOnCl_const
  · -- `Ψ` is bounded
    obtain ⟨C, hC⟩ := hb
    refine ⟨|C|, fun ζ hζ i j => ?_⟩
    rw [hΨa, norm_mul, hc, norm_two_cpow, ← one_mul |C|]
    refine mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (neg_nonpos.2
      (mul_nonneg (Nat.cast_nonneg _) (interp_pos hp₀' hp₁' hζ.1 hζ.2).le))) ?_ (norm_nonneg _)
      zero_le_one
    split_ifs
    · exact (hC ζ hζ _ _ _).trans (le_abs_self C)
    · exact norm_zero.trans_le (abs_nonneg C)
  · refine (complexSchattenNorm_smul_blockDiagonal hp₀' ?_ _).trans_le (h₀ y)
    rw [hc, norm_two_cpow]
    simp
  · refine (complexSchattenNorm_smul_blockDiagonal hp₁' ?_ _).trans_le (h₁ y)
    rw [hc, norm_two_cpow]
    simp

end BanachProbability
