module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Complex.Hadamard
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
of trace classes `S_p`*, Studia Math. 50 (1974), pp. 166–167: the first statement is quoted there
from I. C. Gohberg and M. G. Krein, *Introduction to the theory of linear nonselfadjoint operators*
(Moscow, 1965), §13; the second is Proposition 1.2, deduced from the first by block diagonal
operators. Boundedness of `Ψ` is not among the hypotheses quoted on pp. 166–167, but it is needed:
`Ψ (z) = exp (exp (iπ (z − 1/2)))` has modulus `1` on both lines and `Ψ (1/2) = e`. The exponents
are finite here, in either order; the source has `1 ≤ p₀ < p₁ ≤ ∞`. The first statement is proved
by the argument of D. Sutter, M. Berta and M. Tomamichel, *Multivariate trace inequalities*, Comm.
Math. Phys. 352 (2017), arXiv:1604.03023, Theorem 3.1, p. 6, and Appendix D, pp. 15–16, with
Hadamard's three lines theorem in place of Hirschman's sharper form: the polar decomposition of
`Ψ (θ)` gives an analytic family of norming operators `X (z)`, and the three lines theorem is
applied to `tr (X (z) Ψ (z))`.

Here the matrices have a fixed finite size, the exponents `p₀`, `p₁` are finite, and `Ψ` is bounded
in the sense that its entries are. Sutter–Berta–Tomamichel consider a point `θ ∈ (0, 1)`; for a
point `θ + iy` of the closed strip the exponents of the norming operators are translated by `iy`.
The polar decomposition is written with the matrix `V` of eigenvectors of `Ψ (θ)ᴴ Ψ (θ)`, see
`polarPower`.
-/

@[expose] public section

open Complex Complex.HadamardThreeLines
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The powers of the polar decomposition -/

section PolarPower

/-- If `A = U Δ` is the polar decomposition, `polarPower r A w = U (Δ / ‖A‖_{S_r})^w`, `0` on the
kernel of `A`, for `w ∈ ℂ`. With `Aᴴ A = V diag (s_i²) Vᴴ`, `s_i` the singular values of `A`, this
is `A V diag (s_i⁻¹ (s_i / ‖A‖_{S_r})^w) Vᴴ` (`s_i⁻¹ = 0` for `s_i = 0`), which is taken as the
definition. -/
noncomputable def polarPower (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) : Matrix n n ℂ :=
  A * ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary *
    Matrix.diagonal (fun i => (complexSingularValue A i : ℂ)⁻¹ * Complex.exp (w * (Real.log
      (complexSingularValue A i / complexSchattenNorm (ENNReal.ofReal r) A) : ℝ))) *
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ)ᴴ)

/-- The numbers `s_i⁻¹ (s_i / ‖A‖_{S_r})^w`. -/
private noncomputable def polarPowerCoeff (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) (i : n) : ℂ :=
  (complexSingularValue A i : ℂ)⁻¹ * Complex.exp (w * (Real.log
    (complexSingularValue A i / complexSchattenNorm (ENNReal.ofReal r) A) : ℝ))

private theorem polarPower_eq (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) :
    polarPower r A w = A * ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary *
      Matrix.diagonal (polarPowerCoeff r A w) *
      ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ)ᴴ) :=
  rfl

private theorem singularValue_nonneg' (A : Matrix n n ℂ) (i : n) : 0 ≤ complexSingularValue A i :=
  Real.sqrt_nonneg _

/-- `‖A‖_{S_r}^r = Σ s_i^r`. -/
private theorem complexSchattenNorm_ofReal_rpow {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal r) A ^ r = ∑ i, complexSingularValue A i ^ r := by
  rw [complexSchattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le, one_div,
    Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg' A i) _)
      hr.ne']

/-- `s_i ≤ ‖A‖_{S_r}`. -/
private theorem complexSingularValue_le {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) (i : n) :
    complexSingularValue A i ≤ complexSchattenNorm (ENNReal.ofReal r) A := by
  rw [← Real.rpow_le_rpow_iff (singularValue_nonneg' A i) (complexSchattenNorm_nonneg _ _) hr,
    complexSchattenNorm_ofReal_rpow hr]
  exact Finset.single_le_sum (f := fun i => complexSingularValue A i ^ r)
    (fun i _ => Real.rpow_nonneg (singularValue_nonneg' A i) r) (Finset.mem_univ i)

/-- `(A V diag (c) Vᴴ)ᴴ (A V diag (d) Vᴴ) = V diag (c̄_i s_i² d_i) Vᴴ` if `Aᴴ A = V diag (s_i²) Vᴴ`,
for the matrix `V` of eigenvectors. -/
private theorem conjTranspose_mul_diagonal_mul (A : Matrix n n ℂ) (c d : n → ℂ) {V : Matrix n n ℂ}
    (hV : V = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary) :
    (A * (V * Matrix.diagonal c * Vᴴ))ᴴ * (A * (V * Matrix.diagonal d * Vᴴ)) =
      V * Matrix.diagonal (fun i => star (c i) * (complexSingularValue A i ^ 2 : ℝ) * d i) *
        Vᴴ := by
  have hVV : Vᴴ * V = 1 := hV ▸ Unitary.coe_star_mul_self _
  -- `Aᴴ A = V diag (s²) Vᴴ`
  have h : Aᴴ * A = V * Matrix.diagonal (fun i => ((complexSingularValue A i ^ 2 : ℝ) : ℂ)) *
      Vᴴ := by
    have hs : ∀ i, complexSingularValue A i ^ 2 =
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i := fun i =>
      Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
    simp only [hs, hV]
    exact eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose _
  have hd : Matrix.diagonal (fun i => star (c i) * (complexSingularValue A i ^ 2 : ℝ) * d i) =
      Matrix.diagonal (star c) *
        Matrix.diagonal (fun i => ((complexSingularValue A i ^ 2 : ℝ) : ℂ)) *
        Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rfl
  rw [hd, Matrix.conjTranspose_mul, Matrix.mul_assoc _ Aᴴ, ← Matrix.mul_assoc Aᴴ A, h,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul]

/-- `‖A V diag (c) Vᴴ‖_{S_p} = (Σ (|c_i| s_i)^p)^{1/p}`, for `c_i = s_i⁻¹ (s_i / ‖A‖_{S_r})^w`. -/
private theorem complexSchattenNorm_polarPower {p : ℝ} (hp : 0 < p) (r : ℝ) (A : Matrix n n ℂ)
    (w : ℂ) : complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) =
      (∑ i, (‖polarPowerCoeff r A w i‖ * complexSingularValue A i) ^ p) ^ (1 / p) := by
  have hterm : ∀ i, 0 ≤ ‖polarPowerCoeff r A w i‖ * complexSingularValue A i := fun i =>
    mul_nonneg (norm_nonneg _) (singularValue_nonneg' A i)
  have hsum : 0 ≤ ∑ i, (‖polarPowerCoeff r A w i‖ * complexSingularValue A i) ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hterm i) p
  have hV := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary.2
  -- `‖B‖_{S_p}² = ‖Bᴴ B‖_{S_{p/2}}`
  rw [← sq_eq_sq₀ (complexSchattenNorm_nonneg _ _) (Real.rpow_nonneg hsum _),
    ← complexSchattenNorm_conjTranspose_mul_self (ENNReal.ofReal_pos.2 hp).ne', polarPower_eq,
    conjTranspose_mul_diagonal_mul A _ _ rfl, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_div_of_pos two_pos,
    complexSchattenNorm_unitary_mul_diagonal_mul (half_pos hp) hV hV,
    ← Real.rpow_mul_natCast hsum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
      show ‖polarPowerCoeff r A w i‖ * complexSingularValue A i ^ 2 * ‖polarPowerCoeff r A w i‖ =
        (‖polarPowerCoeff r A w i‖ * complexSingularValue A i) ^ (2 : ℕ) by ring,
      ← Real.rpow_natCast_mul (hterm i), Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero]
  · rw [one_div_div, Nat.cast_ofNat, one_div, div_eq_mul_inv, mul_comm]

/-- `|s_i⁻¹ (s_i / ‖A‖_{S_r})^w| s_i = (s_i / ‖A‖_{S_r})^{Re w}` if `s_i ≠ 0`. -/
private theorem norm_polarPowerCoeff_mul {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) (w : ℂ) {i : n}
    (hi : complexSingularValue A i ≠ 0) :
    ‖polarPowerCoeff r A w i‖ * complexSingularValue A i =
      (complexSingularValue A i / complexSchattenNorm (ENNReal.ofReal r) A) ^ w.re := by
  have hs : 0 < complexSingularValue A i := (singularValue_nonneg' A i).lt_of_ne' hi
  have hC := hs.trans_le (complexSingularValue_le hr A i)
  rw [polarPowerCoeff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le,
    Complex.norm_exp, Complex.re_mul_ofReal, Real.rpow_def_of_pos (div_pos hs hC), mul_right_comm,
    inv_mul_cancel₀ hi, one_mul, mul_comm]

/-- On the line `Re w = r / p` the norm is (at most, if `A = 0`) one:
`‖U (Δ / ‖A‖_{S_r})^w‖_{S_p} ≤ 1` (Sutter–Berta–Tomamichel (2017), (91)). -/
theorem complexSchattenNorm_polarPower_le_one {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (A : Matrix n n ℂ) {w : ℂ} (hw : w.re = r / p) :
    complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) ≤ 1 := by
  set C := complexSchattenNorm (ENNReal.ofReal r) A with hC
  have hC0 : 0 ≤ C := complexSchattenNorm_nonneg _ _
  have hi : ∀ i, (‖polarPowerCoeff r A w i‖ * complexSingularValue A i) ^ p =
      complexSingularValue A i ^ r / C ^ r := fun i => by
    rcases eq_or_ne (complexSingularValue A i) 0 with h | h
    · rw [h, mul_zero, Real.zero_rpow hp.ne', Real.zero_rpow hr.ne', zero_div]
    · rw [norm_polarPowerCoeff_mul hr A w h, hw, ← hC, ← Real.rpow_mul
        (div_nonneg (singularValue_nonneg' A i) hC0), div_mul_cancel₀ _ hp.ne',
        Real.div_rpow (singularValue_nonneg' A i) hC0]
  rw [complexSchattenNorm_polarPower hp, Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_div,
    ← complexSchattenNorm_ofReal_rpow hr, ← hC]
  exact Real.rpow_le_one (div_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC0 _))
    (div_self_le_one _) (by positivity)

/-- On the half plane `Re w ≥ 0` the singular values of `U (Δ / ‖A‖_{S_r})^w` are at most one. -/
private theorem complexSchattenNorm_polarPower_le_card {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (A : Matrix n n ℂ) {w : ℂ} (hw : 0 ≤ w.re) :
    complexSchattenNorm (ENNReal.ofReal p) (polarPower r A w) ≤
      (Fintype.card n : ℝ) ^ (1 / p) := by
  have hi : ∀ i, (‖polarPowerCoeff r A w i‖ * complexSingularValue A i) ^ p ≤ 1 := fun i => by
    rcases eq_or_ne (complexSingularValue A i) 0 with h | h
    · rw [h, mul_zero, Real.zero_rpow hp.ne']
      exact zero_le_one
    · have hC0 := complexSchattenNorm_nonneg (ENNReal.ofReal r) A
      have hd := div_nonneg (singularValue_nonneg' A i) hC0
      rw [norm_polarPowerCoeff_mul hr A w h]
      exact Real.rpow_le_one (Real.rpow_nonneg hd _) (Real.rpow_le_one hd
        (div_le_one_of_le₀ (complexSingularValue_le hr A i) hC0) hw) hp.le
  rw [complexSchattenNorm_polarPower hp]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
    (mul_nonneg (norm_nonneg _) (singularValue_nonneg' A i)) p) ?_ (by positivity)
  exact (Finset.sum_le_sum fun i _ => hi i).trans_eq (by simp)

/-- The entries of `U (Δ / ‖A‖_{S_r})^w`. -/
private theorem polarPower_apply (r : ℝ) (A : Matrix n n ℂ) (w : ℂ) (i j : n) :
    polarPower r A w i j = ∑ k,
      (A * (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ) i k *
        polarPowerCoeff r A w k *
        ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ)ᴴ k j := by
  rw [polarPower_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

/-- The entries of `U (Δ / ‖A‖_{S_r})^w` are entire functions of `w`. -/
theorem differentiable_polarPower (r : ℝ) (A : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun w => polarPower r A w i j := by
  simp only [polarPower_apply, polarPowerCoeff]
  fun_prop

/-- The entries of `U (Δ / ‖A‖_{S_r})^w` are bounded on the half plane `Re w ≥ 0`. -/
theorem exists_norm_polarPower_le {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    ∃ B : ℝ, ∀ w : ℂ, 0 ≤ w.re → ∀ i j, ‖polarPower r A w i j‖ ≤ B := by
  set V : Matrix n n ℂ :=
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ)
  have hc : ∀ w : ℂ, 0 ≤ w.re → ∀ k, ‖polarPowerCoeff r A w k‖ ≤ (complexSingularValue A k)⁻¹ :=
    fun w hw k => by
      have hs := singularValue_nonneg' A k
      have hC0 := complexSchattenNorm_nonneg (ENNReal.ofReal r) A
      rw [polarPowerCoeff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs,
        Complex.norm_exp, Complex.re_mul_ofReal]
      refine mul_le_of_le_one_right (inv_nonneg.2 hs) (Real.exp_le_one_iff.2 ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hw (Real.log_nonpos (div_nonneg hs hC0)
        (div_le_one_of_le₀ (complexSingularValue_le hr A k) hC0))
  obtain ⟨B, hB⟩ := Finite.bddAbove_range fun x : n × n =>
    ∑ k, ‖(A * V) x.1 k‖ * (complexSingularValue A k)⁻¹ * ‖Vᴴ k x.2‖
  refine ⟨B, fun w hw i j => le_trans ?_ (hB ⟨(i, j), rfl⟩)⟩
  rw [polarPower_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hc w hw k) (norm_nonneg _))
    (norm_nonneg _)

/-- `tr ((U (Δ / ‖A‖_{S_r})^{r − 1})ᴴ A) = ‖A‖_{S_r}` (Sutter–Berta–Tomamichel (2017), (93)). -/
private theorem trace_conjTranspose_polarPower_mul {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    ((polarPower r A ((r - 1 : ℝ) : ℂ))ᴴ * A).trace =
      (complexSchattenNorm (ENNReal.ofReal r) A : ℂ) := by
  set V : Matrix n n ℂ :=
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVV : Vᴴ * V = 1 := Unitary.coe_star_mul_self
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  set C := complexSchattenNorm (ENNReal.ofReal r) A with hC
  have h1 : (polarPower r A ((r - 1 : ℝ) : ℂ))ᴴ * A =
      (polarPower r A ((r - 1 : ℝ) : ℂ))ᴴ * (A * (V * Matrix.diagonal 1 * Vᴴ)) := by
    rw [Matrix.diagonal_one', Matrix.mul_one, hVV', Matrix.mul_one]
  rw [h1, polarPower_eq, conjTranspose_mul_diagonal_mul A _ _ rfl, ← hV, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hVV, Matrix.one_mul, Matrix.trace_diagonal]
  -- the terms are `s_i⁻¹ (s_i / C)^{r − 1} s_i² = C s_i^r / C^r`
  have hi : ∀ i, star (polarPowerCoeff r A ((r - 1 : ℝ) : ℂ) i) *
      (complexSingularValue A i ^ 2 : ℝ) * (1 : n → ℂ) i =
        ((complexSingularValue A i ^ r * (C / C ^ r) : ℝ) : ℂ) := fun i => by
    rw [polarPowerCoeff, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_mul, ← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Pi.one_apply, mul_one, ← hC]
    congr 1
    rcases eq_or_ne (complexSingularValue A i) 0 with h | h
    · rw [h, Real.zero_rpow hr.ne']
      ring
    · have hs : 0 < complexSingularValue A i := (singularValue_nonneg' A i).lt_of_ne' h
      have hC0 : 0 < C := hs.trans_le (complexSingularValue_le hr A i)
      rw [mul_comm (r - 1), ← Real.rpow_def_of_pos (div_pos hs hC0), Real.rpow_sub_one
        (div_pos hs hC0).ne', Real.div_rpow hs.le hC0.le]
      field_simp
  rw [Finset.sum_congr rfl fun i _ => hi i, ← Complex.ofReal_sum, ← Finset.sum_mul,
    ← complexSchattenNorm_ofReal_rpow hr, ← hC]
  congr 1
  rcases (complexSchattenNorm_nonneg (ENNReal.ofReal r) A).eq_or_lt with h | h
  · rw [hC, ← h, zero_div, mul_zero]
  · rw [mul_div_cancel₀ _ (Real.rpow_pos_of_pos h r).ne']

open scoped ComplexOrder in
/-- `‖A‖_{S_r} U (Δ / ‖A‖_{S_r}) = A`. -/
theorem smul_polarPower_one {r : ℝ} (hr : 0 < r) (A : Matrix n n ℂ) :
    (complexSchattenNorm (ENNReal.ofReal r) A : ℂ) • polarPower r A 1 = A := by
  set V : Matrix n n ℂ :=
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ) with hV
  set C := complexSchattenNorm (ENNReal.ofReal r) A with hC
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  -- the coefficients are `1`, up to those with `s_i = 0`
  set χ : n → ℂ := (C : ℂ) • polarPowerCoeff r A 1 with hχ
  have hi : ∀ i, complexSingularValue A i ≠ 0 → χ i = 1 := fun i h => by
    have hs : 0 < complexSingularValue A i := (singularValue_nonneg' A i).lt_of_ne' h
    have hC0 : 0 < C := hs.trans_le (complexSingularValue_le hr A i)
    rw [hχ, Pi.smul_apply, polarPowerCoeff, one_mul, ← Complex.ofReal_exp, ← hC,
      Real.exp_log (div_pos hs hC0), smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  -- `A V diag (1 − χ) Vᴴ = 0`, as its square is `V diag (|1 − χ_i|² s_i²) Vᴴ = 0`
  have h0 : A * (V * Matrix.diagonal (1 - χ) * Vᴴ) = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero, conjTranspose_mul_diagonal_mul A _ _ hV]
    have hz : (fun i => star ((1 - χ) i) * ((complexSingularValue A i ^ 2 : ℝ) : ℂ) * (1 - χ) i) =
        0 := by
      funext i
      rcases eq_or_ne (complexSingularValue A i) 0 with h | h
      · simp [h]
      · simp [hi i h]
    rw [hz, Matrix.diagonal_zero', Matrix.mul_zero, Matrix.zero_mul]
  have h1 : (C : ℂ) • polarPower r A 1 = A * (V * Matrix.diagonal χ * Vᴴ) := by
    rw [polarPower_eq, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.diagonal_smul]
  have h2 : Matrix.diagonal (1 - χ) = 1 - Matrix.diagonal χ := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rfl
  rw [h1, eq_comm, ← sub_eq_zero, ← h0, h2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_one, hVV', Matrix.mul_one]

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

/-- The exponent `w (ζ) = r ((1 − ζ)/q₀ + ζ/q₁)` of the norming operators, `1/q_μ = 1 − 1/p_μ`,
translated by `i y`. -/
private noncomputable def normingExponent (r p₀ p₁ y : ℝ) (ζ : ℂ) : ℂ :=
  r * ((1 - (ζ - y * I)) * (1 - 1 / p₀ : ℝ) + (ζ - y * I) * (1 - 1 / p₁ : ℝ))

private theorem re_normingExponent (r p₀ p₁ y : ℝ) (ζ : ℂ) :
    (normingExponent r p₀ p₁ y ζ).re =
      r * ((1 - ζ.re) * (1 - 1 / p₀) + ζ.re * (1 - 1 / p₁)) := by
  simp [normingExponent]

private theorem re_star_normingExponent_nonneg {r p₀ p₁ : ℝ} (hr : 0 ≤ r) (hp₀ : 1 ≤ p₀)
    (hp₁ : 1 ≤ p₁) (y : ℝ) {ζ : ℂ} (hζ : ζ ∈ verticalClosedStrip 0 1) :
    0 ≤ (star (normingExponent r p₀ p₁ y ζ)).re := by
  have hc₀ : 0 ≤ 1 - 1 / p₀ := sub_nonneg.2 (div_le_one_of_le₀ hp₀ (by linarith))
  have hc₁ : 0 ≤ 1 - 1 / p₁ := sub_nonneg.2 (div_le_one_of_le₀ hp₁ (by linarith))
  rw [← starRingEnd_apply, conj_re, re_normingExponent]
  exact mul_nonneg hr (add_nonneg (mul_nonneg (sub_nonneg.2 hζ.2) hc₀) (mul_nonneg hζ.1 hc₁))

/-- The norming operators `X (ζ) = U (Δ / C)^{w̄ (ζ)}`, `C = ‖A‖_{S_r}`, are anti-analytic. -/
private theorem differentiable_star_polarPower (r p₀ p₁ y : ℝ) (A : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun ζ => star (polarPower r A (star (normingExponent r p₀ p₁ y ζ)) i j) := by
  have h : Differentiable ℂ fun v => star (polarPower r A (star v) i j) := fun v =>
    differentiableAt_conj_conj_iff.2 (differentiable_polarPower r A i j _)
  have hw : Differentiable ℂ (normingExponent r p₀ p₁ y) := by
    unfold normingExponent
    fun_prop
  exact h.comp hw

/-- `w (θ + i y) = r − 1` if `1/r = (1 − θ)/p₀ + θ/p₁`. -/
private theorem normingExponent_self {r p₀ p₁ : ℝ} (hr0 : 0 < r) {z : ℂ}
    (hr : 1 / r = (1 - z.re) / p₀ + z.re / p₁) :
    normingExponent r p₀ p₁ z.im z = ((r - 1 : ℝ) : ℂ) := by
  have h1 : z - z.im * I = z.re := by
    rw [sub_eq_iff_eq_add, Complex.re_add_im]
  have h2 : r * ((1 - z.re) * (1 - 1 / p₀) + z.re * (1 - 1 / p₁)) = r - 1 := by
    have h3 : r * (1 / r) = 1 := mul_one_div_cancel hr0.ne'
    rw [hr] at h3
    linear_combination -h3
  rw [normingExponent, h1, ← h2]
  push_cast
  ring

private theorem interp_pos {p₀ p₁ θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 < (1 - θ) / p₀ + θ / p₁ := by
  rcases h0.eq_or_lt with rfl | h
  · simpa using hp₀
  · exact add_pos_of_nonneg_of_pos (div_nonneg (sub_nonneg.2 h1) hp₀.le) (div_pos h hp₁)

/-- **The three lines theorem for Schatten norms** (Gohberg–Krein (1965), §13;
Sutter–Berta–Tomamichel (2017), Theorem 3.1). -/
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
  have hwre : ∀ ζ, (star (w ζ)).re = r * ((1 - ζ.re) * (1 - 1 / p₀) + ζ.re * (1 - 1 / p₁)) :=
    fun ζ => by
      rw [← starRingEnd_apply, conj_re, hw, re_normingExponent]
  -- `g` is bounded
  have hB : BddAbove ((norm ∘ fun ζ => ((X ζ)ᴴ * Ψ ζ).trace) '' verticalClosedStrip 0 1) := by
    obtain ⟨C, hC⟩ := hb
    obtain ⟨B, hB⟩ := exists_norm_polarPower_le hr0 (Ψ z)
    refine ⟨∑ _i : n, ∑ _j : n, B * C, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    exact norm_trace_conjTranspose_mul_le
      (hB _ (re_star_normingExponent_nonneg hr0.le hp₀ hp₁ z.im hζ)) (hC ζ hζ)
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

/-- Complex block diagonal matrices: `‖diag (A_i)‖_{S_p} = (Σ ‖A_i‖_{S_p}^p)^{1/p}`
(Tomczak-Jaegermann (1974), p. 166). -/
private theorem complexSchattenNorm_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (A : ι → Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (Matrix.blockDiagonal A) =
      (∑ i, complexSchattenNorm (ENNReal.ofReal p) (A i) ^ p) ^ (1 / p) := by
  have hA : ∀ i, ((A i)ᴴ * A i).IsHermitian := fun i =>
    Matrix.isHermitian_conjTranspose_mul_self (A i)
  -- diagonalise each block
  set U : Matrix (n × ι) (n × ι) ℂ :=
    Matrix.blockDiagonal fun i => ((hA i).eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    rw [hU, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]
    exact Matrix.blockDiagonal_one
  set μ : n × ι → ℝ := fun x => (hA x.2).eigenvalues x.1 with hμ
  have h : (Matrix.blockDiagonal A)ᴴ * Matrix.blockDiagonal A =
      U * Matrix.diagonal (fun x => (μ x : ℂ)) * Uᴴ := by
    have hd : Matrix.diagonal (fun x => (μ x : ℂ)) =
        Matrix.blockDiagonal fun i => Matrix.diagonal fun j => ((hA i).eigenvalues j : ℂ) := by
      rw [Matrix.blockDiagonal_diagonal]
    rw [hd, hU, Matrix.blockDiagonal_conjTranspose, Matrix.blockDiagonal_conjTranspose,
      ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    exact congrArg Matrix.blockDiagonal (funext fun i =>
      eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose (hA i))
  have h1 := sum_comp_eq_of_map_eq (map_eigenvalues_eq_of_eq_mul_diagonal_mul_conjTranspose
    (Matrix.isHermitian_conjTranspose_mul_self (Matrix.blockDiagonal A)) hUU μ h) fun x => √x ^ p
  simp only [complexSchattenNorm_ofReal_rpow hp]
  rw [complexSchattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  simp only [complexSingularValue]
  rw [h1, Fintype.sum_prod_type_right]

/-- `‖2^{−N/p} diag (X (ε))‖_{S_p} = ‖X‖_{L^p (Ω; S_p)}` (Tomczak-Jaegermann (1974), pp. 166–167),
for scalars of modulus `2^{−N/p}`. -/
private theorem complexSchattenNorm_smul_blockDiagonal {p : ℝ} (hp : 0 < p) {c : ℂ}
    (hc : ‖c‖ = (2 : ℝ) ^ (-(N * (1 / p)))) (X : (Fin N → Bool) → Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (c • Matrix.blockDiagonal X) =
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) p X := by
  rw [complexSchattenNorm_smul (ENNReal.ofReal_pos.2 hp).ne', complexSchattenNorm_blockDiagonal hp,
    scb_lpNorm_eq_sum (complexSchattenNorm_nonneg _), hc, Real.rpow_neg zero_le_two,
    Real.rpow_mul zero_le_two, Real.rpow_natCast, ← div_eq_inv_mul]

/-- The scalars `2^{−N/p(z)}`, `1/p(z) = (1 − z)/p₀ + z/p₁`. -/
private noncomputable def blockScalar (N : ℕ) (p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(N * ((1 - z) / p₀ + z / p₁)) * (Real.log 2 : ℝ))

private theorem norm_blockScalar (N : ℕ) (p₀ p₁ : ℝ) (z : ℂ) :
    ‖blockScalar N p₀ p₁ z‖ = (2 : ℝ) ^ (-(N * ((1 - z.re) / p₀ + z.re / p₁))) := by
  rw [blockScalar, Complex.norm_exp, Complex.re_mul_ofReal, Real.rpow_def_of_pos two_pos, mul_comm]
  congr 2
  rw [Complex.neg_re, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.add_re,
    Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]

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
  set Ψ : ℂ → Matrix (n × (Fin N → Bool)) (n × (Fin N → Bool)) ℂ := fun ζ =>
    blockScalar N p₀ p₁ ζ • Matrix.blockDiagonal (Φ ζ) with hΨ
  have hΨa : ∀ ζ i j, Ψ ζ i j =
      blockScalar N p₀ p₁ ζ * if i.2 = j.2 then Φ ζ i.2 i.1 j.1 else 0 := fun ζ i j => rfl
  rw [← complexSchattenNorm_smul_blockDiagonal hr0 (c := blockScalar N p₀ p₁ z)
    (by rw [norm_blockScalar, hr])]
  refine complexSchattenNorm_le_of_verticalStrip hp₀ hp₁ (Ψ := Ψ) (fun i j => ?_) ?_ (fun y => ?_)
    (fun y => ?_) hz hr
  · -- `Ψ` is analytic
    have hd : DiffContOnCl ℂ (blockScalar N p₀ p₁) (verticalStrip 0 1) := by
      refine Differentiable.diffContOnCl ?_
      unfold blockScalar
      fun_prop
    simp only [hΨa]
    by_cases h : i.2 = j.2
    · simp only [ite_eq_left h]
      exact hd.smul (hΦ _ _ _)
    · simp only [ite_eq_right h, mul_zero]
      exact diffContOnCl_const
  · -- `Ψ` is bounded
    obtain ⟨C, hC⟩ := hb
    refine ⟨|C|, fun ζ hζ i j => ?_⟩
    rw [hΨa, norm_mul, norm_blockScalar, ← one_mul |C|]
    refine mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (neg_nonpos.2
      (mul_nonneg (Nat.cast_nonneg _) (interp_pos hp₀' hp₁' hζ.1 hζ.2).le))) ?_ (norm_nonneg _)
      zero_le_one
    split_ifs
    · exact (hC ζ hζ _ _ _).trans (le_abs_self C)
    · exact norm_zero.trans_le (abs_nonneg C)
  · refine (complexSchattenNorm_smul_blockDiagonal hp₀' ?_ _).trans_le (h₀ y)
    rw [norm_blockScalar]
    simp
  · refine (complexSchattenNorm_smul_blockDiagonal hp₁' ?_ _).trans_le (h₁ y)
    rw [norm_blockScalar]
    simp

end BanachProbability
