module

public import BanachProbability.TypeTwo.Basic
public import BanachProbability.Schatten.Complex
public import BanachProbability.KahaneKhintchine.Basic
import BanachProbability.Schatten.Dilation
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Type 2 of the Schatten classes

For `q ≥ 2` the Schatten class `S_q` of real matrices has type 2 with a constant of order `√q`,
uniformly in the size. For an even integer `q = 2m` the constant is the scalar Khintchine constant,
at most `√(2m − 1)` (`lpNorm_schattenNorm_le_of_even`; N. Tomczak-Jaegermann; Hytönen–van
Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces II* (2017), Lemma 7.1.12, pp. 62–63: the
trace is expanded, and Hölder's inequality compares each term with the scalar one). The other
exponents follow by complex interpolation between `2m` and `2m + 2` (HNVW II, Proposition 7.1.11,
pp. 63, with Proposition 7.1.3 and HNVW I, Proposition D.3.1, p. 574), by Hadamard's three lines
theorem (`isTypeTwoBound_schattenSpace`, with the constant `√(q + 1)`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Even exponents -/

/-- `‖u‖_{S_{2m}}^{2m} = tr ((uᵀ u)^m)`. -/
private theorem tts_schattenNorm_rpow {m : ℕ} (hm : 1 ≤ m) (u : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal (2 * m)) u ^ (2 * m : ℝ) = ((uᵀ * u) ^ m).trace := by
  have hm0 : (0 : ℝ) < 2 * m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hA : (uᴴ * u).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self u
  have h := trace_cfc_eq_sum hA (fun t => t ^ m)
  rw [cfc_pow_id (uᴴ * u) m hA.isSelfAdjoint] at h
  rw [schattenNorm_ofReal_rpow hm0, ← Matrix.conjTranspose_eq_transpose_of_trivial, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← singularValue_sq, ← pow_mul, ← Real.rpow_natCast]
  push_cast
  rfl

/-- The iterated Hölder inequality: `‖w_0 ⋯ w_r‖_{S_{p/(r+1)}} ≤ ∏ ‖w_j‖_{S_p}`. -/
private theorem tts_schattenNorm_prod_le {p : ℝ} (hp : 0 < p) :
    ∀ (r : ℕ) (w : Fin (r + 1) → Matrix n n ℝ),
      schattenNorm (ENNReal.ofReal (p / (r + 1 : ℕ))) (List.ofFn w).prod ≤
        ∏ j, schattenNorm (ENNReal.ofReal p) (w j)
  | 0, w => by simp
  | r + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    refine (schattenNorm_mul_le hp (div_pos hp (by positivity : (0 : ℝ) < (r + 1 : ℕ)))
      ?_ _ _).trans (mul_le_mul_of_nonneg_left (tts_schattenNorm_prod_le hp r _)
        (schattenNorm_nonneg _ _))
    push_cast
    field_simp
    ring

/-- `|tr (v_1ᵀ w_1 ⋯ v_mᵀ w_m)| ≤ ∏ ‖v_j‖_{S_{2m}} ‖w_j‖_{S_{2m}}`. -/
private theorem tts_abs_trace_prod_le {m : ℕ} (hm : 1 ≤ m) (v w : Fin m → Matrix n n ℝ) :
    |(List.ofFn fun j => (v j)ᵀ * w j).prod.trace| ≤
      ∏ j, schattenNorm (ENNReal.ofReal (2 * m)) (v j) *
        schattenNorm (ENNReal.ofReal (2 * m)) (w j) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hr : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  calc |(List.ofFn fun j => (v j)ᵀ * w j).prod.trace|
      ≤ schattenNorm 1 (List.ofFn fun j => (v j)ᵀ * w j).prod := abs_trace_le_schattenNorm_one _
    _ ≤ ∏ j, schattenNorm (ENNReal.ofReal ((r + 1 : ℕ) : ℝ)) ((v j)ᵀ * w j) := by
        have h := tts_schattenNorm_prod_le hr r fun j => (v j)ᵀ * w j
        rwa [div_self hr.ne', ENNReal.ofReal_one] at h
    _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => schattenNorm_nonneg _ _) fun j _ => by
        have h := schattenNorm_mul_le (p := ((r + 1 : ℕ) : ℝ)) (q := 2 * ((r + 1 : ℕ) : ℝ))
          (r := 2 * ((r + 1 : ℕ) : ℝ)) (by positivity) (by positivity) (by field_simp; norm_num)
          (v j)ᵀ (w j)
        rwa [schattenNorm_transpose] at h

/-- The expectation of a product of signs is `1` or `0`, and so nonnegative: it is `1` if every
sign occurs an even number of times, and otherwise `0`. -/
private theorem tts_avg_prod_coin_nonneg {ι : Type*} [Fintype ι] (τ : ι → Fin N) :
    0 ≤ avg fun ε : Fin N → Bool => ∏ i, coin (ε (τ i)) := by
  classical
  by_cases h : ∀ k, Even (Finset.univ.filter fun i => τ i = k).card
  · refine avg_nonneg fun ε => ?_
    rw [Finset.prod_comp (fun k => coin (ε k)) τ]
    exact Finset.prod_nonneg fun k _ => (h k).pow_nonneg _
  · obtain ⟨k, hk⟩ := not_forall.1 h
    refine (scb_avg_eq_zero_of_flip k fun ε => ?_).ge
    have hi : ∀ i, coin (SignCube.flip k ε (τ i)) =
        (if τ i = k then -1 else 1) * coin (ε (τ i)) := fun i => by
      split_ifs with hik
      · rw [hik, flip_apply_self, coin_not, neg_one_mul]
      · rw [flip_apply_of_ne hik, one_mul]
    simp only [hi]
    rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      (Nat.not_even_iff_odd.1 hk).neg_one_pow, neg_one_mul]

/-- The expansion of a power of a sum in an algebra. -/
private theorem tts_sum_smul_pow {ι A : Type*} [Fintype ι] [Ring A] [Algebra ℝ A] (m : ℕ)
    (c : ι → ℝ) (y : ι → A) :
    (∑ i, c i • y i) ^ m =
      ∑ σ : Fin m → ι, (∏ j, c (σ j)) • (List.ofFn fun j => y (σ j)).prod := by
  classical
  have h := (MultilinearMap.mkPiAlgebraFin ℝ m A).map_sum fun (_ : Fin m) i => c i • y i
  rw [MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate] at h
  rw [h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ (MultilinearMap.mkPiAlgebraFin ℝ m A) (fun j => c (σ j))
    (fun j => y (σ j)), MultilinearMap.mkPiAlgebraFin_apply]

/-- `E ‖Σ ε_k x_k‖_{S_{2m}}^{2m} ≤ E |Σ ε_k ‖x_k‖_{S_{2m}}|^{2m}`: both sides are expanded over the
sequences `(i_1, j_1, …, i_m, j_m)`, and the terms are compared by Hölder's inequality. -/
private theorem tts_avg_schattenNorm_rpow_le {m : ℕ} (hm : 1 ≤ m) (x : Fin N → Matrix n n ℝ) :
    (avg fun ε => schattenNorm (ENNReal.ofReal (2 * m)) (∑ k, coin (ε k) • x k) ^ (2 * m : ℝ)) ≤
      avg fun ε => |∑ k, coin (ε k) • schattenNorm (ENNReal.ofReal (2 * m)) (x k)| ^
        (2 * m : ℝ) := by
  set a : Fin N → ℝ := fun k => schattenNorm (ENNReal.ofReal (2 * m)) (x k)
  change _ ≤ avg fun ε => |∑ k, coin (ε k) • a k| ^ (2 * m : ℝ)
  -- the signs of the term of a sequence `σ = (i_1, j_1, …, i_m, j_m)`
  set s : (Fin m → Fin N × Fin N) → (Fin N → Bool) → ℝ :=
    fun σ ε => ∏ j, (coin (ε (σ j).1) * coin (ε (σ j).2)) with hs
  have hL : ∀ ε : Fin N → Bool,
      schattenNorm (ENNReal.ofReal (2 * m)) (∑ k, coin (ε k) • x k) ^ (2 * m : ℝ) =
        ∑ σ, (List.ofFn fun j => (x (σ j).1)ᵀ * x (σ j).2).prod.trace * s σ ε := fun ε => by
    have h : (∑ k, coin (ε k) • x k)ᵀ * ∑ k, coin (ε k) • x k =
        ∑ p : Fin N × Fin N, (coin (ε p.1) * coin (ε p.2)) • ((x p.1)ᵀ * x p.2) := by
      rw [Matrix.transpose_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [Matrix.transpose_smul, smul_mul_smul_comm]
    rw [tts_schattenNorm_rpow hm, h, tts_sum_smul_pow, Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul, mul_comm, hs]
  have hR : ∀ ε : Fin N → Bool, |∑ k, coin (ε k) • a k| ^ (2 * m : ℝ) =
      ∑ σ, (∏ j, (a (σ j).1 * a (σ j).2)) * s σ ε := fun ε => by
    have h : (∑ k, coin (ε k) • a k) ^ 2 =
        ∑ p : Fin N × Fin N, (coin (ε p.1) * coin (ε p.2)) • (a p.1 * a p.2) := by
      rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
    rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, pow_mul, sq_abs,
      h, tts_sum_smul_pow]
    simp only [List.prod_ofFn, smul_eq_mul, mul_comm, hs]
  simp only [hL, hR, avg_sum, avg_const_mul]
  refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (tts_abs_trace_prod_le hm _ _)) ?_
  have h := tts_avg_prod_coin_nonneg (Sum.elim (fun j => (σ j).1) fun j => (σ j).2)
  simpa only [hs, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.prod_mul_distrib]
    using h

/-- `(E nrm (X)²)^{1/2}` as a square root. -/
private theorem tts_lpNorm_two {E : Type*} (nrm : E → ℝ) (X : (Fin N → Bool) → E) :
    SignCube.lpNorm nrm 2 X = √(avg fun ε => nrm (X ε) ^ 2) := by
  simp only [SignCube.lpNorm, Real.rpow_two, Real.sqrt_eq_rpow]

/-- `(E |Σ ε_k a_k|²)^{1/2} = (Σ a_k²)^{1/2}`. -/
private theorem tts_lpNorm_two_real (a : Fin N → ℝ) :
    SignCube.lpNorm (fun t : ℝ => |t|) 2 (fun ε : Fin N → Bool => ∑ k, coin (ε k) • a k) =
      √(∑ k, a k ^ 2) := by
  rw [tts_lpNorm_two]
  congr 1
  have h : ∀ ε : Fin N → Bool, |∑ k, coin (ε k) • a k| ^ 2 =
      ∑ i, ∑ j, a i * a j * (coin (ε i) * coin (ε j)) := fun ε => by
    rw [sq_abs, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_mul]
    ring
  simp only [h, avg_sum, avg_const_mul, avg_coin_mul_coin, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, sq]

/-- Type 2 of `S_{2m}` (HNVW II, Lemma 7.1.12), even in `L^{2m}`:
`(E ‖Σ ε_k x_k‖_{S_{2m}}^{2m})^{1/2m} ≤ √(2m − 1) (Σ ‖x_k‖_{S_{2m}}²)^{1/2}`. -/
theorem lpNorm_schattenNorm_le_of_even {m : ℕ} (hm : 1 ≤ m) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * m))) (2 * m)
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m - 1) * √(∑ k, schattenNorm (ENNReal.ofReal (2 * m)) (x k) ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set a : Fin N → ℝ := fun k => schattenNorm (ENNReal.ofReal (2 * m)) (x k)
  -- comparison with the scalar sum
  have h1 : SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * m))) (2 * m)
      (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
        SignCube.lpNorm (fun t : ℝ => |t|) (2 * m)
          (fun ε : Fin N → Bool => ∑ k, coin (ε k) • a k) :=
    Real.rpow_le_rpow (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _)
      (tts_avg_schattenNorm_rpow_le hm x) (by positivity)
  -- the scalar Khintchine inequality
  have h2 := kahaneKhintchine_hypercontractive (normSeminorm ℝ ℝ) one_lt_two
    (by linarith : (2 : ℝ) ≤ 2 * m) a
  have h3 : SignCube.lpNorm (normSeminorm ℝ ℝ) 2
      (fun ε : Fin N → Bool => ∑ k, coin (ε k) • a k) = √(∑ k, a k ^ 2) := tts_lpNorm_two_real a
  rw [h3, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at h2
  exact h1.trans h2

/-- The same for complex matrices. -/
theorem lpNorm_complexSchattenNorm_le_of_even {m : ℕ} (hm : 1 ≤ m) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (2 * m))) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m - 1) * √(∑ k, complexSchattenNorm (ENNReal.ofReal (2 * m)) (x k) ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : ENNReal.ofReal (2 * m) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  set c : ℝ := (2 : ℝ) ^ (-(1 / (ENNReal.ofReal (2 * m)).toReal)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hnorm : ∀ A : Matrix n n ℂ, complexSchattenNorm (ENNReal.ofReal (2 * m)) A ^ 2 =
      c ^ 2 * schattenNorm (ENNReal.ofReal (2 * m)) (realify A) ^ 2 := fun A => by
    rw [complexSchattenNorm_eq_realify hq, mul_pow]
  have hlin : ∀ ε : Fin N → Bool,
      realify (∑ k, coin (ε k) • x k) = ∑ k, coin (ε k) • realify (x k) := fun ε => by
    have h := map_sum (AddMonoidHom.mk' (realify : Matrix n n ℂ → _) realify_add)
      (fun k => coin (ε k) • x k) Finset.univ
    simpa only [AddMonoidHom.mk'_apply, realify_smul] using h
  -- the real inequality for the realifications, and `L² ≤ L^{2m}`
  have h := (lpNorm_mono_exponent (schattenNorm_nonneg (ENNReal.ofReal (2 * m))) two_pos
    (by linarith : (2 : ℝ) ≤ 2 * m) _).trans
      (lpNorm_schattenNorm_le_of_even hm fun k => realify (x k))
  rw [tts_lpNorm_two] at h ⊢
  simp only [hnorm, hlin, avg_const_mul, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h hc0

/-! ### Interpolation

HNVW II, Proposition 7.1.3 interpolates the operator `(x_k) ↦ Σ_k ε_k x_k`, which is bounded from
`ℓ² (S_{p_j})` to `L² (S_{p_j})`, `j = 0, 1`, with `[S_{p₀}, S_{p₁}]_θ = S_q`. Here the matrices
have a fixed size, and the interpolation is written out with the three lines theorem: to bound
`E tr (Φ (ε) Σ_k ε_k x_k)`, the matrices `x_k` and `Φ (ε)` are put in analytic families `x_k^{[w]}`,
`Φ (ε)^{[w']}` (`ttsFamily`), bounded on the two lines by `‖x_k‖_{S_q}` and `‖Φ (ε)‖_{S_{q'}}`. -/

section Family

variable {A : Matrix n n ℂ}

/-- The eigenvalues `s sgn (λ_i) (|λ_i| / s)^w`, `s = ‖A‖_{S_q}`, of the analytic family through a
Hermitian matrix `A`; the power is written as an exponential. -/
private noncomputable def ttsCoeff (q : ℝ) (hA : A.IsHermitian) (w : ℂ) (i : n) : ℂ :=
  ((complexSchattenNorm (ENNReal.ofReal q) A * Real.sign (hA.eigenvalues i) : ℝ) : ℂ) *
    Complex.exp (w * (Real.log
      (|hA.eigenvalues i| / complexSchattenNorm (ENNReal.ofReal q) A) : ℝ))

/-- The analytic family through a Hermitian matrix `A = U diag (λ) Uᴴ` (HNVW I, proof of
Proposition D.3.1, p. 574, on finite sequences of eigenvalues): with `s = ‖A‖_{S_q}`,
`A^{[w]} = U diag (s sgn (λ_i) (|λ_i| / s)^w) Uᴴ`, an entire function of `w` with `A^{[1]} = A`. -/
private noncomputable def ttsFamily (q : ℝ) (hA : A.IsHermitian) (w : ℂ) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (ttsCoeff q hA w) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

/-- `|λ_i| ≤ ‖A‖_{S_q}`. -/
private theorem tts_abs_eigenvalue_le {q : ℝ} (hq : 0 < q) (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ complexSchattenNorm (ENNReal.ofReal q) A := by
  refine (Real.rpow_le_rpow_iff (abs_nonneg _) (complexSchattenNorm_nonneg _ _) hq).1 ?_
  rw [complexSchattenNorm_rpow_of_isHermitian hA hq]
  exact Finset.single_le_sum (f := fun i => |hA.eigenvalues i| ^ q)
    (fun i _ => Real.rpow_nonneg (abs_nonneg _) q) (Finset.mem_univ i)

private theorem ttsFamily_one {q : ℝ} (hq : 0 < q) (hA : A.IsHermitian) :
    ttsFamily q hA 1 = A := by
  have hc : ttsCoeff q hA 1 = fun i => (hA.eigenvalues i : ℂ) := by
    funext i
    rcases eq_or_ne (hA.eigenvalues i) 0 with h | h
    · simp [ttsCoeff, h]
    · have hl : 0 < |hA.eigenvalues i| := abs_pos.2 h
      have hs : 0 < complexSchattenNorm (ENNReal.ofReal q) A :=
        hl.trans_le (tts_abs_eigenvalue_le hq hA i)
      rw [ttsCoeff, one_mul, ← Complex.ofReal_exp, Real.exp_log (div_pos hl hs),
        ← Complex.ofReal_mul, mul_right_comm, mul_div_cancel₀ _ hs.ne']
      congr 1
      rcases lt_or_gt_of_ne h with h' | h'
      · rw [Real.sign_of_neg h', abs_of_neg h', mul_neg_one, neg_neg]
      · rw [Real.sign_of_pos h', abs_of_pos h', mul_one]
  rw [ttsFamily, hc]
  conv_rhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

private theorem differentiable_ttsFamily (q : ℝ) (hA : A.IsHermitian) (i j : n) :
    Differentiable ℂ fun w => ttsFamily q hA w i j := by
  have h : ∀ k, Differentiable ℂ fun w => ttsCoeff q hA w k := fun k => by
    unfold ttsCoeff
    fun_prop
  have e : ∀ w, ttsFamily q hA w i j = ∑ k, (hA.eigenvectorUnitary : Matrix n n ℂ) i k *
      ttsCoeff q hA w k * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ k j := fun w => by
    rw [ttsFamily, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  simp only [e]
  fun_prop

private theorem norm_ttsCoeff (q : ℝ) (hA : A.IsHermitian) (w : ℂ) (i : n) :
    ‖ttsCoeff q hA w i‖ = complexSchattenNorm (ENNReal.ofReal q) A *
      |Real.sign (hA.eigenvalues i)| * Real.exp (w.re * Real.log
        (|hA.eigenvalues i| / complexSchattenNorm (ENNReal.ofReal q) A)) := by
  rw [ttsCoeff, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (complexSchattenNorm_nonneg _ _), Complex.re_mul_ofReal]

private theorem tts_abs_sign_le (t : ℝ) : |Real.sign t| ≤ 1 := by
  rcases Real.sign_apply_eq t with h | h | h <;> simp [h]

/-- On the half plane `Re w ≥ 0` the eigenvalues of `A^{[w]}` are at most `‖A‖_{S_q}`. -/
private theorem norm_ttsCoeff_le {q : ℝ} (hq : 0 < q) (hA : A.IsHermitian) {w : ℂ}
    (hw : 0 ≤ w.re) (i : n) :
    ‖ttsCoeff q hA w i‖ ≤ complexSchattenNorm (ENNReal.ofReal q) A := by
  have hs := complexSchattenNorm_nonneg (ENNReal.ofReal q) A
  rw [norm_ttsCoeff, mul_assoc]
  refine mul_le_of_le_one_right hs ((mul_le_of_le_one_left (Real.exp_nonneg _)
    (tts_abs_sign_le _)).trans ?_)
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hw (Real.log_nonpos (div_nonneg (abs_nonneg _) hs)
    (div_le_one_of_le₀ (tts_abs_eigenvalue_le hq hA i) hs))

private theorem complexSchattenNorm_ttsFamily {p : ℝ} (hp : 0 < p) (q : ℝ) (hA : A.IsHermitian)
    (w : ℂ) : complexSchattenNorm (ENNReal.ofReal p) (ttsFamily q hA w) =
      (∑ i, ‖ttsCoeff q hA w i‖ ^ p) ^ (1 / p) :=
  complexSchattenNorm_unitary_mul_diagonal_mul hp hA.eigenvectorUnitary.2
    hA.eigenvectorUnitary.2 _

/-- The bound of the family on the half plane `Re w ≥ 0`. -/
private theorem complexSchattenNorm_ttsFamily_le_card {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hA : A.IsHermitian) {w : ℂ} (hw : 0 ≤ w.re) :
    complexSchattenNorm (ENNReal.ofReal p) (ttsFamily q hA w) ≤
      (Fintype.card n : ℝ) ^ (1 / p) * complexSchattenNorm (ENNReal.ofReal q) A := by
  have hs := complexSchattenNorm_nonneg (ENNReal.ofReal q) A
  rw [complexSchattenNorm_ttsFamily hp]
  calc (∑ i, ‖ttsCoeff q hA w i‖ ^ p) ^ (1 / p)
      ≤ (∑ _i : n, complexSchattenNorm (ENNReal.ofReal q) A ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) p)
          (Finset.sum_le_sum fun i _ =>
            Real.rpow_le_rpow (norm_nonneg _) (norm_ttsCoeff_le hq hA hw i) hp.le) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hs _), ← Real.rpow_mul hs,
          mul_one_div_cancel hp.ne', Real.rpow_one]

/-- On the line `Re w = q / p` the family has `‖A^{[w]}‖_{S_p} ≤ ‖A‖_{S_q}` (with equality):
`Σ_i |s sgn (λ_i) (|λ_i| / s)^w|^p = s^{p − q} Σ_i |λ_i|^q = s^p`. -/
private theorem complexSchattenNorm_ttsFamily_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hA : A.IsHermitian) {w : ℂ} (hw : w.re = q / p) :
    complexSchattenNorm (ENNReal.ofReal p) (ttsFamily q hA w) ≤
      complexSchattenNorm (ENNReal.ofReal q) A := by
  set s := complexSchattenNorm (ENNReal.ofReal q) A with hs_def
  have hs : 0 ≤ s := complexSchattenNorm_nonneg (ENNReal.ofReal q) A
  have hsum : ∑ i, |hA.eigenvalues i| ^ q = s ^ q :=
    (complexSchattenNorm_rpow_of_isHermitian hA hq).symm
  -- the terms
  have hi : ∀ i, ‖ttsCoeff q hA w i‖ ^ p ≤ s ^ p * (|hA.eigenvalues i| ^ q / s ^ q) := fun i => by
    rcases eq_or_ne (hA.eigenvalues i) 0 with h | h
    · rw [norm_ttsCoeff, h, Real.sign_zero, abs_zero, mul_zero, zero_mul, Real.zero_rpow hp.ne',
        Real.zero_rpow hq.ne', zero_div, mul_zero]
    · have hl : 0 < |hA.eigenvalues i| := abs_pos.2 h
      have hs0 : 0 < s := hl.trans_le (tts_abs_eigenvalue_le hq hA i)
      have hd : 0 < |hA.eigenvalues i| / s := div_pos hl hs0
      have he : Real.exp (w.re * Real.log (|hA.eigenvalues i| / s)) =
          (|hA.eigenvalues i| / s) ^ (q / p) := by
        rw [Real.rpow_def_of_pos hd, hw, mul_comm]
      have h1 : |Real.sign (hA.eigenvalues i)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero _ h with h' | h' <;> simp [h']
      rw [norm_ttsCoeff, ← hs_def, he, h1, mul_one, Real.mul_rpow hs (Real.rpow_nonneg hd.le _),
        ← Real.rpow_mul hd.le, div_mul_cancel₀ _ hp.ne', Real.div_rpow hl.le hs]
  rw [complexSchattenNorm_ttsFamily hp]
  calc (∑ i, ‖ttsCoeff q hA w i‖ ^ p) ^ (1 / p) ≤ (s ^ p) ^ (1 / p) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) p)
          ((Finset.sum_le_sum fun i _ => hi i).trans ?_) (by positivity)
        rw [← Finset.mul_sum, ← Finset.sum_div, hsum]
        exact mul_le_of_le_one_right (Real.rpow_nonneg hs _) (div_self_le_one _)
    _ = s := by rw [← Real.rpow_mul hs, mul_one_div_cancel hp.ne', Real.rpow_one]

end Family

/-- The Cauchy–Schwarz inequality `E a b ≤ (E a²)^{1/2} (E b²)^{1/2}`. -/
private theorem tts_avg_mul_le (a b : (Fin N → Bool) → ℝ) :
    (avg fun ε => a ε * b ε) ≤ √(avg fun ε => a ε ^ 2) * √(avg fun ε => b ε ^ 2) := by
  rw [← Real.sqrt_mul (avg_nonneg fun _ => sq_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  unfold avg
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- The bilinear form `E tr (Ψ (ε) Σ_k ε_k y_k)`. -/
private noncomputable def ttsForm (Ψ : (Fin N → Bool) → Matrix n n ℂ) (y : Fin N → Matrix n n ℂ) :
    ℂ :=
  ((2 : ℂ) ^ N)⁻¹ * ∑ ε, (Ψ ε * ∑ k, coin (ε k) • y k).trace

/-- Hölder's inequality for the bilinear form, and a type 2 bound of `S_p`. -/
private theorem norm_ttsForm_le {p p' C : ℝ} (hp : p.HolderConjugate p')
    (Ψ : (Fin N → Bool) → Matrix n n ℂ) (y : Fin N → Matrix n n ℂ)
    (hC : SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
      C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2)) :
    ‖ttsForm Ψ y‖ ≤ √(avg fun ε => complexSchattenNorm (ENNReal.ofReal p') (Ψ ε) ^ 2) *
      (C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2)) := by
  calc ‖ttsForm Ψ y‖ ≤ avg fun ε => ‖(Ψ ε * ∑ k, coin (ε k) • y k).trace‖ := by
        rw [ttsForm, avg, div_eq_inv_mul, norm_mul, norm_inv, norm_pow, Complex.norm_two]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ avg fun ε => complexSchattenNorm (ENNReal.ofReal p') (Ψ ε) *
          complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • y k) :=
        avg_mono fun ε => norm_trace_mul_le hp.symm _ _
    _ ≤ √(avg fun ε => complexSchattenNorm (ENNReal.ofReal p') (Ψ ε) ^ 2) *
          √(avg fun ε => complexSchattenNorm (ENNReal.ofReal p)
            (∑ k, coin (ε k) • y k) ^ 2) := tts_avg_mul_le _ _
    _ ≤ _ := by
        rw [tts_lpNorm_two] at hC
        exact mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)

/-- The bilinear form on analytic families, with bounds of the families. -/
private theorem norm_ttsForm_family_le {p p' q q' C c c' : ℝ} (hp : p.HolderConjugate p')
    (hC0 : 0 ≤ C) (hC : ∀ y : Fin N → Matrix n n ℂ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
      C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2))
    {Φ : (Fin N → Bool) → Matrix n n ℂ} (hΦ : ∀ ε, (Φ ε).IsHermitian)
    {x : Fin N → Matrix n n ℂ} (hx : ∀ k, (x k).IsHermitian) {w w' : ℂ}
    (h' : ∀ ε, complexSchattenNorm (ENNReal.ofReal p') (ttsFamily q' (hΦ ε) w') ≤
      c' * complexSchattenNorm (ENNReal.ofReal q') (Φ ε))
    (h : ∀ k, complexSchattenNorm (ENNReal.ofReal p) (ttsFamily q (hx k) w) ≤
      c * complexSchattenNorm (ENNReal.ofReal q) (x k)) :
    ‖ttsForm (fun ε => ttsFamily q' (hΦ ε) w') fun k => ttsFamily q (hx k) w‖ ≤
      √(avg fun ε => (c' * complexSchattenNorm (ENNReal.ofReal q') (Φ ε)) ^ 2) *
        (C * √(∑ k, (c * complexSchattenNorm (ENNReal.ofReal q) (x k)) ^ 2)) := by
  refine (norm_ttsForm_le hp _ _ (hC _)).trans (mul_le_mul ?_ (mul_le_mul_of_nonneg_left ?_ hC0)
    (mul_nonneg hC0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact Real.sqrt_le_sqrt (avg_mono fun ε =>
      pow_le_pow_left₀ (complexSchattenNorm_nonneg _ _) (h' ε) 2)
  · exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
      pow_le_pow_left₀ (complexSchattenNorm_nonneg _ _) (h k) 2)

omit [DecidableEq n] in
private theorem differentiable_ttsForm {Ψ : ℂ → (Fin N → Bool) → Matrix n n ℂ}
    {y : ℂ → Fin N → Matrix n n ℂ} (hΨ : ∀ ε i j, Differentiable ℂ fun z => Ψ z ε i j)
    (hy : ∀ k i j, Differentiable ℂ fun z => y z k i j) :
    Differentiable ℂ fun z => ttsForm (Ψ z) (y z) := by
  simp only [ttsForm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply]
  fun_prop

/-- Interpolation of type 2 (HNVW II, Proposition 7.1.3, with HNVW I, Proposition D.3.1), in the
dual formulation: the three lines theorem for `F (z) = E tr (Φ (ε)^{[q'/p'(z)]} Σ_k ε_k
x_k^{[q/p(z)]})`, `1/p (z) = (1 − z)/p₀ + z/p₁`. -/
private theorem tts_three_lines {p₀ p₀' p₁ p₁' q q' θ C₀ C₁ : ℝ} (hp₀ : p₀.HolderConjugate p₀')
    (hp₁ : p₁.HolderConjugate p₁') (hq : q.HolderConjugate q') (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθ : 1 / q = (1 - θ) / p₀ + θ / p₁) (hC₀0 : 0 ≤ C₀) (hC₁0 : 0 ≤ C₁)
    (hC₀ : ∀ y : Fin N → Matrix n n ℂ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₀)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
      C₀ * √(∑ k, complexSchattenNorm (ENNReal.ofReal p₀) (y k) ^ 2))
    (hC₁ : ∀ y : Fin N → Matrix n n ℂ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p₁)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
      C₁ * √(∑ k, complexSchattenNorm (ENNReal.ofReal p₁) (y k) ^ 2))
    {Φ : (Fin N → Bool) → Matrix n n ℂ} (hΦ : ∀ ε, (Φ ε).IsHermitian)
    {x : Fin N → Matrix n n ℂ} (hx : ∀ k, (x k).IsHermitian) :
    ‖ttsForm Φ x‖ ≤
      (√(avg fun ε => complexSchattenNorm (ENNReal.ofReal q') (Φ ε) ^ 2) *
        (C₀ * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2))) ^ (1 - θ) *
      (√(avg fun ε => complexSchattenNorm (ENNReal.ofReal q') (Φ ε) ^ 2) *
        (C₁ * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2))) ^ θ := by
  have hq0 : 0 < q := hq.pos
  have hq'0 : 0 < q' := hq.symm.pos
  -- `1 / p (z) = (1 - z) / p₀ + z / p₁`, and its real part
  set r : ℂ → ℂ := fun z => (1 - z) / p₀ + z / p₁ with hr
  have hre : ∀ z, (r z).re = (1 - z.re) / p₀ + z.re / p₁ := fun z => by
    simp only [hr, Complex.add_re, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]
  have hw : ∀ z, ((q : ℂ) * r z).re = q * (r z).re := fun z => Complex.re_ofReal_mul _ _
  have hw' : ∀ z, ((q' : ℂ) * (1 - r z)).re = q' * (1 - (r z).re) := fun z => by
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  set F : ℂ → ℂ := fun z => ttsForm (fun ε => ttsFamily q' (hΦ ε) (q' * (1 - r z)))
    fun k => ttsFamily q (hx k) (q * r z) with hF
  -- the value at `θ`
  have hFθ : F θ = ttsForm Φ x := by
    have hrθ : r θ = ((1 / q : ℝ) : ℂ) := by
      rw [hθ]
      simp only [hr]
      push_cast
      rfl
    have h1 : (q : ℂ) * r θ = 1 := by
      rw [hrθ, ← Complex.ofReal_mul, mul_one_div_cancel hq0.ne', Complex.ofReal_one]
    have h2 : (q' : ℂ) * (1 - r θ) = 1 := by
      have : q' * (1 - 1 / q) = 1 := by
        rw [one_div, hq.one_sub_inv, mul_inv_cancel₀ hq'0.ne']
      rw [hrθ, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, this]
    simp only [hF, h1, h2, ttsFamily_one hq0, ttsFamily_one hq'0]
  have hd : Differentiable ℂ F := by
    have hrd : Differentiable ℂ r := by
      simp only [hr]
      fun_prop
    refine differentiable_ttsForm (fun ε i j => ?_) fun k i j => ?_
    · exact (differentiable_ttsFamily q' (hΦ ε) i j).comp (by fun_prop)
    · exact (differentiable_ttsFamily q (hx k) i j).comp (by fun_prop)
  -- boundedness on the strip
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨√(avg fun ε => ((Fintype.card n : ℝ) ^ (1 / p₀') *
        complexSchattenNorm (ENNReal.ofReal q') (Φ ε)) ^ 2) *
      (C₀ * √(∑ k, ((Fintype.card n : ℝ) ^ (1 / p₀) *
        complexSchattenNorm (ENNReal.ofReal q) (x k)) ^ 2)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : 0 ≤ z.re := hz.1
    have hz1 : z.re ≤ 1 := hz.2
    have e1 : (1 - z.re) / p₀ ≤ 1 - z.re := div_le_self (by linarith) hp₀.lt.le
    have e2 : z.re / p₁ ≤ z.re := div_le_self hz0 hp₁.lt.le
    have e3 : 0 ≤ (1 - z.re) / p₀ := div_nonneg (by linarith) hp₀.pos.le
    have e4 : 0 ≤ z.re / p₁ := div_nonneg hz0 hp₁.pos.le
    refine norm_ttsForm_family_le hp₀ hC₀0 hC₀ hΦ hx
      (fun ε => complexSchattenNorm_ttsFamily_le_card hp₀.symm.pos hq'0 _ ?_)
      (fun k => complexSchattenNorm_ttsFamily_le_card hp₀.pos hq0 _ ?_)
    · rw [hw', hre]
      exact mul_nonneg hq'0.le (by linarith)
    · rw [hw, hre]
      exact mul_nonneg hq0.le (by linarith)
  -- the two lines
  have hline : ∀ {p p' C : ℝ}, p.HolderConjugate p' → 0 ≤ C → (∀ y : Fin N → Matrix n n ℂ,
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
      C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2)) → ∀ z : ℂ,
      (r z).re = p⁻¹ → ‖F z‖ ≤
        √(avg fun ε => complexSchattenNorm (ENNReal.ofReal q') (Φ ε) ^ 2) *
          (C * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2)) := by
    intro p p' C hp hC0 hC z hz
    have h := norm_ttsForm_family_le (c := 1) (c' := 1) (q := q) (q' := q') hp hC0 hC hΦ hx
      (w := q * r z) (w' := q' * (1 - r z))
      (fun ε => (complexSchattenNorm_ttsFamily_le hp.symm.pos hq'0 _
        (by rw [hw', hz, hp.one_sub_inv, div_eq_mul_inv])).trans_eq (one_mul _).symm)
      (fun k => (complexSchattenNorm_ttsFamily_le hp.pos hq0 _
        (by rw [hw, hz, div_eq_mul_inv])).trans_eq (one_mul _).symm)
    simpa only [one_mul] using h
  rw [← hFθ]
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (θ : ℂ)) ⟨by simpa using hθ0, by simpa using hθ1⟩ hd.diffContOnCl hB
    (fun z hz => hline hp₀ hC₀0 hC₀ z (by rw [hre, show z.re = 0 from hz]; simp))
    (fun z hz => hline hp₁ hC₁0 hC₁ z (by rw [hre, show z.re = 1 from hz]; simp))
  rwa [Complex.ofReal_re] at h

/-- The norming function of `Y ∈ L² (S_q)`, `Y (ε)` symmetric: `Φ = ‖Y (ε)‖^{2−q} N (Y (ε)) / ‖Y‖`
with the norming element `N` has `‖Φ‖_{L² (S_{q'})} ≤ 1` and `E tr (Φ Y) = ‖Y‖_{L² (S_q)}`. -/
private theorem tts_exists_avg_trace_eq {q q' : ℝ} (hq : q.HolderConjugate q')
    (Y : (Fin N → Bool) → Matrix n n ℝ) (hY : ∀ ε, (Y ε).IsHermitian) :
    ∃ Φ : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (Φ ε).IsHermitian) ∧
      √(avg fun ε => schattenNorm (ENNReal.ofReal q') (Φ ε) ^ 2) ≤ 1 ∧
      (avg fun ε => (Φ ε * Y ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) 2 Y := by
  have hq1 : 1 < q := hq.lt
  have hq' : q' = q / (q - 1) := hq.conjugate_eq
  have hq'ne : ENNReal.ofReal q' ≠ 0 := (ENNReal.ofReal_pos.2 hq.symm.pos).ne'
  set L := SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) 2 Y with hL
  have hL2 : (avg fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2) = L ^ 2 := by
    rw [hL, tts_lpNorm_two, Real.sq_sqrt (avg_nonneg fun ε => sq_nonneg _)]
  have hL0 : 0 ≤ L := lpNorm_nonneg (schattenNorm_nonneg _) 2 Y
  -- the powers of `s = ‖Y (ε)‖_{S_q}`, which may vanish
  have hpow : ∀ {s a : ℝ}, 0 ≤ s → a ≠ 0 → 2 - q + a ≠ 0 →
      s ^ (2 - q) * s ^ a = s ^ (2 - q + a) := by
    intro s a hs ha hb
    rcases hs.eq_or_lt with rfl | hs
    · rw [Real.zero_rpow ha, Real.zero_rpow hb, mul_zero]
    · rw [Real.rpow_add hs]
  refine ⟨fun ε => (L⁻¹ * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (2 - q)) •
    normingElement q (Y ε), fun ε =>
      (isHermitian_normingElement q (Y ε)).smul (IsSelfAdjoint.all _), ?_, ?_⟩
  · have hn : ∀ ε, schattenNorm (ENNReal.ofReal q')
        ((L⁻¹ * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (2 - q)) • normingElement q (Y ε)) ^ 2 =
          L⁻¹ ^ 2 * schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2 := fun ε => by
      have hs := schattenNorm_nonneg (ENNReal.ofReal q) (Y ε)
      have h := schattenNorm_normingElement (hY ε) hq1
      rw [← hq'] at h
      rw [schattenNorm_smul hq'ne, h, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hL0)
        (Real.rpow_nonneg hs _)), mul_assoc, hpow hs (by linarith) (by ring_nf; norm_num),
        show 2 - q + (q - 1) = 1 by ring, Real.rpow_one, mul_pow]
    simp only [hn, avg_const_mul, hL2]
    rw [← mul_pow, Real.sqrt_sq (mul_nonneg (inv_nonneg.2 hL0) hL0)]
    exact inv_mul_le_one
  · have ht : ∀ ε, (((L⁻¹ * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (2 - q)) •
        normingElement q (Y ε)) * Y ε).trace =
          L⁻¹ * schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2 := fun ε => by
      have hs := schattenNorm_nonneg (ENNReal.ofReal q) (Y ε)
      rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm,
        trace_mul_normingElement (hY ε) hq1, smul_eq_mul, mul_assoc,
        hpow hs (by linarith) (by ring_nf; norm_num), show 2 - q + q = (2 : ℝ) by ring,
        Real.rpow_two]
    simp only [ht, avg_const_mul, hL2]
    rcases hL0.eq_or_lt with h | h
    · rw [← h]
      simp
    · rw [sq, inv_mul_cancel_left₀ h.ne']

/-- The interpolation parameter: `1/q = (1 − θ)/p₀ + θ/p₁`. -/
private theorem tts_exists_theta {p₀ p₁ q : ℝ} (hp₀ : 0 < p₀) (hp : p₀ < p₁) (hq₀ : p₀ ≤ q)
    (hq₁ : q ≤ p₁) : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 1 / q = (1 - θ) / p₀ + θ / p₁ := by
  have hq : 0 < q := hp₀.trans_le hq₀
  have hp₁ : 0 < p₁ := hp₀.trans hp
  have hd : 0 < p₁ - p₀ := by linarith
  refine ⟨p₁ * (q - p₀) / (q * (p₁ - p₀)), ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hp₁.le (by linarith)) (mul_pos hq hd).le
  · rw [div_le_one (mul_pos hq hd)]
    nlinarith
  · have := hd.ne'
    field_simp
    ring

omit [DecidableEq n] in
/-- The bilinear form of real matrices. -/
private theorem ttsForm_map_ofReal (Ψ : (Fin N → Bool) → Matrix n n ℝ)
    (y : Fin N → Matrix n n ℝ) :
    ttsForm (fun ε => (Ψ ε).map Complex.ofReal) (fun k => (y k).map Complex.ofReal) =
      ((avg fun ε => (Ψ ε * ∑ k, coin (ε k) • y k).trace : ℝ) : ℂ) := by
  have h : ∀ ε : Fin N → Bool, ((Ψ ε).map Complex.ofReal *
      ∑ k, coin (ε k) • (y k).map Complex.ofReal).trace =
        (((Ψ ε * ∑ k, coin (ε k) • y k).trace : ℝ) : ℂ) := fun ε => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
  simp only [ttsForm, h, avg, div_eq_inv_mul]
  push_cast
  rfl

/-- Interpolation (HNVW II, Propositions 7.1.3 and 7.1.11): for `2m ≤ q ≤ 2m + 2`,
`(E ‖Σ ε_k x_k‖_{S_q}²)^{1/2} ≤ √(2m + 1) (Σ ‖x_k‖_{S_q}²)^{1/2}`, for symmetric `x_k`. -/
theorem lpNorm_two_schattenNorm_le_of_isHermitian {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hmq : 2 * m ≤ q)
    (hqm : q ≤ 2 * m + 2) (x : Fin N → Matrix n n ℝ) (hx : ∀ k, (x k).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m + 1) * √(∑ k, schattenNorm (ENNReal.ofReal q) (x k) ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq1 : 1 < q := by linarith
  have hq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq1
  have hqne : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq.pos).ne'
  have hq'ne : ENNReal.ofReal (q / (q - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 hq.symm.pos).ne'
  -- the norming function
  have hY : ∀ ε : Fin N → Bool, (∑ k, coin (ε k) • x k).IsHermitian := fun ε =>
    isSelfAdjoint_sum _ fun k _ => (hx k).smul (IsSelfAdjoint.all (coin (ε k)))
  obtain ⟨Φ, hΦ, hΦ1, hΦY⟩ := tts_exists_avg_trace_eq hq _ hY
  -- the bounds in the end points `2m` and `2m + 2`
  have hC₀ := fun y : Fin N → Matrix n n ℂ => lpNorm_complexSchattenNorm_le_of_even hm y
  have hC₁ := fun y : Fin N → Matrix n n ℂ =>
    lpNorm_complexSchattenNorm_le_of_even (Nat.le_add_left 1 m) y
  have e1 : 2 * ((m + 1 : ℕ) : ℝ) = 2 * m + 2 := by push_cast; ring
  have e2 : (2 * m + 2 - 1 : ℝ) = 2 * m + 1 := by ring
  rw [e1, e2] at hC₁
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := tts_exists_theta (p₀ := 2 * m) (p₁ := 2 * m + 2) (by linarith)
    (by linarith) hmq hqm
  have hmap : ∀ {B : Matrix n n ℝ}, B.IsHermitian → (B.map Complex.ofReal).IsHermitian :=
    fun hB => hB.map _ fun t => (Complex.conj_ofReal t).symm
  have h := tts_three_lines (Real.HolderConjugate.conjExponent (by linarith : (1 : ℝ) < 2 * m))
    (Real.HolderConjugate.conjExponent (by linarith : (1 : ℝ) < 2 * m + 2)) hq hθ0 hθ1 hθ
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC₀ hC₁ (fun ε => hmap (hΦ ε)) fun k => hmap (hx k)
  simp only [complexSchattenNorm_map_ofReal hqne, complexSchattenNorm_map_ofReal hq'ne] at h
  rw [ttsForm_map_ofReal, hΦY, Complex.norm_real, Real.norm_of_nonneg
    (lpNorm_nonneg (schattenNorm_nonneg _) 2 _)] at h
  -- both end point bounds are at most `√(2m + 1) (Σ ‖x_k‖²)^{1/2}`
  set Q := √(∑ k, schattenNorm (ENNReal.ofReal q) (x k) ^ 2)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  set P := √(avg fun ε => schattenNorm (ENNReal.ofReal (q / (q - 1))) (Φ ε) ^ 2)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hC : √(2 * m - 1) ≤ √(2 * m + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hR : 0 ≤ √(2 * m + 1 : ℝ) * Q := mul_nonneg (Real.sqrt_nonneg _) hQ
  have b0 : P * (√(2 * m - 1) * Q) ≤ √(2 * m + 1) * Q :=
    (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) hQ) hΦ1).trans
      (mul_le_mul_of_nonneg_right hC hQ)
  have b1 : P * (√(2 * m + 1) * Q) ≤ √(2 * m + 1) * Q := mul_le_of_le_one_left hR hΦ1
  refine h.trans ?_
  calc _ ≤ (√(2 * m + 1 : ℝ) * Q) ^ (1 - θ) * (√(2 * m + 1 : ℝ) * Q) ^ θ := by
        gcongr
    _ = √(2 * m + 1) * Q := by
        rw [← Real.rpow_add_of_nonneg hR (by linarith) hθ0, sub_add_cancel, Real.rpow_one]

/-- **Type 2 of the Schatten classes** (HNVW II, Proposition 7.1.11): for `q ≥ 2`, `S_q` has type 2
with constant `√(q + 1)`, in every size. -/
theorem isTypeTwoBound_schattenSpace {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)] :
    IsTypeTwoBound (SchattenSpace (ENNReal.ofReal q) n n) √(q + 1) := by
  intro N x
  have hq0 : 0 < q := by linarith
  -- `2m ≤ q ≤ 2m + 2` for `m = ⌊q/2⌋`
  set m := ⌊q / 2⌋₊ with hm_def
  have hm : 1 ≤ m := by
    rw [hm_def, Nat.one_le_floor_iff]
    linarith
  have hmq : 2 * (m : ℝ) ≤ q := by
    have := Nat.floor_le (by linarith : 0 ≤ q / 2)
    linarith
  have hqm : q ≤ 2 * m + 2 := by
    have := Nat.lt_floor_add_one (q / 2)
    linarith
  -- the dilations: `‖D (A)‖_{S_q} = 2^{1/q} ‖A‖_{S_q}`
  set X : Fin N → Matrix n n ℝ := fun k => SchattenSpace.ofMatrix.symm (x k)
  set c : ℝ := 2 ^ (1 / q) with hc
  have hc0 : 0 < c := by positivity
  have hD : ∀ A : Matrix n n ℝ, schattenNorm (ENNReal.ofReal q) (dilation A) ^ 2 =
      c ^ 2 * schattenNorm (ENNReal.ofReal q) A ^ 2 := fun A => by
    have h := congrArg (fun t => t ^ (1 / q)) (schattenNorm_dilation_rpow hq0 A)
    rw [Real.mul_rpow zero_le_two (Real.rpow_nonneg (schattenNorm_nonneg _ _) _),
      ← Real.rpow_mul (schattenNorm_nonneg _ _), ← Real.rpow_mul (schattenNorm_nonneg _ _),
      mul_one_div_cancel hq0.ne', Real.rpow_one, Real.rpow_one] at h
    rw [h, mul_pow]
  have hlin : ∀ ε : Fin N → Bool, dilation (∑ k, coin (ε k) • X k) =
      ∑ k, coin (ε k) • dilation (X k) := fun ε => by
    have h := map_sum dilationLinearMap (fun k => coin (ε k) • X k) Finset.univ
    simp only [map_smul] at h
    exact h
  have h := lpNorm_two_schattenNorm_le_of_isHermitian hm hmq hqm (fun k => dilation (X k))
    fun k => dilation_isHermitian (X k)
  rw [tts_lpNorm_two] at h
  simp only [← hlin, hD, avg_const_mul, ← Finset.mul_sum] at h
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0.le,
    mul_left_comm] at h
  have h' := le_of_mul_le_mul_left h hc0
  have hnorm : ∀ ε : Fin N → Bool, ‖∑ k, coin (ε k) • x k‖ =
      schattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • X k) := fun ε => by
    rw [SchattenSpace.norm_def, map_sum]
    simp only [map_smul, X]
  rw [tts_lpNorm_two]
  simp only [hnorm]
  refine h'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_nonneg _))

end BanachProbability
