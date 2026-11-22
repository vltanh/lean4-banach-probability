module

public import BanachProbability.TypeTwo.Basic
public import BanachProbability.Schatten.Complex
public import BanachProbability.KahaneKhintchine.Basic
import BanachProbability.Schatten.CubeDuality
import BanachProbability.Schatten.Dilation
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Type 2 of the Schatten classes

For `q ≥ 2` the Schatten class `S_q` of real square matrices of any size has type 2 with the
constant `√(q + 1)` (`isTypeTwoBound_schattenSpace`). The result is due to N. Tomczak-Jaegermann,
Studia Math. 50 (1974), 163–182, as cited by Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in
Banach spaces II* (2017), p. 146. The proof is that of HNVW II, Proposition 7.1.11, pp. 62–63, which
does not state a constant:

* for an even integer `q = 2m` the constant is at most that of the scalar Khintchine inequality, for
  which `√(2m − 1)` is taken (`lpNorm_schattenNorm_le_of_even`; HNVW II, Lemma 7.1.12, pp. 62–63):
  the trace is expanded, and Hölder's inequality compares each term with the scalar one;
* the other exponents follow by interpolation between `2m` and `2m + 2`
  (`lpNorm_two_schattenNorm_le_of_isHermitian`).

Departure from the source: for the interpolation the book uses the complex interpolation functor,
HNVW II, Proposition 7.1.3, pp. 55–56, with HNVW I, Theorem 2.2.6 (`L^p` spaces) and Proposition
D.3.1, pp. 574–575 (`[S_{p₀}, S_{p₁}]_θ = S_p`, both inclusions). Here the estimate is proved
directly, by duality and the three lines theorem (the argument of the Riesz–Thorin theorem), with
analytic families through the `x_k`, as in the first half of the proof of Proposition D.3.1, and
through a norming function of `Σ_k ε_k x_k`; the converse half of that proof is not needed. This is
done for symmetric matrices, with their spectral decomposition in place of the singular value
decomposition of the book; general real matrices are reduced to these by the dilation
`[[0, A], [Aᵀ, 0]]`.
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

/-- The expectation of a product of signs is nonnegative: if every sign occurs an even number of
times, then the product is nonnegative, and otherwise the expectation is `0`. -/
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

/-- Type 2 of `S_{2m}` (HNVW II, Lemma 7.1.12, pp. 62–63), even with the `L^{2m}` norm of the sum:
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

/-- Type 2 of `S_{2m}` for complex matrices, real signs and the `L²` norm of the sum, from the real
case by realification: `(E ‖Σ ε_k x_k‖_{S_{2m}}²)^{1/2} ≤ √(2m − 1) (Σ ‖x_k‖_{S_{2m}}²)^{1/2}`. -/
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
`ℓ² (S_{p_j})` to `L² (S_{p_j})`, `j = 0, 1`, with the complex interpolation functor. Here (a
departure from the source, see the beginning of the file) the matrices have a fixed size, and the
interpolation is written out with the three lines theorem: to bound `E tr ((Σ_k ε_k x_k) Φ (ε))`,
the Hermitian matrices `x_k` and `Φ (ε)` are put in analytic families `x_k^{[w]}`, `Φ (ε)^{[w']}`
(`ttsFamily`), which are bounded on the two lines by `‖x_k‖_{S_q}` and `‖Φ (ε)‖_{S_{q'}}`. -/

section Family

variable {A : Matrix n n ℂ}

/-- The eigenvalues `s sgn (λ_i) (|λ_i| / s)^w`, `s = ‖A‖_{S_q}`, of the analytic family through a
Hermitian matrix `A`; the power is written as an exponential. -/
private noncomputable def ttsCoeff (q : ℝ) (hA : A.IsHermitian) (w : ℂ) (i : n) : ℂ :=
  ((complexSchattenNorm (ENNReal.ofReal q) A * Real.sign (hA.eigenvalues i) : ℝ) : ℂ) *
    Complex.exp (w * (Real.log
      (|hA.eigenvalues i| / complexSchattenNorm (ENNReal.ofReal q) A) : ℝ))

/-- The analytic family through a Hermitian matrix `A = U diag (λ) Uᴴ`: with `s = ‖A‖_{S_q}`,
`A^{[w]} = U diag (s sgn (λ_i) (|λ_i| / s)^w) Uᴴ`, an entire function of `w` with `A^{[1]} = A`
(HNVW I, the first half of the proof of Proposition D.3.1, p. 574, with an explicit function of `w`
for the eigenvalues, and the spectral in place of the singular value decomposition). -/
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

/-- `A^{[1]} = A`. -/
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
  rw [ttsFamily, hc, ← eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hA]

/-- The entries of `A^{[w]}` are entire functions of `w`. -/
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

/-- On the line `Re w = q / p` the family has `‖A^{[w]}‖_{S_p} ≤ ‖A‖_{S_q} = s`:
`Σ_i |s sgn (λ_i) (|λ_i| / s)^w|^p ≤ s^p Σ_i |λ_i|^q / s^q ≤ s^p`. -/
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

/-- The bilinear form `E tr ((Σ_k ε_k y_k) Ψ (ε))`. -/
private noncomputable def ttsForm (y : Fin N → Matrix n n ℂ) (Ψ : (Fin N → Bool) → Matrix n n ℂ) :
    ℂ :=
  ((2 : ℂ) ^ N)⁻¹ * ∑ ε, ((∑ k, coin (ε k) • y k) * Ψ ε).trace

/-- The type 2 bound with constant `C` for sums of `N` complex matrices in `S_p`. -/
private def TtsBound (N : ℕ) (n : Type*) [Fintype n] [DecidableEq n] (p C : ℝ) : Prop :=
  ∀ y : Fin N → Matrix n n ℂ, SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) 2
      (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) ≤
    C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2)

/-- Hölder's inequality for the bilinear form, and a type 2 bound of `S_p`. -/
private theorem norm_ttsForm_le {p p' C : ℝ} (hp : p.HolderConjugate p') (hC : TtsBound N n p C)
    (y : Fin N → Matrix n n ℂ) (Ψ : (Fin N → Bool) → Matrix n n ℂ) :
    ‖ttsForm y Ψ‖ ≤ C * √(∑ k, complexSchattenNorm (ENNReal.ofReal p) (y k) ^ 2) *
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p')) 2 Ψ := by
  calc ‖ttsForm y Ψ‖ ≤ avg fun ε => ‖((∑ k, coin (ε k) • y k) * Ψ ε).trace‖ := by
        rw [ttsForm, avg, div_eq_inv_mul, norm_mul, norm_inv, norm_pow, Complex.norm_two]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ avg fun ε => complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • y k) *
          complexSchattenNorm (ENNReal.ofReal p') (Ψ ε) :=
        avg_mono fun ε => norm_trace_mul_le hp _ _
    _ ≤ SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) 2
            (fun ε : Fin N → Bool => ∑ k, coin (ε k) • y k) *
          SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p')) 2 Ψ :=
        avg_mul_le_rpow_mul_rpow Real.HolderConjugate.two_two
          (fun _ => complexSchattenNorm_nonneg _ _) fun _ => complexSchattenNorm_nonneg _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC y) (lpNorm_nonneg (complexSchattenNorm_nonneg _) _ _)

omit [DecidableEq n] in
/-- The bilinear form of entire families is entire. -/
private theorem differentiable_ttsForm {y : ℂ → Fin N → Matrix n n ℂ}
    {Ψ : ℂ → (Fin N → Bool) → Matrix n n ℂ} (hy : ∀ k i j, Differentiable ℂ fun z => y z k i j)
    (hΨ : ∀ ε i j, Differentiable ℂ fun z => Ψ z ε i j) :
    Differentiable ℂ fun z => ttsForm (y z) (Ψ z) := by
  simp only [ttsForm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply]
  fun_prop

section ThreeLines

variable {p p' q q' C : ℝ} {x : Fin N → Matrix n n ℂ} {Φ : (Fin N → Bool) → Matrix n n ℂ}

/-- The analytic function of the three lines theorem, with `s` in place of `1/p`:
`F (s) = E tr ((Σ_k ε_k x_k^{[q s]}) Φ (ε)^{[q' (1 − s)]})`. -/
private noncomputable def ttsFun (q q' : ℝ) (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) (s : ℂ) : ℂ :=
  ttsForm (fun k => ttsFamily q (hx k) (q * s)) fun ε => ttsFamily q' (hΦ ε) (q' * (1 - s))

private theorem differentiable_ttsFun (q q' : ℝ) (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) : Differentiable ℂ (ttsFun q q' hx hΦ) :=
  differentiable_ttsForm
    (fun k i j => (differentiable_ttsFamily q (hx k) i j).comp (by fun_prop))
    fun ε i j => (differentiable_ttsFamily q' (hΦ ε) i j).comp (by fun_prop)

/-- `F (1/q) = E tr ((Σ_k ε_k x_k) Φ (ε))`. -/
private theorem ttsFun_inv (hq : q.HolderConjugate q') (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) : ttsFun q q' hx hΦ ((q⁻¹ : ℝ) : ℂ) = ttsForm x Φ := by
  have h1 : (q : ℂ) * ((q⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hq.ne_zero, Complex.ofReal_one]
  have h2 : (q' : ℂ) * (1 - ((q⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, hq.one_sub_inv,
      mul_inv_cancel₀ hq.symm.ne_zero]
  simp only [ttsFun, h1, h2, ttsFamily_one hq.pos, ttsFamily_one hq.symm.pos]

/-- The bound of `F (s)` from a type 2 bound of `S_p` and bounds of the families. -/
private theorem norm_ttsFun_le {c c' : ℝ} (hp : p.HolderConjugate p') (hC0 : 0 ≤ C)
    (hC : TtsBound N n p C) (hx : ∀ k, (x k).IsHermitian) (hΦ : ∀ ε, (Φ ε).IsHermitian) {s : ℂ}
    (h : ∀ k, complexSchattenNorm (ENNReal.ofReal p) (ttsFamily q (hx k) (q * s)) ≤
      c * complexSchattenNorm (ENNReal.ofReal q) (x k))
    (h' : ∀ ε, complexSchattenNorm (ENNReal.ofReal p') (ttsFamily q' (hΦ ε) (q' * (1 - s))) ≤
      c' * complexSchattenNorm (ENNReal.ofReal q') (Φ ε)) :
    ‖ttsFun q q' hx hΦ s‖ ≤ C * √(∑ k, (c * complexSchattenNorm (ENNReal.ofReal q) (x k)) ^ 2) *
      SignCube.lpNorm (fun A => c' * complexSchattenNorm (ENNReal.ofReal q') A) 2 Φ := by
  refine (norm_ttsForm_le hp hC _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ hC0) ?_
    (lpNorm_nonneg (complexSchattenNorm_nonneg _) _ _) (mul_nonneg hC0 (Real.sqrt_nonneg _)))
  · exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
      pow_le_pow_left₀ (complexSchattenNorm_nonneg _ _) (h k) 2)
  · exact Real.rpow_le_rpow
      (avg_nonneg fun ε => Real.rpow_nonneg (complexSchattenNorm_nonneg _ _) _)
      (avg_mono fun ε => Real.rpow_le_rpow (complexSchattenNorm_nonneg _ _) (h' ε) zero_le_two)
      (by norm_num)

/-- The bound of `F` on the line `Re s = 1/p`:
`|F (s)| ≤ C (Σ ‖x_k‖_{S_q}²)^{1/2} ‖Φ‖_{L² (S_{q'})}`. -/
private theorem norm_ttsFun_le_of_re_eq (hp : p.HolderConjugate p') (hq : q.HolderConjugate q')
    (hC0 : 0 ≤ C) (hC : TtsBound N n p C) (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) {s : ℂ} (hs : s.re = p⁻¹) :
    ‖ttsFun q q' hx hΦ s‖ ≤ C * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2) *
      SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q')) 2 Φ := by
  have h := norm_ttsFun_le (c := 1) (c' := 1) (q := q) (q' := q') hp hC0 hC hx hΦ (s := s)
    (fun k => (complexSchattenNorm_ttsFamily_le hp.pos hq.pos _ (by
      rw [Complex.re_ofReal_mul, hs, div_eq_mul_inv])).trans_eq (one_mul _).symm)
    (fun ε => (complexSchattenNorm_ttsFamily_le hp.symm.pos hq.symm.pos _ (by
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hs, hp.one_sub_inv,
        div_eq_mul_inv])).trans_eq (one_mul _).symm)
  simpa only [one_mul] using h

/-- `F` is bounded on the strip `0 ≤ Re s ≤ 1`. -/
private theorem exists_norm_ttsFun_le (hp : p.HolderConjugate p') (hq : q.HolderConjugate q')
    (hC0 : 0 ≤ C) (hC : TtsBound N n p C) (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) :
    ∃ B : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖ttsFun q q' hx hΦ s‖ ≤ B := by
  refine ⟨_, fun s h0 h1 => norm_ttsFun_le hp hC0 hC hx hΦ
    (fun k => complexSchattenNorm_ttsFamily_le_card hp.pos hq.pos _ ?_)
    fun ε => complexSchattenNorm_ttsFamily_le_card hp.symm.pos hq.symm.pos _ ?_⟩
  · rw [Complex.re_ofReal_mul]
    exact mul_nonneg hq.nonneg h0
  · rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
    exact mul_nonneg hq.symm.nonneg (sub_nonneg.2 h1)

/-- Interpolation of type 2, in the dual formulation (instead of HNVW II, Proposition 7.1.3, with
HNVW I, Proposition D.3.1): the three lines theorem for `F (1/p (z))`,
`1/p (z) = (1 − z)/p₀ + z/p₁`. -/
private theorem tts_three_lines {p₀ p₀' p₁ p₁' θ C₀ C₁ : ℝ} (hp₀ : p₀.HolderConjugate p₀')
    (hp₁ : p₁.HolderConjugate p₁') (hq : q.HolderConjugate q') (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθ : 1 / q = (1 - θ) / p₀ + θ / p₁) (hC₀0 : 0 ≤ C₀) (hC₁0 : 0 ≤ C₁)
    (hC₀ : TtsBound N n p₀ C₀) (hC₁ : TtsBound N n p₁ C₁) (hx : ∀ k, (x k).IsHermitian)
    (hΦ : ∀ ε, (Φ ε).IsHermitian) :
    ‖ttsForm x Φ‖ ≤
      (C₀ * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2) *
        SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q')) 2 Φ) ^ (1 - θ) *
      (C₁ * √(∑ k, complexSchattenNorm (ENNReal.ofReal q) (x k) ^ 2) *
        SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q')) 2 Φ) ^ θ := by
  -- `r (z) = 1 / p (z)`, and its real part
  set r : ℂ → ℂ := fun z => (1 - z) / p₀ + z / p₁ with hr
  have hre : ∀ z, (r z).re = (1 - z.re) / p₀ + z.re / p₁ := fun z => by
    simp only [hr, Complex.add_re, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]
  have hrθ : r θ = ((q⁻¹ : ℝ) : ℂ) := by
    rw [← one_div, hθ]
    simp only [hr]
    push_cast
    rfl
  have hd : Differentiable ℂ fun z => ttsFun q q' hx hΦ (r z) :=
    (differentiable_ttsFun q q' hx hΦ).comp (by fun_prop)
  obtain ⟨B, hB⟩ := exists_norm_ttsFun_le hp₀ hq hC₀0 hC₀ hx hΦ
  have hbdd : BddAbove ((norm ∘ fun z => ttsFun q q' hx hΦ (r z)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, ⟨hz0, hz1⟩, rfl⟩
    have e1 : (1 - z.re) / p₀ ≤ 1 - z.re := div_le_self (sub_nonneg.2 hz1) hp₀.lt.le
    have e2 : z.re / p₁ ≤ z.re := div_le_self hz0 hp₁.lt.le
    have e3 : 0 ≤ (1 - z.re) / p₀ := div_nonneg (sub_nonneg.2 hz1) hp₀.nonneg
    have e4 : 0 ≤ z.re / p₁ := div_nonneg hz0 hp₁.nonneg
    refine hB _ ?_ ?_ <;> rw [hre] <;> linarith
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' _
    (z := (θ : ℂ)) ⟨by simpa using hθ0, by simpa using hθ1⟩ hd.diffContOnCl hbdd
    (fun z hz => norm_ttsFun_le_of_re_eq hp₀ hq hC₀0 hC₀ hx hΦ (s := r z)
      (by rw [hre, show z.re = 0 from hz]; simp))
    (fun z hz => norm_ttsFun_le_of_re_eq hp₁ hq hC₁0 hC₁ hx hΦ (s := r z)
      (by rw [hre, show z.re = 1 from hz]; simp))
  rwa [hrθ, ttsFun_inv hq, Complex.ofReal_re] at h

end ThreeLines

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
private theorem ttsForm_map_ofReal (y : Fin N → Matrix n n ℝ)
    (Ψ : (Fin N → Bool) → Matrix n n ℝ) :
    ttsForm (fun k => (y k).map Complex.ofReal) (fun ε => (Ψ ε).map Complex.ofReal) =
      ((avg fun ε => ((∑ k, coin (ε k) • y k) * Ψ ε).trace : ℝ) : ℂ) := by
  have h : ∀ ε : Fin N → Bool, ((∑ k, coin (ε k) • (y k).map Complex.ofReal) *
      (Ψ ε).map Complex.ofReal).trace =
        ((((∑ k, coin (ε k) • y k) * Ψ ε).trace : ℝ) : ℂ) := fun ε => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
  simp only [ttsForm, h, avg, div_eq_inv_mul]
  push_cast
  rfl

/-- Interpolation between `2m` and `2m + 2` (HNVW II, Proposition 7.1.11, pp. 62–63): for
`2m ≤ q ≤ 2m + 2`, `(E ‖Σ ε_k x_k‖_{S_q}²)^{1/2} ≤ √(2m + 1) (Σ ‖x_k‖_{S_q}²)^{1/2}`, for symmetric
`x_k`. Departure from the source: the book uses the complex interpolation functor (Proposition
7.1.3, pp. 55–56, with HNVW I, Theorem 2.2.6 and Proposition D.3.1, pp. 574–575); here the bilinear
form `E tr ((Σ_k ε_k x_k) Φ (ε))` with a norming function `Φ` is estimated by the three lines
theorem. -/
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
  obtain ⟨Φ, hΦ, hΦ1, hΦY⟩ := exists_avg_trace_mul_eq_lpNorm_of_holderConjugate hq
    Real.HolderConjugate.two_two (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) fun ε =>
      isSelfAdjoint_sum _ fun k _ => (hx k).smul (IsSelfAdjoint.all (coin (ε k)))
  -- the bounds in the end points `2m` and `2m + 2`
  have hC₀ : TtsBound N n (2 * m) √(2 * m - 1) := lpNorm_complexSchattenNorm_le_of_even hm
  have hC₁ : TtsBound N n (2 * m + 2) √(2 * m + 1) := by
    have h := fun y : Fin N → Matrix n n ℂ =>
      lpNorm_complexSchattenNorm_le_of_even (Nat.le_add_left 1 m) y
    have e1 : 2 * ((m + 1 : ℕ) : ℝ) = 2 * m + 2 := by push_cast; ring
    have e2 : (2 * m + 2 - 1 : ℝ) = 2 * m + 1 := by ring
    rwa [e1, e2] at h
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := tts_exists_theta (p₀ := 2 * m) (p₁ := 2 * m + 2) (by linarith)
    (by linarith) hmq hqm
  have hmap : ∀ {B : Matrix n n ℝ}, B.IsHermitian → (B.map Complex.ofReal).IsHermitian :=
    fun hB => hB.map _ fun t => (Complex.conj_ofReal t).symm
  have h := tts_three_lines (Real.HolderConjugate.conjExponent (by linarith : (1 : ℝ) < 2 * m))
    (Real.HolderConjugate.conjExponent (by linarith : (1 : ℝ) < 2 * m + 2)) hq hθ0 hθ1 hθ
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC₀ hC₁ (fun k => hmap (hx k)) fun ε => hmap (hΦ ε)
  have hP1 : SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (q / (q - 1)))) 2
      (fun ε => (Φ ε).map Complex.ofReal) ≤ 1 := by
    simpa only [SignCube.lpNorm, complexSchattenNorm_map_ofReal hq'ne] using hΦ1
  simp only [complexSchattenNorm_map_ofReal hqne] at h
  rw [ttsForm_map_ofReal, hΦY, Complex.norm_real, Real.norm_of_nonneg
    (lpNorm_nonneg (schattenNorm_nonneg _) 2 _)] at h
  -- both end point bounds are at most `√(2m + 1) (Σ ‖x_k‖²)^{1/2}`
  set Q := √(∑ k, schattenNorm (ENNReal.ofReal q) (x k) ^ 2)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  set P := SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (q / (q - 1)))) 2
    (fun ε => (Φ ε).map Complex.ofReal)
  have hP : 0 ≤ P := lpNorm_nonneg (complexSchattenNorm_nonneg _) _ _
  have hC : √(2 * m - 1) ≤ √(2 * m + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hR : 0 ≤ √(2 * m + 1 : ℝ) * Q := mul_nonneg (Real.sqrt_nonneg _) hQ
  have b0 : √(2 * m - 1) * Q * P ≤ √(2 * m + 1) * Q :=
    (mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) hQ) hP1).trans
      (mul_le_mul_of_nonneg_right hC hQ)
  have b1 : √(2 * m + 1) * Q * P ≤ √(2 * m + 1) * Q := mul_le_of_le_one_right hR hP1
  refine h.trans ?_
  calc _ ≤ (√(2 * m + 1 : ℝ) * Q) ^ (1 - θ) * (√(2 * m + 1 : ℝ) * Q) ^ θ := by
        gcongr
    _ = √(2 * m + 1) * Q := by
        rw [← Real.rpow_add_of_nonneg hR (by linarith) hθ0, sub_add_cancel, Real.rpow_one]

/-- **Type 2 of the Schatten classes** (Tomczak-Jaegermann 1974; HNVW II, Proposition 7.1.11, pp.
62–63, without a constant): for `q ≥ 2`, the space `S_q` of real square matrices, of every size, has
type 2 with constant `√(q + 1)`. The symmetric case is `lpNorm_two_schattenNorm_le_of_isHermitian`;
the general case follows by the dilation `D (A) = [[0, A], [Aᵀ, 0]]`, `‖D (A)‖_{S_q} = 2^{1/q}
‖A‖_{S_q}` (the book works with the singular value decomposition instead). -/
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
