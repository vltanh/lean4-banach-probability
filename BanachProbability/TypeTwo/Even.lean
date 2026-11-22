module

public import BanachProbability.TypeTwo.Basic
public import BanachProbability.Schatten.Complex
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Type 2 of the Schatten classes with even exponents

For matrices `A_1, …, A_N` and `k ≥ 1`, with `M_{2k} = ((2k)! / (2^k k!))^{1/2k}`,

`(E ‖Σ ε_i A_i‖_{S_{2k}}^{2k})^{1/2k} ≤ M_{2k} (Σ ‖A_i‖_{S_{2k}}²)^{1/2}`

(`lpNorm_schattenNorm_le_of_even`, `lpNorm_complexSchattenNorm_le_of_even`).

Source: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, Theorem 3.1 (ii), pp.
176–178, (3.14)–(3.15): the trace is expanded; by the general Horn inequality (Lemma 1.1) each trace
is at most `Σ_j Π s_j (C_ν)`, so that the whole is at most `Σ_j E (Σ ε_i s_j (A_i))^{2k}`
(`avg_schattenNorm_rpow_le_sum`); the multinomial coefficients are compared
(`(2k)! / Π (2β_i)! ≤ M_{2k}^{2k} k! / Π β_i!`, `avg_sum_coin_mul_pow_le`), and the triangle
inequality in `ℓ_k` finishes. Complex matrices are treated by realification.
-/

@[expose] public section

open scoped ENNReal Matrix Nat

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The constant `M_{2k}` -/

/-- `M_{2k} ≥ 0`. -/
theorem evenKhintchineConst_nonneg (k : ℕ) : 0 ≤ evenKhintchineConst k :=
  Real.rpow_nonneg (by positivity) _

/-- `M_{2k}^{2k} = (2k)! / (2^k k!)`. -/
private theorem evenKhintchineConst_pow {k : ℕ} (hk : 1 ≤ k) :
    evenKhintchineConst k ^ (2 * k) = ((2 * k).factorial : ℝ) / (2 ^ k * k.factorial) := by
  rw [evenKhintchineConst, one_div, show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; rfl]
  exact Real.rpow_inv_natCast_pow (by positivity) (by omega)

/-- `(2k − 1)!! ≤ (2k − 1)^k`, with `k = r + 1`. -/
private theorem doubleFactorial_le_pow (r : ℕ) : (2 * r + 1)‼ ≤ (2 * r + 1) ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 2 by ring, Nat.doubleFactorial_add_two, pow_succ']
    exact Nat.mul_le_mul_left _ (ih.trans (Nat.pow_le_pow_left (by omega) _))

/-- `M_{2k} ≤ √(2k − 1)`. -/
theorem evenKhintchineConst_le {k : ℕ} (hk : 1 ≤ k) : evenKhintchineConst k ≤ √(2 * k - 1) := by
  refine (pow_le_pow_iff_left₀ (evenKhintchineConst_nonneg k) (Real.sqrt_nonneg _)
    (by omega : 2 * k ≠ 0)).1 ?_
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [evenKhintchineConst_pow hk, pow_mul, Real.sq_sqrt (by linarith),
    div_le_iff₀ (by positivity)]
  -- `(2k)! = (2k)!! (2k − 1)!! = 2^k k! (2k − 1)!!`
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h : (2 * (r + 1)).factorial ≤
      (2 * r + 1) ^ (r + 1) * (2 ^ (r + 1) * (r + 1).factorial) := by
    rw [← Nat.doubleFactorial_two_mul, show 2 * (r + 1) = 2 * r + 1 + 1 by ring,
      Nat.factorial_eq_mul_doubleFactorial, mul_comm]
    exact Nat.mul_le_mul_right _ (doubleFactorial_le_pow r)
  have h' : (((2 * (r + 1)).factorial : ℕ) : ℝ) ≤
      (2 * r + 1) ^ (r + 1) * (2 ^ (r + 1) * ((r + 1).factorial : ℕ)) := by exact_mod_cast h
  refine h'.trans_eq ?_
  push_cast
  ring

/-! ### The scalar inequality -/

/-- `E Π ε_i^{β_i}` is `1` if all the `β_i` are even, and `0` otherwise (Tomczak-Jaegermann (1974),
p. 176). -/
private theorem avg_prod_coin_pow (β : Fin N → ℕ) :
    (avg fun ε : Fin N → Bool => ∏ i, coin (ε i) ^ β i) = if ∀ i, Even (β i) then 1 else 0 := by
  split_ifs with h
  · have h1 : ∀ ε : Fin N → Bool, ∏ i, coin (ε i) ^ β i = 1 := fun ε =>
      Finset.prod_eq_one fun i _ => by
        obtain ⟨c, hc⟩ := h i
        rw [hc, pow_add, ← mul_pow, coin_mul_self, one_pow]
    simp only [h1, avg_const]
  · obtain ⟨j, hj⟩ := not_forall.1 h
    refine scb_avg_eq_zero_of_flip j fun ε => ?_
    have hi : ∀ i, coin (SignCube.flip j ε i) ^ β i =
        (if i = j then -1 else 1) * coin (ε i) ^ β i := fun i => by
      split_ifs with hij
      · rw [hij, flip_apply_self, coin_not, (Nat.not_even_iff_odd.1 hj).neg_pow, neg_one_mul]
      · rw [flip_apply_of_ne hij, one_mul]
    simp only [hi, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true,
      neg_one_mul]

/-- The comparison of the multinomial coefficients (Tomczak-Jaegermann (1974), p. 177):
`(2k)! / Π (2β_i)! ≤ ((2k)! / (2^k k!)) (k! / Π β_i!)` if `Σ β_i = k`, since `(2β)! ≥ 2^β β!`; here
multiplied by `2^k k!`. (The source refers to the literature.) -/
private theorem multinomial_two_mul_le {k : ℕ} {β : Fin N → ℕ} (hβ : ∑ i, β i = k) :
    Nat.multinomial Finset.univ (fun i => 2 * β i) * (2 ^ k * k.factorial) ≤
      (2 * k).factorial * Nat.multinomial Finset.univ β := by
  have h1 := Nat.multinomial_spec Finset.univ (fun i => 2 * β i)
  have h2 := Nat.multinomial_spec Finset.univ β
  rw [← Finset.mul_sum, hβ] at h1
  rw [hβ] at h2
  have h3 : 2 ^ k * ∏ i, (β i).factorial ≤ ∏ i, (2 * β i).factorial := by
    rw [← hβ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod fun i _ => Nat.two_pow_mul_factorial_le_factorial_two_mul _
  calc Nat.multinomial Finset.univ (fun i => 2 * β i) * (2 ^ k * k.factorial)
      = (2 ^ k * ∏ i, (β i).factorial) * Nat.multinomial Finset.univ (fun i => 2 * β i) *
          Nat.multinomial Finset.univ β := by rw [← h2]; ring
    _ ≤ (∏ i, (2 * β i).factorial) * Nat.multinomial Finset.univ (fun i => 2 * β i) *
          Nat.multinomial Finset.univ β := by gcongr
    _ = (2 * k).factorial * Nat.multinomial Finset.univ β := by rw [h1]

/-- The scalar part of the argument: in the expansion of the power, the terms with an odd exponent
have expectation `0` (Tomczak-Jaegermann (1974), pp. 176–177), so
`E (Σ ε_i a_i)^{2k} = Σ_{β_1 + ⋯ + β_N = k} ((2k)! / Π (2β_i)!) Π a_i^{2β_i}`. -/
private theorem avg_sum_coin_mul_pow (k : ℕ) (a : Fin N → ℝ) :
    (avg fun ε : Fin N → Bool => (∑ i, coin (ε i) * a i) ^ (2 * k)) =
      ∑ β ∈ Finset.piAntidiag Finset.univ k,
        (Nat.multinomial Finset.univ (fun i => 2 * β i) : ℝ) * ∏ i, a i ^ (2 * β i) := by
  have hexp : ∀ ε : Fin N → Bool, (∑ i, coin (ε i) * a i) ^ (2 * k) =
      ∑ β ∈ Finset.piAntidiag Finset.univ (2 * k),
        ((Nat.multinomial Finset.univ β : ℝ) * ∏ i, a i ^ β i) * ∏ i, coin (ε i) ^ β i := by
    intro ε
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [mul_pow, Finset.prod_mul_distrib]
    ring
  -- the multi-indices with even entries are the `2β`
  have heven : (Finset.piAntidiag Finset.univ (2 * k)).filter
      (fun β : Fin N → ℕ => ∀ i, Even (β i)) = (Finset.piAntidiag Finset.univ k).map
        ⟨(2 • ·), nsmul_right_injective two_ne_zero⟩ := by
    rw [Finset.map_nsmul_piAntidiag Finset.univ k two_ne_zero]
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_imp_iff, even_iff_two_dvd]
  simp only [hexp, avg_sum, avg_const_mul, avg_prod_coin_pow, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, heven, Finset.sum_map]
  rfl

/-- The scalar part of the argument (Tomczak-Jaegermann (1974), p. 177, for the numbers
`a_i = s_j (A_i)`), which is the Khintchine inequality for an even exponent, with the constant
`M_{2k}`: `E (Σ ε_i a_i)^{2k} ≤ M_{2k}^{2k} (Σ a_i²)^k`. -/
theorem avg_sum_coin_mul_pow_le {k : ℕ} (hk : 1 ≤ k) (a : Fin N → ℝ) :
    (avg fun ε : Fin N → Bool => (∑ i, coin (ε i) * a i) ^ (2 * k)) ≤
      evenKhintchineConst k ^ (2 * k) * (∑ i, a i ^ 2) ^ k := by
  rw [avg_sum_coin_mul_pow, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum,
    evenKhintchineConst_pow hk]
  refine Finset.sum_le_sum fun β hβ => ?_
  have h : ((Nat.multinomial Finset.univ (fun i => 2 * β i) * (2 ^ k * k.factorial) : ℕ) : ℝ) ≤
      (((2 * k).factorial * Nat.multinomial Finset.univ β : ℕ) : ℝ) :=
    Nat.cast_le.2 (multinomial_two_mul_le (Finset.mem_piAntidiag.1 hβ).1)
  push_cast at h
  simp only [← pow_mul]
  rw [← mul_assoc, div_mul_eq_mul_div]
  refine mul_le_mul_of_nonneg_right ((le_div_iff₀ (by positivity)).2 h)
    (Finset.prod_nonneg fun i _ => ?_)
  rw [pow_mul]
  positivity

/-! ### The expansion of the trace -/

/-- `‖u‖_{S_{2k}}^{2k} = tr ((uᵀ u)^k)`. -/
private theorem schattenNorm_rpow_eq_trace_pow {k : ℕ} (hk : 1 ≤ k) (u : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal (2 * k)) u ^ (2 * k : ℝ) = ((uᵀ * u) ^ k).trace := by
  have hk0 : (0 : ℝ) < 2 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hA : (uᴴ * u).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self u
  have h := trace_cfc_eq_sum hA (fun t => t ^ k)
  rw [cfc_pow_id (uᴴ * u) k hA.isSelfAdjoint] at h
  rw [schattenNorm_ofReal_rpow hk0, ← Matrix.conjTranspose_eq_transpose_of_trivial, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← singularValue_sq, ← pow_mul, ← Real.rpow_natCast]
  push_cast
  rfl

/-- The singular values of a square matrix and of its transpose are equal: `A Aᵀ` and `Aᵀ A` have
the same characteristic polynomial. -/
private theorem sortedSingularValue_transpose (A : Matrix n n ℝ) (j : ℕ) :
    sortedSingularValue Aᵀ j = sortedSingularValue A j := by
  have hc : (Aᵀᴴ * Aᵀ).charpoly = (Aᴴ * A).charpoly := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, Matrix.charpoly_mul_comm]
  have h : (Matrix.isHermitian_conjTranspose_mul_self Aᵀ).eigenvalues₀ =
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ := by
    rw [← List.ofFn_inj, ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀,
      ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀, hc]
  unfold sortedSingularValue
  rw [h]

/-- The letters `C_1, …, C_{2k}` of a word `C` (Tomczak-Jaegermann (1974), p. 176, condition (+)):
`C_{2l−1} = A_mᵀ` and `C_{2l} = A_{m'}`, where `(m, m')` is the `l`-th entry of `σ`. -/
private def letters {k : ℕ} (x : Fin N → Matrix n n ℝ) (σ : Fin k → Fin N × Fin N) :
    List (Matrix n n ℝ) :=
  (List.ofFn fun l => [(x (σ l).1)ᵀ, x (σ l).2]).flatten

/-- The number `b_m (C)` of the `ν` such that `C_ν` is `A_mᵀ` or `A_m`. -/
private def letterCount {k : ℕ} (σ : Fin k → Fin N × Fin N) (m : Fin N) : ℕ :=
  (Finset.univ.filter fun l => (σ l).1 = m).card + (Finset.univ.filter fun l => (σ l).2 = m).card

/-- The signs of a word are `Π_m ε_m^{b_m (C)}`. -/
private theorem prod_coin_eq {k : ℕ} (σ : Fin k → Fin N × Fin N) (ε : Fin N → Bool) :
    ∏ l, (coin (ε (σ l).1) * coin (ε (σ l).2)) = ∏ m, coin (ε m) ^ letterCount σ m := by
  rw [Finset.prod_mul_distrib,
    ← Finset.prod_fiberwise' Finset.univ (fun l => (σ l).1) fun m => coin (ε m),
    ← Finset.prod_fiberwise' Finset.univ (fun l => (σ l).2) fun m => coin (ε m)]
  simp only [Finset.prod_const, letterCount, pow_add, Finset.prod_mul_distrib]

/-- The word `C = C_1 ⋯ C_{2k}`, the letters grouped in pairs. -/
private theorem prod_letters {k : ℕ} (x : Fin N → Matrix n n ℝ) (σ : Fin k → Fin N × Fin N) :
    (letters x σ).prod = (List.ofFn fun l => (x (σ l).1)ᵀ * x (σ l).2).prod := by
  rw [letters, List.prod_flatten, List.map_ofFn]
  simp [Function.comp_def]

/-- `Π_ν s_j (C_ν)`, since the singular values of `A_m` and `A_mᵀ` are equal. -/
private theorem prod_map_letters {k : ℕ} (x : Fin N → Matrix n n ℝ) (σ : Fin k → Fin N × Fin N)
    (j : ℕ) : ((letters x σ).map fun A => sortedSingularValue A j).prod =
      ∏ l, (sortedSingularValue (x (σ l).1) j * sortedSingularValue (x (σ l).2) j) := by
  rw [letters, List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  simp [sortedSingularValue_transpose]

/-- `|tr C| ≤ Σ_j s_j (C) ≤ Σ_j Π_ν s_j (C_ν)` (Tomczak-Jaegermann (1974), p. 177), by Lemma 1.1 and
`s_j (Aᵀ) = s_j (A)`. -/
private theorem abs_trace_word_le {k : ℕ} (x : Fin N → Matrix n n ℝ)
    (σ : Fin k → Fin N × Fin N) :
    |(letters x σ).prod.trace| ≤ ∑ j ∈ Finset.range (Fintype.card n),
      ∏ l, (sortedSingularValue (x (σ l).1) j * sortedSingularValue (x (σ l).2) j) := by
  have h1 := schattenNorm_eq_sum_sortedSingularValue one_pos (letters x σ).prod
  simp only [ENNReal.ofReal_one, Real.rpow_one, div_one] at h1
  simp only [← prod_map_letters]
  exact (abs_trace_le_schattenNorm_one _).trans
    (h1.trans_le (sum_sortedSingularValue_prod_le (letters x σ) _))

/-- The expansion of a power of a sum in an algebra. -/
private theorem sum_smul_pow {ι A : Type*} [Fintype ι] [Ring A] [Algebra ℝ A] (k : ℕ)
    (c : ι → ℝ) (y : ι → A) :
    (∑ i, c i • y i) ^ k =
      ∑ σ : Fin k → ι, (∏ l, c (σ l)) • (List.ofFn fun l => y (σ l)).prod := by
  classical
  have h := (MultilinearMap.mkPiAlgebraFin ℝ k A).map_sum fun (_ : Fin k) i => c i • y i
  rw [MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate] at h
  rw [h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ (MultilinearMap.mkPiAlgebraFin ℝ k A) (fun l => c (σ l))
    (fun l => y (σ l)), MultilinearMap.mkPiAlgebraFin_apply]

/-- `‖Σ ε_i A_i‖_{S_{2k}}^{2k} = Σ_C tr (C) Π_m ε_m^{b_m (C)}`, the sum over all the words
`C = C_1 ⋯ C_{2k}` of the condition (+) (Tomczak-Jaegermann (1974), p. 176). -/
private theorem schattenNorm_sum_rpow_eq {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℝ)
    (ε : Fin N → Bool) :
    schattenNorm (ENNReal.ofReal (2 * k)) (∑ i, coin (ε i) • x i) ^ (2 * k : ℝ) =
      ∑ σ : Fin k → Fin N × Fin N,
        (letters x σ).prod.trace * ∏ m, coin (ε m) ^ letterCount σ m := by
  have h : (∑ i, coin (ε i) • x i)ᵀ * ∑ i, coin (ε i) • x i =
      ∑ p : Fin N × Fin N, (coin (ε p.1) * coin (ε p.2)) • ((x p.1)ᵀ * x p.2) := by
    rw [Matrix.transpose_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [Matrix.transpose_smul, smul_mul_smul_comm]
  rw [schattenNorm_rpow_eq_trace_pow hk, h, sum_smul_pow, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul, mul_comm, prod_coin_eq, prod_letters]

/-- The same expansion for scalars: `(Σ ε_i a_i)^{2k} = Σ_C (Π_ν a (C_ν)) Π_m ε_m^{b_m (C)}`. -/
private theorem sum_coin_mul_pow_eq (k : ℕ) (a : Fin N → ℝ) (ε : Fin N → Bool) :
    (∑ i, coin (ε i) * a i) ^ (2 * k) =
      ∑ σ : Fin k → Fin N × Fin N,
        (∏ l, (a (σ l).1 * a (σ l).2)) * ∏ m, coin (ε m) ^ letterCount σ m := by
  have h : (∑ i, coin (ε i) * a i) ^ 2 =
      ∑ p : Fin N × Fin N, (coin (ε p.1) * coin (ε p.2)) • (a p.1 * a p.2) := by
    rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [smul_eq_mul, mul_mul_mul_comm]
  rw [pow_mul, h, sum_smul_pow]
  simp only [List.prod_ofFn, smul_eq_mul, mul_comm, prod_coin_eq]

/-- Tomczak-Jaegermann (1974), pp. 176–177, (3.14) and Lemma 1.1:
`E ‖Σ ε_i A_i‖_{S_{2k}}^{2k} ≤ Σ_j E (Σ_i ε_i s_j (A_i))^{2k}`. The right-hand side is the
expression `Σ_j Σ_{β_1 + ⋯ + β_N = k} ((2k)! / Π_i (2β_i)!) Π_i s_j (A_i)^{2β_i}` of the source,
written as an expectation. -/
theorem avg_schattenNorm_rpow_le_sum {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℝ) :
    (avg fun ε : Fin N → Bool =>
        schattenNorm (ENNReal.ofReal (2 * k)) (∑ i, coin (ε i) • x i) ^ (2 * k : ℝ)) ≤
      ∑ j ∈ Finset.range (Fintype.card n),
        avg fun ε : Fin N → Bool => (∑ i, coin (ε i) * sortedSingularValue (x i) j) ^ (2 * k) := by
  -- (3.14): only the words with even `b_m (C)` contribute, on both sides
  simp only [schattenNorm_sum_rpow_eq hk, sum_coin_mul_pow_eq, avg_sum, avg_const_mul,
    avg_prod_coin_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun σ _ => ?_
  split_ifs
  · exact (le_abs_self _).trans (abs_trace_word_le x σ)
  · rw [Finset.sum_const_zero]

/-! ### The triangle inequality in `ℓ_k` -/

/-- The triangle inequality in `ℓ_p` for several nonnegative terms. -/
private theorem rpow_sum_rpow_sum_le {ι κ : Type*} (s : Finset κ) (t : Finset ι) {p : ℝ}
    (hp : 1 ≤ p) {f : ι → κ → ℝ} (hf : ∀ i j, 0 ≤ f i j) :
    (∑ j ∈ s, (∑ i ∈ t, f i j) ^ p) ^ (1 / p) ≤ ∑ i ∈ t, (∑ j ∈ s, f i j ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Real.Lp_add_le_of_nonneg s hp (fun j _ => hf i j)
      fun j _ => Finset.sum_nonneg fun i _ => hf i j).trans (add_le_add_right ih _)

/-- `(Σ_j s_j (A)^{2k})^{1/k} = ‖A‖_{S_{2k}}²`. -/
private theorem rpow_sum_sortedSingularValue {k : ℕ} (hk : 1 ≤ k) (A : Matrix n n ℝ) :
    (∑ j ∈ Finset.range (Fintype.card n), (sortedSingularValue A j ^ 2) ^ (k : ℝ)) ^ (1 / k : ℝ) =
      schattenNorm (ENNReal.ofReal (2 * k)) A ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [schattenNorm_eq_sum_sortedSingularValue (by linarith), ← Real.rpow_mul_natCast
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (sortedSingularValue_nonneg A j) _)]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Real.rpow_natCast_mul (sortedSingularValue_nonneg A j)]
    norm_num
  · push_cast
    field_simp

/-- **Type 2 of `S_{2k}`** (Tomczak-Jaegermann (1974), (3.15), p. 178), real matrices:
`(E ‖Σ ε_i A_i‖_{S_{2k}}^{2k})^{1/2k} ≤ M_{2k} (Σ ‖A_i‖_{S_{2k}}²)^{1/2}`. -/
theorem lpNorm_schattenNorm_le_of_even {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k * √(∑ i, schattenNorm (ENNReal.ofReal (2 * k)) (x i) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set T : ℝ := ∑ j ∈ Finset.range (Fintype.card n),
    (∑ i, sortedSingularValue (x i) j ^ 2) ^ (k : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
  -- the scalar inequality, for every `j`
  have h1 : (avg fun ε : Fin N → Bool =>
      schattenNorm (ENNReal.ofReal (2 * k)) (∑ i, coin (ε i) • x i) ^ (2 * k : ℝ)) ≤
        evenKhintchineConst k ^ (2 * k : ℝ) * T := by
    refine (avg_schattenNorm_rpow_le_sum hk x).trans ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := avg_sum_coin_mul_pow_le hk fun i => sortedSingularValue (x i) j
    rwa [← Real.rpow_natCast, ← Real.rpow_natCast _ k, Nat.cast_mul, Nat.cast_ofNat] at h
  -- the triangle inequality in `ℓ_k`
  have h2 : T ^ (1 / k : ℝ) ≤ ∑ i, schattenNorm (ENNReal.ofReal (2 * k)) (x i) ^ 2 := by
    refine (rpow_sum_rpow_sum_le _ _ hk1 fun i j => sq_nonneg _).trans_eq ?_
    exact Finset.sum_congr rfl fun i _ => rpow_sum_sortedSingularValue hk (x i)
  calc SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i)
      ≤ (evenKhintchineConst k ^ (2 * k : ℝ) * T) ^ (1 / (2 * k) : ℝ) :=
        Real.rpow_le_rpow (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) h1
          (by positivity)
    _ = evenKhintchineConst k * √(T ^ (1 / k : ℝ)) := by
        rw [Real.mul_rpow (Real.rpow_nonneg (evenKhintchineConst_nonneg k) _) hT0,
          ← Real.rpow_mul (evenKhintchineConst_nonneg k), mul_one_div_cancel (by positivity),
          Real.rpow_one, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
        congr 2
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (evenKhintchineConst_nonneg k)

/-- **Type 2 of `S_{2k}`** (Tomczak-Jaegermann (1974), (3.15), p. 178), complex matrices. The source
argues directly with operators on a Hilbert space; here the complex case is deduced from the real
one by realification: every singular value of `A` occurs twice in `realify A`, and the factors
`2^{−1/2k}` on the two sides cancel. -/
theorem lpNorm_complexSchattenNorm_le_of_even {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k * √(∑ i, complexSchattenNorm (ENNReal.ofReal (2 * k)) (x i) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : ENNReal.ofReal (2 * k) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  set c : ℝ := (2 : ℝ) ^ (-(1 / (ENNReal.ofReal (2 * k)).toReal)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hnorm : ∀ A : Matrix n n ℂ, complexSchattenNorm (ENNReal.ofReal (2 * k)) A =
      c * schattenNorm (ENNReal.ofReal (2 * k)) (realify A) := complexSchattenNorm_eq_realify hq
  have hlin : ∀ ε : Fin N → Bool,
      realify (∑ i, coin (ε i) • x i) = ∑ i, coin (ε i) • realify (x i) := fun ε => by
    have h := map_sum (AddMonoidHom.mk' (realify : Matrix n n ℂ → _) realify_add)
      (fun i => coin (ε i) • x i) Finset.univ
    simpa only [AddMonoidHom.mk'_apply, realify_smul] using h
  have h := lpNorm_schattenNorm_le_of_even hk fun i => realify (x i)
  have hL : SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
      (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) =
        c * SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
          (fun ε : Fin N → Bool => ∑ i, coin (ε i) • realify (x i)) := by
    simp only [SignCube.lpNorm, hnorm, hlin, Real.mul_rpow hc0 (schattenNorm_nonneg _ _),
      avg_const_mul]
    rw [Real.mul_rpow (by positivity) (avg_nonneg fun ε =>
      Real.rpow_nonneg (schattenNorm_nonneg _ _) _), ← Real.rpow_mul hc0,
      mul_one_div_cancel (by positivity), Real.rpow_one]
  rw [hL]
  simp only [hnorm, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h hc0

end BanachProbability
