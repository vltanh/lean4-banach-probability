module

public import BanachProbability.NoncommutativeKhintchine.Symmetric
public import BanachProbability.NoncommutativeKhintchine.Lower
public import BanachProbability.Schatten.Dilation

/-!
# The noncommutative Khintchine inequality

For real `n × n` matrices `x_1, …, x_k`, `q ∈ [2, ∞)` and independent fair signs `ε_i`:

* upper bound (`ncKhintchine_upper`):
  `(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) max (‖Σ_i x_i x_iᵀ‖_{S_{q/2}},
  ‖Σ_i x_iᵀ x_i‖_{S_{q/2}})^{1/2}`, from the symmetric case applied to the Hermitian dilations
  `D (x_i) = [[0, x_i], [x_iᵀ, 0]]` (Mackey–Jordan–Chen–Farrell–Tropp, Ann. Probab. 42 (2014),
  §8): `‖D (S)‖_q^q = 2 ‖S‖_q^q` and `Σ_i D (x_i)² = diag (Σ_i x_i x_iᵀ, Σ_i x_iᵀ x_i)`; with the
  lower bounds of `NoncommutativeKhintchine/Lower.lean`, the two-sided inequality (`ncKhintchine`);
* for normal `x_i` (`x_i x_iᵀ = x_iᵀ x_i`), both bounds together (`ncKhintchine_normal`):
  `‖(Σ_i x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤
  √2 √q ‖(Σ_i x_i x_iᵀ)^{1/2}‖_{S_q}`; this is the noncommutative Khintchine inequality of
  F. Lust-Piquard (1986), F. Lust-Piquard and G. Pisier (1991) and G. Pisier and Q. Xu,
  *Non-commutative `L^p`-spaces* (2003), Theorem 6.1, with the constant `C √q`, `C = √2`
  (`pisierXu_khintchine`).

Here `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} = ‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2}`, which is how the statements are
written.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The dilation step (Mackey et al. 2014, §8): an upper bound with a constant `K` for the symmetric
matrices `D (x_i)` gives one with the same constant for the `x_i`. -/
private theorem ncKhintchine_upper_of_dilation {q K : ℝ} (hq : 2 ≤ q) (hK : 0 ≤ K) {k : ℕ}
    (x : Fin k → Matrix n n ℝ)
    (hsym : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • dilation (x i)) ≤
      K * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, dilation (x i) * dilation (x i)))) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      K * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) := by
  have hq0 : 0 < q := by linarith
  have hq2 : 0 < q / 2 := by linarith
  set B := ∑ i, x i * (x i)ᵀ
  set C := ∑ i, (x i)ᵀ * x i
  set m := max (schattenNorm (ENNReal.ofReal (q / 2)) B)
    (schattenNorm (ENNReal.ofReal (q / 2)) C)
  have hm0 : 0 ≤ m := (schattenNorm_nonneg _ _).trans (le_max_left _ _)
  set M := avg fun ε : Fin k → Bool =>
    schattenNorm (ENNReal.ofReal q) (∑ i, coin (ε i) • x i) ^ q
  have hM0 : 0 ≤ M := avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  -- `Σ_i ε_i D (x_i) = D (Σ_i ε_i x_i)`
  have hD : ∀ ε : Fin k → Bool,
      ∑ i, coin (ε i) • dilation (x i) = dilation (∑ i, coin (ε i) • x i) := fun ε => by
    change _ = dilationLinearMap (∑ i, coin (ε i) • x i)
    rw [map_sum]
    simp only [map_smul]
    rfl
  -- `‖D (Y)‖_q^q = 2 ‖Y‖_q^q`, so the left side is `2^{1/q} (E ‖Y‖_q^q)^{1/q}`
  have hlpD : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
      (fun ε : Fin k → Bool => ∑ i, coin (ε i) • dilation (x i)) =
      (2 : ℝ) ^ (1 / q) * M ^ (1 / q) := by
    unfold SignCube.lpNorm
    simp only [hD, schattenNorm_dilation_rpow hq0]
    rw [avg_const_mul, Real.mul_rpow (by norm_num) hM0]
  -- `Σ_i D (x_i)² = diag (Σ_i x_i x_iᵀ, Σ_i x_iᵀ x_i)`, whose `S_{q/2}` norm is at most
  -- `2^{2/q} max (‖Σ_i x_i x_iᵀ‖_{S_{q/2}}, ‖Σ_i x_iᵀ x_i‖_{S_{q/2}})`
  have hsq : ∑ i, dilation (x i) * dilation (x i) = Matrix.fromBlocks B 0 0 C :=
    sum_dilation_mul_self _ _
  have hinv : q / 2 * (2 / q) = 1 := by field_simp
  have hblock : schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C) ≤
      (2 : ℝ) ^ (2 / q) * m := by
    have hle : schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C) ^ (q / 2) ≤
        2 * m ^ (q / 2) := by
      rw [schattenNorm_fromBlocks_rpow hq2 B C]
      have h1 : schattenNorm (ENNReal.ofReal (q / 2)) B ^ (q / 2) ≤ m ^ (q / 2) :=
        Real.rpow_le_rpow (schattenNorm_nonneg _ _) (le_max_left _ _) hq2.le
      have h2 : schattenNorm (ENNReal.ofReal (q / 2)) C ^ (q / 2) ≤ m ^ (q / 2) :=
        Real.rpow_le_rpow (schattenNorm_nonneg _ _) (le_max_right _ _) hq2.le
      linarith
    calc schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C)
        = (schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C) ^ (q / 2)) ^
            (2 / q) := by
          rw [← Real.rpow_mul (schattenNorm_nonneg _ _), hinv, Real.rpow_one]
      _ ≤ (2 * m ^ (q / 2)) ^ (2 / q) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (schattenNorm_nonneg _ _) _) hle (by positivity)
      _ = (2 : ℝ) ^ (2 / q) * m := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hm0 _), ← Real.rpow_mul hm0, hinv,
            Real.rpow_one]
  have hsqrt : √(schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C)) ≤
      (2 : ℝ) ^ (1 / q) * √m := by
    calc √(schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C))
        ≤ √((2 : ℝ) ^ (2 / q) * m) := Real.sqrt_le_sqrt hblock
      _ = √((2 : ℝ) ^ (2 / q)) * √m := Real.sqrt_mul (by positivity) _
      _ = (2 : ℝ) ^ (1 / q) * √m := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
          congr 2
          ring
  rw [hlpD, hsq] at hsym
  -- the factors `2^{1/q}` cancel
  have h2pos : 0 < (2 : ℝ) ^ (1 / q) := by positivity
  change M ^ (1 / q) ≤ K * √m
  refine le_of_mul_le_mul_left ?_ h2pos
  calc (2 : ℝ) ^ (1 / q) * M ^ (1 / q)
      ≤ K * √(schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C)) := hsym
    _ ≤ K * ((2 : ℝ) ^ (1 / q) * √m) := mul_le_mul_of_nonneg_left hsqrt hK
    _ = (2 : ℝ) ^ (1 / q) * (K * √m) := by ring

/-- **Noncommutative Khintchine inequality, upper bound**, for real square matrices:
`(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) max (‖Σ x_i x_iᵀ‖_{S_{q/2}},
‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`, `q ≥ 2`. -/
theorem ncKhintchine_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) :=
  ncKhintchine_upper_of_dilation hq (Real.sqrt_nonneg _) x (ncKhintchine_symmetric_upper hq
    (fun i => dilation (x i)) fun i => dilation_isHermitian (x i))

/-- **Noncommutative Khintchine inequality, upper bound**, for real square matrices and `q = 2` or
`q ≥ 3`, with the constant `√(q − 1)`:
`(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(q − 1) max (‖Σ x_i x_iᵀ‖_{S_{q/2}},
‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`. -/
theorem ncKhintchine_upper_of_eq_two_or_three_le {q : ℝ} (hq : q = 2 ∨ 3 ≤ q) {k : ℕ}
    (x : Fin k → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q - 1) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) :=
  ncKhintchine_upper_of_dilation (by rcases hq with h | h <;> linarith) (Real.sqrt_nonneg _) x
    (ncKhintchine_symmetric_upper_of_eq_two_or_three_le hq (fun i => dilation (x i)) fun i =>
      dilation_isHermitian (x i))

/-- **The noncommutative Khintchine inequality** for real square matrices, `q ≥ 2`, both bounds
(Pisier–Xu 2003, Theorem 6.1 (i); Lust-Piquard 1986): with
`m = max (‖Σ x_i x_iᵀ‖_{S_{q/2}}, ‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`,
`m ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) m`. -/
theorem ncKhintchine {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) := by
  refine ⟨?_, ncKhintchine_upper hq x⟩
  rcases max_choice (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
    (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i)) with h | h
  · rw [h]
    exact ncKhintchine_lower_row hq x
  · rw [h]
    exact ncKhintchine_lower_col hq x

/-- **Noncommutative Khintchine inequality for normal matrices**, both bounds:
`‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}` and
`(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √2 √q ‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2}`, `q ≥ 2`. -/
theorem ncKhintchine_normal {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ)
    (hx : ∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        √2 * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  refine ⟨ncKhintchine_lower_row hq x, ?_⟩
  -- for normal `x_i` the two square functions coincide
  have hBC : ∑ i, (x i)ᵀ * x i = ∑ i, x i * (x i)ᵀ :=
    Finset.sum_congr rfl fun i _ => (hx i).symm
  have h := ncKhintchine_upper hq x
  rw [hBC, max_self] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  -- `√(2 (q − 1)) ≤ √2 √q`
  rw [← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The noncommutative Khintchine inequality** (Lust-Piquard 1986; Lust-Piquard–Pisier 1991;
Pisier–Xu 2003, Theorem 6.1), for real normal matrices, with an absolute constant: there is
`C > 0` such that for every `q ∈ [2, ∞)`, every dimension and every family of normal `x_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ C √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`.
The proof (`ncKhintchine_normal`) gives `C = √2`. -/
theorem pisierXu_khintchine : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ), 2 ≤ q → ∀ (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
      (x : Fin k → Matrix n n ℝ), (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) :=
  ⟨√2, by positivity, fun _q hq _n _ _ _k x hx => ncKhintchine_normal hq x hx⟩

end BanachProbability
