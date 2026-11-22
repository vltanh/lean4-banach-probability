module

public import BanachProbability.TypeTwo.Basic
public import BanachProbability.Schatten.Complex

/-!
# Type 2 of the Schatten classes with even exponents

For matrices `A_1, …, A_N` and `k ≥ 1`, with `M_{2k} = ((2k)! / (2^k k!))^{1/2k}` (the best constant
in the scalar Khintchine inequality for the exponent `2k`),

`(E ‖Σ ε_i A_i‖_{S_{2k}}^{2k})^{1/2k} ≤ M_{2k} (Σ ‖A_i‖_{S_{2k}}²)^{1/2}`

(`lpNorm_schattenNorm_le_of_even`, `lpNorm_complexSchattenNorm_le_of_even`).

Source: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, Theorem 3.1 (ii), pp.
176–178, (3.14)–(3.15): the trace is expanded; by the general Horn inequality (Lemma 1.1) each trace
is at most `Σ_j Π s_j (C_ν)`, so that the whole is at most `Σ_j E (Σ ε_i s_j (A_i))^{2k}`; the
multinomial coefficients are compared (`(2k)! / Π (2β_i)! ≤ M_{2k}^{2k} k! / Π β_i!`), and the
triangle inequality in `ℓ_k` finishes. Complex matrices are treated by realification.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The constant `M_{2k} = ((2k)! / (2^k k!))^{1/2k}` (Tomczak-Jaegermann (1974), p. 177). -/
noncomputable def evenKhintchineConst (k : ℕ) : ℝ :=
  (((2 * k).factorial : ℝ) / (2 ^ k * k.factorial)) ^ (1 / (2 * k : ℝ))

/-- `M_{2k} ≤ √(2k − 1)`. -/
theorem evenKhintchineConst_le {k : ℕ} (hk : 1 ≤ k) : evenKhintchineConst k ≤ √(2 * k - 1) := by
  sorry

/-- The scalar Khintchine inequality for an even exponent, with the constant `M_{2k}`
(Tomczak-Jaegermann (1974), p. 177): `E (Σ ε_i a_i)^{2k} ≤ M_{2k}^{2k} (Σ a_i²)^k`. -/
theorem avg_sum_coin_mul_pow_le {k : ℕ} (hk : 1 ≤ k) (a : Fin N → ℝ) :
    (avg fun ε : Fin N → Bool => (∑ i, coin (ε i) * a i) ^ (2 * k)) ≤
      evenKhintchineConst k ^ (2 * k) * (∑ i, a i ^ 2) ^ k := by
  sorry

/-- Tomczak-Jaegermann (1974), pp. 176–177, (3.14) and Lemma 1.1:
`E ‖Σ ε_i A_i‖_{S_{2k}}^{2k} ≤ Σ_j E (Σ_i ε_i s_j (A_i))^{2k}`. -/
theorem avg_schattenNorm_rpow_le_sum {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℝ) :
    (avg fun ε : Fin N → Bool =>
        schattenNorm (ENNReal.ofReal (2 * k)) (∑ i, coin (ε i) • x i) ^ (2 * k : ℝ)) ≤
      ∑ j ∈ Finset.range (Fintype.card n),
        avg fun ε : Fin N → Bool => (∑ i, coin (ε i) * sortedSingularValue (x i) j) ^ (2 * k) := by
  sorry

/-- **Type 2 of `S_{2k}`** (Tomczak-Jaegermann (1974), (3.15), p. 178), real matrices:
`(E ‖Σ ε_i A_i‖_{S_{2k}}^{2k})^{1/2k} ≤ M_{2k} (Σ ‖A_i‖_{S_{2k}}²)^{1/2}`. -/
theorem lpNorm_schattenNorm_le_of_even {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k * √(∑ i, schattenNorm (ENNReal.ofReal (2 * k)) (x i) ^ 2) := by
  sorry

/-- **Type 2 of `S_{2k}`** (Tomczak-Jaegermann (1974), (3.15), p. 178), complex matrices. -/
theorem lpNorm_complexSchattenNorm_le_of_even {k : ℕ} (hk : 1 ≤ k) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (2 * k))) (2 * k)
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k * √(∑ i, complexSchattenNorm (ENNReal.ofReal (2 * k)) (x i) ^ 2) := by
  sorry

end BanachProbability
