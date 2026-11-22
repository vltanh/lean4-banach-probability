module

public import BanachProbability.Schatten.Complex
public import BanachProbability.SignCube.LpSeminorm

/-!
# Block rows and block columns: row and column square functions

For matrices `a_1, …, a_K`, `blockRow a = (a_1 … a_K)` and `blockCol a = (a_1; …; a_K)`. Their
Schatten norms are the row and column square functions:
`‖blockCol a‖_{S_q} = ‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q}` and
`‖blockRow a‖_{S_q} = ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q}`, that is,
`‖blockCol a‖_{S_q}² = ‖Σ a_kᴴ a_k‖_{S_{q/2}}` (Lust-Piquard–Pisier, *Non commutative Khintchine and
Paley inequalities*, Ark. Mat. 29 (1991), (I.2), p. 245; their norms of `C_E (ℓ²_R)` and
`C_E (ℓ²_L)`). Hölder's inequality for a block row times a block column is their (I.3), p. 246; and
for `q ≥ 2` the square functions are dominated by the Rademacher sums, (I.5)–(I.7), pp. 246–247:
`‖blockCol a‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {𝕜 : Type*} {K : ℕ} {l m n : Type*}

/-- The block column `(a_1; …; a_K)`. -/
def blockCol (a : Fin K → Matrix m n 𝕜) : Matrix (Fin K × m) n 𝕜 :=
  Matrix.of fun p j => a p.1 p.2 j

/-- The block row `(a_1 … a_K)`. -/
def blockRow (a : Fin K → Matrix m n 𝕜) : Matrix m (Fin K × n) 𝕜 :=
  Matrix.of fun i p => a p.1 i p.2

section Algebra

variable [CommRing 𝕜] [StarRing 𝕜]

theorem conjTranspose_blockRow (a : Fin K → Matrix m n 𝕜) :
    (blockRow a)ᴴ = blockCol fun k => (a k)ᴴ := by
  sorry

theorem blockRow_mul_blockCol [Fintype m] (a : Fin K → Matrix l m 𝕜) (b : Fin K → Matrix m n 𝕜) :
    blockRow a * blockCol b = ∑ k, a k * b k := by
  sorry

theorem conjTranspose_blockCol_mul_blockCol [Fintype m] (a b : Fin K → Matrix m n 𝕜) :
    (blockCol a)ᴴ * blockCol b = ∑ k, (a k)ᴴ * b k := by
  sorry

theorem blockRow_mul_conjTranspose_blockRow [Fintype n] (a b : Fin K → Matrix m n 𝕜) :
    blockRow a * (blockRow b)ᴴ = ∑ k, a k * (b k)ᴴ := by
  sorry

theorem mul_blockRow [Fintype m] (x : Matrix l m 𝕜) (a : Fin K → Matrix m n 𝕜) :
    x * blockRow a = blockRow fun k => x * a k := by
  sorry

theorem blockCol_mul [Fintype n] (a : Fin K → Matrix m n 𝕜) {o : Type*} (x : Matrix n o 𝕜) :
    blockCol a * x = blockCol fun k => a k * x := by
  sorry

end Algebra

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `‖blockCol a‖_{S_q}² = ‖Σ a_kᴴ a_k‖_{S_{q/2}}`. -/
theorem complexSchattenNorm_blockCol_sq {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockCol a) ^ 2 = complexSchattenNorm (q / 2) (∑ k, (a k)ᴴ * a k) := by
  sorry

/-- `‖blockRow a‖_{S_q}² = ‖Σ a_k a_kᴴ‖_{S_{q/2}}`. -/
theorem complexSchattenNorm_blockRow_sq {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockRow a) ^ 2 = complexSchattenNorm (q / 2) (∑ k, a k * (a k)ᴴ) := by
  sorry

theorem complexSchattenNorm_blockRow_conjTranspose (q : ℝ≥0∞) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm q (blockRow fun k => (a k)ᴴ) = complexSchattenNorm q (blockCol a) := by
  sorry

/-- The row square function does not change when the `a_k` are multiplied by unimodular scalars. -/
theorem complexSchattenNorm_blockRow_smul {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ)
    {c : Fin K → ℂ} (hc : ∀ k, ‖c k‖ = 1) :
    complexSchattenNorm q (blockRow fun k => c k • a k) = complexSchattenNorm q (blockRow a) := by
  sorry

/-- The column square function does not change when the `a_k` are multiplied by unimodular scalars.
-/
theorem complexSchattenNorm_blockCol_smul {q : ℝ≥0∞} (hq : q ≠ 0) (a : Fin K → Matrix m n ℂ)
    {c : Fin K → ℂ} (hc : ∀ k, ‖c k‖ = 1) :
    complexSchattenNorm q (blockCol fun k => c k • a k) = complexSchattenNorm q (blockCol a) := by
  sorry

/-- Lust-Piquard–Pisier (1991), (I.3), for the trace:
`|Σ tr (a_k b_k)| ≤ ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q} ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_{q'}}`. -/
theorem norm_sum_trace_mul_le {q q' : ℝ} (hq : q.HolderConjugate q') (a : Fin K → Matrix n m ℂ)
    (b : Fin K → Matrix m n ℂ) :
    ‖∑ k, (a k * b k).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) (blockRow a) *
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b) := by
  sorry

/-- Lust-Piquard–Pisier (1991), (I.7) with signs, column form: for `q ≥ 2`,
`‖(Σ a_kᴴ a_k)^{1/2}‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`. -/
theorem complexSchattenNorm_blockCol_sq_le_avg {q : ℝ} (hq : 2 ≤ q) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockCol a) ^ 2 ≤
      avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • a k) ^ 2 := by
  sorry

/-- Lust-Piquard–Pisier (1991), (I.7) with signs, row form: for `q ≥ 2`,
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_q}² ≤ E ‖Σ ε_k a_k‖_{S_q}²`. -/
theorem complexSchattenNorm_blockRow_sq_le_avg {q : ℝ} (hq : 2 ≤ q) (a : Fin K → Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockRow a) ^ 2 ≤
      avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • a k) ^ 2 := by
  sorry

end BanachProbability
