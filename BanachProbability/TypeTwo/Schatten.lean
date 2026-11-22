module

public import BanachProbability.TypeTwo.Even
public import BanachProbability.Schatten.ThreeLines
public import BanachProbability.Schatten.Space

/-!
# Type 2 of the Schatten classes

For `q ≥ 2` the Schatten class `S_q` has type 2 with a constant of order `√q`, uniformly in the
size, even in the stronger form with the norm of `L^q (Ω; S_q)` on the left:

`(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(q + 1) (Σ ‖A_i‖_{S_q}²)^{1/2}`

(`lpNorm_complexSchattenNorm_le`, `lpNorm_schattenNorm_le`, `isTypeTwoBound_schattenSpace`).

Source: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, Theorem 3.1 (ii), pp.
178–179: for `2k ≤ q ≤ 2k + 2` the even case (`TypeTwo.Even`) at `2k` and `2k + 2` is interpolated
by Proposition 1.2 (`Schatten.ThreeLines`), applied to the analytic families
`φ_i (z) a_{ij} = α_{ij}^{q/p(z)} ‖A_i‖_q^{1 − q/p(z)} a'_{ij}`, where `A_i a_{ij} = α_{ij} a'_{ij}`
is the singular value decomposition and `1/p(z) = (1 − z)/(2k) + z/(2k + 2)`. The constant is
`M_{2k}^{1−θ} M_{2k+2}^θ` (`lpNorm_complexSchattenNorm_le_interp`), at most `√(q + 1)`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **Type 2 of `S_q`**, complex matrices, with the constant of the source (Tomczak-Jaegermann
(1974), Theorem 3.1 (ii), p. 179): for `2k ≤ q ≤ 2k + 2` and `θ = (2k + 2) (q − 2k) / (2q)`,
`(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ M_{2k}^{1−θ} M_{2k+2}^θ (Σ ‖A_i‖_{S_q}²)^{1/2}`. -/
theorem lpNorm_complexSchattenNorm_le_interp {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hkq : 2 * k ≤ q)
    (hqk : q ≤ 2 * k + 2) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k ^ (1 - (2 * k + 2) * (q - 2 * k) / (2 * q)) *
        evenKhintchineConst (k + 1) ^ ((2 * k + 2) * (q - 2 * k) / (2 * q)) *
        √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  sorry

/-- **Type 2 of `S_q`**, `q ≥ 2`, complex matrices, with the constant `√(q + 1)`. -/
theorem lpNorm_complexSchattenNorm_le {q : ℝ} (hq : 2 ≤ q) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q + 1) * √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  sorry

/-- **Type 2 of `S_q`**, `q ≥ 2`, real matrices, with the constant `√(q + 1)`. -/
theorem lpNorm_schattenNorm_le {q : ℝ} (hq : 2 ≤ q) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q + 1) * √(∑ i, schattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  sorry

/-- **Type 2 of the Schatten classes** (Tomczak-Jaegermann (1974), Theorem 3.1 (ii)): for `q ≥ 2`,
`S_q` has type 2 with constant `√(q + 1)`, for square matrices of every size. -/
theorem isTypeTwoBound_schattenSpace {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)] :
    IsTypeTwoBound (SchattenSpace (ENNReal.ofReal q) n n) √(q + 1) := by
  sorry

end BanachProbability
