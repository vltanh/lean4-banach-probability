module

public import BanachProbability.TypeTwo.Basic
public import BanachProbability.Schatten.Complex
public import BanachProbability.KahaneKhintchine.Basic

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

/-- Type 2 of `S_{2m}` (HNVW II, Lemma 7.1.12), even in `L^{2m}`:
`(E ‖Σ ε_k x_k‖_{S_{2m}}^{2m})^{1/2m} ≤ √(2m − 1) (Σ ‖x_k‖_{S_{2m}}²)^{1/2}`. -/
theorem lpNorm_schattenNorm_le_of_even {m : ℕ} (hm : 1 ≤ m) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal (2 * m))) (2 * m)
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m - 1) * √(∑ k, schattenNorm (ENNReal.ofReal (2 * m)) (x k) ^ 2) := by
  sorry

/-- The same for complex matrices. -/
theorem lpNorm_complexSchattenNorm_le_of_even {m : ℕ} (hm : 1 ≤ m) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal (2 * m))) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m - 1) * √(∑ k, complexSchattenNorm (ENNReal.ofReal (2 * m)) (x k) ^ 2) := by
  sorry

/-- Interpolation (HNVW II, Propositions 7.1.3 and 7.1.11): for `2m ≤ q ≤ 2m + 2`,
`(E ‖Σ ε_k x_k‖_{S_q}²)^{1/2} ≤ √(2m + 1) (Σ ‖x_k‖_{S_q}²)^{1/2}`, for symmetric `x_k`. -/
theorem lpNorm_two_schattenNorm_le_of_isHermitian {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hmq : 2 * m ≤ q)
    (hqm : q ≤ 2 * m + 2) (x : Fin N → Matrix n n ℝ) (hx : ∀ k, (x k).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) 2
        (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      √(2 * m + 1) * √(∑ k, schattenNorm (ENNReal.ofReal q) (x k) ^ 2) := by
  sorry

/-- **Type 2 of the Schatten classes** (HNVW II, Proposition 7.1.11): for `q ≥ 2`, `S_q` has type 2
with constant `√(q + 1)`, in every size. -/
theorem isTypeTwoBound_schattenSpace {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)] :
    IsTypeTwoBound (SchattenSpace (ENNReal.ofReal q) n n) √(q + 1) := by
  sorry

end BanachProbability
