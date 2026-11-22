module

public import BanachProbability.Noncommutative.Cuculescu
public import BanachProbability.Noncommutative.Distribution

/-!
# Weak type `(1, 1)` of martingale transforms on the matrix cube

Randrianantoanina's theorem (N. Randrianantoanina, *Non-commutative martingale transforms*,
J. Funct. Anal. 194 (2002), Theorem 3.1, with the constant `14√3/3 + 28`), restricted to the
matrix cube `ℓ^∞ (Ω_N) ⊗ M_n (ℝ)` and to scalar predictable signs (which are central, hence
satisfy the commutation hypothesis of the theorem): there is an absolute constant `C` with
`λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C ‖x‖_{L¹ (τ)}` for every symmetric-matrix-valued `x`, every
`λ > 0` and every family of predictable signs `σ` (`weakType_one_one`).

The proof follows the source:

* the Krickeberg decomposition (Randrianantoanina, Theorem 2.3), which is trivial in finite time:
  `x = x⁺ − x⁻` pointwise (`posPart`, `negPart`), each part positive semidefinite, with
  `‖x⁺‖₁ + ‖x⁻‖₁ = ‖x‖₁` (`schattenNorm_one_eq_trace_posPart_add`); the distribution function is
  subadditive (`distribution_add_add_le`);
* Cuculescu's projections `q_k` at level `λ` (`cuculescu`, Proposition 2.4);
* Lemma 3.2, in the form needed for finite `N`: for a projection `q`, `S − q S q` has rank at
  most `2 rank (1 − q)`, so `#{s_i (S) > s} ≤ #{s_i (q S q) > s} + 2 rank (1 − q)`
  (`countAbove_le_countAbove_compress`);
* Lemma 3.3, the supermartingale property of `q_k x_k q_k` (`condAvg_cuculescu_le`) and
  Chebyshev's inequality in `L² (τ)`;
* Lemmas 3.4 and 3.5, the Doob decomposition of the compressed martingale and the `L² (τ)` bounds
  of its two parts; with scalar signs, the cross term is `E σ σ' tr (a b) ≤ E tr (a b)` for
  positive semidefinite `a`, `b`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive part `A⁺ = max (A, 0)` of a symmetric matrix. -/
noncomputable def posPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => max t 0) A

/-- The negative part `A⁻ = max (−A, 0)` of a symmetric matrix. -/
noncomputable def negPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => max (-t) 0) A

theorem posPart_sub_negPart {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    posPart A - negPart A = A := by
  sorry

theorem posSemidef_posPart (A : Matrix n n ℝ) : (posPart A).PosSemidef := by
  sorry

theorem posSemidef_negPart (A : Matrix n n ℝ) : (negPart A).PosSemidef := by
  sorry

/-- `‖A‖_{S_1} = tr A⁺ + tr A⁻` for a symmetric `A`. -/
theorem schattenNorm_one_eq_trace_posPart_add {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    schattenNorm 1 A = (posPart A).trace + (negPart A).trace := by
  sorry

/-- Lemma 3.2 of Randrianantoanina (2002), for finite matrices: compressing `S` by `q` (a
projection in the applications) changes the number of singular values larger than `s` by at most
`2 rank (1 − q)`, since `S − q S q = (1 − q) S + q S (1 − q)`. -/
theorem countAbove_le_countAbove_compress (S q : Matrix n n ℝ) (s : ℝ) :
    countAbove s S ≤ countAbove s (q * S * q) + 2 * (1 - q).rank := by
  sorry

end Matrix

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
positive semidefinite matrix-valued functions on the cube: there is an absolute `C` with
`λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C τ (x)`. -/
theorem weakType_one_one_of_posSemidef : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n] (x : (Fin N → Bool) → Matrix n n ℝ)
      (σ : Fin N → (Fin N → Bool) → ℝ), (∀ ε, (x ε).PosSemidef) → IsPredictable σ →
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ l : ℝ, 0 < l →
        l * distribution l (transform σ x) ≤ C * cubeTrace x := by
  sorry

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1) on the
matrix cube: there is an absolute `C` with `λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C ‖x‖_{L¹ (τ)}` for
symmetric-matrix-valued `x`. -/
theorem weakType_one_one : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n] (x : (Fin N → Bool) → Matrix n n ℝ)
      (σ : Fin N → (Fin N → Bool) → ℝ), (∀ ε, (x ε).IsHermitian) → IsPredictable σ →
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ l : ℝ, 0 < l →
        l * distribution l (transform σ x) ≤ C * avg fun ε => schattenNorm 1 (x ε) := by
  sorry

end BanachProbability
