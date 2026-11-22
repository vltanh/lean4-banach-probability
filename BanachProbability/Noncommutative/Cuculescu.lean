module

public import BanachProbability.Noncommutative.MatrixCube

/-!
# Cuculescu's projections on the matrix cube

For a positive semidefinite matrix-valued function `x` on the sign cube, with martingale
`x_k = E_k x`, and `λ > 0`, Cuculescu's projections (I. Cuculescu, *Martingales on von Neumann
algebras*, J. Multivariate Anal. 1 (1971); Randrianantoanina, *Non-commutative martingale
transforms*, J. Funct. Anal. 194 (2002), Proposition 2.4) are defined recursively by
`q_0 = 1` and `q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)` (`cuculescu x λ`); with this indexing
`q_{k+1}` is a function of the signs `ε_j`, `j < k`, the Cuculescu projection at time `k`. They
satisfy:

1. `q_{k+1}` is an orthogonal projection, a function of the first `k` signs, and
   `q_{k+1} ≤ q_k` (`cuculescu_isProj`, `cuculescu_succ_adapted`, `cuculescu_succ_mul`);
2. `q_{k+1}` commutes with `q_k x_k q_k` (`commute_cuculescu_succ`);
3. `q_{k+1} x_k q_{k+1} ≤ λ q_{k+1}` (`cuculescu_mul_mul_le`);
4. `λ τ (1 − q_{N+1}) ≤ τ (x)` (`cuculescu_trace_le`), by a telescoping argument;

and the compressed process `q_{k+1} x_k q_{k+1}` is a supermartingale
(`condAvg_cuculescu_le`; Randrianantoanina, Lemma 3.3), since `q_{k+2}` commutes with
`q_{k+1} x_{k+1} q_{k+1}` and `p A p ≤ A` for a projection `p` commuting with `A ≥ 0`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Cuculescu's projections `q_0 = 1`, `q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)` of the martingale
`x_k = E_k x` at level `λ`. -/
noncomputable def cuculescu (x : (Fin N → Bool) → Matrix n n ℝ) (l : ℝ) :
    ℕ → (Fin N → Bool) → Matrix n n ℝ
  | 0 => fun _ => 1
  | k + 1 => fun ε =>
      cuculescu x l k ε *
        spectralProj (cuculescu x l k ε * condAvg k x ε * cuculescu x l k ε) (Set.Icc 0 l)

variable {x : (Fin N → Bool) → Matrix n n ℝ} {l : ℝ}

theorem cuculescu_isProj (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    cuculescu x l k ε * cuculescu x l k ε = cuculescu x l k ε ∧
      (cuculescu x l k ε)ᵀ = cuculescu x l k ε := by
  sorry

theorem cuculescu_succ_adapted (k : ℕ) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    cuculescu x l (k + 1) ε = cuculescu x l (k + 1) ε' := by
  sorry

/-- The projections decrease: `q_{k+1} q_k = q_{k+1}`. -/
theorem cuculescu_succ_mul (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    cuculescu x l (k + 1) ε * cuculescu x l k ε = cuculescu x l (k + 1) ε := by
  sorry

theorem commute_cuculescu_succ (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    Commute (cuculescu x l (k + 1) ε)
      (cuculescu x l k ε * condAvg k x ε * cuculescu x l k ε) := by
  sorry

/-- `q_{k+1} x_k q_{k+1} ≤ λ q_{k+1}`. -/
theorem cuculescu_mul_mul_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) (k : ℕ)
    (ε : Fin N → Bool) :
    (l • cuculescu x l (k + 1) ε -
      cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε).PosSemidef := by
  sorry

/-- `λ τ (1 − q_{N+1}) ≤ τ (x)`. -/
theorem cuculescu_trace_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) :
    l * cubeTrace (fun ε => 1 - cuculescu x l (N + 1) ε) ≤ cubeTrace x := by
  sorry

/-- The compressed process `q_{k+1} x_k q_{k+1}` is a supermartingale:
`E_k (q_{k+2} x_{k+1} q_{k+2}) ≤ q_{k+1} x_k q_{k+1}`. -/
theorem condAvg_cuculescu_le (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε -
      condAvg k (fun ε => cuculescu x l (k + 2) ε * condAvg (k + 1) x ε *
        cuculescu x l (k + 2) ε) ε).PosSemidef := by
  sorry

end BanachProbability
