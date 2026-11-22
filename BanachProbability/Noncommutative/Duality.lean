module

public import BanachProbability.Noncommutative.MatrixCube
public import BanachProbability.Schatten.Holder

/-!
# Duality for martingale transforms on the matrix cube

* Hölder's inequality and its equality case in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}`
  for symmetric-matrix-valued `x`, `y` (`cubeTrace_mul_le`), with equality for a norming function
  built from `normingElement` (`exists_cubeTrace_mul_eq`).
* A transform by predictable scalar signs is self-adjoint for `τ (x y)`:
  `τ (T_σ x · y) = τ (x · T_σ y)` (`cubeTrace_transform_mul`), by the orthogonality of martingale
  differences and the bimodule property (the signs are scalar and predictable).
* Hence a strong `(r, r)` bound for `T_σ` on symmetric-matrix-valued functions gives the strong
  `(r', r')` bound with the same constant (`lpNorm_transform_le_of_dual`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Hölder's inequality in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}`, `r' = r / (r − 1)`. -/
theorem cubeTrace_mul_le {x y : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (hy : ∀ ε, (y ε).IsHermitian) {r : ℝ} (hr : 1 < r) :
    cubeTrace (fun ε => x ε * y ε) ≤
      lpNorm (schattenNorm (ENNReal.ofReal r)) r x *
        lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) y := by
  sorry

/-- The norming function of `x` in `L^r (τ)`: a symmetric-matrix-valued `y` with
`‖y‖_{L^{r'}} ≤ 1` and `τ (x y) = ‖x‖_{L^r}`. -/
theorem exists_cubeTrace_mul_eq {x : (Fin N → Bool) → Matrix n n ℝ}
    (hx : ∀ ε, (x ε).IsHermitian) {r : ℝ} (hr : 1 < r) :
    ∃ y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (y ε).IsHermitian) ∧
      lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) y ≤ 1 ∧
      cubeTrace (fun ε => x ε * y ε) = lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  sorry

omit [DecidableEq n] in
/-- A transform by predictable scalar signs is self-adjoint for the trace pairing. -/
theorem cubeTrace_transform_mul {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => transform σ x ε * y ε) = cubeTrace (fun ε => x ε * transform σ y ε) := by
  sorry

/-- **Duality**: a strong `(r, r)` bound for a transform by predictable signs on
symmetric-matrix-valued functions gives the strong `(r', r')` bound with the same constant. -/
theorem lpNorm_transform_le_of_dual {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    {r K : ℝ} (hr : 1 < r)
    (h : ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) →
      lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
        K * lpNorm (schattenNorm (ENNReal.ofReal r)) r x)
    (x : (Fin N → Bool) → Matrix n n ℝ) (hx : ∀ ε, (x ε).IsHermitian) :
    lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) (transform σ x) ≤
      K * lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) x := by
  sorry

end BanachProbability
