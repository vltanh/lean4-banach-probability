module

public import BanachProbability.SignCube.PaleyWalsh
public import BanachProbability.Schatten.Spectral

/-!
# Matrix-valued functions on the sign cube

The finite-dimensional von Neumann algebra `ℓ^∞ (Ω_N) ⊗ M_n (ℝ)` of matrix-valued functions on
the sign cube `Ω_N = Fin N → Bool`, with the trace `τ (x) = E tr x (ε)` (`cubeTrace`), the
filtration of subalgebras of functions of the first `k` signs, and the conditional expectations
`E_k = SignCube.condAvg k`, applied entrywise. Every operator statement in it is pointwise matrix
analysis, then averaged. The noncommutative `L^r` norm is
`‖x‖_{L^r (τ)} = (E ‖x (ε)‖_{S_r}^r)^{1/r} = SignCube.lpNorm (schattenNorm r) r x`.

Facts: `E_k` preserves symmetry and positivity, is a bimodule map over the functions of the first
`k` signs and preserves `τ`; martingale differences are orthogonal for `τ (x y)`; a transform by
`±1` predictable scalar signs (`SignCube.transform`) is an isometry of `L² (τ)`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace `τ (x) = E tr x (ε)` on matrix-valued functions on the sign cube. -/
noncomputable def cubeTrace (x : (Fin N → Bool) → Matrix n n ℝ) : ℝ :=
  avg fun ε => (x ε).trace

/-- The martingale difference `d_k x = E_{k+1} x − E_k x`. -/
noncomputable def mdiff (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ) :
    (Fin N → Bool) → Matrix n n ℝ :=
  fun ε => condAvg (k + 1) x ε - condAvg k x ε

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_condAvg {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (k : ℕ) (ε : Fin N → Bool) : (condAvg k x ε).IsHermitian := by
  sorry

omit [Fintype n] [DecidableEq n] in
theorem posSemidef_condAvg {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).PosSemidef)
    (k : ℕ) (ε : Fin N → Bool) : (condAvg k x ε).PosSemidef := by
  sorry

omit [Fintype n] [DecidableEq n] in
/-- `E_k` is order preserving. -/
theorem posSemidef_condAvg_sub {x y : (Fin N → Bool) → Matrix n n ℝ}
    (h : ∀ ε, (y ε - x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (condAvg k y ε - condAvg k x ε).PosSemidef := by
  sorry

omit [DecidableEq n] in
/-- The bimodule property: `E_k (a x b) = a E_k (x) b` for `a`, `b` functions of the first `k`
signs. -/
theorem condAvg_mul_mul {k : ℕ} {a b : (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → a ε = a ε')
    (hb : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → b ε = b ε')
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    condAvg k (fun ε => a ε * x ε * b ε) = fun ε => a ε * condAvg k x ε * b ε := by
  sorry

omit [DecidableEq n] in
theorem cubeTrace_condAvg (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (condAvg k x) = cubeTrace x := by
  sorry

omit [DecidableEq n] in
/-- Martingale differences are orthogonal: `τ (d_j x · d_k y) = 0` for `j ≠ k`. -/
theorem cubeTrace_mdiff_mul_mdiff {j k : ℕ} (hjk : j ≠ k) (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => mdiff j x ε * mdiff k y ε) = 0 := by
  sorry

/-- A transform by predictable `±1` scalar signs is an isometry of `L² (τ)`. -/
theorem lpNorm_two_transform {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (x : (Fin N → Bool) → Matrix n n ℝ) :
    lpNorm (schattenNorm 2) 2 (transform σ x) = lpNorm (schattenNorm 2) 2 x := by
  sorry

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_transform {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (σ : Fin N → (Fin N → Bool) → ℝ) (ε : Fin N → Bool) : (transform σ x ε).IsHermitian := by
  sorry

end BanachProbability
