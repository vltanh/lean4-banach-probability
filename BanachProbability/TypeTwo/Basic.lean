module

public import BanachProbability.SignCube.LpSeminorm

/-!
# Type 2

A normed space `X` has type 2 with constant `τ` when
`(E ‖Σ ε_k x_k‖²)^{1/2} ≤ τ (Σ ‖x_k‖²)^{1/2}` for all `x_1, …, x_N ∈ X`, with independent real signs
`ε_k` (`IsTypeTwoBound X τ`, in `BanachProbability.Defs`; Hytönen–van Neerven–Veraar–Weis (HNVW),
*Analysis in Banach spaces II* (2017), Definition 7.1.1, p. 54). The book takes complex signs for
complex spaces; with real signs, as here, the constant of a complex space is that of the underlying
real space, `τ^ℝ_{2,X}` on p. 56.

A real inner product space has type 2 with constant `1` (`isTypeTwoBound_of_innerProductSpace`; HNVW
II, Example 7.1.2, p. 55).
-/

@[expose] public section

namespace BanachProbability

open SignCube

/-- A real inner product space has type 2 with constant `1` (HNVW II, Example 7.1.2, p. 55), by the
orthonormality of the signs: `E ‖Σ ε_k x_k‖² = Σ ‖x_k‖²`. -/
theorem isTypeTwoBound_of_innerProductSpace (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] : IsTypeTwoBound H 1 := by
  intro N x
  have h : (avg fun ε : Fin N → Bool => ‖∑ k, coin (ε k) • x k‖ ^ 2) = ∑ k, ‖x k‖ ^ 2 := by
    have e : ∀ ε : Fin N → Bool, ‖∑ k, coin (ε k) • x k‖ ^ 2 =
        ∑ i, ∑ j, inner ℝ (x i) (x j) * (coin (ε i) * coin (ε j)) := fun ε => by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    simp only [e, avg_sum, avg_const_mul, avg_coin_mul_coin, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, real_inner_self_eq_norm_sq]
  rw [one_mul, SignCube.lpNorm, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, h, le_refl]

end BanachProbability
