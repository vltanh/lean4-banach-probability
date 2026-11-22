module

public import BanachProbability.SignCube.LpSeminorm

/-!
# Type 2

A normed space `X` has type 2 with constant `τ` when
`(E ‖Σ ε_k x_k‖²)^{1/2} ≤ τ (Σ ‖x_k‖²)^{1/2}` for all `x_1, …, x_N ∈ X`, with independent real signs
`ε_k` (`IsTypeTwoBound X τ`; Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces II* (2017),
Definition 7.1.1, p. 54). The book takes complex signs for complex spaces; with real signs, as here,
the constant of a complex space is that of the underlying real space, `τ^ℝ_{2,X}` on p. 56.
-/

@[expose] public section

namespace BanachProbability

open SignCube

/-- `X` has type 2 with constant `τ`, for real signs. -/
def IsTypeTwoBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (τ : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → X),
    SignCube.lpNorm (fun y => ‖y‖) 2 (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) ≤
      τ * √(∑ k, ‖x k‖ ^ 2)

end BanachProbability
