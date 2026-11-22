module

public import BanachProbability.Schatten.Basic

/-!
# The triangle inequality for Schatten norms

For `q ∈ [1, ∞]`, `‖A + B‖_{S_q} ≤ ‖A‖_{S_q} + ‖B‖_{S_q}` (von Neumann; R. Bhatia, *Matrix
Analysis* (1997), Chapter IV). The proof is the standard one through doubly substochastic
matrices: write `W = A + B` with its singular vectors, `s_k (W) = ⟨ξ_k, A v_k⟩ + ⟨ξ_k, B v_k⟩`;
for `A = Σ_j s_j x_j ⊗ y_j`, `|⟨ξ_k, A v_k⟩| ≤ Σ_j M_{kj} s_j (A)` with `M` doubly substochastic
(`2|ab| ≤ a²/s + s b²` and Bessel's inequality), so that Jensen's inequality for `t ↦ t^q` gives
`Σ_k |⟨ξ_k, A v_k⟩|^q ≤ Σ_j s_j (A)^q`; Minkowski's inequality in `ℓ^q` concludes.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The triangle inequality for Schatten norms**, `q ≥ 1`. -/
theorem schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  sorry

end BanachProbability
