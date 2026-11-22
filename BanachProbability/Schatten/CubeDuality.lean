module

public import BanachProbability.Schatten.Horn
public import BanachProbability.SignCube.LpSeminorm

/-!
# Duality of `L^q (Ω; S_q)` and `L^{q'} (Ω; S_{q'})` on the sign cube

For functions `X`, `Y` on the sign cube `Ω = {±1}^N` with values in real `n × n` matrices:
Hölder's inequality `|E tr (X Y)| ≤ ‖X‖_{L^q (S_q)} ‖Y‖_{L^{q'} (S_{q'})}`
(`abs_avg_trace_mul_le`), with equality for some `Y` of norm at most `1` when `X` is symmetric
(`exists_avg_trace_mul_eq_lpNorm`; HNVW I, Theorem D.2.6, p. 572).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Hölder's inequality in `L^q (Ω; S_q)`. -/
theorem abs_avg_trace_mul_le {q q' : ℝ} (hq : q.HolderConjugate q')
    (X Y : (Fin N → Bool) → Matrix n n ℝ) :
    |avg fun ε => (X ε * Y ε).trace| ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X *
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y := by
  sorry

/-- The norm of `L^q (Ω; S_q)` is attained: for symmetric `X` there is a symmetric `Y` with
`‖Y‖_{L^{q'} (S_{q'})} ≤ 1` and `E tr (X Y) = ‖X‖_{L^q (S_q)}`. -/
theorem exists_avg_trace_mul_eq_lpNorm {q q' : ℝ} (hq : q.HolderConjugate q')
    (X : (Fin N → Bool) → Matrix n n ℝ) (hX : ∀ ε, (X ε).IsHermitian) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (Y ε).IsHermitian) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y ≤ 1 ∧
      (avg fun ε => (X ε * Y ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X := by
  sorry

end BanachProbability
