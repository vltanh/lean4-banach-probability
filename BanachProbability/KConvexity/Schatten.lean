module

public import BanachProbability.KConvexity.Basic
public import BanachProbability.TypeTwo.Schatten
public import BanachProbability.Schatten.CubeDuality

/-!
# The Rademacher projection on `L^q (Ω; S_q)`

For `q ≥ 2` the Rademacher projection is bounded on `L^q (Ω; S_q)`, real matrices, with norm at most
`√(π/2) √(q + 1)`, uniformly in the size (`lpNorm_rademacherProj_schattenNorm_le`), and, by duality,
with the same norm on `L^{q'} (Ω; S_{q'})` for symmetric matrices
(`lpNorm_rademacherProj_schattenNorm_conj_le`). The proof is G. Pisier's, *Non-commutative
vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998), p. 106: by
averaging, the norm on `L_q (X)` is at most `K (L_q (X))`, the K-convexity constant of `L_q (X)`;
for `X = S_q` this is `K (S_q)`, because `ℓ_q (S_q)` embeds isometrically in `S_q` (block diagonal
matrices); and `K (S_q)` is at most the type 2 constant (here up to the factor `√(π/2)`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Block diagonal matrices: `‖diag (A_1, …, A_k)‖_{S_q}^q = Σ ‖A_i‖_{S_q}^q`. -/
theorem schattenNorm_blockDiagonal_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ}
    (hq : 0 < q) (A : ι → Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.blockDiagonal A) ^ q =
      ∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ q := by
  sorry

/-- **The Rademacher projection on `L^q (Ω; S_q)`**, `q ≥ 2` (Pisier (1998), p. 106). -/
theorem lpNorm_rademacherProj_schattenNorm_le {q : ℝ} (hq : 2 ≤ q)
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q f := by
  sorry

/-- The Rademacher projection on `L^{q'} (Ω; S_{q'})`, `q ≥ 2`, by duality (Pisier (1998), p. 106).
-/
theorem lpNorm_rademacherProj_schattenNorm_conj_le {q q' : ℝ} (hq : 2 ≤ q)
    (hqq' : q.HolderConjugate q') (f : (Fin N → Bool) → Matrix n n ℝ)
    (hf : ∀ ε, (f ε).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q'
        (fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
  sorry

end BanachProbability
