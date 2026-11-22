module

public import BanachProbability.Noncommutative.WeakType
public import BanachProbability.Noncommutative.Interpolation
public import BanachProbability.Noncommutative.Duality
public import BanachProbability.Schatten.Dilation
public import BanachProbability.Schatten.Space
public import BanachProbability.UMD.Extrapolation

/-!
# Schatten classes are UMD, with constants uniform in the dimension

For real `n × n` matrices and `q ∈ (1, ∞)`:

* `UMD_q (S_q^{n×n}) ≤ K q*` with an absolute `K` (`umdConst_schattenSpace_le`;
  N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002),
  Theorem 4.3 and Corollary 4.5, `C_p (L^p (M)) ≤ C p² / (p − 1)`);
* `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` with an absolute `C` (`umdConst_two_schattenSpace_le`;
  Randrianantoanina (2002), Remark 4.6 (1), with Pisier's extrapolation).

The route, on the matrix cube with scalar predictable signs:

1. weak type `(1, 1)` (`weakType_one_one`) and the `L²` isometry (`lpNorm_two_transform`);
2. three regimes, for uniform constants with real methods only: for `r ∈ (1, 5/3]`, Marcinkiewicz
   between `1` and `2` gives `K / (r − 1)` (`lpNorm_transform_le_of_le_five_thirds`); for
   `r ∈ [5/3, 5/2]`, Marcinkiewicz between `3/2` (first regime) and `3` (from `3/2` by duality)
   gives a bounded constant (`lpNorm_transform_le_of_mem_Icc`); for `r ≥ 5/2`, duality from
   `r' ≤ 5/3` gives `K r` (`lpNorm_transform_le_of_five_halves_le`). A direct weak-`(1,1)`/`L²`
   interpolation would degenerate like `(2 − r)^{−1/2}` near `r = 2`; the middle regime is what
   keeps the constant uniform there. This fills in the step "by interpolation" of the source's
   Theorem 4.3, whose details it does not give;
3. general real matrices through the Hermitian dilation (`dilation`, `‖D (A)‖_q^q = 2 ‖A‖_q^q`),
   which commutes with conditional expectations and transforms;
4. the dyadic constant, then Maurey's theorem (`dyadicUMDConst_eq_umdConst`) for the full one;
5. extrapolation from `q` to `2` (`umdConst_two_le_mul`, `umdConst_le_mul_umdConst_two`), with an
   absolute constant, and `q* − 1 ≥ q* / 2`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

/-- First regime, `r ∈ (1, 5/3]`: `‖T_σ x‖_{L^r (S_r)} ≤ (K / (r − 1)) ‖x‖_{L^r (S_r)}` for
symmetric-matrix-valued `x` (Marcinkiewicz between weak `(1, 1)` and strong `(2, 2)`). -/
theorem lpNorm_transform_le_of_le_five_thirds : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 1 < r → r ≤ 5 / 3 → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K / (r - 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  sorry

/-- Middle regime, `r ∈ [5/3, 5/2]`: a bounded constant (Marcinkiewicz between `3/2` and `3`). -/
theorem lpNorm_transform_le_of_mem_Icc : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 5 / 3 ≤ r → r ≤ 5 / 2 → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  sorry

/-- Third regime, `r ≥ 5/2`: `K r`, by duality from `r' ≤ 5/3`. -/
theorem lpNorm_transform_le_of_five_halves_le : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 5 / 2 ≤ r → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * r * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  sorry

/-- Martingale transforms by predictable signs on `L^r (S_r)` of the matrix cube, for all real
square matrices: `‖T_σ x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}` with an absolute `K`. -/
theorem lpNorm_transform_le : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 1 < r → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * pStar r * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  sorry

/-- `UMD_q^Δ (S_q^{n×n}) ≤ K q*` with an absolute `K`. -/
theorem dyadicUMDConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      dyadicUMDConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  sorry

/-- **Schatten classes are UMD** (Randrianantoanina 2002, Theorem 4.3 and Corollary 4.5):
`UMD_q (S_q^{n×n}) ≤ K q*` with an absolute `K`, for every `q ∈ (1, ∞)` and every `n`. -/
theorem umdConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  sorry

/-- **`UMD₂` of Schatten classes** (Randrianantoanina 2002, Corollary 4.5 and Remark 4.6 (1)): there
is an absolute `C` with `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` for every `q ∈ (1, ∞)` and every `n`. -/
theorem umdConst_two_schattenSpace_le : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) 2 ≤ ENNReal.ofReal (C * (pStar q.toReal - 1)) := by
  sorry

end BanachProbability
