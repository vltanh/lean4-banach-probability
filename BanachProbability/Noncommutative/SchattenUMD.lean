module

public import BanachProbability.Noncommutative.WeakType
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

(The route: Theorem 4.3 on `L^r (L^∞ (Ω) ⊗ M_n)` for a general filtration, then Corollary 4.5
through `L^r (L^∞ (Ω) ⊗ M_n) = L^r (μ; S_r^n)`; see the declarations below.)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

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

/-- `UMD_q^Δ (S_q^{n×n}) ≤ K q*` with an absolute `K`. -/
theorem dyadicUMDConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      dyadicUMDConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  sorry

end BanachProbability
