module

public import BanachProbability.ZigZag.Basic

/-!
# Solution: Burkholder's characterization of UMD by zig-zag concave functions

The statements of `palomar/ZigZag/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ZigZagChallenge

open BanachProbability

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ}

theorem umd_iff_signZigZag (hp : 1 < p) :
    umdConst X p < ∞ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y :=
  umdConst_lt_top_iff_exists_isSignZigZagConcave hp

theorem isLeast_signZigZag [Nontrivial X] (hp : 1 < p) (h : umdConst X p < ∞) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (umdConst X p).toReal :=
  isLeast_umdConst_isSignZigZagConcave hp h

theorem umd_iff_ballZigZag (hp : 1 < p) :
    umdConst X p < ∞ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℝ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y :=
  umdConst_lt_top_iff_exists_isBallZigZagConcave hp

theorem isLeast_ballZigZag (hp : 1 < p) (h : umdConst X p < ∞) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℝ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y} (umdConst X p).toReal :=
  isLeast_umdConst_isBallZigZagConcave hp h

end Real

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {p : ℝ}

theorem complexUMD_iff_signZigZag (hp : 1 < p) :
    complexUMDConst X p < ∞ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y :=
  complexUMDConst_lt_top_iff_exists_isSignZigZagConcave hp

theorem isLeast_complexSignZigZag [Nontrivial X] (hp : 1 < p) (h : complexUMDConst X p < ∞) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (complexUMDConst X p).toReal :=
  isLeast_complexUMDConst_isSignZigZagConcave hp h

theorem complexUMD_iff_ballZigZag (hp : 1 < p) :
    complexUMDConst X p < ∞ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℂ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y :=
  complexUMDConst_lt_top_iff_exists_isBallZigZagConcave hp

theorem isLeast_complexBallZigZag (hp : 1 < p) (h : complexUMDConst X p < ∞) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℂ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y} (complexUMDConst X p).toReal :=
  isLeast_complexUMDConst_isBallZigZagConcave hp h

end Complex

end ZigZagChallenge
