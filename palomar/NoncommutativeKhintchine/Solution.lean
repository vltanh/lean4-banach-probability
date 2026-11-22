module

public import BanachProbability.NoncommutativeKhintchine.Basic

/-!
# Solution: the noncommutative Khintchine inequality

The statements of `palomar/NoncommutativeKhintchine/Challenge.lean`, word for word, proved from the
library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NoncommutativeKhintchineChallenge

open BanachProbability BanachProbability.SignCube
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem khintchine {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) :=
  ncKhintchine hq x

theorem khintchine_symmetric {q : ℝ} (hq : 3 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q - 1) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) :=
  ncKhintchine_symmetric_upper_of_three_le hq A hA

theorem schattenNorm_transpose_mul_self {m : Type*} [Fintype m] {q : ℝ≥0∞} (hq : q ≠ 0)
    (B : Matrix m n ℝ) : schattenNorm (q / 2) (Bᵀ * B) = schattenNorm q B ^ 2 :=
  BanachProbability.schattenNorm_transpose_mul_self hq B

theorem schattenNorm_two_sq {m : Type*} [Fintype m] (B : Matrix m n ℝ) :
    schattenNorm 2 B ^ 2 = ∑ i, ∑ j, B i j ^ 2 :=
  BanachProbability.schattenNorm_two_sq B

end NoncommutativeKhintchineChallenge
