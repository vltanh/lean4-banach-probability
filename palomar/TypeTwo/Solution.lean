module

public import BanachProbability.KConvexity.Schatten

/-!
# Solution: type 2, K-convexity and the Schatten classes

The statements of `palomar/TypeTwo/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TypeTwoChallenge

open BanachProbability BanachProbability.SignCube

theorem typeTwo_hilbert (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    IsTypeTwoBound H 1 :=
  isTypeTwoBound_of_innerProductSpace H

section General

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem gaussianTypeTwo_of_typeTwo {τ : ℝ} (h : IsTypeTwoBound X τ) :
    IsGaussianTypeTwoBound X τ :=
  h.isGaussianTypeTwoBound

theorem typeTwo_of_gaussianTypeTwo {τ : ℝ} (h : IsGaussianTypeTwoBound X τ) (hτ : 0 ≤ τ) :
    IsTypeTwoBound X (√(Real.pi / 2) * τ) :=
  h.isTypeTwoBound hτ

theorem kConvex_of_gaussianTypeTwo {τ : ℝ} (h : IsGaussianTypeTwoBound X τ) (hτ : 0 ≤ τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) :=
  h.isKConvexBound hτ

theorem kConvex_of_typeTwo {τ : ℝ} (h : IsTypeTwoBound X τ) :
    IsKConvexBound X 2 (√(Real.pi / 2) * τ) :=
  h.isKConvexBound

theorem kConvex_of_piLp {p K : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (h : ∀ M : ℕ, IsKConvexBound (PiLp (ENNReal.ofReal p) fun _ : Fin M → Bool => X) 2 K) :
    IsKConvexBound X p K :=
  isKConvexBound_of_piLp h

end General

section Schatten

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem typeTwo_schatten_interp {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hkq : 2 * k ≤ q) (hqk : q ≤ 2 * k + 2)
    (A : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      evenKhintchineConst k ^ (1 - (2 * k + 2) * (q - 2 * k) / (2 * q)) *
        evenKhintchineConst (k + 1) ^ ((2 * k + 2) * (q - 2 * k) / (2 * q)) *
        √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (A i) ^ 2) :=
  lpNorm_complexSchattenNorm_le_interp hk hkq hqk A

theorem typeTwo_schatten {q : ℝ} (hq : 2 ≤ q) :
    (∀ A : Fin N → Matrix n n ℂ, SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q + 1) * √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (A i) ^ 2)) ∧
    ∀ A : Fin N → Matrix n n ℝ, SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q + 1) * √(∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ 2) :=
  ⟨lpNorm_complexSchattenNorm_le hq, lpNorm_schattenNorm_le hq⟩

theorem rademacherProj_schatten {q : ℝ} (hq : 2 ≤ q) (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q f :=
  lpNorm_rademacherProj_schattenNorm_le hq f

theorem rademacherProj_schatten_conj {q q' : ℝ} (hq : 2 ≤ q) (hqq' : q.HolderConjugate q')
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f :=
  lpNorm_rademacherProj_schattenNorm_conj_le hq hqq' f

end Schatten

end TypeTwoChallenge
