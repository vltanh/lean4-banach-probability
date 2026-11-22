module

public import BanachProbability.KahaneKhintchine.Basic
public import BanachProbability.RandomSums.Contraction
public import BanachProbability.SignCube.Bridge

/-!
# Solution: hypercontractivity on the cube and the Kahane–Khintchine inequality

The statements of `palomar/KahaneKhintchine/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace KahaneKhintchineChallenge

open BanachProbability BanachProbability.SignCube

theorem lpNorm_eq_eLpNorm {X : Type*} [NormedAddCommGroup X] {n : ℕ} (f : (Fin n → Bool) → X)
    {p : ℝ} (hp : 0 < p) : eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) :=
  eLpNorm_uniformOn f hp

section Seminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem heatSemigroup_walsh (t : ℝ) {n : ℕ} (α : Finset (Fin n)) (x : E) :
    heatSemigroup t (fun ε : Fin n → Bool => (∏ i ∈ α, coin (ε i)) • x) =
      fun ε => Real.exp (-t * α.card) • (∏ i ∈ α, coin (ε i)) • x :=
  BanachProbability.heatSemigroup_walsh t α x

theorem heatSemigroup_hypercontractive (S : Seminorm ℝ E) {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (ht : Real.exp (-t) ≤ √((p - 1) / (q - 1))) {n : ℕ} (f : (Fin n → Bool) → E) :
    SignCube.lpNorm S q (heatSemigroup t f) ≤ SignCube.lpNorm S p f :=
  heatSemigroup_lpNorm_le S hp hpq ht f

theorem bonami (S : Seminorm ℝ E) {p q θ : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ √((p - 1) / (q - 1))) (x y : E) :
    ((S (x + θ • y) ^ q + S (x - θ • y) ^ q) / 2) ^ (1 / q) ≤
      ((S (x + y) ^ p + S (x - y) ^ p) / 2) ^ (1 / p) := by
  have h := bonami_seminorm S hp hpq hθ0 hθ (fun b => if b then x + y else x - y)
  have e1 : kBar θ (fun b : Bool => if b then x + y else x - y) true = x + θ • y := by
    simp only [kBar, coin_true, ite_true, Bool.false_eq_true, ite_false]
    module
  have e2 : kBar θ (fun b : Bool => if b then x + y else x - y) false = x - θ • y := by
    simp only [kBar, coin_false, ite_true, Bool.false_eq_true, ite_false]
    module
  rw [e1, e2] at h
  exact h

theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) :=
  BanachProbability.hypercontractive_affine S hp hpq c x

theorem kahaneKhintchine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {n : ℕ}
    (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  kahaneKhintchine_hypercontractive S hp hpq x

end Seminorm

theorem exists_kahaneKhintchine {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Seminorm ℝ E) {n : ℕ}
      (x : Fin n → E),
      SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
        κ * SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  BanachProbability.exists_kahaneKhintchine hp hq

section Contraction

variable {X : Type*} [NormedAddCommGroup X] {p : ℝ} {N : ℕ}

theorem contraction_real [NormedSpace ℝ X] (hp : 1 ≤ p) {c : Fin N → ℝ} {M : ℝ}
    (hc : ∀ k, |c k| ≤ M) (x : Fin N → X) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      M * SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) :=
  lpNorm_sum_coin_smul_le_max_mul hp hc x

theorem contraction_complex [NormedSpace ℂ X] (hp : 1 ≤ p) {c : Fin N → ℂ} {M : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ M) (x : Fin N → X) :
    SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • c k • x k) ≤
      Real.pi / 2 * M *
        SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin N → Bool => ∑ k, coin (ε k) • x k) :=
  lpNorm_sum_coin_smul_le_pi_div_two_mul_max_mul hp hc x

end Contraction

end KahaneKhintchineChallenge
