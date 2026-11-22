module

public import BanachProbability.Martingale.Burkholder.Inequality
public import BanachProbability.Martingale.Osekowski.Sharpness

/-!
# Solution: Burkholder's inequality for martingales in a Hilbert space

The statements of `palomar/Burkholder/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BurkholderChallenge

open BanachProbability BanachProbability.SignCube

section Hilbert

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {p : ℝ}

theorem burkholder_inequality (hp : 1 < p) {f g : ℕ → Ω → H} (hf : Martingale f ℱ μ)
    (hg : Martingale g ℱ μ) (h0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (h : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖) (n : ℕ) :
    eLpNorm (g n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ :=
  Osekowski.eLpNorm_le_of_subordinate hp hf hg h0 h n

theorem squareFunction_inequality (hp : 1 < p) {f : ℕ → Ω → H} (hf : Martingale f ℱ μ) (n : ℕ) :
    eLpNorm (fun ω => √(‖f 0 ω‖ ^ 2 + ∑ k ∈ Finset.range n, ‖f (k + 1) ω - f k ω‖ ^ 2))
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ ∧
      eLpNorm (f n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(‖f 0 ω‖ ^ 2 + ∑ k ∈ Finset.range n, ‖f (k + 1) ω - f k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  Burkholder.squareFunction_with_start hp hf n

end Hilbert

theorem burkholder_sharp {p K : ℝ} (hp : 1 < p) (hK : K < max p (p / (p - 1)) - 1) :
    ∃ (N : ℕ) (φ : Fin N → (Fin N → Bool) → ℝ) (l : Fin N → ℝ), IsPredictable φ ∧
      (∀ k, l k = 1 ∨ l k = -1) ∧
        K * SignCube.lpNorm (fun x => |x|) p (paleyWalsh φ N) <
          SignCube.lpNorm (fun x => |x|) p (paleyWalsh (fun k ε => l k * φ k ε) N) :=
  Osekowski.exists_lt_lpNorm_transform_const hp hK

theorem martingale_paleyWalsh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (N : ℕ) :
    (∃ ℱ : Filtration ℕ (inferInstance : MeasurableSpace (Fin N → Bool)),
      (∀ (k : ℕ) (f : (Fin N → Bool) → E), StronglyMeasurable[ℱ k] f ↔
        ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε') ∧
      ∀ ξ : Fin N → (Fin N → Bool) → E, IsPredictable ξ →
        Martingale (fun n => paleyWalsh ξ n) ℱ (ProbabilityTheory.uniformOn Set.univ)) ∧
    ∀ (f : (Fin N → Bool) → E) (p : ℝ), 0 < p →
      eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
        ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) :=
  ⟨⟨filtration N, fun _ _ => stronglyMeasurable_filtration_iff,
    fun ξ hξ => SignCube.martingale_paleyWalsh ξ hξ⟩,
    fun f _ hp => SignCube.eLpNorm_uniformOn f hp⟩

theorem burkholderFun_majorizes {H : Type*} [NormedAddCommGroup H] {p : ℝ} (hp : 1 < p)
    (x y : H) :
    ‖y‖ ^ p - (max p (p / (p - 1)) - 1) ^ p * ‖x‖ ^ p ≤ Burkholder.burkholderFun p x y :=
  Burkholder.burkholderFun_ge hp x y

theorem burkholderFun_concave {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {p : ℝ}
    (hp : 1 < p) (x y h k : H) (hk : ‖k‖ ≤ ‖h‖) :
    ConcaveOn ℝ Set.univ fun t : ℝ => Burkholder.burkholderFun p (x + t • h) (y + t • k) :=
  Burkholder.burkholderFun_concaveOn_line hp x y h k hk

end BurkholderChallenge
