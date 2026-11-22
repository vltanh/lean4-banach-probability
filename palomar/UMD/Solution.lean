module

public import BanachProbability.Martingale.Osekowski.Sharpness
public import BanachProbability.UMD.Complex
public import BanachProbability.UMD.Extrapolation
public import BanachProbability.UMD.Incremental
public import BanachProbability.UMD.Lp

/-!
# Solution: UMD constants

The statements of `palomar/UMD/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace UMDChallenge

open BanachProbability BanachProbability.SignCube

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem isUMDBound_iff_deterministic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsUMDBound X p β ↔ IsDeterministicUMDBound ℝ X p β :=
  isUMDBound_iff_isDeterministicUMDBound hp.le

theorem isUMDBound_iff_dyadic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsUMDBound X p β ↔ IsDeterministicDyadicUMDBound ℝ X p β :=
  isUMDBound_iff_isDeterministicDyadicUMDBound hp.le

theorem umdConst_extrapolation [CompleteSpace X] {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdConst X p ≤
      ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1)))) * umdConst X q :=
  umdConst_le_mul_umdConst hp hq

theorem umdConst_two_comparison [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    umdConst X 2 ≤ 200 * umdConst X p ∧
      umdConst X p ≤ ENNReal.ofReal (50 * (p + p / (p - 1))) * umdConst X 2 :=
  ⟨umdConst_two_le_mul hp, umdConst_le_fifty_mul_umdConst_two hp⟩

theorem umdConst_Lp {S : Type*} {mS : MeasurableSpace S} (μ : Measure S) [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ∞) :
    umdConst (Lp X p μ) p.toReal ≤ umdConst X p.toReal ∧
      ((∃ A, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞) →
        umdConst (Lp X p μ) p.toReal = umdConst X p.toReal) :=
  ⟨umdConst_Lp_le μ p hp hpt, fun ⟨_, hA, h0, ht⟩ => umdConst_Lp_eq μ p hp hpt hA h0 ht⟩

end Real

theorem umdConst_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Nontrivial H] {p : ℝ} (hp : 1 < p) :
    umdConst H p = ENNReal.ofReal (max p (p / (p - 1)) - 1) ∧
      sInf {β | IsDeterministicDyadicUMDBound ℝ H p β} =
        ENNReal.ofReal (max p (p / (p - 1)) - 1) := by
  refine ⟨Osekowski.umdConst_of_innerProductSpace hp, ?_⟩
  simp only [← isUMDBound_iff_isDeterministicDyadicUMDBound hp.le]
  exact Osekowski.umdConst_of_innerProductSpace hp

theorem deterministic_transform_le {𝕜 : Type} {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] {p : ℝ}
    (hp : 1 < p) {β : ℝ≥0∞} (h : IsDeterministicUMDBound 𝕜 X p β) {Ω : Type}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0) {φ : ℕ → Ω → 𝕜}
    (hφ1 : ∀ n ω, ‖φ n ω‖ ≤ 1) (hφ : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
        (ENNReal.ofReal p) μ ≤ β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ :=
  h.eLpNorm_transform_le hp.le hY hY0 hφ1 hφ n

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem isComplexUMDBound_iff_deterministic {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsComplexUMDBound X p β ↔ IsDeterministicUMDBound ℂ X p β :=
  isComplexUMDBound_iff_isDeterministicUMDBound hp.le

theorem isComplexUMDBound_iff_dyadic {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} :
    IsComplexUMDBound X p β ↔ IsDeterministicDyadicUMDBound ℂ X p β :=
  isComplexUMDBound_iff_isDeterministicDyadicUMDBound hp.le

theorem umdConst_le_complexUMDConst_le {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  BanachProbability.umdConst_le_complexUMDConst_le hp

theorem complexUMDConst_Lp {S : Type*} {mS : MeasurableSpace S} (μ : Measure S) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : 1 < p) (hpt : p ≠ ∞) :
    complexUMDConst (Lp X p μ) p.toReal ≤ complexUMDConst X p.toReal ∧
      ((∃ A, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞) →
        complexUMDConst (Lp X p μ) p.toReal = complexUMDConst X p.toReal) :=
  ⟨complexUMDConst_Lp_le μ p hp hpt,
    fun ⟨_, hA, h0, ht⟩ => complexUMDConst_Lp_eq μ p hp hpt hA h0 ht⟩

end Complex

end UMDChallenge
