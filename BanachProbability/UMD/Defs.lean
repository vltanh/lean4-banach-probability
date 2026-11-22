module

public import BanachProbability.SignCube.Bridge
public import BanachProbability.Martingale.Transform
public import Mathlib.Analysis.Complex.Basic

/-!
# UMD constants

A Banach space `X` has the UMD property (unconditional martingale differences) for an exponent
`p ∈ (1, ∞)` when martingale transforms by predictable signs are bounded in `L^p (X)`:
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}` for every `X`-valued martingale `Y`
started at `0` and every sequence of signs `σ_k ∈ {±1}` with `σ_{k+1}` `ℱ_k`-measurable. This
file defines:

* `IsUMDBound X p β` and `umdConst X p`, the best constant `UMD_p (X) ∈ [0, ∞]`, for martingales
  on arbitrary probability spaces (Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I*
  (2016), Definition 4.2.1; Pisier, *Martingales in Banach spaces* (2016), Chapter 5);
* `IsDyadicUMDBound X p β` and `dyadicUMDConst X p`, the same for Paley–Walsh martingales on the
  sign cube, `UMD_p^Δ (X)`;
* `IsComplexUMDBound X p β`, `complexUMDConst X p` and their dyadic versions, for a complex
  Banach space and predictable unimodular complex multipliers, `UMD_{ℂ,p} (X)`;
* `pStar p = max (p, p / (p − 1))`, Burkholder's exponent.

Basic facts: the constants are attained (`isUMDBound_umdConst`), they do not increase under linear
isometric embeddings (`umdConst_le_of_linearIsometry`), they are at least `1` on a nonzero space
(`one_le_umdConst`), and the dyadic constant is at most the full one
(`dyadicUMDConst_le_umdConst`). The converse, `dyadicUMDConst X p = umdConst X p`, is Maurey's
theorem (`BanachProbability.dyadicUMDConst_eq_umdConst`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

/-- Burkholder's exponent `p* = max (p, p / (p − 1))`. -/
noncomputable def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

section Real

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `β` is a `UMD_p` constant of the Banach space `X`: for every probability space and filtration,
every `X`-valued martingale `Y` with `Y₀ = 0` and every sequence of predictable signs
`σ_k ∈ {±1}` (`σ_{k+1}` is `ℱ_k`-measurable),
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. The probability spaces range over
`Type`. -/
def IsUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (σ : ℕ → Ω → ℝ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, σ n ω = 1 ∨ σ n ω = -1) →
      (∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

/-- `UMD_p (X)`: the best `UMD_p` constant of `X` (`∞` if there is none). -/
noncomputable def umdConst [CompleteSpace X] (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsUMDBound X p β}

/-- `β` bounds the `±1`-transforms of Paley–Walsh martingales with values in `X`:
`‖Σ_{k<n} σ_k ε_k ξ_k‖_{L^p} ≤ β ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` for predictable `ξ_k` and predictable
signs `σ_k`. -/
def IsDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ n : ℕ,
      ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic `UMD_p` constant `UMD_p^Δ (X)`. -/
noncomputable def dyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsDyadicUMDBound X p β}

variable {X}

theorem IsUMDBound.mono [CompleteSpace X] {p : ℝ} {β β' : ℝ≥0∞} (h : IsUMDBound X p β)
    (hβ : β ≤ β') : IsUMDBound X p β' := by
  sorry

theorem umdConst_le_of_isUMDBound [CompleteSpace X] {p : ℝ} {β : ℝ≥0∞}
    (h : IsUMDBound X p β) : umdConst X p ≤ β :=
  sInf_le h

/-- The infimum defining `UMD_p (X)` is attained. -/
theorem isUMDBound_umdConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    IsUMDBound X p (umdConst X p) := by
  sorry

theorem IsDyadicUMDBound.mono {p : ℝ} {β β' : ℝ≥0∞} (h : IsDyadicUMDBound X p β)
    (hβ : β ≤ β') : IsDyadicUMDBound X p β' := by
  sorry

theorem dyadicUMDConst_le_of_isDyadicUMDBound {p : ℝ} {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : dyadicUMDConst X p ≤ β :=
  sInf_le h

/-- The infimum defining `UMD_p^Δ (X)` is attained. -/
theorem isDyadicUMDBound_dyadicUMDConst {p : ℝ} (hp : 0 < p) :
    IsDyadicUMDBound X p (dyadicUMDConst X p) := by
  sorry

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A `UMD_p` constant of `Y` is one of every space linearly isometric to a subspace of `Y`. -/
theorem IsUMDBound.of_linearIsometry [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℝ] Y)
    {p : ℝ} {β : ℝ≥0∞} (h : IsUMDBound Y p β) : IsUMDBound X p β := by
  sorry

theorem umdConst_le_of_linearIsometry [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℝ] Y)
    (p : ℝ) : umdConst X p ≤ umdConst Y p := by
  sorry

theorem umdConst_congr [CompleteSpace X] [CompleteSpace Y] (e : X ≃ₗᵢ[ℝ] Y) (p : ℝ) :
    umdConst X p = umdConst Y p := by
  sorry

theorem IsDyadicUMDBound.of_linearIsometry (f : X →ₗᵢ[ℝ] Y) {p : ℝ} {β : ℝ≥0∞}
    (h : IsDyadicUMDBound Y p β) : IsDyadicUMDBound X p β := by
  sorry

theorem dyadicUMDConst_le_of_linearIsometry (f : X →ₗᵢ[ℝ] Y) (p : ℝ) :
    dyadicUMDConst X p ≤ dyadicUMDConst Y p := by
  sorry

theorem dyadicUMDConst_congr (e : X ≃ₗᵢ[ℝ] Y) (p : ℝ) :
    dyadicUMDConst X p = dyadicUMDConst Y p := by
  sorry

/-- `UMD_p (X) ≥ 1` on a nonzero space (the transform by `σ ≡ 1` is the martingale itself). -/
theorem one_le_umdConst [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 1 < p) :
    1 ≤ umdConst X p := by
  sorry

theorem one_le_dyadicUMDConst [Nontrivial X] {p : ℝ} (hp : 0 < p) : 1 ≤ dyadicUMDConst X p := by
  sorry

/-- The dyadic constant is at most the full one: Paley–Walsh martingales are martingales on the
probability space `Fin N → Bool` (`SignCube.martingale_paleyWalsh`), whose `L^p` norms are the
cube averages (`SignCube.eLpNorm_uniformOn`). -/
theorem dyadicUMDConst_le_umdConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X p ≤ umdConst X p := by
  sorry

end Real

section Complex

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `β` is a complex `UMD_p` constant of the complex Banach space `X`: for every `X`-valued
martingale `Y` with `Y₀ = 0` and every predictable sequence of unimodular `c_k ∈ ℂ`,
`‖Σ_{k<n} c_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. -/
def IsComplexUMDBound [CompleteSpace X] (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (c : ℕ → Ω → ℂ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, ‖c n ω‖ = 1) →
      (∀ k, StronglyMeasurable[ℱ k] (c (k + 1))) →
      ∀ n, eLpNorm (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Y (k + 1) ω - Y k ω))
          (ENNReal.ofReal p) μ ≤ β * eLpNorm (Y n) (ENNReal.ofReal p) μ

/-- `UMD_{ℂ,p} (X)`: the best complex `UMD_p` constant (`∞` if there is none). -/
noncomputable def complexUMDConst [CompleteSpace X] (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexUMDBound X p β}

/-- The dyadic complex `UMD_p` bound: predictable unimodular complex multipliers of Paley–Walsh
martingales. -/
def IsComplexDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (c : Fin N → (Fin N → Bool) → ℂ),
    IsPredictable ξ → IsPredictable c → (∀ k ε, ‖c k ε‖ = 1) → ∀ n : ℕ,
      ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => c k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic complex `UMD_p` constant `UMD_{ℂ,p}^Δ (X)`. -/
noncomputable def complexDyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexDyadicUMDBound X p β}

variable {X}

theorem complexUMDConst_le_of_isComplexUMDBound [CompleteSpace X] {p : ℝ} {β : ℝ≥0∞}
    (h : IsComplexUMDBound X p β) : complexUMDConst X p ≤ β :=
  sInf_le h

theorem isComplexUMDBound_complexUMDConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    IsComplexUMDBound X p (complexUMDConst X p) := by
  sorry

theorem complexDyadicUMDConst_le_complexUMDConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    complexDyadicUMDConst X p ≤ complexUMDConst X p := by
  sorry

end Complex

end BanachProbability
