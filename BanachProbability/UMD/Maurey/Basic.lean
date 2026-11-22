module

public import BanachProbability.ZigZag.Basic

/-!
# Dyadic UMD equals UMD

For a Banach space `X` and `p ∈ (1, ∞)`, the UMD inequality for Paley–Walsh martingales on sign
cubes implies it, with the same constant, for martingales on arbitrary probability spaces:
`UMD_p^Δ (X) = UMD_p (X)` (B. Maurey, *Système de Haar*, Séminaire Maurey–Schwartz 1974–1975;
Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016) (HNVW), Theorem 4.2.5,
p. 282).

The proof is the alternative one of HNVW, p. 334, which is due to Burkholder (Notes, p. 355;
*Martingales and Fourier analysis in Banach spaces*, Lecture Notes in Math. 1206 (1986)):
the dyadic UMD property gives a zig-zag concave function `U ≥ ‖y‖^p − β^p ‖x‖^p`, with `β` the
dyadic constant (Theorem 4.5.6, (2)⇒(3), `isZigZagConcave_bellmanFunction`), and `U` bounds the UMD
constant by `β` (Theorem 4.5.6, (3)⇒(1), `isUMDBound_of_isSignZigZagConcave`). The first proof of
the book, p. 284–285, approximates a martingale by Paley–Walsh martingales (Theorem 3.6.1, after
Maurey). The reverse inequality is `dyadicUMDConst_le_umdConst`.

Differences from the source: the constants of this library are for predictable signs and for
probability spaces, and those of HNVW for deterministic signs and σ-finite measure spaces
(Definition 4.2.1, p. 281). The proof starts from the dyadic inequality for deterministic signs
(`IsSignDyadicUMDBound`) and ends with the inequality for predictable signs, so that it also shows
that the two kinds of signs give the same constants (`isSignDyadicUMDBound_iff_isDyadicUMDBound`;
compare HNVW, Theorem 4.2.25, p. 300).

The complex version, with predictable unimodular multipliers, is
`complexDyadicUMDConst_eq_complexUMDConst`; its proof is the same.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The dyadic UMD inequality for deterministic signs implies the UMD inequality for predictable
signs on all probability spaces, with the same constant: HNVW I, Theorem 4.2.5, by the alternative
proof of p. 334 (Theorem 4.5.6, (2)⇒(3)⇒(1); Burkholder (1986)). -/
theorem isUMDBound_of_isSignDyadicUMDBound {p β : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (h : IsSignDyadicUMDBound ℝ X p β) : IsUMDBound X p (ENNReal.ofReal β) := by
  have hU := h.isZigZagConcave_bellmanFunction hp hβ
  exact isUMDBound_of_isSignZigZagConcave hp hβ hU.isSignZigZagConcave hU.2.2

/-- A dyadic UMD bound is a UMD bound (HNVW I, Theorem 4.2.5, by the alternative proof of
p. 334). -/
theorem isUMDBound_of_isDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : IsUMDBound X p β := by
  by_cases hβ : β = ⊤
  · -- `β = ∞`: the transform vanishes if `Y_n = 0`
    intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
    have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
    by_cases h0 : eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ = 0
    · exact (stp_eLpNorm_norm_transform_eq_zero hY hp0 h0 σ).le.trans zero_le
    · rw [hβ, ENNReal.top_mul h0]
      exact le_top
  · rw [← ENNReal.ofReal_toReal hβ] at h ⊢
    exact isUMDBound_of_isSignDyadicUMDBound hp ENNReal.toReal_nonneg
      (h.isSignDyadicUMDBound ENNReal.toReal_nonneg)

/-- Deterministic and predictable signs give the same dyadic UMD constants (compare HNVW I,
Theorem 4.2.25, p. 300). -/
theorem isSignDyadicUMDBound_iff_isDyadicUMDBound {p β : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β) :
    IsSignDyadicUMDBound ℝ X p β ↔ IsDyadicUMDBound X p (ENNReal.ofReal β) :=
  ⟨fun h => umdd_isDyadicUMDBound_of_isUMDBound (by linarith)
    (isUMDBound_of_isSignDyadicUMDBound hp hβ h), fun h => h.isSignDyadicUMDBound hβ⟩

/-- `UMD_p (X) ≤ UMD_p^Δ (X)`: HNVW I, Theorem 4.2.5, by the alternative proof of p. 334
(Theorem 4.5.6 with `β = UMD_p^Δ (X)`; Burkholder (1986)). -/
theorem umdConst_le_dyadicUMDConst {p : ℝ} (hp : 1 < p) : umdConst X p ≤ dyadicUMDConst X p :=
  umdConst_le_of_isUMDBound
    (isUMDBound_of_isDyadicUMDBound hp.le (isDyadicUMDBound_dyadicUMDConst (by linarith)))

/-- **Dyadic UMD equals UMD** (HNVW I, Theorem 4.2.5, p. 282, by the alternative proof of p. 334:
Theorem 4.5.6, Burkholder (1986); the first proof, p. 284–285, approximates by Paley–Walsh
martingales, Theorem 3.6.1, Maurey): restricting the UMD inequality to Paley–Walsh martingales gives
the same optimal constant, `UMD_p^Δ (X) = UMD_p (X)`. Differences from the source: predictable
instead of deterministic signs, and probability spaces instead of σ-finite measure spaces. -/
theorem dyadicUMDConst_eq_umdConst {p : ℝ} (hp : 1 < p) : dyadicUMDConst X p = umdConst X p :=
  le_antisymm (dyadicUMDConst_le_umdConst hp) (umdConst_le_dyadicUMDConst hp)

end Real

section Complex

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The dyadic UMD inequality for deterministic unimodular multipliers implies the complex UMD
inequality for predictable ones on all probability spaces, with the same constant (HNVW I,
Theorem 4.2.5, complex scalars, by the alternative proof of p. 334). -/
theorem isComplexUMDBound_of_isSignDyadicUMDBound {p β : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (h : IsSignDyadicUMDBound ℂ Z p β) : IsComplexUMDBound Z p (ENNReal.ofReal β) := by
  have hU := h.isComplexZigZagConcave_complexBellmanFunction hp hβ
  exact isComplexUMDBound_of_isSignZigZagConcave hp hβ hU.isSignZigZagConcave hU.2.2

/-- A dyadic complex UMD bound is a complex UMD bound (HNVW I, Theorem 4.2.5, complex scalars, by
the alternative proof of p. 334). -/
theorem isComplexUMDBound_of_isComplexDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsComplexDyadicUMDBound Z p β) : IsComplexUMDBound Z p β := by
  by_cases hβ : β = ⊤
  · -- `β = ∞`: the transform vanishes if `Y_n = 0`
    intro Ω mΩ μ _ ℱ Y c hY hY0 hc hcm n
    have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
    by_cases h0 : eLpNorm (Y n) (ENNReal.ofReal p) μ = 0
    · exact (umdd_eLpNorm_transform_eq_zero hY hp0 h0 c).le.trans zero_le
    · rw [hβ, ENNReal.top_mul h0]
      exact le_top
  · rw [← ENNReal.ofReal_toReal hβ] at h ⊢
    exact isComplexUMDBound_of_isSignDyadicUMDBound hp ENNReal.toReal_nonneg
      (h.isSignDyadicUMDBound ENNReal.toReal_nonneg)

/-- Deterministic and predictable unimodular multipliers give the same dyadic complex UMD constants
(compare HNVW I, Theorem 4.2.25, p. 300). -/
theorem isSignDyadicUMDBound_iff_isComplexDyadicUMDBound {p β : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β) :
    IsSignDyadicUMDBound ℂ Z p β ↔ IsComplexDyadicUMDBound Z p (ENNReal.ofReal β) :=
  ⟨fun h => umdd_isComplexDyadicUMDBound_of_isComplexUMDBound (by linarith)
    (isComplexUMDBound_of_isSignDyadicUMDBound hp hβ h), fun h => h.isSignDyadicUMDBound hβ⟩

end Complex

/-- **Dyadic UMD equals UMD, complex version** (HNVW I, Theorem 4.2.5, p. 282, over `ℂ`, by the
alternative proof of p. 334: Theorem 4.5.6, Burkholder (1986)): for a complex Banach space, the
complex UMD constant is attained on Paley–Walsh martingales,
`UMD_{ℂ,p}^Δ (X) = UMD_{ℂ,p} (X)`. The proof is the real one. Differences from the source:
predictable instead of deterministic unimodular multipliers, and probability spaces instead of
σ-finite measure spaces. -/
theorem complexDyadicUMDConst_eq_complexUMDConst {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {p : ℝ} (hp : 1 < p) :
    complexDyadicUMDConst Z p = complexUMDConst Z p :=
  le_antisymm (complexDyadicUMDConst_le_complexUMDConst hp)
    (complexUMDConst_le_of_isComplexUMDBound (isComplexUMDBound_of_isComplexDyadicUMDBound hp.le
      (isComplexDyadicUMDBound_complexDyadicUMDConst (by linarith))))

end BanachProbability
