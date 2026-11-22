module

public import BanachProbability.UMD.Maurey.StepApprox
public import BanachProbability.UMD.Maurey.Realization

/-!
# Maurey's theorem: dyadic UMD equals UMD

For a Banach space `X` and `p ∈ (1, ∞)`, the UMD inequality for Paley–Walsh martingales on sign
cubes implies it, with the same constant, for martingales on arbitrary probability spaces:
`UMD_p^Δ (X) = UMD_p (X)` (B. Maurey, *Système de Haar*, Séminaire Maurey–Schwartz 1974–1975;
Pisier, *Martingales in Banach spaces* (2016), §5.6; Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Theorem 4.2.5).

The proof: reduce to finite models (`isUMDBound_of_isFiniteUMDBound`); move the transition
probabilities of a finite model to dyadic rationals (`exists_hasDyadicTransitions_approx`);
realize the result by a Paley–Walsh martingale (`exists_paleyWalsh_realization`); let the
approximation error tend to `0`. The reverse inequality is `dyadicUMDConst_le_umdConst`.
The complex version, with predictable unimodular multipliers, is
`complexDyadicUMDConst_eq_complexUMDConst`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A dyadic UMD bound is a UMD bound for finite models. -/
theorem isFiniteUMDBound_of_isDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : IsFiniteUMDBound X p β := by
  sorry

/-- A dyadic UMD bound is a UMD bound. -/
theorem isUMDBound_of_isDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : IsUMDBound X p β :=
  isUMDBound_of_isFiniteUMDBound hp (isFiniteUMDBound_of_isDyadicUMDBound hp h)

theorem umdConst_le_dyadicUMDConst {p : ℝ} (hp : 1 < p) : umdConst X p ≤ dyadicUMDConst X p := by
  sorry

/-- **Maurey's theorem** (Maurey 1975; Pisier 2016, §5.6; HNVW I, Theorem 4.2.5): restricting the
UMD inequality to Paley–Walsh martingales gives the same optimal constant,
`UMD_p^Δ (X) = UMD_p (X)`. -/
theorem dyadicUMDConst_eq_umdConst {p : ℝ} (hp : 1 < p) : dyadicUMDConst X p = umdConst X p :=
  le_antisymm (dyadicUMDConst_le_umdConst hp) (umdConst_le_dyadicUMDConst hp)

/-- **Maurey's theorem, complex version**: for a complex Banach space, the complex UMD constant
is attained on Paley–Walsh martingales, `UMD_{ℂ,p}^Δ (X) = UMD_{ℂ,p} (X)`. The proof is the real
one, the unimodular multipliers being approximated by finitely-valued ones in the reduction to
finite models. -/
theorem complexDyadicUMDConst_eq_complexUMDConst {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {p : ℝ} (hp : 1 < p) :
    complexDyadicUMDConst Z p = complexUMDConst Z p := by
  sorry

end BanachProbability
