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
`complexDyadicUMDConst_eq_complexUMDConst`: the multipliers are first rounded to finitely many
points of the unit circle, which moves the transform by little in `L^p`, and the same three steps
then run with multipliers in the unit circle (`exists_finite_model_gen`,
`exists_hasDyadicTransitions_approx_gen`, `exists_paleyWalsh_realization_gen`);
see `mba_isComplexUMDBound_of_isComplexDyadicUMDBound`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Finite models from the dyadic bound**, general multipliers (Pisier, Theorem 8.32): if `β`
bounds the transforms of Paley–Walsh martingales by predictable multipliers with values in
`A ∋ 1`, it bounds the transforms of martingales on finite probability spaces by such
multipliers. For `η > 0`, move the transition probabilities to dyadic rationals
(`exists_hasDyadicTransitions_approx_gen`), realize the result on a sign cube
(`exists_paleyWalsh_realization_gen`) and apply the dyadic bound:
`‖(φ • Y)_n‖_p ≤ ‖(φ • Y')_n‖_{p, μ'} + η ≤ β ‖Y'_n‖_{p, μ'} + η ≤ β (‖Y_n‖_p + η) + η`;
then let `η → 0`. -/
private theorem mba_finite_gen {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X]
    {A : Set 𝕜} (hA : (1 : 𝕜) ∈ A) {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (hβ : ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (s : Fin N → (Fin N → Bool) → 𝕜),
      SignCube.IsPredictable ξ → SignCube.IsPredictable s → (∀ k ε, s k ε ∈ A) →
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
          (SignCube.paleyWalsh (fun k ε => s k ε • ξ k ε) N)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (SignCube.paleyWalsh ξ N))) :
    ∀ (Ω : Type) [Finite Ω] (mΩ : MeasurableSpace Ω) [DiscreteMeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X)
      (φ : ℕ → Ω → 𝕜), Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, φ n ω ∈ A) →
      (∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  intro Ω _ mΩ _ μ _ ℱ Y φ hY hY0 hφA hφm n
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  refine stp_le_mul (fun h0 => stp_eLpNorm_norm_transform_eq_zero hY hp0 h0 φ) fun η hη => ?_
  obtain ⟨μ', _, Y', hdy, hY', hY'0, h1, h2⟩ :=
    exists_hasDyadicTransitions_approx_gen (φ := φ) hY hY0 hp n hη
  obtain ⟨M, ξ, s, hξ, hs, hsA, e1, e2⟩ :=
    exists_paleyWalsh_realization_gen hY' hY'0 hA hφA hφm hdy (p := p) (by linarith)
  have key := hβ M ξ s hξ hs hsA
  rw [e1, e2] at key
  calc _ ≤ _ := h2
    _ ≤ β * eLpNorm (fun ω => ‖Y' n ω‖) (ENNReal.ofReal p) μ' + ENNReal.ofReal η := by gcongr
    _ ≤ _ := by gcongr

/-- A dyadic UMD bound is a UMD bound for finite models (Pisier, Theorem 8.32): for `η > 0`, the
dyadic perturbation (`exists_hasDyadicTransitions_approx`) and the realization on a sign cube
(`exists_paleyWalsh_realization`) give `‖(σ • Y)_n‖_p ≤ β (‖Y_n‖_p + η) + η`; let `η → 0`. This
is the case `𝕜 = ℝ`, `A = {1, −1}` of the same statement for multipliers with values in a set
`A ∋ 1` proved above, which also serves the complex version. -/
theorem isFiniteUMDBound_of_isDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : IsFiniteUMDBound X p β := by
  intro Ω _ mΩ _ μ _ ℱ Y σ hY hY0 hσ hσm n
  exact mba_finite_gen (𝕜 := ℝ) (A := {1, -1}) (by simp) hp
    (fun N ξ s hξ hs hsA => h N ξ s hξ hs (fun k ε => by simpa using hsA k ε) N)
    Ω mΩ μ ℱ Y σ hY hY0 (fun n ω => by simpa using hσ n ω) hσm n

/-- A dyadic UMD bound is a UMD bound. -/
theorem isUMDBound_of_isDyadicUMDBound {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : IsUMDBound X p β :=
  isUMDBound_of_isFiniteUMDBound hp (isFiniteUMDBound_of_isDyadicUMDBound hp h)

theorem umdConst_le_dyadicUMDConst {p : ℝ} (hp : 1 < p) : umdConst X p ≤ dyadicUMDConst X p :=
  umdConst_le_of_isUMDBound
    (isUMDBound_of_isDyadicUMDBound hp.le (isDyadicUMDBound_dyadicUMDConst (by linarith)))

/-- **Maurey's theorem** (Maurey 1975; Pisier 2016, §5.6; HNVW I, Theorem 4.2.5): restricting the
UMD inequality to Paley–Walsh martingales gives the same optimal constant,
`UMD_p^Δ (X) = UMD_p (X)`. -/
theorem dyadicUMDConst_eq_umdConst {p : ℝ} (hp : 1 < p) : dyadicUMDConst X p = umdConst X p :=
  le_antisymm (dyadicUMDConst_le_umdConst hp) (umdConst_le_dyadicUMDConst hp)

section Complex

/-- The cube instance for the dyadic complex constant: `ξ_0 ≡ x` on the one-sign cube, multiplied
by `c ≡ 1`, shows that every dyadic complex `UMD_p` constant of a nonzero space is at least
`1`. -/
theorem mba_one_le_of_isComplexDyadicUMDBound {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [Nontrivial Z] {p : ℝ} (hp : 0 < p) {β : ℝ≥0∞}
    (h : IsComplexDyadicUMDBound Z p β) : 1 ≤ β := by
  obtain ⟨x, hx⟩ := exists_ne (0 : Z)
  have key := h 1 (fun _ _ => x) (fun _ _ => 1) (umdd_isPredictable_const x)
    (umdd_isPredictable_const 1) (fun _ _ => norm_one) 1
  simp only [one_smul] at key
  rw [umdd_lpNorm_of_norm_eq (norm_nonneg x) (umdd_norm_paleyWalsh_const x) hp] at key
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by simpa using hx
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).mp (by simpa using key)

/-- **A dyadic complex UMD bound is a complex UMD bound** (Pisier, Theorem 8.32, for the
complex constants): the dyadic transitions (`exists_hasDyadicTransitions_approx_gen`) and the
realization on a sign cube (`exists_paleyWalsh_realization_gen` with `A` the unit circle) give the
bound for finite models, and `isComplexUMDBound_of_isFiniteComplexUMDBound` passes to all
martingales. -/
theorem mba_isComplexUMDBound_of_isComplexDyadicUMDBound {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsComplexDyadicUMDBound Z p β) : IsComplexUMDBound Z p β :=
  isComplexUMDBound_of_isFiniteComplexUMDBound hp
    (mba_finite_gen (A := {z : ℂ | ‖z‖ = 1}) (by simp) hp
      fun N ξ s hξ hs hsA => h N ξ s hξ hs hsA N)

end Complex

/-- **Maurey's theorem, complex version**: for a complex Banach space, the complex UMD constant
is attained on Paley–Walsh martingales, `UMD_{ℂ,p}^Δ (X) = UMD_{ℂ,p} (X)`. The proof is the real
one, the unimodular multipliers being approximated by finitely-valued ones in the reduction to
finite models. -/
theorem complexDyadicUMDConst_eq_complexUMDConst {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {p : ℝ} (hp : 1 < p) :
    complexDyadicUMDConst Z p = complexUMDConst Z p :=
  le_antisymm (complexDyadicUMDConst_le_complexUMDConst hp) (le_sInf fun _ hβ =>
    complexUMDConst_le_of_isComplexUMDBound
      (mba_isComplexUMDBound_of_isComplexDyadicUMDBound hp.le hβ))

end BanachProbability
