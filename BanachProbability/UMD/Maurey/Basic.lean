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

section Helpers

/-- The limiting step `η → 0`: if `a ≤ β (b + η) + η` for every `η > 0`, then `a ≤ β b`, provided
`a = 0` when `b = 0` (needed for `β = ∞`). -/
private theorem mba_le_mul {a b β : ℝ≥0∞} (h0 : b = 0 → a = 0)
    (key : ∀ η : ℝ, 0 < η → a ≤ β * (b + ENNReal.ofReal η) + ENNReal.ofReal η) : a ≤ β * b := by
  by_cases hβt : β = ⊤
  · by_cases hb : b = 0
    · simp [h0 hb]
    · rw [hβt, ENNReal.top_mul hb]
      exact le_top
  lift β to NNReal using hβt
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hη : 0 < (ε : ℝ) / (β + 1) := by positivity
  refine (key _ hη).trans (le_of_eq ?_)
  rw [mul_add, add_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal (p := β), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal]
  congr 1
  field_simp

/-- For a finite `C` and `η > 0`, some `δ > 0` has `δ C ≤ η`. -/
private theorem mba_exists_pos_mul_le {C : ℝ≥0∞} (hC : C ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ * C ≤ ENNReal.ofReal η := by
  lift C to NNReal using hC
  refine ⟨η / (C + 1), by positivity, ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [C.coe_nonneg]

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The zero corner with norms: if `‖Y_n‖_{L^p} = 0`, the transform at time `n` has `L^p`
norm `0`. -/
private theorem mba_eLpNorm_norm_transform_eq_zero {𝕜 : Type*} [SMulZeroClass 𝕜 E]
    {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {p : ℝ≥0∞} (hp : p ≠ 0) {n : ℕ}
    (hn : eLpNorm (fun ω => ‖Y n ω‖) p μ = 0) (φ : ℕ → Ω → 𝕜) :
    eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) p μ = 0 := by
  rw [eLpNorm_eq_zero_iff hp] at hn ⊢
  have hn' : Y n =ᵐ[μ] 0 := by
    filter_upwards [hn] with ω hω
    simpa using hω
  filter_upwards [umdd_transform_ae_eq_zero hY hn' φ] with ω hω
  simp only [Pi.zero_apply] at hω ⊢
  rw [martingaleTransform, hω, norm_zero]

omit [CompleteSpace E] in
/-- A martingale transform by predictable multipliers is strongly measurable. -/
private theorem mba_aestronglyMeasurable_transform {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {φ : ℕ → Ω → 𝕜}
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    AEStronglyMeasurable (martingaleTransform φ Y n) μ :=
  (Finset.stronglyMeasurable_fun_sum _ fun k _ => ((hφm k).mono (ℱ.le k)).smul
    (((hY.stronglyAdapted (k + 1)).mono (ℱ.le _)).sub
      ((hY.stronglyAdapted k).mono (ℱ.le _)))).aestronglyMeasurable

/-- Two transforms whose multipliers are `δ`-close differ by at most `2 n δ ‖Y_n‖_{L^p}`:
`‖Σ_{k<n} (φ − ψ)_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ δ Σ_{k<n} ‖Y_{k+1} − Y_k‖_{L^p}`
(`eLpNorm_sub_le_two_mul`). -/
private theorem mba_eLpNorm_transform_sub_le [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {φ ψ : ℕ → Ω → 𝕜}
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1)))
    (hψm : ∀ k, StronglyMeasurable[ℱ k] (ψ (k + 1))) {δ : ℝ}
    (hδ : ∀ n ω, ‖φ n ω - ψ n ω‖ ≤ δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (n : ℕ) :
    eLpNorm (fun ω => martingaleTransform φ Y n ω - martingaleTransform ψ Y n ω) p μ ≤
      ENNReal.ofReal δ * (2 * n * eLpNorm (Y n) p μ) := by
  have e : (fun ω => martingaleTransform φ Y n ω - martingaleTransform ψ Y n ω) =
      ∑ k ∈ Finset.range n, fun ω => (φ (k + 1) ω - ψ (k + 1) ω) • (Y (k + 1) ω - Y k ω) := by
    funext ω
    simp only [martingaleTransform, Finset.sum_apply, ← Finset.sum_sub_distrib, sub_smul]
  rw [e]
  refine (eLpNorm_sum_le hp).trans ?_
  calc ∑ k ∈ Finset.range n,
        eLpNorm (fun ω => (φ (k + 1) ω - ψ (k + 1) ω) • (Y (k + 1) ω - Y k ω)) p μ
      ≤ ∑ _k ∈ Finset.range n, ENNReal.ofReal δ * (2 * eLpNorm (Y n) p μ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hm : AEStronglyMeasurable
            (fun ω => (φ (k + 1) ω - ψ (k + 1) ω) • (Y (k + 1) ω - Y k ω)) μ :=
          ((((hφm k).sub (hψm k)).mono (ℱ.le k)).smul
            (((hY.stronglyAdapted (k + 1)).mono (ℱ.le _)).sub
              ((hY.stronglyAdapted k).mono (ℱ.le _)))).aestronglyMeasurable
        refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := fun ω => Y (k + 1) ω - Y k ω) (c := δ) hm
          (Filter.Eventually.of_forall fun ω => ?_) p).trans ?_
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (hδ _ ω) (norm_nonneg _)
        · gcongr
          exact eLpNorm_sub_le_two_mul hY hp (Finset.mem_range.mp hk)
    _ = ENNReal.ofReal δ * (2 * n * eLpNorm (Y n) p μ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end Helpers

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
  refine mba_le_mul (fun h0 => mba_eLpNorm_norm_transform_eq_zero hY hp0 h0 φ) fun η hη => ?_
  obtain ⟨μ', _, Y', hdy, hY', hY'0, h1, h2⟩ :=
    exists_hasDyadicTransitions_approx_gen hY hY0 hφm hp n hη
  obtain ⟨M, ξ, s, hξ, hs, hsA, e1, e2⟩ :=
    exists_paleyWalsh_realization_gen hY' hY'0 hA hφA hφm hdy (p := p) (by linarith)
  have key := hβ M ξ s hξ hs hsA
  rw [e1, e2] at key
  calc _ ≤ _ := h2
    _ ≤ β * eLpNorm (fun ω => ‖Y' n ω‖) (ENNReal.ofReal p) μ' + ENNReal.ofReal η := by gcongr
    _ ≤ _ := by gcongr

/-- **From finite models to all martingales**, finitely-valued multipliers with values in `A`
(Pisier, Lemma 8.29): a bound for finite models bounds the transforms on arbitrary probability
spaces, when `‖Y_n‖_{L^p} < ∞`. The finite models (`exists_finite_model_gen`) give
`‖(φ • Y)_n‖_p ≤ β (‖Y_n‖_p + η) + η` for every `η > 0`. -/
private theorem mba_of_finite_gen {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 X]
    [IsScalarTower ℝ 𝕜 X] {A : Set 𝕜} {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (hfin : ∀ (Ω : Type) [Finite Ω] (mΩ : MeasurableSpace Ω) [DiscreteMeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X)
      (φ : ℕ → Ω → 𝕜), Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, φ n ω ∈ A) →
      (∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} (hY : Martingale Y ℱ μ)
    (hY0 : ∀ ω, Y 0 ω = 0) (hφA : ∀ n ω, φ n ω ∈ A)
    (hφfin : ∀ k, (Set.range (φ (k + 1))).Finite)
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ)
    (hYn : eLpNorm (Y n) (ENNReal.ofReal p) μ ≠ ⊤) :
    eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  refine mba_le_mul (fun h0 => mba_eLpNorm_norm_transform_eq_zero hY hp0 h0 φ) fun η hη => ?_
  obtain ⟨Ω', _, m', _, μ', _, ℱ', Y', φ', hY', hY'0, hφ'A, hφ'm, h1, h2⟩ :=
    exists_finite_model_gen hY hY0 hφA hφfin hφm hp n hYn hη
  calc _ ≤ _ := h2
    _ ≤ β * eLpNorm (fun ω => ‖Y' n ω‖) (ENNReal.ofReal p) μ' + ENNReal.ofReal η := by
        gcongr
        exact hfin Ω' m' μ' ℱ' Y' φ' hY' hY'0 hφ'A hφ'm n
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

/-- **Rounding unimodular multipliers**: for `δ > 0` there is a measurable map `r` of `ℂ` to the
unit circle with finitely many values and `‖z − r z‖ ≤ δ` on the unit circle,
`r z = exp (i h ⌊arg z / h⌋)` for a step `h ≤ min (δ / 2) 1`
(`‖e^{iθ} − e^{iθ'}‖ = ‖e^{i (θ − θ')} − 1‖ ≤ 2 |θ − θ'|`). -/
private theorem mba_exists_round {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℂ → ℂ, Measurable r ∧ (Set.range r).Finite ∧ (∀ z, ‖r z‖ = 1) ∧
      ∀ z, ‖z‖ = 1 → ‖z - r z‖ ≤ δ := by
  set h : ℝ := min (δ / 2) 1 with hh
  have h0 : 0 < h := lt_min (by linarith) one_pos
  set g : ℤ → ℂ := fun m => Complex.exp (↑(h * m) * Complex.I) with hg
  refine ⟨fun z => g ⌊Complex.arg z / h⌋, ?_, ?_, fun z => Complex.norm_exp_ofReal_mul_I _, ?_⟩
  · exact (measurable_of_countable g).comp
      (Int.floor_mono.measurable.comp (Complex.measurable_arg.div_const h))
  · refine ((Set.finite_Icc ⌊-Real.pi / h⌋ ⌊Real.pi / h⌋).image g).subset ?_
    rintro _ ⟨z, rfl⟩
    refine ⟨⌊Complex.arg z / h⌋, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (Complex.neg_pi_lt_arg z).le h0.le
    · exact div_le_div_of_nonneg_right (Complex.arg_le_pi z) h0.le
  · intro z hz
    set θ := Complex.arg z
    set θ' : ℝ := h * ⌊θ / h⌋
    have hlo : θ' ≤ θ := by
      have := Int.floor_le (θ / h)
      rw [le_div_iff₀ h0] at this
      simp only [θ']
      linarith
    have hhi : θ < θ' + h := by
      have := Int.lt_floor_add_one (θ / h)
      rw [div_lt_iff₀ h0] at this
      simp only [θ']
      linarith
    have hz' : z = Complex.exp (↑θ * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
      rw [hz, Complex.ofReal_one, one_mul]
    have e : z - g ⌊θ / h⌋ =
        Complex.exp (↑θ' * Complex.I) * (Complex.exp (↑(θ - θ') * Complex.I) - 1) := by
      rw [hz', mul_sub, mul_one, ← Complex.exp_add]
      simp only [hg, θ']
      congr 2
      push_cast
      ring
    have hn : ‖(↑(θ - θ') : ℂ) * Complex.I‖ = θ - θ' := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    change ‖z - g ⌊θ / h⌋‖ ≤ δ
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine (Complex.norm_exp_sub_one_le (by rw [hn]; linarith [min_le_right (δ / 2) 1])).trans ?_
    rw [hn]
    linarith [min_le_left (δ / 2) 1]

/-- **A dyadic complex UMD bound is a complex UMD bound** (Pisier, Theorem 8.32, for the
complex constants). Round the unimodular multipliers `c` to finitely-valued unimodular
predictable ones `c'` with `‖c − c'‖ ≤ δ` (`c' = exp (i h ⌊arg c / h⌋)`), which moves the
transform by at most `2 n δ ‖Y_n‖_p`; for `c'`, the finite models (`exists_finite_model_gen`),
the dyadic transitions (`exists_hasDyadicTransitions_approx_gen`) and the realization on a sign
cube (`exists_paleyWalsh_realization_gen` with `A` the unit circle) give
`‖(c' • Y)_n‖_p ≤ β ‖Y_n‖_p`; then let `δ → 0`. If `‖Y_n‖_p = ∞`, the right side is infinite,
as `β ≥ 1` on a nonzero space (`mba_one_le_of_isComplexDyadicUMDBound`). -/
theorem mba_isComplexUMDBound_of_isComplexDyadicUMDBound {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsComplexDyadicUMDBound Z p β) : IsComplexUMDBound Z p β := by
  intro Ω mΩ μ _ ℱ Y c hY hY0 hc hcm n
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  change eLpNorm (martingaleTransform c Y n) (ENNReal.ofReal p) μ ≤ _
  have hYnm : AEStronglyMeasurable (Y n) μ :=
    ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable
  -- the bound for finitely-valued unimodular predictable multipliers
  have hB : ∀ c' : ℕ → Ω → ℂ, (∀ n ω, ‖c' n ω‖ = 1) → (∀ k, (Set.range (c' (k + 1))).Finite) →
      (∀ k, StronglyMeasurable[ℱ k] (c' (k + 1))) →
      eLpNorm (Y n) (ENNReal.ofReal p) μ ≠ ⊤ →
      eLpNorm (martingaleTransform c' Y n) (ENNReal.ofReal p) μ ≤
        β * eLpNorm (Y n) (ENNReal.ofReal p) μ := by
    intro c' hc'1 hc'fin hc'm hYn
    rw [← eLpNorm_norm _ hYnm, ← eLpNorm_norm _ (mba_aestronglyMeasurable_transform hY hc'm n)]
    exact mba_of_finite_gen (A := {z : ℂ | ‖z‖ = 1}) hp
      (mba_finite_gen (by simp) hp fun N ξ s hξ hs hsA => h N ξ s hξ hs hsA N)
      hY hY0 hc'1 hc'fin hc'm n hYn
  -- the corner `‖Y_n‖_p = ∞`
  by_cases hYn : eLpNorm (Y n) (ENNReal.ofReal p) μ = ⊤
  · by_cases hβ : β = 0
    · rcases subsingleton_or_nontrivial Z with hZ | hZ
      · exact (le_of_eq ((eLpNorm_eq_zero_iff hp0).mpr
          (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _))).trans zero_le
      · exact absurd hβ (zero_lt_one.trans_le
          (mba_one_le_of_isComplexDyadicUMDBound (by linarith) h)).ne'
    · rw [hYn, ENNReal.mul_top hβ]
      exact le_top
  refine mba_le_mul (fun h0 => umdd_eLpNorm_transform_eq_zero hY hp0 h0 c) fun η hη => ?_
  -- round the multipliers within `δ`, with `2 n δ ‖Y_n‖_p ≤ η`
  obtain ⟨δ, hδ, hδη⟩ := mba_exists_pos_mul_le (C := 2 * n * eLpNorm (Y n) (ENNReal.ofReal p) μ)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)) hYn) hη
  obtain ⟨r, hrm, hrfin, hr1, hr⟩ := mba_exists_round hδ
  set c' : ℕ → Ω → ℂ := fun n ω => r (c n ω) with hc'
  have hc'm : ∀ k, StronglyMeasurable[ℱ k] (c' (k + 1)) := fun k =>
    (hrm.comp (hcm k).measurable).stronglyMeasurable
  have hc'fin : ∀ k, (Set.range (c' (k + 1))).Finite := fun k =>
    hrfin.subset (Set.range_subset_iff.2 fun ω => ⟨_, rfl⟩)
  have herr := mba_eLpNorm_transform_sub_le hY hcm hc'm (fun n ω => hr _ (hc n ω)) hp1 n
  have hsplit : martingaleTransform c Y n = martingaleTransform c' Y n +
      fun ω => martingaleTransform c Y n ω - martingaleTransform c' Y n ω := by
    funext ω
    simp
  calc eLpNorm (martingaleTransform c Y n) (ENNReal.ofReal p) μ
      ≤ eLpNorm (martingaleTransform c' Y n) (ENNReal.ofReal p) μ +
          eLpNorm (fun ω => martingaleTransform c Y n ω - martingaleTransform c' Y n ω)
            (ENNReal.ofReal p) μ :=
        (le_of_eq (congrArg (eLpNorm · (ENNReal.ofReal p) μ) hsplit)).trans (eLpNorm_add_le hp1)
    _ ≤ β * eLpNorm (Y n) (ENNReal.ofReal p) μ + ENNReal.ofReal η :=
        add_le_add (hB c' (fun n ω => hr1 _) hc'fin hc'm hYn) (herr.trans hδη)
    _ ≤ β * (eLpNorm (Y n) (ENNReal.ofReal p) μ + ENNReal.ofReal η) + ENNReal.ofReal η := by
        gcongr
        exact le_self_add

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
