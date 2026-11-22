module

public import BanachProbability.SignCube.PaleyWalsh
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Paley–Walsh martingales are martingales

The sign cube `Fin N → Bool` with the uniform probability `ProbabilityTheory.uniformOn Set.univ`
and the natural filtration `ℱ_k = σ (ε₀, …, ε_{k−1})` (`SignCube.filtration`) is a probability
space in Mathlib's sense. On it:

* a Paley–Walsh martingale of a predictable family is a `MeasureTheory.Martingale`
  (`martingale_paleyWalsh`);
* `L^p` norms are averages (`eLpNorm_uniformOn`);
* `ℱ_k`-measurability is dependence on the first `k` signs (`stronglyMeasurable_filtration_iff`);
* every martingale is a Paley–Walsh martingale plus its initial value
  (`exists_paleyWalsh_of_martingale`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability.SignCube

variable {N : ℕ}

theorem trunc_trunc {k k' : ℕ} (h : k ≤ k') (ε : Fin N → Bool) :
    trunc k (trunc k' ε) = trunc k ε := by
  funext j
  simp only [trunc, splice]
  split_ifs <;> first | rfl | omega

/-- The natural filtration of the signs: `ℱ_k = σ (ε₀, …, ε_{k−1})`. -/
noncomputable def filtration (N : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin N → Bool)) where
  seq k := MeasurableSpace.comap (trunc k) inferInstance
  mono' k k' h := by
    change MeasurableSpace.comap (trunc k) _ ≤ MeasurableSpace.comap (trunc k') _
    rw [show (trunc k : (Fin N → Bool) → (Fin N → Bool)) = trunc k ∘ trunc k' from
        funext fun ε => (trunc_trunc h ε).symm, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono fun s _ => MeasurableSet.of_discrete
  le' _ := fun _ _ => MeasurableSet.of_discrete

theorem paleyWalsh_trunc {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin N → (Fin N → Bool) → E) (hξ : IsPredictable ξ) (k : ℕ) (ε : Fin N → Bool) :
    paleyWalsh ξ k (trunc k ε) = paleyWalsh ξ k ε := by
  unfold paleyWalsh
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [hξ j (trunc k ε) ε fun i hi => by
    have : i.val < k := lt_trans (Fin.lt_def.mp hi) hj
    simp [trunc, splice, this]]
  simp [trunc, splice, hj]

theorem uniformOn_singleton (ε : Fin N → Bool) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool))).real {ε} = 1 / 2 ^ N := by
  rw [Measure.real, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
  simp [Fintype.card_bool]

/-- `ℱ_k`-measurability on the sign cube is dependence on the signs `ε_j`, `j < k` only, for
functions with values in a Hausdorff space. -/
theorem stronglyMeasurable_filtration_iff {β : Type*} [TopologicalSpace β] [T2Space β]
    [Nonempty β]
    {k : ℕ} {f : (Fin N → Bool) → β} :
    StronglyMeasurable[filtration N k] f ↔
      ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε' := by
  constructor
  · intro hf ε ε' h
    have htr : trunc k ε = trunc k ε' := by
      funext j
      simp only [trunc, splice]
      split_ifs with hj
      · exact h j hj
      · rfl
    -- each approximating simple function is constant on the fibres of `trunc k`, since its fibres
    -- are `ℱ_k`-measurable, i.e. preimages under `trunc k`
    have key : ∀ n, hf.approx n ε' = hf.approx n ε := by
      intro n
      obtain ⟨t, -, ht⟩ :=
        @SimpleFunc.measurableSet_fiber _ _ (filtration N k) (hf.approx n) (hf.approx n ε)
      have hε : ε ∈ trunc k ⁻¹' t := by
        rw [ht]
        exact rfl
      have hε' : ε' ∈ trunc k ⁻¹' t := by
        rw [Set.mem_preimage, ← htr]
        exact hε
      rw [ht] at hε'
      exact hε'
    -- limits are unique in a Hausdorff space
    exact tendsto_nhds_unique (hf.tendsto_approx ε) ((hf.tendsto_approx ε').congr key)
  · intro h
    have hf : f = f ∘ trunc k :=
      funext fun ε => h ε (trunc k ε) fun j hj => by simp [trunc, splice, hj]
    change StronglyMeasurable[MeasurableSpace.comap (trunc k) inferInstance] f
    rw [hf]
    exact StronglyMeasurable.of_discrete.comp_measurable (comap_measurable _)

/-- A Paley–Walsh martingale `k ↦ Σ_{j<k} ε_j ξ_j` with predictable `ξ` is a martingale for the
natural filtration of the signs and the uniform probability. -/
theorem martingale_paleyWalsh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ξ : Fin N → (Fin N → Bool) → E) (hξ : IsPredictable ξ) :
    Martingale (fun k => paleyWalsh ξ k) (filtration N)
      (ProbabilityTheory.uniformOn Set.univ) := by
  refine martingale_of_setIntegral_eq_succ (fun k => ?_) (fun k => Integrable.of_finite)
    (fun k s hs => ?_)
  · have : (paleyWalsh ξ k) = (paleyWalsh ξ k) ∘ trunc k :=
      funext fun ε => (paleyWalsh_trunc ξ hξ k ε).symm
    change StronglyMeasurable[MeasurableSpace.comap (trunc k) inferInstance] (paleyWalsh ξ k)
    rw [this]
    exact StronglyMeasurable.of_discrete.comp_measurable (comap_measurable _)
  · obtain ⟨t, -, rfl⟩ := hs
    simp_rw [paleyWalsh_succ ξ k]
    rw [integral_add Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn,
      left_eq_add]
    split_ifs with h
    swap
    · simp
    rw [← integral_indicator MeasurableSet.of_discrete, integral_fintype Integrable.of_finite]
    simp_rw [uniformOn_singleton]
    rw [← Finset.smul_sum]
    -- the flip of the `k`-th sign
    set σ : (Fin N → Bool) ≃ (Fin N → Bool) :=
      { toFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        invFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        left_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj]
        right_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj] } with hσ
    set g := (trunc k ⁻¹' t).indicator
      (fun ε => coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε) with hg
    have hflip : ∀ ε, g (σ ε) = -g ε := by
      intro ε
      have htr : trunc k (σ ε) = trunc k ε := by
        funext j
        simp only [trunc, splice, hσ, Equiv.coe_fn_mk]
        split_ifs with hj
        · rw [Function.update_of_ne]
          intro hjk
          rw [hjk] at hj
          exact lt_irrefl _ hj
        · rfl
      have hξσ : ξ ⟨k, h⟩ (σ ε) = ξ ⟨k, h⟩ ε := hξ _ _ _ fun i hi => by
        simp only [hσ, Equiv.coe_fn_mk]
        exact Function.update_of_ne (ne_of_lt hi) _ _
      have hmem : σ ε ∈ trunc k ⁻¹' t ↔ ε ∈ trunc k ⁻¹' t := by
        simp only [Set.mem_preimage, htr]
      by_cases hε : ε ∈ trunc k ⁻¹' t
      · rw [hg, Set.indicator_of_mem (hmem.mpr hε), Set.indicator_of_mem hε, hξσ]
        simp [hσ, coin_not, neg_smul]
      · rw [hg, Set.indicator_of_notMem (fun h' => hε (hmem.mp h')),
          Set.indicator_of_notMem hε, neg_zero]
    have hsum : ∑ ε, g ε = -∑ ε, g ε := by
      conv_lhs => rw [← Equiv.sum_comp σ g]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ε _ => hflip ε
    have h2 : (2 : ℝ) • ∑ ε, g ε = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsum]
      exact add_neg_cancel _
    rw [smul_eq_zero.mp h2 |>.resolve_left two_ne_zero, smul_zero]

/-- On the signs with the uniform probability, `L^p` norms are averages:
`‖f‖_{L^p} = (2^{−N} Σ_ε ‖f (ε)‖^p)^{1/p}`. -/
theorem eLpNorm_uniformOn {E : Type*} [NormedAddCommGroup E] (f : (Fin N → Bool) → E) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp.le, lintegral_fintype]
  have hμ : ∀ ε : Fin N → Bool,
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool))) {ε} =
        ENNReal.ofReal (1 / 2 ^ N) := fun ε => by
    rw [← uniformOn_singleton ε, ofReal_measureReal]
  have hsum : 0 ≤ (∑ ε, ‖f ε‖ ^ p) / 2 ^ N :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  rw [SignCube.lpNorm, avg, ← ENNReal.ofReal_rpow_of_nonneg hsum (by positivity)]
  congr 1
  have hterm : ∀ ε, ‖f ε‖ₑ ^ p * (ProbabilityTheory.uniformOn Set.univ) {ε} =
      ENNReal.ofReal (‖f ε‖ ^ p * (1 / 2 ^ N)) := by
    intro ε
    rw [hμ, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [Finset.sum_congr rfl fun ε _ => hterm ε, ← ENNReal.ofReal_sum_of_nonneg fun ε _ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity), ← Finset.sum_mul]
  congr 1
  ring

/-- Every point of the cube has positive mass, so almost-everywhere equality is equality. -/
private theorem eq_of_ae_eq_uniformOn {β : Type*} {f g : (Fin N → Bool) → β}
    (h : f =ᵐ[ProbabilityTheory.uniformOn Set.univ] g) : f = g := by
  funext ε
  by_contra hne
  have h0 : ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool)) {ε} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.mpr hne) (ae_iff.mp h)
  have h1 := uniformOn_singleton ε
  rw [Measure.real, h0, ENNReal.toReal_zero] at h1
  exact (by positivity : (0 : ℝ) < 1 / 2 ^ N).ne h1

private theorem splice_zero' (ε ε' : Fin N → Bool) : splice 0 ε ε' = ε' := by
  funext j
  simp [splice]

/-- `E [f | ℱ_k]` depends only on the signs `ε_j`, `j < k`. -/
private theorem condAvg_eq_of_agree {E : Type*} [AddCommGroup E] [Module ℝ E] (k : ℕ)
    (f : (Fin N → Bool) → E) (ε ε' : Fin N → Bool) (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    condAvg k f ε = condAvg k f ε' := by
  have : ∀ η, splice k ε η = splice k ε' η := fun η => by
    funext j
    simp only [splice]
    split_ifs with hj
    · exact h j hj
    · rfl
  simp only [condAvg, this]

/-- The cube conditional expectation preserves sums over the cube (the tower property with
`ℱ_0`). -/
private theorem sum_condAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (g : (Fin N → Bool) → E) : ∑ ε, condAvg k g ε = ∑ ε, g ε := by
  have h := congrFun (condAvg_condAvg (Nat.zero_le k) g) (fun _ => false)
  have h0 : ∀ g' : (Fin N → Bool) → E,
      condAvg 0 g' (fun _ => false) = ((2 : ℝ) ^ N)⁻¹ • ∑ ε, g' ε := fun g' => by
    simp only [condAvg, splice_zero']
  rw [h0, h0] at h
  exact smul_right_injective E (inv_ne_zero (pow_ne_zero N two_ne_zero)) h

/-- An `ℱ_k`-measurable indicator commutes with the cube conditional expectation. -/
private theorem indicator_condAvg {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (t : Set (Fin N → Bool)) (f : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    (trunc k ⁻¹' t).indicator (condAvg k f) ε = condAvg k ((trunc k ⁻¹' t).indicator f) ε := by
  have htr : ∀ η, trunc k (splice k ε η) = trunc k ε := fun η => by
    funext j
    simp only [trunc, splice]
    split_ifs <;> rfl
  have hmem : ∀ η, splice k ε η ∈ trunc k ⁻¹' t ↔ ε ∈ trunc k ⁻¹' t := fun η => by
    simp only [Set.mem_preimage, htr]
  by_cases hε : ε ∈ trunc k ⁻¹' t
  · rw [Set.indicator_of_mem hε]
    simp only [condAvg]
    congr 1
    exact Finset.sum_congr rfl fun η _ => (Set.indicator_of_mem ((hmem η).mpr hε) f).symm
  · rw [Set.indicator_of_notMem hε]
    simp only [condAvg]
    rw [Finset.sum_eq_zero fun η _ => Set.indicator_of_notMem (fun h => hε ((hmem η).mp h)) f,
      smul_zero]

/-- Mathlib's conditional expectation on the cube is the cube conditional expectation
`condAvg k`, everywhere (every point has positive mass). -/
private theorem condExp_eq_condAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (k : ℕ) (f : (Fin N → Bool) → E) :
    (ProbabilityTheory.uniformOn Set.univ)[f | filtration N k] = condAvg k f := by
  refine (eq_of_ae_eq_uniformOn (ae_eq_condExp_of_forall_setIntegral_eq ((filtration N).le k)
    Integrable.of_finite (fun s _ _ => Integrable.of_finite.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_filtration_iff.mpr (condAvg_eq_of_agree k f)).aestronglyMeasurable)).symm
  obtain ⟨t, -, rfl⟩ := hs
  rw [← integral_indicator MeasurableSet.of_discrete,
    ← integral_indicator MeasurableSet.of_discrete, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  simp_rw [uniformOn_singleton]
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  simp_rw [indicator_condAvg]
  exact sum_condAvg k _

/-- Every martingale for the natural filtration of the signs and the uniform probability is a
Paley–Walsh martingale plus its (constant) initial value. -/
theorem exists_paleyWalsh_of_martingale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {M : ℕ → (Fin N → Bool) → E}
    (hM : Martingale M (filtration N) (ProbabilityTheory.uniformOn Set.univ)) :
    ∃ ξ : Fin N → (Fin N → Bool) → E, IsPredictable ξ ∧
      ∀ n ε, M n ε = M 0 ε + paleyWalsh ξ n ε := by
  refine exists_paleyWalsh_of_isCubeMartingale
    ⟨fun n => stronglyMeasurable_filtration_iff.mp (hM.stronglyAdapted n), fun n => ?_⟩
  rw [← condExp_eq_condAvg]
  exact eq_of_ae_eq_uniformOn (hM.condExp_ae_eq (Nat.le_succ n))

end BanachProbability.SignCube
