module

public import BanachProbability.UMD.Defs

/-!
# The randomised UMD property and decoupling of Paley–Walsh martingales

**The randomised UMD property** (Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces
I* (2016), Proposition 4.2.3, p. 282): if `X` is `UMD_p` with constant `β`, then for every
`X`-valued martingale `Y` started at `0` and independent fair signs `ε_k`, on a further probability
space, `β⁻¹ ‖Y_n‖_p ≤ ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`
(`IsUMDBound.isLowerRandomisedUMDBound`, `IsUMDBound.isUpperRandomisedUMDBound`), and conversely
two such inequalities with constants `β⁻`, `β⁺` give the UMD constant `β⁻ β⁺`
(`isUMDBound_of_randomised`): `max (β⁻, β⁺) ≤ β ≤ β⁻ β⁺`.

The proof is the book's, p. 279–280: Proposition 4.1.16, (1)⇒(2) and (2)⇒(1), from which the book
deduces Proposition 4.2.3 ("As an immediate consequence we therefore obtain the following corollary
to Proposition 4.1.16", p. 282). (1)⇒(2): for *fixed* values of the signs `ε_k` the sum
`Σ ε_k dY_k` is the transform of `Y` by constant signs, so its norm is at most `β ‖Y_n‖_p`; the
reverse inequality is the same one for the martingale `Σ ε_k dY_k` and the same signs; raise both
to the power `p` and integrate over the signs. (2)⇒(1): for signs `σ_k` the families `(σ_k ε_k)`
and `(ε_k)` have the same law, so
`‖Σ σ_k dY_k‖ ≤ β⁻ ‖Σ ε_k σ_k dY_k‖ = β⁻ ‖Σ ε_k dY_k‖ ≤ β⁻ β⁺ ‖Y_n‖`.

Differences from the source: the scalars, hence the signs and the Rademacher variables, are real;
the signs `σ_k` of the UMD inequality are predictable here, which changes nothing (in (2)⇒(1), for
each `ω` the families `(σ_k (ω) ε_k)` and `(ε_k)` have the same law); the spaces are probability
spaces. Of the dyadic version of the proposition, for Paley–Walsh martingales, only the two
inequalities are proved (`decoupling_dyadic`), not the converse.

**Decoupling** of Paley–Walsh martingales. For a Paley–Walsh martingale
`Y_n = Σ_{k<n} ε_k ξ_k (ε)` with predictable `ξ` and an independent copy `ε̃` of the signs, the
decoupled sum `Ỹ_n = Σ_{k<n} ε̃_k ξ_k (ε)` satisfies
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}` (`decoupling_dyadic`, `decoupling`). This is
the randomised UMD property for Paley–Walsh martingales, as `dY_k = ε_k ξ_k` and, for each `ε`, the
families `(ε̃_k ε_k)` and `(ε̃_k)` have the same law (`SignCube.avg_mul_left`). The book also has
it as a case of the tangent martingale inequality of Hitczenko and McConnell (HNVW, Theorem 4.4.11
with Example 4.4.13, p. 326), with the same constant. S. Cox, M. Veraar (*Some remarks on tangent
martingale difference sequences in `L¹`-spaces*, Electron. Commun. Probab. 12 (2007)) credit the
result for tangent sequences to T. R. McConnell (1989) and, independently, P. Hitczenko, and a proof
from the definition of UMD to S. Montgomery-Smith.

Since the dyadic constant is that of the space in which the `ξ_k` take values, the statement for a
subspace `V` (with the constant `UMD_p^Δ (V)`) is the statement for the normed space `V`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

/-- The average over the cube of nonnegative numbers, in `[0, ∞]`. -/
private theorem dec_ofReal_avg {N : ℕ} {a : (Fin N → Bool) → ℝ} (ha : ∀ ε, 0 ≤ a ε) :
    ENNReal.ofReal (avg a) = ((2 : ℝ≥0∞) ^ N)⁻¹ * ∑ ε, ENNReal.ofReal (a ε) := by
  rw [avg, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_sum_of_nonneg fun ε _ => ha ε,
    ENNReal.div_eq_inv_mul, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The average over the cube of a constant, in `[0, ∞]`. -/
private theorem dec_avg_const (N : ℕ) (c : ℝ≥0∞) :
    ((2 : ℝ≥0∞) ^ N)⁻¹ * ∑ _ε : Fin N → Bool, c = c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

section Randomised

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {p : ℝ}

/-- The randomised sum of a measurable process is measurable on the product. -/
private theorem dec_aestronglyMeasurable {Y : ℕ → Ω → X} (hY : ∀ k, StronglyMeasurable (Y k))
    (n : ℕ) (ν : Measure (Ω × (Fin n → Bool))) :
    AEStronglyMeasurable (randomisedSum Y n) ν := by
  refine (Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_).aestronglyMeasurable
  exact (StronglyMeasurable.of_discrete (f := fun η : Fin n → Bool => coin (η k))).comp_measurable
    measurable_snd |>.smul (((hY (k + 1)).comp_measurable measurable_fst).sub
      ((hY k).comp_measurable measurable_fst))

private theorem dec_eLpNorm_rpow {S E : Type*} [NormedAddCommGroup E] {mS : MeasurableSpace S}
    {ν : Measure S} (hp : 0 < p) {f : S → E} (hf : AEStronglyMeasurable f ν) :
    eLpNorm f (ENNReal.ofReal p) ν ^ p = ∫⁻ z, ‖f z‖ₑ ^ p ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The integral over the uniform probability on the cube is the average. -/
private theorem dec_lintegral_uniformOn {N : ℕ} (G : (Fin N → Bool) → ℝ≥0∞) :
    ∫⁻ η, G η ∂(ProbabilityTheory.uniformOn Set.univ) = ((2 : ℝ≥0∞) ^ N)⁻¹ * ∑ η, G η := by
  rw [lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  have hμ : (ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool))) {η} =
      ((2 : ℝ≥0∞) ^ N)⁻¹ := by
    rw [← ofReal_measureReal, uniformOn_singleton, one_div,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hμ, mul_comm]

/-- Integrating over the signs (Fubini): the `p`-th power of the `L^p` norm of the randomised sum is
the average over the signs `η` of the `p`-th powers of the norms of `Σ η_k (Y_{k+1} − Y_k)`. -/
private theorem dec_eLpNorm_randomisedSum_rpow [SFinite μ] (hp : 0 < p) {Y : ℕ → Ω → X}
    (hY : ∀ k, StronglyMeasurable (Y k)) (n : ℕ) :
    eLpNorm (randomisedSum Y n) (ENNReal.ofReal p)
        (μ.prod (ProbabilityTheory.uniformOn Set.univ)) ^ p =
      ((2 : ℝ≥0∞) ^ n)⁻¹ * ∑ η : Fin n → Bool,
        eLpNorm (fun ω => randomisedSum Y n (ω, η)) (ENNReal.ofReal p) μ ^ p := by
  have hm := dec_aestronglyMeasurable hY n (μ.prod (ProbabilityTheory.uniformOn Set.univ))
  rw [dec_eLpNorm_rpow hp hm, lintegral_prod_symm _ (hm.enorm.pow_const p),
    dec_lintegral_uniformOn]
  congr 1
  refine Finset.sum_congr rfl fun η _ => (dec_eLpNorm_rpow hp ?_).symm
  refine (Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_).aestronglyMeasurable
  exact (stronglyMeasurable_const (b := coin (η k))).smul ((hY (k + 1)).sub (hY k))

/-- The constant signs `η`, as the multipliers of a martingale transform. -/
private def decSign {n : ℕ} (η : Fin n → Bool) (k : ℕ) : ℝ :=
  if hk : k - 1 < n then coin (η ⟨k - 1, hk⟩) else 1

private theorem decSign_eq {n : ℕ} (η : Fin n → Bool) (k : ℕ) :
    decSign η k = 1 ∨ decSign η k = -1 := by
  unfold decSign
  split_ifs
  · exact coin_eq_one_or_eq_neg_one _
  · exact Or.inl rfl

/-- For fixed signs the randomised sum is a martingale transform by constant signs. -/
private theorem dec_randomisedSum_eq (Y : ℕ → Ω → X) {n : ℕ} (η : Fin n → Bool) (ω : Ω) :
    randomisedSum Y n (ω, η) = martingaleTransform (fun k _ => decSign η k) Y n ω := by
  rw [randomisedSum, martingaleTransform, Finset.sum_range]
  exact Finset.sum_congr rfl fun k _ => by simp [decSign]

variable [CompleteSpace X]

/-- The inequalities for fixed signs `η` (HNVW I, proof of Proposition 4.1.16, (1)⇒(2), p. 279): the
UMD inequality for `Y` and the signs `η`, and for the martingale `Σ η_k dY_k` and the same signs. -/
private theorem dec_fixed {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {β : ℝ≥0∞} (h : IsUMDBound X p β)
    {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0) {n : ℕ} (η : Fin n → Bool) :
    eLpNorm (fun ω => randomisedSum Y n (ω, η)) (ENNReal.ofReal p) μ ≤
        β * eLpNorm (Y n) (ENNReal.ofReal p) μ ∧
      eLpNorm (Y n) (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => randomisedSum Y n (ω, η)) (ENNReal.ofReal p) μ := by
  set T : ℕ → Ω → X := martingaleTransform (fun k _ => decSign η k) Y with hT_def
  have hT : Martingale T ℱ μ := martingale_martingaleTransform hY
    (fun _ => stronglyMeasurable_const) fun k => ⟨1, fun _ => by
      rcases decSign_eq η (k + 1) with h | h <;> simp [h]⟩
  have hR : (fun ω => randomisedSum Y n (ω, η)) = T n := funext fun ω => dec_randomisedSum_eq Y η ω
  have hnorm : ∀ {M : ℕ → Ω → X}, Martingale M ℱ μ → ∀ m,
      eLpNorm (fun ω => ‖M m ω‖) (ENNReal.ofReal p) μ = eLpNorm (M m) (ENNReal.ofReal p) μ :=
    fun hM m => eLpNorm_norm _ ((hM.stronglyAdapted m).mono (ℱ.le m)).aestronglyMeasurable
  -- the transform of `T` by the same signs is `Y`
  have hTT : martingaleTransform (fun k _ => decSign η k) T n = Y n := by
    funext ω
    simp only [hT_def, martingaleTransform, Finset.sum_range_succ, add_sub_cancel_left, smul_smul]
    have h1 : ∀ k, decSign η (k + 1) * decSign η (k + 1) = 1 := fun k => by
      rcases decSign_eq η (k + 1) with h | h <;> simp [h]
    simp only [h1, one_smul, Finset.sum_range_sub (fun k => Y k ω), hY0, sub_zero]
  have k1 := h Ω mΩ μ ℱ Y (fun k _ => decSign η k) hY hY0 (fun k _ => decSign_eq η k)
    (fun _ => stronglyMeasurable_const) n
  have k2 := h Ω mΩ μ ℱ T (fun k _ => decSign η k) hT (fun ω => by simp [hT_def,
    martingaleTransform]) (fun k _ => decSign_eq η k) (fun _ => stronglyMeasurable_const) n
  change eLpNorm (fun ω => ‖T n ω‖) _ μ ≤ _ at k1
  change eLpNorm (fun ω => ‖martingaleTransform (fun k _ => decSign η k) T n ω‖) _ μ ≤ _ at k2
  rw [hTT, hnorm hY, hnorm hT] at k2
  rw [hnorm hY, hnorm hT] at k1
  rw [hR]
  exact ⟨k1, k2⟩

/-- **The randomised UMD property**, the right-hand inequality (HNVW I, Proposition 4.2.3, p. 282,
`β⁺ ≤ β`; proof of Proposition 4.1.16, (1)⇒(2), p. 279): a UMD constant `β` satisfies
`‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`. -/
theorem IsUMDBound.isUpperRandomisedUMDBound (hp : 0 < p) {β : ℝ≥0∞} (h : IsUMDBound X p β) :
    IsUpperRandomisedUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Y hY hY0 n
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    dec_eLpNorm_randomisedSum_rpow hp fun k => (hY.stronglyAdapted k).mono (ℱ.le k)]
  refine le_of_le_of_eq ?_ (dec_avg_const n _)
  gcongr with η
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact ENNReal.rpow_le_rpow (dec_fixed h hY hY0 η).1 hp.le

/-- **The randomised UMD property**, the left-hand inequality (HNVW I, Proposition 4.2.3, p. 282,
`β⁻ ≤ β`; proof of Proposition 4.1.16, (1)⇒(2), p. 279): a UMD constant `β` satisfies
`‖Y_n‖_p ≤ β ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p`. -/
theorem IsUMDBound.isLowerRandomisedUMDBound (hp : 0 < p) {β : ℝ≥0∞} (h : IsUMDBound X p β) :
    IsLowerRandomisedUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Y hY hY0 n
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    dec_eLpNorm_randomisedSum_rpow hp fun k => (hY.stronglyAdapted k).mono (ℱ.le k),
    mul_left_comm, Finset.mul_sum]
  refine le_of_eq_of_le (dec_avg_const n _).symm ?_
  gcongr with η
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact ENNReal.rpow_le_rpow (dec_fixed h hY hY0 η).2 hp.le

omit [CompleteSpace X] in
/-- The randomised sums of `Y` and of its transform by signs have the same law: for each `ω` the
families `(ε_k σ_k (ω))` and `(ε_k)` have the same law (HNVW I, proof of Proposition 4.1.16,
(2)⇒(1), p. 280). -/
private theorem dec_eLpNorm_randomisedSum_transform [SFinite μ] (hp : 0 < p) {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) {σ : ℕ → Ω → ℝ} (hσ : ∀ n ω, σ n ω = 1 ∨ σ n ω = -1)
    (hσm : ∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) (n : ℕ) :
    eLpNorm (randomisedSum (martingaleTransform σ Y) n) (ENNReal.ofReal p)
        (μ.prod (ProbabilityTheory.uniformOn Set.univ)) =
      eLpNorm (randomisedSum Y n) (ENNReal.ofReal p)
        (μ.prod (ProbabilityTheory.uniformOn Set.univ)) := by
  have hYm : ∀ k, StronglyMeasurable (Y k) := fun k => (hY.stronglyAdapted k).mono (ℱ.le k)
  have hTm : ∀ k, StronglyMeasurable (martingaleTransform σ Y k) := fun k =>
    Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      ((hσm j).mono (ℱ.le j)).smul ((hYm (j + 1)).sub (hYm j))
  refine (ENNReal.rpow_left_injective hp.ne') ?_
  have hmY := dec_aestronglyMeasurable hYm n (μ.prod (ProbabilityTheory.uniformOn Set.univ))
  have hmT := dec_aestronglyMeasurable hTm n (μ.prod (ProbabilityTheory.uniformOn Set.univ))
  simp only
  rw [dec_eLpNorm_rpow hp hmY, dec_eLpNorm_rpow hp hmT, lintegral_prod _ (hmY.enorm.pow_const p),
    lintegral_prod _ (hmT.enorm.pow_const p)]
  refine lintegral_congr fun ω => ?_
  rw [dec_lintegral_uniformOn, dec_lintegral_uniformOn]
  congr 1
  -- the signs `σ_{k+1} (ω)`, as a sign vector
  set s : Fin n → Bool := fun k => decide (σ (k + 1) ω = 1) with hs
  have hcoin : ∀ k : Fin n, coin (s k) = σ (k + 1) ω := fun k => by
    rcases hσ (k + 1) ω with h | h
    · simp [hs, h]
    · simp [hs, h]
      norm_num
  rw [← Equiv.sum_comp ((scb_mul_involutive s).toPerm _) fun η => ‖randomisedSum Y n (ω, η)‖ₑ ^ p]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  simp only [randomisedSum, martingaleTransform, Finset.sum_range_succ, add_sub_cancel_left,
    Function.Involutive.coe_toPerm, coin_mul_apply, hcoin, smul_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

/-- **The randomised UMD property**, the converse (HNVW I, Proposition 4.2.3, p. 282,
`β ≤ β⁻ β⁺`; proof of Proposition 4.1.16, (2)⇒(1), p. 280): the two inequalities (4.10) with
constants `β⁻`, `β⁺` give the UMD constant `β⁻ β⁺`:
`‖Σ σ_k dY_k‖ ≤ β⁻ ‖Σ ε_k σ_k dY_k‖ = β⁻ ‖Σ ε_k dY_k‖ ≤ β⁻ β⁺ ‖Y_n‖`. -/
theorem isUMDBound_of_randomised (hp : 0 < p) {β' β'' : ℝ≥0∞}
    (hl : IsLowerRandomisedUMDBound X p β') (hu : IsUpperRandomisedUMDBound X p β'') :
    IsUMDBound X p (β' * β'') := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
  have hT : Martingale (martingaleTransform σ Y) ℱ μ := martingale_martingaleTransform hY hσm
    fun k => ⟨1, fun ω => by rcases hσ (k + 1) ω with h | h <;> simp [h]⟩
  change eLpNorm (fun ω => ‖martingaleTransform σ Y n ω‖) _ μ ≤ _
  rw [eLpNorm_norm _ ((hT.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable,
    eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable, mul_assoc]
  refine (hl Ω mΩ μ ℱ _ hT (fun ω => by simp [martingaleTransform]) n).trans ?_
  rw [dec_eLpNorm_randomisedSum_transform hp hY hσ hσm]
  gcongr
  exact hu Ω mΩ μ ℱ Y hY hY0 n

end Randomised

section PaleyWalsh

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {N : ℕ} {p : ℝ}

omit [NormedSpace ℝ X] in
private theorem dec_ofReal_lpNorm_rpow (hp : 0 < p) (f : (Fin N → Bool) → X) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) ^ p =
      ENNReal.ofReal (avg fun ε => ‖f ε‖ ^ p) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (lpNorm_nonneg (fun x => norm_nonneg x) p f) hp.le,
    lpNorm_rpow (fun x : X => norm_nonneg x) hp]

/-- `decoupledLpNorm p ξ n` is the `L^p` norm of the decoupled sum `Σ_{k<n} ε̃_k ξ_k (ε)` on the
product of two sign cubes, with the uniform probabilities. -/
theorem eLpNorm_prod_uniformOn (hp : 0 < p) (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) :
    eLpNorm (fun z : (Fin N → Bool) × (Fin N → Bool) => paleyWalsh (fun k _ => ξ k z.1) n z.2)
        (ENNReal.ofReal p) ((ProbabilityTheory.uniformOn Set.univ).prod
          (ProbabilityTheory.uniformOn Set.univ)) =
      ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  have h0 : ∀ ε : Fin N → Bool,
      0 ≤ avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p := fun ε =>
    avg_nonneg fun ε' => Real.rpow_nonneg (norm_nonneg _) p
  have h1 : 0 ≤ avg (fun ε => avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) :=
    avg_nonneg h0
  have hm : AEStronglyMeasurable (fun z : (Fin N → Bool) × (Fin N → Bool) =>
      paleyWalsh (fun k _ => ξ k z.1) n z.2) ((ProbabilityTheory.uniformOn Set.univ).prod
        (ProbabilityTheory.uniformOn Set.univ)) :=
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine ENNReal.rpow_left_injective hp.ne' ?_
  simp only
  rw [dec_eLpNorm_rpow hp hm, lintegral_prod _ (hm.enorm.pow_const p), decoupledLpNorm,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg h1 _) hp.le, ← Real.rpow_mul h1,
    one_div_mul_cancel hp.ne', Real.rpow_one, dec_lintegral_uniformOn, dec_ofReal_avg h0]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [dec_lintegral_uniformOn, dec_ofReal_avg fun ε' => Real.rpow_nonneg (norm_nonneg _) p]
  congr 1
  refine Finset.sum_congr rfl fun ε' _ => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]

/-- The inequalities for fixed signs `η` (HNVW I, proof of Proposition 4.1.16, (1)⇒(2), p. 279, for
Paley–Walsh martingales): the dyadic UMD inequality for `Σ ε_k ξ_k` and the constant signs `η`, and
for the Paley–Walsh martingale `Σ ε_k η_k ξ_k` and the same signs. -/
private theorem dec_fixed_dyadic {β : ℝ≥0∞} (h : IsDyadicUMDBound X p β)
    {ξ : Fin N → (Fin N → Bool) → X} (hξ : IsPredictable ξ) (η : Fin N → Bool) (n : ℕ) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
          (paleyWalsh (fun k ε => coin (η k) • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
          (paleyWalsh (fun k ε => coin (η k) • ξ k ε) n)) := by
  have hs : IsPredictable fun (k : Fin N) (_ : Fin N → Bool) => coin (η k) := fun _ _ _ _ => rfl
  have hs1 : ∀ (k : Fin N) (_ : Fin N → Bool), coin (η k) = 1 ∨ coin (η k) = -1 := fun k _ =>
    coin_eq_one_or_eq_neg_one _
  refine ⟨h N ξ _ hξ hs hs1 n, ?_⟩
  have key := h N _ _ (hs.smul hξ) hs hs1 n
  simpa only [smul_smul, coin_mul_self, one_smul] using key

/-- The decoupled sum is the randomised sum of `Σ ε_k ξ_k`: integrating over the signs,
`E_ε E_{ε̃} ‖Σ ε̃_k ξ_k (ε)‖^p = E_η E_ε ‖Σ η_k ε_k ξ_k (ε)‖^p`, as for each `ε` the families
`(ε̃_k)` and `(ε_k η_k)` have the same law. -/
private theorem dec_ofReal_decoupledLpNorm_rpow (hp : 0 < p) (ξ : Fin N → (Fin N → Bool) → X)
    (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ^ p =
      ((2 : ℝ≥0∞) ^ N)⁻¹ * ∑ η : Fin N → Bool, ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
        (paleyWalsh (fun k ε => coin (η k) • ξ k ε) n)) ^ p := by
  have h0 : ∀ ε : Fin N → Bool,
      0 ≤ avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p := fun ε =>
    avg_nonneg fun ε' => Real.rpow_nonneg (norm_nonneg _) p
  have h1 : 0 ≤ avg (fun ε => avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) :=
    avg_nonneg h0
  have hlaw : ∀ ε : Fin N → Bool, (avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) =
      avg fun η => ‖paleyWalsh (fun k ε => coin (η k) • ξ k ε) n ε‖ ^ p := by
    intro ε
    rw [← avg_mul_left ε fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p]
    congr 1
    funext η
    simp only [paleyWalsh, coin_mul_apply, smul_smul]
  have hswap : avg (fun ε => avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) =
      avg fun η => avg fun ε =>
        ‖paleyWalsh (fun k ε => coin (η k) • ξ k ε) n ε‖ ^ p := by
    simp only [hlaw]
    simp only [avg, ← Finset.sum_div]
    rw [Finset.sum_comm]
  rw [decoupledLpNorm, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg h1 _) hp.le,
    ← Real.rpow_mul h1, one_div_mul_cancel hp.ne', Real.rpow_one, hswap,
    dec_ofReal_avg fun η => avg_nonneg fun ε => Real.rpow_nonneg (norm_nonneg _) p]
  simp only [dec_ofReal_lpNorm_rpow hp]

/-- **Decoupling** of Paley–Walsh martingales with the dyadic UMD constant:
`‖Ỹ_n‖_{L^p} ≤ UMD_p^Δ ‖Y_n‖_{L^p}` and `‖Y_n‖_{L^p} ≤ UMD_p^Δ ‖Ỹ_n‖_{L^p}` (HNVW I,
Proposition 4.2.3, p. 282, for Paley–Walsh martingales). For fixed signs `η` both are the dyadic
UMD inequality for constant signs (`dec_fixed_dyadic`); raise to the power `p` and integrate over
`η` (proof of Proposition 4.1.16, (1)⇒(2), p. 279). -/
theorem decoupling_dyadic {p : ℝ} (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X)
    (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        dyadicUMDConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        dyadicUMDConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  have hp0 : 0 < p := by linarith
  have hu := isDyadicUMDBound_dyadicUMDConst (X := X) hp0
  constructor
  · rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      dec_ofReal_decoupledLpNorm_rpow hp0]
    refine le_of_le_of_eq ?_ (dec_avg_const N _)
    gcongr with η
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    exact ENNReal.rpow_le_rpow (dec_fixed_dyadic hu hξ η n).1 hp0.le
  · rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      dec_ofReal_decoupledLpNorm_rpow hp0, mul_left_comm, Finset.mul_sum]
    refine le_of_eq_of_le (dec_avg_const N _).symm ?_
    gcongr with η
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    exact ENNReal.rpow_le_rpow (dec_fixed_dyadic hu hξ η n).2 hp0.le

/-- **Decoupling** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.3; Cox–Veraar 2007) for
Paley–Walsh martingales in a real Banach space, with the constant `UMD_p (X)`:
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`. -/
theorem decoupling [CompleteSpace X] {p : ℝ} (hp : 1 < p) {N : ℕ}
    (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  have h := decoupling_dyadic hp ξ hξ n
  have hle := dyadicUMDConst_le_umdConst (X := X) hp
  exact ⟨h.1.trans (by gcongr), h.2.trans (by gcongr)⟩

end PaleyWalsh

end BanachProbability
