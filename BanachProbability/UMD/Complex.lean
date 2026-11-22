module

public import BanachProbability.UMD.Incremental

/-!
# Complex UMD constants

For a complex Banach space `X` and `p ∈ (1, ∞)`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)` (Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach Spaces I* (2016), Proposition 4.2.10, p. 286, for the constants with deterministic
multipliers; quoted by Yaroslavtsev, *Even Fourier multipliers and martingale transforms in
infinite dimensions*, Indag. Math. 29 (2018), Lemma 3.2), for general filtrations.

The proof is that of the book. The first inequality holds because real signs are unimodular
complex numbers. For the second, a sequence `α = (α_1, …, α_n)` of complex numbers of modulus at
most one is `α = (π / 2) Σ_j λ^{(j)} ε^{(j)}` with `ε^{(j)} ∈ {−1, 1}^n` and `Σ_j |λ^{(j)}| ≤ 1`
(Proposition 3.2.14, `exists_sum_coin_complex`); by the triangle inequality in `L^p` and the real
UMD property
`‖Σ_k α_k dY_k‖_p ≤ (π / 2) Σ_j |λ^{(j)}| ‖Σ_k ε^{(j)}_k dY_k‖_p ≤ (π / 2) UMD_p (X) ‖Y_n‖_p`
(`cpx_eLpNorm_le`). This is the inequality for deterministic multipliers; for the predictable ones
of `complexUMDConst` it follows by Theorem 4.2.25 of the book
(`isComplexUMDBound_iff_isDeterministicUMDBound`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every complex `UMD_p` bound is a real one: signs `σ_k = ±1` are unimodular complex multipliers,
and `(σ_k : ℂ) • v = σ_k • v`. -/
private theorem cpx_isUMDBound_of_isComplexUMDBound {p : ℝ} {β : ℝ≥0∞}
    (h : IsComplexUMDBound X p β) : IsUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
  have key := h Ω mΩ μ ℱ Y (fun k ω => (σ k ω : ℂ)) hY hY0
    (fun k ω => by rcases hσ k ω with h1 | h1 <;> simp [h1])
    (fun k => Complex.continuous_ofReal.comp_stronglyMeasurable (hσm k)) n
  simp only [Complex.coe_smul] at key
  have hT : AEStronglyMeasurable
      (fun ω => ∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)) μ :=
    stp_aestronglyMeasurable_transform hY hσm n
  rwa [eLpNorm_norm _ hT,
    eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]

omit [CompleteSpace X] in
/-- The second inequality of HNVW I, Proposition 4.2.10 (p. 286), for deterministic multipliers: if
`β` is a UMD constant for real signs, then `‖Σ_{k<n} α_{k+1} (Y_{k+1} − Y_k)‖_p ≤ (π / 2) β ‖Y_n‖_p`
for complex numbers `|α_k| ≤ 1`. By Proposition 3.2.14, `α = Σ_ε c (ε) ε` with
`Σ_ε |c (ε)| ≤ π / 2`, the sums over the sign vectors `ε ∈ {−1, 1}^n`; then the triangle inequality
in `L^p` and the real UMD inequality for each sign vector give the claim. -/
private theorem cpx_eLpNorm_le {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDeterministicUMDBound ℝ X p β) {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ)
    (hY0 : ∀ ω, Y 0 ω = 0) {α : ℕ → ℂ} (hα : ∀ k, ‖α k‖ ≤ 1) (n : ℕ) :
    eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, α (k + 1) • (Y (k + 1) ω - Y k ω)‖)
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Real.pi / 2) * β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hdYm : ∀ k, StronglyMeasurable (fun ω => Y (k + 1) ω - Y k ω) := fun k =>
    ((hY.stronglyAdapted (k + 1)).mono (ℱ.le _)).sub ((hY.stronglyAdapted k).mono (ℱ.le _))
  -- the decomposition `α = Σ_ε c (ε) ε`
  obtain ⟨c, hc, hαc⟩ := exists_sum_coin_complex (fun j : Fin n => α (j + 1)) fun j => hα _
  -- the transforms by the sign vectors
  set T : (Fin n → Bool) → Ω → X :=
    fun ε ω => ∑ j : Fin n, SignCube.coin (ε j) • (Y (j + 1) ω - Y j ω) with hT
  have hTm : ∀ ε, AEStronglyMeasurable (T ε) μ := fun ε =>
    (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      (stronglyMeasurable_const (b := SignCube.coin (ε j))).smul (hdYm j)).aestronglyMeasurable
  have hTb : ∀ ε, eLpNorm (T ε) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
    intro ε
    have key := h Ω mΩ μ ℱ Y
      (fun i => if hi : i - 1 < n then SignCube.coin (ε ⟨i - 1, hi⟩) else 1) hY hY0
      (fun i => by split_ifs <;> simp [SignCube.abs_coin]) n
    have e : (fun ω => ∑ k ∈ Finset.range n,
        (fun i => if hi : i - 1 < n then SignCube.coin (ε ⟨i - 1, hi⟩) else 1) (k + 1) •
          (Y (k + 1) ω - Y k ω)) = T ε := by
      funext ω
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [← eLpNorm_norm _ (hTm ε), ← e]
    exact key
  have hsum : (fun ω => ∑ k ∈ Finset.range n, α (k + 1) • (Y (k + 1) ω - Y k ω)) =
      ∑ ε, c ε • T ε := by
    funext ω
    rw [Finset.sum_range, Finset.sum_apply]
    simp only [Pi.smul_apply, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hαc j, Finset.sum_smul]
    exact Finset.sum_congr rfl fun ε _ => by rw [mul_smul, Complex.coe_smul]
  have hm : AEStronglyMeasurable
      (fun ω => ∑ k ∈ Finset.range n, α (k + 1) • (Y (k + 1) ω - Y k ω)) μ :=
    (Finset.stronglyMeasurable_fun_sum _ fun k _ =>
      (stronglyMeasurable_const (b := α (k + 1))).smul (hdYm k)).aestronglyMeasurable
  rw [eLpNorm_norm _ hm, hsum]
  calc eLpNorm (∑ ε, c ε • T ε) (ENNReal.ofReal p) μ
      ≤ ∑ ε, eLpNorm (c ε • T ε) (ENNReal.ofReal p) μ := eLpNorm_sum_le hp1
    _ ≤ ∑ ε, ENNReal.ofReal ‖c ε‖ *
          (β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ) := by
        refine Finset.sum_le_sum fun ε _ => ?_
        rw [eLpNorm_const_smul, ofReal_norm]
        gcongr
        exact hTb ε
    _ = ENNReal.ofReal (∑ ε, ‖c ε‖) *
          (β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
    _ ≤ ENNReal.ofReal (Real.pi / 2) *
          (β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

/-- `UMD_p (X) ≤ UMD_{ℂ,p} (X)`: real signs are unimodular complex multipliers. -/
theorem umdConst_le_complexUMDConst {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p := by
  exact umdConst_le_of_isUMDBound
    (cpx_isUMDBound_of_isComplexUMDBound (isComplexUMDBound_complexUMDConst hp))

/-- `UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)` (HNVW I, Proposition 4.2.10): for deterministic
multipliers by `cpx_eLpNorm_le`, hence for predictable ones by Theorem 4.2.25. -/
theorem complexUMDConst_le_pi_div_two_mul {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p := by
  have hR : IsDeterministicUMDBound ℝ X p (umdConst X p) :=
    (isUMDBound_iff_isDeterministicUMDBound hp.le).1 (isUMDBound_umdConst hp)
  refine complexUMDConst_le_of_isComplexUMDBound
    ((isComplexUMDBound_iff_isDeterministicUMDBound hp.le).2 ?_)
  intro Ω mΩ μ _ ℱ Y ε hY hY0 hε n
  exact cpx_eLpNorm_le hp.le hR hY hY0 (fun k => (hε k).le) n

/-- **Complex UMD constants** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.10;
Yaroslavtsev 2018, Lemma 3.2): `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
theorem umdConst_le_complexUMDConst_le {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  ⟨umdConst_le_complexUMDConst hp, complexUMDConst_le_pi_div_two_mul hp⟩

end BanachProbability
