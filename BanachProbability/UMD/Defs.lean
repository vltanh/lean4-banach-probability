module

public import BanachProbability.SignCube.Bridge
public import BanachProbability.Martingale.Transform
public import Mathlib.Analysis.Complex.Basic

/-!
# UMD constants

A Banach space `X` has the UMD property (unconditional martingale differences) for an exponent
`p ∈ (1, ∞)` when martingale transforms by predictable signs are bounded in `L^p (X)`:
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}` for every `X`-valued martingale `Y`
started at `0` and every sequence of signs `σ_k ∈ {±1}` with `σ_{k+1}` `ℱ_k`-measurable. The
constants, defined in `BanachProbability.Defs`:

* `IsUMDBound X p β` and `umdConst X p`, the best constant `UMD_p (X) ∈ [0, ∞]`, for martingales
  on arbitrary probability spaces (Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I*
  (2016), Definition 4.2.1; Pisier, *Martingales in Banach spaces* (2016), Chapter 5). The
  definition here quantifies over predictable signs and martingales started at `0`; the sources
  define the constant with deterministic signs, which, on probability spaces, gives the same
  constant (`BanachProbability.umdConst_eq_sInf_isDeterministicUMDBound`; Hytönen–van
  Neerven–Veraar–Weis, Theorem 4.2.25);
* `IsDyadicUMDBound X p β` and `dyadicUMDConst X p`, the same for Paley–Walsh martingales on the
  sign cube, `UMD_p^Δ (X)`, with predictable signs, defined here (with deterministic signs the
  constants are the same, `isUMDBound_iff_isDeterministicDyadicUMDBound`);
* `IsComplexUMDBound X p β`, `complexUMDConst X p` and their dyadic versions, for a complex
  Banach space and predictable unimodular complex multipliers, `UMD_{ℂ,p} (X)`.

Burkholder's exponent is `pStar p = max (p, p / (p − 1))`, defined here.

Basic facts: the constants are attained (`isUMDBound_umdConst`), they do not increase under linear
isometric embeddings (`umdConst_le_of_linearIsometry`), they are at least `1` on a nonzero space
(`one_le_umdConst`), and the dyadic constant is at most the full one
(`dyadicUMDConst_le_umdConst`). In fact `dyadicUMDConst X p = umdConst X p`, a theorem of Maurey
(`BanachProbability.dyadicUMDConst_eq_umdConst`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

/-- Burkholder's exponent `p* = max (p, p / (p − 1))`. -/
noncomputable def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

section Helpers

/-- The step that makes an infimum of constants a constant: if `A ≤ β c` for every `β ∈ S`, then
`A ≤ (inf S) c`, provided `A = 0` when `c = 0`, and when `c = ∞` and `inf S = 0`. -/
theorem umdd_le_sInf_mul {S : Set ℝ≥0∞} {A c : ℝ≥0∞} (hA : ∀ β ∈ S, A ≤ β * c)
    (h0 : c = 0 → A = 0) (htop : c = ∞ → sInf S = 0 → A = 0) : A ≤ sInf S * c := by
  by_cases hc0 : c = 0
  · simp [h0 hc0]
  by_cases hct : c = ∞
  · by_cases hS : sInf S = 0
    · simp [htop hct hS]
    · rw [hct, ENNReal.mul_top hS]
      exact le_top
  rw [← ENNReal.div_le_iff hc0 hct]
  exact le_sInf fun β hβ => ENNReal.div_le_of_le_mul (hA β hβ)

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A martingale vanishing a.e. at time `n` vanishes a.e. at every time `k ≤ n`:
`Y_k = E [Y_n | ℱ_k] = 0`. -/
private theorem umdd_ae_eq_zero_of_le {Y : ℕ → Ω → E} (hY : Martingale Y ℱ μ) {n : ℕ}
    (hn : Y n =ᵐ[μ] 0) {k : ℕ} (hk : k ≤ n) : Y k =ᵐ[μ] 0 := by
  refine (hY.condExp_ae_eq hk).symm.trans ((condExp_congr_ae hn).trans ?_)
  rw [condExp_zero]

/-- If a martingale vanishes a.e. at time `n`, so does its transform `Σ_{k<n} φ_{k+1} (Y_{k+1} −
Y_k)` by arbitrary multipliers. -/
theorem umdd_transform_ae_eq_zero {𝕜 : Type*} [SMulZeroClass 𝕜 E] {Y : ℕ → Ω → E}
    (hY : Martingale Y ℱ μ) {n : ℕ} (hn : Y n =ᵐ[μ] 0) (φ : ℕ → Ω → 𝕜) :
    (fun ω => ∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω)) =ᵐ[μ] 0 := by
  have h : ∀ᵐ ω ∂μ, ∀ k : ℕ, k ≤ n → Y k ω = 0 := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k ≤ n
    · filter_upwards [umdd_ae_eq_zero_of_le hY hn hk] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [h] with ω hω
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [hω (k + 1) hk', hω k hk'.le, sub_zero, smul_zero]

/-- If `‖Y_n‖_{L^p} = 0` (`p ≠ 0`), the transform at time `n` has `L^p` norm `0`. -/
theorem umdd_eLpNorm_transform_eq_zero {𝕜 : Type*} [SMulZeroClass 𝕜 E] {Y : ℕ → Ω → E}
    (hY : Martingale Y ℱ μ) {p : ℝ≥0∞} (hp : p ≠ 0) {n : ℕ} (hn : eLpNorm (Y n) p μ = 0)
    (φ : ℕ → Ω → 𝕜) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω)) p μ = 0 :=
  (eLpNorm_eq_zero_iff hp).mpr
    (umdd_transform_ae_eq_zero hY ((eLpNorm_eq_zero_iff hp).mp hn) φ)

end Helpers

section Real

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `β` bounds the `±1`-transforms of Paley–Walsh martingales with values in `X`:
`‖Σ_{k<n} σ_k ε_k ξ_k‖_{L^p} ≤ β ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` for predictable `ξ_k` and predictable
signs `σ_k`. -/
def IsDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ n : ℕ,
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic `UMD_p` constant `UMD_p^Δ (X)`. -/
noncomputable def dyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsDyadicUMDBound X p β}

variable {X}

theorem IsUMDBound.mono [CompleteSpace X] {p : ℝ} {β β' : ℝ≥0∞} (h : IsUMDBound X p β)
    (hβ : β ≤ β') : IsUMDBound X p β' := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
  exact (h Ω mΩ μ ℱ Y σ hY hY0 hσ hσm n).trans (by gcongr)

theorem umdConst_le_of_isUMDBound [CompleteSpace X] {p : ℝ} {β : ℝ≥0∞}
    (h : IsUMDBound X p β) : umdConst X p ≤ β :=
  sInf_le h

/-- A constant family `ξ_k ≡ x` is predictable. -/
theorem umdd_isPredictable_const {E : Type*} {N : ℕ} (x : E) :
    IsPredictable (fun (_ : Fin N) (_ : Fin N → Bool) => x) :=
  fun _ _ _ _ => rfl

/-- On the one-sign cube, `‖Σ_{k<1} ε_k x‖ = ‖x‖`. -/
theorem umdd_norm_paleyWalsh_const (x : X) (ε : Fin 1 → Bool) :
    ‖paleyWalsh (fun (_ : Fin 1) (_ : Fin 1 → Bool) => x) 1 ε‖ = ‖x‖ := by
  rw [paleyWalsh_of_le _ le_rfl]
  simp [norm_smul, abs_coin]

/-- The `L^p` norm of a function of constant norm `a` is `a`. -/
theorem umdd_lpNorm_of_norm_eq {E : Type*} [SeminormedAddCommGroup E] {N : ℕ}
    {f : (Fin N → Bool) → E} {a : ℝ} (ha : 0 ≤ a) (hf : ∀ ε, ‖f ε‖ = a) {p : ℝ} (hp : 0 < p) :
    SignCube.lpNorm (fun x => ‖x‖) p f = a := by
  simp only [SignCube.lpNorm, hf, avg_const]
  rw [← Real.rpow_mul ha, mul_one_div_cancel hp.ne', Real.rpow_one]

/-- On the cube, the `L^p` norm of `ε ↦ ‖f ε‖` is the `L^p` norm of `f`. -/
theorem umdd_eLpNorm_norm_uniformOn {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    (f : (Fin N → Bool) → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun ε => ‖f ε‖) (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) := by
  rw [eLpNorm_uniformOn _ hp]
  simp only [SignCube.lpNorm, norm_norm]

/-- The cube instance: the martingale `Y_1 = ε_0 x` on the one-sign cube, transformed by `σ ≡ 1`,
shows that every `UMD_p` constant of a nonzero space is at least `1`. -/
private theorem umdd_one_le_of_isUMDBound [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 0 < p)
    {β : ℝ≥0∞} (h : IsUMDBound X p β) : 1 ≤ β := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have key := h (Fin 1 → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (filtration 1) (fun k => paleyWalsh (fun _ _ => x) k) (fun _ _ => 1)
    (martingale_paleyWalsh _ (umdd_isPredictable_const x)) (fun ω => paleyWalsh_zero _ ω)
    (fun _ _ => Or.inl rfl) (fun _ => stronglyMeasurable_const) 1
  simp only [Finset.sum_range_one, one_smul, zero_add, paleyWalsh_zero, sub_zero] at key
  rw [umdd_eLpNorm_norm_uniformOn _ hp,
    umdd_lpNorm_of_norm_eq (norm_nonneg x) (umdd_norm_paleyWalsh_const x) hp] at key
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by simpa using hx
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).mp (by simpa using key)

/-- The infimum defining `UMD_p (X)` is attained. -/
theorem isUMDBound_umdConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    IsUMDBound X p (umdConst X p) := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  refine umdd_le_sInf_mul (fun β hβ => hβ Ω mΩ μ ℱ Y σ hY hY0 hσ hσm n) (fun h0 => ?_)
    (fun _ hS => ?_)
  · have h0' : Y n =ᵐ[μ] 0 := by
      filter_upwards [(eLpNorm_eq_zero_iff hp0).mp h0] with ω hω
      simpa using hω
    refine (eLpNorm_eq_zero_iff hp0).mpr ?_
    filter_upwards [umdd_transform_ae_eq_zero hY h0' σ] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    rw [hω, norm_zero]
  · rcases subsingleton_or_nontrivial X with hX | hX
    · simp [norm_of_subsingleton]
    · have : 1 ≤ umdConst X p := le_sInf fun _ hβ => umdd_one_le_of_isUMDBound (by linarith) hβ
      exact absurd hS (zero_lt_one.trans_le this).ne'

theorem IsDyadicUMDBound.mono {p : ℝ} {β β' : ℝ≥0∞} (h : IsDyadicUMDBound X p β)
    (hβ : β ≤ β') : IsDyadicUMDBound X p β' := by
  intro N ξ σ hξ hσ hσ1 n
  exact (h N ξ σ hξ hσ hσ1 n).trans (by gcongr)

theorem dyadicUMDConst_le_of_isDyadicUMDBound {p : ℝ} {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : dyadicUMDConst X p ≤ β :=
  sInf_le h

/-- For `p > 0`, the `L^p` norm of a function on the cube vanishes exactly when the function
does (a finite average of nonnegative terms). -/
theorem umdd_lpNorm_eq_zero_iff {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    {f : (Fin N → Bool) → E} {p : ℝ} (hp : 0 < p) :
    SignCube.lpNorm (fun x => ‖x‖) p f = 0 ↔ ∀ ε, f ε = 0 := by
  have hnn : ∀ ε, 0 ≤ ‖f ε‖ ^ p := fun ε => Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · intro h ε
    rw [SignCube.lpNorm, Real.rpow_eq_zero_iff_of_nonneg (avg_nonneg hnn), avg,
      div_eq_zero_iff] at h
    have hsum : ∑ ε, ‖f ε‖ ^ p = 0 := h.1.resolve_right (by positivity)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun ε _ => hnn ε).mp hsum ε (Finset.mem_univ _)
    rw [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)] at this
    exact norm_eq_zero.mp this.1
  · intro h
    simp [SignCube.lpNorm, avg, h, Real.zero_rpow hp.ne', hp.ne']

/-- The zero corner of the dyadic constant: if a Paley–Walsh martingale of a predictable family
vanishes at time `n`, then `ξ_k = 0` for `k < n` (`M_k = E [M_n | ℱ_k] = 0` for `k ≤ n`, and
`‖ξ_k‖ = ‖M_{k+1} − M_k‖`). -/
theorem umdd_eq_zero_of_paleyWalsh_eq_zero {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    (hξ : IsPredictable ξ) {n : ℕ} (h : ∀ ε, paleyWalsh ξ n ε = 0) {k : Fin N} (hk : k.val < n)
    (ε : Fin N → Bool) : ξ k ε = 0 := by
  have hzero : ∀ m ≤ n, paleyWalsh ξ m = 0 := by
    intro m hm
    rw [← min_eq_left hm, ← condAvg_paleyWalsh hξ m n]
    funext ε
    simp [condAvg, h]
  have := norm_paleyWalsh_succ_sub ξ k ε
  rw [congrFun (hzero _ hk) ε, congrFun (hzero _ hk.le) ε] at this
  simp only [Pi.zero_apply, sub_zero, norm_zero] at this
  exact norm_eq_zero.mp this.symm

/-- The infimum defining `UMD_p^Δ (X)` is attained. -/
theorem isDyadicUMDBound_dyadicUMDConst {p : ℝ} (hp : 0 < p) :
    IsDyadicUMDBound X p (dyadicUMDConst X p) := by
  intro N ξ σ hξ hσ hσ1 n
  refine umdd_le_sInf_mul (fun β hβ => hβ N ξ σ hξ hσ hσ1 n) (fun h0 => ?_)
    (fun ht => absurd ht ENNReal.ofReal_ne_top)
  have h1 : SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n) = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp h0) (lpNorm_nonneg (fun x => norm_nonneg x) p _)
  have h2 := (umdd_lpNorm_eq_zero_iff hp).mp h1
  rw [(umdd_lpNorm_eq_zero_iff hp).mpr, ENNReal.ofReal_zero]
  intro ε
  refine Finset.sum_eq_zero fun k hk => ?_
  dsimp only
  rw [umdd_eq_zero_of_paleyWalsh_eq_zero hξ h2 (Finset.mem_filter.mp hk).2 ε, smul_zero,
    smul_zero]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A `UMD_p` constant of `Y` is one of every space linearly isometric to a subspace of `Y`. -/
theorem IsUMDBound.of_linearIsometry [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℝ] Y)
    {p : ℝ} {β : ℝ≥0∞} (h : IsUMDBound Y p β) : IsUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Z σ hZ hZ0 hσ hσm n
  have key := h Ω mΩ μ ℱ (fun m ω => f.toContinuousLinearMap (Z m ω)) σ
    (martingale_map_continuousLinearMap hZ f.toContinuousLinearMap) (fun ω => by simp [hZ0])
    hσ hσm n
  have e1 : (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω •
      (f.toContinuousLinearMap (Z (k + 1) ω) - f.toContinuousLinearMap (Z k ω))‖) =
      fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Z (k + 1) ω - Z k ω)‖ := by
    funext ω
    rw [← f.norm_map (∑ k ∈ Finset.range n, σ (k + 1) ω • (Z (k + 1) ω - Z k ω)), map_sum]
    simp [map_sub, map_smul]
  have e2 : (fun ω => ‖f.toContinuousLinearMap (Z n ω)‖) = fun ω => ‖Z n ω‖ := by
    funext ω
    simp
  rwa [e1, e2] at key

theorem umdConst_le_of_linearIsometry [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℝ] Y)
    (p : ℝ) : umdConst X p ≤ umdConst Y p := by
  exact sInf_le_sInf fun _ hβ => IsUMDBound.of_linearIsometry f hβ

theorem umdConst_congr [CompleteSpace X] [CompleteSpace Y] (e : X ≃ₗᵢ[ℝ] Y) (p : ℝ) :
    umdConst X p = umdConst Y p := by
  exact le_antisymm (umdConst_le_of_linearIsometry e.toLinearIsometry p)
    (umdConst_le_of_linearIsometry e.symm.toLinearIsometry p)

/-- A linear isometry preserves the `L^p` norms of Paley–Walsh martingales. -/
private theorem umdd_lpNorm_paleyWalsh_linearIsometry (f : X →ₗᵢ[ℝ] Y) {N : ℕ}
    (ζ : Fin N → (Fin N → Bool) → X) (p : ℝ) (n : ℕ) :
    SignCube.lpNorm (fun y => ‖y‖) p (paleyWalsh (fun k ε => f (ζ k ε)) n) =
      SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ζ n) := by
  have h : ∀ ε, ‖paleyWalsh (fun k ε => f (ζ k ε)) n ε‖ = ‖paleyWalsh ζ n ε‖ := fun ε => by
    have := map_paleyWalsh f.toLinearMap ζ n ε
    simp only [LinearIsometry.coe_toLinearMap] at this
    rw [← this, f.norm_map]
  simp only [SignCube.lpNorm, h]

theorem IsDyadicUMDBound.of_linearIsometry (f : X →ₗᵢ[ℝ] Y) {p : ℝ} {β : ℝ≥0∞}
    (h : IsDyadicUMDBound Y p β) : IsDyadicUMDBound X p β := by
  intro N ξ σ hξ hσ hσ1 n
  have hfξ : IsPredictable fun k ε => f (ξ k ε) := fun k ε ε' hk => congrArg f (hξ k ε ε' hk)
  have key := h N (fun k ε => f (ξ k ε)) σ hfξ hσ hσ1 n
  have e : paleyWalsh (fun k ε => σ k ε • f (ξ k ε)) n =
      paleyWalsh (fun k ε => f (σ k ε • ξ k ε)) n := by
    simp only [map_smul]
  rwa [e, umdd_lpNorm_paleyWalsh_linearIsometry, umdd_lpNorm_paleyWalsh_linearIsometry] at key

theorem dyadicUMDConst_le_of_linearIsometry (f : X →ₗᵢ[ℝ] Y) (p : ℝ) :
    dyadicUMDConst X p ≤ dyadicUMDConst Y p := by
  exact sInf_le_sInf fun _ hβ => IsDyadicUMDBound.of_linearIsometry f hβ

theorem dyadicUMDConst_congr (e : X ≃ₗᵢ[ℝ] Y) (p : ℝ) :
    dyadicUMDConst X p = dyadicUMDConst Y p := by
  exact le_antisymm (dyadicUMDConst_le_of_linearIsometry e.toLinearIsometry p)
    (dyadicUMDConst_le_of_linearIsometry e.symm.toLinearIsometry p)

/-- `UMD_p (X) ≥ 1` on a nonzero space (the transform by `σ ≡ 1` is the martingale itself). -/
theorem one_le_umdConst [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 1 < p) :
    1 ≤ umdConst X p := by
  exact le_sInf fun _ hβ => umdd_one_le_of_isUMDBound (by linarith) hβ

/-- The cube instance for the dyadic constant: `ξ_0 ≡ x` on the one-sign cube, transformed by
`σ ≡ 1`, shows that every dyadic `UMD_p` constant of a nonzero space is at least `1`. -/
theorem umdd_one_le_of_isDyadicUMDBound [Nontrivial X] {p : ℝ} (hp : 0 < p) {β : ℝ≥0∞}
    (h : IsDyadicUMDBound X p β) : 1 ≤ β := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have key := h 1 (fun _ _ => x) (fun _ _ => 1) (umdd_isPredictable_const x)
    (umdd_isPredictable_const 1) (fun _ _ => Or.inl rfl) 1
  simp only [one_smul] at key
  rw [umdd_lpNorm_of_norm_eq (norm_nonneg x) (umdd_norm_paleyWalsh_const x) hp] at key
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by simpa using hx
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).mp (by simpa using key)

theorem one_le_dyadicUMDConst [Nontrivial X] {p : ℝ} (hp : 0 < p) : 1 ≤ dyadicUMDConst X p := by
  exact le_sInf fun _ hβ => umdd_one_le_of_isDyadicUMDBound hp hβ

/-- The signs of a cube transform, re-indexed as the multipliers of a martingale transform:
`σ' (k + 1) = σ k` for `k < N`, and `σ' (k + 1) = 1` otherwise. -/
private theorem umdd_shift_succ {N : ℕ} {Ω 𝕜 : Type*} [One 𝕜] (σ : Fin N → Ω → 𝕜) (k : ℕ) (ε : Ω) :
    (fun m ε => if hm : m - 1 < N then σ ⟨m - 1, hm⟩ ε else 1) (k + 1) ε =
      if hk : k < N then σ ⟨k, hk⟩ ε else 1 :=
  rfl

/-- The martingale transform of a Paley–Walsh martingale by the re-indexed signs is the
Paley–Walsh martingale of the transformed family:
`Σ_{k<n} σ'_{k+1} (M_{k+1} − M_k) = Σ_{k<n} σ_k ε_k ξ_k`. -/
theorem umdd_sum_shift_smul_paleyWalsh {N : ℕ} {𝕜 : Type*} [Monoid 𝕜] {E : Type*}
    [AddCommGroup E] [Module ℝ E] [DistribMulAction 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (σ : Fin N → (Fin N → Bool) → 𝕜) (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ)
    (ε : Fin N → Bool) :
    ∑ k ∈ Finset.range n, (fun m ε => if hm : m - 1 < N then σ ⟨m - 1, hm⟩ ε else 1) (k + 1) ε •
        (paleyWalsh ξ (k + 1) ε - paleyWalsh ξ k ε) =
      paleyWalsh (fun k ε => σ k ε • ξ k ε) n ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, paleyWalsh_succ ξ n ε, paleyWalsh_succ _ n ε,
      add_sub_cancel_left, umdd_shift_succ]
    congr 1
    split_ifs with hn
    · exact (smul_comm _ _ _).symm
    · exact smul_zero _

/-- The re-indexed signs `σ' (k + 1)` of a predictable family are `ℱ_k`-measurable. -/
private theorem umdd_stronglyMeasurable_shift {N : ℕ} {𝕜 : Type*} [TopologicalSpace 𝕜] [T2Space 𝕜]
    [One 𝕜] {σ : Fin N → (Fin N → Bool) → 𝕜} (hσ : IsPredictable σ) (k : ℕ) :
    StronglyMeasurable[filtration N k]
      ((fun m ε => if hm : m - 1 < N then σ ⟨m - 1, hm⟩ ε else 1) (k + 1)) := by
  rw [stronglyMeasurable_filtration_iff]
  intro ε ε' hεε'
  rw [umdd_shift_succ, umdd_shift_succ]
  split_ifs with hk
  · exact hσ ⟨k, hk⟩ ε ε' fun j hj => hεε' j hj
  · rfl

/-- Every `UMD_p` constant is a dyadic one: a Paley–Walsh martingale is a martingale on the
probability space `Fin N → Bool`, and its transform by predictable signs is a martingale
transform. -/
theorem umdd_isDyadicUMDBound_of_isUMDBound [CompleteSpace X] {p : ℝ} (hp : 0 < p) {β : ℝ≥0∞}
    (h : IsUMDBound X p β) : IsDyadicUMDBound X p β := by
  intro N ξ σ hξ hσ hσ1 n
  set σ' : ℕ → (Fin N → Bool) → ℝ :=
    fun m ε => if hm : m - 1 < N then σ ⟨m - 1, hm⟩ ε else 1 with hσ'
  have hσ'1 : ∀ m ε, σ' m ε = 1 ∨ σ' m ε = -1 := by
    intro m ε
    simp only [hσ']
    split_ifs
    · exact hσ1 _ ε
    · exact Or.inl rfl
  have hσ'm : ∀ k, StronglyMeasurable[filtration N k] (σ' (k + 1)) :=
    umdd_stronglyMeasurable_shift hσ
  have key := h (Fin N → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (filtration N) (fun k => paleyWalsh ξ k) σ' (martingale_paleyWalsh ξ hξ)
    (fun ω => paleyWalsh_zero ξ ω) hσ'1 hσ'm n
  simp only [hσ', umdd_sum_shift_smul_paleyWalsh] at key
  rwa [umdd_eLpNorm_norm_uniformOn _ hp, umdd_eLpNorm_norm_uniformOn _ hp] at key

/-- The dyadic constant is at most the full one: Paley–Walsh martingales are martingales on the
probability space `Fin N → Bool` (`SignCube.martingale_paleyWalsh`), whose `L^p` norms are the
cube averages (`SignCube.eLpNorm_uniformOn`). -/
theorem dyadicUMDConst_le_umdConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X p ≤ umdConst X p := by
  exact sInf_le_sInf fun _ hβ => umdd_isDyadicUMDBound_of_isUMDBound (by linarith) hβ

end Real

section Complex

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The dyadic complex `UMD_p` bound: predictable unimodular complex multipliers of Paley–Walsh
martingales. -/
def IsComplexDyadicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (c : Fin N → (Fin N → Bool) → ℂ),
    IsPredictable ξ → IsPredictable c → (∀ k ε, ‖c k ε‖ = 1) → ∀ n : ℕ,
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => c k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n))

/-- The dyadic complex `UMD_p` constant `UMD_{ℂ,p}^Δ (X)`. -/
noncomputable def complexDyadicUMDConst (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexDyadicUMDBound X p β}

variable {X}

theorem complexUMDConst_le_of_isComplexUMDBound [CompleteSpace X] {p : ℝ} {β : ℝ≥0∞}
    (h : IsComplexUMDBound X p β) : complexUMDConst X p ≤ β :=
  sInf_le h

/-- The cube instance for the complex constant: the martingale `Y_1 = ε_0 x` on the one-sign cube,
transformed by `c ≡ 1`, shows that every complex `UMD_p` constant of a nonzero space is at
least `1`. -/
private theorem umdd_one_le_of_isComplexUMDBound [CompleteSpace X] [Nontrivial X] {p : ℝ}
    (hp : 0 < p) {β : ℝ≥0∞} (h : IsComplexUMDBound X p β) : 1 ≤ β := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have key := h (Fin 1 → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (filtration 1) (fun k => paleyWalsh (fun _ _ => x) k) (fun _ _ => 1)
    (martingale_paleyWalsh _ (umdd_isPredictable_const x)) (fun ω => paleyWalsh_zero _ ω)
    (fun _ _ => norm_one) (fun _ => stronglyMeasurable_const) 1
  simp only [Finset.sum_range_one, one_smul, zero_add, paleyWalsh_zero, sub_zero] at key
  rw [eLpNorm_uniformOn _ hp,
    umdd_lpNorm_of_norm_eq (norm_nonneg x) (umdd_norm_paleyWalsh_const x) hp] at key
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by simpa using hx
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).mp (by simpa using key)

theorem isComplexUMDBound_complexUMDConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    IsComplexUMDBound X p (complexUMDConst X p) := by
  intro Ω mΩ μ _ ℱ Y c hY hY0 hc hcm n
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  refine umdd_le_sInf_mul (fun β hβ => hβ Ω mΩ μ ℱ Y c hY hY0 hc hcm n)
    (fun h0 => umdd_eLpNorm_transform_eq_zero hY hp0 h0 c) (fun _ hS => ?_)
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact (eLpNorm_eq_zero_iff hp0).mpr
      (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)
  · have : 1 ≤ complexUMDConst X p :=
      le_sInf fun _ hβ => umdd_one_le_of_isComplexUMDBound (by linarith) hβ
    exact absurd hS (zero_lt_one.trans_le this).ne'

/-- `UMD_{ℂ,p} (X) ≥ 1` on a nonzero space. -/
theorem one_le_complexUMDConst [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 1 < p) :
    1 ≤ complexUMDConst X p :=
  le_sInf fun _ hβ => umdd_one_le_of_isComplexUMDBound (by linarith) hβ

/-- A complex `UMD_p` constant of `Y` is one of every complex space linearly isometric to a subspace
of `Y`. -/
theorem IsComplexUMDBound.of_linearIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℂ] Y) {p : ℝ} {β : ℝ≥0∞}
    (h : IsComplexUMDBound Y p β) : IsComplexUMDBound X p β := by
  intro Ω mΩ μ _ ℱ Z c hZ hZ0 hc hcm n
  have hfZ : Martingale (fun m ω => f (Z m ω)) ℱ μ :=
    martingale_map_continuousLinearMap hZ (f.toContinuousLinearMap.restrictScalars ℝ)
  have key := h Ω mΩ μ ℱ (fun m ω => f (Z m ω)) c hfZ (fun ω => by simp [hZ0]) hc hcm n
  have hZm : ∀ k, StronglyMeasurable (Z k) := fun k => (hZ.stronglyAdapted k).mono (ℱ.le k)
  have hm : AEStronglyMeasurable
      (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Z (k + 1) ω - Z k ω)) μ :=
    (Finset.stronglyMeasurable_fun_sum _ fun k _ => ((hcm k).mono (ℱ.le k)).smul
      ((hZm (k + 1)).sub (hZm k))).aestronglyMeasurable
  have e1 : (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (f (Z (k + 1) ω) - f (Z k ω))) =
      fun ω => f (∑ k ∈ Finset.range n, c (k + 1) ω • (Z (k + 1) ω - Z k ω)) := by
    funext ω
    simp only [map_sum, map_smul, map_sub]
  have e2 : ∀ {g : Ω → X}, AEStronglyMeasurable g μ →
      eLpNorm (fun ω => f (g ω)) (ENNReal.ofReal p) μ = eLpNorm g (ENNReal.ofReal p) μ :=
    fun {g} hg => by
      rw [← eLpNorm_norm _ (f.continuous.comp_aestronglyMeasurable hg), ← eLpNorm_norm g hg]
      simp only [f.norm_map]
  rw [e1, e2 hm, e2 (hZm n).aestronglyMeasurable] at key
  exact key

theorem complexUMDConst_le_of_linearIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace X] [CompleteSpace Y] (f : X →ₗᵢ[ℂ] Y) (p : ℝ) :
    complexUMDConst X p ≤ complexUMDConst Y p :=
  sInf_le_sInf fun _ hβ => IsComplexUMDBound.of_linearIsometry f hβ

/-- Every complex `UMD_p` constant is a dyadic one: a Paley–Walsh martingale is a martingale on
the probability space `Fin N → Bool`, and its transform by predictable unimodular multipliers is
a martingale transform. -/
theorem umdd_isComplexDyadicUMDBound_of_isComplexUMDBound [CompleteSpace X] {p : ℝ} (hp : 0 < p)
    {β : ℝ≥0∞} (h : IsComplexUMDBound X p β) : IsComplexDyadicUMDBound X p β := by
  intro N ξ c hξ hc hc1 n
  set c' : ℕ → (Fin N → Bool) → ℂ :=
    fun m ε => if hm : m - 1 < N then c ⟨m - 1, hm⟩ ε else 1 with hc'
  have hc'1 : ∀ m ε, ‖c' m ε‖ = 1 := by
    intro m ε
    simp only [hc']
    split_ifs
    · exact hc1 _ ε
    · exact norm_one
  have key := h (Fin N → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (filtration N) (fun k => paleyWalsh ξ k) c' (martingale_paleyWalsh ξ hξ)
    (fun ω => paleyWalsh_zero ξ ω) hc'1 (umdd_stronglyMeasurable_shift hc) n
  simp only [hc', umdd_sum_shift_smul_paleyWalsh] at key
  rwa [eLpNorm_uniformOn _ hp, eLpNorm_uniformOn _ hp] at key

theorem complexDyadicUMDConst_le_complexUMDConst [CompleteSpace X] {p : ℝ} (hp : 1 < p) :
    complexDyadicUMDConst X p ≤ complexUMDConst X p := by
  exact sInf_le_sInf fun _ hβ => umdd_isComplexDyadicUMDBound_of_isComplexUMDBound (by linarith) hβ

end Complex

end BanachProbability
