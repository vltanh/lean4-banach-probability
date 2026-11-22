module

public import BanachProbability.UMD.Maurey.StepApprox
public import BanachProbability.ZigZag.Bellman

/-!
# Burkholder's characterisation of UMD by zig-zag concave functions

A Banach space `X` is `UMD_p`, `p ∈ (1, ∞)`, if and only if there are `β > 0` and a function
`U : X × X → ℝ` with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, and zig-zag concave:
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]` (`IsZigZagConcave`); then
`UMD_p (X) ≤ β`, and `UMD_p (X)` is the infimum of these `β`, attained if `X ≠ 0` (for `X = 0` every
`β > 0` is possible, and `UMD_p (X) = 0`). The theorem is D. L. Burkholder's (*A geometrical
characterization of Banach spaces in which martingale difference sequences are unconditional*, Ann.
Probab. 9 (1981), *Boundary value problems and sharp inequalities for martingale transforms*, Ann.
Probab. 12 (1984), and, with biconcave functions, *Martingales and Fourier analysis in Banach
spaces*, Lecture Notes in Math. 1206 (1986)); it is Theorem 4.5.6, p. 332, of Hytönen–van
Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016) (HNVW).

For a complex space and `ε` in the closed unit disc of `ℂ` (`IsComplexZigZagConcave`), the same
holds with the complex constant `UMD_{ℂ,p} (X)` (I. Yaroslavtsev, *Even Fourier multipliers and
martingale transforms in infinite dimensions*, Indag. Math. 29 (2018), Proposition 3.7). HNVW ask
concavity only for the signs `‖ε‖ = 1` (`IsSignZigZagConcave`, Definition 4.5.3) and do not ask
`U (0, 0) = 0`; the functions above satisfy more, and the bound for `UMD_p (X)` is proved from
HNVW's hypotheses (`umdConst_le_of_isSignZigZagConcave`). Yaroslavtsev asks concavity for all the
multipliers of a set, here the closed unit ball of `ℝ` or `ℂ` (`IsBallZigZagConcave`), without
`U (0, 0) = 0` (`umdConst_lt_top_iff_exists_isBallZigZagConcave`,
`complexUMDConst_lt_top_iff_exists_isBallZigZagConcave`).

The proof is HNVW's, p. 330–337, for `𝕜 = ℝ` and `ℂ` at once:

* (3)⇒(1), `U ⇒ UMD_p ≤ β`: `E F (f_n, g_n) ≤ E U (f_n, g_n) ≤ … ≤ E U (f_0, g_0) = U (0, 0) ≤ 0`,
  `F (x, y) = ‖y‖^p − β^p ‖x‖^p`, for a martingale `f` started at `0` on a finite probability space
  and its transform `g` (Lemma 4.5.5, `IsSignZigZagConcave.integral_transform_le`), then
  approximation by such martingales (Lemma 3.6.17, `isUMDBound_of_isFiniteUMDBound`). Without
  `U (0, 0) = 0` one first replaces `U` by its homogenisation (4.31). Two departures from the
  source: the signs are predictable instead of deterministic, which does not change the argument;
  and the martingales start at `0`, so that `U (0, 0) ≤ 0` is enough and the reduction (4.32) and
  (4.33), `U (ε_1 z, ε_2 z) ≤ 0`, which serve the martingales with `f_0 ≠ 0` of Lemma 4.2.8, are not
  needed.
* (2)⇒(3), dyadic `UMD_p ⇒ U`: for `β ≥ UMD_p^Δ (X)`, Burkholder's function
  `U (x, y) = sup E F (f_∞, g_∞)` over the Paley–Walsh martingales `f` started at `x` and their
  transforms `g` started at `y` by constants in the closed unit ball (`bellmanFunction`,
  `complexBellmanFunction`; `ZigZag/Bellman.lean`).
* (1)⇒(2) is trivial (`dyadicUMDConst_le_umdConst`).

The assertions (1) `UMD_p (X) < ∞`, (2) `UMD_p^Δ (X) < ∞` (on sign cubes) and (3) are stated here
for a fixed `p`. The final clause, that the least `β` is the UMD constant, is
`isLeast_umdConst_isZigZagConcave`, and `isLeast_umdConst_isSignZigZagConcave` in HNVW's form,
`isLeast_umdConst_isBallZigZagConcave` in Yaroslavtsev's; the complex versions are likewise. The
equality `UMD_p^Δ (X) = UMD_p (X)`, which this gives, is in `UMD/Maurey/Basic.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

/-- `U : X × X → ℝ` is zig-zag concave for the obstacle `‖y‖^p − β^p ‖x‖^p` (real scalars):
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]`, `U (0, 0) = 0`, and
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
def IsZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℝ), |ε| ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- The complex version: `ε` ranges over the closed unit disc. -/
def IsComplexZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℂ), ‖ε‖ ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- A zig-zag concave function is zig-zag concave for the signs `±1` (HNVW I, Definition 4.5.3). -/
theorem IsZigZagConcave.isSignZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p β : ℝ} {U : X → X → ℝ} (hU : IsZigZagConcave p β U) : IsSignZigZagConcave ℝ U :=
  fun x y ε hε => hU.1 x y ε (by rw [← Real.norm_eq_abs, hε])

/-- A complex zig-zag concave function is zig-zag concave for the complex signs (HNVW I,
Definition 4.5.3). -/
theorem IsComplexZigZagConcave.isSignZigZagConcave {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {p β : ℝ} {U : X → X → ℝ} (hU : IsComplexZigZagConcave p β U) :
    IsSignZigZagConcave ℂ U :=
  fun x y ε hε => hU.1 x y ε hε.le

section Scalars

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] {p β : ℝ} {u : X → X → ℝ}

omit [NormedSpace ℝ X] in
/-- The `L^p` norm on a finite probability space is `(E ‖h‖^p)^{1/p}`. -/
private theorem zzg_eLpNorm_eq {Ω : Type*} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (hp : 0 < p) (h : Ω → X) :
    eLpNorm (fun ω => ‖h ω‖) (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∫ ω, ‖h ω‖ ^ p ∂μ) ^ p⁻¹) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top
    MemLp.of_discrete]
  simp only [ENNReal.toReal_ofReal hp.le, norm_norm]

/-- **HNVW I, Theorem 4.5.6, (3)⇒(1)** (p. 333–334) on finite probability spaces: if `u` is zig-zag
concave for the signs of `𝕜`, `u ≥ F`, `F (x, y) = ‖y‖^p − β^p ‖x‖^p`, and `u (0, 0) ≤ 0`, then
`E F (f_n, g_n) ≤ E u (f_n, g_n) ≤ … ≤ E u (f_0, g_0) = u (0, 0) ≤ 0`, hence
`‖g_n‖_p ≤ β ‖f_n‖_p`, for a martingale `f` started at `0` and its transform `g` by predictable
signs. -/
private theorem zzg_eLpNorm_transform_le [CompleteSpace X] (hp : 0 < p) (hβ : 0 ≤ β)
    (hu : IsSignZigZagConcave 𝕜 u) (hu0 : u 0 0 ≤ 0)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) {Ω : Type*} [Finite Ω]
    {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} (hf : Martingale f ℱ μ)
    (hf0 : ∀ ω, f 0 ω = 0) (hφ1 : ∀ n ω, ‖φ n ω‖ = 1)
    (hφ : ∀ n, StronglyMeasurable[ℱ n] (φ (n + 1))) (n : ℕ) :
    eLpNorm (fun ω => ‖martingaleTransform φ f n ω‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal β * eLpNorm (fun ω => ‖f n ω‖) (ENNReal.ofReal p) μ := by
  have h1 : ∫ ω, (‖martingaleTransform φ f n ω‖ ^ p - β ^ p * ‖f n ω‖ ^ p) ∂μ ≤ 0 :=
    (integral_mono Integrable.of_finite Integrable.of_finite fun ω => hF _ _).trans
      ((hu.integral_transform_le hf hf0 hφ1 hφ n).trans hu0)
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul, sub_nonpos] at h1
  have hnn : ∀ h : Ω → X, 0 ≤ ∫ ω, ‖h ω‖ ^ p ∂μ := fun h => integral_nonneg fun ω => by positivity
  rw [zzg_eLpNorm_eq hp, zzg_eLpNorm_eq hp, ← ENNReal.ofReal_mul hβ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ ω, ‖martingaleTransform φ f n ω‖ ^ p ∂μ) ^ p⁻¹
      ≤ (β ^ p * ∫ ω, ‖f n ω‖ ^ p ∂μ) ^ p⁻¹ :=
        Real.rpow_le_rpow (hnn _) h1 (inv_nonneg.mpr hp.le)
    _ = β * (∫ ω, ‖f n ω‖ ^ p ∂μ) ^ p⁻¹ := by
        rw [Real.mul_rpow (by positivity) (hnn _), Real.rpow_rpow_inv hβ hp.ne']

/-- The reduction at the beginning of the proof of HNVW I, Theorem 4.5.6 (p. 332–333): if `u` is
zig-zag concave for the signs of `𝕜` and `u ≥ F`, the same holds for the homogenisation
`ũ = inf_{α ≠ 0} |α|^{−p} u (α ·, α ·)`, (4.31), and `ũ (0, 0) = 0`. -/
private theorem zzg_exists_homogeneous (hp : 0 < p) (hu : IsSignZigZagConcave 𝕜 u)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) :
    ∃ v : X → X → ℝ, IsSignZigZagConcave 𝕜 v ∧ v 0 0 ≤ 0 ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ v x y :=
  ⟨zigZagHomogenize 𝕜 p u, hu.zigZagHomogenize hF, (zigZagHomogenize_zero hp u).le,
    le_zigZagHomogenize hF⟩

end Scalars

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p β : ℝ}

section Bound

/-- **HNVW I, Theorem 4.5.6, (3)⇒(1)** (p. 333–334), real scalars, from HNVW's hypotheses: if `u` is
zig-zag concave for the signs `±1` and `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, (4.30), then `β` is a
`UMD_p` constant of `X`. By the homogenisation (4.31) one may assume `u (0, 0) = 0`; then
`E F (f_n, g_n) ≤ E u (f_n, g_n) ≤ … ≤ E u (f_0, g_0) = u (0, 0) = 0` on finite probability spaces
(Lemma 4.5.5), which suffices by approximation (HNVW I, Lemma 3.6.17). -/
theorem isUMDBound_of_isSignZigZagConcave [CompleteSpace X] (hp : 1 ≤ p) (hβ : 0 ≤ β)
    {u : X → X → ℝ} (hu : IsSignZigZagConcave ℝ u)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) : IsUMDBound X p (ENNReal.ofReal β) := by
  obtain ⟨v, hv, hv0, hFv⟩ := zzg_exists_homogeneous (by linarith) hu hF
  refine isUMDBound_of_isFiniteUMDBound hp fun Ω _ mΩ _ μ _ ℱ Y σ hY hY0 hσ hσm n => ?_
  exact zzg_eLpNorm_transform_le (by linarith) hβ hv hv0 hFv hY hY0
    (fun n ω => by rcases hσ n ω with h | h <;> simp [h]) hσm n

/-- **HNVW I, Theorem 4.5.6, (3)⇒(1)** (p. 333–334), real scalars, from HNVW's hypotheses:
`UMD_p (X) ≤ β` if `u` is zig-zag concave for the signs `±1` and `u ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem umdConst_le_of_isSignZigZagConcave [CompleteSpace X] (hp : 1 ≤ p) (hβ : 0 ≤ β)
    {u : X → X → ℝ} (hu : IsSignZigZagConcave ℝ u)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) : umdConst X p ≤ ENNReal.ofReal β :=
  umdConst_le_of_isUMDBound (isUMDBound_of_isSignZigZagConcave hp hβ hu hF)

/-- A zig-zag concave function bounds the UMD constant: `UMD_p (X) ≤ β` (Burkholder; HNVW I,
Theorem 4.5.6, (3)⇒(1), p. 333–334). -/
theorem umdConst_le_of_isZigZagConcave [CompleteSpace X] {p β : ℝ} (hp : 1 < p) (hβ : 0 < β)
    {U : X → X → ℝ} (hU : IsZigZagConcave p β U) : umdConst X p ≤ ENNReal.ofReal β :=
  umdConst_le_of_isSignZigZagConcave hp.le hβ.le hU.isSignZigZagConcave hU.2.2

end Bound

section Existence

variable (X) in
/-- Burkholder's function (HNVW I, p. 334), real scalars:
`U (x, y) = sup E [‖g_∞‖^p − β^p ‖f_∞‖^p]` over the Paley–Walsh martingales `f = x + Σ ε_k ξ_k` and
their transforms `g = y + Σ λ_k ε_k ξ_k` by constants `λ_k ∈ [−1, 1]`. HNVW take signs `λ_k = ±1`;
constants in `[−1, 1]` make `U` zig-zag concave for all `ε ∈ [−1, 1]`. -/
noncomputable def bellmanFunction (p β : ℝ) (x y : X) : ℝ :=
  sSup (bellmanValues ℝ p β x y)

/-- The predictable-sign dyadic bound includes the one for deterministic signs. -/
theorem IsDyadicUMDBound.isSignDyadicUMDBound (hβ : 0 ≤ β)
    (h : IsDyadicUMDBound X p (ENNReal.ofReal β)) : IsSignDyadicUMDBound ℝ X p β := by
  intro N ξ l hξ hl
  have key := h N ξ (fun k _ => l k) hξ (fun _ _ _ _ => rfl)
    (fun k _ => by simpa [abs_eq] using hl k) N
  rw [← ENNReal.ofReal_mul hβ] at key
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hβ (lpNorm_nonneg (fun x : X => norm_nonneg x) p _))).mp key

/-- **HNVW I, Theorem 4.5.6, (2)⇒(3)** (p. 334–337), real scalars: if `β` is a dyadic `UMD_p`
constant of `X` for deterministic signs, Burkholder's function `bellmanFunction X p β` is zig-zag
concave. -/
theorem IsSignDyadicUMDBound.isZigZagConcave_bellmanFunction (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hD : IsSignDyadicUMDBound ℝ X p β) : IsZigZagConcave p β (bellmanFunction X p β) :=
  ⟨fun x y _ hε => concaveOn_sSup_bellmanValues hp hβ hD x y hε,
    sSup_bellmanValues_zero hp hβ hD, le_sSup_bellmanValues hp hβ hD⟩

/-- **HNVW I, Theorem 4.5.6, (2)⇒(3)** (p. 334–337), real scalars: for `β ≥ UMD_p^Δ (X)`, in
particular for `β = UMD_p^Δ (X)` as in the book, Burkholder's function is zig-zag concave: it is
finite, `0` at the origin, at least `‖y‖^p − β^p ‖x‖^p` and concave along the zig-zag lines. -/
theorem isZigZagConcave_bellmanFunction {p β : ℝ} (hp : 1 < p) (hβ0 : 0 ≤ β)
    (hβ : dyadicUMDConst X p ≤ ENNReal.ofReal β) : IsZigZagConcave p β (bellmanFunction X p β) :=
  (((isDyadicUMDBound_dyadicUMDConst (by linarith)).mono hβ).isSignDyadicUMDBound
    hβ0).isZigZagConcave_bellmanFunction hp.le hβ0

end Existence

variable [CompleteSpace X]

/-- **Burkholder's characterisation of UMD** (HNVW I, Theorem 4.5.6, p. 332; Burkholder):
`UMD_p (X) < ∞` if and only if a zig-zag concave function exists for some `β > 0`. -/
theorem umdConst_lt_top_iff_exists_isZigZagConcave {p : ℝ} (hp : 1 < p) :
    umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U := by
  constructor
  · -- `β = max (1, UMD_p^Δ (X))` (`β = UMD_p^Δ (X)` if `X ≠ 0`)
    intro h
    have hD : dyadicUMDConst X p ≠ ⊤ := ((dyadicUMDConst_le_umdConst hp).trans_lt h).ne
    refine ⟨max 1 (dyadicUMDConst X p).toReal, lt_max_of_lt_left one_pos, bellmanFunction X p _,
      isZigZagConcave_bellmanFunction hp (by positivity) ?_⟩
    rw [ENNReal.ofReal_max, ENNReal.ofReal_toReal hD]
    exact le_max_right _ _
  · rintro ⟨β, hβ, U, hU⟩
    exact (umdConst_le_of_isZigZagConcave hp hβ hU).trans_lt ENNReal.ofReal_lt_top

/-- **HNVW I, Theorem 4.5.6, (1)⇔(3)** (p. 332), real scalars, for a fixed `p`: `UMD_p (X) < ∞` if
and only if there are `β ≥ 1` and a function `u`, zig-zag concave for the signs `±1`, with
`u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, (4.30). -/
theorem umdConst_lt_top_iff_exists_isSignZigZagConcave {p : ℝ} (hp : 1 < p) :
    umdConst X p < ⊤ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y := by
  refine ⟨fun h => ?_, fun ⟨β, hβ, u, hu, hF⟩ => (umdConst_le_of_isSignZigZagConcave hp.le
    (by linarith) hu hF).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨β, hβ, U, hU⟩ := (umdConst_lt_top_iff_exists_isZigZagConcave hp).1 h
  refine ⟨max 1 β, le_max_left _ _, U, hU.isSignZigZagConcave, fun x y => ?_⟩
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hβ.le (le_max_right _ _)
    (by linarith)) (Real.rpow_nonneg (norm_nonneg x) p)) _).trans (hU.2.2 x y)

omit [CompleteSpace X] in
/-- A zig-zag concave function is concave along the zig-zag lines for all `ε ∈ [−1, 1]`. -/
theorem IsZigZagConcave.isBallZigZagConcave {p β : ℝ} {U : X → X → ℝ}
    (hU : IsZigZagConcave p β U) : IsBallZigZagConcave ℝ U :=
  fun x y ε hε => hU.1 x y ε (by rwa [← Real.norm_eq_abs])

omit [CompleteSpace X] in
/-- A function concave along the zig-zag lines for all `ε ∈ [−1, 1]` is so for the signs `±1`. -/
theorem IsBallZigZagConcave.isSignZigZagConcave {u : X → X → ℝ} (hu : IsBallZigZagConcave ℝ u) :
    IsSignZigZagConcave ℝ u :=
  fun x y ε hε => hu x y ε hε.le

/-- Burkholder's characterisation with the closed unit ball of scalars, real case (Yaroslavtsev
2018, Proposition 3.7, `A = [−1, 1]`): `UMD_p (X) < ∞` if and only if there are `β > 0` and a
function `U`, concave along `z ↦ (x + z, y + ε z)` for all `ε ∈ [−1, 1]`, with
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem umdConst_lt_top_iff_exists_isBallZigZagConcave {p : ℝ} (hp : 1 < p) :
    umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℝ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y := by
  refine ⟨fun h => ?_, fun ⟨β, hβ, U, hU, hF⟩ => (umdConst_le_of_isSignZigZagConcave hp.le hβ.le
    hU.isSignZigZagConcave hF).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨β, hβ, U, hU⟩ := (umdConst_lt_top_iff_exists_isZigZagConcave hp).1 h
  exact ⟨β, hβ, U, hU.isBallZigZagConcave, hU.2.2⟩

/-- The final clause of **HNVW I, Theorem 4.5.6** (p. 332), for the zig-zag concave functions of
`IsZigZagConcave`: the infimum of the `β ≥ 0` for which a zig-zag concave function exists is
`UMD_p (X)`, and it is attained, by Burkholder's function with `β = UMD_p^Δ (X) = UMD_p (X)`. (HNVW
ask `β ≥ 1`, which excludes the space `0`, whose constant is `0` here; see
`isLeast_umdConst_isSignZigZagConcave`.) -/
theorem isLeast_umdConst_isZigZagConcave {p : ℝ} (hp : 1 < p) (h : umdConst X p < ⊤) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U} (umdConst X p).toReal := by
  refine ⟨⟨ENNReal.toReal_nonneg, bellmanFunction X p _,
    isZigZagConcave_bellmanFunction hp ENNReal.toReal_nonneg ?_⟩, ?_⟩
  · rw [ENNReal.ofReal_toReal h.ne]
    exact dyadicUMDConst_le_umdConst hp
  · rintro β ⟨hβ, U, hU⟩
    exact ENNReal.toReal_le_of_le_ofReal hβ
      (umdConst_le_of_isSignZigZagConcave hp.le hβ hU.isSignZigZagConcave hU.2.2)

/-- The best constant with the closed unit ball of scalars, real case (Yaroslavtsev 2018,
Proposition 3.7, `A = [−1, 1]`): the least `β ≥ 0` for which there is a function `U`, concave along
`z ↦ (x + z, y + ε z)` for all `ε ∈ [−1, 1]`, with `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, is
`UMD_p (X)`. -/
theorem isLeast_umdConst_isBallZigZagConcave {p : ℝ} (hp : 1 < p) (h : umdConst X p < ⊤) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℝ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y} (umdConst X p).toReal := by
  obtain ⟨hβ, U, hU⟩ := (isLeast_umdConst_isZigZagConcave hp h).1
  refine ⟨⟨hβ, U, hU.isBallZigZagConcave, hU.2.2⟩, ?_⟩
  rintro β ⟨hβ, u, hu, hF⟩
  exact ENNReal.toReal_le_of_le_ofReal hβ
    (umdConst_le_of_isSignZigZagConcave hp.le hβ hu.isSignZigZagConcave hF)

/-- The final clause of **HNVW I, Theorem 4.5.6** (p. 332), in HNVW's form, real scalars: for
`X ≠ 0`, the infimum of the `β ∈ [1, ∞)` for which there is a function `u`, zig-zag concave for the
signs `±1`, with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, (4.30), is `UMD_p (X)`, and it is attained. -/
theorem isLeast_umdConst_isSignZigZagConcave [Nontrivial X] {p : ℝ} (hp : 1 < p)
    (h : umdConst X p < ⊤) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (umdConst X p).toReal := by
  obtain ⟨-, U, hU⟩ := (isLeast_umdConst_isZigZagConcave hp h).1
  refine ⟨⟨?_, U, hU.isSignZigZagConcave, hU.2.2⟩, ?_⟩
  · simpa using ENNReal.toReal_mono h.ne (one_le_umdConst hp)
  · rintro β ⟨hβ, u, hu, hF⟩
    exact ENNReal.toReal_le_of_le_ofReal (by linarith)
      (umdConst_le_of_isSignZigZagConcave hp.le (by linarith) hu hF)

end Real

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {p β : ℝ}

/-- **HNVW I, Theorem 4.5.6, (3)⇒(1)** (p. 333–334), complex scalars, from HNVW's hypotheses: if `u`
is zig-zag concave for the complex signs and `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, then `β` is a complex
`UMD_p` constant of `X`; the proof is that of `isUMDBound_of_isSignZigZagConcave`. -/
theorem isComplexUMDBound_of_isSignZigZagConcave [CompleteSpace X] (hp : 1 ≤ p) (hβ : 0 ≤ β)
    {u : X → X → ℝ} (hu : IsSignZigZagConcave ℂ u)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) :
    IsComplexUMDBound X p (ENNReal.ofReal β) := by
  obtain ⟨v, hv, hv0, hFv⟩ := zzg_exists_homogeneous (by linarith) hu hF
  exact isComplexUMDBound_of_isFiniteComplexUMDBound hp
    fun Ω _ mΩ _ μ _ ℱ Y c hY hY0 hc hcm n =>
      zzg_eLpNorm_transform_le (by linarith) hβ hv hv0 hFv hY hY0 hc hcm n

/-- **HNVW I, Theorem 4.5.6, (3)⇒(1)** (p. 333–334), complex scalars, from HNVW's hypotheses:
`UMD_{ℂ,p} (X) ≤ β` if `u` is zig-zag concave for the complex signs and
`u ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem complexUMDConst_le_of_isSignZigZagConcave [CompleteSpace X] (hp : 1 ≤ p) (hβ : 0 ≤ β)
    {u : X → X → ℝ} (hu : IsSignZigZagConcave ℂ u)
    (hF : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) :
    complexUMDConst X p ≤ ENNReal.ofReal β :=
  complexUMDConst_le_of_isComplexUMDBound (isComplexUMDBound_of_isSignZigZagConcave hp hβ hu hF)

/-- A complex zig-zag concave function bounds the complex UMD constant:
`UMD_{ℂ,p} (X) ≤ β` (Yaroslavtsev 2018, Proposition 3.7; HNVW I, Theorem 4.5.6). -/
theorem complexUMDConst_le_of_isComplexZigZagConcave {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ}
    (hU : IsComplexZigZagConcave p β U) : complexUMDConst X p ≤ ENNReal.ofReal β :=
  complexUMDConst_le_of_isSignZigZagConcave hp.le hβ.le hU.isSignZigZagConcave hU.2.2

variable (X) in
/-- Burkholder's function (HNVW I, p. 334), complex scalars:
`U (x, y) = sup E [‖g_∞‖^p − β^p ‖f_∞‖^p]` over the Paley–Walsh martingales `f = x + Σ ε_k ξ_k` and
their transforms `g = y + Σ λ_k ε_k ξ_k` by constants `λ_k` in the closed unit disc of `ℂ` (HNVW
take `|λ_k| = 1`). -/
noncomputable def complexBellmanFunction (p β : ℝ) (x y : X) : ℝ :=
  sSup (bellmanValues ℂ p β x y)

/-- The bound for predictable complex signs includes the one for deterministic complex signs. -/
theorem IsComplexDyadicUMDBound.isSignDyadicUMDBound (hβ : 0 ≤ β)
    (h : IsComplexDyadicUMDBound X p (ENNReal.ofReal β)) : IsSignDyadicUMDBound ℂ X p β := by
  intro N ξ l hξ hl
  have key := h N ξ (fun k _ => l k) hξ (fun _ _ _ _ => rfl) (fun k _ => hl k) N
  rw [← ENNReal.ofReal_mul hβ] at key
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hβ (lpNorm_nonneg (fun x : X => norm_nonneg x) p _))).mp key

/-- **HNVW I, Theorem 4.5.6, (2)⇒(3)** (p. 334–337), complex scalars: if `β` is a dyadic `UMD_p`
constant of `X` for deterministic complex signs, Burkholder's function
`complexBellmanFunction X p β` is zig-zag concave. -/
theorem IsSignDyadicUMDBound.isComplexZigZagConcave_complexBellmanFunction (hp : 1 ≤ p)
    (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound ℂ X p β) :
    IsComplexZigZagConcave p β (complexBellmanFunction X p β) :=
  ⟨fun x y _ hε => concaveOn_sSup_bellmanValues hp hβ hD x y hε,
    sSup_bellmanValues_zero hp hβ hD, le_sSup_bellmanValues hp hβ hD⟩

/-- The infimum defining `UMD_{ℂ,p}^Δ (X)` is attained. -/
theorem isComplexDyadicUMDBound_complexDyadicUMDConst (hp : 0 < p) :
    IsComplexDyadicUMDBound X p (complexDyadicUMDConst X p) := by
  intro N ξ c hξ hc hc1 n
  refine umdd_le_sInf_mul (fun β hβ => hβ N ξ c hξ hc hc1 n) (fun h0 => ?_)
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

theorem IsComplexDyadicUMDBound.mono {β β' : ℝ≥0∞} (h : IsComplexDyadicUMDBound X p β)
    (hβ : β ≤ β') : IsComplexDyadicUMDBound X p β' := by
  intro N ξ c hξ hc hc1 n
  exact (h N ξ c hξ hc hc1 n).trans (by gcongr)

/-- **HNVW I, Theorem 4.5.6, (2)⇒(3)** (p. 334–337), complex scalars: for `β ≥ UMD_{ℂ,p}^Δ (X)`,
Burkholder's function is zig-zag concave for all `ε` in the closed unit disc. -/
theorem isComplexZigZagConcave_complexBellmanFunction {p β : ℝ} (hp : 1 < p) (hβ0 : 0 ≤ β)
    (hβ : complexDyadicUMDConst X p ≤ ENNReal.ofReal β) :
    IsComplexZigZagConcave p β (complexBellmanFunction X p β) :=
  (((isComplexDyadicUMDBound_complexDyadicUMDConst (by linarith)).mono hβ).isSignDyadicUMDBound
    hβ0).isComplexZigZagConcave_complexBellmanFunction hp.le hβ0

variable [CompleteSpace X]

/-- **Burkholder's characterisation of UMD**, complex scalars (HNVW I, Theorem 4.5.6, p. 332;
Yaroslavtsev 2018, Proposition 3.7): `UMD_{ℂ,p} (X) < ∞` if and only if a complex zig-zag concave
function exists for some `β > 0`. -/
theorem complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p < ⊤ ↔
      ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsComplexZigZagConcave p β U := by
  constructor
  · intro h
    have hD : complexDyadicUMDConst X p ≠ ⊤ :=
      ((complexDyadicUMDConst_le_complexUMDConst hp).trans_lt h).ne
    refine ⟨max 1 (complexDyadicUMDConst X p).toReal, lt_max_of_lt_left one_pos,
      complexBellmanFunction X p _,
      isComplexZigZagConcave_complexBellmanFunction hp (by positivity) ?_⟩
    rw [ENNReal.ofReal_max, ENNReal.ofReal_toReal hD]
    exact le_max_right _ _
  · rintro ⟨β, hβ, U, hU⟩
    exact (complexUMDConst_le_of_isComplexZigZagConcave hp hβ hU).trans_lt ENNReal.ofReal_lt_top

/-- **HNVW I, Theorem 4.5.6, (1)⇔(3)** (p. 332), complex scalars, for a fixed `p`:
`UMD_{ℂ,p} (X) < ∞` if and only if there are `β ≥ 1` and a function `u`, zig-zag concave for the
complex signs, with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, (4.30). -/
theorem complexUMDConst_lt_top_iff_exists_isSignZigZagConcave {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p < ⊤ ↔ ∃ β : ℝ, 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y := by
  refine ⟨fun h => ?_, fun ⟨β, hβ, u, hu, hF⟩ => (complexUMDConst_le_of_isSignZigZagConcave hp.le
    (by linarith) hu hF).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨β, hβ, U, hU⟩ := (complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave hp).1 h
  refine ⟨max 1 β, le_max_left _ _, U, hU.isSignZigZagConcave, fun x y => ?_⟩
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hβ.le (le_max_right _ _)
    (by linarith)) (Real.rpow_nonneg (norm_nonneg x) p)) _).trans (hU.2.2 x y)

omit [CompleteSpace X] in
/-- A complex zig-zag concave function is concave along the zig-zag lines for all `ε` in the closed
unit disc. -/
theorem IsComplexZigZagConcave.isBallZigZagConcave {p β : ℝ} {U : X → X → ℝ}
    (hU : IsComplexZigZagConcave p β U) : IsBallZigZagConcave ℂ U :=
  hU.1

omit [CompleteSpace X] in
/-- A function concave along the zig-zag lines for all `ε` in the closed unit disc is so for the
complex signs. -/
theorem IsBallZigZagConcave.isComplexSignZigZagConcave {u : X → X → ℝ}
    (hu : IsBallZigZagConcave ℂ u) : IsSignZigZagConcave ℂ u :=
  fun x y ε hε => hu x y ε hε.le

/-- Burkholder's characterisation with the closed unit disc of scalars (Yaroslavtsev 2018,
Proposition 3.7): `UMD_{ℂ,p} (X) < ∞` if and only if there are `β > 0` and a function `U`, concave
along `z ↦ (x + z, y + ε z)` for all `|ε| ≤ 1`, with `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
theorem complexUMDConst_lt_top_iff_exists_isBallZigZagConcave {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℂ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y := by
  refine ⟨fun h => ?_, fun ⟨β, hβ, U, hU, hF⟩ => (complexUMDConst_le_of_isSignZigZagConcave hp.le
    hβ.le hU.isComplexSignZigZagConcave hF).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨β, hβ, U, hU⟩ := (complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave hp).1 h
  exact ⟨β, hβ, U, hU.isBallZigZagConcave, hU.2.2⟩

/-- The final clause of **HNVW I, Theorem 4.5.6** (p. 332), complex scalars: the least `β ≥ 0` for
which a complex zig-zag concave function exists is `UMD_{ℂ,p} (X)`. -/
theorem isLeast_complexUMDConst_isComplexZigZagConcave {p : ℝ} (hp : 1 < p)
    (h : complexUMDConst X p < ⊤) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsComplexZigZagConcave p β U}
      (complexUMDConst X p).toReal := by
  refine ⟨⟨ENNReal.toReal_nonneg, complexBellmanFunction X p _,
    isComplexZigZagConcave_complexBellmanFunction hp ENNReal.toReal_nonneg ?_⟩, ?_⟩
  · rw [ENNReal.ofReal_toReal h.ne]
    exact complexDyadicUMDConst_le_complexUMDConst hp
  · rintro β ⟨hβ, U, hU⟩
    exact ENNReal.toReal_le_of_le_ofReal hβ
      (complexUMDConst_le_of_isSignZigZagConcave hp.le hβ hU.isSignZigZagConcave hU.2.2)

/-- The best constant with the closed unit disc of scalars (Yaroslavtsev 2018, Proposition 3.7): the
least `β ≥ 0` for which there is a function `U`, concave along `z ↦ (x + z, y + ε z)` for all
`|ε| ≤ 1`, with `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, is `UMD_{ℂ,p} (X)`. -/
theorem isLeast_complexUMDConst_isBallZigZagConcave {p : ℝ} (hp : 1 < p)
    (h : complexUMDConst X p < ⊤) :
    IsLeast {β : ℝ | 0 ≤ β ∧ ∃ U : X → X → ℝ, IsBallZigZagConcave ℂ U ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y} (complexUMDConst X p).toReal := by
  obtain ⟨hβ, U, hU⟩ := (isLeast_complexUMDConst_isComplexZigZagConcave hp h).1
  refine ⟨⟨hβ, U, hU.isBallZigZagConcave, hU.2.2⟩, ?_⟩
  rintro β ⟨hβ, u, hu, hF⟩
  exact ENNReal.toReal_le_of_le_ofReal hβ
    (complexUMDConst_le_of_isSignZigZagConcave hp.le hβ hu.isComplexSignZigZagConcave hF)

/-- The final clause of **HNVW I, Theorem 4.5.6** (p. 332), in HNVW's form, complex scalars: for
`X ≠ 0`, the infimum of the `β ∈ [1, ∞)` for which there is a function `u`, zig-zag concave for the
complex signs, with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, (4.30), is `UMD_{ℂ,p} (X)`, and it is
attained. -/
theorem isLeast_complexUMDConst_isSignZigZagConcave [Nontrivial X] {p : ℝ} (hp : 1 < p)
    (h : complexUMDConst X p < ⊤) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℂ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (complexUMDConst X p).toReal := by
  obtain ⟨-, U, hU⟩ := (isLeast_complexUMDConst_isComplexZigZagConcave hp h).1
  refine ⟨⟨?_, U, hU.isSignZigZagConcave, hU.2.2⟩, ?_⟩
  · simpa using ENNReal.toReal_mono h.ne (one_le_complexUMDConst hp)
  · rintro β ⟨hβ, u, hu, hF⟩
    exact ENNReal.toReal_le_of_le_ofReal (by linarith)
      (complexUMDConst_le_of_isSignZigZagConcave hp.le (by linarith) hu hF)

end Complex

end BanachProbability
