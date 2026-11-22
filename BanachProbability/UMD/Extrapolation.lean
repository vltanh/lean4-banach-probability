module

public import BanachProbability.UMD.Maurey.Basic
public import BanachProbability.Martingale.Doob

/-!
# Extrapolation of the UMD property

A Banach space that is `UMD_{p₀}` for one `p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`, and
`UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)` (Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Theorem 4.2.7).

The proof is Burkholder's good-λ method (D. L. Burkholder, *Distribution function inequalities
for martingales*, Ann. Probab. 1 (1973); *A geometrical characterization of Banach spaces in which
martingale difference sequences are unconditional*, Ann. Probab. 9 (1981); for dyadic martingales
Pisier, *Martingales in Banach spaces* (2016), the second proof of the extrapolation theorem),
run on Paley–Walsh martingales, then lifted by Maurey's theorem (`dyadicUMDConst_eq_umdConst`).

* `goodLambda`: for a Paley–Walsh martingale `f_k = Σ_{j<k} ε_j ξ_j`, its transform `g` by
  predictable signs, `β > 1`, `δ > 0` with `a = β − 1 − 2δ > 0` and `λ > 0`,
  `P (g*_n > βλ, f*_n ≤ δλ) ≤ (4 u δ / a)^p P (g*_n > λ)`, `u` a dyadic `UMD_p` constant. The
  stopping times `μ = inf {k : ‖g_k‖ > λ}`, `ν = inf {k : ‖g_k‖ > βλ}` and
  `ρ = inf {k : ‖f_k‖ > δλ or ‖ξ_k‖ > 2δλ}` (a stopping time because the jumps `‖ξ_k‖` are
  predictable), taken as `Nat.find`s, cut out the predictable family
  `h_k = 1_{μ ≤ k < ν ∧ ρ} ξ_k`. Its Paley–Walsh martingale at time `n` is `f_{n ∧ ν ∧ ρ} − f_μ`
  (or `0`), of norm at most `4δλ 1_{g*_n > λ}`, and its transform is `g_ν − g_μ`, of norm at
  least `aλ`, on `{g*_n > βλ, f*_n ≤ δλ}`; apply the `UMD_p` bound to `h` and Chebyshev.
* `isDyadicUMDBound_of_goodLambda`: the layer-cake formula on the cube (Mathlib's
  `lintegral_rpow_eq_lintegral_meas_lt_mul` for the uniform probability, applied to `g* / β`,
  `g*` and `f* / δ`, which performs the substitutions `λ ↦ βλ`, `λ ↦ λ / δ`), absorption (every
  quantity is finite on the cube) and Doob's inequality (`SignCube.lpNorm_runningMax_le`) give,
  for every `r ∈ (1, ∞)`, the dyadic `UMD_r` constant
  `r' (β / δ) (1 − β^r (4 u δ / a)^p)^{−1/r}` whenever `β^r (4 u δ / a)^p < 1`.
* With `δ = θ (β − 1) / (4u + 2θ)` (so that `4uδ / a = θ`) and `β`, `θ` chosen as functions of
  the exponents: `UMD_r^Δ ≤ 100 r* UMD_2^Δ` (the proof gives `76 r UMD_2^Δ` for `r ≥ 2`, with
  `β = 1 + 1/r`, `θ = 1/3`, and `48 r' UMD_2^Δ` for `r < 2`, with `β = 2`, `θ = 1/4`),
  `UMD_2^Δ ≤ 200 UMD_p^Δ` (the proof gives `180`, with `β = 3/2`, `θ = 2/9`), and finiteness for
  every pair of exponents.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

section Helpers

/-- Telescoping a stopped sum: `Σ_{i<n} 1_{i<e} (F_{i+1} − F_i) = F_{min (n, e)} − F_0`. -/
private theorem xtr_sum_range_ite_lt {E : Type*} [AddCommGroup E] (F : ℕ → E) (n e : ℕ) :
    ∑ i ∈ Finset.range n, (if i < e then F (i + 1) - F i else 0) = F (min n e) - F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs with h
    · rw [min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h)]
      abel
    · rw [min_eq_right (not_lt.mp h), min_eq_right (by omega), add_zero]

/-- The increments of `F` summed over the times `i < n` of an event which, for `i < n`, is the
interval `m ≤ i < e` (`m ≤ e ≤ n`): `F_e − F_m`. -/
private theorem xtr_sum_indicator_interval {Ω E : Type*} [AddCommGroup E] (F : ℕ → Ω → E)
    (A : ℕ → Set Ω) (ω : Ω) {n m e : ℕ} (hA : ∀ i < n, (ω ∈ A i ↔ m ≤ i ∧ i < e))
    (hme : m ≤ e) (hen : e ≤ n) :
    ∑ i ∈ Finset.range n, (A i).indicator (fun ω => F (i + 1) ω - F i ω) ω = F e ω - F m ω := by
  have key : ∀ i ∈ Finset.range n, (A i).indicator (fun ω => F (i + 1) ω - F i ω) ω =
      (if i < e then F (i + 1) ω - F i ω else 0) - (if i < m then F (i + 1) ω - F i ω else 0) := by
    intro i hi
    have hi' := hA i (Finset.mem_range.mp hi)
    by_cases hω : ω ∈ A i
    · rw [Set.indicator_of_mem hω, ite_eq_left (hi'.mp hω).2,
        ite_eq_right (not_lt.mpr (hi'.mp hω).1), sub_zero]
    · rw [Set.indicator_of_notMem hω]
      by_cases him : i < m
      · rw [ite_eq_left (lt_of_lt_of_le him hme), ite_eq_left him, sub_self]
      · have hie : ¬ i < e := fun h => hω (hi'.mpr ⟨not_lt.mp him, h⟩)
        rw [ite_eq_right hie, ite_eq_right him, sub_self]
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    xtr_sum_range_ite_lt (fun i => F i ω) n e, xtr_sum_range_ite_lt (fun i => F i ω) n m,
    min_eq_right hen, min_eq_right (hme.trans hen), sub_sub_sub_cancel_right]

/-- First hitting times, through `Nat.find`: for a property `P` that holds somewhere, with `m` the
first time of `P` and `e` the first time `< n` at which `Q` fails (`e = n` if there is none), the
times `i < n` at which `P` has happened and `Q` has always held form the interval `m ≤ i < e`. -/
private theorem xtr_exists_interval (P Q : ℕ → Prop) (hP : ∃ j, P j) (n : ℕ) :
    ∃ m e, P m ∧ (∀ j < m, ¬ P j) ∧ e ≤ n ∧ (∀ j < e, Q j) ∧ (e < n → ¬ Q e) ∧
      ∀ i < n, (((∃ j ≤ i, P j) ∧ ∀ j ≤ i, Q j) ↔ m ≤ i ∧ i < e) := by
  classical
  have hQ : ∃ j, n ≤ j ∨ ¬ Q j := ⟨n, Or.inl le_rfl⟩
  refine ⟨Nat.find hP, Nat.find hQ, Nat.find_spec hP, fun j hj => Nat.find_min hP hj,
    Nat.find_min' hQ (Or.inl le_rfl), fun j hj => ?_, fun he => ?_, fun i hi => ?_⟩
  · have := Nat.find_min hQ hj
    push Not at this
    exact this.2
  · exact (Nat.find_spec hQ).resolve_left (by omega)
  · rw [Nat.find_le_iff, Nat.lt_find_iff]
    refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => ?_
    constructor
    · rintro hq (h' | h')
      · omega
      · exact h' hq
    · intro h'
      by_contra hq
      exact h' (Or.inr hq)

variable {N : ℕ}

/-- A Paley–Walsh martingale of a family cut down to events `A k`: its value at time `n` is the
sum of the increments `M_{i+1} − M_i` of the uncut martingale over the times `i < n` with
`ε ∈ A i`. -/
private theorem xtr_paleyWalsh_indicator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ζ : Fin N → (Fin N → Bool) → E) (A : ℕ → Set (Fin N → Bool)) (n : ℕ) (ε : Fin N → Bool) :
    paleyWalsh (fun k => (A k.val).indicator (ζ k)) n ε =
      ∑ i ∈ Finset.range n,
        (A i).indicator (fun ε => paleyWalsh ζ (i + 1) ε - paleyWalsh ζ i ε) ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [paleyWalsh_succ, Finset.sum_range_succ, ih]
    congr 1
    by_cases hA : ε ∈ A n
    · simp only [Set.indicator_of_mem hA, paleyWalsh_succ ζ n, add_sub_cancel_left]
    · simp only [Set.indicator_of_notMem hA, smul_zero, dite_eq_ite, ite_self]

private theorem xtr_prob_nonneg (s : Set (Fin N → Bool)) : 0 ≤ prob s :=
  avg_nonneg fun ε => Set.indicator_nonneg (fun _ _ => zero_le_one) ε

private theorem xtr_prob_mono {s s' : Set (Fin N → Bool)} (h : s ⊆ s') : prob s ≤ prob s' :=
  avg_mono fun ε => Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) ε

/-- The union bound on the cube. -/
private theorem xtr_prob_le_add {s s₁ s₂ : Set (Fin N → Bool)} (h : s ⊆ s₁ ∪ s₂) :
    prob s ≤ prob s₁ + prob s₂ := by
  unfold prob
  rw [← avg_add]
  refine avg_mono fun ε => ?_
  have h1 : 0 ≤ s₁.indicator (1 : (Fin N → Bool) → ℝ) ε :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ε
  have h2 : 0 ≤ s₂.indicator (1 : (Fin N → Bool) → ℝ) ε :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ε
  by_cases hs : ε ∈ s
  · rw [Set.indicator_of_mem hs]
    rcases h hs with h' | h'
    · have := Set.indicator_of_mem h' (1 : (Fin N → Bool) → ℝ)
      simp only [Pi.one_apply] at this ⊢
      linarith
    · have := Set.indicator_of_mem h' (1 : (Fin N → Bool) → ℝ)
      simp only [Pi.one_apply] at this ⊢
      linarith
  · rw [Set.indicator_of_notMem hs]
    linarith

/-- On the cube with the uniform probability, `∫⁻ ofReal ∘ G = ofReal (avg G)` for `G ≥ 0`. -/
private theorem xtr_lintegral_uniformOn {G : (Fin N → Bool) → ℝ} (hG : ∀ ε, 0 ≤ G ε) :
    ∫⁻ ε, ENNReal.ofReal (G ε) ∂(ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (avg G) := by
  rw [MeasureTheory.lintegral_fintype]
  have hμ : ∀ ε : Fin N → Bool,
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool))) {ε} =
        ENNReal.ofReal (1 / 2 ^ N) := fun ε => by
    rw [← uniformOn_singleton ε, MeasureTheory.ofReal_measureReal]
  simp_rw [hμ, ← ENNReal.ofReal_mul (hG _)]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ε _ => mul_nonneg (hG ε) (by positivity), avg,
    ← Finset.sum_mul]
  congr 1
  ring

/-- The uniform probability of a set of sign vectors is `prob`. -/
private theorem xtr_uniformOn_apply (s : Set (Fin N → Bool)) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Bool)) s = ENNReal.ofReal (prob s) := by
  rw [← MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete, prob,
    ← xtr_lintegral_uniformOn (G := s.indicator 1) (Set.indicator_nonneg (fun _ _ => zero_le_one))]
  refine MeasureTheory.lintegral_congr fun ε => ?_
  by_cases h : ε ∈ s <;> simp [h]

/-- **The layer-cake formula on the cube**: for `Z ≥ 0` and `r > 0`,
`E Z^r = r ∫_0^∞ t^{r−1} P (Z > t) dt` (Mathlib's `lintegral_rpow_eq_lintegral_meas_lt_mul` for
the uniform probability). -/
private theorem xtr_layerCake {Z : (Fin N → Bool) → ℝ} (hZ : ∀ ε, 0 ≤ Z ε) {r : ℝ}
    (hr : 0 < r) :
    ENNReal.ofReal (avg fun ε => Z ε ^ r) = ENNReal.ofReal r *
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (prob {ε | t < Z ε}) * ENNReal.ofReal (t ^ (r - 1)) := by
  rw [← xtr_lintegral_uniformOn fun ε => Real.rpow_nonneg (hZ ε) r,
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul _ (Filter.Eventually.of_forall hZ)
      Measurable.of_discrete.aemeasurable hr]
  simp_rw [xtr_uniformOn_apply]

/-- The integrand of the layer-cake formula is measurable (`t ↦ P (Z > t)` is antitone). -/
private theorem xtr_measurable_integrand (Z : (Fin N → Bool) → ℝ) (r : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (prob {ε | t < Z ε}) * ENNReal.ofReal (t ^ (r - 1)) := by
  have hanti : Antitone fun t : ℝ => prob {ε | t < Z ε} := fun t t' htt' =>
    xtr_prob_mono fun ε hε => lt_of_le_of_lt htt' hε
  exact hanti.measurable.ennreal_ofReal.mul (measurable_id.pow_const _).ennreal_ofReal

end Helpers

section Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The event `{μ ≤ k < min (ν, ρ)}` of the good-λ argument for processes `f`, `g` and the levels
`t`, `β t`, `δ t`: some `‖g_j‖`, `j ≤ k`, exceeds `t` (`μ ≤ k`), and for every `j ≤ k`,
`‖g_j‖ ≤ β t` (`k < ν`), `‖f_j‖ ≤ δ t` and `‖f_{j+1} − f_j‖ ≤ 2 δ t` (`k < ρ`). -/
private def xtrEvent {Ω : Type*} (f g : ℕ → Ω → X) (β δ t : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∃ j ≤ k, t < ‖g j ω‖) ∧
    ∀ j ≤ k, ‖g j ω‖ ≤ β * t ∧ ‖f j ω‖ ≤ δ * t ∧ ‖f (j + 1) ω - f j ω‖ ≤ 2 * δ * t}

omit [NormedSpace ℝ X] in
/-- First fact of the good-λ argument: the cut process `Σ_{i<n} 1_{μ ≤ i < min (ν, ρ)} df_i` is
`f_e − f_μ`, `e = min (n, ν, ρ)`, with `‖f_μ‖ ≤ δ t` and
`‖f_e‖ ≤ ‖f_{e−1}‖ + ‖df_{e−1}‖ ≤ 3 δ t`; so its norm is at most `4 δ t`, and it vanishes unless
`μ < n`, which forces `g*_n > t`. -/
private theorem xtr_norm_cut_le {Ω : Type*} (f g : ℕ → Ω → X) {β δ t : ℝ} (hδt : 0 ≤ δ * t)
    (n : ℕ) (ω : Ω) :
    ‖∑ i ∈ Finset.range n,
        (xtrEvent f g β δ t i).indicator (fun ω => f (i + 1) ω - f i ω) ω‖ ≤ 4 * δ * t ∧
      (¬ t < runningMax (fun k ω => ‖g k ω‖) n ω →
        ∑ i ∈ Finset.range n,
          (xtrEvent f g β δ t i).indicator (fun ω => f (i + 1) ω - f i ω) ω = 0) := by
  by_cases hex : ∃ k < n, ω ∈ xtrEvent f g β δ t k
  · obtain ⟨k, hkn, hk⟩ := hex
    obtain ⟨j, hjk, hj⟩ := hk.1
    obtain ⟨m, e, -, -, hen, hQ, -, hS⟩ := xtr_exists_interval (fun j => t < ‖g j ω‖)
      (fun j => ‖g j ω‖ ≤ β * t ∧ ‖f j ω‖ ≤ δ * t ∧ ‖f (j + 1) ω - f j ω‖ ≤ 2 * δ * t)
      ⟨j, hj⟩ n
    have hS' : ∀ i < n, (ω ∈ xtrEvent f g β δ t i ↔ m ≤ i ∧ i < e) := hS
    have hmk := (hS' k hkn).mp hk
    rw [xtr_sum_indicator_interval f _ ω hS' (hmk.1.trans hmk.2.le) hen]
    refine ⟨?_, fun h => absurd (lt_of_lt_of_le hj
      (le_runningMax (fun k ω => ‖g k ω‖) (hjk.trans hkn.le) ω)) h⟩
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have h1 := (hQ m (by omega)).2.1
    have h2 := (hQ e' (by omega)).2
    calc ‖f (e' + 1) ω - f m ω‖ ≤ ‖f (e' + 1) ω‖ + ‖f m ω‖ := norm_sub_le _ _
      _ ≤ (‖f e' ω‖ + ‖f (e' + 1) ω - f e' ω‖) + ‖f m ω‖ := by
          gcongr
          exact norm_le_insert' _ _
      _ ≤ (δ * t + 2 * δ * t) + δ * t := by
          gcongr
          · exact h2.1
          · exact h2.2
      _ = 4 * δ * t := by ring
  · push Not at hex
    have h0 : ∑ i ∈ Finset.range n,
        (xtrEvent f g β δ t i).indicator (fun ω => f (i + 1) ω - f i ω) ω = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i (Finset.mem_range.mp hi)) _
    rw [h0, norm_zero]
    exact ⟨by linarith, fun _ => rfl⟩

omit [NormedSpace ℝ X] in
/-- Second fact of the good-λ argument: on `{g*_n > β t, f*_n ≤ δ t}`, `ρ ≥ n ≥ ν`, `μ ≥ 1` (as
`g_0 = 0`), `‖g_μ‖ ≤ ‖g_{μ−1}‖ + ‖dg_{μ−1}‖ ≤ t + 2 δ t < β t` (the jumps of `g` and `f` have the
same norm), so `μ < ν`, and the cut transform `Σ_{i<n} 1_{μ ≤ i < min (ν, ρ)} dg_i = g_ν − g_μ` has
norm at least `β t − (1 + 2 δ) t`. -/
private theorem xtr_le_norm_cut {Ω : Type*} (f g : ℕ → Ω → X) {β δ t : ℝ} (hβ : 1 < β)
    (ht : 0 < t) (hg0 : ∀ ω, g 0 ω = 0)
    (hjump : ∀ j ω, ‖g (j + 1) ω - g j ω‖ = ‖f (j + 1) ω - f j ω‖) (n : ℕ) (ω : Ω)
    (hgω : β * t < runningMax (fun k ω => ‖g k ω‖) n ω)
    (hfω : runningMax (fun k ω => ‖f k ω‖) n ω ≤ δ * t) :
    (β - 1 - 2 * δ) * t ≤
      ‖∑ i ∈ Finset.range n,
        (xtrEvent f g β δ t i).indicator (fun ω => g (i + 1) ω - g i ω) ω‖ := by
  have hF : ∀ j ≤ n, ‖f j ω‖ ≤ δ * t := fun j hj =>
    (le_runningMax (fun k ω => ‖f k ω‖) hj ω).trans hfω
  have hD : ∀ j < n, ‖f (j + 1) ω - f j ω‖ ≤ 2 * δ * t := fun j hj => by
    have := norm_sub_le (f (j + 1) ω) (f j ω)
    linarith [hF (j + 1) hj, hF j hj.le]
  obtain ⟨j₀, hj₀n, hj₀⟩ : ∃ j₀ ≤ n, β * t < ‖g j₀ ω‖ := by
    obtain ⟨j, hj, h⟩ := (Finset.lt_sup'_iff _).mp hgω
    exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), h⟩
  have htβ : t < β * t := by nlinarith
  obtain ⟨m, e, hPm, hPlt, hen, hQ, hQe, hS⟩ := xtr_exists_interval (fun j => t < ‖g j ω‖)
    (fun j => ‖g j ω‖ ≤ β * t ∧ ‖f j ω‖ ≤ δ * t ∧ ‖f (j + 1) ω - f j ω‖ ≤ 2 * δ * t)
    ⟨j₀, htβ.trans hj₀⟩ n
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : t < ‖g 0 ω‖ := hPm
    rw [hg0, norm_zero] at this
    linarith
  have hmj₀ : m ≤ j₀ := not_lt.mp fun h => hPlt j₀ h (htβ.trans hj₀)
  have hgm : ‖g m ω‖ ≤ t + 2 * δ * t := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : ‖g m' ω‖ ≤ t := not_lt.mp (hPlt m' (by omega))
    have h2 := hD m' (by omega)
    rw [← hjump] at h2
    linarith [norm_le_insert' (g (m' + 1) ω) (g m' ω)]
  have hge : β * t < ‖g e ω‖ := by
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hen with hlt | heq
    · exact hQe hlt ⟨hle, hF e hen, hD e hlt⟩
    · rcases lt_or_eq_of_le hj₀n with hj | hj
      · have := (hQ j₀ (by omega)).1
        linarith
      · rw [hj, ← heq] at hj₀
        linarith
  have hme : m ≤ e := not_lt.mp fun h => by
    have := not_lt.mp (hPlt e h)
    linarith
  have hS' : ∀ i < n, (ω ∈ xtrEvent f g β δ t i ↔ m ≤ i ∧ i < e) := hS
  rw [xtr_sum_indicator_interval g _ ω hS' hme hen]
  have := norm_sub_norm_le (g e ω) (g m ω)
  nlinarith

/-- The jumps of the transform have the norms of the jumps of the martingale (`|σ_k| = 1`). -/
private theorem xtr_norm_jump {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    {σ : Fin N → (Fin N → Bool) → ℝ} (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (j : ℕ)
    (ε : Fin N → Bool) :
    ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) (j + 1) ε -
        paleyWalsh (fun k ε => σ k ε • ξ k ε) j ε‖ =
      ‖paleyWalsh ξ (j + 1) ε - paleyWalsh ξ j ε‖ := by
  rw [paleyWalsh_succ, paleyWalsh_succ ξ, add_sub_cancel_left, add_sub_cancel_left]
  split_ifs with hj
  · rw [norm_smul, norm_smul, norm_smul]
    rcases hσ1 ⟨j, hj⟩ ε with h | h <;> simp [h]
  · rfl

/-- **Burkholder's good-λ inequality** for Paley–Walsh martingales: with `f = Σ ε_k ξ_k`,
`g = Σ σ_k ε_k ξ_k` and `u` a dyadic `UMD_p` constant,
`P (g*_n > β t, f*_n ≤ δ t) ≤ (4 u δ / (β − 1 − 2δ))^p P (g*_n > t)`. -/
theorem goodLambda {p u : ℝ} (hp : 0 < p) (hu0 : 0 ≤ u)
    (hu : IsDyadicUMDBound X p (ENNReal.ofReal u)) {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    {σ : Fin N → (Fin N → Bool) → ℝ} (hξ : IsPredictable ξ) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) {β δ t : ℝ} (hβ : 1 < β) (hδ : 0 < δ)
    (ha : 0 < β - 1 - 2 * δ) (ht : 0 < t) (n : ℕ) :
    prob {ε | β * t < runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) n ε ∧
        runningMax (fun k ε => ‖paleyWalsh ξ k ε‖) n ε ≤ δ * t} ≤
      (4 * u * δ / (β - 1 - 2 * δ)) ^ p *
        prob {ε | t < runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) n ε} := by
  classical
  set f : ℕ → (Fin N → Bool) → X := paleyWalsh ξ with hf
  set g : ℕ → (Fin N → Bool) → X := paleyWalsh (fun k ε => σ k ε • ξ k ε) with hg
  set A := xtrEvent f g β δ t with hA
  set a := β - 1 - 2 * δ with ha_def
  -- the cut family `h_k = 1_{μ ≤ k < min (ν, ρ)} ξ_k`: the event depends on `ε_j`, `j < k`, only
  set h : Fin N → (Fin N → Bool) → X := fun k => (A k.val).indicator (ξ k) with hh
  have hAp : ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) →
      (ε ∈ A k.val ↔ ε' ∈ A k.val) := by
    intro k ε ε' hεε'
    have hlt : ∀ j ≤ k.val, ∀ i : Fin N, i.val < j → ε i = ε' i := fun j hj i hi =>
      hεε' i (Fin.lt_def.mpr (lt_of_lt_of_le hi hj))
    have hfj : ∀ j ≤ k.val, f j ε = f j ε' := fun j hj =>
      hξ.isAdapted_paleyWalsh j ε ε' (hlt j hj)
    have hgj : ∀ j ≤ k.val, g j ε = g j ε' := fun j hj =>
      (hσ.smul hξ).isAdapted_paleyWalsh j ε ε' (hlt j hj)
    have hdj : ∀ j ≤ k.val, ‖f (j + 1) ε - f j ε‖ = ‖f (j + 1) ε' - f j ε'‖ := by
      intro j hj
      have hjN : j < N := lt_of_le_of_lt hj k.isLt
      have e1 := norm_paleyWalsh_succ_sub ξ ⟨j, hjN⟩ ε
      have e2 := norm_paleyWalsh_succ_sub ξ ⟨j, hjN⟩ ε'
      simp only at e1 e2
      rw [hf, e1, e2, hξ ⟨j, hjN⟩ ε ε' fun i hi => hlt j hj i (Fin.lt_def.mp hi)]
    simp only [hA, xtrEvent, Set.mem_ofPred_eq]
    exact and_congr (exists_congr fun j => and_congr_right fun hj => by rw [hgj j hj])
      (forall_congr' fun j => imp_congr_right fun hj => by rw [hgj j hj, hdj j hj, hfj j hj])
  have hhp : IsPredictable h := hξ.indicator hAp
  have hH : ∀ ε, paleyWalsh h n ε = ∑ i ∈ Finset.range n,
      (A i).indicator (fun ε => f (i + 1) ε - f i ε) ε := xtr_paleyWalsh_indicator ξ A n
  have hT : ∀ ε, paleyWalsh (fun k ε => σ k ε • h k ε) n ε = ∑ i ∈ Finset.range n,
      (A i).indicator (fun ε => g (i + 1) ε - g i ε) ε := by
    intro ε
    have e : (fun k ε => σ k ε • h k ε) =
        fun k => (A k.val).indicator (fun ε => σ k ε • ξ k ε) := by
      funext k ε
      by_cases hk : ε ∈ A k.val
      · simp only [hh, Set.indicator_of_mem hk]
      · simp only [hh, Set.indicator_of_notMem hk, smul_zero]
    rw [e]
    exact xtr_paleyWalsh_indicator _ A n ε
  -- the dyadic `UMD_p` bound applied to `h`, raised to the power `p`
  have hUMD := hu N h σ hhp hσ hσ1 n
  rw [← ENNReal.ofReal_mul hu0, ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hu0 (lpNorm_nonneg (fun x => norm_nonneg x) p _))] at hUMD
  have hpow : ∀ Y : (Fin N → Bool) → X,
      SignCube.lpNorm (fun x => ‖x‖) p Y ^ p = avg fun ε => ‖Y ε‖ ^ p := by
    intro Y
    rw [SignCube.lpNorm, ← Real.rpow_mul (avg_nonneg fun ε => Real.rpow_nonneg (norm_nonneg _) _),
      one_div_mul_cancel hp.ne', Real.rpow_one]
  have hTH : (avg fun ε => ‖paleyWalsh (fun k ε => σ k ε • h k ε) n ε‖ ^ p) ≤
      u ^ p * avg fun ε => ‖paleyWalsh h n ε‖ ^ p := by
    rw [← hpow, ← hpow, ← Real.mul_rpow hu0 (lpNorm_nonneg (fun x => norm_nonneg x) p _)]
    exact Real.rpow_le_rpow (lpNorm_nonneg (fun x => norm_nonneg x) p _) hUMD hp.le
  set E := {ε | β * t < runningMax (fun k ε => ‖g k ε‖) n ε ∧
    runningMax (fun k ε => ‖f k ε‖) n ε ≤ δ * t} with hE
  set B := {ε | t < runningMax (fun k ε => ‖g k ε‖) n ε} with hB
  -- Chebyshev: `‖T h‖ ≥ a t` on `E`
  have hcheb : (a * t) ^ p * prob E ≤
      avg fun ε => ‖paleyWalsh (fun k ε => σ k ε • h k ε) n ε‖ ^ p := by
    rw [prob, ← avg_const_mul]
    refine avg_mono fun ε => ?_
    by_cases hε : ε ∈ E
    · rw [Set.indicator_of_mem hε, Pi.one_apply, mul_one, hT ε]
      exact Real.rpow_le_rpow (by positivity) (xtr_le_norm_cut f g hβ ht
        (fun ε => paleyWalsh_zero _ ε) (xtr_norm_jump hσ1) n ε hε.1 hε.2) hp.le
    · rw [Set.indicator_of_notMem hε, mul_zero]
      exact Real.rpow_nonneg (norm_nonneg _) _
  -- `‖h‖ ≤ 4 δ t 1_B`
  have hH4 : (avg fun ε => ‖paleyWalsh h n ε‖ ^ p) ≤ (4 * δ * t) ^ p * prob B := by
    rw [prob, ← avg_const_mul]
    refine avg_mono fun ε => ?_
    obtain ⟨h1, h2⟩ := xtr_norm_cut_le f g (β := β) (δ := δ) (t := t) (by positivity) n ε
    rw [hH ε]
    by_cases hε : ε ∈ B
    · rw [Set.indicator_of_mem hε, Pi.one_apply, mul_one]
      exact Real.rpow_le_rpow (norm_nonneg _) h1 hp.le
    · rw [Set.indicator_of_notMem hε, mul_zero, h2 hε, norm_zero, Real.zero_rpow hp.ne']
  have hat : 0 < a * t := mul_pos ha ht
  have hconst : u ^ p * (4 * δ * t) ^ p = (a * t) ^ p * (4 * u * δ / a) ^ p := by
    rw [← Real.mul_rpow hu0 (by positivity), ← Real.mul_rpow hat.le (by positivity)]
    congr 1
    field_simp
  have hcomb : (a * t) ^ p * prob E ≤ (a * t) ^ p * ((4 * u * δ / a) ^ p * prob B) := by
    calc (a * t) ^ p * prob E ≤ u ^ p * ((4 * δ * t) ^ p * prob B) :=
          hcheb.trans (hTH.trans (mul_le_mul_of_nonneg_left hH4 (Real.rpow_nonneg hu0 _)))
      _ = (a * t) ^ p * ((4 * u * δ / a) ^ p * prob B) := by
          rw [← mul_assoc, hconst, mul_assoc]
  exact le_of_mul_le_mul_left hcomb (Real.rpow_pos_of_pos hat p)

/-- **Extrapolation by the good-λ inequality**: a dyadic `UMD_p` constant `u` gives, for every
`r ∈ (1, ∞)` and every `β > 1`, `δ > 0` with `a = β − 1 − 2δ > 0` and
`β^r (4 u δ / a)^p < 1`, the dyadic `UMD_r` constant
`(r / (r − 1)) (β / δ) (1 − β^r (4 u δ / a)^p)^{−1/r}`. -/
theorem isDyadicUMDBound_of_goodLambda {p r u β δ : ℝ} (hp : 0 < p) (hr : 1 < r) (hu0 : 0 ≤ u)
    (hu : IsDyadicUMDBound X p (ENNReal.ofReal u)) (hβ : 1 < β) (hδ : 0 < δ)
    (ha : 0 < β - 1 - 2 * δ) (hc : β ^ r * (4 * u * δ / (β - 1 - 2 * δ)) ^ p < 1) :
    IsDyadicUMDBound X r (ENNReal.ofReal (r / (r - 1) * (β / δ) *
      (1 - β ^ r * (4 * u * δ / (β - 1 - 2 * δ)) ^ p) ^ (-(1 / r)))) := by
  intro N ξ σ hξ hσ hσ1 n
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hβ0 : 0 < β := by linarith
  set a := β - 1 - 2 * δ with ha_def
  set c' := (4 * u * δ / a) ^ p with hc'
  have hc'0 : 0 ≤ c' := Real.rpow_nonneg (by positivity) _
  set c := β ^ r * c' with hc_def
  set Zg := runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) n with hZg
  set Zf := runningMax (fun k ε => ‖paleyWalsh ξ k ε‖) n with hZf
  have hZg0 : ∀ ε, 0 ≤ Zg ε := fun ε => (norm_nonneg _).trans
    (le_runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) (Nat.zero_le n) ε)
  have hZf0 : ∀ ε, 0 ≤ Zf ε := fun ε => (norm_nonneg _).trans
    (le_runningMax (fun k ε => ‖paleyWalsh ξ k ε‖) (Nat.zero_le n) ε)
  -- the good-λ inequality and the union bound:
  -- `P (g* > β t) ≤ c' P (g* > t) + P (f* > δ t)`
  have hGL : ∀ t, 0 < t →
      prob {ε | β * t < Zg ε} ≤ c' * prob {ε | t < Zg ε} + prob {ε | δ * t < Zf ε} := by
    intro t ht
    refine (xtr_prob_le_add (s₁ := {ε | β * t < Zg ε ∧ Zf ε ≤ δ * t})
      (s₂ := {ε | δ * t < Zf ε}) fun ε hε => ?_).trans
      (add_le_add (goodLambda hp hu0 hu hξ hσ hσ1 hβ hδ ha ht n) le_rfl)
    by_cases h' : Zf ε ≤ δ * t
    · exact Or.inl ⟨hε, h'⟩
    · exact Or.inr (not_le.mp h')
  -- integrate against `r t^{r−1} dt` (layer cake), after the substitutions `t ↦ β t`, `t ↦ t / δ`,
  -- done as `E (Z / b)^r = b^{−r} E Z^r`
  have hdiv : ∀ (Z : (Fin N → Bool) → ℝ) (b : ℝ), 0 < b → (∀ ε, 0 ≤ Z ε) →
      avg (fun ε => (Z ε / b) ^ r) = avg (fun ε => Z ε ^ r) / b ^ r := by
    intro Z b hb hZ
    simp only [Real.div_rpow (hZ _) hb.le, avg]
    rw [← Finset.sum_div, div_right_comm]
  have hset : ∀ (Z : (Fin N → Bool) → ℝ) (b : ℝ), 0 < b → ∀ t : ℝ,
      {ε | t < Z ε / b} = {ε | b * t < Z ε} := by
    intro Z b hb t
    ext ε
    simp only [Set.mem_ofPred_eq, lt_div_iff₀ hb, mul_comm]
  have hkey : ENNReal.ofReal (avg fun ε => (Zg ε / β) ^ r) ≤
      ENNReal.ofReal c' * ENNReal.ofReal (avg fun ε => Zg ε ^ r) +
        ENNReal.ofReal (avg fun ε => (Zf ε / δ) ^ r) := by
    rw [xtr_layerCake (fun ε => div_nonneg (hZg0 ε) hβ0.le) hr0, xtr_layerCake hZg0 hr0,
      xtr_layerCake (fun ε => div_nonneg (hZf0 ε) hδ.le) hr0, mul_left_comm, ← mul_add,
      ← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal c') _ ENNReal.ofReal_ne_top,
      ← MeasureTheory.lintegral_add_left ((xtr_measurable_integrand Zg r).const_mul _)]
    gcongr ENNReal.ofReal r * ?_
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    simp only [hset Zg β hβ0, hset Zf δ hδ]
    rw [← mul_assoc, ← add_mul]
    gcongr
    rw [← ENNReal.ofReal_mul hc'0,
      ← ENNReal.ofReal_add (mul_nonneg hc'0 (xtr_prob_nonneg _)) (xtr_prob_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hGL t ht)
  set G := avg fun ε => Zg ε ^ r with hG
  set F := avg fun ε => Zf ε ^ r with hF
  have hG0 : 0 ≤ G := avg_nonneg fun ε => Real.rpow_nonneg (hZg0 ε) r
  have hF0 : 0 ≤ F := avg_nonneg fun ε => Real.rpow_nonneg (hZf0 ε) r
  have hβr : 0 < β ^ r := Real.rpow_pos_of_pos hβ0 r
  have hδr : 0 < δ ^ r := Real.rpow_pos_of_pos hδ r
  rw [hdiv Zg β hβ0 hZg0, hdiv Zf δ hδ hZf0, ← ENNReal.ofReal_mul hc'0,
    ← ENNReal.ofReal_add (mul_nonneg hc'0 hG0) (div_nonneg hF0 hδr.le),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hc'0 hG0) (div_nonneg hF0 hδr.le)),
    div_le_iff₀ hβr] at hkey
  -- absorb: `(1 − c) E (g*)^r ≤ (β / δ)^r E (f*)^r`, everything being finite on the cube
  have h1c : 0 < 1 - c := by linarith
  have hGle : G * (1 - c) ≤ (β / δ) ^ r * F := by
    rw [Real.div_rpow hβ0.le hδ.le]
    have e : (c' * G + F / δ ^ r) * β ^ r = c * G + β ^ r / δ ^ r * F := by
      rw [hc_def]
      field_simp
    rw [e] at hkey
    nlinarith
  have hnormZ : ∀ Z : (Fin N → Bool) → ℝ, (∀ ε, 0 ≤ Z ε) →
      SignCube.lpNorm (fun t : ℝ => ‖t‖) r Z = (avg fun ε => Z ε ^ r) ^ (1 / r) := by
    intro Z hZ
    simp only [SignCube.lpNorm, Real.norm_of_nonneg (hZ _)]
  have hmain : G ^ (1 / r) ≤ β / δ * (1 - c) ^ (-(1 / r)) * F ^ (1 / r) := by
    have hG' : G ≤ (β / δ) ^ r * F * (1 - c)⁻¹ := by
      rw [le_mul_inv_iff₀ h1c]
      exact hGle
    calc G ^ (1 / r) ≤ ((β / δ) ^ r * F * (1 - c)⁻¹) ^ (1 / r) :=
          Real.rpow_le_rpow hG0 hG' (by positivity)
      _ = β / δ * (1 - c) ^ (-(1 / r)) * F ^ (1 / r) := by
          rw [Real.mul_rpow (mul_nonneg (by positivity) hF0) (inv_nonneg.mpr h1c.le),
            Real.mul_rpow (by positivity) hF0, one_div, Real.rpow_rpow_inv (by positivity) hr0.ne',
            Real.inv_rpow h1c.le, Real.rpow_neg h1c.le]
          ring
  -- `‖g_n‖_r ≤ ‖g*_n‖_r` and Doob's inequality `‖f*_n‖_r ≤ r' ‖f_n‖_r`
  have hgn : SignCube.lpNorm (fun x => ‖x‖) r (paleyWalsh (fun k ε => σ k ε • ξ k ε) n) ≤
      SignCube.lpNorm (fun t : ℝ => ‖t‖) r Zg := by
    rw [hnormZ Zg hZg0]
    exact Real.rpow_le_rpow (avg_nonneg fun ε => Real.rpow_nonneg (norm_nonneg _) _)
      (avg_mono fun ε => Real.rpow_le_rpow (norm_nonneg _)
        (le_runningMax (fun k ε => ‖paleyWalsh (fun k ε => σ k ε • ξ k ε) k ε‖) le_rfl ε) hr0.le)
      (by positivity)
  have hdoob := SignCube.lpNorm_runningMax_le hξ hr n
  have hfin : SignCube.lpNorm (fun x => ‖x‖) r (paleyWalsh (fun k ε => σ k ε • ξ k ε) n) ≤
      r / (r - 1) * (β / δ) * (1 - c) ^ (-(1 / r)) *
        SignCube.lpNorm (fun x => ‖x‖) r (paleyWalsh ξ n) := by
    have hK : 0 ≤ β / δ * (1 - c) ^ (-(1 / r)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg h1c.le _)
    calc SignCube.lpNorm (fun x => ‖x‖) r (paleyWalsh (fun k ε => σ k ε • ξ k ε) n)
        ≤ SignCube.lpNorm (fun t : ℝ => ‖t‖) r Zg := hgn
      _ = G ^ (1 / r) := hnormZ Zg hZg0
      _ ≤ β / δ * (1 - c) ^ (-(1 / r)) * F ^ (1 / r) := hmain
      _ = β / δ * (1 - c) ^ (-(1 / r)) * SignCube.lpNorm (fun t : ℝ => ‖t‖) r Zf := by
          rw [hnormZ Zf hZf0]
      _ ≤ β / δ * (1 - c) ^ (-(1 / r)) *
          (r / (r - 1) * SignCube.lpNorm (fun x => ‖x‖) r (paleyWalsh ξ n)) :=
          mul_le_mul_of_nonneg_left hdoob hK
      _ = _ := by ring
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.rpow_nonneg h1c.le _))]
  exact ENNReal.ofReal_le_ofReal hfin

/-- The good-λ extrapolation with `δ = θ (β − 1) / (4 u + 2 θ)`, for which
`4 u δ / (β − 1 − 2 δ) = θ` and `β / δ = β (4 u + 2 θ) / (θ (β − 1))`. -/
private theorem xtr_isDyadicUMDBound_theta {p r u β θ : ℝ} (hp : 0 < p) (hr : 1 < r)
    (hu1 : 1 ≤ u) (hu : IsDyadicUMDBound X p (ENNReal.ofReal u)) (hβ : 1 < β) (hθ : 0 < θ)
    (hc : β ^ r * θ ^ p < 1) :
    IsDyadicUMDBound X r (ENNReal.ofReal (r / (r - 1) * (β * (4 * u + 2 * θ) / (θ * (β - 1))) *
      (1 - β ^ r * θ ^ p) ^ (-(1 / r)))) := by
  have hβ1 : 0 < β - 1 := by linarith
  have hD : 0 < 4 * u + 2 * θ := by linarith
  have hD' : 4 * u + 2 * θ ≠ 0 := hD.ne'
  have hθ' : θ ≠ 0 := hθ.ne'
  have hβ1' : β - 1 ≠ 0 := hβ1.ne'
  have hu' : u ≠ 0 := by linarith
  set δ := θ * (β - 1) / (4 * u + 2 * θ) with hδ_def
  have hδ : 0 < δ := div_pos (mul_pos hθ hβ1) hD
  have ha : β - 1 - 2 * δ = 4 * u * (β - 1) / (4 * u + 2 * θ) := by
    rw [hδ_def]
    field_simp
    ring
  have ha0 : 0 < β - 1 - 2 * δ := by
    rw [ha]
    exact div_pos (mul_pos (by linarith) hβ1) hD
  have hθδ : 4 * u * δ / (β - 1 - 2 * δ) = θ := by
    rw [ha, hδ_def]
    field_simp
  have hβδ : β / δ = β * (4 * u + 2 * θ) / (θ * (β - 1)) := by
    rw [hδ_def]
    field_simp
  have key := isDyadicUMDBound_of_goodLambda hp hr (by linarith) hu hβ hδ ha0 (by rwa [hθδ])
  rwa [hθδ, hβδ] at key

/-- On the zero space every constant is a dyadic `UMD_p` constant. -/
private theorem xtr_dyadicUMDConst_eq_zero [Subsingleton X] {p : ℝ} (hp : 0 < p) :
    dyadicUMDConst X p = 0 := by
  refine le_antisymm (dyadicUMDConst_le_of_isDyadicUMDBound fun N ξ σ _ _ _ n => ?_) zero_le
  rw [(umdd_lpNorm_eq_zero_iff hp).mpr fun ε => Subsingleton.elim _ _, ENNReal.ofReal_zero]
  exact zero_le

/-- A finite dyadic `UMD_s` constant of a nonzero space is a real number `u ≥ 1` that is itself
a dyadic `UMD_s` constant. -/
private theorem xtr_exists_finite [Nontrivial X] {s : ℝ} (hs : 0 < s)
    (ht : dyadicUMDConst X s ≠ ⊤) :
    1 ≤ (dyadicUMDConst X s).toReal ∧
      IsDyadicUMDBound X s (ENNReal.ofReal (dyadicUMDConst X s).toReal) := by
  refine ⟨?_, ?_⟩
  · simpa using ENNReal.toReal_mono ht (one_le_dyadicUMDConst hs)
  · rw [ENNReal.ofReal_toReal ht]
    exact isDyadicUMDBound_dyadicUMDConst hs

/-- From constants to best constants: if every real dyadic `UMD_s` constant `u ≥ 1` gives a dyadic
`UMD_q` constant at most `C u`, then `UMD_q^Δ ≤ C UMD_s^Δ` (on the zero space both sides vanish,
and the right side is `∞` when `UMD_s^Δ` is). -/
private theorem xtr_dyadicUMDConst_le {q s C : ℝ} (hq : 0 < q) (hs : 0 < s) (hC : 0 < C)
    (h : ∀ u : ℝ, 1 ≤ u → IsDyadicUMDBound X s (ENNReal.ofReal u) →
      ∃ K ≤ C * u, IsDyadicUMDBound X q (ENNReal.ofReal K)) :
    dyadicUMDConst X q ≤ ENNReal.ofReal C * dyadicUMDConst X s := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · rw [xtr_dyadicUMDConst_eq_zero hq]
    exact zero_le
  by_cases ht : dyadicUMDConst X s = ⊤
  · rw [ht, ENNReal.mul_top (by simpa using hC)]
    exact le_top
  obtain ⟨hu1, hu⟩ := xtr_exists_finite hs ht
  obtain ⟨K, hK, hKb⟩ := h _ hu1 hu
  calc dyadicUMDConst X q ≤ ENNReal.ofReal K := dyadicUMDConst_le_of_isDyadicUMDBound hKb
    _ ≤ ENNReal.ofReal (C * (dyadicUMDConst X s).toReal) := ENNReal.ofReal_le_ofReal hK
    _ = ENNReal.ofReal C * dyadicUMDConst X s := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal ht]

/-- `y^{−1/r} ≤ y^{−1}` for `0 < y ≤ 1` and `r ≥ 1`. -/
private theorem xtr_rpow_neg_le_inv {y r : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hr : 1 ≤ r) :
    y ^ (-(1 / r)) ≤ y⁻¹ := by
  rw [← Real.rpow_neg_one]
  refine Real.rpow_le_rpow_of_exponent_ge hy0 hy1 ?_
  rw [neg_le_neg_iff, div_le_one (by linarith)]
  exact hr

/-- `(1 + 1 / p)^p ≤ e ≤ 4` (`1 + x ≤ eˣ`, and `e^{1/2} ≤ 1 / (1 − 1/2)`). -/
private theorem xtr_one_add_inv_rpow_le {p : ℝ} (hp : 0 < p) : (1 + 1 / p) ^ p ≤ 4 := by
  have h1 : 1 + 1 / p ≤ Real.exp (1 / p) := by linarith [Real.add_one_le_exp (1 / p)]
  have h2 : Real.exp (1 / 2) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)).trans
      (by norm_num)
  calc (1 + 1 / p) ^ p ≤ Real.exp (1 / p) ^ p := Real.rpow_le_rpow (by positivity) h1 hp.le
    _ = Real.exp (1 / 2) * Real.exp (1 / 2) := by
        rw [← Real.exp_mul, ← Real.exp_add, one_div_mul_cancel hp.ne']
        norm_num
    _ ≤ 2 * 2 := by gcongr
    _ = 4 := by norm_num

/-- Extrapolation of the dyadic UMD property: finiteness for one exponent gives it for all. -/
theorem dyadicUMDConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀)
    (h : dyadicUMDConst X p₀ < ⊤) (hp : 1 < p) : dyadicUMDConst X p < ⊤ := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · rw [xtr_dyadicUMDConst_eq_zero (by linarith)]
    exact ENNReal.zero_lt_top
  obtain ⟨hu1, hu⟩ := xtr_exists_finite (X := X) (by linarith : (0 : ℝ) < p₀) h.ne
  -- `β = 2` and `θ = (2^{p+1})^{−1/p₀}`, so that `β^p θ^{p₀} = 1/2`
  set x : ℝ := (2 ^ p * 2)⁻¹ with hx_def
  have hx : 0 < x := by positivity
  have hθ : 0 < x ^ p₀⁻¹ := Real.rpow_pos_of_pos hx _
  have h2p : 0 < (2 : ℝ) ^ p := by positivity
  have hc : (2 : ℝ) ^ p * (x ^ p₀⁻¹) ^ p₀ < 1 := by
    rw [Real.rpow_inv_rpow hx.le (by linarith), hx_def, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ h2p.ne', one_mul]
    norm_num
  exact (dyadicUMDConst_le_of_isDyadicUMDBound (xtr_isDyadicUMDBound_theta (by linarith) hp hu1
    hu one_lt_two hθ hc)).trans_lt ENNReal.ofReal_lt_top

/-- `UMD_p^Δ (X) ≤ 100 p* UMD_2^Δ (X)`, by the good-λ inequality from `L²` with `β`, `δ` chosen as
functions of `p`. -/
theorem dyadicUMDConst_le_mul_dyadicUMDConst_two {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X p ≤ ENNReal.ofReal (100 * pStar p) * dyadicUMDConst X 2 := by
  have hpS : p ≤ pStar p := le_max_left _ _
  have hpS' : p / (p - 1) ≤ pStar p := le_max_right _ _
  have hp1 : 0 < p - 1 := by linarith
  refine xtr_dyadicUMDConst_le (by linarith) two_pos (by linarith) fun u hu1 hu => ?_
  rcases le_or_gt 2 p with hp2 | hp2
  · -- `p ≥ 2`: `β = 1 + 1 / p`, `θ = 1 / 3`
    have hq : 0 < 1 / p := by positivity
    have hβ : 1 < 1 + 1 / p := by linarith
    have hB : (1 + 1 / p) ^ p ≤ 4 := xtr_one_add_inv_rpow_le (by linarith)
    have hB0 : 0 ≤ (1 + 1 / p) ^ p := Real.rpow_nonneg (by linarith) _
    have hc : (1 + 1 / p) ^ p * (1 / 3 : ℝ) ^ (2 : ℝ) ≤ 4 / 9 := by
      rw [Real.rpow_two]
      nlinarith
    have hc0 : 0 ≤ (1 + 1 / p) ^ p * (1 / 3 : ℝ) ^ (2 : ℝ) := by positivity
    refine ⟨_, ?_, xtr_isDyadicUMDBound_theta (θ := 1 / 3) two_pos hp hu1 hu hβ (by norm_num)
      (by linarith)⟩
    have hA1 : p / (p - 1) ≤ 2 := by
      rw [div_le_iff₀ hp1]
      linarith
    have hA2 : (1 + 1 / p) * (4 * u + 2 * (1 / 3)) / (1 / 3 * (1 + 1 / p - 1)) =
        3 * (p + 1) * (4 * u + 2 / 3) := by
      field_simp
      ring
    have hA2' : 3 * (p + 1) * (4 * u + 2 / 3) ≤ 21 * p * u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hu1)]
    have hA3 : (1 - (1 + 1 / p) ^ p * (1 / 3 : ℝ) ^ (2 : ℝ)) ^ (-(1 / p)) ≤ 9 / 5 := by
      refine (xtr_rpow_neg_le_inv (by linarith) (by linarith) hp.le).trans ?_
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    rw [hA2]
    calc p / (p - 1) * (3 * (p + 1) * (4 * u + 2 / 3)) *
          (1 - (1 + 1 / p) ^ p * (1 / 3 : ℝ) ^ (2 : ℝ)) ^ (-(1 / p))
        ≤ 2 * (21 * p * u) * (9 / 5) :=
          mul_le_mul (mul_le_mul hA1 hA2' (by positivity) (by norm_num)) hA3
            (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ ≤ 100 * pStar p * u := by nlinarith [mul_le_mul_of_nonneg_right hpS (by linarith : 0 ≤ u)]
  · -- `1 < p < 2`: `β = 2`, `θ = 1 / 4`
    have h2p : (2 : ℝ) ^ p < 4 := by
      have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hp2
      rw [Real.rpow_two] at this
      linarith
    have h2p0 : 0 ≤ (2 : ℝ) ^ p := by positivity
    have hc : (2 : ℝ) ^ p * (1 / 4 : ℝ) ^ (2 : ℝ) < 1 / 4 := by
      rw [Real.rpow_two]
      nlinarith
    have hc0 : 0 ≤ (2 : ℝ) ^ p * (1 / 4 : ℝ) ^ (2 : ℝ) := by positivity
    refine ⟨_, ?_, xtr_isDyadicUMDBound_theta (θ := 1 / 4) two_pos hp hu1 hu one_lt_two
      (by norm_num) (by linarith)⟩
    have hA2 : (2 : ℝ) * (4 * u + 2 * (1 / 4)) / (1 / 4 * (2 - 1)) = 32 * u + 4 := by ring
    have hA3 : (1 - (2 : ℝ) ^ p * (1 / 4 : ℝ) ^ (2 : ℝ)) ^ (-(1 / p)) ≤ 4 / 3 := by
      refine (xtr_rpow_neg_le_inv (by linarith) (by linarith) hp.le).trans ?_
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    rw [hA2]
    calc p / (p - 1) * (32 * u + 4) * (1 - (2 : ℝ) ^ p * (1 / 4 : ℝ) ^ (2 : ℝ)) ^ (-(1 / p))
        ≤ pStar p * (36 * u) * (4 / 3) :=
          mul_le_mul (mul_le_mul hpS' (by linarith) (by linarith) (by linarith)) hA3
            (Real.rpow_nonneg (by linarith) _) (by nlinarith)
      _ ≤ 100 * pStar p * u := by nlinarith

/-- `UMD_2^Δ (X) ≤ 200 UMD_p^Δ (X)`, by the good-λ inequality from `L^p` to `L²`. -/
theorem dyadicUMDConst_two_le_mul {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X 2 ≤ 200 * dyadicUMDConst X p := by
  rw [← ENNReal.ofReal_ofNat 200]
  refine xtr_dyadicUMDConst_le two_pos (by linarith) (by norm_num) fun u hu1 hu => ?_
  -- `β = 3 / 2`, `θ = 2 / 9`
  have hθp : (2 / 9 : ℝ) ^ p ≤ 2 / 9 := by
    have := Real.rpow_le_rpow_of_exponent_ge (x := 2 / 9) (by norm_num) (by norm_num) hp.le
    rwa [Real.rpow_one] at this
  have hθp0 : 0 ≤ (2 / 9 : ℝ) ^ p := by positivity
  have hc : (3 / 2 : ℝ) ^ (2 : ℝ) * (2 / 9 : ℝ) ^ p ≤ 1 / 2 := by
    rw [Real.rpow_two]
    nlinarith
  refine ⟨_, ?_, xtr_isDyadicUMDBound_theta (θ := 2 / 9) (by linarith) one_lt_two hu1 hu
    (by norm_num : (1 : ℝ) < 3 / 2) (by norm_num) (by linarith)⟩
  have hA2 : (2 : ℝ) / (2 - 1) * (3 / 2 * (4 * u + 2 * (2 / 9)) / (2 / 9 * (3 / 2 - 1))) =
      2 * (54 * u + 6) := by ring
  have hA3 : (1 - (3 / 2 : ℝ) ^ (2 : ℝ) * (2 / 9 : ℝ) ^ p) ^ (-(1 / 2 : ℝ)) ≤ 3 / 2 := by
    set y := 1 - (3 / 2 : ℝ) ^ (2 : ℝ) * (2 / 9 : ℝ) ^ p with hy_def
    have hy : 1 / 2 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    rw [Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow,
      inv_le_comm₀ (Real.sqrt_pos.mpr hy0) (by norm_num), Real.le_sqrt (by norm_num) hy0.le]
    nlinarith
  rw [hA2]
  calc 2 * (54 * u + 6) * (1 - (3 / 2 : ℝ) ^ (2 : ℝ) * (2 / 9 : ℝ) ^ p) ^ (-(1 / 2 : ℝ))
      ≤ 2 * (60 * u) * (3 / 2) :=
        mul_le_mul (by linarith) hA3 (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ ≤ 200 * u := by linarith

end Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Extrapolation of the UMD property** (Hytönen–van Neerven–Veraar–Weis I, Theorem 4.2.7): a
Banach space that is `UMD_{p₀}` for some `p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`. -/
theorem umdConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀) (h : umdConst X p₀ < ⊤)
    (hp : 1 < p) : umdConst X p < ⊤ := by
  rw [← dyadicUMDConst_eq_umdConst hp₀] at h
  rw [← dyadicUMDConst_eq_umdConst hp]
  exact dyadicUMDConst_lt_top_of_lt_top hp₀ h hp

/-- **Extrapolation of the UMD property, constants** (Hytönen–van Neerven–Veraar–Weis I,
Theorem 4.2.7): `UMD_p (X) ≤ 100 p* UMD₂ (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_le_mul_umdConst_two {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ ENNReal.ofReal (100 * pStar p) * umdConst X 2 := by
  rw [← dyadicUMDConst_eq_umdConst hp, ← dyadicUMDConst_eq_umdConst one_lt_two]
  exact dyadicUMDConst_le_mul_dyadicUMDConst_two hp

/-- **Extrapolation of the UMD property, constants** (Hytönen–van Neerven–Veraar–Weis I,
Theorem 4.2.7): `UMD₂ (X) ≤ 200 UMD_p (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_two_le_mul {p : ℝ} (hp : 1 < p) : umdConst X 2 ≤ 200 * umdConst X p := by
  rw [← dyadicUMDConst_eq_umdConst hp, ← dyadicUMDConst_eq_umdConst one_lt_two]
  exact dyadicUMDConst_two_le_mul hp

end BanachProbability
