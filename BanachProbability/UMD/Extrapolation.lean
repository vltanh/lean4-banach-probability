module

public import BanachProbability.UMD.GoodLambda
public import BanachProbability.UMD.Maurey.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Extrapolation of the UMD property

A real Banach space that is `UMD_q` for one `q ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`, with
`UMD_p (X) ≤ 100 (p / q + p' / q') UMD_q (X)`, and in particular
`UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 50 (p + p') UMD₂ (X)`: T. Hytönen, J. van Neerven, M. Veraar and
L. Weis (HNVW), *Analysis in Banach Spaces I* (2016), Theorem 4.2.7 (p. 283). The proof is theirs:
(3.49) of Theorem 3.5.4 (p. 223), the extrapolation of the bounds of one transform `T` of
Paley–Walsh martingales, then the supremum over the transforms, in the form of Lemma 4.2.8, and the
equality of the dyadic and the general constants, Theorem 4.2.5 (`dyadicUMDConst_eq_umdConst`). The
book's statement is for real and complex scalars; here the scalars, hence the signs, are real.

* Lemma 3.5.15 with the constant of (3.59) (p. 232), `IsWeakTransformBound.lpNorm_cubeMax_le`: a
  bound `K ≥ 1` of `T` from `H^q` to `L^{q,∞}` gives
  `‖T* f‖_p ≤ 2^{1/p+1/q} (1 + p/q) (3e + 1) K ‖f* ∨ w*‖_p`, by integrating the good-λ inequality of
  `BanachProbability.UMD.GoodLambda` with `θ = 1 + q/p`, `α = 2^{1/q} K θ^{p/q}`.
* Proof of (3.49) (p. 234), `IsWeakTransformBound.lpNorm_cubeMax_le_lpNorm`: with `w_n = ‖df_n‖`,
  predictable for Paley–Walsh martingales, and Doob's inequality (`doob_lpNorm_cubeMax_le`),
  `‖T* f‖_p ≤ 20 K C (p, q) p p' ‖f‖_p`, `C (p, q) = 2^{1/p+1/q} (1/p + 1/q)`. The same for the
  adjoint of `T` (Lemma 3.5.3) gives the minimum of `C (p, q)` and `C (p', q')`
  (`IsTransformBound.extrapolation_min`), and an elementary inequality gives (3.49):
  `‖T‖_{p → p} ≤ 80 (p/q + p'/q') ‖T‖_{q → q}` (`IsTransformBound.extrapolation`), which the book
  states with `100` (`isTransformBound_extrapolation`).
* Theorem 4.2.7 for the dyadic constants (`dyadicUMDConst_le_mul_dyadicUMDConst`) and for the UMD
  constants (`umdConst_le_mul_umdConst`), with the special cases of one exponent `2` and the
  finiteness (`umdConst_lt_top_of_lt_top`).
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

variable {N : ℕ}

section LayerCake

/-! ### Integration of a good-λ inequality -/

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
    gdl_prob_mono fun ε hε => lt_of_le_of_lt htt' hε
  exact hanti.measurable.ennreal_ofReal.mul (measurable_id.pow_const _).ennreal_ofReal

/-- The integration of a good-λ inequality `P (G > θ λ, Z ≤ δ λ) ≤ η P (G > λ)` against
`p λ^{p−1} dλ` (HNVW, proof of Lemma 3.5.15, p. 232):
`‖G‖_p^p ≤ η θ^p ‖G‖_p^p + (θ / δ)^p ‖Z‖_p^p`. -/
private theorem xtr_avg_rpow_le {G Z : (Fin N → Bool) → ℝ} (hG : ∀ ε, 0 ≤ G ε)
    (hZ : ∀ ε, 0 ≤ Z ε) {p θ δ η : ℝ} (hp : 0 < p) (hθ : 0 < θ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (h : ∀ t, 0 < t → prob {ε | θ * t < G ε ∧ Z ε ≤ δ * t} ≤ η * prob {ε | t < G ε}) :
    (avg fun ε => G ε ^ p) ≤
      η * θ ^ p * (avg fun ε => G ε ^ p) + (θ / δ) ^ p * avg fun ε => Z ε ^ p := by
  -- `P (G > θ t) ≤ η P (G > t) + P (Z > δ t)`
  have hGL : ∀ t, 0 < t →
      prob {ε | θ * t < G ε} ≤ η * prob {ε | t < G ε} + prob {ε | δ * t < Z ε} := by
    intro t ht
    refine (xtr_prob_le_add (s₁ := {ε | θ * t < G ε ∧ Z ε ≤ δ * t})
      (s₂ := {ε | δ * t < Z ε}) fun ε hε => ?_).trans (add_le_add (h t ht) le_rfl)
    by_cases h' : Z ε ≤ δ * t
    · exact Or.inl ⟨hε, h'⟩
    · exact Or.inr (not_le.mp h')
  -- the substitutions `t ↦ θ t`, `t ↦ δ t`, done as `E (Z / b)^p = b^{−p} E Z^p`
  have hdiv : ∀ (Z : (Fin N → Bool) → ℝ) (b : ℝ), 0 < b → (∀ ε, 0 ≤ Z ε) →
      avg (fun ε => (Z ε / b) ^ p) = avg (fun ε => Z ε ^ p) / b ^ p := by
    intro Z b hb hZ
    simp only [Real.div_rpow (hZ _) hb.le, avg]
    rw [← Finset.sum_div, div_right_comm]
  have hset : ∀ (Z : (Fin N → Bool) → ℝ) (b : ℝ), 0 < b → ∀ t : ℝ,
      {ε | t < Z ε / b} = {ε | b * t < Z ε} := by
    intro Z b hb t
    ext ε
    simp only [Set.mem_ofPred_eq, lt_div_iff₀ hb, mul_comm]
  have hkey : ENNReal.ofReal (avg fun ε => (G ε / θ) ^ p) ≤
      ENNReal.ofReal η * ENNReal.ofReal (avg fun ε => G ε ^ p) +
        ENNReal.ofReal (avg fun ε => (Z ε / δ) ^ p) := by
    rw [xtr_layerCake (fun ε => div_nonneg (hG ε) hθ.le) hp, xtr_layerCake hG hp,
      xtr_layerCake (fun ε => div_nonneg (hZ ε) hδ.le) hp, mul_left_comm, ← mul_add,
      ← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal η) _ ENNReal.ofReal_ne_top,
      ← MeasureTheory.lintegral_add_left ((xtr_measurable_integrand G p).const_mul _)]
    gcongr ENNReal.ofReal p * ?_
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    simp only [hset G θ hθ, hset Z δ hδ]
    rw [← mul_assoc, ← add_mul]
    gcongr
    rw [← ENNReal.ofReal_mul hη,
      ← ENNReal.ofReal_add (mul_nonneg hη (gdl_prob_nonneg _)) (gdl_prob_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hGL t ht)
  set A := avg fun ε => G ε ^ p with hA
  set B := avg fun ε => Z ε ^ p with hB
  have hA0 : 0 ≤ A := avg_nonneg fun ε => Real.rpow_nonneg (hG ε) p
  have hB0 : 0 ≤ B := avg_nonneg fun ε => Real.rpow_nonneg (hZ ε) p
  have hθp : 0 < θ ^ p := Real.rpow_pos_of_pos hθ p
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ p
  rw [hdiv G θ hθ hG, hdiv Z δ hδ hZ, ← ENNReal.ofReal_mul hη,
    ← ENNReal.ofReal_add (mul_nonneg hη hA0) (div_nonneg hB0 hδp.le),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hη hA0) (div_nonneg hB0 hδp.le)),
    div_le_iff₀ hθp] at hkey
  refine hkey.trans_eq ?_
  rw [Real.div_rpow hθ.le hδ.le]
  field_simp

end LayerCake

section Extrapolation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {σ : Fin N → (Fin N → Bool) → ℝ}

/-- `(1 + x)^{1/x} ≤ e` (with `x = q / p`, the book's `θ^{p/q} ≤ e`, p. 232). -/
private theorem xtr_rpow_le_exp {x : ℝ} (hx : 0 < x) : (1 + x) ^ (1 / x) ≤ Real.exp 1 := by
  calc (1 + x) ^ (1 / x) ≤ Real.exp x ^ (1 / x) :=
        Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp x]) (by positivity)
    _ = Real.exp 1 := by rw [← Real.exp_mul, mul_one_div_cancel hx.ne']

/-- The `L^p` norm of a nonnegative function. -/
private theorem xtr_lpNorm_of_nonneg {Z : (Fin N → Bool) → ℝ} (hZ : ∀ ε, 0 ≤ Z ε) (p : ℝ) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) p Z = (avg fun ε => Z ε ^ p) ^ (1 / p) := by
  simp only [SignCube.lpNorm, Real.norm_of_nonneg (hZ _)]

/-- **HNVW, Lemma 3.5.15** (p. 232) with the constant of (3.59): if the transform `T` by predictable
signs is bounded from `H^q (X)` to `L^{q,∞} (X)` with constant `K ≥ 1`, and `w` is a predictable
majorant of the differences of the martingale generated by `f`, then
`‖T* f‖_p ≤ 2^{1/p+1/q} (1 + p/q) (3e + 1) K ‖f* ∨ w*‖_p` (the book, `p, q ∈ [1, ∞)`, rounds the
constant to `37 (1 + p/q) K` in (3.58)).

As in the book: the good-λ inequality (Lemma 3.5.14) is integrated with `θ = 1 + q/p`,
`α = 2^{1/q} K θ^{p/q}`, for which `η = (K / α)^q = θ^{−p} / 2`, and
`δ = (θ − 1) / (3 α + 1)`; the first term is absorbed, everything being finite on the cube; finally
`θ / (θ − 1) = 1 + p/q`, `θ^{p/q} ≤ e` and `‖v‖_∞ = 1 ≤ 2^{1/q} K` (Proposition 3.5.10 of the book;
trivial for signs, as `K ≥ 1`, see `IsTransformBound.one_le`). -/
theorem IsWeakTransformBound.lpNorm_cubeMax_le {p q K : ℝ} (hp : 0 < p) (hq : 0 < q) (hK : 1 ≤ K)
    (h : IsWeakTransformBound X σ q K) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (f : (Fin N → Bool) → X)
    {w : ℕ → (Fin N → Bool) → ℝ} (hw : IsAdapted w)
    (hfw : ∀ k ε, ‖condAvg (k + 1) f ε - condAvg k f ε‖ ≤ w k ε) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) p (cubeMax (cubeTransform σ f)) ≤
      (2 : ℝ) ^ (1 / p + 1 / q) * (1 + p / q) * (3 * Real.exp 1 + 1) * K *
        SignCube.lpNorm (fun t : ℝ => ‖t‖) p (fun ε => max (cubeMax f ε) (runningMax w N ε)) := by
  have hK0 : 0 < K := by linarith
  -- the choices `θ = 1 + q / p`, `α = 2^{1/q} K θ^{p/q}`, `δ = (θ − 1) / (3 α + 1)`
  set θ : ℝ := 1 + q / p with hθ_def
  have hqp : 0 < q / p := div_pos hq hp
  have hθ : 1 < θ := by linarith
  have hθ0 : 0 < θ := by linarith
  set α : ℝ := 2 ^ (1 / q) * K * θ ^ (p / q) with hα_def
  have hα : 0 < α := by positivity
  set δ : ℝ := (θ - 1) / (3 * α + 1) with hδ_def
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  -- `η = (K / α)^q = θ^{−p} / 2`
  have hη : (K / α) ^ q * θ ^ p = 1 / 2 := by
    have e1 : K / α = ((2 : ℝ) ^ (1 / q) * θ ^ (p / q))⁻¹ := by
      rw [hα_def]
      field_simp
    rw [e1, Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hθ0.le, one_div_mul_cancel hq.ne',
      div_mul_cancel₀ _ hq.ne', Real.rpow_one, mul_inv, mul_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hθ0 p).ne', mul_one, one_div]
  have hloc := h.isLocalTransformBound hq hK0.le hα
  set G := cubeMax (cubeTransform σ f) with hG_def
  set Z : (Fin N → Bool) → ℝ := fun ε => max (cubeMax f ε) (runningMax w N ε) with hZ_def
  have hG : ∀ ε, 0 ≤ G ε := cubeMax_nonneg _
  have hZ : ∀ ε, 0 ≤ Z ε := fun ε => (cubeMax_nonneg f ε).trans (le_max_left _ _)
  have hint := xtr_avg_rpow_le hG hZ hp hθ0 hδ
    (Real.rpow_nonneg (div_nonneg hK0.le hα.le) q) fun t ht =>
      hloc.goodLambda hσ hσ1 hα.le hθ hδ.le le_rfl ht hw hfw
  rw [hη] at hint
  rw [xtr_lpNorm_of_nonneg hG, xtr_lpNorm_of_nonneg hZ]
  set A := avg fun ε => G ε ^ p with hA
  set B := avg fun ε => Z ε ^ p with hB
  have hA0 : 0 ≤ A := avg_nonneg fun ε => Real.rpow_nonneg (hG ε) p
  have hB0 : 0 ≤ B := avg_nonneg fun ε => Real.rpow_nonneg (hZ ε) p
  -- absorb
  have hAB : A ≤ 2 * ((θ / δ) ^ p * B) := by linarith
  have hθδ : θ / δ = (1 + p / q) * (3 * α + 1) := by
    rw [hδ_def, show θ - 1 = q / p by rw [hθ_def]; ring, hθ_def]
    field_simp
    ring
  have hα1 : 3 * α + 1 ≤ 2 ^ (1 / q) * (3 * Real.exp 1 + 1) * K := by
    have h1 : θ ^ (p / q) ≤ Real.exp 1 := by
      have := xtr_rpow_le_exp hqp
      rwa [one_div_div] at this
    have h2 : (1 : ℝ) ≤ 2 ^ (1 / q) := Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : 1 ≤ (2 : ℝ) ^ (1 / q) * K := by nlinarith
    have h4 : α ≤ 2 ^ (1 / q) * K * Real.exp 1 := by
      rw [hα_def]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hpq : 0 < p / q := div_pos hp hq
  calc A ^ (1 / p) ≤ (2 * ((θ / δ) ^ p * B)) ^ (1 / p) :=
        Real.rpow_le_rpow hA0 hAB (by positivity)
    _ = 2 ^ (1 / p) * (θ / δ) * B ^ (1 / p) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) hB0,
          one_div, Real.rpow_rpow_inv (by positivity) hp.ne', mul_assoc]
    _ ≤ 2 ^ (1 / p) * ((1 + p / q) * (2 ^ (1 / q) * (3 * Real.exp 1 + 1) * K)) * B ^ (1 / p) := by
        rw [hθδ]
        gcongr
    _ = 2 ^ (1 / p + 1 / q) * (1 + p / q) * (3 * Real.exp 1 + 1) * K * B ^ (1 / p) := by
        rw [Real.rpow_add (by norm_num)]
        ring

/-- Doob's maximal inequality on the cube, `‖f*‖_p ≤ p' ‖f‖_p`. Doob's inequality for Paley–Walsh
martingales (`SignCube.lpNorm_runningMax_le`) is about martingales started at `0`; it is applied to
`g_0 = 0`, `g_{n+1} = r f_n` with one more sign `r`, as in the proof of HNVW, Lemma 4.2.8. -/
theorem doob_lpNorm_cubeMax_le {p : ℝ} (hp : 1 < p) (f : (Fin N → Bool) → X) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) p (cubeMax f) ≤
      p / (p - 1) * SignCube.lpNorm (fun x => ‖x‖) p f := by
  obtain ⟨ξ, hξ, hf⟩ := cbt_exists_paleyWalsh f
  set c := condAvg 0 f fun _ => false with hc_def
  have hc : ∀ ε, condAvg 0 f ε = c := fun ε => cbt_condAvg_eq_of_agree 0 f _ _ (by simp)
  have hcons := cbt_paleyWalsh_cons_condAvg hc hf
  have key := SignCube.lpNorm_runningMax_le (cbt_isPredictable_cons c hξ) hp (N + 1)
  rw [show paleyWalsh (cbtCons c ξ) (N + 1) = fun ω => coin (ω 0) • f (Fin.tail ω) from
    funext fun ω => by rw [hcons, cbt_condAvg_of_le le_rfl], cbt_lpNorm_coin_smul_tail] at key
  refine le_trans ?_ key
  rw [xtr_lpNorm_of_nonneg (cubeMax_nonneg f), SignCube.lpNorm,
    ← cbt_avg_tail fun ε => cubeMax f ε ^ p]
  refine Real.rpow_le_rpow (avg_nonneg fun ω => Real.rpow_nonneg (cubeMax_nonneg f _) p)
    (avg_mono fun ω => Real.rpow_le_rpow (cubeMax_nonneg f _) ?_ (by linarith)) (by positivity)
  refine le_trans (gdl_runningMax_le fun k hk => ?_) (le_abs_self _)
  have h1 := le_runningMax (fun k ω => ‖paleyWalsh (cbtCons c ξ) k ω‖) (Nat.succ_le_succ hk) ω
  rw [hcons, norm_smul, Real.norm_eq_abs, abs_coin, one_mul] at h1
  exact h1

/-- The first bound in the proof of HNVW, (3.49) (p. 234): if the transform `T` by predictable signs
is bounded from `H^q (X)` to `L^{q,∞} (X)` with constant `K ≥ 1`, then
`‖T* f‖_p ≤ 20 K C (p, q) p p' ‖f‖_p`, `C (p, q) = 2^{1/p+1/q} (1/p + 1/q)`. The weights
`w_n = ‖df_n‖` are predictable because the martingale generated by `f` is a Paley–Walsh martingale
(Proposition 3.1.10, p. 169), `f* ∨ (df)* ≤ 2 f*`, `3e + 1 ≤ 10`, and Doob's inequality. -/
theorem IsWeakTransformBound.lpNorm_cubeMax_le_lpNorm {p q K : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hK : 1 ≤ K) (h : IsWeakTransformBound X σ q K) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (f : (Fin N → Bool) → X) :
    SignCube.lpNorm (fun t : ℝ => ‖t‖) p (cubeMax (cubeTransform σ f)) ≤
      20 * K * (2 ^ (1 / p + 1 / q) * (1 / p + 1 / q)) * (p * (p / (p - 1))) *
        SignCube.lpNorm (fun x => ‖x‖) p f := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  -- `w_n = ‖df_n‖` is predictable
  set w : ℕ → (Fin N → Bool) → ℝ := fun k ε => ‖condAvg (k + 1) f ε - condAvg k f ε‖ with hw_def
  have hw : IsAdapted w := by
    obtain ⟨ξ, hξ, hf⟩ := cbt_exists_paleyWalsh f
    intro k ε ε' hε
    have hwk : ∀ ε, w k ε = if h : k < N then ‖ξ ⟨k, h⟩ ε‖ else 0 := by
      intro ε
      simp only [hw_def]
      rw [hf (k + 1), hf k, add_sub_add_left_eq_sub]
      split_ifs with hk
      · exact norm_paleyWalsh_succ_sub ξ ⟨k, hk⟩ ε
      · rw [paleyWalsh_succ, dite_eq_right hk, add_zero, sub_self, norm_zero]
    rw [hwk, hwk]
    split_ifs with hk
    · rw [hξ ⟨k, hk⟩ ε ε' fun j hj => hε j (Fin.lt_def.mp hj)]
    · rfl
  have hwt : ∀ ε, max (cubeMax f ε) (runningMax w N ε) ≤ 2 * cubeMax f ε := by
    intro ε
    refine max_le (by linarith [cubeMax_nonneg f ε]) (gdl_runningMax_le fun k _ => ?_)
    have := norm_sub_le (condAvg (k + 1) f ε) (condAvg k f ε)
    linarith [norm_condAvg_le_cubeMax f (k + 1) ε, norm_condAvg_le_cubeMax f k ε]
  have hm0 : ∀ ε, 0 ≤ max (cubeMax f ε) (runningMax w N ε) := fun ε =>
    (cubeMax_nonneg f ε).trans (le_max_left _ _)
  have hZ : SignCube.lpNorm (fun t : ℝ => ‖t‖) p
        (fun ε => max (cubeMax f ε) (runningMax w N ε)) ≤
      2 * SignCube.lpNorm (fun t : ℝ => ‖t‖) p (cubeMax f) := by
    rw [xtr_lpNorm_of_nonneg hm0, xtr_lpNorm_of_nonneg (cubeMax_nonneg f)]
    calc (avg fun ε => max (cubeMax f ε) (runningMax w N ε) ^ p) ^ (1 / p)
        ≤ (avg fun ε => 2 ^ p * cubeMax f ε ^ p) ^ (1 / p) := by
          refine Real.rpow_le_rpow (avg_nonneg fun ε => Real.rpow_nonneg (hm0 ε) p)
            (avg_mono fun ε => ?_) (by positivity)
          rw [← Real.mul_rpow (by norm_num) (cubeMax_nonneg f ε)]
          exact Real.rpow_le_rpow (hm0 ε) (hwt ε) hp0.le
      _ = 2 * (avg fun ε => cubeMax f ε ^ p) ^ (1 / p) := by
          rw [avg_const_mul, Real.mul_rpow (by positivity)
            (avg_nonneg fun ε => Real.rpow_nonneg (cubeMax_nonneg f ε) p), one_div,
            Real.rpow_rpow_inv (by norm_num) hp0.ne']
  have he : 3 * Real.exp 1 + 1 ≤ 10 := by linarith [Real.exp_one_lt_d9]
  have h3 := h.lpNorm_cubeMax_le hp0 hq hK hσ hσ1 f hw fun _ _ => le_rfl
  have hD := doob_lpNorm_cubeMax_le hp f
  set c : ℝ := 2 ^ (1 / p + 1 / q) * (1 + p / q) with hc
  have hc0 : 0 ≤ c := by positivity
  have hK0 : 0 ≤ K := by linarith
  calc SignCube.lpNorm (fun t : ℝ => ‖t‖) p (cubeMax (cubeTransform σ f))
      ≤ c * (3 * Real.exp 1 + 1) * K * SignCube.lpNorm (fun t : ℝ => ‖t‖) p
          (fun ε => max (cubeMax f ε) (runningMax w N ε)) := h3
    _ ≤ c * 10 * K * (2 * (p / (p - 1) * SignCube.lpNorm (fun x => ‖x‖) p f)) := by
        have h0 : 0 ≤ SignCube.lpNorm (fun t : ℝ => ‖t‖) p
            (fun ε => max (cubeMax f ε) (runningMax w N ε)) :=
          lpNorm_nonneg (fun t => norm_nonneg t) p _
        refine mul_le_mul ?_ (hZ.trans (by linarith)) h0 (by positivity)
        gcongr
    _ = _ := by
        rw [hc]
        field_simp
        ring

/-- The consequence of the first bound in the proof of HNVW, (3.49) (p. 234), for `‖T f‖ ≤ T* f`. -/
theorem IsWeakTransformBound.isTransformBound {p q K : ℝ} (hp : 1 < p) (hq : 0 < q) (hK : 1 ≤ K)
    (h : IsWeakTransformBound X σ q K) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) :
    IsTransformBound X σ p
      (20 * K * (2 ^ (1 / p + 1 / q) * (1 / p + 1 / q)) * (p * (p / (p - 1)))) := by
  intro f
  refine le_trans ?_ (h.lpNorm_cubeMax_le_lpNorm hp hq hK hσ hσ1 f)
  have hp0 : 0 < p := by linarith
  rw [xtr_lpNorm_of_nonneg (cubeMax_nonneg _)]
  exact Real.rpow_le_rpow (avg_nonneg fun ε => Real.rpow_nonneg (norm_nonneg _) p)
    (avg_mono fun ε => Real.rpow_le_rpow (norm_nonneg _) (norm_le_cubeMax _ ε) hp0.le)
    (by positivity)

/-- `2^s s ≤ 4 s − 2 s²` for `0 ≤ s ≤ 1`: `2^s ≤ 1 + s ≤ 4 − 2 s`. -/
private theorem xtr_two_rpow_mul_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (2 : ℝ) ^ s * s ≤ 4 * s - 2 * s ^ 2 := by
  have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hs0 hs1
  rw [one_add_one_eq_two, mul_one] at h
  nlinarith

/-- The elementary inequality "left to the reader" in the proof of HNVW, (3.49) (p. 234):
`min {C (p, q), C (p', q')} ≤ 4 (1 / (p q') + 1 / (p' q))`, `C (p, q) = 2^{1/p+1/q} (1/p + 1/q)`.
With `a = 1/p`, `b = 1/q`, `s = a + b`, the right side is `4 (s − 2 a b) ≥ 4 s − 2 s²`; it and the
left side do not change under `(a, b) ↦ (1 − a, 1 − b)`, so `s ≤ 1` without loss of generality. -/
private theorem xtr_min_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    min ((2 : ℝ) ^ (a + b) * (a + b)) (2 ^ ((1 - a) + (1 - b)) * ((1 - a) + (1 - b))) ≤
      4 * (a * (1 - b) + (1 - a) * b) := by
  rcases le_total (a + b) 1 with h | h
  · refine (min_le_left _ _).trans ((xtr_two_rpow_mul_le (by linarith) h).trans ?_)
    nlinarith [sq_nonneg (a - b)]
  · refine (min_le_right _ _).trans
      ((xtr_two_rpow_mul_le (s := (1 - a) + (1 - b)) (by linarith) (by linarith)).trans ?_)
    nlinarith [sq_nonneg (a - b)]

/-- The second bound in the proof of HNVW, (3.49) (p. 234):
`‖T‖_{p → p} ≤ 20 ‖T‖_{q → q} min {C (p, q), C (p', q')} p p'`, from the first bound for `T` on `X`
at the exponents `p, q` and for its adjoint, the transform by the same signs on the dual of `X`, at
the exponents `p', q'` (Lemma 3.5.3). -/
theorem IsTransformBound.extrapolation_min {p p' q q' K : ℝ} (hp : p.HolderConjugate p')
    (hq : q.HolderConjugate q') (hK : 1 ≤ K) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (h : IsTransformBound X σ q K) :
    IsTransformBound X σ p (20 * K * min (2 ^ (1 / p + 1 / q) * (1 / p + 1 / q))
      (2 ^ (1 / p' + 1 / q') * (1 / p' + 1 / q')) * (p * p')) := by
  have hK0 : 0 ≤ K := by linarith
  have hp0 := hp.pos
  have hp'0 := hp.symm.pos
  have hq0 := hq.pos
  have hq'0 := hq.symm.pos
  rcases min_choice ((2 : ℝ) ^ (1 / p + 1 / q) * (1 / p + 1 / q))
    (2 ^ (1 / p' + 1 / q') * (1 / p' + 1 / q')) with hm | hm
  · rw [hm, hp.conjugate_eq]
    exact (h.isWeakTransformBound hq0 hK0).isTransformBound hp.lt hq0 hK hσ hσ1
  · -- the adjoint
    have h1 := ((h.dual hq hσ hK0).isWeakTransformBound hq'0 hK0).isTransformBound hp.symm.lt
      hq'0 hK hσ hσ1
    rw [← hp.symm.conjugate_eq] at h1
    rw [hm, mul_comm p p']
    exact h1.of_dual hp hσ (by positivity)

/-- **HNVW, (3.49)** with the constant of its proof (p. 234):
`‖T‖_{p → p} ≤ 80 (p/q + p'/q') ‖T‖_{q → q}` for the transform `T` by predictable signs on
Paley–Walsh martingales, for a bound `K ≥ 1` of `T` on `L^q (X)`. -/
theorem IsTransformBound.extrapolation {p p' q q' K : ℝ} (hp : p.HolderConjugate p')
    (hq : q.HolderConjugate q') (hK : 1 ≤ K) (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (h : IsTransformBound X σ q K) :
    IsTransformBound X σ p (80 * (p / q + p' / q') * K) := by
  refine (h.extrapolation_min hp hq hK hσ hσ1).mono ?_
  have hp0 := hp.pos
  have hp'0 := hp.symm.pos
  have hq0 := hq.pos
  have hq'0 := hq.symm.pos
  have ep : 1 / p' = 1 - 1 / p := by rw [one_div, one_div, hp.one_sub_inv]
  have eq : 1 / q' = 1 - 1 / q := by rw [one_div, one_div, hq.one_sub_inv]
  have hmin := xtr_min_le (a := 1 / p) (b := 1 / q) hp.one_div_nonneg
    ((div_le_one hp0).mpr hp.lt.le) hq.one_div_nonneg ((div_le_one hq0).mpr hq.lt.le)
  rw [← ep, ← eq] at hmin
  calc 20 * K * min (2 ^ (1 / p + 1 / q) * (1 / p + 1 / q))
        (2 ^ (1 / p' + 1 / q') * (1 / p' + 1 / q')) * (p * p')
      ≤ 20 * K * (4 * (1 / p * (1 / q') + 1 / p' * (1 / q))) * (p * p') := by gcongr
    _ = 80 * (p / q + p' / q') * K := by
        field_simp
        ring

/-- **HNVW, Theorem 3.5.4, (3.49)** (p. 223), for transforms by predictable signs of Paley–Walsh
martingales: `‖T‖_{L^p → L^p} ≤ 100 (p/q + p'/q') ‖T‖_{L^q → L^q}`, `p, q ∈ (1, ∞)`. (The proof
gives `80`, see `IsTransformBound.extrapolation`. On the zero space there is nothing to prove; on a
nonzero space a bound of `T` is at least `1`.) -/
theorem isTransformBound_extrapolation {p p' q q' K : ℝ} (hp : p.HolderConjugate p')
    (hq : q.HolderConjugate q') (hσ : IsPredictable σ) (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1)
    (h : IsTransformBound X σ q K) : IsTransformBound X σ p (100 * (p / q + p' / q') * K) := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · intro f
    have h0 : ∀ u : (Fin N → Bool) → X, SignCube.lpNorm (fun x => ‖x‖) p u = 0 := fun u =>
      (umdd_lpNorm_eq_zero_iff hp.pos).mpr fun ε => Subsingleton.elim _ _
    rw [h0, h0, mul_zero]
  · have hK := h.one_le hq.pos
    refine (h.extrapolation hp hq hK hσ hσ1).mono ?_
    have : 0 ≤ (p / q + p' / q') * K :=
      mul_nonneg (add_nonneg (div_nonneg hp.nonneg hq.nonneg)
        (div_nonneg hp.symm.nonneg hq.symm.nonneg)) (by linarith)
    linarith

end Extrapolation

section Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- On the zero space every constant is a dyadic `UMD_p` constant. -/
private theorem xtr_dyadicUMDConst_eq_zero [Subsingleton X] {p : ℝ} (hp : 0 < p) :
    dyadicUMDConst X p = 0 := by
  refine le_antisymm (dyadicUMDConst_le_of_isDyadicUMDBound fun N ξ σ _ _ _ n => ?_) zero_le
  rw [(umdd_lpNorm_eq_zero_iff hp).mpr fun ε => Subsingleton.elim _ _, ENNReal.ofReal_zero]
  exact zero_le

/-- **HNVW, Theorem 4.2.7** (p. 283) for the dyadic constants, with its proof (p. 285): the
transforms `T` by predictable signs on all sign cubes satisfy (3.49), and, by Lemma 4.2.8, the
supremum of their norms is the dyadic constant. -/
theorem dyadicUMDConst_le_mul_dyadicUMDConst {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    dyadicUMDConst X p ≤
      ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1)))) * dyadicUMDConst X q := by
  have hp' : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hq' : 0 < q / (q - 1) := div_pos (by linarith) (by linarith)
  have hC : 0 < 100 * (p / q + p / (p - 1) / (q / (q - 1))) := by positivity
  rcases subsingleton_or_nontrivial X with hX | hX
  · rw [xtr_dyadicUMDConst_eq_zero (by linarith)]
    exact zero_le
  by_cases ht : dyadicUMDConst X q = ⊤
  · rw [ht, ENNReal.mul_top (by simpa using hC)]
    exact le_top
  set K := (dyadicUMDConst X q).toReal with hK_def
  have hK : IsDyadicUMDBound X q (ENNReal.ofReal K) := by
    rw [hK_def, ENNReal.ofReal_toReal ht]
    exact isDyadicUMDBound_dyadicUMDConst (by linarith)
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  calc dyadicUMDConst X p
      ≤ ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1))) * K) :=
        dyadicUMDConst_le_of_isDyadicUMDBound <|
          isDyadicUMDBound_of_isTransformBound (mul_nonneg hC.le hK0) fun N σ hσ hσ1 =>
            isTransformBound_extrapolation (Real.HolderConjugate.conjExponent hp)
              (Real.HolderConjugate.conjExponent hq) hσ hσ1 (hK.isTransformBound hK0 hσ hσ1)
    _ = _ := by rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal ht]

/-- Extrapolation of the dyadic UMD property: finiteness for one exponent gives it for all. -/
theorem dyadicUMDConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀)
    (h : dyadicUMDConst X p₀ < ⊤) (hp : 1 < p) : dyadicUMDConst X p < ⊤ :=
  (dyadicUMDConst_le_mul_dyadicUMDConst hp hp₀).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

/-- `50 (p + p') ≤ 100 p*`. -/
private theorem xtr_le_pStar (p : ℝ) : 50 * (p + p / (p - 1)) ≤ 100 * pStar p := by
  have h1 : p ≤ pStar p := le_max_left _ _
  have h2 : p / (p - 1) ≤ pStar p := le_max_right _ _
  linarith

/-- `100 (p / 2 + p' / 2') = 50 (p + p')`. -/
private theorem xtr_const_two (p : ℝ) :
    100 * (p / 2 + p / (p - 1) / (2 / (2 - 1))) = 50 * (p + p / (p - 1)) := by
  ring

/-- `100 (2 / p + 2' / p') = 200`. -/
private theorem xtr_two_const {p : ℝ} (hp : 1 < p) :
    100 * (2 / p + 2 / (2 - 1) / (p / (p - 1))) = (200 : ℝ) := by
  have h0 : p ≠ 0 := by linarith
  have h1 : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `UMD_p^Δ (X) ≤ 100 p* UMD_2^Δ (X)`, by `50 (p + p') ≤ 100 p*`. -/
theorem dyadicUMDConst_le_mul_dyadicUMDConst_two {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X p ≤ ENNReal.ofReal (100 * pStar p) * dyadicUMDConst X 2 := by
  refine (dyadicUMDConst_le_mul_dyadicUMDConst hp one_lt_two).trans ?_
  rw [xtr_const_two]
  gcongr ENNReal.ofReal ?_ * _
  exact xtr_le_pStar p

/-- `UMD_2^Δ (X) ≤ 200 UMD_p^Δ (X)`. -/
theorem dyadicUMDConst_two_le_mul {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst X 2 ≤ 200 * dyadicUMDConst X p := by
  have h := dyadicUMDConst_le_mul_dyadicUMDConst (X := X) one_lt_two hp
  rwa [xtr_two_const hp, ENNReal.ofReal_ofNat] at h

end Dyadic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Extrapolation of the UMD property** (HNVW, Theorem 4.2.7, p. 283, for real scalars):
`UMD_p (X) ≤ 100 (p/q + p'/q') UMD_q (X)` for all `p, q ∈ (1, ∞)`, with `p' = p / (p − 1)` and
`q' = q / (q − 1)`. -/
theorem umdConst_le_mul_umdConst {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdConst X p ≤
      ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1)))) * umdConst X q := by
  rw [← dyadicUMDConst_eq_umdConst hp, ← dyadicUMDConst_eq_umdConst hq]
  exact dyadicUMDConst_le_mul_dyadicUMDConst hp hq

/-- **Extrapolation of the UMD property** (HNVW, Theorem 4.2.7, p. 283): a real Banach space that is
`UMD_{p₀}` for some `p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`. -/
theorem umdConst_lt_top_of_lt_top {p₀ p : ℝ} (hp₀ : 1 < p₀) (h : umdConst X p₀ < ⊤)
    (hp : 1 < p) : umdConst X p < ⊤ :=
  (umdConst_le_mul_umdConst hp hp₀).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

/-- **Extrapolation of the UMD property, the exponent `2`** (HNVW, Theorem 4.2.7, p. 283):
`UMD_p (X) ≤ 50 (p + p') UMD₂ (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_le_fifty_mul_umdConst_two {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ ENNReal.ofReal (50 * (p + p / (p - 1))) * umdConst X 2 := by
  have h := umdConst_le_mul_umdConst (X := X) hp one_lt_two
  rwa [xtr_const_two] at h

/-- **Extrapolation of the UMD property, the exponent `2`** (HNVW, Theorem 4.2.7, p. 283, weakened
by `50 (p + p') ≤ 100 p*`): `UMD_p (X) ≤ 100 p* UMD₂ (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_le_mul_umdConst_two {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ ENNReal.ofReal (100 * pStar p) * umdConst X 2 := by
  refine (umdConst_le_fifty_mul_umdConst_two hp).trans ?_
  gcongr ENNReal.ofReal ?_ * _
  exact xtr_le_pStar p

/-- **Extrapolation of the UMD property, the exponent `2`** (HNVW, Theorem 4.2.7, p. 283):
`UMD₂ (X) ≤ 200 UMD_p (X)` for every `p ∈ (1, ∞)`. -/
theorem umdConst_two_le_mul {p : ℝ} (hp : 1 < p) : umdConst X 2 ≤ 200 * umdConst X p := by
  have h := umdConst_le_mul_umdConst (X := X) one_lt_two hp
  rwa [xtr_two_const hp, ENNReal.ofReal_ofNat] at h

end BanachProbability
