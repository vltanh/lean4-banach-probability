module

public import BanachProbability.Noncommutative.WeakType
public import BanachProbability.Noncommutative.Interpolation
public import BanachProbability.Noncommutative.Duality
public import BanachProbability.Schatten.Dilation
public import BanachProbability.Schatten.Space
public import BanachProbability.UMD.Extrapolation

/-!
# Schatten classes are UMD, with constants uniform in the dimension

For real `n × n` matrices and `q ∈ (1, ∞)`:

* `UMD_q (S_q^{n×n}) ≤ K q*` with an absolute `K` (`umdConst_schattenSpace_le`;
  N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002),
  Theorem 4.3 and Corollary 4.5, `C_p (L^p (M)) ≤ C p² / (p − 1)`);
* `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` with an absolute `C` (`umdConst_two_schattenSpace_le`;
  Randrianantoanina (2002), Remark 4.6 (1), with Pisier's extrapolation).

The route, on the matrix cube with scalar predictable signs:

1. weak type `(1, 1)` (`weakType_one_one`) and the `L²` isometry (`lpNorm_two_transform`);
2. three regimes, for uniform constants with real methods only: for `r ∈ (1, 5/3]`, Marcinkiewicz
   between `1` and `2` gives `K / (r − 1)` (`lpNorm_transform_le_of_le_five_thirds`); for
   `r ∈ [5/3, 5/2]`, Marcinkiewicz between `3/2` (first regime) and `3` (from `3/2` by duality)
   gives a bounded constant (`lpNorm_transform_le_of_mem_Icc`); for `r ≥ 5/2`, duality from
   `r' ≤ 5/3` gives `K r` (`lpNorm_transform_le_of_five_halves_le`). A direct weak-`(1,1)`/`L²`
   interpolation would degenerate like `(2 − r)^{−1/2}` near `r = 2`; the middle regime is what
   keeps the constant uniform there. This fills in the step "by interpolation" of the source's
   Theorem 4.3, whose details it does not give;
3. general real matrices through the Hermitian dilation (`dilation`, `‖D (A)‖_q^q = 2 ‖A‖_q^q`),
   which commutes with conditional expectations and transforms;
4. the dyadic constant, then Maurey's theorem (`dyadicUMDConst_eq_umdConst`) for the full one;
5. extrapolation from `q` to `2` (`umdConst_two_le_mul`, `UMD₂ ≤ 200 UMD_q`), with an absolute
   constant, and `q* − 1 ≥ q* / 2`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

section Helpers

variable {N : ℕ} {E : Type*}

/-- The conditional expectations are additive in the function. -/
private theorem sumd_condAvg_add [AddCommGroup E] [Module ℝ E] (k : ℕ)
    (x y : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    condAvg k (x + y) ε = condAvg k x ε + condAvg k y ε := by
  simp only [condAvg, Pi.add_apply, Finset.sum_add_distrib, smul_add]

/-- The conditional expectations are homogeneous in the function. -/
private theorem sumd_condAvg_smul [AddCommGroup E] [Module ℝ E] (k : ℕ) (c : ℝ)
    (x : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    condAvg k (c • x) ε = c • condAvg k x ε := by
  simp only [condAvg, Pi.smul_apply, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The martingale transform by scalar multipliers `σ`, as a linear map on functions on the
cube. -/
private noncomputable def sumdTransformLM [AddCommGroup E] [Module ℝ E]
    (σ : Fin N → (Fin N → Bool) → ℝ) : ((Fin N → Bool) → E) →ₗ[ℝ] ((Fin N → Bool) → E) where
  toFun := transform σ
  map_add' x y := by
    funext ε
    simp only [transform, Pi.add_apply, sumd_condAvg_add, smul_sub, smul_add,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  map_smul' c x := by
    funext ε
    simp only [transform, Pi.smul_apply, RingHom.id_apply, sumd_condAvg_smul, smul_add,
      Finset.smul_sum, ← smul_sub]
    congr 1
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

private theorem sumdTransformLM_apply [AddCommGroup E] [Module ℝ E]
    (σ : Fin N → (Fin N → Bool) → ℝ) (x : (Fin N → Bool) → E) :
    sumdTransformLM σ x = transform σ x :=
  rfl

/-- From `E nrm (Y)^r ≤ M E nrm (X)^r` with `M ≥ 1` and `r ≥ 1` to
`‖Y‖_{L^r} ≤ M ‖X‖_{L^r}` (since `M^{1/r} ≤ M`). -/
private theorem sumd_lpNorm_le_of_avg_le {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {r M : ℝ}
    (hr : 1 ≤ r) (hM : 1 ≤ M) {X Y : (Fin N → Bool) → E}
    (h : (avg fun ε => nrm (Y ε) ^ r) ≤ M * avg fun ε => nrm (X ε) ^ r) :
    SignCube.lpNorm nrm r Y ≤ M * SignCube.lpNorm nrm r X := by
  have hA := avg_nonneg fun ε => Real.rpow_nonneg (hnrm (X ε)) r
  have hB := avg_nonneg fun ε => Real.rpow_nonneg (hnrm (Y ε)) r
  have hr' : 0 ≤ 1 / r := div_nonneg zero_le_one (by linarith)
  unfold SignCube.lpNorm
  calc (avg fun ε => nrm (Y ε) ^ r) ^ (1 / r)
      ≤ (M * avg fun ε => nrm (X ε) ^ r) ^ (1 / r) := Real.rpow_le_rpow hB h hr'
    _ = M ^ (1 / r) * (avg fun ε => nrm (X ε) ^ r) ^ (1 / r) :=
        Real.mul_rpow (by linarith) hA
    _ ≤ M * (avg fun ε => nrm (X ε) ^ r) ^ (1 / r) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le hM (div_le_one_of_le₀ hr (by linarith)))
          (Real.rpow_nonneg hA _)

private theorem sumd_le_pStar (r : ℝ) : r ≤ pStar r :=
  le_max_left _ _

private theorem sumd_div_le_pStar (r : ℝ) : r / (r - 1) ≤ pStar r :=
  le_max_right _ _

/-- `p* ≥ 2` for `p > 1`. -/
private theorem sumd_two_le_pStar {r : ℝ} (hr : 1 < r) : 2 ≤ pStar r := by
  rcases le_total 2 r with h | h
  · exact h.trans (sumd_le_pStar r)
  · refine le_trans ?_ (sumd_div_le_pStar r)
    rw [le_div_iff₀ (by linarith)]
    linarith

private theorem sumd_one_lt_toReal {q : ℝ≥0∞} (hq1 : 1 < q) (hqt : q ≠ ⊤) : 1 < q.toReal := by
  have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt).mpr hq1
  rwa [ENNReal.toReal_one] at this

/-- A Paley–Walsh martingale at time `m` is the Paley–Walsh martingale, at the final time `N`, of
the family `1_{k < m} ξ_k`. -/
private theorem sumd_paleyWalsh_eq_stop [AddCommGroup E] [Module ℝ E]
    (ξ : Fin N → (Fin N → Bool) → E) (m : ℕ) :
    paleyWalsh ξ m = paleyWalsh (fun k ε => if k.val < m then ξ k ε else 0) N := by
  funext ε
  have h : paleyWalsh ξ (min N m) ε =
      paleyWalsh (fun k ε => if k.val < m then ξ k ε else 0) N ε :=
    paleyWalsh_stopped ξ (fun _ => m) N ε
  rw [← h]
  rcases le_total m N with hm | hm
  · rw [min_eq_right hm]
  · rw [min_eq_left hm, paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ hm]

end Helpers

/-- First regime, `r ∈ (1, 5/3]`: `‖T_σ x‖_{L^r (S_r)} ≤ (K / (r − 1)) ‖x‖_{L^r (S_r)}` for
symmetric-matrix-valued `x` (Marcinkiewicz between weak `(1, 1)` and strong `(2, 2)`). -/
theorem lpNorm_transform_le_of_le_five_thirds : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 1 < r → r ≤ 5 / 3 → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K / (r - 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  obtain ⟨C, hC, hW⟩ := weakType_one_one
  refine ⟨8 * (C + 2), by positivity, ?_⟩
  intro r hr1 hr53 N n _ _ x σ hx hσ hσ1
  have hr2 : r < 2 := by linarith
  have hr0 : 0 < r := by linarith
  -- weak type `(1, 1)` with constant `C` (Randrianantoanina, Theorem 3.1)
  have h₀ : IsWeakType (sumdTransformLM (E := Matrix n n ℝ) σ) 1 C := by
    intro y hy s hs
    have h := hW N n y σ hy hσ hσ1 s hs
    simp only [Real.rpow_one, ENNReal.ofReal_one, sumdTransformLM_apply]
    exact h
  -- weak type `(2, 2)` with constant `1`, from the `L²` isometry
  have h₁ : IsWeakType (sumdTransformLM (E := Matrix n n ℝ) σ) 2 1 := by
    refine isWeakType_of_lpNorm_le two_pos zero_le_one fun y _ => ?_
    rw [one_mul, ENNReal.ofReal_ofNat, sumdTransformLM_apply]
    exact (lpNorm_two_transform hσ hσ1 y).le
  -- Marcinkiewicz between `1` and `2`
  have hM := marcinkiewicz (sumdTransformLM σ) one_pos hr1 hr2 hC.le zero_le_one h₀ h₁ x hx
  simp only [sumdTransformLM_apply, Real.rpow_one, Real.one_rpow] at hM
  -- the constant: `2^r r (C / (r − 1) + 1 / (2 − r)) ≤ 8 (C + 2) / (r − 1)`
  have h2r : (2 : ℝ) ^ r ≤ 4 := by
    calc (2 : ℝ) ^ r ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hr2.le
      _ = 4 := by norm_num
  have hsum : C / (r - 1) + 1 / (2 - r) ≤ (C + 2) / (r - 1) := by
    have h3 : 1 / (2 - r) ≤ 2 / (r - 1) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    calc C / (r - 1) + 1 / (2 - r) ≤ C / (r - 1) + 2 / (r - 1) := by linarith
      _ = (C + 2) / (r - 1) := by rw [add_div]
  have hconst : 2 ^ r * r * (C / (r - 1) + 1 / (2 - r)) ≤ 8 * (C + 2) / (r - 1) := by
    calc 2 ^ r * r * (C / (r - 1) + 1 / (2 - r)) ≤ 2 ^ r * r * ((C + 2) / (r - 1)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 4 * 2 * ((C + 2) / (r - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h2r hr2.le hr0.le (by norm_num))
            (div_nonneg (by linarith) (by linarith))
      _ = 8 * (C + 2) / (r - 1) := by ring
  have hK1 : 1 ≤ 8 * (C + 2) / (r - 1) := by
    rw [one_le_div (by linarith)]
    linarith
  refine sumd_lpNorm_le_of_avg_le (schattenNorm_nonneg _) hr1.le hK1 (hM.trans ?_)
  exact mul_le_mul_of_nonneg_right hconst
    (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _)

/-- Middle regime, `r ∈ [5/3, 5/2]`: a bounded constant (Marcinkiewicz between `3/2` and `3`). -/
theorem lpNorm_transform_le_of_mem_Icc : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 5 / 3 ≤ r → r ≤ 5 / 2 → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  obtain ⟨K₁, hK₁, h1⟩ := lpNorm_transform_le_of_le_five_thirds
  -- the strong `(3/2, 3/2)` and `(3, 3)` bounds have the constant `L = 2 K₁`
  set L := 2 * K₁ with hL_def
  have hL : 0 ≤ L := by positivity
  refine ⟨24 * (6 * L ^ (3 / 2 : ℝ) + 2 * L ^ (3 : ℝ)) + 1, by positivity, ?_⟩
  intro r hr53 hr52 N n _ _ x σ hx hσ hσ1
  have hr1 : 1 ≤ r := by linarith
  -- strong type `(3/2, 3/2)`, from the first regime: `K₁ / (3/2 − 1) = 2 K₁`
  have hs₀ : ∀ y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (y ε).IsHermitian) →
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal (3 / 2))) (3 / 2) (transform σ y) ≤
        L * SignCube.lpNorm (schattenNorm (ENNReal.ofReal (3 / 2))) (3 / 2) y := by
    intro y hy
    have h := h1 (3 / 2) (by norm_num) (by norm_num) N n y σ hy hσ hσ1
    rwa [show K₁ / (3 / 2 - 1) = L by rw [hL_def]; ring] at h
  -- strong type `(3, 3)`, by duality: `(3/2)' = 3`
  have hs₁ : ∀ y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (y ε).IsHermitian) →
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal 3)) 3 (transform σ y) ≤
        L * SignCube.lpNorm (schattenNorm (ENNReal.ofReal 3)) 3 y := by
    intro y hy
    have h := lpNorm_transform_le_of_dual hσ (by norm_num) hs₀ y hy
    rwa [show (3 / 2 : ℝ) / (3 / 2 - 1) = 3 by norm_num] at h
  have h₀ : IsWeakType (sumdTransformLM (E := Matrix n n ℝ) σ) (3 / 2) L :=
    isWeakType_of_lpNorm_le (by norm_num) hL fun y hy => by
      rw [sumdTransformLM_apply]
      exact hs₀ y hy
  have h₁ : IsWeakType (sumdTransformLM (E := Matrix n n ℝ) σ) 3 L :=
    isWeakType_of_lpNorm_le (by norm_num) hL fun y hy => by
      rw [sumdTransformLM_apply]
      exact hs₁ y hy
  -- Marcinkiewicz between `3/2` and `3`
  have hM := marcinkiewicz (sumdTransformLM σ) (by norm_num) (by linarith : (3 / 2 : ℝ) < r)
    (by linarith : r < 3) hL hL h₀ h₁ x hx
  simp only [sumdTransformLM_apply] at hM
  -- the constant: `r − 3/2 ≥ 1/6`, `3 − r ≥ 1/2`, `2^r r ≤ 24`
  have h2r : (2 : ℝ) ^ r ≤ 8 := by
    calc (2 : ℝ) ^ r ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 8 := by norm_num
  have hA : 0 ≤ L ^ (3 / 2 : ℝ) := Real.rpow_nonneg hL _
  have hB : 0 ≤ L ^ (3 : ℝ) := Real.rpow_nonneg hL _
  have ha : L ^ (3 / 2 : ℝ) / (r - 3 / 2) ≤ 6 * L ^ (3 / 2 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb : L ^ (3 : ℝ) / (3 - r) ≤ 2 * L ^ (3 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hconst : 2 ^ r * r * (L ^ (3 / 2 : ℝ) / (r - 3 / 2) + L ^ (3 : ℝ) / (3 - r)) ≤
      24 * (6 * L ^ (3 / 2 : ℝ) + 2 * L ^ (3 : ℝ)) + 1 := by
    have : 2 ^ r * r * (L ^ (3 / 2 : ℝ) / (r - 3 / 2) + L ^ (3 : ℝ) / (3 - r)) ≤
        8 * 3 * (6 * L ^ (3 / 2 : ℝ) + 2 * L ^ (3 : ℝ)) :=
      mul_le_mul (mul_le_mul h2r (by linarith) (by linarith) (by norm_num)) (by linarith)
        (add_nonneg (div_nonneg hA (by linarith)) (div_nonneg hB (by linarith))) (by norm_num)
    linarith
  refine sumd_lpNorm_le_of_avg_le (schattenNorm_nonneg _) hr1 (by linarith) (hM.trans ?_)
  exact mul_le_mul_of_nonneg_right hconst
    (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _)

/-- Third regime, `r ≥ 5/2`: `K r`, by duality from `r' ≤ 5/3`. -/
theorem lpNorm_transform_le_of_five_halves_le : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 5 / 2 ≤ r → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * r * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  obtain ⟨K₁, hK₁, h1⟩ := lpNorm_transform_le_of_le_five_thirds
  refine ⟨K₁, hK₁, ?_⟩
  intro r hr N n _ _ x σ hx hσ hσ1
  have hr1 : 0 < r - 1 := by linarith
  -- the dual exponent `r' = r / (r − 1) ∈ (1, 5/3]`, with `r' − 1 = 1 / (r − 1)` and `r'' = r`
  set r' := r / (r - 1) with hr'_def
  have hr'1 : 1 < r' := by
    rw [hr'_def, lt_div_iff₀ hr1]
    linarith
  have hr'53 : r' ≤ 5 / 3 := by
    rw [hr'_def, div_le_iff₀ hr1]
    linarith
  have he : r' - 1 = 1 / (r - 1) := by
    rw [hr'_def]
    field_simp
    ring
  have hr'' : r' / (r' - 1) = r := by
    rw [he, div_div_eq_mul_div, div_one, hr'_def, div_mul_cancel₀ _ hr1.ne']
  have hd := lpNorm_transform_le_of_dual hσ hr'1
    (fun y hy => h1 r' hr'1 hr'53 N n y σ hy hσ hσ1) x hx
  rw [hr''] at hd
  -- `K₁ / (r' − 1) = K₁ (r − 1) ≤ K₁ r`
  refine hd.trans (mul_le_mul_of_nonneg_right ?_ (lpNorm_nonneg (schattenNorm_nonneg _) _ _))
  rw [he, div_div_eq_mul_div, div_one]
  nlinarith

/-- Martingale transforms by predictable signs on `L^r (S_r)` of the matrix cube, for all real
square matrices: `‖T_σ x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}` with an absolute `K`. -/
theorem lpNorm_transform_le : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ), 1 < r → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * pStar r * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  obtain ⟨K₁, hK₁, h1⟩ := lpNorm_transform_le_of_le_five_thirds
  obtain ⟨K₂, hK₂, h2⟩ := lpNorm_transform_le_of_mem_Icc
  obtain ⟨K₃, hK₃, h3⟩ := lpNorm_transform_le_of_five_halves_le
  set K := K₁ + K₂ + K₃ with hK_def
  -- symmetric matrices: the three regimes, `K₁ / (r − 1) ≤ K r*`, `K₂ ≤ K r*`, `K₃ r ≤ K r*`
  have hH : ∀ (r : ℝ), 1 < r → ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n]
      (x : (Fin N → Bool) → Matrix n n ℝ) (σ : Fin N → (Fin N → Bool) → ℝ),
      (∀ ε, (x ε).IsHermitian) → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
          K * pStar r * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
    intro r hr N n _ _ x σ hx hσ hσ1
    have hP1 := sumd_le_pStar r
    have hP2 := sumd_div_le_pStar r
    have hnx := lpNorm_nonneg (schattenNorm_nonneg (ENNReal.ofReal r)) r x
    rcases le_or_gt r (5 / 3) with hr53 | hr53
    · refine (h1 r hr hr53 N n x σ hx hσ hσ1).trans (mul_le_mul_of_nonneg_right ?_ hnx)
      calc K₁ / (r - 1) ≤ K₁ * (r / (r - 1)) := by
            rw [mul_div_assoc']
            exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
        _ ≤ K * pStar r :=
            mul_le_mul (by linarith) hP2 (div_nonneg (by linarith) (by linarith)) (by linarith)
    rcases le_or_gt r (5 / 2) with hr52 | hr52
    · refine (h2 r hr53.le hr52 N n x σ hx hσ hσ1).trans (mul_le_mul_of_nonneg_right ?_ hnx)
      nlinarith
    · refine (h3 r hr52.le N n x σ hx hσ hσ1).trans (mul_le_mul_of_nonneg_right ?_ hnx)
      nlinarith
  refine ⟨K, by positivity, ?_⟩
  intro r hr N n _ _ x σ hσ hσ1
  have hr0 : 0 < r := by linarith
  -- the Hermitian dilation: `‖D y‖_{L^r (S_r)} = 2^{1/r} ‖y‖_{L^r (S_r)}`
  have hD : ∀ y : (Fin N → Bool) → Matrix n n ℝ,
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (fun ε => dilation (y ε)) =
        2 ^ (1 / r) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r y := by
    intro y
    unfold SignCube.lpNorm
    simp_rw [schattenNorm_dilation_rpow hr0]
    rw [avg_const_mul, Real.mul_rpow zero_le_two
      (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _)]
  -- the dilation commutes with the transform
  have hT : (fun ε => dilation (transform σ x ε)) = transform σ (fun ε => dilation (x ε)) :=
    funext fun ε => map_transform dilationLinearMap σ x ε
  have key := hH r hr N (n ⊕ n) (fun ε => dilation (x ε)) σ (fun ε => dilation_isHermitian _)
    hσ hσ1
  rw [← hT, hD, hD, mul_left_comm] at key
  exact le_of_mul_le_mul_left key (by positivity)

/-- `UMD_q^Δ (S_q^{n×n}) ≤ K q*` with an absolute `K`. -/
theorem dyadicUMDConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      dyadicUMDConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  obtain ⟨K, hK, hT⟩ := lpNorm_transform_le
  refine ⟨K, hK, ?_⟩
  intro q _ hq1 hqt n _ _
  have hr1 := sumd_one_lt_toReal hq1 hqt
  set r := q.toReal with hr_def
  have hrq : ENNReal.ofReal r = q := ENNReal.ofReal_toReal hqt
  apply dyadicUMDConst_le_of_isDyadicUMDBound
  intro N ξ σ hξ hσ hσ1 m
  -- the family stopped at time `m`, `ξ' = 1_{k < m} ξ`, is predictable
  set ξ' : Fin N → (Fin N → Bool) → SchattenSpace q n n :=
    fun k ε => if k.val < m then ξ k ε else 0 with hξ'_def
  have hξ' : IsPredictable ξ' := hξ.stopped (τ := fun _ => m) fun _ _ _ _ => Iff.rfl
  -- `M_m = Σ_k ε_k ξ'_k` and `Σ_{k<m} σ_k ε_k ξ_k = T_σ (Σ_k ε_k ξ'_k)`
  have e1 : paleyWalsh ξ m = paleyWalsh ξ' N := sumd_paleyWalsh_eq_stop ξ m
  have e2 : paleyWalsh (fun k ε => σ k ε • ξ k ε) m = transform σ (paleyWalsh ξ' N) := by
    rw [transform_paleyWalsh hξ' hσ, sumd_paleyWalsh_eq_stop]
    congr 1
    funext k ε
    simp only [hξ'_def, smul_ite, smul_zero]
  -- read through `SchattenSpace.ofMatrix` as a matrix-valued function
  set x : (Fin N → Bool) → Matrix n n ℝ :=
    fun ε => (SchattenSpace.ofMatrix (q := q)).symm (paleyWalsh ξ' N ε) with hx_def
  have hx : ∀ ε, (SchattenSpace.ofMatrix (q := q)).symm (transform σ (paleyWalsh ξ' N) ε) =
      transform σ x ε := fun ε =>
    map_transform (SchattenSpace.ofMatrix (q := q) (m := n) (n := n)).symm.toLinearMap σ _ ε
  have hn1 : SignCube.lpNorm (fun v => ‖v‖) r (paleyWalsh ξ' N) =
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
    have h : (fun ε => ‖paleyWalsh ξ' N ε‖ ^ r) = fun ε => schattenNorm q (x ε) ^ r :=
      funext fun ε => by rw [SchattenSpace.norm_def]
    rw [hrq]
    unfold SignCube.lpNorm
    rw [h]
  have hn2 : SignCube.lpNorm (fun v => ‖v‖) r (transform σ (paleyWalsh ξ' N)) =
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) := by
    have h : (fun ε => ‖transform σ (paleyWalsh ξ' N) ε‖ ^ r) =
        fun ε => schattenNorm q (transform σ x ε) ^ r :=
      funext fun ε => by rw [SchattenSpace.norm_def, hx ε]
    rw [hrq]
    unfold SignCube.lpNorm
    rw [h]
  rw [e1, e2, hn1, hn2, ← ENNReal.ofReal_mul
    (mul_nonneg hK.le ((zero_le_one.trans hr1.le).trans (sumd_le_pStar r)))]
  exact ENNReal.ofReal_le_ofReal (hT r hr1 N n x σ hσ hσ1)

/-- **Schatten classes are UMD** (Randrianantoanina 2002, Theorem 4.3 and Corollary 4.5):
`UMD_q (S_q^{n×n}) ≤ K q*` with an absolute `K`, for every `q ∈ (1, ∞)` and every `n`. -/
theorem umdConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  obtain ⟨K, hK, h⟩ := dyadicUMDConst_schattenSpace_le
  refine ⟨K, hK, fun q _ hq1 hqt n _ _ => ?_⟩
  -- Maurey's theorem: `UMD_q^Δ = UMD_q`
  rw [← dyadicUMDConst_eq_umdConst (sumd_one_lt_toReal hq1 hqt)]
  exact h q hq1 hqt n

/-- **`UMD₂` of Schatten classes** (Randrianantoanina 2002, Corollary 4.5 and Remark 4.6 (1)): there
is an absolute `C` with `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` for every `q ∈ (1, ∞)` and every `n`. -/
theorem umdConst_two_schattenSpace_le : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) 2 ≤ ENNReal.ofReal (C * (pStar q.toReal - 1)) := by
  obtain ⟨K, hK, h⟩ := umdConst_schattenSpace_le
  refine ⟨400 * K, by positivity, fun q _ hq1 hqt n _ _ => ?_⟩
  have hr1 := sumd_one_lt_toReal hq1 hqt
  have hP := sumd_two_le_pStar hr1
  -- extrapolation `UMD₂ ≤ 200 UMD_q`, then `q* ≤ 2 (q* − 1)`
  calc umdConst (SchattenSpace q n n) 2 ≤ 200 * umdConst (SchattenSpace q n n) q.toReal :=
        umdConst_two_le_mul hr1
    _ ≤ 200 * ENNReal.ofReal (K * pStar q.toReal) := by
        gcongr
        exact h q hq1 hqt n
    _ = ENNReal.ofReal (200 * (K * pStar q.toReal)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (400 * K * (pStar q.toReal - 1)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)

end BanachProbability
