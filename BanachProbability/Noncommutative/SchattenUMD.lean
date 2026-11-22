module

public import BanachProbability.Noncommutative.WeakType
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

The route, for a general filtration `ℱ` of a probability space, on
`𝒩 = L^∞ (Ω) ⊗ M_n (ℝ)` with the conditional expectations `E_k = 𝔼 [· | ℱ_k] ⊗ Id` and the
transforms `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` by predictable scalar multipliers
`|c_k| ≤ 1`:

1. **Theorem 4.3**, `‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}` (`eLpNorm_ncTransform_le`).
   The endpoints are the weak type `(1, 1)` bound of Theorem 3.1 with constant `52`
   (`isWeakTypeNC_one_ncTransform`, from `weakType_one_one`) and the `L²` contraction
   (`isStrongTypeNC_two_ncTransform`, from `matrixTrace_ncTransform_le` and
   `‖A‖_{S_2}² = tr (Aᵀ A)`). The source's "by interpolation" for `1 < r < 2` and "by duality" for
   `r > 2` are carried out in three regimes, with real methods only, so that the constant stays
   uniform: for `r ∈ (1, 5/3]`, Marcinkiewicz between `1` and `2` gives `432 / (r − 1)`
   (`isStrongTypeNC_ncTransform_of_le_five_thirds`); for `r ∈ [5/3, 5/2]`, Marcinkiewicz between
   `3/2` (first regime) and `3` (from `3/2` by duality, `isStrongTypeNC_ncTransform_dual`) gives
   a bounded constant (`isStrongTypeNC_ncTransform_of_mem_Icc`); for `r ≥ 5/2`, duality from
   `r' ≤ 5/3` gives `432 (r − 1)` (`isStrongTypeNC_ncTransform_of_five_halves_le`). A direct
   weak-`(1, 1)`/`L²` interpolation would degenerate like `(2 − r)^{−1/2}` near `r = 2`; the
   middle regime is what keeps the constant uniform there. This fills in the details of the step
   "by interpolation" of the source, which it does not give.
2. General real matrices through the Hermitian dilation `D (A) = [[0, A], [Aᵀ, 0]]`
   (`dilation`, `‖D (A)‖_{S_r}^r = 2 ‖A‖_{S_r}^r`): every entry of `D (x)` is an entry of `x` or
   `0`, so `E_k (D x) = D (E_k x)` exactly, hence `T_c (D x) = D (T_c x)`.
3. **Corollary 4.5**, `UMD_q (S_q^{n×n}) ≤ K q*` (`isUMDBound_schattenSpace`), directly for
   martingales on an arbitrary filtered probability space, as in the source's proof: an
   `S_q^n`-valued martingale `(Y_k)` with `Y_0 = 0` is, entrywise, a martingale of `𝒩` for
   `E_k = 𝔼 [· | ℱ_k] ⊗ Id`, so that `Y_k = E_k (Y_n)` for `k ≤ n` and the transform
   `Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)` by predictable signs is `T_c (Y_n)` with `c_k = σ_{k+1}`; and
   `L^q (𝒩) = L^q (μ; S_q^n)` holds by definition of the norms. No passage through the dyadic
   constant (Maurey's theorem) is needed.
4. **Remark 4.6 (1)**: the extrapolation `UMD₂ ≤ 200 UMD_q` (`umdConst_two_le_mul`;
   Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016), Theorem 4.2.7), with an
   absolute constant, and `q* − 1 ≥ q* / 2`. The dyadic constant follows from
   `UMD_q^Δ ≤ UMD_q` (`dyadicUMDConst_le_umdConst`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

section Helpers

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

/-- `X^{1/r} ≤ M` for `0 ≤ X ≤ M`, `M ≥ 1` and `r ≥ 1`. -/
private theorem sumd_rpow_one_div_le {X M r : ℝ} (hX : 0 ≤ X) (hXM : X ≤ M) (hM : 1 ≤ M)
    (hr : 1 ≤ r) : X ^ (1 / r) ≤ M :=
  calc X ^ (1 / r) ≤ M ^ (1 / r) := Real.rpow_le_rpow hX hXM (by positivity)
    _ ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (div_le_one_of_le₀ hr (by linarith))
    _ = M := Real.rpow_one M

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- A strong type bound holds for every larger constant. -/
private theorem sumd_isStrongTypeNC_mono {T : (Ω → Matrix n n ℝ) → Ω → Matrix n n ℝ} {r K K' : ℝ}
    (h : IsStrongTypeNC μ m T r K) (hK : K ≤ K') : IsStrongTypeNC μ m T r K' :=
  fun x hxm hx hxr => (h x hxm hx hxr).trans (by gcongr)

end Helpers

/-! ### Theorem 4.3: transforms on `L^r (L^∞ (Ω) ⊗ M_n)` -/

section Transform

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n] {ℱ : Filtration ℕ mΩ} {c : ℕ → Ω → ℝ} {N : ℕ}

/-- `‖A‖_{S_2}² = tr (Aᵀ A)`. -/
private theorem sumd_schattenNorm_two_sq (A : Matrix n n ℝ) :
    ‖schattenNorm 2 A‖ ^ (2 : ℝ≥0∞).toReal = (Aᵀ * A).trace := by
  rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _), ENNReal.toReal_ofNat, Real.rpow_two,
    schattenNorm_two_sq, Finset.sum_comm]
  simp [Matrix.trace, Matrix.mul_apply, sq]

/-- Weak type `(1, 1)` with constant `52` (Randrianantoanina 2002, Theorem 3.1). -/
theorem isWeakTypeNC_one_ncTransform [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) :
    IsWeakTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) 1 52 := by
  intro x hxm hx hx1 s hs
  rw [ENNReal.ofReal_one] at hx1 ⊢
  simp only [Real.rpow_one]
  exact weakType_one_one hxm hx1 hx hc hc1 hs

/-- Strong type `(2, 2)` with constant `1`: the `L²` contraction. -/
theorem isStrongTypeNC_two_ncTransform [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) 2 1 := by
  intro x hxm _ hx2
  rw [ENNReal.ofReal_ofNat] at hx2 ⊢
  rw [ENNReal.ofReal_one, one_mul]
  have hf := (hx2.ncTransform (N := N) hc hc1 one_le_two).memLp_schattenNorm (q := 2) one_le_two
  have hg := hx2.memLp_schattenNorm (q := 2) one_le_two
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity))
  simp only [sumd_schattenNorm_two_sq]
  exact matrixTrace_ncTransform_le hc hc1 hxm hx2

/-- **First regime**, `r ∈ (1, 5/3]`: strong type `(r, r)` with constant `432 / (r − 1)`
(Marcinkiewicz between weak `(1, 1)` and strong `(2, 2)`). -/
theorem isStrongTypeNC_ncTransform_of_le_five_thirds [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {r : ℝ} (hr1 : 1 < r)
    (hr53 : r ≤ 5 / 3) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r (432 / (r - 1)) := by
  have hr2 : r < 2 := by linarith
  have hr0 : 0 < r := by linarith
  have hT : ∀ x : Ω → Matrix n n ℝ, Measurable (ncTransform ℱ μ c N x) :=
    fun x => (measurable_ncTransform hc x).mono (ℱ.le N) le_rfl
  have hM := marcinkiewicz (T := ncTransform ℱ μ c N) (ℱ.le N) hT
    (fun x y hx hy => ncTransform_add hx hy) le_rfl hr1 hr2 (by norm_num : (0 : ℝ) ≤ 52)
    zero_le_one (isWeakTypeNC_one_ncTransform hc hc1)
    ((isStrongTypeNC_two_ncTransform hc hc1).isWeakTypeNC hT one_le_two zero_le_one)
  refine sumd_isStrongTypeNC_mono hM ?_
  rw [Real.rpow_one, Real.one_rpow]
  -- `2^r r (52 / (r − 1) + 1 / (2 − r)) ≤ 8 · 54 / (r − 1)`
  have h2r : (2 : ℝ) ^ r ≤ 4 := by
    calc (2 : ℝ) ^ r ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hr2.le
      _ = 4 := by norm_num
  have hsum : 52 / (r - 1) + 1 / (2 - r) ≤ 54 / (r - 1) := by
    have h3 : 1 / (2 - r) ≤ 2 / (r - 1) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    calc 52 / (r - 1) + 1 / (2 - r) ≤ 52 / (r - 1) + 2 / (r - 1) := by linarith
      _ = 54 / (r - 1) := by ring
  have hsum0 : 0 ≤ 52 / (r - 1) + 1 / (2 - r) :=
    add_nonneg (div_nonneg (by norm_num) (by linarith)) (div_nonneg zero_le_one (by linarith))
  have hX : 2 ^ r * r * (52 / (r - 1) + 1 / (2 - r)) ≤ 432 / (r - 1) := by
    calc 2 ^ r * r * (52 / (r - 1) + 1 / (2 - r)) ≤ 4 * 2 * (54 / (r - 1)) :=
          mul_le_mul (mul_le_mul h2r hr2.le hr0.le (by norm_num)) hsum hsum0 (by norm_num)
      _ = 432 / (r - 1) := by ring
  refine sumd_rpow_one_div_le (mul_nonneg (by positivity) hsum0) hX ?_ hr1.le
  rw [one_le_div (by linarith)]
  linarith

/-- **Middle regime**, `r ∈ [5/3, 5/2]`: strong type `(r, r)` with the absolute constant
`192 · 864³` (Marcinkiewicz between `3/2`, from the first regime, and `3`, from `3/2` by
duality). -/
theorem isStrongTypeNC_ncTransform_of_mem_Icc [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {r : ℝ}
    (hr53 : 5 / 3 ≤ r) (hr52 : r ≤ 5 / 2) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r (192 * 864 ^ 3) := by
  have hT : ∀ x : Ω → Matrix n n ℝ, Measurable (ncTransform ℱ μ c N x) :=
    fun x => (measurable_ncTransform hc x).mono (ℱ.le N) le_rfl
  -- strong type `(3/2, 3/2)`, from the first regime: `432 / (3/2 − 1) = 864`
  have hs₀ : IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) (3 / 2) 864 := by
    have h := isStrongTypeNC_ncTransform_of_le_five_thirds (μ := μ) (n := n) (N := N) hc hc1
      (r := 3 / 2) (by norm_num) (by norm_num)
    rwa [show (432 : ℝ) / (3 / 2 - 1) = 864 by norm_num] at h
  -- strong type `(3, 3)`, by duality: `(3/2)' = 3`
  have hs₁ : IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) 3 864 := by
    have h := isStrongTypeNC_ncTransform_dual (μ := μ) hc hc1 (by norm_num) hs₀
    rwa [show (3 / 2 : ℝ) / (3 / 2 - 1) = 3 by norm_num] at h
  have hM := marcinkiewicz (T := ncTransform ℱ μ c N) (ℱ.le N) hT
    (fun x y hx hy => ncTransform_add hx hy) (by norm_num) (by linarith : (3 / 2 : ℝ) < r)
    (by linarith : r < 3) (by norm_num : (0 : ℝ) ≤ 864) (by norm_num : (0 : ℝ) ≤ 864)
    (hs₀.isWeakTypeNC hT (by norm_num) (by norm_num))
    (hs₁.isWeakTypeNC hT (by norm_num) (by norm_num))
  refine sumd_isStrongTypeNC_mono hM ?_
  -- the constant: `r − 3/2 ≥ 1/6`, `3 − r ≥ 1/2`, `2^r r ≤ 24`, `864^{3/2} ≤ 864^3`
  set A := (864 : ℝ) ^ (3 / 2 : ℝ)
  set B := (864 : ℝ) ^ (3 : ℝ) with hB_def
  have hA : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
  have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hB : B = 864 ^ 3 := by
    rw [hB_def, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2r : (2 : ℝ) ^ r ≤ 8 := by
    calc (2 : ℝ) ^ r ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 8 := by norm_num
  have ha : A / (r - 3 / 2) ≤ 6 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb : B / (3 - r) ≤ 2 * B := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsum0 : 0 ≤ A / (r - 3 / 2) + B / (3 - r) :=
    add_nonneg (div_nonneg hA (by linarith)) (div_nonneg (hA.trans hAB) (by linarith))
  have hX : 2 ^ r * r * (A / (r - 3 / 2) + B / (3 - r)) ≤ 192 * 864 ^ 3 := by
    calc 2 ^ r * r * (A / (r - 3 / 2) + B / (3 - r)) ≤ 8 * 3 * (6 * A + 2 * B) :=
          mul_le_mul (mul_le_mul h2r (by linarith) (by linarith) (by norm_num))
            (by linarith) hsum0 (by norm_num)
      _ ≤ 192 * 864 ^ 3 := by rw [← hB]; nlinarith
  exact sumd_rpow_one_div_le (mul_nonneg (by positivity) hsum0) hX (by norm_num) (by linarith)

/-- **Third regime**, `r ≥ 5/2`: strong type `(r, r)` with constant `432 (r − 1)`, by duality
from `r' = r / (r − 1) ∈ (1, 5/3]`. -/
theorem isStrongTypeNC_ncTransform_of_five_halves_le [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {r : ℝ}
    (hr : 5 / 2 ≤ r) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r (432 * (r - 1)) := by
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
  have h := isStrongTypeNC_ncTransform_dual (μ := μ) hc hc1 hr'1
    (isStrongTypeNC_ncTransform_of_le_five_thirds (n := n) (N := N) hc hc1 hr'1 hr'53)
  rwa [hr'', he, div_div_eq_mul_div, div_one] at h

/-- **Theorem 4.3** for symmetric functions: strong type `(r, r)` with constant
`192 · 864³ · r*`, for every `r ∈ (1, ∞)`, from the three regimes. The source obtains
`1 < r < 2` "by interpolation" from Theorem 3.1 and the `L²` bound, and `r > 2` "by duality"; a
direct weak-`(1, 1)`/`L²` Marcinkiewicz interpolation degenerates like `(2 − r)^{−1/2}` near
`r = 2`, and the middle regime (interpolation between `3/2` and `3`) fills this gap. -/
theorem isStrongTypeNC_ncTransform [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {r : ℝ} (hr : 1 < r) :
    IsStrongTypeNC μ (ℱ N) (ncTransform (n := n) ℱ μ c N) r (192 * 864 ^ 3 * pStar r) := by
  have hP1 := sumd_le_pStar r
  have hP2 := sumd_div_le_pStar r
  have hP := sumd_two_le_pStar hr
  rcases le_or_gt r (5 / 3) with hr53 | hr53
  · -- `432 / (r − 1) ≤ 432 r / (r − 1) ≤ 192 · 864³ · r*`
    refine sumd_isStrongTypeNC_mono
      (isStrongTypeNC_ncTransform_of_le_five_thirds hc hc1 hr hr53) ?_
    have h1 : 432 / (r - 1) ≤ 432 * (r / (r - 1)) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
    have h2 : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
    nlinarith
  rcases le_or_gt r (5 / 2) with hr52 | hr52
  · exact sumd_isStrongTypeNC_mono
      (isStrongTypeNC_ncTransform_of_mem_Icc hc hc1 hr53.le hr52) (by nlinarith)
  · exact sumd_isStrongTypeNC_mono
      (isStrongTypeNC_ncTransform_of_five_halves_le hc hc1 hr52.le) (by nlinarith)

/-! #### The Hermitian dilation -/

omit [Fintype n] [DecidableEq n] in
private theorem sumd_measurable_dilation :
    Measurable (dilation : Matrix n n ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · exact measurable_const
  · exact Matrix.measurable_apply
  · exact Matrix.measurable_apply
  · exact measurable_const

omit [Fintype n] [DecidableEq n] in
private theorem sumd_matrixMemLp_dilation {x : Ω → Matrix n n ℝ} {p : ℝ≥0∞}
    (hx : MatrixMemLp x p μ) : MatrixMemLp (fun ω => dilation (x ω)) p μ := by
  rintro (i | i) (j | j)
  · exact MemLp.zero'
  · exact hx i j
  · exact hx j i
  · exact MemLp.zero'

omit [Fintype n] [DecidableEq n] in
/-- `E_m (D x) = D (E_m x)`: every entry of `D x` is an entry of `x` or `0`. -/
private theorem sumd_matrixCondExp_dilation (m : MeasurableSpace Ω) (x : Ω → Matrix n n ℝ) :
    matrixCondExp m μ (fun ω => dilation (x ω)) = fun ω => dilation (matrixCondExp m μ x ω) := by
  funext ω
  ext (i | i) (j | j)
  · change μ[(0 : Ω → ℝ) | m] ω = 0
    rw [condExp_zero, Pi.zero_apply]
  · rfl
  · rfl
  · change μ[(0 : Ω → ℝ) | m] ω = 0
    rw [condExp_zero, Pi.zero_apply]

omit [Fintype n] [DecidableEq n] in
/-- `T_c (D x) = D (T_c x)`. -/
private theorem sumd_ncTransform_dilation (x : Ω → Matrix n n ℝ) :
    ncTransform ℱ μ c N (fun ω => dilation (x ω)) =
      fun ω => dilation (ncTransform ℱ μ c N x ω) := by
  funext ω
  simp only [ncTransform, sumd_matrixCondExp_dilation]
  change _ = dilationLinearMap _
  simp only [map_add, map_sum, map_smul, map_sub]
  rfl

/-- `‖D (A)‖_{S_r} = 2^{1/r} ‖A‖_{S_r}`, in `L^r`. -/
private theorem sumd_eLpNorm_dilation {r : ℝ} (hr : 0 < r) (y : Ω → Matrix n n ℝ) :
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (dilation (y ω))) (ENNReal.ofReal r) μ =
      ENNReal.ofReal (2 ^ r⁻¹) *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (y ω)) (ENNReal.ofReal r) μ := by
  have h : ∀ A : Matrix n n ℝ, schattenNorm (ENNReal.ofReal r) (dilation A) =
      2 ^ r⁻¹ * schattenNorm (ENNReal.ofReal r) A := fun A => by
    rw [← Real.rpow_rpow_inv (schattenNorm_nonneg _ (dilation A)) hr.ne',
      schattenNorm_dilation_rpow hr, Real.mul_rpow zero_le_two
        (Real.rpow_nonneg (schattenNorm_nonneg _ _) _),
      Real.rpow_rpow_inv (schattenNorm_nonneg _ _) hr.ne']
  simp only [h]
  have := eLpNorm_const_smul (2 ^ r⁻¹ : ℝ) (fun ω => schattenNorm (ENNReal.ofReal r) (y ω))
    (ENNReal.ofReal r) μ
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg zero_le_two _)] at this
  exact this

/-- **Theorem 4.3** (Randrianantoanina 2002): martingale transforms by predictable scalar
multipliers `|c_k| ≤ 1` are bounded on `L^r (L^∞ (Ω) ⊗ M_n)`, for all real matrices,
`‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}` with the absolute constant `K = 192 · 864³`, for every
`r ∈ (1, ∞)` and every `n` (the source's `c_r ≤ C r² / (r − 1)`, as `r* ≤ r² / (r − 1)`). -/
theorem eLpNorm_ncTransform_le [IsProbabilityMeasure μ]
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) {r : ℝ} (hr : 1 < r)
    {x : Ω → Matrix n n ℝ} (hxm : Measurable[ℱ N] x) (hxr : MatrixMemLp x (ENNReal.ofReal r) μ) :
    eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (ncTransform ℱ μ c N x ω))
        (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (192 * 864 ^ 3 * pStar r) *
        eLpNorm (fun ω => schattenNorm (ENNReal.ofReal r) (x ω)) (ENNReal.ofReal r) μ := by
  have hr0 : 0 < r := by linarith
  -- the symmetric case for the dilation `D x`, and `T_c (D x) = D (T_c x)`
  have key := isStrongTypeNC_ncTransform (n := n ⊕ n) (N := N) hc hc1 hr
    (fun ω => dilation (x ω)) (sumd_measurable_dilation.comp hxm)
    (fun ω => dilation_isHermitian _) (sumd_matrixMemLp_dilation hxr)
  simp only [sumd_ncTransform_dilation] at key
  rw [sumd_eLpNorm_dilation hr0, sumd_eLpNorm_dilation hr0, mul_left_comm] at key
  exact (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos two_pos _)).ne' ENNReal.ofReal_ne_top).1 key

end Transform

/-! ### Corollary 4.5: Schatten classes are UMD -/

/-- **Corollary 4.5** (Randrianantoanina 2002): `‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^q (S_q)} ≤
K q* ‖Y_n‖_{L^q (S_q)}`, `K = 192 · 864³`, for every `S_q^{n×n}`-valued martingale `Y` with
`Y_0 = 0` on any filtered probability space and predictable signs `σ`: entrywise, `Y` is a
martingale of `L^∞ (Ω) ⊗ M_n` for `E_k = 𝔼 [· | ℱ_k] ⊗ Id`, so `Y_k = E_k (Y_n)` and the transform
is `T_c (Y_n)`, `c_k = σ_{k+1}` (Theorem 4.3). -/
theorem isUMDBound_schattenSpace (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hqt : q ≠ ⊤)
    (n : Type) [Fintype n] [DecidableEq n] :
    IsUMDBound (SchattenSpace q n n) q.toReal
      (ENNReal.ofReal (192 * 864 ^ 3 * pStar q.toReal)) := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm N
  have hr1 := sumd_one_lt_toReal hq1 hqt
  set r := q.toReal
  have hrq : ENNReal.ofReal r = q := ENNReal.ofReal_toReal hqt
  have hK : 0 < 192 * 864 ^ 3 * pStar r := by
    have := sumd_two_le_pStar hr1
    positivity
  -- if `Y_N ∉ L^q`, the bound is trivial
  by_cases hYn : eLpNorm (fun ω => ‖Y N ω‖) (ENNReal.ofReal r) μ = ⊤
  · rw [hYn, ENNReal.mul_top (ENNReal.ofReal_pos.2 hK).ne']
    exact le_top
  -- the entries of `Y` are real martingales
  set E : n → n → SchattenSpace q n n →L[ℝ] ℝ := fun i j =>
    LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℝ i j).comp (SchattenSpace.ofMatrix (q := q)).symm.toLinearMap)
  have hYm : ∀ i j, Martingale (fun k ω => E i j (Y k ω)) ℱ μ :=
    fun i j => martingale_map_continuousLinearMap hY (E i j)
  -- `x = Y_N` as a matrix-valued function: `ℱ_N`-measurable and in `L^q`
  set x : Ω → Matrix n n ℝ := fun ω => (SchattenSpace.ofMatrix (q := q)).symm (Y N ω)
  have hxm : Measurable[ℱ N] x := @Measurable.of_eval_matrix n n ℝ _ Ω (ℱ N) x fun i j =>
    ((E i j).continuous.comp_stronglyMeasurable (hY.stronglyAdapted N)).measurable
  have hYN : MemLp (Y N) (ENNReal.ofReal r) μ := by
    rw [memLp_iff,
      ← eLpNorm_norm _ ((hY.stronglyAdapted N).mono (ℱ.le N)).aestronglyMeasurable]
    exact lt_top_iff_ne_top.2 hYn
  have hxr : MatrixMemLp x (ENNReal.ofReal r) μ := fun i j => (E i j).comp_memLp' hYN
  -- `E_k x = Y_k` a.e. for `k ≤ N`
  have hcond : ∀ k, k ≤ N → matrixCondExp (ℱ k) μ x =ᵐ[μ]
      fun ω => (SchattenSpace.ofMatrix (q := q)).symm (Y k ω) := by
    intro k hk
    have h : ∀ᵐ ω ∂μ, ∀ i j, matrixCondExp (ℱ k) μ x ω i j =
        (SchattenSpace.ofMatrix (q := q)).symm (Y k ω) i j := by
      refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
      exact (hYm i j).condExp_ae_eq hk
    filter_upwards [h] with ω hω
    ext i j
    exact hω i j
  have hall : ∀ᵐ ω ∂μ, ∀ k, k ≤ N →
      matrixCondExp (ℱ k) μ x ω = (SchattenSpace.ofMatrix (q := q)).symm (Y k ω) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : k ≤ N
    · filter_upwards [hcond k hk] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  -- the transform of `Y` is `T_c x`, `c_k = σ_{k+1}`
  have hT : ∀ᵐ ω ∂μ, ‖∑ k ∈ Finset.range N, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖ =
      schattenNorm (ENNReal.ofReal r) (ncTransform ℱ μ (fun k => σ (k + 1)) N x ω) := by
    filter_upwards [hall] with ω hω
    rw [SchattenSpace.norm_def, hrq]
    congr 1
    have e : ncTransform ℱ μ (fun k => σ (k + 1)) N x ω = ∑ k ∈ Finset.range N,
        σ (k + 1) ω • ((SchattenSpace.ofMatrix (q := q)).symm (Y (k + 1) ω) -
          (SchattenSpace.ofMatrix (q := q)).symm (Y k ω)) := by
      simp only [ncTransform]
      rw [hω 0 (Nat.zero_le _), hY0 ω, map_zero, zero_add]
      exact Finset.sum_congr rfl fun k hk => by
        rw [hω (k + 1) (Finset.mem_range.1 hk), hω k (Finset.mem_range.1 hk).le]
    rw [e, map_sum]
    simp only [map_smul, map_sub]
  have hc1 : ∀ k ω, |σ (k + 1) ω| ≤ 1 := fun k ω => by
    rcases hσ (k + 1) ω with h | h <;> simp [h]
  rw [eLpNorm_congr_ae hT]
  have hxn : (fun ω => ‖Y N ω‖) = fun ω => schattenNorm (ENNReal.ofReal r) (x ω) := by
    funext ω
    rw [SchattenSpace.norm_def, hrq]
  rw [hxn]
  exact eLpNorm_ncTransform_le hσm hc1 hr1 hxm hxr

/-- **Schatten classes are UMD** (Randrianantoanina 2002, Theorem 4.3 and Corollary 4.5):
`UMD_q (S_q^{n×n}) ≤ K q*` with an absolute `K`, for every `q ∈ (1, ∞)` and every `n`. -/
theorem umdConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) :=
  ⟨192 * 864 ^ 3, by norm_num, fun q _ hq1 hqt n _ _ =>
    umdConst_le_of_isUMDBound (isUMDBound_schattenSpace q hq1 hqt n)⟩

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

/-- `UMD_q^Δ (S_q^{n×n}) ≤ K q*` with an absolute `K`. -/
theorem dyadicUMDConst_schattenSpace_le : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      dyadicUMDConst (SchattenSpace q n n) q.toReal ≤ ENNReal.ofReal (K * pStar q.toReal) := by
  obtain ⟨K, hK, h⟩ := umdConst_schattenSpace_le
  exact ⟨K, hK, fun q _ hq1 hqt n _ _ =>
    (dyadicUMDConst_le_umdConst (sumd_one_lt_toReal hq1 hqt)).trans (h q hq1 hqt n)⟩

end BanachProbability
