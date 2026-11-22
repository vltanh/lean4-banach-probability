module

public import BanachProbability.Noncommutative.MatrixCube
public import BanachProbability.Schatten.Holder

/-!
# Duality for martingale transforms on the matrix cube

* Hölder's inequality and its equality case in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}`
  for symmetric-matrix-valued `x`, `y` (`cubeTrace_mul_le`), with equality for a norming function
  built from `normingElement` (`exists_cubeTrace_mul_eq`).
* A transform by predictable scalar signs is self-adjoint for `τ (x y)`:
  `τ (T_σ x · y) = τ (x · T_σ y)` (`cubeTrace_transform_mul`), by the orthogonality of martingale
  differences and the bimodule property (the signs are scalar and predictable).
* Hence a strong `(r, r)` bound for `T_σ` on symmetric-matrix-valued functions gives the strong
  `(r', r')` bound with the same constant (`lpNorm_transform_le_of_dual`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Hölder's inequality in `L^r (τ)`: `τ (x y) ≤ ‖x‖_{L^r} ‖y‖_{L^{r'}}`, `r' = r / (r − 1)`. -/
theorem cubeTrace_mul_le {x y : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (hy : ∀ ε, (y ε).IsHermitian) {r : ℝ} (hr : 1 < r) :
    cubeTrace (fun ε => x ε * y ε) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x *
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) y := by
  have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
  have hS : ∀ (q : ℝ≥0∞) (A : Matrix n n ℝ), 0 ≤ schattenNorm q A :=
    fun q A => schattenNorm_nonneg q A
  -- the pointwise trace Hölder inequality
  have hpt : ∀ ε, (x ε * y ε).trace ≤
      schattenNorm (ENNReal.ofReal r) (x ε) * schattenNorm (ENNReal.ofReal (r / (r - 1))) (y ε) :=
    fun ε => (le_abs_self _).trans (abs_trace_mul_le_of_isHermitian (hx ε) (hy ε) hr)
  have h2 : ((2 : ℝ) ^ N) ^ (1 / r) * ((2 : ℝ) ^ N) ^ (1 / (r / (r - 1))) = 2 ^ N := by
    rw [← Real.rpow_add (by positivity), one_div, one_div, hpq.inv_add_inv_eq_one, Real.rpow_one]
  rw [scb_lpNorm_eq_sum (hS _), scb_lpNorm_eq_sum (hS _), div_mul_div_comm, h2]
  unfold cubeTrace avg
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  -- the scalar Hölder inequality for the sum over the cube
  exact (Finset.sum_le_sum fun ε _ => hpt ε).trans
    (Real.inner_le_Lp_mul_Lq_of_nonneg _ hpq (fun ε _ => hS _ _) (fun ε _ => hS _ _))

/-- A function in `L^p (τ)` with zero norm vanishes. -/
private theorem ipd_eq_zero_of_lpNorm_eq_zero {p : ℝ} (hp : 0 < p)
    {x : (Fin N → Bool) → Matrix n n ℝ}
    (h : SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p x = 0) : x = 0 := by
  have hS : ∀ ε, 0 ≤ schattenNorm (ENNReal.ofReal p) (x ε) ^ p :=
    fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  rw [SignCube.lpNorm, Real.rpow_eq_zero_iff_of_nonneg (avg_nonneg hS), avg,
    div_eq_zero_iff] at h
  have hsum := h.1.resolve_right (by positivity)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun ε _ => hS ε] at hsum
  funext ε
  have := hsum ε (Finset.mem_univ _)
  rw [Real.rpow_eq_zero_iff_of_nonneg (schattenNorm_nonneg _ _)] at this
  exact (schattenNorm_eq_zero_iff (ENNReal.ofReal_pos.2 hp).ne').1 this.1

/-- The `L^p (τ)` norm of `0`. -/
private theorem ipd_lpNorm_zero {p : ℝ} (hp : 0 < p) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p
      (0 : (Fin N → Bool) → Matrix n n ℝ) = 0 := by
  simp [SignCube.lpNorm, schattenNorm_zero (ENNReal.ofReal_pos.2 hp).ne', Real.zero_rpow hp.ne',
    Real.zero_rpow (inv_pos.2 hp).ne']

/-- The norming function of `x` in `L^r (τ)`: a symmetric-matrix-valued `y` with
`‖y‖_{L^{r'}} ≤ 1` and `τ (x y) = ‖x‖_{L^r}`. -/
theorem exists_cubeTrace_mul_eq {x : (Fin N → Bool) → Matrix n n ℝ}
    (hx : ∀ ε, (x ε).IsHermitian) {r : ℝ} (hr : 1 < r) :
    ∃ y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (y ε).IsHermitian) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) y ≤ 1 ∧
      cubeTrace (fun ε => x ε * y ε) = SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr' : 0 < r / (r - 1) := div_pos hr0 hr1
  have hS : ∀ (q : ℝ≥0∞) (A : Matrix n n ℝ), 0 ≤ schattenNorm q A :=
    fun q A => schattenNorm_nonneg q A
  have hA : 0 ≤ avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r :=
    avg_nonneg fun ε => Real.rpow_nonneg (hS _ _) _
  set L := SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x with hL
  have hLr : L ^ r = avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
    rw [hL, SignCube.lpNorm, ← Real.rpow_mul hA, one_div_mul_cancel hr0.ne', Real.rpow_one]
  have hL0 : 0 ≤ L := lpNorm_nonneg (hS (ENNReal.ofReal r)) r x
  rcases hL0.eq_or_lt with hL0 | hLpos
  · -- `‖x‖_{L^r} = 0`: take `y = 0`
    refine ⟨0, fun ε => Matrix.isHermitian_zero, (ipd_lpNorm_zero hr').trans_le zero_le_one, ?_⟩
    rw [← hL0]
    simp [cubeTrace, avg]
  · -- `y = c⁻¹ • normingElement r x`, `c = ‖x‖_{L^r}^{r−1}`
    have hc : 0 < L ^ (r - 1) := Real.rpow_pos_of_pos hLpos _
    refine ⟨fun ε => (L ^ (r - 1))⁻¹ • normingElement r (x ε),
      fun ε => (isHermitian_normingElement r (x ε)).smul (IsSelfAdjoint.all _), le_of_eq ?_, ?_⟩
    · have hpt : ∀ ε, schattenNorm (ENNReal.ofReal (r / (r - 1)))
          ((L ^ (r - 1))⁻¹ • normingElement r (x ε)) ^ (r / (r - 1)) =
          ((L ^ (r - 1))⁻¹) ^ (r / (r - 1)) * schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
        intro ε
        rw [schattenNorm_smul (ENNReal.ofReal_pos.2 hr').ne', schattenNorm_normingElement (hx ε) hr,
          abs_of_pos (inv_pos.2 hc), Real.mul_rpow (inv_pos.2 hc).le (Real.rpow_nonneg (hS _ _) _),
          ← Real.rpow_mul (hS _ _), mul_div_cancel₀ _ hr1.ne']
      simp only [SignCube.lpNorm, hpt]
      rw [avg_const_mul, ← hLr, Real.mul_rpow (Real.rpow_nonneg (inv_pos.2 hc).le _)
        (Real.rpow_nonneg hLpos.le _), ← Real.rpow_mul (inv_pos.2 hc).le,
        mul_one_div_cancel hr'.ne', Real.rpow_one, ← Real.rpow_mul hLpos.le]
      rw [show r * (1 / (r / (r - 1))) = r - 1 by field_simp]
      exact inv_mul_cancel₀ hc.ne'
    · unfold cubeTrace
      simp only [Matrix.mul_smul, Matrix.trace_smul, trace_mul_normingElement (hx _) hr,
        smul_eq_mul]
      rw [avg_const_mul, ← hLr, Real.rpow_sub hLpos, Real.rpow_one]
      field_simp

omit [DecidableEq n] in
/-- `τ (x y) = τ (y x)`. -/
private theorem ipd_cubeTrace_mul_comm (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => x ε * y ε) = cubeTrace (fun ε => y ε * x ε) := by
  unfold cubeTrace
  simp_rw [Matrix.trace_mul_comm (x _)]

omit [Fintype n] [DecidableEq n] in
/-- `E_k x` is a function of the first `k` signs. -/
private theorem ipd_condAvg_apply_eq (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ)
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    condAvg k x ε = condAvg k x ε' := by
  simp only [condAvg]
  congr 1
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 1
  funext j
  simp only [splice]
  split_ifs with hj
  · exact h j hj
  · rfl

omit [DecidableEq n] in
/-- `τ (a y) = τ (a E_k y)` for `a` a function of the first `k` signs (bimodule property and
`τ ∘ E_k = τ`). -/
private theorem ipd_cubeTrace_mul_condAvg {k : ℕ} {a : (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → a ε = a ε')
    (y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => a ε * y ε) = cubeTrace (fun ε => a ε * condAvg k y ε) := by
  classical
  have h := condAvg_mul_mul ha (b := fun _ => (1 : Matrix n n ℝ)) (fun _ _ _ => rfl) y
  simp only [mul_one] at h
  rw [← cubeTrace_condAvg k, h]

omit [Fintype n] [DecidableEq n] in
/-- `E_k (d_k x) = 0`. -/
private theorem ipd_condAvg_mdiff (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ) :
    condAvg k (mdiff k x) = 0 := by
  have h : condAvg k (mdiff k x) = fun ε => condAvg k (condAvg (k + 1) x) ε -
      condAvg k (condAvg k x) ε := by
    funext ε
    simp only [condAvg, mdiff, Finset.sum_sub_distrib, smul_sub]
  rw [h, condAvg_condAvg (Nat.le_succ k), condAvg_condAvg le_rfl]
  funext ε
  exact sub_self _

omit [DecidableEq n] in
/-- The trace pairing with a transform:
`τ (T_σ x · y) = τ (E_0 x E_0 y) + Σ_k E σ_k tr (d_k x d_k y)`, by the orthogonality of the
martingale differences. -/
private theorem ipd_cubeTrace_transform_mul_eq {σ : Fin N → (Fin N → Bool) → ℝ}
    (hσ : IsPredictable σ) (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => transform σ x ε * y ε) =
      cubeTrace (fun ε => condAvg 0 x ε * condAvg 0 y ε) +
        ∑ k : Fin N, avg fun ε => σ k ε * (mdiff k x ε * mdiff k y ε).trace := by
  have e1 : cubeTrace (fun ε => transform σ x ε * y ε) =
      cubeTrace (fun ε => condAvg 0 x ε * y ε) +
        ∑ k : Fin N, cubeTrace (fun ε => (σ k ε • mdiff k x ε) * y ε) := by
    unfold cubeTrace
    rw [← avg_sum, ← avg_add]
    congr 1
    funext ε
    simp only [transform, mdiff, add_mul, Finset.sum_mul, Matrix.trace_add, Matrix.trace_sum]
  rw [e1, ipd_cubeTrace_mul_condAvg (fun ε ε' h => ipd_condAvg_apply_eq 0 x h) y]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  -- `σ_k d_k x` is a function of the first `k + 1` signs, `σ_k` and `E_k y` of the first `k`
  have hσk : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k.val → ε j = ε' j) →
      σ k ε = σ k ε' := fun ε ε' h => hσ k ε ε' fun j hj => h j hj
  have hu : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k.val + 1 → ε j = ε' j) →
      σ k ε • mdiff k x ε = σ k ε' • mdiff k x ε' := by
    intro ε ε' h
    have h' : ∀ j : Fin N, j.val < k.val → ε j = ε' j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    simp only [mdiff]
    rw [hσk ε ε' h', ipd_condAvg_apply_eq _ x h, ipd_condAvg_apply_eq _ x h']
  have hv : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k.val → ε j = ε' j) →
      σ k ε • condAvg k y ε = σ k ε' • condAvg k y ε' := by
    intro ε ε' h
    rw [hσk ε ε' h, ipd_condAvg_apply_eq _ y h]
  -- `τ (σ_k d_k x · E_k y) = τ (σ_k E_k y · E_k (d_k x)) = 0`
  have h0 : cubeTrace (fun ε => (σ k ε • mdiff k x ε) * condAvg k y ε) = 0 := by
    rw [ipd_cubeTrace_mul_comm]
    have e : (fun ε => condAvg k y ε * (σ k ε • mdiff k x ε)) =
        fun ε => (σ k ε • condAvg k y ε) * mdiff k x ε := by
      funext ε
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e, ipd_cubeTrace_mul_condAvg hv, ipd_condAvg_mdiff]
    simp [cubeTrace, avg]
  rw [ipd_cubeTrace_mul_condAvg hu y, ← sub_zero (cubeTrace _), ← h0]
  unfold cubeTrace
  rw [← avg_sub]
  congr 1
  funext ε
  rw [← Matrix.trace_sub, ← mul_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

omit [DecidableEq n] in
/-- A transform by predictable scalar signs is self-adjoint for the trace pairing. -/
theorem cubeTrace_transform_mul {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => transform σ x ε * y ε) = cubeTrace (fun ε => x ε * transform σ y ε) := by
  rw [ipd_cubeTrace_mul_comm x, ipd_cubeTrace_transform_mul_eq hσ,
    ipd_cubeTrace_transform_mul_eq hσ, ipd_cubeTrace_mul_comm (condAvg 0 x)]
  simp_rw [Matrix.trace_mul_comm (mdiff _ x _)]

/-- **Duality**: a strong `(r, r)` bound for a transform by predictable signs on
symmetric-matrix-valued functions gives the strong `(r', r')` bound with the same constant. -/
theorem lpNorm_transform_le_of_dual {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    {r K : ℝ} (hr : 1 < r)
    (h : ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) →
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ x) ≤
        K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r x)
    (x : (Fin N → Bool) → Matrix n n ℝ) (hx : ∀ ε, (x ε).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) (transform σ x) ≤
      K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) x := by
  have hr1 : 0 < r - 1 := by linarith
  have hr' : 1 < r / (r - 1) := by rw [one_lt_div hr1]; linarith
  have hr'' : r / (r - 1) / (r / (r - 1) - 1) = r := by
    have : r / (r - 1) - 1 = 1 / (r - 1) := by field_simp; ring
    rw [this, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hr1.ne']
  have hS : ∀ (q : ℝ≥0∞) (A : Matrix n n ℝ), 0 ≤ schattenNorm q A :=
    fun q A => schattenNorm_nonneg q A
  rcases lt_or_ge K 0 with hK | hK
  · -- degenerate case `K < 0`: the hypothesis forces `x = 0`
    have h1 := h x hx
    have h2 := lpNorm_nonneg (hS (ENNReal.ofReal r)) r (transform σ x)
    have h3 := lpNorm_nonneg (hS (ENNReal.ofReal r)) r x
    have hx0 : x = 0 := ipd_eq_zero_of_lpNorm_eq_zero (p := r) (by linarith) (by nlinarith)
    subst hx0
    have hT0 : transform σ (0 : (Fin N → Bool) → Matrix n n ℝ) = 0 := by
      funext ε
      simp [transform, condAvg]
    rw [hT0, ipd_lpNorm_zero (by linarith), mul_zero]
  · -- the norming function `y` of `T_σ x` in `L^{r'}`, with `‖y‖_{L^r} ≤ 1`
    obtain ⟨y, hy, hy1, hxy⟩ := exists_cubeTrace_mul_eq (isHermitian_transform hx σ) hr'
    rw [hr''] at hy1
    calc SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1))
          (transform σ x)
        = cubeTrace (fun ε => transform σ x ε * y ε) := hxy.symm
      _ = cubeTrace (fun ε => x ε * transform σ y ε) := cubeTrace_transform_mul hσ x y
      _ ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) x *
            SignCube.lpNorm (schattenNorm (ENNReal.ofReal r)) r (transform σ y) := by
          have := cubeTrace_mul_le hx (isHermitian_transform hy σ) hr'
          rwa [hr''] at this
      _ ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) x *
            (K * 1) :=
          mul_le_mul_of_nonneg_left ((h y hy).trans (mul_le_mul_of_nonneg_left hy1 hK))
            (lpNorm_nonneg (hS _) _ _)
      _ = K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal (r / (r - 1)))) (r / (r - 1)) x := by
          ring

end BanachProbability
