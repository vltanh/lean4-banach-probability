module

public import BanachProbability.SignCube.PaleyWalsh
public import BanachProbability.Schatten.Spectral

/-!
# Matrix-valued functions on the sign cube

The finite-dimensional von Neumann algebra `ℓ^∞ (Ω_N) ⊗ M_n (ℝ)` of matrix-valued functions on
the sign cube `Ω_N = Fin N → Bool`, with the trace `τ (x) = E tr x (ε)` (`cubeTrace`), the
filtration of subalgebras of functions of the first `k` signs, and the conditional expectations
`E_k = SignCube.condAvg k`, applied entrywise. Every operator statement in it is pointwise matrix
analysis, then averaged. The noncommutative `L^r` norm is
`‖x‖_{L^r (τ)} = (E ‖x (ε)‖_{S_r}^r)^{1/r} = SignCube.lpNorm (schattenNorm r) r x`.

Facts: `E_k` preserves symmetry and positivity, is a bimodule map over the functions of the first
`k` signs and preserves `τ`; martingale differences are orthogonal for `τ (x y)`; a transform by
`±1` predictable scalar signs (`SignCube.transform`) is an isometry of `L² (τ)`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace `τ (x) = E tr x (ε)` on matrix-valued functions on the sign cube. -/
noncomputable def cubeTrace (x : (Fin N → Bool) → Matrix n n ℝ) : ℝ :=
  avg fun ε => (x ε).trace

/-- The martingale difference `d_k x = E_{k+1} x − E_k x`. -/
noncomputable def mdiff (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ) :
    (Fin N → Bool) → Matrix n n ℝ :=
  fun ε => condAvg (k + 1) x ε - condAvg k x ε

section Helpers

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `E_l f` is a function of the first `l` signs, hence of the first `k` signs for `k ≥ l`. -/
theorem mcd_condAvg_eq_of_agree {l k : ℕ} (hlk : l ≤ k) (f : (Fin N → Bool) → E)
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    condAvg l f ε = condAvg l f ε' := by
  simp only [condAvg]
  congr 1
  refine Finset.sum_congr rfl fun η _ => congrArg f (funext fun j => ?_)
  simp only [splice]
  split_ifs with hj
  · exact h j (lt_of_lt_of_le hj hlk)
  · rfl

/-- `E_k` is additive on differences. -/
theorem mcd_condAvg_sub (k : ℕ) (f g : (Fin N → Bool) → E) :
    condAvg k (fun ε => f ε - g ε) = fun ε => condAvg k f ε - condAvg k g ε := by
  funext ε
  simp only [condAvg, Finset.sum_sub_distrib, smul_sub]

/-- The conditional expectation `E_k` kills the `k`-th martingale difference:
`E_k (E_{k+1} f − E_k f) = 0`. -/
theorem mcd_condAvg_condAvg_succ_sub (k : ℕ) (f : (Fin N → Bool) → E) :
    condAvg k (fun ε => condAvg (k + 1) f ε - condAvg k f ε) = 0 := by
  rw [mcd_condAvg_sub, condAvg_condAvg (Nat.le_succ k), condAvg_condAvg le_rfl]
  funext ε
  simp

/-- The transform by the constant signs `1` is the identity: `E_0 f + Σ_k d_k f = f`. -/
theorem mcd_transform_one (f : (Fin N → Bool) → E) : transform (fun _ _ => 1) f = f := by
  funext ε
  simp only [transform, one_smul]
  have htel := Finset.sum_range_sub (fun i => condAvg i f ε) N
  rw [← Fin.sum_univ_eq_sum_range (fun i => condAvg (i + 1) f ε - condAvg i f ε) N] at htel
  rw [htel, add_sub_cancel,
    condAvg_of_isAdapted fun ε ε' h => congrArg f (funext fun j => h j j.isLt)]

end Helpers

/-- The plain average is invariant under `E_k`. -/
theorem mcd_avg_condAvg (k : ℕ) (g : (Fin N → Bool) → ℝ) : avg (condAvg k g) = avg g := by
  rw [← condAvg_zero_real (condAvg k g) fun _ => false, condAvg_condAvg (Nat.zero_le k),
    condAvg_zero_real]

/-- Scalar orthogonality: `E (g · d_k f) = 0` for `g` a function of the first `k` signs. -/
theorem mcd_avg_mul_condAvg_succ_sub {k : ℕ} {g : (Fin N → Bool) → ℝ}
    (hg : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → g ε = g ε')
    (f : (Fin N → Bool) → ℝ) :
    avg (fun ε => g ε * (condAvg (k + 1) f ε - condAvg k f ε)) = 0 := by
  rw [← mcd_avg_condAvg k]
  have h : condAvg k (fun ε => g ε * (condAvg (k + 1) f ε - condAvg k f ε)) =
      fun ε => g ε * condAvg k (fun ε => condAvg (k + 1) f ε - condAvg k f ε) ε := by
    funext ε
    simp only [condAvg, smul_eq_mul]
    rw [Finset.sum_congr rfl fun ε' _ => by
      rw [hg (splice k ε ε') ε fun j hj => by simp [splice, hj]], ← Finset.mul_sum]
    ring
  rw [h, mcd_condAvg_condAvg_succ_sub]
  simp [avg]

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_condAvg {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (k : ℕ) (ε : Fin N → Bool) : (condAvg k x ε).IsHermitian := by
  simp only [condAvg]
  exact Matrix.IsHermitian.smul (isSelfAdjoint_sum _ fun ε' _ => hx _) (IsSelfAdjoint.all _)

omit [Fintype n] [DecidableEq n] in
theorem posSemidef_condAvg {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).PosSemidef)
    (k : ℕ) (ε : Fin N → Bool) : (condAvg k x ε).PosSemidef := by
  simp only [condAvg]
  have hs := Matrix.posSemidef_sum Finset.univ fun ε' _ => hx (splice k ε ε')
  have hc : (0 : ℝ) ≤ ((2 : ℝ) ^ N)⁻¹ := by positivity
  refine ⟨Matrix.IsHermitian.smul hs.1 (IsSelfAdjoint.all _), fun y => ?_⟩
  have h2 := mul_nonneg hc (hs.2 y)
  rw [Finsupp.mul_sum] at h2
  refine h2.trans_eq (Finsupp.sum_congr fun i _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

omit [Fintype n] [DecidableEq n] in
/-- `E_k` is order preserving. -/
theorem posSemidef_condAvg_sub {x y : (Fin N → Bool) → Matrix n n ℝ}
    (h : ∀ ε, (y ε - x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (condAvg k y ε - condAvg k x ε).PosSemidef := by
  have h' := posSemidef_condAvg h k ε
  rwa [mcd_condAvg_sub] at h'

omit [DecidableEq n] in
/-- The bimodule property: `E_k (a x b) = a E_k (x) b` for `a`, `b` functions of the first `k`
signs. -/
theorem condAvg_mul_mul {k : ℕ} {a b : (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → a ε = a ε')
    (hb : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → b ε = b ε')
    (x : (Fin N → Bool) → Matrix n n ℝ) :
    condAvg k (fun ε => a ε * x ε * b ε) = fun ε => a ε * condAvg k x ε * b ε := by
  funext ε
  have hs : ∀ ε', (∀ j : Fin N, j.val < k → splice k ε ε' j = ε j) := fun ε' j hj => by
    simp [splice, hj]
  simp only [condAvg]
  rw [Finset.sum_congr rfl fun ε' _ => by rw [ha _ ε (hs ε'), hb _ ε (hs ε')], ← Finset.sum_mul,
    ← Finset.mul_sum, ← Matrix.smul_mul, ← Matrix.mul_smul]

omit [DecidableEq n] in
theorem cubeTrace_condAvg (k : ℕ) (x : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (condAvg k x) = cubeTrace x := by
  simp only [cubeTrace]
  have h : ∀ ε, (condAvg k x ε).trace = condAvg k (fun ε => (x ε).trace) ε := fun ε =>
    map_condAvg (Matrix.traceLinearMap n ℝ ℝ) k x ε
  simp only [h]
  exact mcd_avg_condAvg k _

omit [DecidableEq n] in
/-- Orthogonality to a martingale difference: `τ (a · d_k y) = 0` for `a` a function of the first
`k` signs (`τ (a d_k y) = τ (E_k (a d_k y)) = τ (a E_k (d_k y))` and `E_k d_k y = 0`). -/
theorem mcd_cubeTrace_mul_mdiff {k : ℕ} {a : (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → a ε = a ε')
    (y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => a ε * mdiff k y ε) = 0 := by
  rw [← cubeTrace_condAvg k]
  have h : condAvg k (fun ε => a ε * mdiff k y ε) = fun ε => a ε * condAvg k (mdiff k y) ε := by
    funext ε
    simp only [condAvg]
    rw [Finset.sum_congr rfl fun ε' _ => by
      rw [ha (splice k ε ε') ε fun j hj => by simp [splice, hj]], ← Finset.mul_sum,
      Matrix.mul_smul]
  rw [h, show condAvg k (mdiff k y) = 0 from mcd_condAvg_condAvg_succ_sub k y]
  simp [cubeTrace, avg]

omit [DecidableEq n] in
/-- Martingale differences are orthogonal: `τ (d_j x · d_k y) = 0` for `j ≠ k`. -/
theorem cubeTrace_mdiff_mul_mdiff {j k : ℕ} (hjk : j ≠ k) (x y : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => mdiff j x ε * mdiff k y ε) = 0 := by
  have hlt : ∀ {j k : ℕ}, j < k → ∀ x y : (Fin N → Bool) → Matrix n n ℝ,
      cubeTrace (fun ε => mdiff j x ε * mdiff k y ε) = 0 := by
    intro j k hjk x y
    refine mcd_cubeTrace_mul_mdiff (fun ε ε' h => ?_) y
    simp only [mdiff]
    rw [mcd_condAvg_eq_of_agree (Nat.succ_le_of_lt hjk) x h,
      mcd_condAvg_eq_of_agree hjk.le x h]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hlt h x y
  · rw [← hlt h y x]
    simp only [cubeTrace]
    congr 1
    funext ε
    exact Matrix.trace_mul_comm _ _

/-- The cross terms of `(T_σ f)²` vanish: `E (σ_j d_j f · σ_k d_k f) = 0` for `j < k`, since
`σ_j d_j f σ_k` is a function of the first `k` signs. -/
private theorem mcd_avg_cross {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (f : (Fin N → Bool) → ℝ) {j k : Fin N} (hjk : j < k) :
    avg (fun ε => σ j ε * (condAvg (j.val + 1) f ε - condAvg j.val f ε) *
      (σ k ε * (condAvg (k.val + 1) f ε - condAvg k.val f ε))) = 0 := by
  have hjk' : j.val + 1 ≤ k.val := hjk
  rw [← mcd_avg_mul_condAvg_succ_sub (k := k.val)
    (g := fun ε => σ j ε * (condAvg (j.val + 1) f ε - condAvg j.val f ε) * σ k ε)
    (fun ε ε' h => by
      rw [hσ j ε ε' fun i hi => h i (lt_trans hi hjk), hσ k ε ε' fun i hi => h i hi,
        mcd_condAvg_eq_of_agree hjk' f h, mcd_condAvg_eq_of_agree (Nat.le_of_succ_le hjk') f h])
    f]
  congr 1
  funext ε
  ring

/-- The cross terms between `E_0 f` and `σ_k d_k f` vanish. -/
private theorem mcd_avg_cross_zero {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (f : (Fin N → Bool) → ℝ) (k : Fin N) :
    avg (fun ε => 2 * condAvg 0 f ε * (σ k ε * (condAvg (k.val + 1) f ε - condAvg k.val f ε))) =
      0 := by
  rw [← mcd_avg_mul_condAvg_succ_sub (k := k.val) (g := fun ε => 2 * condAvg 0 f ε * σ k ε)
    (fun ε ε' h => by
      rw [hσ k ε ε' fun i hi => h i hi, mcd_condAvg_eq_of_agree (Nat.zero_le _) f h]) f]
  congr 1
  funext ε
  ring

/-- `E (T_σ f)² = E (E_0 f)² + Σ_k E (d_k f)²` for predictable signs `σ_k = ±1`. -/
private theorem mcd_avg_sq_transform {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε * σ k ε = 1) (f : (Fin N → Bool) → ℝ) :
    avg (fun ε => transform σ f ε ^ 2) = avg (fun ε => condAvg 0 f ε ^ 2) +
      ∑ k : Fin N, avg (fun ε => (condAvg (k.val + 1) f ε - condAvg k.val f ε) ^ 2) := by
  have hexp : (fun ε => transform σ f ε ^ 2) = fun ε => (condAvg 0 f ε ^ 2 +
      ∑ k : Fin N, 2 * condAvg 0 f ε *
        (σ k ε * (condAvg (k.val + 1) f ε - condAvg k.val f ε))) +
      ∑ j : Fin N, ∑ k : Fin N, σ j ε * (condAvg (j.val + 1) f ε - condAvg j.val f ε) *
        (σ k ε * (condAvg (k.val + 1) f ε - condAvg k.val f ε)) := by
    funext ε
    simp only [transform, smul_eq_mul]
    rw [add_sq, sq (∑ _ : Fin N, _), Finset.sum_mul_sum, Finset.mul_sum]
  rw [hexp, avg_add, avg_add]
  simp only [avg_sum]
  rw [Finset.sum_eq_zero fun k _ => mcd_avg_cross_zero hσ f k, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · congr 1
    funext ε
    linear_combination (condAvg (j.val + 1) f ε - condAvg j.val f ε) ^ 2 * hσ1 j ε
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with h | h
    · rw [← mcd_avg_cross hσ f h]
      congr 1
      funext ε
      ring
    · exact mcd_avg_cross hσ f h
  · exact fun h => absurd (Finset.mem_univ j) h

/-- The scalar `L²` isometry: `E (T_σ f)² = E f²` for predictable signs `σ_k = ±1`. -/
private theorem mcd_avg_sq_transform_eq {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (f : (Fin N → Bool) → ℝ) :
    avg (fun ε => transform σ f ε ^ 2) = avg (fun ε => f ε ^ 2) := by
  have h1 : ∀ k ε, σ k ε * σ k ε = 1 := fun k ε => by
    rcases hσ1 k ε with h | h <;> rw [h] <;> norm_num
  have hone : IsPredictable (fun (_ : Fin N) (_ : Fin N → Bool) => (1 : ℝ)) :=
    fun _ _ _ _ => rfl
  rw [show (fun ε => f ε ^ 2) = fun ε => transform (fun _ _ => 1) f ε ^ 2 by
    rw [mcd_transform_one], mcd_avg_sq_transform hσ h1,
    mcd_avg_sq_transform hone fun _ _ => one_mul 1]

/-- A transform by predictable `±1` scalar signs is an isometry of `L² (τ)`. -/
theorem lpNorm_two_transform {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ)
    (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (x : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm 2) 2 (transform σ x) = SignCube.lpNorm (schattenNorm 2) 2 x := by
  have key : ∀ X : (Fin N → Bool) → Matrix n n ℝ,
      (fun ε => schattenNorm 2 (X ε) ^ (2 : ℝ)) = fun ε => ∑ i, ∑ j, X ε i j ^ 2 := by
    intro X
    funext ε
    rw [Real.rpow_two, schattenNorm_two_sq]
  unfold SignCube.lpNorm
  rw [key, key]
  simp only [avg_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hT : ∀ ε, transform σ x ε i j = transform σ (fun ε => x ε i j) ε := fun ε =>
    map_transform (Matrix.entryLinearMap ℝ ℝ i j) σ x ε
  simp only [hT]
  exact mcd_avg_sq_transform_eq hσ hσ1 _

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_transform {x : (Fin N → Bool) → Matrix n n ℝ} (hx : ∀ ε, (x ε).IsHermitian)
    (σ : Fin N → (Fin N → Bool) → ℝ) (ε : Fin N → Bool) : (transform σ x ε).IsHermitian := by
  simp only [transform]
  refine (isHermitian_condAvg hx 0 ε).add ?_
  exact isSelfAdjoint_sum _ fun k _ => Matrix.IsHermitian.smul
    ((isHermitian_condAvg hx _ ε).sub (isHermitian_condAvg hx _ ε)) (IsSelfAdjoint.all (σ k ε))

end BanachProbability
