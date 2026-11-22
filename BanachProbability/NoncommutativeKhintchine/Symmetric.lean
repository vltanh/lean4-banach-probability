module

public import BanachProbability.Schatten.Holder
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The noncommutative Khintchine inequality for symmetric matrices

For real symmetric `n × n` matrices `A_1, …, A_k`, `q ≥ 2` and `Y (ε) = Σ_i ε_i A_i`,
`(E ‖Y‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖(Σ_i A_i²)^{1/2}‖_{S_q}`, where
`‖(Σ_i A_i²)^{1/2}‖_{S_q} = ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}` (`ncKhintchine_symmetric_upper`), with a
constant independent of the dimension.

The proof is the method of exchangeable pairs of L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell
and J. A. Tropp, *Matrix concentration inequalities via the method of exchangeable pairs*, Ann.
Probab. 42 (2014), §7 (the matrix Burkholder–Davis–Gundy inequality, Theorem 7.1, and its
Khintchine case, Corollary 7.3 (7.2)), for the Stein pair of their §2.4: `Y = Y (ε)` and
`Y' = Y (ε')`, where `ε'` resamples a uniformly chosen sign. For Rademacher sums `Y' = Y` unless the
fresh sign differs, and then `Y' = Y^{(i)} = Y (flip_i ε)`, `Y − Y^{(i)} = 2 ε_i A_i`, and the
conditional variance is `Δ_X = V = Σ_i A_i²`. With `h (t) = t |t|^{q−2}` and `g (t) = |t|^{q−2}`:

* Lemma 2.4 for this pair (`avg_trace_mul_eq`):
  `E tr (Y F (Y)) = ¼ Σ_i E tr ((Y − Y^{(i)})(F (Y) − F (Y^{(i)})))`;
* `q = 2`: with `F = id` this is the source's identity (2.5), `E ‖Y‖_{S_2}² = E tr Y² = tr V
  = ‖V‖_{S_1}`;
* `q > 2`: `E ‖Y‖_q^q = E tr (Y h (Y))`, Lemma 2.4 with `F = h`, a mean-value trace inequality
  with constant `c`, `(Y − Y^{(i)})² = 4 A_i²` and flip invariance (exchangeability) give
  `E ‖Y‖_q^q ≤ 2 c E tr (V g (Y))`. For `q ≥ 3` the source's Lemma 3.4
  (`trace_mean_value_of_three_le`, `c = (q − 1) / 2`) gives the source's bound
  `E ‖Y‖_q^q ≤ (q − 1) E tr (V g (Y))`; for `2 < q < 3` the variant named in Remark 7.2
  (`trace_mean_value`, `c = q − 1`) gives `E ‖Y‖_q^q ≤ 2 (q − 1) E tr (V g (Y))`
  (`avg_schattenNorm_rpow_le`, stated for every `q ≥ 2`);
* then the trace Hölder inequality with `r = q / 2` (`trace_mul_le_of_posSemidef`), the identity
  `‖|Y|^{q−2}‖_{S_{q/(q−2)}} = ‖Y‖_{S_q}^{q−2}` (the eigenvalues of `|Y|^{q−2}` are the
  `|λ_i (Y)|^{q−2}`, from `Matrix.IsHermitian.charpoly_cfc_eq`) and Hölder's inequality for the
  expectation give `E ‖Y‖_q^q ≤ 2 c ‖V‖_{q/2} (E ‖Y‖_q^q)^{1−2/q}`, which is solved for
  `E ‖Y‖_q^q`.

The proof thus gives the source's constants: `1` for `q = 2`, `√(q − 1)` for `q ≥ 3`
(Corollary 7.3, `ncKhintchine_symmetric_upper_of_three_le`; both together,
`ncKhintchine_symmetric_upper_of_eq_two_or_three_le`) and `√(2 (q − 1))` for
`2 < q < 3` (Remark 7.2); `ncKhintchine_symmetric_upper` records the largest of them,
`√(2 (q − 1))`, for every `q ≥ 2`. The source does not prove the variant of the mean value trace
inequality that Remark 7.2 requires; it is proved in `BanachProbability.Schatten.Trace`
(`trace_mean_value`).

The elementary facts about the average over the sign cube that the proof uses are those of
`BanachProbability.SignCube.Basic` (linearity over finite sums, `avg_sum`; flip invariance,
`avg_flip`) and `BanachProbability.SignCube.LpSeminorm` (Jensen's inequality,
`avg_le_rpow_avg_rpow`); the spectral facts (`posSemidef_cfc`, `schattenNorm_cfc_rpow`,
`schattenNorm_one_of_posSemidef`) are those of `BanachProbability.Schatten.Spectral`.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Spectral facts -/

/-- `‖|Y|^{q−2}‖_{S_{q/(q−2)}} = ‖Y‖_{S_q}^{q−2}` for a symmetric `Y` and `q > 2`, written with
`r = q / 2` and `r / (r − 1) = q / (q − 2)`: the eigenvalues of `|Y|^{q−2}` are the
`|λ_i (Y)|^{q−2}`. -/
private theorem schattenNorm_cfc_abs_rpow {Y : Matrix n n ℝ} (hY : Y.IsHermitian) {q : ℝ}
    (hq : 2 < q) :
    schattenNorm (ENNReal.ofReal (q / 2 / (q / 2 - 1))) (cfc (fun t : ℝ => |t| ^ (q - 2)) Y) =
      schattenNorm (ENNReal.ofReal q) Y ^ (q - 2) := by
  have hq2 : q - 2 ≠ 0 := by linarith
  have hs : q / 2 / (q / 2 - 1) = q / (q - 2) := by
    field_simp
  have hs0 : 0 < q / (q - 2) := div_pos (by linarith) (by linarith)
  have hsq : (q - 2) * (q / (q - 2)) = q := by field_simp
  have hYn := schattenNorm_nonneg (ENNReal.ofReal q) Y
  rw [hs, ← Real.rpow_left_inj (schattenNorm_nonneg _ _) (Real.rpow_nonneg hYn _) hs0.ne',
    schattenNorm_cfc_rpow hY _ hs0, ← Real.rpow_mul hYn, hsq,
    schattenNorm_rpow_of_isHermitian hY (by linarith)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _), hsq]

/-! ### The exchangeable pair -/

omit [Fintype n] [DecidableEq n] in
/-- `Y (ε) − Y (flip_i ε) = 2 ε_i A_i`. -/
private theorem sum_coin_smul_sub_flip {k : ℕ} (A : Fin k → Matrix n n ℝ) (ε : Fin k → Bool)
    (i : Fin k) :
    (∑ j, coin (ε j) • A j) - ∑ j, coin (SignCube.flip i ε j) • A j =
      (2 * coin (ε i)) • A i := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [flip_apply_self, coin_not, ← sub_smul]
    congr 1
    ring
  · intro j _ hj
    rw [flip_apply_of_ne hj, sub_self]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq n] in
/-- Lemma 2.4 of Mackey et al. for the exchangeable pair `(Y (ε), Y (ε'))` of §2.4, where `ε'`
resamples a uniformly chosen sign `ε_K`: since `Y (ε') = Y (ε)` unless the fresh sign differs, in
which case `Y (ε') = Y^{(K)} (ε) = Y (flip_K ε)`, the identity `E [Y F (Y)] =
(1 / 2α) E [(Y − Y')(F (Y) − F (Y'))]`, `α = 1 / k`, becomes
`E tr (Y F (Y)) = ¼ Σ_i E tr ((Y − Y^{(i)})(F (Y) − F (Y^{(i)})))`. As in the source, it comes
from `E [ε_i tr (A_i F (Y^{(i)}))] = −E [ε_i tr (A_i F (Y))]` (flip invariance). -/
private theorem avg_trace_mul_eq {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i)
    (F : Matrix n n ℝ → Matrix n n ℝ) :
    avg (fun ε => (Y ε * F (Y ε)).trace) =
      1 / 4 * ∑ i, avg (fun ε =>
        ((Y ε - Y (SignCube.flip i ε)) * (F (Y ε) - F (Y (SignCube.flip i ε)))).trace) := by
  have hdiff : ∀ ε i, Y ε - Y (SignCube.flip i ε) = (2 * coin (ε i)) • A i := fun ε i => by
    rw [hY, hY]
    exact sum_coin_smul_sub_flip A ε i
  have hflip : ∀ i, avg (fun ε => coin (ε i) * (A i * F (Y (SignCube.flip i ε))).trace) =
      -avg (fun ε => coin (ε i) * (A i * F (Y ε)).trace) := fun i => by
    rw [← avg_flip i]
    simp only [flip_apply_self, coin_not, flip_involutive i _]
    rw [← neg_one_mul, ← avg_const_mul]
    congr 1
    funext ε
    ring
  have hi : ∀ i, avg (fun ε =>
      ((Y ε - Y (SignCube.flip i ε)) * (F (Y ε) - F (Y (SignCube.flip i ε)))).trace) =
      4 * avg (fun ε => coin (ε i) * (A i * F (Y ε)).trace) := fun i => by
    have h : ∀ ε, ((Y ε - Y (SignCube.flip i ε)) * (F (Y ε) - F (Y (SignCube.flip i ε)))).trace =
        2 * (coin (ε i) * (A i * F (Y ε)).trace) -
          2 * (coin (ε i) * (A i * F (Y (SignCube.flip i ε))).trace) := fun ε => by
      rw [hdiff, smul_mul_assoc, Matrix.trace_smul, mul_sub, Matrix.trace_sub, smul_eq_mul]
      ring
    rw [show (fun ε => ((Y ε - Y (SignCube.flip i ε)) *
        (F (Y ε) - F (Y (SignCube.flip i ε)))).trace) = _ from funext h, avg_sub, avg_const_mul,
      avg_const_mul, hflip]
    ring
  calc avg (fun ε => (Y ε * F (Y ε)).trace)
      = avg (fun ε => ∑ i, coin (ε i) * (A i * F (Y ε)).trace) := by
        congr 1
        funext ε
        calc (Y ε * F (Y ε)).trace = ((∑ i, coin (ε i) • A i) * F (Y ε)).trace := by rw [← hY]
          _ = _ := by
            simp only [Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul,
              smul_eq_mul]
    _ = ∑ i, avg (fun ε => coin (ε i) * (A i * F (Y ε)).trace) := avg_sum _ _
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hi]
      ring

/-- The exchangeable-pair estimate from a mean-value trace inequality with constant `c`
(`trace_mean_value`, `c = q − 1`, or the source's Lemma 3.4, `c = (q − 1) / 2` for `q ≥ 3`):
`E ‖Y‖_q^q ≤ 2 c E tr (V g (Y))`. This is the source's proof of Theorem 7.1 up to the
identification of the conditional variance `Δ_X = Σ_i A_i² = V`: Lemma 2.4 with
`F = h`, the mean-value inequality, `(Y − Y^{(i)})² = 4 A_i²`, and exchangeability
(flip invariance) to replace `g (Y^{(i)})` by `g (Y)`. -/
private theorem avg_schattenNorm_rpow_le_of_meanValue {q c : ℝ} (hq : 0 < q) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i)
    (hmv : ∀ P Q : Matrix n n ℝ, P.IsHermitian → Q.IsHermitian →
      ((P - Q) * (cfc (fun t : ℝ => t * |t| ^ (q - 2)) P -
        cfc (fun t : ℝ => t * |t| ^ (q - 2)) Q)).trace ≤
      c * (((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) P).trace +
        ((P - Q) * (P - Q) * cfc (fun t : ℝ => |t| ^ (q - 2)) Q).trace)) :
    avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ≤
      2 * c * avg (fun ε =>
        ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace) := by
  set g : ℝ → ℝ := fun t => |t| ^ (q - 2)
  set h : ℝ → ℝ := fun t => t * |t| ^ (q - 2)
  have hYh : ∀ ε, (Y ε).IsHermitian := fun ε => by
    rw [hY]
    exact isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all (coin (ε i)))
  have hdiff : ∀ ε i, Y ε - Y (SignCube.flip i ε) = (2 * coin (ε i)) • A i := fun ε i => by
    rw [hY, hY]
    exact sum_coin_smul_sub_flip A ε i
  -- `(Y − Y^{(i)})² = 4 A_i²`
  have hsq : ∀ ε i, (Y ε - Y (SignCube.flip i ε)) * (Y ε - Y (SignCube.flip i ε)) =
      (4 : ℝ) • (A i * A i) := fun ε i => by
    rw [hdiff, smul_mul_smul_comm]
    congr 1
    linear_combination 4 * coin_mul_self (ε i)
  -- the mean-value trace inequality and exchangeability, for each `i`
  have hstep : ∀ i, avg (fun ε =>
      ((Y ε - Y (SignCube.flip i ε)) * (cfc h (Y ε) - cfc h (Y (SignCube.flip i ε)))).trace) ≤
      8 * c * avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := fun i => by
    calc _ ≤ avg (fun ε => c *
          (((Y ε - Y (SignCube.flip i ε)) * (Y ε - Y (SignCube.flip i ε)) * cfc g (Y ε)).trace +
          ((Y ε - Y (SignCube.flip i ε)) * (Y ε - Y (SignCube.flip i ε)) *
            cfc g (Y (SignCube.flip i ε))).trace)) :=
          avg_mono fun ε => hmv _ _ (hYh ε) (hYh _)
      _ = avg (fun ε => c * (4 * (A i * A i * cfc g (Y ε)).trace +
          4 * (A i * A i * cfc g (Y (SignCube.flip i ε))).trace)) := by
          congr 1
          funext ε
          simp only [hsq, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
      _ = _ := by
          rw [avg_const_mul, avg_add, avg_const_mul, avg_const_mul,
            avg_flip i (fun ε => (A i * A i * cfc g (Y ε)).trace)]
          ring
  calc avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q)
      = avg (fun ε => (Y ε * cfc h (Y ε)).trace) := by
        congr 1
        funext ε
        exact schattenNorm_rpow_eq_trace (hYh ε) hq
    _ = 1 / 4 * ∑ i, avg (fun ε =>
        ((Y ε - Y (SignCube.flip i ε)) * (cfc h (Y ε) - cfc h (Y (SignCube.flip i ε)))).trace) :=
        avg_trace_mul_eq A Y hY (cfc h)
    _ ≤ 1 / 4 * ∑ i, 8 * c * avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := by
        gcongr with i
        exact hstep i
    _ = 2 * c * ∑ i, avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := by
        rw [← Finset.mul_sum]
        ring
    _ = 2 * c * avg (fun ε => ((∑ i, A i * A i) * cfc g (Y ε)).trace) := by
        rw [← avg_sum]
        congr 2
        funext ε
        rw [Finset.sum_mul, Matrix.trace_sum]

/-- The exchangeable-pair estimate: `E ‖Y‖_{S_q}^q ≤ 2 (q − 1) E tr (V |Y|^{q−2})`,
`Y = Σ_i ε_i A_i`, `V = Σ_i A_i²`, for every `q ≥ 2`, from the cruder mean-value trace inequality
`trace_mean_value` (for `2 < q < 3`, the variant of Lemma 3.4 that Mackey et al., Remark 7.2,
name without proof). -/
theorem avg_schattenNorm_rpow_le {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (avg fun ε => schattenNorm (ENNReal.ofReal q) (∑ i, coin (ε i) • A i) ^ q) ≤
      2 * (q - 1) * avg fun ε =>
        ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (∑ i, coin (ε i) • A i)).trace :=
  avg_schattenNorm_rpow_le_of_meanValue (by linarith) A hA _ (fun _ => rfl)
    fun _ _ hP hQ => trace_mean_value hP hQ hq

/-- The source's bound in the proof of Theorem 7.1, for `q ≥ 3` (their `p ≥ 1.5`), from Lemma 3.4
(`trace_mean_value_of_three_le`): `E ‖Y‖_{S_q}^q ≤ (q − 1) E tr (V |Y|^{q−2})`. -/
private theorem avg_schattenNorm_rpow_le_of_three_le {q : ℝ} (hq : 3 ≤ q) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i) :
    avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ≤
      (q - 1) * avg (fun ε =>
        ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace) := by
  have h := avg_schattenNorm_rpow_le_of_meanValue (c := (q - 1) / 2) (by linarith) A hA Y hY
    fun _ _ hP hQ => trace_mean_value_of_three_le hP hQ hq
  rwa [show 2 * ((q - 1) / 2) = q - 1 by ring] at h

/-- The case `q = 2` (their `p = 1`): the identity (2.5) `E [Δ_X] = E X²`, which the source
derives from Lemma 2.4 with `F (X) = X`; here `Δ_X = V`, so `E ‖Y‖_{S_2}² = E tr Y² = tr V`. -/
private theorem avg_schattenNorm_two_rpow {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i) :
    avg (fun ε => schattenNorm (ENNReal.ofReal 2) (Y ε) ^ (2 : ℝ)) = (∑ i, A i * A i).trace := by
  have hYh : ∀ ε, (Y ε).IsHermitian := fun ε => by
    rw [hY]
    exact isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all (coin (ε i)))
  have hdiff : ∀ ε i, Y ε - Y (SignCube.flip i ε) = (2 * coin (ε i)) • A i := fun ε i => by
    rw [hY, hY]
    exact sum_coin_smul_sub_flip A ε i
  -- `‖Y‖_{S_2}² = tr (Y h (Y))` with `h (t) = t |t|^0 = t`
  have h2 : ∀ ε, schattenNorm (ENNReal.ofReal 2) (Y ε) ^ (2 : ℝ) = (Y ε * id (Y ε)).trace :=
    fun ε => by
      rw [schattenNorm_rpow_eq_trace (hYh ε) two_pos]
      simp only [sub_self, Real.rpow_zero, mul_one, id]
      rw [cfc_id' ℝ (Y ε) (show IsSelfAdjoint (Y ε) from hYh ε)]
  simp only [h2]
  -- Lemma 2.4 with `F = id`, and `(Y − Y^{(i)})² = 4 A_i²`
  rw [avg_trace_mul_eq A Y hY id]
  simp only [id, hdiff, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  have hc : ∀ (ε : Fin k → Bool) (i : Fin k), 2 * coin (ε i) * (2 * coin (ε i)) = 4 :=
    fun ε i => by linear_combination 4 * coin_mul_self (ε i)
  simp only [hc, avg_const, Matrix.trace_sum, ← Finset.mul_sum]
  ring

/-- Solving the moment inequality, for `q > 2`: if `E ‖Y‖_q^q ≤ c E tr (V |Y|^{q−2})`, then the
trace Hölder inequality with `r = q / 2` and Hölder's inequality for the expectation (Jensen)
give `E ‖Y‖_q^q ≤ c ‖V‖_{q/2} (E ‖Y‖_q^q)^{1−2/q}`, whence
`(E ‖Y‖_q^q)^{1/q} ≤ √c ‖V‖_{q/2}^{1/2}` (the end of the source's proof of Theorem 7.1). -/
private theorem rpow_le_of_avg_le {q c : ℝ} (hq2 : 2 < q) (hc : 0 ≤ c) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i)
    (hbound : avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ≤
      c * avg (fun ε => ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace)) :
    avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ^ (1 / q) ≤
      √c * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  have hYh : ∀ ε, (Y ε).IsHermitian := fun ε => by
    rw [hY]
    exact isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all (coin (ε i)))
  set M := avg fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q with hM
  have hq0 : 0 < q := by linarith
  have hM0 : 0 ≤ M := avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  set V := ∑ i, A i * A i
  have hV : V.PosSemidef := Matrix.posSemidef_sum _ fun i _ => by
    have := Matrix.posSemidef_conjTranspose_mul_self (A i)
    rwa [(hA i).eq] at this
  have hr : 1 < q / 2 := by linarith
  set W := schattenNorm (ENNReal.ofReal (q / 2)) V
  have hW : 0 ≤ W := schattenNorm_nonneg _ _
  -- the trace Hölder inequality, `‖|Y|^{q−2}‖_{S_{q/(q−2)}} = ‖Y‖_{S_q}^{q−2}`
  have hG : ∀ ε, (V * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace ≤
      W * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2) := fun ε => by
    have := trace_mul_le_of_posSemidef hV
      (posSemidef_cfc (A := Y ε) (f := fun t : ℝ => |t| ^ (q - 2)) fun t _ =>
        Real.rpow_nonneg (abs_nonneg t) _) hr
    rwa [schattenNorm_cfc_abs_rpow (hYh ε) hq2] at this
  -- Hölder's inequality for the expectation: `E ‖Y‖^{q−2} ≤ (E ‖Y‖^q)^{(q−2)/q}`
  have hJ : avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) ≤
      M ^ ((q - 2) / q) := by
    have hp : 1 ≤ q / (q - 2) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have := avg_le_rpow_avg_rpow
      (X := fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2))
      (fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) hp
    have hq2' : q - 2 ≠ 0 := by linarith
    convert this using 2
    · rw [hM]
      congr 1
      funext ε
      rw [← Real.rpow_mul (schattenNorm_nonneg _ _)]
      congr 1
      field_simp
    · field_simp
  have hMb : M ≤ c * W * M ^ ((q - 2) / q) := by
    calc M ≤ c * avg (fun ε => (V * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace) := hbound
      _ ≤ c * avg (fun ε => W * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) :=
          mul_le_mul_of_nonneg_left (avg_mono hG) hc
      _ = c * W * avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) := by
          rw [avg_const_mul]
          ring
      _ ≤ c * W * M ^ ((q - 2) / q) := mul_le_mul_of_nonneg_left hJ (mul_nonneg hc hW)
  -- solve for `M`
  rcases hM0.eq_or_lt with hM' | hMpos
  · rw [← hM', Real.zero_rpow (one_div_pos.mpr hq0).ne']
    positivity
  · have hsplit : M = M ^ (2 / q) * M ^ ((q - 2) / q) := by
      rw [← Real.rpow_add hMpos, show 2 / q + (q - 2) / q = 1 by field_simp; ring,
        Real.rpow_one]
    have h2 : M ^ (2 / q) ≤ c * W := by
      refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hMpos ((q - 2) / q))
      rw [← hsplit]
      exact hMb
    have hroot : M ^ (1 / q) = √(M ^ (2 / q)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM0]
      congr 1
      ring
    rw [hroot, ← Real.sqrt_mul hc]
    exact Real.sqrt_le_sqrt h2

/-- **Noncommutative Khintchine inequality, symmetric case, `q ≥ 3`** (Mackey et al. 2014,
Corollary 7.3, from Lemma 3.4), with the source's constant `√(q − 1)`:
`(E ‖Σ_i ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(q − 1) ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}`. -/
theorem ncKhintchine_symmetric_upper_of_three_le {q : ℝ} (hq : 3 ≤ q) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q - 1) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) :=
  rpow_le_of_avg_le (by linarith) (by linarith) A hA _ (fun _ => rfl)
    (avg_schattenNorm_rpow_le_of_three_le hq A hA _ fun _ => rfl)

/-- **Noncommutative Khintchine inequality, symmetric case, `q = 2`** (Mackey et al. 2014,
Corollary 7.3 for `p = 1`), an equality, by the identity (2.5):
`(E ‖Σ_i ε_i A_i‖_{S_2}²)^{1/2} = ‖Σ_i A_i²‖_{S_1}^{1/2}`. -/
theorem ncKhintchine_symmetric_two {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal 2)) 2
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) =
      √(schattenNorm (ENNReal.ofReal (2 / 2)) (∑ i, A i * A i)) := by
  set V := ∑ i, A i * A i
  have hV : V.PosSemidef := Matrix.posSemidef_sum _ fun i _ => by
    have := Matrix.posSemidef_conjTranspose_mul_self (A i)
    rwa [(hA i).eq] at this
  have hV1 : schattenNorm (ENNReal.ofReal (2 / 2)) V = V.trace := by
    rw [div_self two_ne_zero]
    exact schattenNorm_one_of_posSemidef hV
  rw [SignCube.lpNorm, avg_schattenNorm_two_rpow A hA _ (fun _ => rfl), hV1, ← Real.sqrt_eq_rpow]

/-- **Noncommutative Khintchine inequality, symmetric case**, with the source's constant
`√(q − 1)` in its range `q = 2` or `q ≥ 3` (Mackey et al. 2014, Corollary 7.3, (7.2), where
`q = 2p`). -/
theorem ncKhintchine_symmetric_upper_of_eq_two_or_three_le {q : ℝ} (hq : q = 2 ∨ 3 ≤ q) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(q - 1) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  rcases hq with rfl | hq
  · rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_one, one_mul]
    exact (ncKhintchine_symmetric_two A hA).le
  · exact ncKhintchine_symmetric_upper_of_three_le hq A hA

/-- **Noncommutative Khintchine inequality, symmetric case, upper bound** (Mackey et al. 2014,
§7, Corollary 7.3 (7.2) and Remark 7.2):
`(E ‖Σ_i ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}`, `q ≥ 2`.

The proof follows the source in each range: for `q = 2`, the identity (2.5) gives the
constant `1`; for `q ≥ 3`, Lemma 3.4 gives `√(q − 1)`; for `2 < q < 3`, the variant of the mean
value trace inequality named in Remark 7.2 gives `√(2 (q − 1))`.

Departure from the source: Remark 7.2 does not prove that variant; it is `trace_mean_value`,
proved from the scalar inequality `mul_sub_le_sq_mul_add`. -/
theorem ncKhintchine_symmetric_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(2 * (q - 1)) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  set Y : (Fin k → Bool) → Matrix n n ℝ := fun ε => ∑ i, coin (ε i) • A i
  have hlp : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q Y =
      avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ^ (1 / q) := rfl
  rw [hlp]
  rcases hq.eq_or_lt with rfl | hq2
  · -- `q = 2`: `E ‖Y‖_{S_2}² = tr V = ‖V‖_{S_1}`, constant `1 ≤ √2`
    set V := ∑ i, A i * A i
    have hV : V.PosSemidef := Matrix.posSemidef_sum _ fun i _ => by
      have := Matrix.posSemidef_conjTranspose_mul_self (A i)
      rwa [(hA i).eq] at this
    have hV1 : schattenNorm (ENNReal.ofReal (2 / 2)) V = V.trace := by
      rw [div_self two_ne_zero]
      exact schattenNorm_one_of_posSemidef hV
    rw [avg_schattenNorm_two_rpow A hA Y (fun _ => rfl), hV1, ← Real.sqrt_eq_rpow]
    refine le_mul_of_one_le_left (Real.sqrt_nonneg _) ?_
    rw [show (2 : ℝ) * (2 - 1) = 2 by norm_num, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  rcases le_or_gt 3 q with hq3 | hq3
  · -- `q ≥ 3`: Lemma 3.4, constant `√(q − 1) ≤ √(2 (q − 1))`
    refine (ncKhintchine_symmetric_upper_of_three_le hq3 A hA).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  · -- `2 < q < 3`: the variant of Lemma 3.4 (Remark 7.2), constant `√(2 (q − 1))`
    exact rpow_le_of_avg_le hq2 (by linarith) A hA Y (fun _ => rfl)
      (avg_schattenNorm_rpow_le hq A hA)

end BanachProbability
