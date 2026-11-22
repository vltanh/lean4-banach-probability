module

public import BanachProbability.Schatten.Holder
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The noncommutative Khintchine inequality for symmetric matrices

For real symmetric `n × n` matrices `A_1, …, A_k`, `q ≥ 2` and `Y (ε) = Σ_i ε_i A_i`,
`(E ‖Y‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖(Σ_i A_i²)^{1/2}‖_{S_q}`, where
`‖(Σ_i A_i²)^{1/2}‖_{S_q} = ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}` (`ncKhintchine_symmetric_upper`), with a
constant independent of the dimension.

The proof is the method of exchangeable pairs of L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell
and J. A. Tropp, *Matrix concentration inequalities via the method of exchangeable pairs*, Ann.
Probab. 42 (2014), §7 (matrix Burkholder–Davis–Gundy and Khintchine inequalities, Corollary 7.3):

* `E ‖Y‖_q^q = E tr (Y h (Y)) = Σ_i E [ε_i tr (A_i h (Y))]` with `h (t) = t |t|^{q−2}`; pairing
  `ε` with its flip in the `i`-th sign, `Y − Y^{(i)} = 2 ε_i A_i`, and the mean-value trace
  inequality (`trace_mean_value`) with flip invariance give
  `E ‖Y‖_q^q ≤ 2 (q − 1) E tr (V g (Y))`, `V = Σ_i A_i²`, `g (t) = |t|^{q−2}`
  (`avg_schattenNorm_rpow_le`);
* for `q > 2`, the trace Hölder inequality with `r = q / 2` (`trace_mul_le_of_posSemidef`), the
  identity `‖|Y|^{q−2}‖_{S_{q/(q−2)}} = ‖Y‖_{S_q}^{q−2}` (the eigenvalues of `|Y|^{q−2}` are the
  `|λ_i (Y)|^{q−2}`, from `Matrix.IsHermitian.charpoly_cfc_eq`) and Jensen's inequality for
  `t ↦ t^{1−2/q}` give `E ‖Y‖_q^q ≤ 2 (q − 1) ‖V‖_{q/2} (E ‖Y‖_q^q)^{1−2/q}`, which is solved for
  `E ‖Y‖_q^q`;
* for `q = 2`, `|Y|^0 = 1` and the estimate reads `E ‖Y‖_2^2 ≤ 2 tr V = 2 ‖V‖_{S_1}`.

The elementary facts about the average over the sign cube that the proof uses (linearity over
finite sums, flip invariance, Jensen's inequality) are proved here as private lemmas.

The constant `√(2 (q − 1))` is that of the cruder mean-value inequality valid for every `q ≥ 2`;
Mackey et al. obtain `√(q − 1)` for `q = 2` and `q ≥ 3` (Corollary 7.3), and `√(2 (q − 1))` for
`2 < q < 3` (Remark 7.2).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary facts about the average over the sign cube -/

section Cube

variable {N : ℕ}

private theorem avg_finset_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin N → Bool) → ℝ) :
    avg (fun ε => ∑ i ∈ s, g i ε) = ∑ i ∈ s, avg (g i) := by
  simp only [avg, Finset.sum_div]
  exact Finset.sum_comm

private theorem avg_const' (c : ℝ) : avg (fun _ : Fin N → Bool => c) = c := by
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- Flip invariance of the uniform measure on the cube. -/
private theorem avg_comp_flip (k : Fin N) (g : (Fin N → Bool) → ℝ) :
    avg (fun ε => g (SignCube.flip k ε)) = avg g := by
  unfold avg
  congr 1
  exact Equiv.sum_comp ((flip_involutive k).toPerm _) g

/-- Jensen's inequality for the average: `avg X ≤ (avg X^p)^{1/p}` for `X ≥ 0`, `p ≥ 1`. -/
private theorem avg_le_avg_rpow_rpow {X : (Fin N → Bool) → ℝ} (hX : ∀ ε, 0 ≤ X ε) {p : ℝ}
    (hp : 1 ≤ p) : avg X ≤ avg (fun ε => X ε ^ p) ^ (1 / p) := by
  have h := Real.arith_mean_le_rpow_mean Finset.univ (fun _ => ((2 : ℝ) ^ N)⁻¹) X
    (fun _ _ => by positivity) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp) (fun ε _ => hX ε) hp
  simpa only [avg, div_eq_inv_mul, Finset.mul_sum] using h

end Cube

/-! ### Spectral facts -/

/-- The eigenvalues of `f (A)` are the `f (λ_i (A))`, as multisets. -/
private theorem map_eigenvalues_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : (cfc f A).IsHermitian) :
    Multiset.map hf.eigenvalues Finset.univ.val =
      Multiset.map (fun i => f (hA.eigenvalues i)) Finset.univ.val := by
  have h1 := hf.roots_charpoly_eq_eigenvalues
  rw [hA.charpoly_cfc_eq f, Polynomial.roots_prod] at h1
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, RCLike.ofReal_real_eq_id,
      Function.id_comp] at h1
    exact h1.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private theorem sum_eigenvalues_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : (cfc f A).IsHermitian) (φ : ℝ → ℝ) :
    ∑ i, φ (hf.eigenvalues i) = ∑ i, φ (f (hA.eigenvalues i)) := by
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  calc (Multiset.map (fun i => φ (hf.eigenvalues i)) Finset.univ.val).sum
      = ((Multiset.map hf.eigenvalues Finset.univ.val).map φ).sum := by
        rw [Multiset.map_map]; rfl
    _ = _ := by rw [map_eigenvalues_cfc hA f hf, Multiset.map_map]; rfl

private theorem isHermitian_cfc (f : ℝ → ℝ) (A : Matrix n n ℝ) : (cfc f A).IsHermitian :=
  cfc_predicate f A

private theorem posSemidef_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ f t) : (cfc f A).PosSemidef := by
  have hG := isHermitian_cfc f A
  rw [hG.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hmem : hG.eigenvalues i ∈ Multiset.map hG.eigenvalues Finset.univ.val :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  rw [map_eigenvalues_cfc hA f hG, Multiset.mem_map] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  rw [Pi.zero_apply, ← hj]
  exact hf _

/-- `‖|Y|^{q−2}‖_{S_{q/(q−2)}} = ‖Y‖_{S_q}^{q−2}` for a symmetric `Y` and `q > 2`, written with
`r = q / 2` and `r / (r − 1) = q / (q − 2)`: the eigenvalues of `|Y|^{q−2}` are the
`|λ_i (Y)|^{q−2}`. -/
private theorem schattenNorm_cfc_abs_rpow {Y : Matrix n n ℝ} (hY : Y.IsHermitian) {q : ℝ}
    (hq : 2 < q) :
    schattenNorm (ENNReal.ofReal (q / 2 / (q / 2 - 1))) (cfc (fun t : ℝ => |t| ^ (q - 2)) Y) =
      schattenNorm (ENNReal.ofReal q) Y ^ (q - 2) := by
  have hG := isHermitian_cfc (fun t : ℝ => |t| ^ (q - 2)) Y
  have hq2 : q - 2 ≠ 0 := by linarith
  have hs : q / 2 / (q / 2 - 1) = q / (q - 2) := by
    field_simp
  have hs0 : 0 < q / (q - 2) := div_pos (by linarith) (by linarith)
  have hsq : (q - 2) * (q / (q - 2)) = q := by field_simp
  have hYn := schattenNorm_nonneg (ENNReal.ofReal q) Y
  rw [hs, ← Real.rpow_left_inj (schattenNorm_nonneg _ _) (Real.rpow_nonneg hYn _) hs0.ne',
    schattenNorm_rpow_of_isHermitian hG hs0, sum_eigenvalues_cfc hY _ hG (fun x => |x| ^ _),
    ← Real.rpow_mul hYn, hsq, schattenNorm_rpow_of_isHermitian hY (by linarith)]
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
    rw [← avg_comp_flip i]
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
    _ = ∑ i, avg (fun ε => coin (ε i) * (A i * F (Y ε)).trace) := avg_finset_sum _ _
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hi]
      ring

private theorem avg_schattenNorm_rpow_le_aux {q : ℝ} (hq : 2 ≤ q) {k : ℕ}
    (A : Fin k → Matrix n n ℝ) (hA : ∀ i, (A i).IsHermitian)
    (Y : (Fin k → Bool) → Matrix n n ℝ) (hY : ∀ ε, Y ε = ∑ i, coin (ε i) • A i) :
    avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q) ≤
      2 * (q - 1) * avg (fun ε =>
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
      8 * (q - 1) * avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := fun i => by
    calc _ ≤ avg (fun ε => (q - 1) *
          (((Y ε - Y (SignCube.flip i ε)) * (Y ε - Y (SignCube.flip i ε)) * cfc g (Y ε)).trace +
          ((Y ε - Y (SignCube.flip i ε)) * (Y ε - Y (SignCube.flip i ε)) *
            cfc g (Y (SignCube.flip i ε))).trace)) :=
          avg_mono fun ε => trace_mean_value (hYh ε) (hYh _) hq
      _ = avg (fun ε => (q - 1) * (4 * (A i * A i * cfc g (Y ε)).trace +
          4 * (A i * A i * cfc g (Y (SignCube.flip i ε))).trace)) := by
          congr 1
          funext ε
          simp only [hsq, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
      _ = _ := by
          rw [avg_const_mul, avg_add, avg_const_mul, avg_const_mul,
            avg_comp_flip i (fun ε => (A i * A i * cfc g (Y ε)).trace)]
          ring
  calc avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q)
      = avg (fun ε => (Y ε * cfc h (Y ε)).trace) := by
        congr 1
        funext ε
        exact schattenNorm_rpow_eq_trace (hYh ε) (by linarith)
    _ = 1 / 4 * ∑ i, avg (fun ε =>
        ((Y ε - Y (SignCube.flip i ε)) * (cfc h (Y ε) - cfc h (Y (SignCube.flip i ε)))).trace) :=
        avg_trace_mul_eq A Y hY (cfc h)
    _ ≤ 1 / 4 * ∑ i, 8 * (q - 1) * avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := by
        gcongr with i
        exact hstep i
    _ = 2 * (q - 1) * ∑ i, avg (fun ε => (A i * A i * cfc g (Y ε)).trace) := by
        rw [← Finset.mul_sum]
        ring
    _ = 2 * (q - 1) * avg (fun ε => ((∑ i, A i * A i) * cfc g (Y ε)).trace) := by
        rw [← avg_finset_sum]
        congr 2
        funext ε
        rw [Finset.sum_mul, Matrix.trace_sum]

/-- The exchangeable-pair estimate: `E ‖Y‖_{S_q}^q ≤ 2 (q − 1) E tr (V |Y|^{q−2})`,
`Y = Σ_i ε_i A_i`, `V = Σ_i A_i²`. -/
theorem avg_schattenNorm_rpow_le {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (avg fun ε => schattenNorm (ENNReal.ofReal q) (∑ i, coin (ε i) • A i) ^ q) ≤
      2 * (q - 1) * avg fun ε =>
        ((∑ i, A i * A i) * cfc (fun t : ℝ => |t| ^ (q - 2)) (∑ i, coin (ε i) • A i)).trace :=
  avg_schattenNorm_rpow_le_aux hq A hA _ fun _ => rfl

/-- **Noncommutative Khintchine inequality, symmetric case, upper bound** (Mackey et al. 2014,
§7): `(E ‖Σ_i ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) ‖Σ_i A_i²‖_{S_{q/2}}^{1/2}`, `q ≥ 2`.

Departure from the source: for `q = 2` (their `p = 1`) Mackey et al. use the identity
`E [Δ_X] = E X²` (2.5), which gives the constant `1`; here the exchangeable-pair estimate
`avg_schattenNorm_rpow_le` is used for every `q ≥ 2`, and at `q = 2` it gives the constant `√2`
of the statement. -/
theorem ncKhintchine_symmetric_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (A : Fin k → Matrix n n ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • A i) ≤
      √(2 * (q - 1)) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, A i * A i)) := by
  set Y : (Fin k → Bool) → Matrix n n ℝ := fun ε => ∑ i, coin (ε i) • A i
  have hYh : ∀ ε, (Y ε).IsHermitian := fun ε =>
    show (∑ i, coin (ε i) • A i).IsHermitian from
      isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all (coin (ε i)))
  set M := avg fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q with hM
  have hlp : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q Y = M ^ (1 / q) := rfl
  rw [hlp]
  have hq0 : 0 < q := by linarith
  have hM0 : 0 ≤ M := avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  set V := ∑ i, A i * A i
  have hV : V.PosSemidef := Matrix.posSemidef_sum _ fun i _ => by
    have := Matrix.posSemidef_conjTranspose_mul_self (A i)
    rwa [(hA i).eq] at this
  have hbound : M ≤ 2 * (q - 1) * avg (fun ε =>
      (V * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace) := avg_schattenNorm_rpow_le hq A hA
  rcases hq.eq_or_lt with rfl | hq2
  · -- `q = 2`: `|t|^0 = 1`, and `‖V‖_{S_1} = tr V`
    have hG : ∀ ε, cfc (fun t : ℝ => |t| ^ ((2 : ℝ) - 2)) (Y ε) = 1 := fun ε => by
      simp only [sub_self, Real.rpow_zero]
      exact cfc_const_one ℝ (Y ε)
    simp only [hG, Matrix.mul_one, avg_const'] at hbound
    have hV1 : schattenNorm (ENNReal.ofReal (2 / 2)) V = V.trace := by
      have := schattenNorm_rpow_of_isHermitian hV.1 one_pos
      rw [Real.rpow_one] at this
      rw [div_self two_ne_zero, this, hV.1.trace_eq_sum_eigenvalues]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_one, abs_of_nonneg (hV.eigenvalues_nonneg i)]
      rfl
    rw [hV1, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hbound
  · -- `q > 2`: trace Hölder with `r = q / 2`, then Jensen
    have hr : 1 < q / 2 := by linarith
    set W := schattenNorm (ENNReal.ofReal (q / 2)) V
    have hW : 0 ≤ W := schattenNorm_nonneg _ _
    have hG : ∀ ε, (V * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace ≤
        W * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2) := fun ε => by
      have := trace_mul_le_of_posSemidef hV
        (posSemidef_cfc (f := fun t : ℝ => |t| ^ (q - 2)) (hYh ε) fun t =>
          Real.rpow_nonneg (abs_nonneg t) _) hr
      rwa [schattenNorm_cfc_abs_rpow (hYh ε) hq2] at this
    have hJ : avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) ≤
        M ^ ((q - 2) / q) := by
      have hp : 1 ≤ q / (q - 2) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      have := avg_le_avg_rpow_rpow
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
    have hMb : M ≤ 2 * (q - 1) * W * M ^ ((q - 2) / q) := by
      calc M ≤ 2 * (q - 1) * avg (fun ε =>
            (V * cfc (fun t : ℝ => |t| ^ (q - 2)) (Y ε)).trace) := hbound
        _ ≤ 2 * (q - 1) * avg (fun ε => W * schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) :=
            mul_le_mul_of_nonneg_left (avg_mono hG) (by linarith)
        _ = 2 * (q - 1) * W * avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ (q - 2)) := by
            rw [avg_const_mul]
            ring
        _ ≤ 2 * (q - 1) * W * M ^ ((q - 2) / q) :=
            mul_le_mul_of_nonneg_left hJ (mul_nonneg (by linarith) hW)
    rcases hM0.eq_or_lt with hM' | hMpos
    · rw [← hM', Real.zero_rpow (one_div_pos.mpr hq0).ne']
      positivity
    · have hsplit : M = M ^ (2 / q) * M ^ ((q - 2) / q) := by
        rw [← Real.rpow_add hMpos, show 2 / q + (q - 2) / q = 1 by field_simp; ring,
          Real.rpow_one]
      have h2 : M ^ (2 / q) ≤ 2 * (q - 1) * W := by
        refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hMpos ((q - 2) / q))
        rw [← hsplit]
        exact hMb
      have hroot : M ^ (1 / q) = √(M ^ (2 / q)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM0]
        congr 1
        ring
      rw [hroot, ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h2

end BanachProbability
