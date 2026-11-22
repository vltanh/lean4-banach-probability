module

public import BanachProbability.Schatten.Holder
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The lower noncommutative Khintchine inequality

For real `n × n` matrices `x_1, …, x_k` and `q ≥ 2`, with `S (ε) = Σ_i ε_i x_i`,
`‖(Σ_i x_iᵀ x_i)^{1/2}‖_{S_q} ≤ (E ‖S‖_{S_q}^q)^{1/q}` and the same with `x_i x_iᵀ`, with
constant `1` and no normality assumption (`ncKhintchine_lower_col`, `ncKhintchine_lower_row`;
F. Lust-Piquard, *Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303
(1986); G. Pisier and Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach
Spaces 2 (2003), Theorem 6.1).

The proof is the standard convexity argument: `‖S‖_q^q = ‖Sᵀ S‖_{q/2}^{q/2}`; Jensen's inequality
for `t ↦ t^{q/2}`, then the convexity of the `S_{q/2}` norm on positive semidefinite matrices
(`schattenNorm_sum_le_of_posSemidef`), give `E ‖Sᵀ S‖_{q/2}^{q/2} ≥ ‖E Sᵀ S‖_{q/2}^{q/2}`; and
`E Sᵀ S = Σ_i x_iᵀ x_i` by the orthonormality of the signs. The row version follows from the
column version applied to the `x_iᵀ`, by `‖Sᵀ‖_{S_q} = ‖S‖_{S_q}`.

The elementary facts about the average over the sign cube that the proof uses (orthonormality of
the signs, flip invariance, Jensen's inequality) are proved here as private lemmas.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary facts about the average over the sign cube -/

section Cube

variable {N : ℕ}

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

/-- The signs are orthonormal: `E [ε_i ε_j] = δ_{ij}`. -/
private theorem avg_coin_mul_coin (i j : Fin N) :
    avg (fun ε => coin (ε i) * coin (ε j)) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    simp only [coin_mul_self]
    exact avg_const' 1
  · have h1 := avg_comp_flip i (fun ε => coin (ε i) * coin (ε j))
    simp only [flip_apply_self, flip_apply_of_ne (Ne.symm h), coin_not] at h1
    have h2 := avg_const_mul (-1) (fun ε => coin (ε i) * coin (ε j))
    simp only [neg_one_mul, ← neg_mul] at h2
    linarith

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

/-- **Lower noncommutative Khintchine inequality** (column square function):
`‖Σ_i x_iᵀ x_i‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}`, `q ≥ 2`. -/
theorem ncKhintchine_lower_col {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) := by
  set Y : (Fin k → Bool) → Matrix n n ℝ := fun ε => ∑ i, coin (ε i) • x i with hYdef
  set M := avg fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ q with hM
  have hlp : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q Y = M ^ (1 / q) := rfl
  rw [hlp]
  have hq0 : 0 < q := by linarith
  have hr : 1 ≤ q / 2 := by linarith
  have hM0 : 0 ≤ M := avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  -- `E [Yᵀ Y] = Σ_i x_iᵀ x_i`, by the orthonormality of the signs
  have hmean : ∑ ε, ((2 : ℝ) ^ k)⁻¹ • ((Y ε)ᵀ * Y ε) = ∑ i, (x i)ᵀ * x i := by
    have hexp : ∀ ε, (Y ε)ᵀ * Y ε =
        ∑ i, ∑ j, (coin (ε i) * coin (ε j)) • ((x i)ᵀ * x j) := fun ε => by
      simp only [hYdef, Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul_sum,
        smul_mul_smul_comm]
    have hcoin : ∀ i j, ∑ ε : Fin k → Bool, ((2 : ℝ) ^ k)⁻¹ * (coin (ε i) * coin (ε j)) =
        if i = j then 1 else 0 := fun i j => by
      rw [← avg_coin_mul_coin i j, avg, ← Finset.mul_sum, div_eq_inv_mul]
    simp only [hexp, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hcoin, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  -- `‖Yᵀ Y‖_{S_{q/2}} = ‖Y‖_{S_q}²`
  have hYY : ∀ ε, schattenNorm (ENNReal.ofReal (q / 2)) ((Y ε)ᵀ * Y ε) =
      schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2 := fun ε => by
    have := schattenNorm_transpose_mul_self (ENNReal.ofReal_pos.mpr hq0).ne' (Y ε)
    rwa [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos two_pos] at this
  -- convexity of the `S_{q/2}` norm on positive semidefinite matrices
  have h1 : schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i) ≤
      avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2) := by
    rw [← hmean]
    refine (schattenNorm_sum_le_of_posSemidef _ (fun ε _ => ?_) hr).trans (le_of_eq ?_)
    · have := Matrix.posSemidef_conjTranspose_mul_self (Y ε)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
      exact this.smul (by positivity)
    · rw [avg, Finset.sum_div]
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [schattenNorm_smul (ENNReal.ofReal_pos.mpr (by linarith)).ne', hYY,
        abs_of_pos (by positivity), div_eq_inv_mul]
  -- Jensen's inequality for `t ↦ t^{q/2}`
  have h2 : avg (fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2) ≤ M ^ (2 / q) := by
    have := avg_le_avg_rpow_rpow (X := fun ε => schattenNorm (ENNReal.ofReal q) (Y ε) ^ 2)
      (fun ε => by positivity) hr
    convert this using 2
    · rw [hM]
      congr 1
      funext ε
      rw [← Real.rpow_natCast, ← Real.rpow_mul (schattenNorm_nonneg _ _)]
      congr 1
      push_cast
      ring
    · field_simp
  calc √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i)) ≤ √(M ^ (2 / q)) :=
        Real.sqrt_le_sqrt (h1.trans h2)
    _ = M ^ (1 / q) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM0]
      congr 1
      ring

/-- **Lower noncommutative Khintchine inequality** (row square function):
`‖Σ_i x_i x_iᵀ‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}`, `q ≥ 2`. -/
theorem ncKhintchine_lower_row {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) := by
  have h := ncKhintchine_lower_col hq (fun i => (x i)ᵀ)
  simp only [Matrix.transpose_transpose] at h
  refine h.trans (le_of_eq ?_)
  -- `(Σ_i ε_i x_i)ᵀ = Σ_i ε_i x_iᵀ`
  unfold SignCube.lpNorm
  congr 2
  funext ε
  rw [← schattenNorm_transpose _ (∑ i, coin (ε i) • x i), Matrix.transpose_sum]
  simp only [Matrix.transpose_smul]

end BanachProbability
