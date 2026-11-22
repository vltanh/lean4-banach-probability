module

public import BanachProbability.Schatten.Horn
public import BanachProbability.SignCube.LpSeminorm

/-!
# Duality of `L^q (Ω; S_q)` and `L^{q'} (Ω; S_{q'})` on the sign cube

For functions `X`, `Y` on the sign cube `Ω = {±1}^N` with values in real `n × n` matrices:
Hölder's inequality `|E tr (X Y)| ≤ ‖X‖_{L^q (S_q)} ‖Y‖_{L^{q'} (S_{q'})}`
(`abs_avg_trace_mul_le`), with equality for some `Y` of norm at most `1` when `X` is symmetric
(`exists_avg_trace_mul_eq_lpNorm`; HNVW I, Theorem D.2.6, p. 572).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Hölder's inequality for averages over the sign cube: `E f g ≤ (E f^q)^{1/q} (E g^{q'})^{1/q'}`
for `f, g ≥ 0`. -/
private theorem avg_mul_le_rpow_mul_rpow {q q' : ℝ} (hq : q.HolderConjugate q')
    {f g : (Fin N → Bool) → ℝ} (hf : ∀ ε, 0 ≤ f ε) (hg : ∀ ε, 0 ≤ g ε) :
    (avg fun ε => f ε * g ε) ≤
      (avg fun ε => f ε ^ q) ^ (1 / q) * (avg fun ε => g ε ^ q') ^ (1 / q') := by
  have hc : (0 : ℝ) < 2 ^ N := by positivity
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hq (fun ε _ => hf ε) fun ε _ => hg ε
  have hc1 : ((2 : ℝ) ^ N) ^ (1 / q) * ((2 : ℝ) ^ N) ^ (1 / q') = 2 ^ N := by
    rw [← Real.rpow_add hc, one_div, one_div, hq.inv_add_inv_eq_one, Real.rpow_one]
  unfold avg
  rw [Real.div_rpow (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (hf ε) q) hc.le,
    Real.div_rpow (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (hg ε) q') hc.le,
    div_mul_div_comm, hc1]
  exact div_le_div_of_nonneg_right h hc.le

/-- Hölder's inequality in `L^q (Ω; S_q)`. -/
theorem abs_avg_trace_mul_le {q q' : ℝ} (hq : q.HolderConjugate q')
    (X Y : (Fin N → Bool) → Matrix n n ℝ) :
    |avg fun ε => (X ε * Y ε).trace| ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X *
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y := by
  calc |avg fun ε => (X ε * Y ε).trace|
      ≤ avg fun ε => |(X ε * Y ε).trace| := by
        unfold avg
        rw [abs_div, abs_of_pos (a := (2 : ℝ) ^ N) (by positivity)]
        exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ avg fun ε => schattenNorm (ENNReal.ofReal q) (X ε) *
          schattenNorm (ENNReal.ofReal q') (Y ε) :=
        avg_mono fun ε => abs_trace_mul_le hq (X ε) (Y ε)
    _ ≤ _ := avg_mul_le_rpow_mul_rpow hq (fun ε => schattenNorm_nonneg _ _)
        fun ε => schattenNorm_nonneg _ _

/-- The norm of `L^q (Ω; S_q)` is attained: for symmetric `X` there is a symmetric `Y` with
`‖Y‖_{L^{q'} (S_{q'})} ≤ 1` and `E tr (X Y) = ‖X‖_{L^q (S_q)}`. -/
theorem exists_avg_trace_mul_eq_lpNorm {q q' : ℝ} (hq : q.HolderConjugate q')
    (X : (Fin N → Bool) → Matrix n n ℝ) (hX : ∀ ε, (X ε).IsHermitian) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (Y ε).IsHermitian) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y ≤ 1 ∧
      (avg fun ε => (X ε * Y ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X := by
  have hq1 : 1 < q := hq.lt
  have hq0 : 0 < q := hq.pos
  have hq'0 : 0 < q' := hq.symm.pos
  have hq' : q' = q / (q - 1) := hq.conjugate_eq
  have hqq' : (q - 1) * q' = q := hq.sub_one_mul_conj
  have hq'ne : ENNReal.ofReal q' ≠ 0 := (ENNReal.ofReal_pos.2 hq'0).ne'
  set A := SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X
  have hAq : A ^ q = avg fun ε => schattenNorm (ENNReal.ofReal q) (X ε) ^ q :=
    lpNorm_rpow (schattenNorm_nonneg _) hq0 X
  rcases (lpNorm_nonneg (schattenNorm_nonneg (ENNReal.ofReal q)) q X).eq_or_lt with hA | hA
  · -- `‖X‖ = 0`: take `Y = 0`
    refine ⟨fun _ => 0, fun _ => Matrix.isHermitian_zero, ?_, ?_⟩
    · rw [lpNorm_const (schattenNorm_nonneg _ _) hq'0, schattenNorm_zero hq'ne]
      exact zero_le_one
    · simp only [Matrix.mul_zero, Matrix.trace_zero, avg_const]
      exact hA
  · -- `Y = c normingElement q (X)`, `c = ‖X‖^{1 - q}`
    have hAp : 0 < A ^ (q - 1) := Real.rpow_pos_of_pos hA _
    set c := (A ^ (q - 1))⁻¹ with hc
    have hc0 : 0 < c := inv_pos.2 hAp
    refine ⟨fun ε => c • normingElement q (X ε),
      fun ε => (isHermitian_normingElement q (X ε)).smul (IsSelfAdjoint.all _), le_of_eq ?_, ?_⟩
    · -- `E ‖Y‖_{S_{q'}}^{q'} = c^{q'} E ‖X‖_{S_q}^q = 1`
      have hY : ∀ ε, schattenNorm (ENNReal.ofReal q') (c • normingElement q (X ε)) ^ q' =
          c ^ q' * schattenNorm (ENNReal.ofReal q) (X ε) ^ q := fun ε => by
        have h := schattenNorm_normingElement (hX ε) hq1
        rw [← hq'] at h
        rw [schattenNorm_smul hq'ne, abs_of_pos hc0, h, Real.mul_rpow hc0.le
          (Real.rpow_nonneg (schattenNorm_nonneg _ _) _), ← Real.rpow_mul (schattenNorm_nonneg _ _),
          hqq']
      have h1 : c ^ q' * A ^ q = 1 := by
        rw [hc, Real.inv_rpow hAp.le, ← Real.rpow_mul hA.le, hqq',
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hA _).ne']
      unfold SignCube.lpNorm
      simp only [hY]
      rw [avg_const_mul, ← hAq, h1, Real.one_rpow]
    · -- `E tr (X Y) = c E ‖X‖_{S_q}^q = ‖X‖`
      simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, avg_const_mul,
        trace_mul_normingElement (hX _) hq1]
      rw [← hAq, hc, ← div_eq_inv_mul, ← Real.rpow_sub hA, sub_sub_cancel, Real.rpow_one]

end BanachProbability
