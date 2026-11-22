module

public import BanachProbability.Schatten.Holder
public import BanachProbability.Schatten.Horn
public import BanachProbability.SignCube.LpSeminorm

/-!
# Duality of `L^r (Ω; S_q)` and `L^{r'} (Ω; S_{q'})` on the sign cube

For functions `X`, `Y` on the sign cube `Ω = {±1}^N` with values in real `n × n` matrices:
Hölder's inequality `|E tr (X Y)| ≤ ‖X‖_{L^q (S_q)} ‖Y‖_{L^{q'} (S_{q'})}`
(`abs_avg_trace_mul_le`), and, when the values of `X` are symmetric, the norm
`‖X‖_{L^r (S_q)}`, `1 < q, r < ∞`, is attained: `E tr (X Y) = ‖X‖_{L^r (S_q)}` for some symmetric
`Y` with `‖Y‖_{L^{r'} (S_{q'})} ≤ 1` (`exists_avg_trace_mul_eq_lpNorm_of_holderConjugate`; for
`r = q`, `exists_avg_trace_mul_eq_lpNorm`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), the first
paragraph of the proof of Theorem D.2.6, p. 573: the trace duality `⟨Λ v, u⟩ = tr (v u)` of `S_{q'}`
and `S_q` is contractive, and it is isometric, by the test element `Σ_k τ_k^{q−1} e_k f_kᵀ` of
`Σ_k τ_k f_k e_kᵀ`. The book treats a single operator. Here it is the duality of functions on the
sign cube, by the same test element at every point (`normingElement`, defined for symmetric
matrices, hence the symmetry of `X`), times a scalar function.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Hölder's inequality for averages over the sign cube: `E f g ≤ (E f^q)^{1/q} (E g^{q'})^{1/q'}`
for `f, g ≥ 0`. -/
theorem avg_mul_le_rpow_mul_rpow {q q' : ℝ} (hq : q.HolderConjugate q')
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

/-- Hölder's inequality `|E tr (X Y)| ≤ ‖X‖_{L^q (S_q)} ‖Y‖_{L^{q'} (S_{q'})}` (the first line of
the proof of HNVW I, Theorem D.2.6, p. 573, at every point, and Hölder's inequality on the cube). -/
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

/-- The norm of `L^r (Ω; S_q)`, `1 < q, r < ∞`, is attained: for symmetric `X` there is a symmetric
`Y` with `‖Y‖_{L^{r'} (S_{q'})} ≤ 1` and `E tr (X Y) = ‖X‖_{L^r (S_q)}`. It is
`Y (ε) = ‖X‖^{1−r} ‖X (ε)‖_{S_q}^{r−q} N (X (ε))` with the norming element `N` (the test element of
HNVW I, proof of Theorem D.2.6, p. 573). -/
theorem exists_avg_trace_mul_eq_lpNorm_of_holderConjugate {q q' r r' : ℝ}
    (hq : q.HolderConjugate q') (hr : r.HolderConjugate r')
    (X : (Fin N → Bool) → Matrix n n ℝ) (hX : ∀ ε, (X ε).IsHermitian) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (Y ε).IsHermitian) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) r' Y ≤ 1 ∧
      (avg fun ε => (X ε * Y ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) r X := by
  have hq1 : 1 < q := hq.lt
  have hr1 : 1 < r := hr.lt
  have hq'ne : ENNReal.ofReal q' ≠ 0 := (ENNReal.ofReal_pos.2 hq.symm.pos).ne'
  set s : (Fin N → Bool) → ℝ := fun ε => schattenNorm (ENNReal.ofReal q) (X ε)
  have hs : ∀ ε, 0 ≤ s ε := fun ε => schattenNorm_nonneg _ _
  set L := SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) r X
  have hL : 0 ≤ L := lpNorm_nonneg (schattenNorm_nonneg _) r X
  have hLr : (avg fun ε => s ε ^ r) = L ^ r := (lpNorm_rpow (schattenNorm_nonneg _) hr.pos X).symm
  have hpow : 0 ≤ (L ^ (r - 1))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hL _)
  refine ⟨fun ε => ((L ^ (r - 1))⁻¹ * s ε ^ (r - q)) • normingElement q (X ε), fun ε =>
    (isHermitian_normingElement q (X ε)).smul (IsSelfAdjoint.all _), ?_, ?_⟩
  · -- `‖Y (ε)‖_{S_{q'}}^{r'} = (‖X‖^{1−r} ‖X (ε)‖^{r−1})^{r'} = ‖X‖^{−r} ‖X (ε)‖^r`
    have hY : ∀ ε, schattenNorm (ENNReal.ofReal q')
        (((L ^ (r - 1))⁻¹ * s ε ^ (r - q)) • normingElement q (X ε)) ^ r' =
          (L ^ r)⁻¹ * s ε ^ r := fun ε => by
      have h := schattenNorm_normingElement (hX ε) hq1
      rw [← hq.conjugate_eq] at h
      rw [schattenNorm_smul hq'ne, h,
        abs_of_nonneg (mul_nonneg hpow (Real.rpow_nonneg (hs ε) _)), mul_assoc,
        ← Real.rpow_add' (hs ε) (by linarith), sub_add_sub_cancel,
        Real.mul_rpow hpow (Real.rpow_nonneg (hs ε) _), Real.inv_rpow (Real.rpow_nonneg hL _),
        ← Real.rpow_mul hL, ← Real.rpow_mul (hs ε), hr.sub_one_mul_conj]
    unfold SignCube.lpNorm
    simp only [hY]
    rw [avg_const_mul, hLr]
    exact Real.rpow_le_one (mul_nonneg (inv_nonneg.2 (Real.rpow_nonneg hL _))
      (Real.rpow_nonneg hL _)) inv_mul_le_one (by have := hr.symm.pos; positivity)
  · -- `E tr (X Y) = ‖X‖^{1−r} E ‖X (ε)‖^r = ‖X‖`
    have ht : ∀ ε, (X ε * (((L ^ (r - 1))⁻¹ * s ε ^ (r - q)) • normingElement q (X ε))).trace =
        (L ^ (r - 1))⁻¹ * s ε ^ r := fun ε => by
      rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_normingElement (hX ε) hq1, smul_eq_mul,
        mul_assoc, ← Real.rpow_add' (hs ε) (by linarith), sub_add_cancel]
    simp only [ht]
    rw [avg_const_mul, hLr]
    rcases hL.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hr.ne_zero, mul_zero]
    · rw [← div_eq_inv_mul, ← Real.rpow_sub h, sub_sub_cancel, Real.rpow_one]

/-- The norm of `L^q (Ω; S_q)` is attained: for symmetric `X` there is a symmetric `Y` with
`‖Y‖_{L^{q'} (S_{q'})} ≤ 1` and `E tr (X Y) = ‖X‖_{L^q (S_q)}`. -/
theorem exists_avg_trace_mul_eq_lpNorm {q q' : ℝ} (hq : q.HolderConjugate q')
    (X : (Fin N → Bool) → Matrix n n ℝ) (hX : ∀ ε, (X ε).IsHermitian) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (Y ε).IsHermitian) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y ≤ 1 ∧
      (avg fun ε => (X ε * Y ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X :=
  exists_avg_trace_mul_eq_lpNorm_of_holderConjugate hq hq X hX

end BanachProbability
