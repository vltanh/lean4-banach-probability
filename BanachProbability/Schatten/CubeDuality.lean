module

public import BanachProbability.Schatten.Holder
public import BanachProbability.Schatten.Horn
public import BanachProbability.SignCube.LpSeminorm

/-!
# Duality of `L^q (Ω; S_q)` and `L^{q'} (Ω; S_{q'})` on the sign cube

For functions `X`, `Y` on the sign cube `Ω = {±1}^N` with values in real `n × n` matrices:
Hölder's inequality `|E tr (X Y)| ≤ ‖X‖_{L^q (S_q)} ‖Y‖_{L^{q'} (S_{q'})}`
(`abs_avg_trace_mul_le`), and the norm `‖X‖_{L^q (S_q)}`, `1 < q < ∞`, is attained:
`E tr (Yᵀ X) = ‖X‖_{L^q (S_q)}` for some `Y` with `‖Y‖_{L^{q'} (S_{q'})} ≤ 1`
(`exists_avg_trace_transpose_mul_eq_lpNorm`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), the first
paragraph of the proof of Theorem D.2.6, p. 573: the trace duality of `S_{q'}` and `S_q` is
contractive, and it is isometric, by the test element `Σ_k τ_k^{q−1} f_k e_kᵀ` of `Σ_k τ_k f_k e_kᵀ`
(`trNormingElement`). The book treats a single operator; here it is the duality of functions on the
sign cube, by the same test element at every point, times a constant. (The duality
`⟨A, B⟩ = tr A Bᴴ` of Lust-Piquard and Pisier, *Non commutative Khintchine and Paley inequalities*,
Ark. Mat. 29 (1991), p. 245.)
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

/-- The norming element `A (Aᵀ A)^{(q−2)/2}` of a real matrix `A`, that is `Σ_k τ_k^{q−1} f_k e_kᵀ`
when `A = Σ_k τ_k f_k e_kᵀ` is the singular value decomposition (HNVW I, proof of Theorem D.2.6, p.
573). -/
noncomputable def trNormingElement (q : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * cfc (fun t : ℝ => t ^ ((q - 2) / 2)) (Aᵀ * A)

/-- `tr (N (A)ᵀ A) = ‖A‖_{S_q}^q`. -/
theorem trace_transpose_trNormingElement_mul {q : ℝ} (hq : 1 < q) (A : Matrix n n ℝ) :
    ((trNormingElement q A)ᵀ * A).trace = schattenNorm (ENNReal.ofReal q) A ^ q := by
  sorry

/-- `‖N (A)‖_{S_{q'}} = ‖A‖_{S_q}^{q−1}`. -/
theorem schattenNorm_trNormingElement {q q' : ℝ} (hq : q.HolderConjugate q') (A : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q') (trNormingElement q A) =
      schattenNorm (ENNReal.ofReal q) A ^ (q - 1) := by
  sorry

/-- The norm of `L^q (Ω; S_q)`, `1 < q < ∞`, is attained in the trace duality `⟨Y, X⟩ = E tr (Yᵀ X)`
(the isometry of HNVW I, Theorem D.2.6, for functions on the sign cube): for some `Y` with
`‖Y‖_{L^{q'} (S_{q'})} ≤ 1`, `E tr (Yᵀ X) = ‖X‖_{L^q (S_q)}`. -/
theorem exists_avg_trace_transpose_mul_eq_lpNorm {q q' : ℝ} (hq : q.HolderConjugate q')
    (X : (Fin N → Bool) → Matrix n n ℝ) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ,
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y ≤ 1 ∧
      (avg fun ε => ((Y ε)ᵀ * X ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X := by
  sorry

end BanachProbability
