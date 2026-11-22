module

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
contractive, and it is isometric, by the test element `u = Σ_k τ_k^{q−1} e_k f_kᵀ` of
`v = Σ_k τ_k f_k e_kᵀ` (`u = N (v)ᵀ`, `trNormingElement`). The book treats a single operator; here
it is the duality of functions on the sign cube, by the same test element at every point, times a
constant. The pairing `⟨Y, X⟩ = tr (Yᵀ X) = tr (X Yᵀ)` at a point is the real form of the duality
`⟨A, B⟩ = tr A Bᴴ` of F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley
inequalities*, Ark. Mat. 29 (1991) 241–260, p. 245, who cite B. Simon, *Trace ideals and their
applications* (1979), Theorem 3.2, for the dual of `C_E`.
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

/-- The norming element `N (A) = A (Aᵀ A)^{(q−2)/2}` of a real matrix `A`, that is
`Σ_k τ_k^{q−1} f_k e_kᵀ` when `A = Σ_k τ_k f_k e_kᵀ` is the singular value decomposition; its
transpose is the test element in HNVW I, proof of Theorem D.2.6, p. 573. (For `q < 2` the function
`t^{(q−2)/2}` is `0` at `t = 0`; its value there does not matter, as `A` vanishes on the kernel of
`Aᵀ A`.) -/
noncomputable def trNormingElement (q : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * cfc (fun t : ℝ => t ^ ((q - 2) / 2)) (Aᵀ * A)

/-- `t^{(q−2)/2} t = s^q` for `t = s²`, `s ≥ 0` (also for `s = 0`, as `q > 0`). -/
private theorem rpow_mul_self_eq {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) :
    t ^ ((q - 2) / 2) * t = √t ^ q := by
  rcases ht.eq_or_lt with rfl | h
  · rw [mul_zero, Real.sqrt_zero, Real.zero_rpow hq.ne']
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht, ← Real.rpow_add_one h.ne']
    congr 1
    ring

/-- `(t^{(q−2)/2} t t^{(q−2)/2})^{q'/2} = s^{(q−1) q'} = s^q` for `t = s²`, `s ≥ 0` (also for
`s = 0`, as `q > 1`). -/
private theorem sqrt_rpow_mul_self_mul_rpow {q q' t : ℝ} (hq : q.HolderConjugate q') (ht : 0 ≤ t) :
    √(t ^ ((q - 2) / 2) * t * t ^ ((q - 2) / 2)) ^ q' = √t ^ q := by
  rcases ht.eq_or_lt with rfl | h
  · rw [mul_zero, zero_mul, Real.sqrt_zero, Real.zero_rpow hq.symm.ne_zero,
      Real.zero_rpow hq.ne_zero]
  · rw [← Real.rpow_add_one h.ne', ← Real.rpow_add h, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht, ← Real.rpow_mul ht, ← Real.rpow_mul ht]
    congr 1
    linear_combination (1 / 2 : ℝ) * hq.sub_one_mul_conj

/-- `(A f (Aᵀ A))ᵀ A = (t ↦ f (t) t) (Aᵀ A)`. -/
private theorem transpose_mul_cfc_mul (A : Matrix n n ℝ) (f : ℝ → ℝ) :
    (A * cfc f (Aᵀ * A))ᵀ * A = cfc (fun t => f t * t) (Aᵀ * A) := by
  have hA : IsSelfAdjoint (Aᵀ * A) := Matrix.isHermitian_conjTranspose_mul_self A
  have hC : (cfc f (Aᵀ * A))ᵀ = cfc f (Aᵀ * A) := isHermitian_cfc f _
  rw [Matrix.transpose_mul, hC, Matrix.mul_assoc,
    cfc_mul f (fun t => t) _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
    cfc_id' ℝ _ hA]

/-- `tr (N (A)ᵀ A) = Σ_k τ_k^q = ‖A‖_{S_q}^q` (HNVW I, proof of Theorem D.2.6, p. 573). -/
theorem trace_transpose_trNormingElement_mul {q : ℝ} (hq : 0 < q) (A : Matrix n n ℝ) :
    ((trNormingElement q A)ᵀ * A).trace = schattenNorm (ENNReal.ofReal q) A ^ q := by
  have hA : (Aᵀ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  -- `tr (N (A)ᵀ A) = tr (f (Aᵀ A) Aᵀ A) = Σ s_i^{q−2} s_i²`
  rw [trNormingElement, transpose_mul_cfc_mul, trace_cfc_eq_sum hA, schattenNorm_ofReal_rpow hq]
  exact Finset.sum_congr rfl fun i _ => rpow_mul_self_eq hq
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- `‖N (A)‖_{S_{q'}} = ‖A‖_{S_q}^{q−1}`, that is `‖N (A)‖_{S_{q'}}^{q'} = ‖A‖_{S_q}^q` (HNVW I,
proof of Theorem D.2.6, p. 573): the singular values of `N (A)` are the `τ_k^{q−1}`. -/
theorem schattenNorm_trNormingElement {q q' : ℝ} (hq : q.HolderConjugate q') (A : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q') (trNormingElement q A) =
      schattenNorm (ENNReal.ofReal q) A ^ (q - 1) := by
  have hA : (Aᵀ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  set f : ℝ → ℝ := fun t => t ^ ((q - 2) / 2)
  -- `N (A)ᵀ N (A) = f (Aᵀ A) Aᵀ A f (Aᵀ A)`
  have hN : (trNormingElement q A)ᴴ * trNormingElement q A =
      cfc (fun t => f t * t * f t) (Aᵀ * A) := by
    rw [trNormingElement, Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc,
      transpose_mul_cfc_mul, ← cfc_mul (fun t => f t * t) f _ (continuousOn_spectrum _ _)
        (continuousOn_spectrum _ _)]
  -- hence `‖N (A)‖_{S_{q'}}^{q'} = Σ s_i^{(q−1) q'} = ‖A‖_{S_q}^q`
  have h : schattenNorm (ENNReal.ofReal q') (trNormingElement q A) ^ q' =
      schattenNorm (ENNReal.ofReal q) A ^ q := by
    rw [schattenNorm_ofReal_rpow hq.symm.pos, schattenNorm_ofReal_rpow hq.pos]
    have hH := Matrix.isHermitian_conjTranspose_mul_self (trNormingElement q A)
    have hS : ∑ i, √(hH.eigenvalues i) ^ q' =
        ∑ i, √(f (hA.eigenvalues i) * hA.eigenvalues i * f (hA.eigenvalues i)) ^ q' := by
      have hB := isHermitian_cfc (fun t => f t * t * f t) (Aᵀ * A)
      simp only [hN]
      exact sum_comp_eigenvalues_cfc hA (fun t => f t * t * f t) hB fun t => √t ^ q'
    refine hS.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact sqrt_rpow_mul_self_mul_rpow hq (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  rw [← Real.rpow_left_inj (schattenNorm_nonneg _ _)
    (Real.rpow_nonneg (schattenNorm_nonneg _ _) _) hq.symm.ne_zero, h,
    ← Real.rpow_mul (schattenNorm_nonneg _ _), hq.sub_one_mul_conj]

/-- The norm of `L^q (Ω; S_q)`, `1 < q < ∞`, is attained in the trace duality `⟨Y, X⟩ = E tr (Yᵀ X)`
(the isometry of HNVW I, Theorem D.2.6, for functions on the sign cube): for some `Y` with
`‖Y‖_{L^{q'} (S_{q'})} ≤ 1`, `E tr (Yᵀ X) = ‖X‖_{L^q (S_q)}`. -/
theorem exists_avg_trace_transpose_mul_eq_lpNorm {q q' : ℝ} (hq : q.HolderConjugate q')
    (X : (Fin N → Bool) → Matrix n n ℝ) :
    ∃ Y : (Fin N → Bool) → Matrix n n ℝ,
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' Y ≤ 1 ∧
      (avg fun ε => ((Y ε)ᵀ * X ε).trace) =
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X := by
  set L := SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q X
  have hL : 0 ≤ L := lpNorm_nonneg (schattenNorm_nonneg _) q X
  have hLq : (avg fun ε => schattenNorm (ENNReal.ofReal q) (X ε) ^ q) = L ^ q :=
    (lpNorm_rpow (schattenNorm_nonneg _) hq.pos X).symm
  have hc : 0 ≤ (L ^ (q - 1))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hL _)
  -- `Y (ε) = ‖X‖^{1−q} N (X (ε))`, which is `0` if `‖X‖ = 0`
  refine ⟨fun ε => (L ^ (q - 1))⁻¹ • trNormingElement q (X ε), ?_, ?_⟩
  · -- `‖Y (ε)‖_{S_{q'}}^{q'} = (‖X‖^{1−q} ‖X (ε)‖^{q−1})^{q'} = ‖X‖^{−q} ‖X (ε)‖^q`
    have hY : ∀ ε, schattenNorm (ENNReal.ofReal q')
        ((L ^ (q - 1))⁻¹ • trNormingElement q (X ε)) ^ q' =
          (L ^ q)⁻¹ * schattenNorm (ENNReal.ofReal q) (X ε) ^ q := fun ε => by
      rw [schattenNorm_smul (ENNReal.ofReal_pos.2 hq.symm.pos).ne',
        schattenNorm_trNormingElement hq, abs_of_nonneg hc,
        Real.mul_rpow hc (Real.rpow_nonneg (schattenNorm_nonneg _ _) _),
        Real.inv_rpow (Real.rpow_nonneg hL _), ← Real.rpow_mul hL,
        ← Real.rpow_mul (schattenNorm_nonneg _ _), hq.sub_one_mul_conj]
    unfold SignCube.lpNorm
    simp only [hY]
    rw [avg_const_mul, hLq]
    exact Real.rpow_le_one (mul_nonneg (inv_nonneg.2 (Real.rpow_nonneg hL _))
      (Real.rpow_nonneg hL _)) inv_mul_le_one (one_div_nonneg.2 hq.symm.nonneg)
  · -- `E tr (Yᵀ X) = ‖X‖^{1−q} E ‖X (ε)‖^q = ‖X‖`
    have ht : ∀ ε, (((L ^ (q - 1))⁻¹ • trNormingElement q (X ε))ᵀ * X ε).trace =
        (L ^ (q - 1))⁻¹ * schattenNorm (ENNReal.ofReal q) (X ε) ^ q := fun ε => by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul,
        trace_transpose_trNormingElement_mul hq.pos, smul_eq_mul]
    simp only [ht]
    rw [avg_const_mul, hLq]
    rcases hL.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hq.ne_zero, mul_zero]
    · rw [← div_eq_inv_mul, ← Real.rpow_sub h, sub_sub_cancel, Real.rpow_one]

end BanachProbability
