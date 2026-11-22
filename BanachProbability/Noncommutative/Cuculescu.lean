module

public import BanachProbability.Noncommutative.Transform
public import BanachProbability.Noncommutative.Distribution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Cuculescu's projections

For a positive semidefinite matrix-valued function `x` on a probability space with a filtration
`ℱ`, with martingale `x_k = E_k x`, and `λ > 0`, Cuculescu's projections (I. Cuculescu,
*Martingales on von Neumann algebras*, J. Multivariate Anal. 1 (1971); N. Randrianantoanina,
*Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002), Proposition 2.4) are the
random projections defined recursively, pointwise in `ω`, by `q_0 = 1` and
`q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)` (`cuculescu`); with this indexing `q_{k+1}` is
`ℱ_k`-measurable, the Cuculescu projection at time `k`.

(The statements and the proofs of Proposition 2.4 (i)–(iv), Lemma 3.3 (the supermartingale
property of the compressed process `z_k = q_{k+1} x_k q_{k+1}`), the Doob decomposition (3.3)–(3.6)
and Lemma 3.4 follow the source; see the declarations below.)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- Cuculescu's projections `q_0 = 1`, `q_{k+1} = q_k 1_{[0, λ]} (q_k X_k q_k)` of a sequence `X`
of matrix-valued functions (the martingale `X_k = E_k x`) at level `λ`, pointwise in `ω`.
Randrianantoanina writes `q_{k+1} = 1_{[0, λ]} (q_k x_k q_k)`; its proof requires reading this in
the reduced algebra `q_k N q_k`, i.e. as `q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)`, which is the
definition here (read literally, `q_{k+1} ≥ 1 − q_k`, since `q_k x_k q_k` vanishes on the range of
`1 − q_k`, and the projections would not decrease). -/
noncomputable def cuculescu (X : ℕ → Ω → Matrix n n ℝ) (l : ℝ) : ℕ → Ω → Matrix n n ℝ
  | 0 => fun _ => 1
  | k + 1 => fun ω =>
      cuculescu X l k ω * spectralProj (cuculescu X l k ω * X k ω * cuculescu X l k ω) (Set.Icc 0 l)

/-! ### Matrix lemmas -/

omit [DecidableEq n] in
/-- `q X q ⪰ 0` for `X ⪰ 0` and `q` symmetric. -/
private theorem cuc_posSemidef_conj {q X : Matrix n n ℝ} (hqt : qᵀ = q) (hX : X.PosSemidef) :
    (q * X * q).PosSemidef := by
  have h := hX.conjTranspose_mul_mul_same q
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hqt] at h

private theorem cuc_cont (f : ℝ → ℝ) (A : Matrix n n ℝ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn _

/-- A function of a matrix that is nonnegative on its spectrum is positive semidefinite:
`g (B) = h (B)ᵀ h (B)` with `h = √g`. -/
private theorem cuc_posSemidef_cfc {B : Matrix n n ℝ} {g : ℝ → ℝ}
    (hg : ∀ t ∈ spectrum ℝ B, 0 ≤ g t) : (cfc g B).PosSemidef := by
  have hC : (cfc (fun t => Real.sqrt (g t)) B).IsHermitian := cfc_predicate _ B
  have hCC : cfc (fun t => Real.sqrt (g t)) B * cfc (fun t => Real.sqrt (g t)) B = cfc g B := by
    rw [← cfc_mul _ _ B (cuc_cont _ _) (cuc_cont _ _)]
    exact cfc_congr fun t ht => Real.mul_self_sqrt (hg t ht)
  have h := Matrix.posSemidef_conjTranspose_mul_self (cfc (fun t => Real.sqrt (g t)) B)
  rwa [hC.eq, hCC] at h

/-- The spectrum of a positive semidefinite matrix is nonnegative. -/
private theorem cuc_spectrum_nonneg {B : Matrix n n ℝ} (hB : B.PosSemidef) {t : ℝ}
    (ht : t ∈ spectrum ℝ B) : 0 ≤ t := by
  rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  rw [hB.isHermitian.eigenvalues_eq]
  exact hB.dotProduct_mulVec_nonneg _

omit [DecidableEq n] in
private theorem cuc_posSemidef_proj {q : Matrix n n ℝ} (hq : q * q = q) (hqt : qᵀ = q) :
    q.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self q
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hqt, hq] at h

private theorem cuc_posSemidef_one_sub {q : Matrix n n ℝ} (hq : q * q = q) (hqt : qᵀ = q) :
    (1 - q).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - q)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, Matrix.transpose_one,
    hqt, sub_mul, one_mul, mul_sub, mul_one, hq, sub_self, sub_zero] at h

omit [DecidableEq n] in
/-- `tr (q X q) = tr (q X)` for a projection `q`. -/
private theorem cuc_trace_mul_eq {q X : Matrix n n ℝ} (hq : q * q = q) :
    (q * X * q).trace = (q * X).trace := by
  rw [Matrix.trace_mul_cycle, hq]

omit [DecidableEq n] in
/-- `tr ((u + v)²) ≤ 2 tr (u²) + 2 tr (v²)` for symmetric `u`, `v` (convexity of `‖·‖₂²`). -/
private theorem cuc_trace_sq_add_le {u v : Matrix n n ℝ} (hu : u.IsHermitian) (hv : v.IsHermitian) :
    ((u + v) * (u + v)).trace ≤ 2 * (u * u).trace + 2 * (v * v).trace := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (u - v)).trace_nonneg
  rw [(hu.sub hv).eq] at h
  have e : (u + v) * (u + v) + (u - v) * (u - v) = u * u + u * u + (v * v + v * v) := by
    noncomm_ring
  have e2 := congrArg Matrix.trace e
  simp only [Matrix.trace_add] at e2
  linarith

omit [DecidableEq n] in
/-- The estimate of `‖a − E a‖₂²` through `a − E a = (a − b) + (b − E a)`, pointwise. -/
private theorem cuc_trace_split_le {a b e : Matrix n n ℝ} (ha : a.IsHermitian) (hb : b.IsHermitian)
    (he : e.IsHermitian) :
    ((a - e) * (a - e)).trace ≤ 2 * (a * a).trace + 2 * (b * b).trace - 4 * (b * a).trace +
      2 * ((b - e) * (b - e)).trace := by
  have h := cuc_trace_sq_add_le (ha.sub hb) (hb.sub he)
  rw [sub_add_sub_cancel] at h
  have e1 : ((a - b) * (a - b)).trace = (a * a).trace + (b * b).trace - 2 * (b * a).trace := by
    rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_mul_comm a b]
    ring
  linarith

omit [DecidableEq n] in
private theorem cuc_trace_add_mul_self (Y D : Matrix n n ℝ) :
    ((Y + D) * (Y + D)).trace = (Y * Y).trace + 2 * (Y * D).trace + (D * D).trace := by
  rw [add_mul, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_mul_comm D Y]
  ring

omit [DecidableEq n] in
private theorem cuc_conj_sub {q B P : Matrix n n ℝ} (l : ℝ) (hq : q * q = q) (hqB : q * B = B)
    (hBq : B * q = B) (hPq : P * q = q * P) :
    q * (l • P - B * P) * q = l • (q * P) - B * P := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc q P q, hPq, ← mul_assoc q q P, hq,
    ← mul_assoc q B P, hqB, mul_assoc B P q, hPq, ← mul_assoc B q P, hBq]

private theorem cuc_conj_sub' {q B P : Matrix n n ℝ} (l : ℝ) (hq : q * q = q) (hqB : q * B = B)
    (hBq : B * q = B) (hPq : P * q = q * P) :
    q * (B * (1 - P) - l • (1 - P)) * q = B - B * P - l • (q - q * P) := by
  have h := cuc_conj_sub l hq hqB hBq hPq
  have e : B * (1 - P) - l • (1 - P) = (B - l • 1) + (l • P - B * P) := by
    rw [mul_sub, mul_one, smul_sub]
    abel
  rw [e, mul_add, add_mul, h, mul_sub, sub_mul, hqB, hBq, mul_smul_comm, mul_one, smul_mul_assoc,
    hq, smul_sub]
  abel

/-! ### One step of the construction

For a projection `q` and `X ⪰ 0`, with `B = q X q` and `P = 1_S (B)`. -/

section Step

variable {q X : Matrix n n ℝ}

omit [DecidableEq n] in
private theorem cuc_mul_conj (hq : q * q = q) : q * (q * X * q) = q * X * q := by
  rw [← mul_assoc, ← mul_assoc, hq]

omit [DecidableEq n] in
private theorem cuc_conj_mul (hq : q * q = q) : q * X * q * q = q * X * q := by
  rw [mul_assoc, hq]

/-- `q` commutes with `B = q X q`, hence with `P = 1_S (B)`. -/
private theorem cuc_commute_q (hq : q * q = q) (S : Set ℝ) :
    Commute (spectralProj (q * X * q) S) q :=
  Commute.cfc_real ((cuc_conj_mul hq).trans (cuc_mul_conj hq).symm) _

private theorem cuc_step_mul_q (hq : q * q = q) (S : Set ℝ) :
    q * spectralProj (q * X * q) S * q = q * spectralProj (q * X * q) S := by
  rw [mul_assoc, (cuc_commute_q hq S).eq, ← mul_assoc, hq]

private theorem cuc_step_mul_self (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef) (S : Set ℝ) :
    q * spectralProj (q * X * q) S * (q * spectralProj (q * X * q) S) =
      q * spectralProj (q * X * q) S := by
  have hP := spectralProj_mul_self (cuc_posSemidef_conj hqt hX).isHermitian S
  rw [← mul_assoc, cuc_step_mul_q hq S, mul_assoc, hP]

private theorem cuc_step_transpose (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef)
    (S : Set ℝ) : (q * spectralProj (q * X * q) S)ᵀ = q * spectralProj (q * X * q) S := by
  rw [Matrix.transpose_mul, spectralProj_transpose (cuc_posSemidef_conj hqt hX).isHermitian, hqt,
    (cuc_commute_q hq S).eq]

private theorem cuc_step_commute (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef) (S : Set ℝ) :
    Commute (q * spectralProj (q * X * q) S) (q * X * q) := by
  have hBP := (commute_spectralProj (cuc_posSemidef_conj hqt hX).isHermitian S).eq
  change q * spectralProj (q * X * q) S * (q * X * q) =
    q * X * q * (q * spectralProj (q * X * q) S)
  rw [mul_assoc, ← hBP, ← mul_assoc, cuc_mul_conj hq, ← mul_assoc, cuc_conj_mul hq]

/-- `(q P) X (q P) = B P`. -/
private theorem cuc_step_conj_eq (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef) (S : Set ℝ) :
    q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) =
      q * X * q * spectralProj (q * X * q) S := by
  have hB := cuc_posSemidef_conj hqt hX
  have hPq := (cuc_commute_q hq (X := X) S).eq
  have hBP := (commute_spectralProj hB.isHermitian S).eq
  have hPP := spectralProj_mul_self hB.isHermitian S
  calc q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S)
      = spectralProj (q * X * q) S * q * X * (q * spectralProj (q * X * q) S) := by rw [hPq]
    _ = spectralProj (q * X * q) S * (q * X * q) * spectralProj (q * X * q) S := by
        simp only [mul_assoc]
    _ = q * X * q * spectralProj (q * X * q) S * spectralProj (q * X * q) S := by rw [← hBP]
    _ = q * X * q * spectralProj (q * X * q) S := by rw [mul_assoc, hPP]

/-- Randrianantoanina, Proposition 2.4 (iii): `(q P) X (q P) ⪯ λ q P` for
`P = 1_{[0, λ]} (q X q)`. -/
private theorem cuc_step_le (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef) (l : ℝ) :
    (l • (q * spectralProj (q * X * q) (Set.Icc 0 l)) -
      q * spectralProj (q * X * q) (Set.Icc 0 l) * X *
        (q * spectralProj (q * X * q) (Set.Icc 0 l))).PosSemidef := by
  have hB := cuc_posSemidef_conj hqt hX
  have hPq := (cuc_commute_q hq (X := X) (Set.Icc 0 l)).eq
  have hcfc : cfc (fun t => l * (Set.Icc 0 l).indicator 1 t - t * (Set.Icc 0 l).indicator 1 t)
      (q * X * q) = l • spectralProj (q * X * q) (Set.Icc 0 l) -
        q * X * q * spectralProj (q * X * q) (Set.Icc 0 l) := by
    rw [cfc_sub (fun t => l * (Set.Icc 0 l).indicator 1 t)
        (fun t => t * (Set.Icc 0 l).indicator 1 t) (q * X * q) (cuc_cont _ _) (cuc_cont _ _),
      cfc_const_mul l ((Set.Icc 0 l).indicator 1) (q * X * q) (cuc_cont _ _),
      cfc_mul (fun t => t) ((Set.Icc 0 l).indicator 1) (q * X * q) (cuc_cont _ _) (cuc_cont _ _),
      cfc_id' ℝ (q * X * q) hB.isHermitian.isSelfAdjoint]
    rfl
  have hg : ∀ t ∈ spectrum ℝ (q * X * q),
      0 ≤ l * (Set.Icc 0 l).indicator 1 t - t * (Set.Icc 0 l).indicator 1 t := by
    intro t _
    by_cases ht : t ∈ Set.Icc 0 l
    · rw [Set.indicator_of_mem ht]
      simp only [Pi.one_apply, mul_one]
      linarith [ht.2]
    · rw [Set.indicator_of_notMem ht]
      simp
  have hC := cuc_posSemidef_conj hqt (cuc_posSemidef_cfc hg)
  rw [hcfc, cuc_conj_sub l hq (cuc_mul_conj hq) (cuc_conj_mul hq) hPq] at hC
  rwa [cuc_step_conj_eq hq hqt hX]

/-- Randrianantoanina, Proposition 2.4 (iv), one step: `λ tr (q − q P) ≤ tr ((q − q P) X)` for
`P = 1_{[0, λ]} (q X q)`, since `q − q P = q 1_{(λ, ∞)} (q X q)` and
`(q − q P) (q X q) (q − q P) ⪰ λ (q − q P)`. -/
private theorem cuc_step_trace (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef) (l : ℝ) :
    l * (q - q * spectralProj (q * X * q) (Set.Icc 0 l)).trace ≤
      ((q - q * spectralProj (q * X * q) (Set.Icc 0 l)) * X).trace := by
  have hB := cuc_posSemidef_conj hqt hX
  have hPq := (cuc_commute_q hq (X := X) (Set.Icc 0 l)).eq
  have h1 : cfc (fun t => 1 - (Set.Icc 0 l).indicator 1 t) (q * X * q) =
      1 - spectralProj (q * X * q) (Set.Icc 0 l) := by
    rw [cfc_sub (fun _ => (1 : ℝ)) ((Set.Icc 0 l).indicator 1) (q * X * q) (cuc_cont _ _)
        (cuc_cont _ _), cfc_const (1 : ℝ) (q * X * q) hB.isHermitian.isSelfAdjoint, map_one]
    rfl
  have hcfc : cfc (fun t => t * (1 - (Set.Icc 0 l).indicator 1 t) -
      l * (1 - (Set.Icc 0 l).indicator 1 t)) (q * X * q) =
        q * X * q * (1 - spectralProj (q * X * q) (Set.Icc 0 l)) -
          l • (1 - spectralProj (q * X * q) (Set.Icc 0 l)) := by
    rw [cfc_sub (fun t => t * (1 - (Set.Icc 0 l).indicator 1 t))
        (fun t => l * (1 - (Set.Icc 0 l).indicator 1 t)) (q * X * q) (cuc_cont _ _) (cuc_cont _ _),
      cfc_mul (fun t => t) (fun t => 1 - (Set.Icc 0 l).indicator 1 t) (q * X * q) (cuc_cont _ _)
        (cuc_cont _ _),
      cfc_const_mul l (fun t => 1 - (Set.Icc 0 l).indicator 1 t) (q * X * q) (cuc_cont _ _),
      cfc_id' ℝ (q * X * q) hB.isHermitian.isSelfAdjoint, h1]
  have hg : ∀ t ∈ spectrum ℝ (q * X * q),
      0 ≤ t * (1 - (Set.Icc 0 l).indicator 1 t) - l * (1 - (Set.Icc 0 l).indicator 1 t) := by
    intro t ht
    have ht0 := cuc_spectrum_nonneg hB ht
    by_cases hS : t ∈ Set.Icc 0 l
    · rw [Set.indicator_of_mem hS]
      simp
    · rw [Set.indicator_of_notMem hS]
      have hlt : l < t := by
        simp only [Set.mem_Icc, not_and, not_le] at hS
        exact hS ht0
      simp only [sub_zero, mul_one]
      linarith
  have hC := cuc_posSemidef_conj hqt (cuc_posSemidef_cfc hg)
  rw [hcfc, cuc_conj_sub' l hq (cuc_mul_conj hq) (cuc_conj_mul hq) hPq] at hC
  have htr := hC.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at htr
  have e : (q * X * q * spectralProj (q * X * q) (Set.Icc 0 l)).trace =
      (q * spectralProj (q * X * q) (Set.Icc 0 l) * X).trace := by
    rw [mul_assoc (q * X) q, Matrix.trace_mul_comm (q * X), ← mul_assoc, cuc_step_mul_q hq]
  rw [sub_mul, Matrix.trace_sub (q * X), ← cuc_trace_mul_eq hq (X := X)]
  linarith

/-- Randrianantoanina, Lemma 3.3, one step: `(q P) X (q P) = (q P) (q X q) (q P) ⪯ q X q`. -/
private theorem cuc_step_conj_le (hq : q * q = q) (hqt : qᵀ = q) (hX : X.PosSemidef)
    (S : Set ℝ) :
    (q * X * q -
      q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S)).PosSemidef := by
  have h := posSemidef_sub_mul_mul_of_commute (cuc_posSemidef_conj hqt hX)
    (cuc_step_mul_self hq hqt hX S) (cuc_step_transpose hq hqt hX S) (cuc_step_commute hq hqt hX S)
  have e : q * spectralProj (q * X * q) S * (q * X * q) * (q * spectralProj (q * X * q) S) =
      q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) := by
    calc q * spectralProj (q * X * q) S * (q * X * q) * (q * spectralProj (q * X * q) S)
        = q * spectralProj (q * X * q) S * q * X * (q * (q * spectralProj (q * X * q) S)) := by
          simp only [mul_assoc]
      _ = q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) := by
          rw [cuc_step_mul_q hq S, ← mul_assoc q q, hq]
  rwa [e] at h

end Step

end BanachProbability
