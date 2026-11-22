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
`ℱ_k`-measurable, the Cuculescu projection at time `k`. They satisfy (Proposition 2.4):

1. `q_k` is an orthogonal projection and `q_{k+1} ≤ q_k` (`cuculescu_isProj`,
   `cuculescu_succ_mul`), and `q_{k+1}` is `ℱ_k`-measurable (`measurable_cuculescu_succ`);
2. `q_{k+1}` commutes with `q_k x_k q_k` (`commute_cuculescu_succ`);
3. `q_{k+1} x_k q_{k+1} ≤ λ q_{k+1}` (`cuculescu_mul_mul_le`);
4. `λ τ (1 − q_{N+1}) ≤ τ (x)` (`cuculescu_trace_le`), by the source's telescoping argument
   `τ (x) = τ (q_{N+1} x) + Σ_{k ≤ N} τ ((q_k − q_{k+1}) E_k x)`, with the trace pull-out
   `τ (a E_k x) = τ (a x)` for the `ℱ_k`-measurable bounded `a = q_k − q_{k+1}`.

The first three hold at every `ω` and for every sequence `X` in place of the martingale (the
spectral projections of a matrix are orthogonal projections, and they vanish when the matrix is
not symmetric); the fourth uses `x_k ⪰ 0` (almost everywhere).

The compressed process `z_k = q_{k+1} x_k q_{k+1}` (`compressed`; the source's `q_k x_k q_k`) is a
supermartingale, `E_k z_{k+1} ⪯ z_k` almost everywhere (`matrixCondExp_compressed_le`;
Randrianantoanina, Lemma 3.3), since `q_{k+2}` commutes with `q_{k+1} x_{k+1} q_{k+1}`, `p A p ≤ A`
for a projection `p` commuting with `A ≥ 0`, `E_k` is positive, and
`E_k (q_{k+1} x_{k+1} q_{k+1}) = q_{k+1} E_k (x_{k+1}) q_{k+1} = q_{k+1} x_k q_{k+1}` (bimodule
property and tower property). Its Doob decomposition `z_k = y_k + z'_k` (Randrianantoanina,
(3.3)–(3.6)) has the martingale part `y_k = z_0 + Σ_{j<k} (z_{j+1} − E_j z_{j+1})`
(`compressedMart`, a martingale: `matrixCondExp_compressedMart`), with `y_k ≥ z_k`
(`posSemidef_compressedMart_sub`) and `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)`
(`matrixTrace_compressedMart_sq_le`, Randrianantoanina, Lemma 3.4: a telescoping sum, using
`0 ⪯ z_k ⪯ λ` and the supermartingale property).
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

For a projection `q` and a matrix `X`, with `B = q X q` and `P = 1_S (B)`. -/

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

private theorem cuc_step_mul_self (hq : q * q = q) (S : Set ℝ) :
    q * spectralProj (q * X * q) S * (q * spectralProj (q * X * q) S) =
      q * spectralProj (q * X * q) S := by
  have hP := spectralProj_mul_self (q * X * q) S
  rw [← mul_assoc, cuc_step_mul_q hq S, mul_assoc, hP]

private theorem cuc_step_transpose (hq : q * q = q) (hqt : qᵀ = q) (S : Set ℝ) :
    (q * spectralProj (q * X * q) S)ᵀ = q * spectralProj (q * X * q) S := by
  rw [Matrix.transpose_mul, spectralProj_transpose (q * X * q), hqt,
    (cuc_commute_q hq S).eq]

private theorem cuc_step_commute (hq : q * q = q) (S : Set ℝ) :
    Commute (q * spectralProj (q * X * q) S) (q * X * q) := by
  have hBP := (commute_spectralProj (q * X * q) S).eq
  change q * spectralProj (q * X * q) S * (q * X * q) =
    q * X * q * (q * spectralProj (q * X * q) S)
  rw [mul_assoc, ← hBP, ← mul_assoc, cuc_mul_conj hq, ← mul_assoc, cuc_conj_mul hq]

/-- `(q P) X (q P) = B P`. -/
private theorem cuc_step_conj_eq (hq : q * q = q) (S : Set ℝ) :
    q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) =
      q * X * q * spectralProj (q * X * q) S := by
  have hPq := (cuc_commute_q hq (X := X) S).eq
  have hBP := (commute_spectralProj (q * X * q) S).eq
  have hPP := spectralProj_mul_self (q * X * q) S
  calc q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S)
      = spectralProj (q * X * q) S * q * X * (q * spectralProj (q * X * q) S) := by rw [hPq]
    _ = spectralProj (q * X * q) S * (q * X * q) * spectralProj (q * X * q) S := by
        simp only [mul_assoc]
    _ = q * X * q * spectralProj (q * X * q) S * spectralProj (q * X * q) S := by rw [← hBP]
    _ = q * X * q * spectralProj (q * X * q) S := by rw [mul_assoc, hPP]

/-- Randrianantoanina, Proposition 2.4 (iii): `(q P) X (q P) ⪯ λ q P` for
`P = 1_{[0, λ]} (q X q)`: `(q P) X (q P) = B P` and `λ P − B P = g (B)` with
`g (t) = (λ − t) 1_{[0, λ]} (t) ≥ 0`. (When `B` is not symmetric, `P = 0`.) -/
private theorem cuc_step_le (hq : q * q = q) (hqt : qᵀ = q) (l : ℝ) :
    (l • (q * spectralProj (q * X * q) (Set.Icc 0 l)) -
      q * spectralProj (q * X * q) (Set.Icc 0 l) * X *
        (q * spectralProj (q * X * q) (Set.Icc 0 l))).PosSemidef := by
  by_cases hB : (q * X * q).IsHermitian
  · have hPq := (cuc_commute_q hq (X := X) (Set.Icc 0 l)).eq
    have hcfc : cfc (fun t => l * (Set.Icc 0 l).indicator 1 t - t * (Set.Icc 0 l).indicator 1 t)
        (q * X * q) = l • spectralProj (q * X * q) (Set.Icc 0 l) -
          q * X * q * spectralProj (q * X * q) (Set.Icc 0 l) := by
      rw [cfc_sub (fun t => l * (Set.Icc 0 l).indicator 1 t)
          (fun t => t * (Set.Icc 0 l).indicator 1 t) (q * X * q) (continuousOn_spectrum _ _)
          (continuousOn_spectrum _ _),
        cfc_const_mul l ((Set.Icc 0 l).indicator 1) (q * X * q) (continuousOn_spectrum _ _),
        cfc_mul (fun t => t) ((Set.Icc 0 l).indicator 1) (q * X * q) (continuousOn_spectrum _ _)
          (continuousOn_spectrum _ _),
        cfc_id' ℝ (q * X * q) hB.isSelfAdjoint]
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
    have hC := cuc_posSemidef_conj hqt (posSemidef_cfc hg)
    rw [hcfc, cuc_conj_sub l hq (cuc_mul_conj hq) (cuc_conj_mul hq) hPq] at hC
    rwa [cuc_step_conj_eq hq]
  · have h0 : spectralProj (q * X * q) (Set.Icc 0 l) = 0 := by
      rw [spectralProj, cfc_apply_of_not_predicate _ (show ¬ IsSelfAdjoint (q * X * q) from hB)]
    simp only [h0, mul_zero, zero_mul, smul_zero, sub_zero]
    exact Matrix.PosSemidef.zero

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
    rw [cfc_sub (fun _ => (1 : ℝ)) ((Set.Icc 0 l).indicator 1) (q * X * q)
        (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
      cfc_const (1 : ℝ) (q * X * q) hB.isHermitian.isSelfAdjoint, map_one]
    rfl
  have hcfc : cfc (fun t => t * (1 - (Set.Icc 0 l).indicator 1 t) -
      l * (1 - (Set.Icc 0 l).indicator 1 t)) (q * X * q) =
        q * X * q * (1 - spectralProj (q * X * q) (Set.Icc 0 l)) -
          l • (1 - spectralProj (q * X * q) (Set.Icc 0 l)) := by
    rw [cfc_sub (fun t => t * (1 - (Set.Icc 0 l).indicator 1 t))
        (fun t => l * (1 - (Set.Icc 0 l).indicator 1 t)) (q * X * q) (continuousOn_spectrum _ _)
        (continuousOn_spectrum _ _),
      cfc_mul (fun t => t) (fun t => 1 - (Set.Icc 0 l).indicator 1 t) (q * X * q)
        (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
      cfc_const_mul l (fun t => 1 - (Set.Icc 0 l).indicator 1 t) (q * X * q)
        (continuousOn_spectrum _ _),
      cfc_id' ℝ (q * X * q) hB.isHermitian.isSelfAdjoint, h1]
  have hg : ∀ t ∈ spectrum ℝ (q * X * q),
      0 ≤ t * (1 - (Set.Icc 0 l).indicator 1 t) - l * (1 - (Set.Icc 0 l).indicator 1 t) := by
    intro t ht
    have ht0 := spectrum_nonneg_of_posSemidef hB ht
    by_cases hS : t ∈ Set.Icc 0 l
    · rw [Set.indicator_of_mem hS]
      simp
    · rw [Set.indicator_of_notMem hS]
      have hlt : l < t := by
        simp only [Set.mem_Icc, not_and, not_le] at hS
        exact hS ht0
      simp only [sub_zero, mul_one]
      linarith
  have hC := cuc_posSemidef_conj hqt (posSemidef_cfc hg)
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
    (cuc_step_mul_self hq S) (cuc_step_transpose hq hqt S) (cuc_step_commute hq S)
  have e : q * spectralProj (q * X * q) S * (q * X * q) * (q * spectralProj (q * X * q) S) =
      q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) := by
    calc q * spectralProj (q * X * q) S * (q * X * q) * (q * spectralProj (q * X * q) S)
        = q * spectralProj (q * X * q) S * q * X * (q * (q * spectralProj (q * X * q) S)) := by
          simp only [mul_assoc]
      _ = q * spectralProj (q * X * q) S * X * (q * spectralProj (q * X * q) S) := by
          rw [cuc_step_mul_q hq S, ← mul_assoc q q, hq]
  rwa [e] at h

end Step

/-! ### Cuculescu's projections, pointwise

Proposition 2.4 (i)–(iii) hold at every `ω`, for every sequence `X`. -/

section Pointwise

variable (X : ℕ → Ω → Matrix n n ℝ) (l : ℝ)

theorem cuculescu_zero (ω : Ω) : cuculescu X l 0 ω = 1 :=
  rfl

theorem cuculescu_succ (k : ℕ) (ω : Ω) :
    cuculescu X l (k + 1) ω = cuculescu X l k ω *
      spectralProj (cuculescu X l k ω * X k ω * cuculescu X l k ω) (Set.Icc 0 l) :=
  rfl

/-- Randrianantoanina, Proposition 2.4: `q_k` is an orthogonal projection. -/
theorem cuculescu_isProj (k : ℕ) (ω : Ω) :
    cuculescu X l k ω * cuculescu X l k ω = cuculescu X l k ω ∧
      (cuculescu X l k ω)ᵀ = cuculescu X l k ω := by
  induction k with
  | zero =>
    rw [cuculescu_zero]
    exact ⟨mul_one 1, Matrix.transpose_one⟩
  | succ k ih =>
    rw [cuculescu_succ]
    exact ⟨cuc_step_mul_self ih.1 _, cuc_step_transpose ih.1 ih.2 _⟩

/-- Randrianantoanina, Proposition 2.4 (iv): the projections decrease, `q_{k+1} q_k = q_{k+1}`. -/
theorem cuculescu_succ_mul (k : ℕ) (ω : Ω) :
    cuculescu X l (k + 1) ω * cuculescu X l k ω = cuculescu X l (k + 1) ω := by
  rw [cuculescu_succ]
  exact cuc_step_mul_q (cuculescu_isProj X l k ω).1 _

/-- The projections decrease: `q_k q_j = q_k` for `j ≤ k`. -/
theorem cuculescu_mul_of_le {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    cuculescu X l k ω * cuculescu X l j ω = cuculescu X l k ω := by
  induction k, hjk using Nat.le_induction with
  | base => exact (cuculescu_isProj X l j ω).1
  | succ k _ ih =>
    calc cuculescu X l (k + 1) ω * cuculescu X l j ω
        = cuculescu X l (k + 1) ω * cuculescu X l k ω * cuculescu X l j ω := by
          rw [cuculescu_succ_mul]
      _ = cuculescu X l (k + 1) ω := by rw [mul_assoc, ih, cuculescu_succ_mul]

/-- The projections decrease: `q_j q_k = q_k` for `j ≤ k` (the transpose of
`cuculescu_mul_of_le`). -/
theorem mul_cuculescu_of_le {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    cuculescu X l j ω * cuculescu X l k ω = cuculescu X l k ω := by
  have h := congrArg Matrix.transpose (cuculescu_mul_of_le X l hjk ω)
  rwa [Matrix.transpose_mul, (cuculescu_isProj X l k ω).2, (cuculescu_isProj X l j ω).2] at h

/-- Randrianantoanina, Proposition 2.4 (ii): `q_{k+1}` commutes with `q_k X_k q_k`. -/
theorem commute_cuculescu_succ (k : ℕ) (ω : Ω) :
    Commute (cuculescu X l (k + 1) ω) (cuculescu X l k ω * X k ω * cuculescu X l k ω) := by
  rw [cuculescu_succ]
  exact cuc_step_commute (cuculescu_isProj X l k ω).1 _

/-- Randrianantoanina, Proposition 2.4 (iii): `q_{k+1} X_k q_{k+1} ≤ λ q_{k+1}`. -/
theorem cuculescu_mul_mul_le (k : ℕ) (ω : Ω) :
    (l • cuculescu X l (k + 1) ω -
      cuculescu X l (k + 1) ω * X k ω * cuculescu X l (k + 1) ω).PosSemidef := by
  rw [cuculescu_succ]
  exact cuc_step_le (cuculescu_isProj X l k ω).1 (cuculescu_isProj X l k ω).2 l

/-- `∑_{k ≤ N} (q_k − q_{k+1}) = 1 − q_{N+1}`. -/
private theorem cuc_sum_range_sub (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range (N + 1), (cuculescu X l k ω - cuculescu X l (k + 1) ω) =
      1 - cuculescu X l (N + 1) ω :=
  Finset.sum_range_sub' (fun k => cuculescu X l k ω) (N + 1)

end Pointwise

/-! ### Measurability and boundedness -/

section Measurable

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → Matrix n n ℝ}

/-- Randrianantoanina, Proposition 2.4 (i): `q_{k+1}` is `ℱ_k`-measurable when `X` is adapted. -/
theorem measurable_cuculescu_succ (hX : ∀ k, Measurable[ℱ k] (X k)) (l : ℝ) (k : ℕ) :
    Measurable[ℱ k] (cuculescu X l (k + 1)) := by
  induction k with
  | zero =>
    have h0 : Measurable[ℱ 0] (cuculescu X l 0) := measurable_const
    exact h0.mul ((measurable_spectralProj_Icc 0 l).comp ((h0.mul (hX 0)).mul h0))
  | succ k ih =>
    have h1 : Measurable[ℱ (k + 1)] (cuculescu X l (k + 1)) :=
      ih.mono (ℱ.mono k.le_succ) le_rfl
    exact h1.mul ((measurable_spectralProj_Icc 0 l).comp ((h1.mul (hX (k + 1))).mul h1))

/-- `q_k` is `ℱ_k`-measurable when `X` is adapted. -/
theorem measurable_cuculescu (hX : ∀ k, Measurable[ℱ k] (X k)) (l : ℝ) (k : ℕ) :
    Measurable[ℱ k] (cuculescu X l k) := by
  cases k with
  | zero => exact measurable_const
  | succ k => exact (measurable_cuculescu_succ hX l k).mono (ℱ.mono k.le_succ) le_rfl

/-- `q_k` is bounded: its entries lie in `[−1, 1]`. -/
theorem matrixMemLp_cuculescu (hX : ∀ k, Measurable[ℱ k] (X k)) (l : ℝ) (k : ℕ) :
    MatrixMemLp (cuculescu X l k) ∞ μ :=
  MatrixMemLp.of_bound ((measurable_cuculescu hX l k).mono (ℱ.le k) le_rfl) 1
    (ae_of_all _ fun ω i j =>
      abs_apply_le_one_of_isProj (cuculescu_isProj X l k ω).1 (cuculescu_isProj X l k ω).2 i j)

end Measurable

/-! ### Integration helpers -/

omit [DecidableEq n] in
private theorem cuc_integrable_trace {f : Ω → Matrix n n ℝ} (hf : MatrixMemLp f 1 μ) :
    Integrable (fun ω => (f ω).trace) μ := by
  simp only [Matrix.trace, Matrix.diag]
  exact integrable_finsetSum _ fun i _ => memLp_one_iff_integrable.1 (hf i i)

omit [DecidableEq n] in
/-- `ω ↦ tr (f ω g ω)` is integrable for bounded `f`, `g`. -/
private theorem cuc_integrable_trace_mul [IsFiniteMeasure μ] {f g : Ω → Matrix n n ℝ}
    (hf : MatrixMemLp f ∞ μ) (hg : MatrixMemLp g ∞ μ) :
    Integrable (fun ω => (f ω * g ω).trace) μ := by
  classical
  exact cuc_integrable_trace ((hf.mul hg).mono_exponent le_top)

omit [Fintype n] [DecidableEq n] in
/-- Integrating a pointwise linear inequality between integrable functions. -/
private theorem cuc_integral_le {f₀ f₁ f₂ f₃ f₄ : Ω → ℝ} (h₀ : Integrable f₀ μ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (a₁ a₂ a₃ a₄ : ℝ) (h : ∀ᵐ ω ∂μ, f₀ ω ≤ a₁ * f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω) :
    ∫ ω, f₀ ω ∂μ ≤
      a₁ * ∫ ω, f₁ ω ∂μ + a₂ * ∫ ω, f₂ ω ∂μ + a₃ * ∫ ω, f₃ ω ∂μ + a₄ * ∫ ω, f₄ ω ∂μ := by
  have h' := integral_mono_ae h₀ (by fun_prop) h
  rw [integral_add (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop),
    integral_add (by fun_prop) (by fun_prop), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul] at h'
  exact h'

omit [Fintype n] [DecidableEq n] in
private theorem cuc_integral_add₃ {f g h : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (a : ℝ) :
    ∫ ω, (f ω + a * g ω + h ω) ∂μ = ∫ ω, f ω ∂μ + a * ∫ ω, g ω ∂μ + ∫ ω, h ω ∂μ := by
  rw [integral_add (by fun_prop) hh, integral_add hf (by fun_prop), integral_const_mul]

/-! ### Proposition 2.4 (iv) -/

section Trace

variable {ℱ : Filtration ℕ mΩ} {x : Ω → Matrix n n ℝ}

/-- **Randrianantoanina, Proposition 2.4 (iv)**: `λ τ (1 − q_{N+1}) ≤ τ (x)` for the Cuculescu
projections of the martingale `x_k = E_k x` of a positive semidefinite `x ∈ L¹`. As in the source,
`τ (x) = τ (q_{N+1} x) + Σ_{k ≤ N} τ ((q_k − q_{k+1}) x)`, `τ (q_{N+1} x) ≥ 0`, and
`τ ((q_k − q_{k+1}) x) = τ ((q_k − q_{k+1}) x_k) ≥ λ τ (q_k − q_{k+1})` (trace pull-out for the
`ℱ_k`-measurable `q_k − q_{k+1}`, then the one-step estimate). -/
theorem cuculescu_trace_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (l : ℝ) (N : ℕ) :
    l * matrixTrace μ (fun ω => 1 - cuculescu (fun k => matrixCondExp (ℱ k) μ x) l (N + 1) ω) ≤
      matrixTrace μ x := by
  have hXm : ∀ k, Measurable[ℱ k] (matrixCondExp (ℱ k) μ x) := fun k => measurable_matrixCondExp x
  have hXp : ∀ᵐ ω ∂μ, ∀ k, (matrixCondExp (ℱ k) μ x ω).PosSemidef :=
    ae_all_iff.2 fun k => posSemidef_matrixCondExp hx hxi
  set q := cuculescu (fun k => matrixCondExp (ℱ k) μ x) l with hq_def
  have hqi : ∀ k, MatrixMemLp (q k) ∞ μ := matrixMemLp_cuculescu hXm l
  have hd : ∀ k, MatrixMemLp (fun ω => q k ω - q (k + 1) ω) ∞ μ :=
    fun k => (hqi k).sub (hqi (k + 1))
  have hd1 : ∀ k, MatrixMemLp (fun ω => q k ω - q (k + 1) ω) 1 μ :=
    fun k => (hd k).mono_exponent le_top
  -- `1 − q_{N+1} = Σ_{k ≤ N} (q_k − q_{k+1})`
  have hsum1 : matrixTrace μ (fun ω => 1 - q (N + 1) ω) =
      ∑ k ∈ Finset.range (N + 1), matrixTrace μ (fun ω => q k ω - q (k + 1) ω) := by
    rw [← matrixTrace_sum _ fun k _ => hd1 k]
    congr 1
    funext ω
    rw [Finset.sum_apply]
    exact (cuc_sum_range_sub _ l N ω).symm
  -- `τ (x) = τ (q_{N+1} x) + Σ_{k ≤ N} τ ((q_k − q_{k+1}) x)`
  have hsum2 : ∑ k ∈ Finset.range (N + 1),
      matrixTrace μ (fun ω => (q k ω - q (k + 1) ω) * x ω) =
      matrixTrace μ x - matrixTrace μ (fun ω => q (N + 1) ω * x ω) := by
    rw [← matrixTrace_sum _ fun k _ => (hd k).mul (r := 1) hxi,
      ← matrixTrace_sub hxi ((hqi (N + 1)).mul (r := 1) hxi)]
    congr 1
    funext ω
    rw [Finset.sum_apply]
    simp only [← Finset.sum_mul]
    rw [cuc_sum_range_sub, sub_mul, one_mul]
    rfl
  -- `τ ((q_k − q_{k+1}) x) = τ ((q_k − q_{k+1}) x_k) ≥ λ τ (q_k − q_{k+1})`
  have hstep : ∀ k, l * matrixTrace μ (fun ω => q k ω - q (k + 1) ω) ≤
      matrixTrace μ (fun ω => (q k ω - q (k + 1) ω) * x ω) := by
    intro k
    have hm : Measurable[ℱ k] (fun ω => q k ω - q (k + 1) ω) :=
      (measurable_cuculescu hXm l k).sub (measurable_cuculescu_succ hXm l k)
    rw [← matrixTrace_mul_matrixCondExp (ℱ.le k) (p := ∞) (q := 1) hm (hd k) hxi,
      ← matrixTrace_smul]
    refine matrixTrace_mono ((hd1 k).const_smul l)
      ((hd k).mul (r := 1) (hxi.matrixCondExp le_rfl)) ?_
    filter_upwards [hXp] with ω hω
    simp only [Pi.smul_apply, Matrix.trace_smul, smul_eq_mul]
    exact cuc_step_trace (cuculescu_isProj _ l k ω).1 (cuculescu_isProj _ l k ω).2 (hω k) l
  -- `τ (q_{N+1} x) = τ (q_{N+1} x q_{N+1}) ≥ 0`
  have hnonneg : 0 ≤ matrixTrace μ (fun ω => q (N + 1) ω * x ω) := by
    have e : matrixTrace μ (fun ω => q (N + 1) ω * x ω) =
        matrixTrace μ (fun ω => q (N + 1) ω * x ω * q (N + 1) ω) := by
      unfold matrixTrace
      congr 1
      funext ω
      exact (cuc_trace_mul_eq (cuculescu_isProj _ l (N + 1) ω).1).symm
    rw [e]
    exact matrixTrace_nonneg
      (hx.mono fun ω hω => cuc_posSemidef_conj (cuculescu_isProj _ l (N + 1) ω).2 hω)
  calc l * matrixTrace μ (fun ω => 1 - q (N + 1) ω)
      = ∑ k ∈ Finset.range (N + 1), l * matrixTrace μ (fun ω => q k ω - q (k + 1) ω) := by
        rw [hsum1, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (N + 1), matrixTrace μ (fun ω => (q k ω - q (k + 1) ω) * x ω) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = matrixTrace μ x - matrixTrace μ (fun ω => q (N + 1) ω * x ω) := hsum2
    _ ≤ matrixTrace μ x := by linarith

end Trace

/-! ### The compressed process -/

/-- The compressed process `z_k = q_{k+1} x_k q_{k+1}` (Randrianantoanina's `q_k x_k q_k`), for the
martingale `x_k = E_k x` and its Cuculescu projections `q` at level `λ`. -/
noncomputable def compressed (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) (x : Ω → Matrix n n ℝ)
    (l : ℝ) (k : ℕ) : Ω → Matrix n n ℝ :=
  fun ω => cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω * matrixCondExp (ℱ k) μ x ω *
    cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω

/-- The martingale part of the Doob decomposition of the compressed process,
`y_k = z_0 + Σ_{j<k} (z_{j+1} − E_j z_{j+1})`, equivalently
`y_k = z_k + Σ_{j<k} (z_j − E_j z_{j+1})` (Randrianantoanina, (3.3)). -/
noncomputable def compressedMart (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) (x : Ω → Matrix n n ℝ)
    (l : ℝ) (k : ℕ) : Ω → Matrix n n ℝ :=
  compressed ℱ μ x l 0 + ∑ j ∈ Finset.range k,
    (compressed ℱ μ x l (j + 1) - matrixCondExp (ℱ j) μ (compressed ℱ μ x l (j + 1)))

section Compressed

variable {ℱ : Filtration ℕ mΩ} {x : Ω → Matrix n n ℝ} {l : ℝ}

/-- `z_k` is `ℱ_k`-measurable. -/
theorem measurable_compressed (k : ℕ) : Measurable[ℱ k] (compressed ℱ μ x l k) :=
  ((measurable_cuculescu_succ (fun _ => measurable_matrixCondExp x) l k).mul
    (measurable_matrixCondExp x)).mul
    (measurable_cuculescu_succ (fun _ => measurable_matrixCondExp x) l k)

/-- `z_k ⪰ 0`. -/
theorem posSemidef_compressed (hxi : MatrixMemLp x 1 μ) (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef)
    (k : ℕ) : ∀ᵐ ω ∂μ, (compressed ℱ μ x l k ω).PosSemidef :=
  (posSemidef_matrixCondExp hx hxi).mono fun ω hω =>
    cuc_posSemidef_conj (cuculescu_isProj _ l (k + 1) ω).2 hω

/-- `z_k ⪯ λ`: `z_k ⪯ λ q_{k+1} ⪯ λ` (Proposition 2.4 (iii)), at every `ω`. -/
theorem posSemidef_smul_one_sub_compressed (hl : 0 ≤ l) (k : ℕ) (ω : Ω) :
    (l • (1 : Matrix n n ℝ) - compressed ℱ μ x l k ω).PosSemidef := by
  have hq := cuculescu_isProj (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω
  have h1 := cuculescu_mul_mul_le (fun j => matrixCondExp (ℱ j) μ x) l k ω
  have h2 := (cuc_posSemidef_one_sub hq.1 hq.2).smul hl
  have e : l • (1 : Matrix n n ℝ) - compressed ℱ μ x l k ω =
      (l • cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω - compressed ℱ μ x l k ω) +
        l • (1 - cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω) := by
    rw [smul_sub]
    abel
  rw [e]
  exact h1.add h2

/-- `z_k ∈ L¹`, by Hölder's inequality. -/
theorem matrixMemLp_compressed_one [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ) (k : ℕ) :
    MatrixMemLp (compressed ℱ μ x l k) 1 μ :=
  ((matrixMemLp_cuculescu (fun _ => measurable_matrixCondExp x) l (k + 1)).mul (r := 1)
    (hxi.matrixCondExp le_rfl)).mul (r := 1)
    (matrixMemLp_cuculescu (fun _ => measurable_matrixCondExp x) l (k + 1))

/-- `z_k ∈ L^∞`: its entries are bounded by `λ`, as `0 ⪯ z_k ⪯ λ`. -/
theorem matrixMemLp_compressed (hxi : MatrixMemLp x 1 μ) (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef)
    (hl : 0 ≤ l) (k : ℕ) : MatrixMemLp (compressed ℱ μ x l k) ∞ μ :=
  MatrixMemLp.of_bound ((measurable_compressed k).mono (ℱ.le k) le_rfl) l
    ((posSemidef_compressed hxi hx k).mono fun ω hω i j =>
      abs_apply_le_of_posSemidef hω (posSemidef_smul_one_sub_compressed hl k ω) i j)

/-- **Randrianantoanina, Lemma 3.3** (first part): the compressed process is a supermartingale,
`E_k z_{k+1} ⪯ z_k`: `z_{k+1} = q_{k+2} x_{k+1} q_{k+2} ⪯ q_{k+1} x_{k+1} q_{k+1}` since `q_{k+2}`
commutes with `q_{k+1} x_{k+1} q_{k+1}` and `q_{k+2} ≤ q_{k+1}`, and `E_k` is positive with
`E_k (q_{k+1} x_{k+1} q_{k+1}) = q_{k+1} E_k (x_{k+1}) q_{k+1} = q_{k+1} x_k q_{k+1}`. -/
theorem matrixCondExp_compressed_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (k : ℕ) :
    ∀ᵐ ω ∂μ, (compressed ℱ μ x l k ω -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω).PosSemidef := by
  set q := cuculescu (fun j => matrixCondExp (ℱ j) μ x) l with hq_def
  have hqm : Measurable[ℱ k] (q (k + 1)) :=
    measurable_cuculescu_succ (fun _ => measurable_matrixCondExp x) l k
  have hqi : MatrixMemLp (q (k + 1)) ∞ μ :=
    matrixMemLp_cuculescu (fun _ => measurable_matrixCondExp x) l (k + 1)
  have hX1 : MatrixMemLp (matrixCondExp (ℱ (k + 1)) μ x) 1 μ := hxi.matrixCondExp le_rfl
  -- `q_{k+2} x_{k+1} q_{k+2} ⪯ q_{k+1} x_{k+1} q_{k+1}`
  have h1 : ∀ᵐ ω ∂μ,
      ((fun ω => q (k + 1) ω * matrixCondExp (ℱ (k + 1)) μ x ω * q (k + 1) ω) ω -
        compressed ℱ μ x l (k + 1) ω).PosSemidef := by
    filter_upwards [posSemidef_matrixCondExp (m := ℱ (k + 1)) hx hxi] with ω hω
    exact cuc_step_conj_le (cuculescu_isProj _ l (k + 1) ω).1 (cuculescu_isProj _ l (k + 1) ω).2
      hω _
  have h2 := posSemidef_matrixCondExp_sub (m := ℱ k) h1 (matrixMemLp_compressed_one hxi (k + 1))
    ((hqi.mul (r := 1) hX1).mul (r := 1) hqi)
  -- `E_k (q_{k+1} x_{k+1} q_{k+1}) = q_{k+1} E_k (x_{k+1}) q_{k+1} = q_{k+1} x_k q_{k+1}`
  have h3 := matrixCondExp_mul_mul (m := ℱ k) hqm hqm hqi hqi hX1
  have h4 := matrixCondExp_matrixCondExp_of_le (μ := μ) (ℱ.mono k.le_succ) (ℱ.le (k + 1)) x
  filter_upwards [h2, h3, h4] with ω h2 h3 h4
  rw [h3, h4] at h2
  exact h2

/-! ### The Doob decomposition of the compressed process -/

theorem compressedMart_zero : compressedMart ℱ μ x l 0 = compressed ℱ μ x l 0 := by
  simp [compressedMart]

theorem compressedMart_succ (k : ℕ) :
    compressedMart ℱ μ x l (k + 1) = compressedMart ℱ μ x l k +
      (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) := by
  simp only [compressedMart, Finset.sum_range_succ, add_assoc]

/-- `y_k − z_k = Σ_{j<k} (z_j − E_j z_{j+1})` (Randrianantoanina, (3.4), (3.5)). -/
theorem compressedMart_sub_compressed (k : ℕ) :
    compressedMart ℱ μ x l k - compressed ℱ μ x l k = ∑ j ∈ Finset.range k,
      (compressed ℱ μ x l j - matrixCondExp (ℱ j) μ (compressed ℱ μ x l (j + 1))) := by
  induction k with
  | zero => simp [compressedMart_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, compressedMart_succ]
    abel

/-- `y_k` is `ℱ_k`-measurable. -/
theorem measurable_compressedMart (k : ℕ) : Measurable[ℱ k] (compressedMart ℱ μ x l k) := by
  refine ((measurable_compressed 0).mono (ℱ.mono (Nat.zero_le k)) le_rfl).add
    (Finset.sum_induction _ (fun g => Measurable[ℱ k] g) (fun _ _ => Measurable.add)
      (measurable_const : Measurable[ℱ k] fun _ : Ω => (0 : Matrix n n ℝ)) fun j hj => ?_)
  have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
  exact ((measurable_compressed (j + 1)).mono (ℱ.mono hjk) le_rfl).sub
    ((measurable_matrixCondExp _).mono (ℱ.mono (by omega)) le_rfl)

/-- `y_k ∈ L¹`. -/
theorem matrixMemLp_compressedMart_one [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ) (k : ℕ) :
    MatrixMemLp (compressedMart ℱ μ x l k) 1 μ :=
  (matrixMemLp_compressed_one hxi 0).add (MatrixMemLp.sum _ fun j _ =>
    (matrixMemLp_compressed_one hxi (j + 1)).sub
      ((matrixMemLp_compressed_one hxi (j + 1)).matrixCondExp le_rfl))

/-- `y_k ∈ L^∞`. -/
theorem matrixMemLp_compressedMart (hxi : MatrixMemLp x 1 μ) (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef)
    (hl : 0 ≤ l) (k : ℕ) : MatrixMemLp (compressedMart ℱ μ x l k) ∞ μ :=
  (matrixMemLp_compressed hxi hx hl 0).add (MatrixMemLp.sum _ fun j _ =>
    (matrixMemLp_compressed hxi hx hl (j + 1)).sub
      ((matrixMemLp_compressed hxi hx hl (j + 1)).matrixCondExp le_top))

/-- `E_k (z_{k+1} − E_k z_{k+1}) = 0`. -/
private theorem cuc_matrixCondExp_mdiff [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ) (k : ℕ) :
    matrixCondExp (ℱ k) μ
        (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) =ᵐ[μ]
      0 := by
  have hz := matrixMemLp_compressed_one (ℱ := ℱ) (l := l) hxi (k + 1)
  have h := matrixCondExp_sub (m := ℱ k) hz (hz.matrixCondExp (m := ℱ k) le_rfl)
  rwa [matrixCondExp_of_measurable (ℱ.le k) (measurable_matrixCondExp _)
    (hz.matrixCondExp le_rfl), sub_self] at h

/-- The martingale property of `y`: `E_k y_{k+1} = y_k`. -/
theorem matrixCondExp_compressedMart_succ [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (k : ℕ) :
    matrixCondExp (ℱ k) μ (compressedMart ℱ μ x l (k + 1)) =ᵐ[μ] compressedMart ℱ μ x l k := by
  have hz := matrixMemLp_compressed_one (ℱ := ℱ) (l := l) hxi (k + 1)
  have h := matrixCondExp_add (m := ℱ k) (matrixMemLp_compressedMart_one (ℱ := ℱ) (l := l) hxi k)
    (hz.sub (hz.matrixCondExp (m := ℱ k) le_rfl))
  rw [matrixCondExp_of_measurable (ℱ.le k) (measurable_compressedMart k)
    (matrixMemLp_compressedMart_one hxi k), ← compressedMart_succ] at h
  filter_upwards [h, cuc_matrixCondExp_mdiff (ℱ := ℱ) (l := l) hxi k] with ω h h'
  rw [h, Pi.add_apply, h', Pi.zero_apply, add_zero]

/-- `y` is a martingale: `E_j y_k = y_j` for `j ≤ k`. -/
theorem matrixCondExp_compressedMart [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ) {j k : ℕ}
    (hjk : j ≤ k) :
    matrixCondExp (ℱ j) μ (compressedMart ℱ μ x l k) =ᵐ[μ] compressedMart ℱ μ x l j := by
  induction k, hjk using Nat.le_induction with
  | base =>
    rw [matrixCondExp_of_measurable (ℱ.le j) (measurable_compressedMart j)
      (matrixMemLp_compressedMart_one hxi j)]
  | succ k hjk ih =>
    exact ((matrixCondExp_matrixCondExp_of_le (ℱ.mono hjk) (ℱ.le k) _).symm.trans
      (matrixCondExp_congr_ae (matrixCondExp_compressedMart_succ hxi k))).trans ih

/-- `y_k − z_k = Σ_{j<k} (z_j − E_j z_{j+1}) ⪰ 0` (Randrianantoanina, (3.5), (3.6)). -/
theorem posSemidef_compressedMart_sub [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (k : ℕ) :
    ∀ᵐ ω ∂μ, (compressedMart ℱ μ x l k ω - compressed ℱ μ x l k ω).PosSemidef := by
  induction k with
  | zero => exact ae_of_all _ fun ω => by simp [compressedMart_zero, Matrix.PosSemidef.zero]
  | succ k ih =>
    filter_upwards [ih, matrixCondExp_compressed_le (l := l) hxi hx k] with ω ih h
    have e : compressedMart ℱ μ x l (k + 1) ω - compressed ℱ μ x l (k + 1) ω =
        (compressedMart ℱ μ x l k ω - compressed ℱ μ x l k ω) +
          (compressed ℱ μ x l k ω - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω) := by
      rw [compressedMart_succ, Pi.add_apply, Pi.sub_apply]
      abel
    rw [e]
    exact ih.add h

/-- `y_k ⪰ 0`, as `y_k ⪰ z_k ⪰ 0`. -/
theorem posSemidef_compressedMart [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (k : ℕ) :
    ∀ᵐ ω ∂μ, (compressedMart ℱ μ x l k ω).PosSemidef := by
  filter_upwards [posSemidef_compressedMart_sub (ℱ := ℱ) (l := l) hxi hx k,
    posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx k] with ω h1 h2
  simpa using h1.add h2

/-! ### Lemma 3.4 -/

/-- Orthogonality of the martingale differences:
`τ (y_{k+1}²) = τ (y_k²) + τ ((z_{k+1} − E_k z_{k+1})²)`, since `τ (y_k (z_{k+1} − E_k z_{k+1}))
= τ (y_k E_k (z_{k+1} − E_k z_{k+1})) = 0`. -/
private theorem cuc_matrixTrace_mart_sq_succ [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hl : 0 ≤ l) (k : ℕ) :
    matrixTrace μ (fun ω => compressedMart ℱ μ x l (k + 1) ω * compressedMart ℱ μ x l (k + 1) ω) =
      matrixTrace μ (fun ω => compressedMart ℱ μ x l k ω * compressedMart ℱ μ x l k ω) +
      matrixTrace μ (fun ω =>
        (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) ω *
        (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) ω) := by
  set d := compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))
    with hd_def
  have hy := matrixMemLp_compressedMart (ℱ := ℱ) hxi hx hl k
  have hz := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl (k + 1)
  have hd : MatrixMemLp d ∞ μ := hz.sub (hz.matrixCondExp le_top)
  have h0 : matrixTrace μ (fun ω => compressedMart ℱ μ x l k ω * d ω) = 0 := by
    rw [← matrixTrace_mul_matrixCondExp (ℱ.le k) (p := ∞) (q := 1) (measurable_compressedMart k) hy
      (hd.mono_exponent le_top)]
    have h1 : (fun ω => compressedMart ℱ μ x l k ω * matrixCondExp (ℱ k) μ d ω) =ᵐ[μ]
        fun _ => 0 :=
      (cuc_matrixCondExp_mdiff (ℱ := ℱ) (l := l) hxi k).mono fun ω hω => by
        simp only [hd_def, hω, Pi.zero_apply, mul_zero]
    rw [matrixTrace_congr_ae h1]
    simp [matrixTrace]
  have e : ∀ ω, (compressedMart ℱ μ x l (k + 1) ω * compressedMart ℱ μ x l (k + 1) ω).trace =
      (compressedMart ℱ μ x l k ω * compressedMart ℱ μ x l k ω).trace +
        2 * (compressedMart ℱ μ x l k ω * d ω).trace + (d ω * d ω).trace := fun ω => by
    rw [compressedMart_succ, Pi.add_apply]
    exact cuc_trace_add_mul_self _ _
  have I1 := cuc_integrable_trace_mul hy hy
  have I2 := cuc_integrable_trace_mul hy hd
  have I3 := cuc_integrable_trace_mul hd hd
  have key := cuc_integral_add₃ I1 I2 I3 2
  unfold matrixTrace at h0 ⊢
  simp only [e]
  beta_reduce at key h0 ⊢
  rw [key, h0, mul_zero, add_zero]

/-- One step of Lemma 3.4 (`I` and `II` of the source):
`‖z_{k+1} − E_k z_{k+1}‖₂² ≤ 2 (‖z_{k+1}‖₂² − ‖z_k‖₂²) + 6 λ τ (z_k − z_{k+1})`. -/
private theorem cuc_matrixTrace_diff_sq_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hl : 0 ≤ l) (k : ℕ) :
    matrixTrace μ (fun ω =>
        (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) ω *
        (compressed ℱ μ x l (k + 1) - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) ω) ≤
      2 * matrixTrace μ (fun ω => compressed ℱ μ x l (k + 1) ω * compressed ℱ μ x l (k + 1) ω) -
        2 * matrixTrace μ (fun ω => compressed ℱ μ x l k ω * compressed ℱ μ x l k ω) +
        6 * l * (matrixTrace μ (compressed ℱ μ x l k) -
          matrixTrace μ (compressed ℱ μ x l (k + 1))) := by
  set a := compressed ℱ μ x l (k + 1) with ha_def
  set b := compressed ℱ μ x l k with hb_def
  set e := matrixCondExp (ℱ k) μ a with he_def
  have ha := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl (k + 1)
  have hb := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl k
  have he : MatrixMemLp e ∞ μ := ha.matrixCondExp le_top
  have hap := posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx (k + 1)
  have hbp := posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx k
  have hep : ∀ᵐ ω ∂μ, (e ω).PosSemidef := posSemidef_matrixCondExp hap (ha.mono_exponent le_top)
  have hc : ∀ᵐ ω ∂μ, (b ω - e ω).PosSemidef := matrixCondExp_compressed_le hxi hx k
  have hbl : ∀ ω, (l • (1 : Matrix n n ℝ) - b ω).PosSemidef :=
    posSemidef_smul_one_sub_compressed hl k
  have hbe : MatrixMemLp (b - e) ∞ μ := hb.sub he
  -- `‖a − E a‖₂² ≤ 2 ‖a − b‖₂² + 2 ‖b − E a‖₂²`, `a = z_{k+1}`, `b = z_k`
  have S1 := cuc_integral_le (cuc_integrable_trace_mul (ha.sub he) (ha.sub he))
    (cuc_integrable_trace_mul ha ha) (cuc_integrable_trace_mul hb hb)
    (cuc_integrable_trace_mul hb ha) (cuc_integrable_trace_mul hbe hbe) 2 2 (-4) 2
    (by
      filter_upwards [hap, hbp, hep] with ω hap hbp hep
      have h := cuc_trace_split_le hap.isHermitian hbp.isHermitian hep.isHermitian
      simp only [Pi.sub_apply]
      linarith)
  -- `I`: `τ (b (b − E a)) ≤ λ τ (b − E a)`, as `0 ⪯ b ⪯ λ` and `b − E a ⪰ 0`
  have S2 := cuc_integral_le (cuc_integrable_trace_mul hb hb) (cuc_integrable_trace_mul hb he)
    (cuc_integrable_trace (hb.mono_exponent le_top))
    (cuc_integrable_trace (he.mono_exponent le_top)) (integrable_zero Ω ℝ μ) 1 l (-l) 0
    (by
      filter_upwards [hc] with ω hc
      have h := trace_mul_le_of_le_smul_one (hbl ω) hc
      rw [mul_sub, Matrix.trace_sub, Matrix.trace_sub] at h
      simp only [Pi.zero_apply]
      linarith)
  -- `II`: `‖b − E a‖₂² ≤ λ τ (b − E a)`, as `0 ⪯ b − E a ⪯ b ⪯ λ`
  have S3 := cuc_integral_le (cuc_integrable_trace_mul hbe hbe)
    (cuc_integrable_trace (hb.mono_exponent le_top))
    (cuc_integrable_trace (he.mono_exponent le_top))
    (integrable_zero Ω ℝ μ) (integrable_zero Ω ℝ μ) l (-l) 0 0
    (by
      filter_upwards [hc, hep] with ω hc hep
      have hcl : (l • (1 : Matrix n n ℝ) - (b ω - e ω)).PosSemidef := by
        have h := (hbl ω).add hep
        rwa [show l • (1 : Matrix n n ℝ) - b ω + e ω = l • 1 - (b ω - e ω) by abel] at h
      have h := trace_mul_le_of_le_smul_one hcl hc
      rw [Matrix.trace_sub] at h
      simp only [Pi.sub_apply, Pi.zero_apply]
      linarith)
  -- `τ (b a) = τ (b E a)` and `τ (E a) = τ (a)`
  have A1 := matrixTrace_mul_matrixCondExp (ℱ.le k) (p := ∞) (q := 1) (measurable_compressed k) hb
    (ha.mono_exponent le_top)
  have A2 := matrixTrace_matrixCondExp (ℱ.le k) (ha.mono_exponent le_top)
  unfold matrixTrace at A1 A2 ⊢
  simp only [← ha_def, ← hb_def, ← he_def, Pi.sub_apply] at S1 S2 S3 A1 A2 ⊢
  rw [A2] at S2 S3
  linarith

/-- The telescoped form of Lemma 3.4:
`‖y_m‖₂² ≤ 2 ‖z_m‖₂² − ‖z_0‖₂² + 6 λ τ (z_0 − z_m)`. -/
private theorem cuc_matrixTrace_mart_sq_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hl : 0 ≤ l) (m : ℕ) :
    matrixTrace μ (fun ω => compressedMart ℱ μ x l m ω * compressedMart ℱ μ x l m ω) ≤
      2 * matrixTrace μ (fun ω => compressed ℱ μ x l m ω * compressed ℱ μ x l m ω) -
        matrixTrace μ (fun ω => compressed ℱ μ x l 0 ω * compressed ℱ μ x l 0 ω) +
        6 * l * (matrixTrace μ (compressed ℱ μ x l 0) - matrixTrace μ (compressed ℱ μ x l m)) := by
  induction m with
  | zero =>
    rw [compressedMart_zero]
    linarith
  | succ m ih =>
    rw [cuc_matrixTrace_mart_sq_succ hxi hx hl m]
    linarith [cuc_matrixTrace_diff_sq_le (ℱ := ℱ) hxi hx hl m]

/-- **Randrianantoanina, Lemma 3.4**: `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)`. -/
theorem matrixTrace_compressedMart_sq_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hl : 0 ≤ l) (N : ℕ) :
    matrixTrace μ (fun ω => compressedMart ℱ μ x l N ω * compressedMart ℱ μ x l N ω) ≤
      6 * l * matrixTrace μ x := by
  have h := cuc_matrixTrace_mart_sq_le (ℱ := ℱ) hxi hx hl N
  have hzN := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl N
  have hz0 := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl 0
  have hpN := posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx N
  have hp0 := posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx 0
  -- `‖z_N‖₂² ≤ λ τ (z_N)`
  have h1 : matrixTrace μ (fun ω => compressed ℱ μ x l N ω * compressed ℱ μ x l N ω) ≤
      l * matrixTrace μ (compressed ℱ μ x l N) := by
    rw [← matrixTrace_smul]
    refine matrixTrace_mono ((hzN.mul hzN).mono_exponent le_top)
      ((hzN.mono_exponent le_top).const_smul l) ?_
    filter_upwards [hpN] with ω hω
    simp only [Pi.smul_apply, Matrix.trace_smul, smul_eq_mul]
    exact trace_mul_le_of_le_smul_one (posSemidef_smul_one_sub_compressed hl N ω) hω
  have h2 : 0 ≤ matrixTrace μ (fun ω => compressed ℱ μ x l 0 ω * compressed ℱ μ x l 0 ω) := by
    unfold matrixTrace
    exact integral_nonneg_of_ae (hp0.mono fun ω hω => trace_mul_nonneg_of_posSemidef hω hω)
  have h3 : 0 ≤ matrixTrace μ (compressed ℱ μ x l N) := matrixTrace_nonneg hpN
  -- `τ (z_0) = τ (q_1 x_0) ≤ τ (x_0) = τ (x)`
  have h4 : matrixTrace μ (compressed ℱ μ x l 0) ≤ matrixTrace μ x := by
    rw [← matrixTrace_matrixCondExp (ℱ.le 0) hxi]
    refine matrixTrace_mono (hz0.mono_exponent le_top) (hxi.matrixCondExp le_rfl) ?_
    filter_upwards [posSemidef_matrixCondExp (m := ℱ 0) hx hxi] with ω hω
    have hq := cuculescu_isProj (fun j => matrixCondExp (ℱ j) μ x) l 1 ω
    have h := trace_mul_le_of_le_smul_one
      (by rw [one_smul]; exact cuc_posSemidef_one_sub hq.1 hq.2) hω
    rw [one_mul, ← cuc_trace_mul_eq hq.1] at h
    exact h
  have h5 := mul_le_mul_of_nonneg_left h4 hl
  have h6 := mul_nonneg hl h3
  linarith

end Compressed

end BanachProbability
