module

public import BanachProbability.Noncommutative.MatrixCube
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Cuculescu's projections on the matrix cube

For a positive semidefinite matrix-valued function `x` on the sign cube, with martingale
`x_k = E_k x`, and `λ > 0`, Cuculescu's projections (I. Cuculescu, *Martingales on von Neumann
algebras*, J. Multivariate Anal. 1 (1971); Randrianantoanina, *Non-commutative martingale
transforms*, J. Funct. Anal. 194 (2002), Proposition 2.4) are defined recursively by
`q_0 = 1` and `q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)` (`cuculescu x λ`); with this indexing
`q_{k+1}` is a function of the signs `ε_j`, `j < k`, the Cuculescu projection at time `k`. They
satisfy:

1. `q_{k+1}` is an orthogonal projection, a function of the first `k` signs, and
   `q_{k+1} ≤ q_k` (`cuculescu_isProj`, `cuculescu_succ_adapted`, `cuculescu_succ_mul`);
2. `q_{k+1}` commutes with `q_k x_k q_k` (`commute_cuculescu_succ`);
3. `q_{k+1} x_k q_{k+1} ≤ λ q_{k+1}` (`cuculescu_mul_mul_le`);
4. `λ τ (1 − q_{N+1}) ≤ τ (x)` (`cuculescu_trace_le`), by a telescoping argument;

and the compressed process `z_k = q_{k+1} x_k q_{k+1}` (`compressed`; the source's `q_k x_k q_k`)
is a supermartingale (`condAvg_cuculescu_le`; Randrianantoanina, Lemma 3.3), since `q_{k+2}`
commutes with `q_{k+1} x_{k+1} q_{k+1}` and `p A p ≤ A` for a projection `p` commuting with
`A ≥ 0`. Its Doob decomposition `z_k = y_k + z'_k` (Randrianantoanina, (3.3)–(3.6)) has the
martingale part `y_k = z_0 + Σ_{j<k} (z_{j+1} − E_j z_{j+1})` (`compressedMart`), with
`y_k ≥ z_k` (`posSemidef_compressedMart_sub`) and `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)`
(`cubeTrace_compressedMart_sq_le`, Randrianantoanina, Lemma 3.4: a telescoping sum, using
`‖z_k‖_∞ ≤ λ` and the supermartingale property).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Cuculescu's projections `q_0 = 1`, `q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)` of the martingale
`x_k = E_k x` at level `λ`. Randrianantoanina writes `q_{k+1} = 1_{[0, λ]} (q_k x_k q_k)`; its
proof requires reading this in the reduced algebra `q_k M q_k`, i.e. as
`q_{k+1} = q_k 1_{[0, λ]} (q_k x_k q_k)`, which is the definition here (read literally,
`q_{k+1} ≥ 1 − q_k`, since `q_k x_k q_k` vanishes on the range of `1 − q_k`, and the projections
would not decrease). -/
noncomputable def cuculescu (x : (Fin N → Bool) → Matrix n n ℝ) (l : ℝ) :
    ℕ → (Fin N → Bool) → Matrix n n ℝ
  | 0 => fun _ => 1
  | k + 1 => fun ε =>
      cuculescu x l k ε *
        spectralProj (cuculescu x l k ε * condAvg k x ε * cuculescu x l k ε) (Set.Icc 0 l)

variable {x : (Fin N → Bool) → Matrix n n ℝ} {l : ℝ}

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

/-! ### Cube lemmas -/

omit [DecidableEq n] in
private theorem cuc_cubeTrace_sum {ι : Type*} (s : Finset ι)
    (f : ι → (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => ∑ i ∈ s, f i ε) = ∑ i ∈ s, cubeTrace (f i) := by
  simp only [cubeTrace, Matrix.trace_sum]
  exact avg_sum s fun i ε => (f i ε).trace

omit [DecidableEq n] in
private theorem cuc_cubeTrace_sub (f g : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => f ε - g ε) = cubeTrace f - cubeTrace g := by
  simp only [cubeTrace, Matrix.trace_sub]
  exact avg_sub _ _

private theorem cuc_condAvg_add {E : Type*} [AddCommGroup E] [Module ℝ E] (k : ℕ)
    (f g : (Fin N → Bool) → E) :
    condAvg k (fun ε => f ε + g ε) = fun ε => condAvg k f ε + condAvg k g ε := by
  funext ε
  simp only [condAvg, Finset.sum_add_distrib, smul_add]

private theorem cuc_condAvg_sub {E : Type*} [AddCommGroup E] [Module ℝ E] (k : ℕ)
    (f g : (Fin N → Bool) → E) :
    condAvg k (fun ε => f ε - g ε) = fun ε => condAvg k f ε - condAvg k g ε := by
  funext ε
  simp only [condAvg, Finset.sum_sub_distrib, smul_sub]

/-- `E_k f` is a function of the first `k` signs. -/
private theorem cuc_condAvg_agree {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (f : (Fin N → Bool) → E) {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    condAvg k f ε = condAvg k f ε' := by
  simp only [condAvg]
  congr 1
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 1
  funext j
  simp only [splice]
  split_ifs with hj
  · exact h j hj
  · rfl

omit [DecidableEq n] in
/-- `τ (e E_k f) = τ (e f)` for `e` a function of the first `k` signs (bimodule property and
`τ ∘ E_k = τ`). -/
private theorem cuc_cubeTrace_mul_condAvg {k : ℕ} {e : (Fin N → Bool) → Matrix n n ℝ}
    (he : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → e ε = e ε')
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => e ε * condAvg k f ε) = cubeTrace (fun ε => e ε * f ε) := by
  classical
  have h := condAvg_mul_mul (b := fun _ => (1 : Matrix n n ℝ)) he (fun _ _ _ => rfl) f
  have h2 := cubeTrace_condAvg k (fun ε => e ε * f ε * 1)
  rw [h] at h2
  simpa only [mul_one] using h2

private theorem cuc_succ (k : ℕ) (ε : Fin N → Bool) :
    cuculescu x l (k + 1) ε = cuculescu x l k ε *
      spectralProj (cuculescu x l k ε * condAvg k x ε * cuculescu x l k ε) (Set.Icc 0 l) :=
  rfl

theorem cuculescu_isProj (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    cuculescu x l k ε * cuculescu x l k ε = cuculescu x l k ε ∧
      (cuculescu x l k ε)ᵀ = cuculescu x l k ε := by
  induction k with
  | zero =>
    change (1 : Matrix n n ℝ) * 1 = 1 ∧ (1 : Matrix n n ℝ)ᵀ = 1
    exact ⟨mul_one 1, Matrix.transpose_one⟩
  | succ k ih =>
    rw [cuc_succ k ε]
    exact ⟨cuc_step_mul_self ih.1 ih.2 (posSemidef_condAvg hx k ε) _,
      cuc_step_transpose ih.1 ih.2 (posSemidef_condAvg hx k ε) _⟩

theorem cuculescu_succ_adapted (k : ℕ) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    cuculescu x l (k + 1) ε = cuculescu x l (k + 1) ε' := by
  induction k generalizing ε ε' with
  | zero =>
    rw [cuc_succ 0 ε, cuc_succ 0 ε', cuc_condAvg_agree x h]
    rfl
  | succ k ih =>
    rw [cuc_succ (k + 1) ε, cuc_succ (k + 1) ε', ih fun j hj => h j (Nat.lt_succ_of_lt hj),
      cuc_condAvg_agree x h]

/-- `q_k` is a function of the first `k` signs. -/
private theorem cuc_adapted (k : ℕ) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) :
    cuculescu x l k ε = cuculescu x l k ε' := by
  cases k with
  | zero => rfl
  | succ k => exact cuculescu_succ_adapted k fun j hj => h j (Nat.lt_succ_of_lt hj)

/-- The projections decrease: `q_{k+1} q_k = q_{k+1}`. -/
theorem cuculescu_succ_mul (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    cuculescu x l (k + 1) ε * cuculescu x l k ε = cuculescu x l (k + 1) ε := by
  rw [cuc_succ k ε]
  exact cuc_step_mul_q (cuculescu_isProj hx k ε).1 _

theorem commute_cuculescu_succ (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    Commute (cuculescu x l (k + 1) ε)
      (cuculescu x l k ε * condAvg k x ε * cuculescu x l k ε) := by
  rw [cuc_succ k ε]
  exact cuc_step_commute (cuculescu_isProj hx k ε).1 (cuculescu_isProj hx k ε).2
    (posSemidef_condAvg hx k ε) _

-- `hl` is not used: `(λ − t) 1_{[0, λ]} (t) ≥ 0` for every real `λ`.
set_option linter.unusedVariables false in
/-- `q_{k+1} x_k q_{k+1} ≤ λ q_{k+1}`. -/
theorem cuculescu_mul_mul_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) (k : ℕ)
    (ε : Fin N → Bool) :
    (l • cuculescu x l (k + 1) ε -
      cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε).PosSemidef := by
  rw [cuc_succ k ε]
  exact cuc_step_le (cuculescu_isProj hx k ε).1 (cuculescu_isProj hx k ε).2
    (posSemidef_condAvg hx k ε) l

-- `hl` is not used: the telescoping argument works for every real `λ`.
set_option linter.unusedVariables false in
/-- `λ τ (1 − q_{N+1}) ≤ τ (x)`. -/
theorem cuculescu_trace_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) :
    l * cubeTrace (fun ε => 1 - cuculescu x l (N + 1) ε) ≤ cubeTrace x := by
  -- `1 − q_{N+1} = Σ_{k ≤ N} (q_k − q_{k+1})`
  have hsum1 : cubeTrace (fun ε => 1 - cuculescu x l (N + 1) ε) =
      ∑ k ∈ Finset.range (N + 1),
        cubeTrace (fun ε => cuculescu x l k ε - cuculescu x l (k + 1) ε) := by
    rw [← cuc_cubeTrace_sum]
    congr 1
    funext ε
    exact (Finset.sum_range_sub' (fun k => cuculescu x l k ε) (N + 1)).symm
  -- `τ (x) = τ (q_{N+1} x) + Σ_{k ≤ N} τ ((q_k − q_{k+1}) x)`
  have hsum2 : ∑ k ∈ Finset.range (N + 1),
      cubeTrace (fun ε => (cuculescu x l k ε - cuculescu x l (k + 1) ε) * x ε) =
      cubeTrace x - cubeTrace (fun ε => cuculescu x l (N + 1) ε * x ε) := by
    rw [← cuc_cubeTrace_sum, ← cuc_cubeTrace_sub]
    congr 1
    funext ε
    rw [← Finset.sum_mul, Finset.sum_range_sub' (fun k => cuculescu x l k ε), sub_mul]
    change 1 * x ε - _ = _
    rw [one_mul]
  -- `τ ((q_k − q_{k+1}) x) = τ ((q_k − q_{k+1}) x_k) ≥ λ τ (q_k − q_{k+1})`
  have hstep : ∀ k, l * cubeTrace (fun ε => cuculescu x l k ε - cuculescu x l (k + 1) ε) ≤
      cubeTrace (fun ε => (cuculescu x l k ε - cuculescu x l (k + 1) ε) * x ε) := by
    intro k
    have he : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) →
        cuculescu x l k ε - cuculescu x l (k + 1) ε =
          cuculescu x l k ε' - cuculescu x l (k + 1) ε' :=
      fun ε ε' h => by rw [cuc_adapted k h, cuculescu_succ_adapted k h]
    rw [← cuc_cubeTrace_mul_condAvg (e := fun ε => cuculescu x l k ε - cuculescu x l (k + 1) ε)
      he x]
    simp only [cubeTrace]
    rw [← avg_const_mul]
    refine avg_mono fun ε => ?_
    rw [cuc_succ k ε]
    exact cuc_step_trace (cuculescu_isProj hx k ε).1 (cuculescu_isProj hx k ε).2
      (posSemidef_condAvg hx k ε) l
  -- `τ (q_{N+1} x) = τ (q_{N+1} x q_{N+1}) ≥ 0`
  have hnonneg : 0 ≤ cubeTrace (fun ε => cuculescu x l (N + 1) ε * x ε) := by
    refine avg_nonneg fun ε => ?_
    rw [← cuc_trace_mul_eq (cuculescu_isProj hx (N + 1) ε).1]
    exact (cuc_posSemidef_conj (cuculescu_isProj hx (N + 1) ε).2 (hx ε)).trace_nonneg
  calc l * cubeTrace (fun ε => 1 - cuculescu x l (N + 1) ε)
      = ∑ k ∈ Finset.range (N + 1),
          l * cubeTrace (fun ε => cuculescu x l k ε - cuculescu x l (k + 1) ε) := by
        rw [hsum1, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (N + 1),
          cubeTrace (fun ε => (cuculescu x l k ε - cuculescu x l (k + 1) ε) * x ε) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = cubeTrace x - cubeTrace (fun ε => cuculescu x l (N + 1) ε * x ε) := hsum2
    _ ≤ cubeTrace x := by linarith

/-- The compressed process `q_{k+1} x_k q_{k+1}` is a supermartingale:
`E_k (q_{k+2} x_{k+1} q_{k+2}) ≤ q_{k+1} x_k q_{k+1}`. -/
theorem condAvg_cuculescu_le (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε -
      condAvg k (fun ε => cuculescu x l (k + 2) ε * condAvg (k + 1) x ε *
        cuculescu x l (k + 2) ε) ε).PosSemidef := by
  -- `q_{k+2} x_{k+1} q_{k+2} ⪯ q_{k+1} x_{k+1} q_{k+1}` pointwise
  have h1 : ∀ ε, (cuculescu x l (k + 1) ε * condAvg (k + 1) x ε * cuculescu x l (k + 1) ε -
      cuculescu x l (k + 2) ε * condAvg (k + 1) x ε * cuculescu x l (k + 2) ε).PosSemidef := by
    intro ε
    rw [cuc_succ (k + 1) ε]
    exact cuc_step_conj_le (cuculescu_isProj hx (k + 1) ε).1 (cuculescu_isProj hx (k + 1) ε).2
      (posSemidef_condAvg hx (k + 1) ε) _
  have h2 := posSemidef_condAvg_sub h1 k ε
  -- `E_k (q_{k+1} x_{k+1} q_{k+1}) = q_{k+1} E_k (x_{k+1}) q_{k+1} = q_{k+1} x_k q_{k+1}`
  have hq : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) →
      cuculescu x l (k + 1) ε = cuculescu x l (k + 1) ε' :=
    fun ε ε' h => cuculescu_succ_adapted k h
  rw [condAvg_mul_mul hq hq, condAvg_condAvg (Nat.le_succ k)] at h2
  exact h2

/-- The compressed process `z_k = q_{k+1} x_k q_{k+1}` (Randrianantoanina's `q_k x_k q_k`). -/
noncomputable def compressed (x : (Fin N → Bool) → Matrix n n ℝ) (l : ℝ) (k : ℕ)
    (ε : Fin N → Bool) : Matrix n n ℝ :=
  cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε

/-- The martingale part of the Doob decomposition of the compressed process,
`y_k = z_0 + Σ_{j<k} (z_{j+1} − E_j z_{j+1})`, equivalently
`y_k = z_k + Σ_{j<k} (z_j − E_j z_{j+1})` (Randrianantoanina, (3.3)). -/
noncomputable def compressedMart (x : (Fin N → Bool) → Matrix n n ℝ) (l : ℝ) (k : ℕ)
    (ε : Fin N → Bool) : Matrix n n ℝ :=
  compressed x l 0 ε +
    ∑ j ∈ Finset.range k, (compressed x l (j + 1) ε - condAvg j (compressed x l (j + 1)) ε)

/-! ### The Doob decomposition of the compressed process -/

private theorem cuc_compressedMart_succ (k : ℕ) (ε : Fin N → Bool) :
    compressedMart x l (k + 1) ε = compressedMart x l k ε +
      (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) := by
  simp only [compressedMart, Finset.sum_range_succ, add_assoc]

/-- `z_k ⪰ 0`. -/
private theorem cuc_compressed_psd (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (compressed x l k ε).PosSemidef :=
  cuc_posSemidef_conj (cuculescu_isProj hx (k + 1) ε).2 (posSemidef_condAvg hx k ε)

/-- `z_k ⪯ λ`: `z_k ⪯ λ q_{k+1} ⪯ λ`. -/
private theorem cuc_compressed_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) (k : ℕ)
    (ε : Fin N → Bool) : (l • (1 : Matrix n n ℝ) - compressed x l k ε).PosSemidef := by
  have h1 := cuculescu_mul_mul_le hx hl k ε
  have h2 := (cuc_posSemidef_one_sub (cuculescu_isProj hx (l := l) (k + 1) ε).1
    (cuculescu_isProj hx (l := l) (k + 1) ε).2).smul hl.le
  have e : l • (1 : Matrix n n ℝ) - compressed x l k ε =
      (l • cuculescu x l (k + 1) ε -
        cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε) +
      l • (1 - cuculescu x l (k + 1) ε) := by
    rw [smul_sub]
    unfold compressed
    abel
  rw [e]
  exact h1.add h2

/-- `z_k` is a function of the first `k` signs. -/
private theorem cuc_compressed_adapted (k : ℕ) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) : compressed x l k ε = compressed x l k ε' := by
  simp only [compressed]
  rw [cuculescu_succ_adapted k h, cuc_condAvg_agree x h]

private theorem cuc_compressedMart_adapted : IsAdapted (compressedMart x l) := by
  intro m ε ε' h
  simp only [compressedMart]
  rw [cuc_compressed_adapted (ε := ε) (ε' := ε') 0 fun j hj => absurd hj (Nat.not_lt_zero _)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [cuc_compressed_adapted (j + 1) fun i hi => h i (by omega),
    cuc_condAvg_agree _ fun i hi => h i (by omega)]

-- `hx` is not used: the martingale property is a formal consequence of the definition.
set_option linter.unusedVariables false in
theorem isCubeMartingale_compressedMart (hx : ∀ ε, (x ε).PosSemidef) :
    IsCubeMartingale (compressedMart x l) := by
  refine ⟨cuc_compressedMart_adapted, fun m => ?_⟩
  have h1 : compressedMart x l (m + 1) = fun ε => compressedMart x l m ε +
      (compressed x l (m + 1) ε - condAvg m (compressed x l (m + 1)) ε) :=
    funext (cuc_compressedMart_succ m)
  rw [h1, cuc_condAvg_add, cuc_condAvg_sub, condAvg_condAvg le_rfl,
    condAvg_of_isAdapted fun ε ε' h => cuc_compressedMart_adapted m ε ε' h]
  funext ε
  simp

/-- `y_k − z_k = Σ_{j<k} (z_j − E_j z_{j+1}) ⪰ 0` (Randrianantoanina, (3.5), (3.6)). -/
theorem posSemidef_compressedMart_sub (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (compressedMart x l k ε - compressed x l k ε).PosSemidef := by
  induction k with
  | zero =>
    rw [show compressedMart x l 0 ε - compressed x l 0 ε = 0 by simp [compressedMart]]
    exact Matrix.PosSemidef.zero
  | succ k ih =>
    have e : compressedMart x l (k + 1) ε - compressed x l (k + 1) ε =
        (compressedMart x l k ε - compressed x l k ε) +
          (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε) := by
      rw [cuc_compressedMart_succ]
      abel
    rw [e]
    exact ih.add (condAvg_cuculescu_le hx k ε)

/-! ### Lemma 3.4 -/

/-- Orthogonality of the martingale differences:
`τ (y_{k+1}²) = τ (y_k²) + τ ((z_{k+1} − E_k z_{k+1})²)`. -/
private theorem cuc_cubeTrace_mart_sq_succ (k : ℕ) :
    cubeTrace (fun ε => compressedMart x l (k + 1) ε * compressedMart x l (k + 1) ε) =
      cubeTrace (fun ε => compressedMart x l k ε * compressedMart x l k ε) +
      cubeTrace (fun ε => (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)) := by
  have hd : condAvg k (fun ε => compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) =
      fun _ => 0 := by
    rw [cuc_condAvg_sub, condAvg_condAvg le_rfl]
    funext ε
    exact sub_self _
  have h0 : cubeTrace (fun ε => compressedMart x l k ε *
      (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)) = 0 := by
    rw [← cuc_cubeTrace_mul_condAvg (fun ε ε' h => cuc_compressedMart_adapted k ε ε' h), hd]
    simp [cubeTrace]
  have e : ∀ ε, (compressedMart x l (k + 1) ε * compressedMart x l (k + 1) ε).trace =
      (compressedMart x l k ε * compressedMart x l k ε).trace +
      2 * (compressedMart x l k ε *
        (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)).trace +
      ((compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)).trace := by
    intro ε
    rw [cuc_compressedMart_succ k ε]
    exact cuc_trace_add_mul_self _ _
  simp only [cubeTrace] at h0 ⊢
  simp only [e, avg_add, avg_const_mul, h0, mul_zero, add_zero]

/-- One step of Lemma 3.4:
`‖y_{k+1} − y_k‖₂² ≤ 2 (‖z_{k+1}‖₂² − ‖z_k‖₂²) + 6 λ τ (z_k − z_{k+1})`. -/
private theorem cuc_cubeTrace_diff_sq_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) (k : ℕ) :
    cubeTrace (fun ε => (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)) ≤
      2 * cubeTrace (fun ε => compressed x l (k + 1) ε * compressed x l (k + 1) ε) -
        2 * cubeTrace (fun ε => compressed x l k ε * compressed x l k ε) +
        6 * l * (cubeTrace (compressed x l k) - cubeTrace (compressed x l (k + 1))) := by
  have ha := cuc_compressed_psd hx (l := l) (k + 1)
  have hb := cuc_compressed_psd hx (l := l) k
  have hEa : ∀ ε, (condAvg k (compressed x l (k + 1)) ε).PosSemidef := posSemidef_condAvg ha k
  have hc : ∀ ε, (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε).PosSemidef :=
    fun ε => condAvg_cuculescu_le hx k ε
  have hbl := cuc_compressed_le hx hl k
  -- `‖a − E a‖₂² ≤ 2 ‖a − b‖₂² + 2 ‖b − E a‖₂²`, `a = z_{k+1}`, `b = z_k`
  have P1 : ∀ ε, ((compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε)).trace ≤
      2 * (compressed x l (k + 1) ε * compressed x l (k + 1) ε).trace +
      2 * (compressed x l k ε * compressed x l k ε).trace -
      4 * (compressed x l k ε * compressed x l (k + 1) ε).trace +
      2 * ((compressed x l k ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε)).trace := fun ε =>
    cuc_trace_split_le (ha ε).isHermitian (hb ε).isHermitian (hEa ε).isHermitian
  -- `τ (b (b − E a)) ≤ λ τ (b − E a)`, as `0 ⪯ b ⪯ λ` and `b − E a ⪰ 0`
  have P2 : ∀ ε, (compressed x l k ε * compressed x l k ε).trace -
      (compressed x l k ε * condAvg k (compressed x l (k + 1)) ε).trace ≤
      l * ((compressed x l k ε).trace - (condAvg k (compressed x l (k + 1)) ε).trace) := by
    intro ε
    have h := trace_mul_le_of_le_smul_one (hb ε) (hbl ε) (hc ε)
    rwa [mul_sub, Matrix.trace_sub, Matrix.trace_sub] at h
  -- `‖b − E a‖₂² ≤ λ τ (b − E a)`, as `0 ⪯ b − E a ⪯ b ⪯ λ`
  have P3 : ∀ ε, ((compressed x l k ε - condAvg k (compressed x l (k + 1)) ε) *
        (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε)).trace ≤
      l * ((compressed x l k ε).trace - (condAvg k (compressed x l (k + 1)) ε).trace) := by
    intro ε
    have hcl : (l • (1 : Matrix n n ℝ) -
        (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε)).PosSemidef := by
      have h := (hbl ε).add (hEa ε)
      rwa [show l • (1 : Matrix n n ℝ) - compressed x l k ε +
          condAvg k (compressed x l (k + 1)) ε =
          l • 1 - (compressed x l k ε - condAvg k (compressed x l (k + 1)) ε) by abel] at h
    have h := trace_mul_le_of_le_smul_one (hc ε) hcl (hc ε)
    rwa [Matrix.trace_sub] at h
  -- `τ (b a) = τ (b E a)` and `τ (E a) = τ (a)`
  have A1 := cuc_cubeTrace_mul_condAvg (k := k) (e := compressed x l k)
    (fun ε ε' h => cuc_compressed_adapted k h) (compressed x l (k + 1))
  have A2 := cubeTrace_condAvg k (compressed x l (k + 1))
  have S1 := avg_mono P1
  have S2 := avg_mono P2
  have S3 := avg_mono P3
  simp only [avg_add, avg_sub, avg_const_mul] at S1 S2 S3
  simp only [cubeTrace] at A1 A2 ⊢
  rw [A2] at S2 S3
  linarith

/-- The telescoped form of Lemma 3.4:
`‖y_m‖₂² ≤ 2 ‖z_m‖₂² − ‖z_0‖₂² + 6 λ τ (z_0 − z_m)`. -/
private theorem cuc_cubeTrace_mart_sq_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) (m : ℕ) :
    cubeTrace (fun ε => compressedMart x l m ε * compressedMart x l m ε) ≤
      2 * cubeTrace (fun ε => compressed x l m ε * compressed x l m ε) -
        cubeTrace (fun ε => compressed x l 0 ε * compressed x l 0 ε) +
        6 * l * (cubeTrace (compressed x l 0) - cubeTrace (compressed x l m)) := by
  induction m with
  | zero =>
    have h0 : compressedMart x l 0 = compressed x l 0 := funext fun ε => by simp [compressedMart]
    rw [h0]
    linarith
  | succ m ih =>
    rw [cuc_cubeTrace_mart_sq_succ m]
    linarith [cuc_cubeTrace_diff_sq_le hx hl m]

/-- **Randrianantoanina, Lemma 3.4**: `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)`. -/
theorem cubeTrace_compressedMart_sq_le (hx : ∀ ε, (x ε).PosSemidef) (hl : 0 < l) :
    cubeTrace (fun ε => compressedMart x l N ε * compressedMart x l N ε) ≤ 6 * l * cubeTrace x := by
  have h := cuc_cubeTrace_mart_sq_le hx hl N
  -- `‖z_N‖₂² ≤ λ τ (z_N)`
  have h1 : cubeTrace (fun ε => compressed x l N ε * compressed x l N ε) ≤
      l * cubeTrace (compressed x l N) := by
    simp only [cubeTrace]
    rw [← avg_const_mul]
    exact avg_mono fun ε => trace_mul_le_of_le_smul_one (cuc_compressed_psd hx N ε)
      (cuc_compressed_le hx hl N ε) (cuc_compressed_psd hx N ε)
  have h2 : 0 ≤ cubeTrace (fun ε => compressed x l 0 ε * compressed x l 0 ε) :=
    avg_nonneg fun ε => trace_mul_nonneg_of_posSemidef (cuc_compressed_psd hx 0 ε)
      (cuc_compressed_psd hx 0 ε)
  have h3 : 0 ≤ cubeTrace (compressed x l N) :=
    avg_nonneg fun ε => (cuc_compressed_psd hx N ε).trace_nonneg
  -- `τ (z_0) = τ (q_1 x_0) ≤ τ (x_0) = τ (x)`
  have h4 : cubeTrace (compressed x l 0) ≤ cubeTrace x := by
    rw [← cubeTrace_condAvg 0 x]
    refine avg_mono fun ε => ?_
    have hq := cuculescu_isProj hx (l := l) 1 ε
    have h := trace_mul_le_of_le_smul_one (cuc_posSemidef_proj hq.1 hq.2)
      (by rw [one_smul]; exact cuc_posSemidef_one_sub hq.1 hq.2) (posSemidef_condAvg hx 0 ε)
    rw [one_mul, ← cuc_trace_mul_eq hq.1] at h
    exact h
  have h5 := mul_le_mul_of_nonneg_left h4 hl.le
  have h6 := mul_nonneg hl.le h3
  linarith

end BanachProbability
