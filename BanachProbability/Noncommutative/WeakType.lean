module

public import BanachProbability.Noncommutative.Cuculescu

/-!
# Weak type `(1, 1)` of noncommutative martingale transforms

Randrianantoanina's theorem (N. Randrianantoanina, *Non-commutative martingale transforms*,
J. Funct. Anal. 194 (2002), Theorem 3.1, with the constant `14√3/3 + 28`) for the von Neumann
algebra `L^∞ (Ω, μ) ⊗ M_n (ℝ)` of a probability space with a filtration `ℱ` and predictable
scalar multipliers `|c_k| ≤ 1` (the multipliers commuting with `N_{k+1}`, see `ncTransform`):
`λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ C ‖x‖_{L¹ (τ)}` for every symmetric `ℱ_N`-measurable `x ∈ L¹`, every
`λ > 0` and every `N` (`weakType_one_one`).

(The steps of the proof, Theorem 2.3 and Lemmas 3.2–3.5 of the source, are described at the
declarations below.)

The constants obtained are `26` for positive semidefinite `x` (`weakType_one_one_of_posSemidef`)
and `52` in general (`weakType_one_one`), instead of the source's `14√3/3 + 28`: the counting form
of Lemma 3.2 corresponds to the source's parameters `α = β = 1` in
`24 α^{−1} β^{−2} + 2 (1 − α)^{−1}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Matrix

namespace BanachProbability

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive part `A⁺ = max (A, 0)` of a symmetric matrix. -/
noncomputable def posPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => max t 0) A

/-- The negative part `A⁻ = max (−A, 0)` of a symmetric matrix. -/
noncomputable def negPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun t : ℝ => max (-t) 0) A

/-- `tr f (A) = Σ_i f (λ_i (A))`: `f (A) = U diag (f (λ_i)) Uᴴ` with `U` orthogonal. -/
private theorem trace_cfc_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

/-- `f (A) ⪰ 0` for `f ≥ 0`: `f (A) = U diag (f (λ_i)) Uᴴ` for a symmetric `A`, and `f (A) = 0`
otherwise (the junk value of `cfc`). -/
private theorem posSemidef_cfc {A : Matrix n n ℝ} {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    (cfc f A).PosSemidef := by
  by_cases hA : A.IsHermitian
  · rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose]
    refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_diagonal _)
      fun v => ?_
    simp only [dotProduct, Matrix.mulVec_diagonal, star_trivial]
    exact Finset.sum_nonneg fun i _ => by
      simpa [mul_left_comm] using mul_nonneg (hf (hA.eigenvalues i)) (mul_self_nonneg (v i))
  · rw [cfc_apply_of_not_predicate A (show ¬ IsSelfAdjoint A from hA)]
    exact Matrix.PosSemidef.zero

omit [Fintype n] [DecidableEq n] in
/-- A real symmetric matrix equals its transpose. -/
private theorem transpose_eq_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA.eq

theorem posPart_sub_negPart {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    posPart A - negPart A = A := by
  rw [posPart, negPart, ← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) A]
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  congr 1
  funext t
  rcases le_total 0 t with ht | ht
  · simp [ht]
  · simp [ht]

theorem posSemidef_posPart (A : Matrix n n ℝ) : (posPart A).PosSemidef := by
  exact posSemidef_cfc fun t => le_max_right t 0

theorem posSemidef_negPart (A : Matrix n n ℝ) : (negPart A).PosSemidef := by
  exact posSemidef_cfc fun t => le_max_right (-t) 0

/-- `‖A‖_{S_1} = tr A⁺ + tr A⁻` for a symmetric `A`. -/
theorem schattenNorm_one_eq_trace_posPart_add {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    schattenNorm 1 A = (posPart A).trace + (negPart A).trace := by
  -- `‖A‖_{S_1} = Σ |λ_i|` and `|t| = max t 0 + max (−t) 0`.
  have h := schattenNorm_rpow_of_isHermitian hA (q := 1) one_pos
  simp only [ENNReal.ofReal_one, Real.rpow_one] at h
  rw [h, posPart, negPart, trace_cfc_eq_sum hA, trace_cfc_eq_sum hA, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (max_zero_add_max_neg_zero_eq_abs_self _).symm

omit [DecidableEq n] in
/-- Subadditivity of the rank. -/
private theorem rank_add_le (A B : Matrix n n ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [DecidableEq n] in
/-- The rank of an idempotent matrix is its trace. -/
private theorem rank_eq_trace {P : Matrix n n ℝ} (hP : P * P = P) : (P.rank : ℝ) = P.trace := by
  classical
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ he).trace]
  rfl

omit [DecidableEq n] in
/-- The Frobenius identity `tr (Aᵀ A) = Σ_{ij} A_{ij}²`. -/
private theorem trace_transpose_mul_self (A : Matrix n n ℝ) :
    (Aᵀ * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

omit [DecidableEq n] in
private theorem trace_transpose_mul_self_nonneg (A : Matrix n n ℝ) : 0 ≤ (Aᵀ * A).trace := by
  rw [trace_transpose_mul_self]
  positivity

omit [DecidableEq n] in
/-- `tr (A²) ≥ 0` for a symmetric `A`. -/
private theorem trace_mul_self_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    0 ≤ (A * A).trace := by
  have h := trace_transpose_mul_self_nonneg A
  rwa [transpose_eq_of_isHermitian hA] at h

omit [DecidableEq n] in
/-- `tr ((U − V)²) ≤ 2 tr (U²) + 2 tr (V²)` for symmetric `U`, `V`, since `tr ((U + V)²) ≥ 0`. -/
private theorem trace_sub_mul_self_le {U V : Matrix n n ℝ} (hU : U.IsHermitian)
    (hV : V.IsHermitian) : ((U - V) * (U - V)).trace ≤ 2 * (U * U).trace + 2 * (V * V).trace := by
  have h := trace_mul_self_nonneg (hU.add hV)
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.trace_add, Matrix.trace_sub] at h ⊢
  linarith

omit [DecidableEq n] in
/-- `‖q A‖_{S_2}² ≤ ‖A‖_{S_2}²` for a symmetric projection `q`:
`tr (Aᵀ A) = tr ((q A)ᵀ q A) + tr (((1 − q) A)ᵀ (1 − q) A)`. -/
private theorem trace_transpose_mul_self_mul_le {q : Matrix n n ℝ} (hq : q * q = q) (hqt : qᵀ = q)
    (A : Matrix n n ℝ) : ((q * A)ᵀ * (q * A)).trace ≤ (Aᵀ * A).trace := by
  classical
  have h1 : (q * A)ᵀ * (q * A) = Aᵀ * q * A := by
    rw [Matrix.transpose_mul, hqt]
    calc Aᵀ * q * (q * A) = Aᵀ * (q * q) * A := by noncomm_ring
      _ = Aᵀ * q * A := by rw [hq]
  have h11 : (1 - q) * (1 - q) = 1 - q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq, sub_self, sub_zero]
  have h2 : ((1 - q) * A)ᵀ * ((1 - q) * A) = Aᵀ * A - Aᵀ * q * A := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hqt]
    calc Aᵀ * (1 - q) * ((1 - q) * A) = Aᵀ * ((1 - q) * (1 - q)) * A := by noncomm_ring
      _ = Aᵀ * A - Aᵀ * q * A := by rw [h11]; noncomm_ring
  have h3 := trace_transpose_mul_self_nonneg ((1 - q) * A)
  rw [h2, Matrix.trace_sub] at h3
  rw [h1]
  linarith

omit [DecidableEq n] in
/-- `‖q A q‖_{S_2}² ≤ ‖A‖_{S_2}²` for a symmetric projection `q`. -/
private theorem trace_transpose_mul_self_compress_le {q : Matrix n n ℝ} (hq : q * q = q)
    (hqt : qᵀ = q) (A : Matrix n n ℝ) :
    ((q * A * q)ᵀ * (q * A * q)).trace ≤ (Aᵀ * A).trace := by
  have hF : ∀ X : Matrix n n ℝ, (Xᵀ * X).trace = (Xᵀᵀ * Xᵀ).trace := fun X => by
    rw [Matrix.transpose_transpose, Matrix.trace_mul_comm]
  calc ((q * A * q)ᵀ * (q * A * q)).trace = ((q * (q * A)ᵀ)ᵀ * (q * (q * A)ᵀ)).trace := by
        rw [hF (q * A * q), Matrix.transpose_mul, hqt]
    _ ≤ ((q * A)ᵀᵀ * (q * A)ᵀ).trace := trace_transpose_mul_self_mul_le hq hqt _
    _ = ((q * A)ᵀ * (q * A)).trace := (hF _).symm
    _ ≤ (Aᵀ * A).trace := trace_transpose_mul_self_mul_le hq hqt A

/-- `#{s_i (−A) > s} = #{s_i (A) > s}`. -/
private theorem countAbove_neg (s : ℝ) (A : Matrix n n ℝ) : countAbove s (-A) = countAbove s A := by
  have key : ∀ {B C : Matrix n n ℝ} (hB : B.IsHermitian) (hC : C.IsHermitian), B = C →
      hB.eigenvalues = hC.eigenvalues := by
    intro B C hB hC h
    subst h
    rfl
  have h : (-A)ᴴ * (-A) = Aᴴ * A := by simp
  unfold countAbove singularValue
  rw [key _ _ h]

/-- The rank count that replaces Lemma 3.2 of Randrianantoanina (2002) for finite matrices:
compressing `S` by `q` (a projection in the applications) changes the number of singular values
larger than `s` by at most `2 rank (1 − q)`, since `S − q S q = (1 − q) S + q S (1 − q)`. -/
theorem countAbove_le_countAbove_compress (S q : Matrix n n ℝ) (s : ℝ) :
    countAbove s S ≤ countAbove s (q * S * q) + 2 * (1 - q).rank := by
  have hS : S = q * S * q + ((1 - q) * S + q * S * (1 - q)) := by noncomm_ring
  have hR : ((1 - q) * S + q * S * (1 - q)).rank ≤ 2 * (1 - q).rank := by
    have h1 := Matrix.rank_mul_le_left (1 - q) S
    have h2 := Matrix.rank_mul_le_right (q * S) (1 - q)
    have h3 := rank_add_le ((1 - q) * S) (q * S * (1 - q))
    omega
  calc countAbove s S = countAbove s (q * S * q + ((1 - q) * S + q * S * (1 - q))) := by
        rw [← hS]
    _ ≤ countAbove s (q * S * q) + ((1 - q) * S + q * S * (1 - q)).rank :=
        countAbove_add_le_add_rank _ _ _
    _ ≤ _ := by omega

end Matrix

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
positive semidefinite `x`: `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 26 τ (x)`. -/
theorem weakType_one_one_of_posSemidef [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {N : ℕ}
    {x : Ω → Matrix n n ℝ} (hxm : Measurable[ℱ N] x) (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ ω, (x ω).PosSemidef) {c : ℕ → Ω → ℝ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 26 * matrixTrace μ x := by
  sorry

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
symmetric `x`: `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 52 ‖x‖_{L¹ (τ)}`. -/
theorem weakType_one_one [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {N : ℕ}
    {x : Ω → Matrix n n ℝ} (hxm : Measurable[ℱ N] x) (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ ω, (x ω).IsHermitian) {c : ℕ → Ω → ℝ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 52 * ∫ ω, schattenNorm 1 (x ω) ∂μ := by
  sorry

end Main

end BanachProbability
