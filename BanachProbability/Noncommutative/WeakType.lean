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

The proof follows the source:

* the Krickeberg decomposition (Randrianantoanina, Theorem 2.3), which is trivial in finite time:
  `x = x⁺ − x⁻` pointwise (`posPart`, `negPart`), each part positive semidefinite, `ℱ_N`-measurable
  and in `L¹`, with `‖x‖_{L¹ (τ)} = τ (x⁺) + τ (x⁻)` (`schattenNorm_one_eq_trace_posPart_add`);
  the transform is additive almost everywhere and the distribution function is subadditive
  (`ncDistribution_add_add_le`);
* Cuculescu's projections `q_k` at level `λ` of the martingale `x_k = E_k x` (`cuculescu`,
  Proposition 2.4);
* in place of Lemma 3.2 (whose proof uses generalized singular values): for a projection `q`,
  `S − q S q` has rank at most `2 rank (1 − q)`, so
  `#{s_i (S) > s} ≤ #{s_i (q S q) > s} + 2 rank (1 − q)` (`countAbove_le_countAbove_compress`),
  and `rank (1 − q) = tr (1 − q)`; integrating, `λ_λ (S) ≤ λ_λ (q S q) + 2 τ (1 − q)`
  (`ncDistribution_le_compress_add`), with `τ (1 − q) ≤ τ (x) / λ` for the last Cuculescu
  projection `q = q_{N+1}` (`cuculescu_trace_le`);
* Lemma 3.3: the supermartingale property of the compressed process `z_k = q_{k+1} x_k q_{k+1}`
  (`matrixCondExp_compressed_le`), and Chebyshev's inequality in `L² (τ)` for the compressed
  transform `W = z_0 + Σ_{k<N} c_k (z_{k+1} − z_k)` (`compressedTransform`), since
  `q T_c x q = q W q` (the multipliers are scalars, so they commute with the projections)
  (`ncDistribution_compress_transform_le`);
* Lemma 3.4: `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)` for the martingale part `y` of the compressed process
  (`matrixTrace_compressedMart_sq_le`);
* Lemma 3.5: `‖W‖_{L² (τ)}² ≤ 4 ‖y_N‖_{L² (τ)}²` (`matrixTrace_compressedTransform_sq_le`): the
  martingale part is transformed with constant `1` in `L² (τ)` (`matrixTrace_ncTransform_le`),
  and, the multipliers being scalar, the decreasing part gives
  `E c_j c_k tr (a_j a_k) ≤ E tr (a_j a_k)` for positive semidefinite `a_j`, `a_k`.

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

omit [DecidableEq n] in
/-- **IV** of Randrianantoanina's proof of Lemma 3.5, pointwise, for scalar multipliers with
`|c_k| ≤ 1`:
`tr ((Σ c_k a_k)²) = Σ_{j,k} c_j c_k tr (a_j a_k) ≤ Σ_{j,k} tr (a_j a_k) = tr ((Σ a_k)²)`, since
`tr (a_j a_k) ≥ 0` for positive semidefinite `a_j`, `a_k`. -/
private theorem trace_sum_smul_mul_self_le {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ i, |c i| ≤ 1) {a : ι → Matrix n n ℝ} (ha : ∀ i, (a i).PosSemidef) :
    ((∑ i ∈ s, c i • a i) * ∑ i ∈ s, c i • a i).trace ≤ ((∑ i ∈ s, a i) * ∑ i ∈ s, a i).trace := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  gcongr with j _ k _
  have h0 := trace_mul_nonneg_of_posSemidef (ha j) (ha k)
  have h0' := trace_mul_nonneg_of_posSemidef (ha k) (ha j)
  have hjk : c j * c k ≤ 1 := by
    have h := abs_mul (c j) (c k)
    have := mul_le_mul (hc j) (hc k) (abs_nonneg _) zero_le_one
    linarith [le_abs_self (c j * c k)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul]
  nlinarith

/-- `‖A⁺‖_{S_1} ≤ ‖A‖_{S_1}` for a symmetric `A`: `Σ_i |max (λ_i, 0)| ≤ Σ_i |λ_i|`. -/
private theorem schattenNorm_one_posPart_le {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    schattenNorm 1 (posPart A) ≤ schattenNorm 1 A := by
  have h1 := mcd_schattenNorm_cfc_rpow hA (fun t => max t 0) one_pos
  have h2 := schattenNorm_rpow_of_isHermitian hA (q := 1) one_pos
  simp only [ENNReal.ofReal_one, Real.rpow_one] at h1 h2
  rw [posPart, h1, h2]
  exact Finset.sum_le_sum fun i _ => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)

/-- `‖A⁻‖_{S_1} ≤ ‖A‖_{S_1}` for a symmetric `A`: `Σ_i |max (−λ_i, 0)| ≤ Σ_i |λ_i|`. -/
private theorem schattenNorm_one_negPart_le {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    schattenNorm 1 (negPart A) ≤ schattenNorm 1 A := by
  have h1 := mcd_schattenNorm_cfc_rpow hA (fun t => max (-t) 0) one_pos
  have h2 := schattenNorm_rpow_of_isHermitian hA (q := 1) one_pos
  simp only [ENNReal.ofReal_one, Real.rpow_one] at h1 h2
  rw [negPart, h1, h2]
  exact Finset.sum_le_sum fun i _ => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)

omit [DecidableEq n] in
private theorem conj_add_sum (Q A : Matrix n n ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (B C : ℕ → Matrix n n ℝ) :
    Q * (A + ∑ k ∈ s, c k • (B k - C k)) * Q =
      Q * A * Q + ∑ k ∈ s, c k • (Q * B k * Q - Q * C k * Q) := by
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul]

end Matrix

/-! ### Integration helpers -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

private theorem wkt_integrable_trace {f : Ω → Matrix n n ℝ} (hf : MatrixMemLp f 1 μ) :
    Integrable (fun ω => (f ω).trace) μ := by
  simp only [Matrix.trace, Matrix.diag]
  exact integrable_finsetSum _ fun i _ => memLp_one_iff_integrable.1 (hf i i)

/-- `ω ↦ tr (f ω g ω)` is integrable for bounded `f`, `g`. -/
private theorem wkt_integrable_trace_mul [IsFiniteMeasure μ] {f g : Ω → Matrix n n ℝ}
    (hf : MatrixMemLp f ∞ μ) (hg : MatrixMemLp g ∞ μ) :
    Integrable (fun ω => (f ω * g ω).trace) μ := by
  classical
  exact wkt_integrable_trace ((hf.mul hg).mono_exponent le_top)

omit [Fintype n] in
private theorem wkt_matrixMemLp_transpose {f : Ω → Matrix n n ℝ} {p : ℝ≥0∞}
    (hf : MatrixMemLp f p μ) : MatrixMemLp (fun ω => (f ω)ᵀ) p μ :=
  fun i j => hf j i

omit [Fintype n] in
/-- Integrating a pointwise linear inequality between integrable functions. -/
private theorem wkt_integral_le {f₀ f₁ f₂ : Ω → ℝ} (h₀ : Integrable f₀ μ) (h₁ : Integrable f₁ μ)
    (h₂ : Integrable f₂ μ) (a₁ a₂ : ℝ) (h : ∀ᵐ ω ∂μ, f₀ ω ≤ a₁ * f₁ ω + a₂ * f₂ ω) :
    ∫ ω, f₀ ω ∂μ ≤ a₁ * ∫ ω, f₁ ω ∂μ + a₂ * ∫ ω, f₂ ω ∂μ := by
  have h' := integral_mono_ae h₀ (by fun_prop) h
  rw [integral_add (by fun_prop) (by fun_prop), integral_const_mul, integral_const_mul] at h'
  exact h'

omit [Fintype n] in
/-- A predictable multiplier with `|c_k| ≤ 1` is in `L^∞`. -/
private theorem wkt_memLp_multiplier {ℱ : Filtration ℕ mΩ} {c : ℕ → Ω → ℝ}
    (hc : ∀ k, StronglyMeasurable[ℱ k] (c k)) (hc1 : ∀ k ω, |c k ω| ≤ 1) (k : ℕ) :
    MemLp (c k) ∞ μ :=
  memLp_top_of_bound ((hc k).mono (ℱ.le k)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hc1 k ω)

end Helpers

/-! ### The compressed transform -/

section Compressed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- The transform of the compressed process by the multipliers `c`,
`W = z_0 + Σ_{k<N} c_k (z_{k+1} − z_k)` with `z_k = q_{k+1} x_k q_{k+1}`
(Randrianantoanina's `q₁ x₁ q₁ + Σ_k ξ_{k−1} (q_k x_k q_k − q_{k−1} x_{k−1} q_{k−1})`). -/
noncomputable def compressedTransform (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) (c : ℕ → Ω → ℝ)
    (N : ℕ) (x : Ω → Matrix n n ℝ) (l : ℝ) : Ω → Matrix n n ℝ :=
  fun ω => compressed ℱ μ x l 0 ω +
    ∑ k ∈ Finset.range N, c k ω • (compressed ℱ μ x l (k + 1) ω - compressed ℱ μ x l k ω)

variable {ℱ : Filtration ℕ mΩ} {x : Ω → Matrix n n ℝ} {l : ℝ} {c : ℕ → Ω → ℝ} {N : ℕ}

/-- `q z_k q = q x_k q` for `q = q_{N+1}` and `k ≤ N`, since `q ≤ q_{k+1}`. -/
private theorem compress_compressed {k : ℕ} (hk : k ≤ N) (ω : Ω) :
    cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * compressed ℱ μ x l k ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω =
      cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * matrixCondExp (ℱ k) μ x ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω := by
  have hk' : k + 1 ≤ N + 1 := by omega
  have h1 := cuculescu_mul_of_le (fun j => matrixCondExp (ℱ j) μ x) l hk' ω
  have h2 := mul_cuculescu_of_le (fun j => matrixCondExp (ℱ j) μ x) l hk' ω
  simp only [compressed]
  calc cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
        (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω * matrixCondExp (ℱ k) μ x ω *
          cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω) *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω
      = (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
          cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω) * matrixCondExp (ℱ k) μ x ω *
        (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (k + 1) ω *
          cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) := by
        simp only [mul_assoc]
    _ = _ := by rw [h1, h2]

/-- `q (T_c x) q = q W q` for `q = q_{N+1}` (Randrianantoanina, proof of Lemma 3.3; the multipliers
are scalars, so they commute with the projections). -/
private theorem compress_transform_eq (ω : Ω) :
    cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * ncTransform ℱ μ c N x ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω =
      cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * compressedTransform ℱ μ c N x l ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω := by
  simp only [ncTransform, compressedTransform]
  rw [conj_add_sum, conj_add_sum, compress_compressed (Nat.zero_le N)]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  rw [compress_compressed hk', compress_compressed hk'.le]

/-- The compressed transform is symmetric. -/
private theorem isHermitian_compressedTransform (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) :
    ∀ᵐ ω ∂μ, (compressedTransform ℱ μ c N x l ω).IsHermitian := by
  filter_upwards [ae_all_iff.2 fun k => posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx k]
    with ω hz
  refine (hz 0).isHermitian.add (Finset.sum_induction _ Matrix.IsHermitian
    (fun _ _ ha hb => ha.add hb) Matrix.isHermitian_zero fun k _ => ?_)
  exact ((hz _).isHermitian.sub (hz _).isHermitian).smul (IsSelfAdjoint.all _)

/-- The compressed transform is bounded. -/
private theorem matrixMemLp_compressedTransform (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hl : 0 ≤ l) (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) : MatrixMemLp (compressedTransform ℱ μ c N x l) ∞ μ := by
  have hz := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl
  have h := (hz 0).add (MatrixMemLp.sum (Finset.range N) fun k _ =>
    MatrixMemLp.smul (r := ∞) (wkt_memLp_multiplier hc hc1 k) ((hz (k + 1)).sub (hz k)))
  convert h using 1
  funext ω
  simp only [compressedTransform, Pi.add_apply, Finset.sum_apply, Pi.sub_apply]

/-- **Randrianantoanina, Lemma 3.3** (second part): with `q = q_{N+1}` the last Cuculescu
projection, `τ (1_{(βλ, ∞)} (|q T_c x q|)) ≤ (βλ)^{−2} ‖W‖_{L² (τ)}²`, by Chebyshev's inequality in
`L² (τ)`, `q T_c x q = q W q` and `‖q W q‖_{S_2} ≤ ‖W‖_{S_2}`. -/
theorem ncDistribution_compress_transform_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {β : ℝ} (hl : 0 < l) (hβ : 0 < β) :
    ncDistribution μ (β * l) (fun ω => cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
        ncTransform ℱ μ c N x ω * cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) ≤
      (β * l)⁻¹ ^ 2 * matrixTrace μ
        (fun ω => compressedTransform ℱ μ c N x l ω * compressedTransform ℱ μ c N x l ω) := by
  have hs : 0 < β * l := mul_pos hβ hl
  have hqm : Measurable (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1)) :=
    (measurable_cuculescu (fun _ => measurable_matrixCondExp x) l (N + 1)).mono (ℱ.le (N + 1))
      le_rfl
  have hqi : MatrixMemLp (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1)) ∞ μ :=
    matrixMemLp_cuculescu (fun _ => measurable_matrixCondExp x) l (N + 1)
  have hTm : Measurable (ncTransform ℱ μ c N x) :=
    (measurable_ncTransform hc x).mono (ℱ.le N) le_rfl
  have hWi : MatrixMemLp (compressedTransform ℱ μ c N x l) ∞ μ :=
    matrixMemLp_compressedTransform hxi hx hl.le hc hc1
  have hqWq : MatrixMemLp (fun ω => cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
      compressedTransform ℱ μ c N x l ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) ∞ μ :=
    (hqi.mul (r := ∞) hWi).mul (r := ∞) hqi
  -- `‖q T_c x q‖₂² = tr ((q W q)ᵀ (q W q))`
  have heq : ∀ ω, schattenNorm (ENNReal.ofReal 2)
      (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * ncTransform ℱ μ c N x ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) ^ (2 : ℝ) =
      ((cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
          compressedTransform ℱ μ c N x l ω *
          cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω)ᵀ *
        (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω *
          compressedTransform ℱ μ c N x l ω *
          cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω)).trace := by
    intro ω
    rw [ENNReal.ofReal_ofNat, Real.rpow_two, schattenNorm_two_sq, ← trace_transpose_mul_self,
      compress_transform_eq]
  have hint : Integrable (fun ω => schattenNorm (ENNReal.ofReal 2)
      (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * ncTransform ℱ μ c N x ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) ^ (2 : ℝ)) μ := by
    simp only [heq]
    exact wkt_integrable_trace_mul (wkt_matrixMemLp_transpose hqWq) hqWq
  have h := ncDistribution_mul_rpow_le ((hqm.mul hTm).mul hqm).aemeasurable hs two_pos hint
  have h2 : ∫ ω, schattenNorm (ENNReal.ofReal 2)
      (cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω * ncTransform ℱ μ c N x ω *
        cuculescu (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω) ^ (2 : ℝ) ∂μ ≤
      matrixTrace μ
        (fun ω => compressedTransform ℱ μ c N x l ω * compressedTransform ℱ μ c N x l ω) := by
    unfold matrixTrace
    refine integral_mono_ae hint (wkt_integrable_trace_mul hWi hWi) ?_
    filter_upwards [isHermitian_compressedTransform (c := c) (N := N) (l := l) hxi hx] with ω hW
    have hq := cuculescu_isProj (fun j => matrixCondExp (ℱ j) μ x) l (N + 1) ω
    rw [heq]
    calc _ ≤ ((compressedTransform ℱ μ c N x l ω)ᵀ * compressedTransform ℱ μ c N x l ω).trace :=
          trace_transpose_mul_self_compress_le hq.1 hq.2 _
      _ = _ := by rw [transpose_eq_of_isHermitian hW]
  have h3 := h.trans h2
  rw [Real.rpow_two] at h3
  rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact h3

/-- **Randrianantoanina, Lemma 3.5**: `‖W‖_{L² (τ)}² ≤ 4 ‖y_N‖_{L² (τ)}²` for predictable scalar
multipliers with `|c_k| ≤ 1`. With the decreasing part `a_k = z_k − E_k z_{k+1} ⪰ 0` of the Doob
decomposition, `W = T_c y_N − Σ_{k<N} c_k a_k`, so `‖W‖₂² ≤ 2 ‖T_c y_N‖₂² + 2 ‖Σ c_k a_k‖₂²`;
`III`: `‖T_c y_N‖₂ ≤ ‖y_N‖₂` (`matrixTrace_ncTransform_le`); `IV`:
`‖Σ c_k a_k‖₂² ≤ ‖Σ a_k‖₂² = ‖y_N − z_N‖₂² ≤ ‖y_N‖₂²`, as `0 ⪯ y_N − z_N ⪯ y_N`. -/
theorem matrixTrace_compressedTransform_sq_le [IsFiniteMeasure μ] (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ᵐ ω ∂μ, (x ω).PosSemidef) (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) (hl : 0 ≤ l) :
    matrixTrace μ (fun ω => compressedTransform ℱ μ c N x l ω * compressedTransform ℱ μ c N x l ω) ≤
      4 * matrixTrace μ (fun ω => compressedMart ℱ μ x l N ω * compressedMart ℱ μ x l N ω) := by
  -- The decreasing part of the Doob decomposition, `a_k = z_k − E_k z_{k+1} ⪰ 0`.
  have ha : ∀ᵐ ω ∂μ, ∀ k, (compressed ℱ μ x l k ω -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω).PosSemidef :=
    ae_all_iff.2 fun k => matrixCondExp_compressed_le hxi hx k
  -- The martingale part: `E_j y_N = y_j` for `j ≤ N`.
  have hmart : ∀ᵐ ω ∂μ, ∀ j, j ≤ N →
      matrixCondExp (ℱ j) μ (compressedMart ℱ μ x l N) ω = compressedMart ℱ μ x l j ω := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : j ≤ N
    · exact (matrixCondExp_compressedMart hxi hj).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hj
  -- `W = T_c y_N − Σ_k c_k a_k`.
  have hW : ∀ᵐ ω ∂μ, compressedTransform ℱ μ c N x l ω =
      ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω - ∑ k ∈ Finset.range N, c k ω •
        (compressed ℱ μ x l k ω - matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω) := by
    filter_upwards [hmart] with ω hω
    simp only [compressedTransform, ncTransform]
    rw [hω 0 (Nat.zero_le N), compressedMart_zero, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [hω (k + 1) hk', hω k hk'.le, compressedMart_succ k, Pi.add_apply, Pi.sub_apply,
      ← smul_sub]
    congr 1
    abel
  have hyN := posSemidef_compressedMart (ℱ := ℱ) (l := l) hxi hx N
  have hU : ∀ᵐ ω ∂μ, (ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω).IsHermitian :=
    isHermitian_ncTransform (hyN.mono fun ω h => h.isHermitian)
  have hV : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range N, c k ω • (compressed ℱ μ x l k ω -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω)).IsHermitian :=
    ha.mono fun ω h => Finset.sum_induction _ Matrix.IsHermitian (fun _ _ hA hB => hA.add hB)
      Matrix.isHermitian_zero fun k _ => (h k).isHermitian.smul (IsSelfAdjoint.all _)
  -- Integrability: all the functions involved are bounded.
  have hz := matrixMemLp_compressed (ℱ := ℱ) hxi hx hl
  have hai : ∀ k, MatrixMemLp (compressed ℱ μ x l k -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1))) ∞ μ :=
    fun k => (hz k).sub ((hz (k + 1)).matrixCondExp le_top)
  have hyi := matrixMemLp_compressedMart (ℱ := ℱ) hxi hx hl N
  have hUi : MatrixMemLp (ncTransform ℱ μ c N (compressedMart ℱ μ x l N)) ∞ μ :=
    hyi.ncTransform hc hc1 le_top
  have hVi : MatrixMemLp (fun ω => ∑ k ∈ Finset.range N, c k ω • (compressed ℱ μ x l k ω -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω)) ∞ μ :=
by
    have h := MatrixMemLp.sum (Finset.range N) fun k _ =>
      MatrixMemLp.smul (r := ∞) (wkt_memLp_multiplier hc hc1 k) (hai k)
    convert h using 1
    funext ω
    rw [Finset.sum_apply]
    rfl
  have hAi : MatrixMemLp (fun ω => ∑ k ∈ Finset.range N, (compressed ℱ μ x l k ω -
      matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω)) ∞ μ := by
    have h := MatrixMemLp.sum (Finset.range N) fun k _ => hai k
    convert h using 1
    funext ω
    rw [Finset.sum_apply]
    rfl
  have hWi : MatrixMemLp (compressedTransform ℱ μ c N x l) ∞ μ :=
    matrixMemLp_compressedTransform hxi hx hl hc hc1
  -- `τ (W²) ≤ 2 τ ((T_c y_N)²) + 2 τ ((Σ c_k a_k)²)`.
  have h1 := wkt_integral_le (wkt_integrable_trace_mul hWi hWi)
    (wkt_integrable_trace_mul hUi hUi) (wkt_integrable_trace_mul hVi hVi) 2 2 (by
      filter_upwards [hW, hU, hV] with ω hW hU hV
      rw [hW]
      exact trace_sub_mul_self_le hU hV)
  -- III: `τ ((T_c y_N)²) ≤ τ (y_N²)`.
  have h2 := matrixTrace_ncTransform_le hc hc1 (measurable_compressedMart N)
    (hyi.mono_exponent (le_top : (2 : ℝ≥0∞) ≤ ∞))
  have eU : (fun ω => (ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω)ᵀ *
      ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω) =ᵐ[μ]
      fun ω => ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω *
        ncTransform ℱ μ c N (compressedMart ℱ μ x l N) ω := by
    filter_upwards [hU] with ω h
    rw [transpose_eq_of_isHermitian h]
  have ey : (fun ω => (compressedMart ℱ μ x l N ω)ᵀ * compressedMart ℱ μ x l N ω) =ᵐ[μ]
      fun ω => compressedMart ℱ μ x l N ω * compressedMart ℱ μ x l N ω := by
    filter_upwards [hyN] with ω h
    rw [transpose_eq_of_isHermitian h.isHermitian]
  rw [matrixTrace_congr_ae eU, matrixTrace_congr_ae ey] at h2
  -- IV: `τ ((Σ c_k a_k)²) ≤ τ ((Σ a_k)²)`.
  have h3 := matrixTrace_mono ((hVi.mul hVi).mono_exponent le_top)
    ((hAi.mul hAi).mono_exponent le_top)
    (ha.mono fun ω h => trace_sum_smul_mul_self_le _ (fun k => hc1 k ω) h)
  -- `Σ_k a_k = y_N − z_N` and `0 ⪯ y_N − z_N ⪯ y_N`, so `τ ((Σ a_k)²) ≤ τ (y_N²)`.
  have h4 := matrixTrace_mono ((hAi.mul hAi).mono_exponent le_top)
    ((hyi.mul hyi).mono_exponent le_top)
    (by
      filter_upwards [posSemidef_compressedMart_sub (ℱ := ℱ) (l := l) hxi hx N,
        posSemidef_compressed (ℱ := ℱ) (l := l) hxi hx N] with ω h hz
      have hB : ∑ k ∈ Finset.range N, (compressed ℱ μ x l k ω -
          matrixCondExp (ℱ k) μ (compressed ℱ μ x l (k + 1)) ω) =
          compressedMart ℱ μ x l N ω - compressed ℱ μ x l N ω := by
        rw [← Pi.sub_apply, compressedMart_sub_compressed, Finset.sum_apply]
        rfl
      rw [hB]
      refine trace_mul_self_le_of_le h ?_
      rwa [sub_sub_cancel])
  simp only [matrixTrace] at h1 h2 h3 h4 ⊢
  linarith

end Compressed

/-! ### Assembly -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n]

/-- Step 1 of the proof of Theorem 3.1 in the counting form (replacing Randrianantoanina's
Lemma 3.2): `λ_s (S) ≤ λ_s (q S q) + 2 τ (1 − q)` for a projection-valued `q`, integrating
`#{s_i (S) > s} ≤ #{s_i (q S q) > s} + 2 rank (1 − q)` (`countAbove_le_countAbove_compress`) with
`rank (1 − q) = tr (1 − q)`. -/
theorem ncDistribution_le_compress_add [IsFiniteMeasure μ] {q S : Ω → Matrix n n ℝ}
    (hq : ∀ ω, q ω * q ω = q ω) (hqi : MatrixMemLp q 1 μ) (hS : AEMeasurable S μ) (s : ℝ) :
    ncDistribution μ s S ≤
      ncDistribution μ s (fun ω => q ω * S ω * q ω) + 2 * matrixTrace μ (fun ω => 1 - q ω) := by
  have hqSq : AEMeasurable (fun ω => q ω * S ω * q ω) μ :=
    (hqi.aemeasurable.mul hS).mul hqi.aemeasurable
  have I1 := integrable_countAbove hS s
  have I2 := integrable_countAbove hqSq s
  have I3 : Integrable (fun ω => (1 - q ω).trace) μ :=
    wkt_integrable_trace ((matrixMemLp_const 1 1).sub hqi)
  unfold ncDistribution matrixTrace
  rw [← integral_const_mul, ← integral_add I2 (I3.const_mul 2)]
  refine integral_mono I1 (I2.add (I3.const_mul 2)) fun ω => ?_
  have hP : (1 - q ω) * (1 - q ω) = 1 - q ω := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq, sub_self, sub_zero]
  have hc := countAbove_le_countAbove_compress (S ω) (q ω) s
  rw [← rank_eq_trace hP]
  exact_mod_cast hc

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
positive semidefinite `x`: `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 26 τ (x)`.

With `q = q_{N+1}` at level `λ`: `λ_λ (T_c x) ≤ λ_λ (q T_c x q) + 2 τ (1 − q)`
(`ncDistribution_le_compress_add`), `τ (1 − q) ≤ τ (x) / λ` (`cuculescu_trace_le`) and
`λ_λ (q T_c x q) ≤ λ^{−2} ‖W‖_{L² (τ)}² ≤ 4 λ^{−2} ‖y_N‖_{L² (τ)}² ≤ 24 τ (x) / λ` (Lemmas 3.3, 3.5
and 3.4). The source optimizes `24 α^{−1} β^{−2} + 2 (1 − α)^{−1}` over `α, β ∈ (0, 1)` to
`14√3/3 + 28`; the counting form of Lemma 3.2 used here corresponds to `α = β = 1`, whence
`24 + 2 = 26`. (The `ℱ_N`-measurability of `x` is not needed: `T_c x` only involves
`E_0 x, …, E_N x`.) -/
theorem weakType_one_one_of_posSemidef [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {N : ℕ}
    {x : Ω → Matrix n n ℝ} (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ ω, (x ω).PosSemidef) {c : ℕ → Ω → ℝ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 26 * matrixTrace μ x := by
  have hx' : ∀ᵐ ω ∂μ, (x ω).PosSemidef := ae_of_all _ hx
  have hq := fun ω => (cuculescu_isProj (fun k => matrixCondExp (ℱ k) μ x) l (N + 1) ω).1
  have hqi := (matrixMemLp_cuculescu (μ := μ) (X := fun k => matrixCondExp (ℱ k) μ x)
    (fun _ => measurable_matrixCondExp x) l (N + 1)).mono_exponent (le_top : (1 : ℝ≥0∞) ≤ ∞)
  have hT : AEMeasurable (ncTransform ℱ μ c N x) μ :=
    ((measurable_ncTransform hc x).mono (ℱ.le N) le_rfl).aemeasurable
  -- Step 1 (Lemma 3.2, counting form) and Cuculescu's estimate `λ τ (1 − q) ≤ τ (x)`.
  have h1 := ncDistribution_le_compress_add hq hqi hT l
  have h2 := cuculescu_trace_le (ℱ := ℱ) hxi hx' l N
  -- Steps 2–4: Lemmas 3.3, 3.5 and 3.4, with `β = 1`.
  have h3 := ncDistribution_compress_transform_le (N := N) hxi hx' hc hc1 hl one_pos
  rw [one_mul] at h3
  have h4 := matrixTrace_compressedTransform_sq_le (N := N) hxi hx' hc hc1 hl.le
  have h5 := matrixTrace_compressedMart_sq_le (ℱ := ℱ) hxi hx' hl.le N
  have hl2 : 0 ≤ l⁻¹ ^ 2 := by positivity
  have h6 : l * ncDistribution μ l
      (fun ω => cuculescu (fun k => matrixCondExp (ℱ k) μ x) l (N + 1) ω *
        ncTransform ℱ μ c N x ω * cuculescu (fun k => matrixCondExp (ℱ k) μ x) l (N + 1) ω) ≤
      24 * matrixTrace μ x := by
    calc _ ≤ l * (l⁻¹ ^ 2 * (4 * (6 * l * matrixTrace μ x))) := by
          refine mul_le_mul_of_nonneg_left (h3.trans ?_) hl.le
          exact mul_le_mul_of_nonneg_left (h4.trans (by linarith)) hl2
      _ = 24 * matrixTrace μ x := by
          field_simp
          ring
  have h7 := mul_le_mul_of_nonneg_left h1 hl.le
  linarith

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
symmetric `x`: `λ τ (1_{(λ, ∞)} (|T_c x|)) ≤ 52 ‖x‖_{L¹ (τ)}`.

From the positive case by the Krickeberg decomposition `x = x⁺ − x⁻` (Randrianantoanina,
Theorem 2.3, trivial in finite time), with `‖x‖_{L¹ (τ)} = τ (x⁺) + τ (x⁻)` and
`λ_λ (T_c x) ≤ λ_{λ/2} (T_c x⁺) + λ_{λ/2} (T_c x⁻)`: the constant is `52`, twice the constant `26`
of `weakType_one_one_of_posSemidef` (the source's constant is `14√3/3 + 28`). -/
theorem weakType_one_one [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {N : ℕ}
    {x : Ω → Matrix n n ℝ} (hxm : Measurable[ℱ N] x) (hxi : MatrixMemLp x 1 μ)
    (hx : ∀ ω, (x ω).IsHermitian) {c : ℕ → Ω → ℝ} (hc : ∀ k, StronglyMeasurable[ℱ k] (c k))
    (hc1 : ∀ k ω, |c k ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    l * ncDistribution μ l (ncTransform ℱ μ c N x) ≤ 52 * ∫ ω, schattenNorm 1 (x ω) ∂μ := by
  -- The Krickeberg decomposition `x = x⁺ − x⁻`: both parts are `ℱ_N`-measurable and in `L¹`.
  have hpm : Measurable[ℱ N] (fun ω => posPart (x ω)) :=
    (measurable_cfc_of_continuous (continuous_id.max continuous_const)).comp hxm
  have hnm : Measurable[ℱ N] (fun ω => negPart (x ω)) :=
    (measurable_cfc_of_continuous (continuous_neg.max continuous_const)).comp hxm
  have hS1 := hxi.memLp_schattenNorm (q := 1) le_rfl
  have hpi : MatrixMemLp (fun ω => posPart (x ω)) 1 μ :=
    matrixMemLp_of_memLp_schattenNorm (hpm.mono (ℱ.le N) le_rfl).aemeasurable one_ne_zero
      (hS1.of_le ((measurable_schattenNorm 1).comp (hpm.mono (ℱ.le N) le_rfl)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _),
            Real.norm_of_nonneg (schattenNorm_nonneg _ _)]
          exact schattenNorm_one_posPart_le (hx ω)))
  have hni : MatrixMemLp (fun ω => negPart (x ω)) 1 μ :=
    matrixMemLp_of_memLp_schattenNorm (hnm.mono (ℱ.le N) le_rfl).aemeasurable one_ne_zero
      (hS1.of_le ((measurable_schattenNorm 1).comp (hnm.mono (ℱ.le N) le_rfl)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (schattenNorm_nonneg _ _),
            Real.norm_of_nonneg (schattenNorm_nonneg _ _)]
          exact schattenNorm_one_negPart_le (hx ω)))
  -- `T_c x = T_c x⁺ + (−T_c x⁻)` almost everywhere.
  have hxpm : x = (fun ω => posPart (x ω)) - fun ω => negPart (x ω) :=
    funext fun ω => (posPart_sub_negPart (hx ω)).symm
  have hT : ncTransform ℱ μ c N x =ᵐ[μ] ncTransform ℱ μ c N (fun ω => posPart (x ω)) +
      fun ω => -ncTransform ℱ μ c N (fun ω => negPart (x ω)) ω := by
    have h := ncTransform_sub (ℱ := ℱ) (c := c) (N := N) hpi hni
    rw [← hxpm] at h
    filter_upwards [h] with ω h
    rw [h, Pi.sub_apply, Pi.add_apply, sub_eq_add_neg]
  have hTp : AEMeasurable (ncTransform ℱ μ c N (fun ω => posPart (x ω))) μ :=
    ((measurable_ncTransform hc _).mono (ℱ.le N) le_rfl).aemeasurable
  have hTn : AEMeasurable (fun ω => -ncTransform ℱ μ c N (fun ω => negPart (x ω)) ω) μ :=
    ((measurable_ncTransform hc _).mono (ℱ.le N) le_rfl).aemeasurable.neg
  have hd := ncDistribution_add_add_le hTp hTn (l / 2) (l / 2)
  rw [add_halves, ← ncDistribution_congr_ae hT, ncDistribution_neg] at hd
  have hp := weakType_one_one_of_posSemidef (N := N) hpi (fun ω => posSemidef_posPart _) hc hc1
    (half_pos hl)
  have hm := weakType_one_one_of_posSemidef (N := N) hni (fun ω => posSemidef_negPart _) hc hc1
    (half_pos hl)
  -- `‖x‖_{L¹ (τ)} = τ (x⁺) + τ (x⁻)`.
  have hnorm : ∫ ω, schattenNorm 1 (x ω) ∂μ =
      matrixTrace μ (fun ω => posPart (x ω)) + matrixTrace μ (fun ω => negPart (x ω)) := by
    unfold matrixTrace
    rw [← integral_add (wkt_integrable_trace hpi) (wkt_integrable_trace hni)]
    congr 1
    funext ω
    exact schattenNorm_one_eq_trace_posPart_add (hx ω)
  rw [hnorm]
  have := mul_le_mul_of_nonneg_left hd hl.le
  linarith

end Main

end BanachProbability
