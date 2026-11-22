module

public import BanachProbability.Noncommutative.Cuculescu
public import BanachProbability.Noncommutative.Distribution

/-!
# Weak type `(1, 1)` of martingale transforms on the matrix cube

Randrianantoanina's theorem (N. Randrianantoanina, *Non-commutative martingale transforms*,
J. Funct. Anal. 194 (2002), Theorem 3.1, with the constant `14√3/3 + 28`), restricted to the
matrix cube `ℓ^∞ (Ω_N) ⊗ M_n (ℝ)` and to scalar predictable signs (which are central, hence
satisfy the commutation hypothesis of the theorem): there is an absolute constant `C` with
`λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C ‖x‖_{L¹ (τ)}` for every symmetric-matrix-valued `x`, every
`λ > 0` and every family of predictable signs `σ` (`weakType_one_one`).

The proof follows the source:

* the Krickeberg decomposition (Randrianantoanina, Theorem 2.3), which is trivial in finite time:
  `x = x⁺ − x⁻` pointwise (`posPart`, `negPart`), each part positive semidefinite, with
  `‖x⁺‖₁ + ‖x⁻‖₁ = ‖x‖₁` (`schattenNorm_one_eq_trace_posPart_add`); the distribution function is
  subadditive (`distribution_add_add_le`);
* Cuculescu's projections `q_k` at level `λ` (`cuculescu`, Proposition 2.4);
* in place of Lemma 3.2 (whose proof uses generalized singular values): for a projection `q`,
  `S − q S q` has rank at most `2 rank (1 − q)`, so
  `#{s_i (S) > s} ≤ #{s_i (q S q) > s} + 2 rank (1 − q)` (`countAbove_le_countAbove_compress`),
  and `rank (1 − q) = tr (1 − q)`, with `τ (1 − q) ≤ τ (x) / λ` for the last Cuculescu projection
  (`cuculescu_trace_le`);
* Lemma 3.3: the supermartingale property of the compressed process (`condAvg_cuculescu_le`),
  and Chebyshev's inequality in `L² (τ)` for the compressed transform
  `W = z_0 + Σ_k σ_k (z_{k+1} − z_k)` (`compressedTransform`), since `q T_σ x q = q W q`
  (`distribution_compress_transform_le`);
* Lemma 3.4: `‖y_N‖_{L² (τ)}² ≤ 6 λ τ (x)` for the martingale part `y` of the compressed process
  (`cubeTrace_compressedMart_sq_le`);
* Lemma 3.5: `‖W‖_{L² (τ)}² ≤ 4 ‖y_N‖_{L² (τ)}²` (`cubeTrace_compressedTransform_sq_le`): the
  martingale part is transformed with constant `1` in `L² (τ)`, and, the signs being scalar, the
  decreasing part gives `E σ σ' tr (a b) ≤ E tr (a b)` for positive semidefinite `a`, `b`.

The constants obtained are `26` for positive semidefinite `x` (`weakType_one_one_of_posSemidef`)
and `52` in general (`weakType_one_one`), instead of the source's `14√3/3 + 28`: the counting form
of Lemma 3.2 corresponds to the source's parameters `α = β = 1` in
`24 α^{−1} β^{−2} + 2 (1 − α)^{−1}`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

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

section Compressed

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The transform of the compressed process by the signs `σ`,
`W = z_0 + Σ_k σ_k (z_{k+1} − z_k)` with `z_k = q_{k+1} x_k q_{k+1}`
(Randrianantoanina's `q₁ x₁ q₁ + Σ_k ξ_{k−1} (q_k x_k q_k − q_{k−1} x_{k−1} q_{k−1})`). -/
noncomputable def compressedTransform (σ : Fin N → (Fin N → Bool) → ℝ)
    (x : (Fin N → Bool) → Matrix n n ℝ) (l : ℝ) (ε : Fin N → Bool) : Matrix n n ℝ :=
  compressed x l 0 ε +
    ∑ k : Fin N, σ k ε • (compressed x l (k.val + 1) ε - compressed x l k.val ε)

/-! ### Orthogonality of martingale differences against predictable multipliers -/

omit [Fintype n] [DecidableEq n] in
private theorem condAvg_sub_fun (k : ℕ) (f g : (Fin N → Bool) → Matrix n n ℝ) :
    condAvg k (fun ε => f ε - g ε) = fun ε => condAvg k f ε - condAvg k g ε := by
  funext ε
  simp only [condAvg, Finset.sum_sub_distrib, smul_sub]

omit [Fintype n] [DecidableEq n] in
/-- `E_k f` is a function of the first `k` signs. -/
private theorem condAvg_congr (k : ℕ) (f : (Fin N → Bool) → Matrix n n ℝ) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) : condAvg k f ε = condAvg k f ε' := by
  simp only [condAvg]
  congr 1
  refine Finset.sum_congr rfl fun η _ => congrArg f (funext fun j => ?_)
  simp only [splice]
  split_ifs with hj
  · exact h j hj
  · rfl

omit [Fintype n] [DecidableEq n] in
/-- `E_N f = f`. -/
private theorem condAvg_self (f : (Fin N → Bool) → Matrix n n ℝ) : condAvg N f = f :=
  condAvg_of_isAdapted fun _ _ h => congrArg f (funext fun j => h j j.isLt)

omit [DecidableEq n] in
/-- `τ (a d_k M) = 0` for `a` a function of the first `k` signs: `τ (a d_k M) = τ (E_k (a d_k M))
= τ (a E_k (d_k M))` and `E_k (d_k M) = 0`. -/
private theorem cubeTrace_mul_mdiff {k : ℕ} {a : (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → a ε = a ε')
    (M : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => a ε * mdiff k M ε) = 0 := by
  classical
  have h1 := condAvg_mul_mul (k := k) ha (b := fun _ => 1) (fun _ _ _ => rfl) (mdiff k M)
  simp only [mul_one] at h1
  have h2 : condAvg k (mdiff k M) = 0 := by
    unfold mdiff
    rw [condAvg_sub_fun, condAvg_condAvg (Nat.le_succ k), condAvg_condAvg le_rfl]
    funext ε
    simp
  rw [← cubeTrace_condAvg k, h1, h2]
  simp [cubeTrace]

omit [DecidableEq n] in
private theorem cubeTrace_sum_mul_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (X : ι → (Fin N → Bool) → Matrix n n ℝ) (Y : κ → (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => (∑ i ∈ s, X i ε) * ∑ j ∈ t, Y j ε) =
      ∑ i ∈ s, ∑ j ∈ t, cubeTrace (fun ε => X i ε * Y j ε) := by
  simp only [cubeTrace, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, avg_sum]
  exact Finset.sum_comm

omit [DecidableEq n] in
private theorem cubeTrace_mul_comm (A B : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => A ε * B ε) = cubeTrace (fun ε => B ε * A ε) := by
  unfold cubeTrace
  congr 1
  funext ε
  exact Matrix.trace_mul_comm _ _

omit [DecidableEq n] in
/-- The pieces `E_0 M`, `c_k d_k M` of a transform are orthogonal for `τ (a b)`. -/
private theorem cubeTrace_transform_piece_mul_eq_zero {c : Fin N → (Fin N → Bool) → ℝ}
    (hc : IsPredictable c) (M : (Fin N → Bool) → Matrix n n ℝ) {i j : Option (Fin N)}
    (hij : i ≠ j) :
    cubeTrace (fun ε => Option.elim i (condAvg 0 M ε) (fun k => c k ε • mdiff k M ε) *
      Option.elim j (condAvg 0 M ε) (fun k => c k ε • mdiff k M ε)) = 0 := by
  -- `τ (E_0 M · c_k d_k M) = 0`
  have h0 : ∀ k : Fin N, cubeTrace (fun ε => condAvg 0 M ε * (c k ε • mdiff k M ε)) = 0 := by
    intro k
    calc cubeTrace (fun ε => condAvg 0 M ε * (c k ε • mdiff k M ε))
        = cubeTrace (fun ε => (c k ε • condAvg 0 M ε) * mdiff k M ε) := by
          congr 1
          funext ε
          rw [mul_smul_comm, smul_mul_assoc]
      _ = 0 := cubeTrace_mul_mdiff (fun ε ε' h => by
          rw [hc k ε ε' (fun j hj => h j hj), condAvg_congr 0 M (fun j hj => absurd hj (by omega))])
          M
  -- `τ (c_j d_j M · c_k d_k M) = 0` for `j < k`
  have h1 : ∀ j k : Fin N, j < k →
      cubeTrace (fun ε => (c j ε • mdiff j M ε) * (c k ε • mdiff k M ε)) = 0 := by
    intro j k hjk
    have hjk' : j.val + 1 ≤ k.val := hjk
    calc cubeTrace (fun ε => (c j ε • mdiff j M ε) * (c k ε • mdiff k M ε))
        = cubeTrace (fun ε => ((c j ε * c k ε) • mdiff j M ε) * mdiff k M ε) := by
          congr 1
          funext ε
          rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_mul_assoc]
      _ = 0 := cubeTrace_mul_mdiff (fun ε ε' h => by
          have hj : ∀ i : Fin N, i.val < j.val + 1 → ε i = ε' i := fun i hi => h i (by omega)
          have hj' : ∀ i : Fin N, i.val < j.val → ε i = ε' i := fun i hi => h i (by omega)
          simp only [mdiff]
          rw [hc j ε ε' (fun i hi => hj' i hi), hc k ε ε' (fun i hi => h i hi),
            condAvg_congr _ M hj, condAvg_congr _ M hj']) M
  rcases i with _ | i <;> rcases j with _ | j
  · exact absurd rfl hij
  · exact h0 j
  · rw [cubeTrace_mul_comm]
    exact h0 i
  · have hij' : i ≠ j := fun h => hij (by rw [h])
    rcases lt_or_gt_of_ne hij' with h | h
    · exact h1 i j h
    · rw [cubeTrace_mul_comm]
      exact h1 j i h

omit [DecidableEq n] in
/-- `τ ((T_c M)²) = τ ((E_0 M)²) + Σ_k τ ((c_k d_k M)²)` for predictable scalar multipliers. -/
private theorem cubeTrace_transform_mul_self {c : Fin N → (Fin N → Bool) → ℝ}
    (hc : IsPredictable c) (M : (Fin N → Bool) → Matrix n n ℝ) :
    cubeTrace (fun ε => transform c M ε * transform c M ε) =
      cubeTrace (fun ε => condAvg 0 M ε * condAvg 0 M ε) +
        ∑ k : Fin N, cubeTrace (fun ε => (c k ε • mdiff k M ε) * (c k ε • mdiff k M ε)) := by
  set X : Option (Fin N) → (Fin N → Bool) → Matrix n n ℝ :=
    fun i ε => Option.elim i (condAvg 0 M ε) (fun k => c k ε • mdiff k M ε) with hX
  have hT : ∀ ε, transform c M ε = ∑ i, X i ε := by
    intro ε
    rw [Fintype.sum_option]
    rfl
  simp only [hT]
  rw [cubeTrace_sum_mul_sum]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hji => cubeTrace_transform_piece_mul_eq_zero hc M (Ne.symm hji)]
  rw [Fintype.sum_option]
  rfl

omit [Fintype n] [DecidableEq n] in
/-- `T_1 M = E_N M = M`. -/
private theorem transform_one (M : (Fin N → Bool) → Matrix n n ℝ) :
    transform (fun _ _ => (1 : ℝ)) M = M := by
  funext ε
  simp only [transform, one_smul]
  rw [Fin.sum_univ_eq_sum_range (fun k => condAvg (k + 1) M ε - condAvg k M ε) N,
    Finset.sum_range_sub (fun k => condAvg k M ε) N, add_sub_cancel, condAvg_self]

omit [DecidableEq n] in
/-- **III** of Randrianantoanina's proof of Lemma 3.5: martingale transforms by predictable scalar
multipliers with `|c_k| ≤ 1` are contractions of `L² (τ)`. -/
private theorem cubeTrace_transform_mul_self_le {c : Fin N → (Fin N → Bool) → ℝ}
    (hc : IsPredictable c) (hc1 : ∀ k ε, |c k ε| ≤ 1) {M : (Fin N → Bool) → Matrix n n ℝ}
    (hM : ∀ ε, (M ε).IsHermitian) :
    cubeTrace (fun ε => transform c M ε * transform c M ε) ≤ cubeTrace (fun ε => M ε * M ε) := by
  have h1 := cubeTrace_transform_mul_self (c := fun _ _ => (1 : ℝ)) (fun _ _ _ _ => rfl) M
  rw [transform_one] at h1
  simp only [one_smul] at h1
  rw [h1, cubeTrace_transform_mul_self hc]
  gcongr with k
  refine avg_mono fun ε => ?_
  have hd : (mdiff k M ε).IsHermitian :=
    (isHermitian_condAvg hM _ ε).sub (isHermitian_condAvg hM _ ε)
  have h0 := trace_mul_self_nonneg hd
  have hc2 : c k ε * c k ε ≤ 1 := by
    have := hc1 k ε
    nlinarith [abs_nonneg (c k ε), sq_abs (c k ε)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul]
  nlinarith

omit [DecidableEq n] in
/-- **IV** of Randrianantoanina's proof of Lemma 3.5, for scalar multipliers with `|c_k| ≤ 1`:
`τ ((Σ c_k a_k)²) = Σ_{j,k} E (c_j c_k tr (a_j a_k)) ≤ Σ_{j,k} τ (a_j a_k) = τ ((Σ a_k)²)`, since
`tr (a_j a_k) ≥ 0` for positive semidefinite `a_j`, `a_k`. -/
private theorem cubeTrace_sum_smul_mul_self_le {c : Fin N → (Fin N → Bool) → ℝ}
    (hc1 : ∀ k ε, |c k ε| ≤ 1) {a : Fin N → (Fin N → Bool) → Matrix n n ℝ}
    (ha : ∀ k ε, (a k ε).PosSemidef) :
    cubeTrace (fun ε => (∑ k, c k ε • a k ε) * ∑ k, c k ε • a k ε) ≤
      cubeTrace (fun ε => (∑ k, a k ε) * ∑ k, a k ε) := by
  rw [cubeTrace_sum_mul_sum, cubeTrace_sum_mul_sum]
  gcongr with j _ k _
  refine avg_mono fun ε => ?_
  have h0 := trace_mul_nonneg_of_posSemidef (ha j ε) (ha k ε)
  have hjk : c j ε * c k ε ≤ 1 := by
    have h := abs_mul (c j ε) (c k ε)
    have := mul_le_mul (hc1 j ε) (hc1 k ε) (abs_nonneg _) zero_le_one
    linarith [le_abs_self (c j ε * c k ε)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul]
  nlinarith

/-! ### Cuculescu projections and the compressed process -/

section Cuculescu

variable {x : (Fin N → Bool) → Matrix n n ℝ} {l : ℝ}

/-- The Cuculescu projections decrease: `q_{j+d} q_j = q_{j+d}`. -/
private theorem cuculescu_add_mul (hx : ∀ ε, (x ε).PosSemidef) (j d : ℕ) (ε : Fin N → Bool) :
    cuculescu x l (j + d) ε * cuculescu x l j ε = cuculescu x l (j + d) ε := by
  induction d with
  | zero => exact (cuculescu_isProj hx j ε).1
  | succ d ih =>
    calc cuculescu x l (j + (d + 1)) ε * cuculescu x l j ε
        = cuculescu x l (j + d + 1) ε * cuculescu x l (j + d) ε * cuculescu x l j ε := by
          rw [cuculescu_succ_mul hx]
          rfl
      _ = cuculescu x l (j + d + 1) ε * cuculescu x l (j + d) ε := by rw [mul_assoc, ih]
      _ = cuculescu x l (j + (d + 1)) ε := cuculescu_succ_mul hx _ ε

/-- `q_j q_{j+d} = q_{j+d}` (the transpose of `cuculescu_add_mul`). -/
private theorem mul_cuculescu_add (hx : ∀ ε, (x ε).PosSemidef) (j d : ℕ) (ε : Fin N → Bool) :
    cuculescu x l j ε * cuculescu x l (j + d) ε = cuculescu x l (j + d) ε := by
  have h := congrArg Matrix.transpose (cuculescu_add_mul (l := l) hx j d ε)
  rwa [Matrix.transpose_mul, (cuculescu_isProj hx (j + d) ε).2, (cuculescu_isProj hx j ε).2] at h

/-- The compressed process is positive semidefinite: `z_k = q_{k+1}ᵀ x_k q_{k+1}`. -/
private theorem posSemidef_compressed (hx : ∀ ε, (x ε).PosSemidef) (k : ℕ) (ε : Fin N → Bool) :
    (compressed x l k ε).PosSemidef := by
  have h := (posSemidef_condAvg hx k ε).conjTranspose_mul_mul_same (cuculescu x l (k + 1) ε)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, (cuculescu_isProj hx (k + 1) ε).2] at h

/-- `q z_k q = q x_k q` for `q = q_{N+1}` and `k ≤ N`, since `q ⪯ q_{k+1}`. -/
private theorem compress_compressed (hx : ∀ ε, (x ε).PosSemidef) {k : ℕ} (hk : k ≤ N)
    (ε : Fin N → Bool) :
    cuculescu x l (N + 1) ε * compressed x l k ε * cuculescu x l (N + 1) ε =
      cuculescu x l (N + 1) ε * condAvg k x ε * cuculescu x l (N + 1) ε := by
  obtain ⟨d, hd⟩ : ∃ d, N + 1 = k + 1 + d := ⟨N - k, by omega⟩
  rw [compressed, hd]
  have h1 := cuculescu_add_mul (l := l) hx (k + 1) d ε
  have h2 := mul_cuculescu_add (l := l) hx (k + 1) d ε
  calc cuculescu x l (k + 1 + d) ε *
        (cuculescu x l (k + 1) ε * condAvg k x ε * cuculescu x l (k + 1) ε) *
          cuculescu x l (k + 1 + d) ε
      = (cuculescu x l (k + 1 + d) ε * cuculescu x l (k + 1) ε) * condAvg k x ε *
          (cuculescu x l (k + 1) ε * cuculescu x l (k + 1 + d) ε) := by
        simp only [mul_assoc]
    _ = _ := by rw [h1, h2]

omit [DecidableEq n] in
private theorem conj_add_sum (Q A : Matrix n n ℝ) (c : Fin N → ℝ) (B C : Fin N → Matrix n n ℝ) :
    Q * (A + ∑ k, c k • (B k - C k)) * Q =
      Q * A * Q + ∑ k, c k • (Q * B k * Q - Q * C k * Q) := by
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul]

/-- `q (T_σ x) q = q W q` for `q = q_{N+1}` (Randrianantoanina, proof of Lemma 3.3; the signs are
scalars, so they commute with the projections). -/
private theorem compress_transform_eq (hx : ∀ ε, (x ε).PosSemidef)
    (σ : Fin N → (Fin N → Bool) → ℝ) (ε : Fin N → Bool) :
    cuculescu x l (N + 1) ε * transform σ x ε * cuculescu x l (N + 1) ε =
      cuculescu x l (N + 1) ε * compressedTransform σ x l ε * cuculescu x l (N + 1) ε := by
  simp only [transform, compressedTransform]
  rw [conj_add_sum, conj_add_sum, compress_compressed hx (Nat.zero_le N)]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [compress_compressed hx k.isLt, compress_compressed hx k.isLt.le]

/-- The compressed transform is symmetric. -/
private theorem isHermitian_compressedTransform (hx : ∀ ε, (x ε).PosSemidef)
    (σ : Fin N → (Fin N → Bool) → ℝ) (ε : Fin N → Bool) :
    (compressedTransform σ x l ε).IsHermitian := by
  have hz : ∀ k, (compressed x l k ε).IsHermitian := fun k =>
    (posSemidef_compressed hx k ε).isHermitian
  refine (hz 0).add (Finset.sum_induction _ Matrix.IsHermitian (fun _ _ ha hb => ha.add hb)
    Matrix.isHermitian_zero fun k _ => ?_)
  exact ((hz _).sub (hz _)).smul (IsSelfAdjoint.all _)

end Cuculescu

/-- **Randrianantoanina, Lemma 3.3** (second part): with `q` the last Cuculescu projection,
`τ (1_{(βλ, ∞)} (|q T_σ x q|)) ≤ (βλ)^{−2} ‖W‖_{L² (τ)}²`. -/
theorem distribution_compress_transform_le {x : (Fin N → Bool) → Matrix n n ℝ}
    (hx : ∀ ε, (x ε).PosSemidef) {l β : ℝ} (hl : 0 < l) (hβ : 0 < β)
    (σ : Fin N → (Fin N → Bool) → ℝ) :
    distribution (β * l)
        (fun ε => cuculescu x l (N + 1) ε * transform σ x ε * cuculescu x l (N + 1) ε) ≤
      (β * l)⁻¹ ^ 2 *
        cubeTrace (fun ε => compressedTransform σ x l ε * compressedTransform σ x l ε) := by
  -- Chebyshev's inequality in `L² (τ)`, `q T_σ x q = q W q` and `‖q W q‖_{S_2} ≤ ‖W‖_{S_2}`.
  have hs : 0 < β * l := mul_pos hβ hl
  have h := distribution_mul_rpow_le hs two_pos
    (fun ε => cuculescu x l (N + 1) ε * transform σ x ε * cuculescu x l (N + 1) ε)
  rw [ENNReal.ofReal_ofNat, Real.rpow_two] at h
  have h2 : (avg fun ε => schattenNorm 2
      (cuculescu x l (N + 1) ε * transform σ x ε * cuculescu x l (N + 1) ε) ^ (2 : ℝ)) ≤
      cubeTrace (fun ε => compressedTransform σ x l ε * compressedTransform σ x l ε) := by
    refine avg_mono fun ε => ?_
    have hW := transpose_eq_of_isHermitian (isHermitian_compressedTransform (l := l) hx σ ε)
    have hq := cuculescu_isProj (l := l) hx (N + 1) ε
    rw [Real.rpow_two, schattenNorm_two_sq, ← trace_transpose_mul_self, compress_transform_eq hx]
    calc _ ≤ ((compressedTransform σ x l ε)ᵀ * compressedTransform σ x l ε).trace :=
          trace_transpose_mul_self_compress_le hq.1 hq.2 _
      _ = _ := by rw [hW]
  have h3 := h.trans h2
  rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact h3

-- `hl` is not used: the inputs from Cuculescu's construction hold at every level.
set_option linter.unusedVariables false in
/-- **Randrianantoanina, Lemma 3.5**: `‖W‖_{L² (τ)}² ≤ 4 ‖y_N‖_{L² (τ)}²` for predictable scalar
multipliers with `|σ_k| ≤ 1`. -/
theorem cubeTrace_compressedTransform_sq_le {x : (Fin N → Bool) → Matrix n n ℝ}
    (hx : ∀ ε, (x ε).PosSemidef) {l : ℝ} (hl : 0 < l) {σ : Fin N → (Fin N → Bool) → ℝ}
    (hσ : IsPredictable σ) (hσ1 : ∀ k ε, |σ k ε| ≤ 1) :
    cubeTrace (fun ε => compressedTransform σ x l ε * compressedTransform σ x l ε) ≤
      4 * cubeTrace (fun ε => compressedMart x l N ε * compressedMart x l N ε) := by
  -- The decreasing part of the Doob decomposition, `a_k = z_k − E_k z_{k+1} ⪰ 0`.
  set a : ℕ → (Fin N → Bool) → Matrix n n ℝ :=
    fun k ε => compressed x l k ε - condAvg k (compressed x l (k + 1)) ε with ha_def
  have ha : ∀ k ε, (a k ε).PosSemidef := fun k ε => condAvg_cuculescu_le hx k ε
  -- The martingale part: `E_j y_N = y_j` for `j ≤ N`, `y_0 = z_0`,
  -- `y_{k+1} − y_k = z_{k+1} − E_k z_{k+1}` and `y_K − z_K = Σ_{j<K} a_j`.
  have hM := isCubeMartingale_compressedMart (l := l) hx
  have hmart : ∀ j d, condAvg j (compressedMart x l (j + d)) = compressedMart x l j := by
    intro j d
    induction d with
    | zero => exact condAvg_of_isAdapted (hM.1 j)
    | succ d ih => rw [← Nat.add_assoc, ← condAvg_condAvg (Nat.le_add_right j d), hM.2, ih]
  have hmartN : ∀ j, j ≤ N → ∀ ε,
      condAvg j (compressedMart x l N) ε = compressedMart x l j ε := by
    intro j hj ε
    have h := hmart j (N - j)
    rw [Nat.add_sub_cancel' hj] at h
    rw [h]
  have hy0 : ∀ ε, compressedMart x l 0 ε = compressed x l 0 ε := fun ε => by
    simp [compressedMart]
  have hdy : ∀ (k : ℕ) ε, compressedMart x l (k + 1) ε - compressedMart x l k ε =
      compressed x l (k + 1) ε - condAvg k (compressed x l (k + 1)) ε := fun k ε => by
    simp only [compressedMart, Finset.sum_range_succ]
    abel
  have hyz : ∀ (K : ℕ) ε, compressedMart x l K ε - compressed x l K ε =
      ∑ j ∈ Finset.range K, a j ε := by
    intro K ε
    induction K with
    | zero => simp [compressedMart]
    | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [compressedMart, Finset.sum_range_succ, ha_def]
      abel
  have hyN : ∀ ε, (compressedMart x l N ε).PosSemidef := fun ε => by
    have h := (posSemidef_compressedMart_sub (l := l) hx N ε).add
      (posSemidef_compressed (l := l) hx N ε)
    rwa [sub_add_cancel] at h
  -- `W = T_σ y_N − Σ_k σ_k a_k`.
  have hW : ∀ ε, compressedTransform σ x l ε =
      transform σ (compressedMart x l N) ε - ∑ k : Fin N, σ k ε • a k ε := by
    intro ε
    simp only [compressedTransform, transform]
    rw [hmartN 0 (Nat.zero_le N) ε, hy0, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmartN _ k.isLt ε, hmartN _ k.isLt.le ε, hdy, ← smul_sub]
    congr 1
    simp only [ha_def]
    abel
  have hU : ∀ ε, (transform σ (compressedMart x l N) ε).IsHermitian :=
    isHermitian_transform (fun ε => (hyN ε).isHermitian) σ
  have hV : ∀ ε, (∑ k : Fin N, σ k ε • a k ε).IsHermitian := fun ε =>
    Finset.sum_induction _ Matrix.IsHermitian (fun _ _ hA hB => hA.add hB)
      Matrix.isHermitian_zero fun k _ => (ha k ε).isHermitian.smul (IsSelfAdjoint.all _)
  -- `τ (W²) ≤ 2 τ ((T_σ y_N)²) + 2 τ ((Σ σ_k a_k)²)`.
  have h1 : cubeTrace (fun ε => compressedTransform σ x l ε * compressedTransform σ x l ε) ≤
      2 * cubeTrace (fun ε => transform σ (compressedMart x l N) ε *
        transform σ (compressedMart x l N) ε) +
      2 * cubeTrace (fun ε => (∑ k : Fin N, σ k ε • a k ε) * ∑ k : Fin N, σ k ε • a k ε) := by
    simp only [hW]
    unfold cubeTrace
    rw [← avg_const_mul, ← avg_const_mul, ← avg_add]
    exact avg_mono fun ε => trace_sub_mul_self_le (hU ε) (hV ε)
  -- III: `τ ((T_σ y_N)²) ≤ τ (y_N²)`.
  have h2 := cubeTrace_transform_mul_self_le hσ hσ1 (fun ε => (hyN ε).isHermitian)
  -- IV: `τ ((Σ σ_k a_k)²) ≤ τ ((Σ a_k)²)`.
  have h3 := cubeTrace_sum_smul_mul_self_le hσ1 (a := fun k : Fin N => a k) (fun k ε => ha k ε)
  -- `Σ_k a_k = y_N − z_N` and `0 ⪯ y_N − z_N ⪯ y_N`, so `τ ((Σ a_k)²) ≤ τ (y_N²)`.
  have h4 : cubeTrace (fun ε => (∑ k : Fin N, a k ε) * ∑ k : Fin N, a k ε) ≤
      cubeTrace (fun ε => compressedMart x l N ε * compressedMart x l N ε) := by
    refine avg_mono fun ε => ?_
    have hB : ∑ k : Fin N, a k ε = compressedMart x l N ε - compressed x l N ε := by
      rw [Fin.sum_univ_eq_sum_range (fun j => a j ε) N, hyz]
    dsimp only
    rw [hB]
    refine trace_mul_self_le_of_le (posSemidef_compressedMart_sub hx N ε) ?_
    rw [sub_sub_cancel]
    exact posSemidef_compressed hx N ε
  linarith

end Compressed

section Assembly

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Step 1 of the proof of Theorem 3.1 in the counting form (replacing Lemma 3.2):
`λ_l (S) ≤ λ_l (q S q) + 2 τ (1 − q)` for `q = q_{N+1}`, since `rank (1 − q) = tr (1 − q)`. -/
private theorem distribution_le_compress_add {x : (Fin N → Bool) → Matrix n n ℝ}
    (hx : ∀ ε, (x ε).PosSemidef) (l : ℝ) (S : (Fin N → Bool) → Matrix n n ℝ) :
    distribution l S ≤
      distribution l (fun ε => cuculescu x l (N + 1) ε * S ε * cuculescu x l (N + 1) ε) +
        2 * cubeTrace (fun ε => 1 - cuculescu x l (N + 1) ε) := by
  unfold distribution cubeTrace
  rw [← avg_const_mul, ← avg_add]
  refine avg_mono fun ε => ?_
  have hq := (cuculescu_isProj (l := l) hx (N + 1) ε).1
  have hP : (1 - cuculescu x l (N + 1) ε) * (1 - cuculescu x l (N + 1) ε) =
      1 - cuculescu x l (N + 1) ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq, sub_self, sub_zero]
  have hc := countAbove_le_countAbove_compress (S ε) (cuculescu x l (N + 1) ε) l
  rw [← rank_eq_trace hP]
  exact_mod_cast hc

omit [Fintype n] [DecidableEq n] in
private theorem transform_sub (σ : Fin N → (Fin N → Bool) → ℝ)
    (f g : (Fin N → Bool) → Matrix n n ℝ) (ε : Fin N → Bool) :
    transform σ (fun ε => f ε - g ε) ε = transform σ f ε - transform σ g ε := by
  simp only [transform, condAvg_sub_fun, smul_sub, Finset.sum_sub_distrib]
  abel

private theorem distribution_neg (s : ℝ) (X : (Fin N → Bool) → Matrix n n ℝ) :
    distribution s (fun ε => -X ε) = distribution s X := by
  unfold distribution
  simp only [countAbove_neg]

end Assembly

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1), for
positive semidefinite matrix-valued functions on the cube: there is an absolute `C` with
`λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C τ (x)`.

The proof gives `C = 26`: with `q = q_{N+1}` at level `λ`,
`λ_λ (T_σ x) ≤ λ_λ (q T_σ x q) + 2 τ (1 − q)` (`countAbove_le_countAbove_compress`),
`τ (1 − q) ≤ τ (x) / λ` (`cuculescu_trace_le`) and
`λ_λ (q T_σ x q) ≤ λ^{−2} ‖W‖_{L² (τ)}² ≤ 4 λ^{−2} ‖y_N‖_{L² (τ)}² ≤ 24 τ (x) / λ`. The source
optimizes `24 α^{−1} β^{−2} + 2 (1 − α)^{−1}` over `α, β ∈ (0, 1)` to `14√3/3 + 28`; the
counting form of Lemma 3.2 used here corresponds to `α = β = 1`, whence `24 + 2 = 26`. -/
theorem weakType_one_one_of_posSemidef : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n] (x : (Fin N → Bool) → Matrix n n ℝ)
      (σ : Fin N → (Fin N → Bool) → ℝ), (∀ ε, (x ε).PosSemidef) → IsPredictable σ →
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ l : ℝ, 0 < l →
        l * distribution l (transform σ x) ≤ C * cubeTrace x := by
  refine ⟨26, by norm_num, fun N n _ _ x σ hx hσ hσ1 l hl => ?_⟩
  have hσ1' : ∀ k ε, |σ k ε| ≤ 1 := fun k ε => by rcases hσ1 k ε with h | h <;> simp [h]
  -- Step 1 (Lemma 3.2, counting form) and Cuculescu's estimate `λ τ (1 − q) ≤ τ (x)`.
  have h1 := distribution_le_compress_add hx l (transform σ x)
  have h2 := cuculescu_trace_le hx hl
  -- Steps 2–4: Lemmas 3.3, 3.5 and 3.4, with `β = 1`.
  have h3 := distribution_compress_transform_le hx hl one_pos σ
  rw [one_mul] at h3
  have h4 := cubeTrace_compressedTransform_sq_le hx hl hσ hσ1'
  have h5 := cubeTrace_compressedMart_sq_le hx hl
  have hl2 : 0 ≤ l⁻¹ ^ 2 := by positivity
  have h6 : l * distribution l
      (fun ε => cuculescu x l (N + 1) ε * transform σ x ε * cuculescu x l (N + 1) ε) ≤
      24 * cubeTrace x := by
    calc _ ≤ l * (l⁻¹ ^ 2 * (4 * (6 * l * cubeTrace x))) := by
          refine mul_le_mul_of_nonneg_left (h3.trans ?_) hl.le
          exact mul_le_mul_of_nonneg_left (h4.trans (by linarith)) hl2
      _ = 24 * cubeTrace x := by
          field_simp
          ring
  nlinarith

/-- **Weak type `(1, 1)` of martingale transforms** (Randrianantoanina 2002, Theorem 3.1) on the
matrix cube: there is an absolute `C` with `λ τ (1_{(λ, ∞)} (|T_σ x|)) ≤ C ‖x‖_{L¹ (τ)}` for
symmetric-matrix-valued `x`.

From the positive case by the Krickeberg decomposition `x = x⁺ − x⁻` (Randrianantoanina,
Theorem 2.3, trivial in finite time), with `‖x‖_{L¹ (τ)} = τ (x⁺) + τ (x⁻)` and
`λ_λ (T_σ x) ≤ λ_{λ/2} (T_σ x⁺) + λ_{λ/2} (T_σ x⁻)`: the proof gives `C = 52`, twice the constant
`26` of `weakType_one_one_of_posSemidef` (the source's constant is `14√3/3 + 28`). -/
theorem weakType_one_one : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n] (x : (Fin N → Bool) → Matrix n n ℝ)
      (σ : Fin N → (Fin N → Bool) → ℝ), (∀ ε, (x ε).IsHermitian) → IsPredictable σ →
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ l : ℝ, 0 < l →
        l * distribution l (transform σ x) ≤ C * avg fun ε => schattenNorm 1 (x ε) := by
  obtain ⟨C, hC, hWT⟩ := weakType_one_one_of_posSemidef
  refine ⟨2 * C, by positivity, fun N n _ _ x σ hx hσ hσ1 l hl => ?_⟩
  -- The Krickeberg decomposition `x = x⁺ − x⁻`, so `T_σ x = T_σ x⁺ + (−T_σ x⁻)`.
  have hxpm : x = fun ε => posPart (x ε) - negPart (x ε) :=
    funext fun ε => (posPart_sub_negPart (hx ε)).symm
  have hT : transform σ x = transform σ (fun ε => posPart (x ε)) +
      fun ε => -transform σ (fun ε => negPart (x ε)) ε := by
    funext ε
    calc transform σ x ε = transform σ (fun ε => posPart (x ε) - negPart (x ε)) ε := by
          rw [← hxpm]
      _ = _ := by rw [transform_sub, sub_eq_add_neg]; rfl
  have hd := distribution_add_add_le (l / 2) (l / 2) (transform σ fun ε => posPart (x ε))
    (fun ε => -transform σ (fun ε => negPart (x ε)) ε)
  rw [add_halves, ← hT, distribution_neg] at hd
  have hp := hWT N n (fun ε => posPart (x ε)) σ (fun ε => posSemidef_posPart _) hσ hσ1 (l / 2)
    (by positivity)
  have hm := hWT N n (fun ε => negPart (x ε)) σ (fun ε => posSemidef_negPart _) hσ hσ1 (l / 2)
    (by positivity)
  -- `‖x‖_{L¹ (τ)} = τ (x⁺) + τ (x⁻)`.
  have hnorm : (avg fun ε => schattenNorm 1 (x ε)) =
      cubeTrace (fun ε => posPart (x ε)) + cubeTrace (fun ε => negPart (x ε)) := by
    unfold cubeTrace
    rw [← avg_add]
    congr 1
    funext ε
    exact schattenNorm_one_eq_trace_posPart_add (hx ε)
  rw [hnorm]
  nlinarith

end BanachProbability
