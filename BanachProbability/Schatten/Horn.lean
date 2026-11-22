module

public import BanachProbability.Schatten.Dilation
public import BanachProbability.Schatten.Holder
import Mathlib.Order.Monotone.Extension

/-!
# Horn's inequality and Hölder's inequality for Schatten norms

For real matrices `A`, `B` with singular values in decreasing order,
`Π_{k < N} s_k (A B) ≤ Π_{k < N} s_k (A) s_k (B)` for every `N` (`prod_sortedSingularValue_mul_le`,
Horn's inequality), and hence **Hölder's inequality**
`‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r` (`schattenNorm_mul_le`), for all
`0 < q, r < ∞`; also `|tr A| ≤ ‖A‖_{S_1}` and `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`.

The proofs are those of Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I*
(2016), Appendix D: Lemma D.1.4 (pp. 567–568), Lemmas D.2.1–D.2.2 (p. 570), Proposition D.2.3 (p.
571), Corollary D.2.4 and Proposition D.2.5 (p. 572).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The singular values of `A` in decreasing order, `s_0 ≥ s_1 ≥ …`, extended by `0`. -/
noncomputable def sortedSingularValue (A : Matrix m n ℝ) (k : ℕ) : ℝ :=
  if h : k < Fintype.card n then
    √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ ⟨k, h⟩) else 0

omit [DecidableEq m] in
theorem sortedSingularValue_nonneg (A : Matrix m n ℝ) (k : ℕ) : 0 ≤ sortedSingularValue A k := by
  unfold sortedSingularValue
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

omit [DecidableEq m] in
theorem antitone_sortedSingularValue (A : Matrix m n ℝ) : Antitone (sortedSingularValue A) := by
  intro j k hjk
  by_cases hk : k < Fintype.card n
  · rw [sortedSingularValue, sortedSingularValue, dite_eq_left hk, dite_eq_left (hjk.trans_lt hk)]
    exact Real.sqrt_le_sqrt (Matrix.IsHermitian.eigenvalues₀_antitone _ hjk)
  · rw [sortedSingularValue, dite_eq_right hk]
    exact sortedSingularValue_nonneg A j

omit [DecidableEq m] in
/-- `s_k = 0` beyond the number of columns. -/
private theorem sortedSingularValue_eq_zero (A : Matrix m n ℝ) {k : ℕ} (hk : Fintype.card n ≤ k) :
    sortedSingularValue A k = 0 :=
  dite_eq_right (not_lt.2 hk)

omit [DecidableEq m] in
/-- The sorted singular values are the singular values, enumerated in decreasing order. -/
private theorem singularValue_eq_sortedSingularValue (A : Matrix m n ℝ)
    (i : Fin (Fintype.card n)) :
    singularValue A (Fintype.equivOfCardEq (Fintype.card_fin _) i) = sortedSingularValue A i := by
  rw [sortedSingularValue, dite_eq_left i.2, singularValue, Matrix.IsHermitian.eigenvalues,
    Equiv.symm_apply_apply]

omit [DecidableEq m] in
private theorem sum_singularValue_eq (A : Matrix m n ℝ) (F : ℝ → ℝ) :
    ∑ i, F (singularValue A i) =
      ∑ k ∈ Finset.range (Fintype.card n), F (sortedSingularValue A k) := by
  rw [Finset.sum_range, ← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).sum_comp]
  simp only [singularValue_eq_sortedSingularValue]

omit [DecidableEq m] in
/-- The Schatten norm in terms of the sorted singular values. -/
theorem schattenNorm_eq_sum_sortedSingularValue {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), sortedSingularValue A k ^ q) ^ (1 / q) := by
  rw [schattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
    sum_singularValue_eq A (· ^ q)]

omit [DecidableEq m] in
/-- (HNVW I, Lemma D.2.1) `det (Mᵀ M) = Π_k s_k (M)²`: the determinant of a symmetric matrix is the
product of its eigenvalues. -/
private theorem det_transpose_mul_self_eq_prod (M : Matrix m n ℝ) :
    (Mᵀ * M).det = ∏ k ∈ Finset.range (Fintype.card n), sortedSingularValue M k ^ 2 := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    (Matrix.isHermitian_conjTranspose_mul_self M).det_eq_prod_eigenvalues, Finset.prod_range,
    ← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← singularValue_eq_sortedSingularValue, singularValue_sq]
  rfl

/-! ### The sorted eigenbasis of `Aᵀ A` -/

/-- The orthonormal eigenvectors `e_0, e_1, …` of `Aᵀ A`, in the order of the sorted singular
values (the right singular vectors of `A`). -/
private noncomputable def sortedBasis (A : Matrix m n ℝ) :
    OrthonormalBasis (Fin (Fintype.card n)) ℝ (EuclideanSpace ℝ n) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_conjTranspose_mul_self A)).eigenvectorBasis finrank_euclideanSpace

omit [DecidableEq m] in
/-- `Aᵀ A e_k = s_k² e_k`. -/
private theorem toEuclideanLin_sortedBasis (A : Matrix m n ℝ) (k : Fin (Fintype.card n)) :
    Matrix.toEuclideanLin (Aᴴ * A) (sortedBasis A k) =
      sortedSingularValue A k ^ 2 • sortedBasis A k := by
  have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_conjTranspose_mul_self A)).apply_eigenvectorBasis finrank_euclideanSpace k
  have hs : sortedSingularValue A k ^ 2 =
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k := by
    rw [← singularValue_eq_sortedSingularValue, singularValue_sq, Matrix.IsHermitian.eigenvalues,
      Equiv.symm_apply_apply]
  rw [hs]
  exact h

omit [DecidableEq m] in
/-- `⟨A v, A w⟩ = ⟨v, Aᵀ A w⟩`. -/
private theorem inner_toEuclideanLin (A : Matrix m n ℝ) (v w : EuclideanSpace ℝ n) :
    inner ℝ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A w) =
      inner ℝ v (Matrix.toEuclideanLin (Aᴴ * A) w) := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

omit [DecidableEq m] in
/-- The vectors `A e_k` are orthogonal, with `‖A e_k‖ = s_k`. -/
private theorem inner_toEuclideanLin_sortedBasis (A : Matrix m n ℝ)
    (j k : Fin (Fintype.card n)) :
    inner ℝ (Matrix.toEuclideanLin A (sortedBasis A j))
      (Matrix.toEuclideanLin A (sortedBasis A k)) =
        if j = k then sortedSingularValue A j ^ 2 else 0 := by
  rw [inner_toEuclideanLin, toEuclideanLin_sortedBasis, real_inner_smul_right,
    (sortedBasis A).inner_eq_ite, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [h]
  · rfl

omit [DecidableEq m] in
/-- `‖A v‖² = Σ_k s_k² ⟨e_k, v⟩²`. -/
private theorem norm_toEuclideanLin_sq (A : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      ∑ k : Fin (Fintype.card n),
        sortedSingularValue A k ^ 2 * inner ℝ (sortedBasis A k) v ^ 2 := by
  conv_lhs => rw [← (sortedBasis A).sum_repr' v]
  rw [← real_inner_self_eq_norm_sq, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [inner_sum, map_smul, real_inner_smul_left, real_inner_smul_right,
    inner_toEuclideanLin_sortedBasis, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  ring

omit [DecidableEq m] in
/-- If the columns of `Q` are orthonormal, then `s_k (A Q) ≤ s_k (A)` (HNVW I, (D.3)). The proof is
the dimension count of HNVW I, Lemma D.1.1: there is a `v ≠ 0` in the span of the first `k + 1`
right singular vectors of `A Q` such that `Q v` is orthogonal to the first `k` right singular
vectors of `A`, and then `s_k (A Q) ‖v‖ ≤ ‖A Q v‖ ≤ s_k (A) ‖Q v‖ = s_k (A) ‖v‖`. -/
private theorem sortedSingularValue_mul_le_of_transpose_mul_self_eq_one {p : Type*} [Fintype p]
    [DecidableEq p] (A : Matrix m n ℝ) {Q : Matrix n p ℝ} (hQ : Qᵀ * Q = 1) (k : ℕ) :
    sortedSingularValue (A * Q) k ≤ sortedSingularValue A k := by
  rcases le_or_gt (Fintype.card p) k with hk | hk
  · rw [sortedSingularValue_eq_zero _ hk]
    exact sortedSingularValue_nonneg _ _
  have hQv : ∀ v : EuclideanSpace ℝ p, ‖Matrix.toEuclideanLin Q v‖ ^ 2 = ‖v‖ ^ 2 := fun v => by
    rw [← real_inner_self_eq_norm_sq, inner_toEuclideanLin,
      Matrix.conjTranspose_eq_transpose_of_trivial, hQ, Matrix.toLpLin_one, LinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  -- the `card p - 1` linear conditions on `v`
  let T : EuclideanSpace ℝ p →ₗ[ℝ] ({i : Fin (Fintype.card p) // i ≠ ⟨k, hk⟩} → ℝ) :=
    LinearMap.pi fun i =>
      if (i : ℕ) < k then
        if h : (i : ℕ) < Fintype.card n then
          innerₛₗ ℝ (sortedBasis A ⟨i, h⟩) ∘ₗ Matrix.toEuclideanLin Q else 0
      else innerₛₗ ℝ (sortedBasis (A * Q) i)
  have hT : LinearMap.ker T ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [Module.finrank_fintype_fun_eq_card, finrank_euclideanSpace]
    exact (Fintype.card_subtype_lt (x := (⟨k, hk⟩ : Fin (Fintype.card p))) (by simp)).trans_eq
      (Fintype.card_fin _)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  have hTv : ∀ i, T v i = 0 := fun i => congrFun (LinearMap.mem_ker.1 hv) i
  -- `⟨e_j (A), Q v⟩ = 0` for `j < k`
  have hA : ∀ j : Fin (Fintype.card n), (j : ℕ) < k →
      inner ℝ (sortedBasis A j) (Matrix.toEuclideanLin Q v) = 0 := fun j hj => by
    have h := hTv ⟨⟨j, hj.trans hk⟩, fun h => hj.ne (congrArg Fin.val h)⟩
    simpa [T, hj] using h
  -- `⟨e_i (A Q), v⟩ = 0` for `k < i`
  have hAQ : ∀ i : Fin (Fintype.card p), k < i → inner ℝ (sortedBasis (A * Q) i) v = 0 :=
    fun i hi => by
      have h := hTv ⟨i, fun h => hi.ne' (congrArg Fin.val h)⟩
      simpa [T, hi.not_gt] using h
  have h1 : sortedSingularValue (A * Q) k ^ 2 * ‖v‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin (A * Q) v‖ ^ 2 := by
    rw [norm_toEuclideanLin_sq, ← (sortedBasis (A * Q)).sum_sq_inner_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases lt_or_ge k i with hi | hi
    · simp [hAQ i hi]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sortedSingularValue_nonneg _ _)
        (antitone_sortedSingularValue _ hi) 2) (sq_nonneg _)
  have h2 : ‖Matrix.toEuclideanLin A (Matrix.toEuclideanLin Q v)‖ ^ 2 ≤
      sortedSingularValue A k ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_toEuclideanLin_sq, ← hQv, ← (sortedBasis A).sum_sq_inner_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge (j : ℕ) k with hj | hj
    · simp [hA j hj]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sortedSingularValue_nonneg _ _)
        (antitone_sortedSingularValue _ hj) 2) (sq_nonneg _)
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply] at h1
  have hv' : 0 < ‖v‖ ^ 2 := by positivity
  exact le_of_sq_le_sq (le_of_mul_le_mul_right (h1.trans h2) hv') (sortedSingularValue_nonneg _ _)

omit [DecidableEq m] in
/-- (HNVW I, Lemma D.2.2 for orthonormal vectors) `det ((A Q)ᵀ (A Q)) ≤ Π_{k < N} s_k (A)²` if the
`N` columns of `Q` are orthonormal. -/
private theorem det_transpose_mul_self_le_of_transpose_mul_self_eq_one (A : Matrix m n ℝ) {N : ℕ}
    {Q : Matrix n (Fin N) ℝ} (hQ : Qᵀ * Q = 1) :
    ((A * Q)ᵀ * (A * Q)).det ≤ ∏ k ∈ Finset.range N, sortedSingularValue A k ^ 2 := by
  rw [det_transpose_mul_self_eq_prod, Fintype.card_fin]
  exact Finset.prod_le_prod₀ (fun k _ => sq_nonneg _) fun k _ =>
    pow_le_pow_left₀ (sortedSingularValue_nonneg _ _)
      (sortedSingularValue_mul_le_of_transpose_mul_self_eq_one A hQ k) 2

omit [DecidableEq n] in
/-- Orthonormalization: `Φ = Q C` with `Qᵀ Q = 1`, if `det (Φᵀ Φ) ≠ 0`; here `C = (Φᵀ Φ)^{1/2}`. -/
private theorem exists_eq_mul_of_det_ne_zero {N : ℕ} {Φ : Matrix n (Fin N) ℝ}
    (hΦ : (Φᵀ * Φ).det ≠ 0) :
    ∃ (Q : Matrix n (Fin N) ℝ) (C : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 ∧ Φ = Q * C := by
  have hG : (Φᵀ * Φ).PosSemidef := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.posSemidef_conjTranspose_mul_self Φ
  set C := cfc Real.sqrt (Φᵀ * Φ)
  have hC : Cᵀ = C := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact isHermitian_cfc _ _
  have hCC : C * C = Φᵀ * Φ := by
    rw [← cfc_mul _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
    conv_rhs => rw [← cfc_id ℝ (Φᵀ * Φ) hG.isHermitian.isSelfAdjoint]
    exact cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_posSemidef hG ht)
  have hCu : IsUnit C.det := by
    rw [← hCC, Matrix.det_mul] at hΦ
    exact (left_ne_zero_of_mul hΦ).isUnit
  refine ⟨Φ * C⁻¹, C, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hC, Matrix.mul_assoc,
      ← Matrix.mul_assoc Φᵀ, ← hCC, Matrix.mul_assoc C C, Matrix.mul_nonsing_inv _ hCu,
      Matrix.mul_one, Matrix.nonsing_inv_mul _ hCu]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCu, Matrix.mul_one]

omit [DecidableEq m] in
/-- (HNVW I, Lemma D.2.2) `det (Φᵀ Aᵀ A Φ) ≤ Π_{k < N} s_k (A)² · det (Φᵀ Φ)` for every `Φ` with `N`
columns. -/
theorem det_conj_transpose_mul_self_le (A : Matrix m n ℝ) {N : ℕ} (Φ : Matrix n (Fin N) ℝ) :
    ((A * Φ)ᵀ * (A * Φ)).det ≤
      (∏ k ∈ Finset.range N, sortedSingularValue A k ^ 2) * (Φᵀ * Φ).det := by
  by_cases hΦ : (Φᵀ * Φ).det = 0
  · -- the columns of `Φ` are linearly dependent, and then so are those of `A Φ`
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hΦ
    have hΦv : Φ *ᵥ v = 0 := by
      rwa [← Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.conjTranspose_mul_self_mulVec_eq_zero] at hv
    have h0 : ((A * Φ)ᵀ * (A * Φ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hΦv, Matrix.mulVec_zero,
          Matrix.mulVec_zero]⟩
    rw [h0, hΦ, mul_zero]
  · -- the product rule: `det ((A Φ)ᵀ (A Φ)) = det ((A Q)ᵀ (A Q)) det (C)²` and
    -- `det (Φᵀ Φ) = det (C)²`
    obtain ⟨Q, C, hQ, rfl⟩ := exists_eq_mul_of_det_ne_zero hΦ
    have h1 : (A * (Q * C))ᵀ * (A * (Q * C)) = Cᵀ * ((A * Q)ᵀ * (A * Q)) * C := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have h2 : (Q * C)ᵀ * (Q * C) = Cᵀ * C := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
    rw [h1, h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    calc C.det * ((A * Q)ᵀ * (A * Q)).det * C.det
        = ((A * Q)ᵀ * (A * Q)).det * (C.det * C.det) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (det_transpose_mul_self_le_of_transpose_mul_self_eq_one A hQ) (mul_self_nonneg _)

/-! ### Horn's inequality -/

omit [DecidableEq m] in
/-- `det ((A Φ)ᵀ (A Φ)) = Π_{k < N} s_k (A)²` for the first `N ≤ #n` right singular vectors `Φ` of
`A`, the case of equality in HNVW I, Lemma D.2.2. -/
private theorem exists_det_transpose_mul_self_eq (A : Matrix m n ℝ) {N : ℕ}
    (hN : N ≤ Fintype.card n) :
    ∃ Φ : Matrix n (Fin N) ℝ, (Φᵀ * Φ).det = 1 ∧
      ((A * Φ)ᵀ * (A * Φ)).det = ∏ k ∈ Finset.range N, sortedSingularValue A k ^ 2 := by
  set e : Fin N → EuclideanSpace ℝ n := fun k => sortedBasis A (Fin.castLE hN k)
  refine ⟨Matrix.of fun i k => e k i, ?_, ?_⟩
  · rw [← Matrix.det_one (n := Fin N) (R := ℝ)]
    congr 1
    ext j k
    have h := (sortedBasis A).inner_eq_ite (Fin.castLE hN j) (Fin.castLE hN k)
    rw [PiLp.inner_apply] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, e, mul_comm, Fin.ext_iff] using h
  · rw [Finset.prod_range, ← Matrix.det_diagonal]
    congr 1
    ext j k
    have h := inner_toEuclideanLin_sortedBasis A (Fin.castLE hN j) (Fin.castLE hN k)
    rw [PiLp.inner_apply] at h
    simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] at h
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, e, mul_comm, Fin.ext_iff] using h

/-- **Horn's inequality** (HNVW I, Proposition D.2.3):
`Π_{k<N} s_k (A B) ≤ Π_{k<N} s_k (A) s_k (B)`. -/
theorem prod_sortedSingularValue_mul_le (A : Matrix l m ℝ) (B : Matrix m n ℝ) (N : ℕ) :
    ∏ k ∈ Finset.range N, sortedSingularValue (A * B) k ≤
      ∏ k ∈ Finset.range N, sortedSingularValue A k * sortedSingularValue B k := by
  have hR : 0 ≤ ∏ k ∈ Finset.range N, sortedSingularValue A k * sortedSingularValue B k :=
    Finset.prod_nonneg fun k _ =>
      mul_nonneg (sortedSingularValue_nonneg A k) (sortedSingularValue_nonneg B k)
  rcases le_or_gt N (Fintype.card n) with hN | hN
  · -- Lemma D.2.2 for the first `N` right singular vectors of `A B`, then for `A` and `B Φ`, and
    -- for `B` and `Φ`
    obtain ⟨Φ, hΦ, hABΦ⟩ := exists_det_transpose_mul_self_eq (A * B) hN
    have hA := det_conj_transpose_mul_self_le A (B * Φ)
    have hB := det_conj_transpose_mul_self_le B Φ
    rw [← Matrix.mul_assoc A B, hABΦ] at hA
    rw [hΦ, mul_one] at hB
    have h := hA.trans (mul_le_mul_of_nonneg_left hB (Finset.prod_nonneg fun k _ => sq_nonneg _))
    rw [← Finset.prod_mul_distrib] at h
    simp only [← mul_pow, Finset.prod_pow] at h
    exact le_of_sq_le_sq h hR
  · -- `s_k (A B) = 0` for `k = #n < N`
    rw [Finset.prod_eq_zero (Finset.mem_range.2 hN) (sortedSingularValue_eq_zero (A * B) le_rfl)]
    exact hR

/-! ### Weak majorization -/

/-- The difference quotient `(f b - f a) / (b - a)` of a convex function is nondecreasing in both
variables. -/
private theorem slope_le_slope {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {a b a' b' : ℝ}
    (h : a ≠ b) (h' : a' ≠ b') (ha : a ≤ a') (hb : b ≤ b') :
    (f b - f a) / (b - a) ≤ (f b' - f a') / (b' - a') := by
  -- `(f y - f x) / (y - x)` is symmetric
  have hsymm : ∀ x y : ℝ, (f y - f x) / (y - x) = (f x - f y) / (x - y) := fun x y => by
    rw [← neg_sub (f x), ← neg_sub x, neg_div_neg_eq]
  have hmono : ∀ {c x y : ℝ}, x ≠ c → y ≠ c → x ≤ y →
      (f x - f c) / (x - c) ≤ (f y - f c) / (y - c) := fun hx hy hxy =>
    hf.secant_mono (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hx hy hxy
  by_cases hab' : b' = a
  · -- `b < b' = a < a'`
    subst hab'
    rw [hsymm a' b']
    exact hmono h.symm h' (hb.trans ha)
  · calc (f b - f a) / (b - a) ≤ (f b' - f a) / (b' - a) := hmono h.symm hab' hb
      _ = (f a - f b') / (a - b') := hsymm _ _
      _ ≤ (f a' - f b') / (a' - b') := hmono (Ne.symm hab') h' ha
      _ = (f b' - f a') / (b' - a') := hsymm _ _

/-- Abel summation: `Σ_{j<N} c_j d_j ≥ 0` if `c_0 ≥ c_1 ≥ … ≥ 0` and the partial sums of `d` are
nonnegative. -/
private theorem sum_mul_nonneg_of_antitone {c d : ℕ → ℝ} (hc : Antitone c) (hc0 : ∀ j, 0 ≤ c j)
    (N : ℕ) (hd : ∀ k ≤ N, 0 ≤ ∑ j ∈ Finset.range k, d j) :
    0 ≤ ∑ j ∈ Finset.range N, c j * d j := by
  have h := Finset.sum_range_by_parts c d N
  simp only [smul_eq_mul] at h
  rw [h, sub_nonneg]
  refine le_trans (Finset.sum_nonpos fun j hj => ?_) (mul_nonneg (hc0 _) (hd N le_rfl))
  rw [Finset.mem_range] at hj
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hc j.le_succ)) (hd _ (by omega))

/-- (HNVW I, Lemma D.1.4) If `a`, `b` are nonincreasing with `Σ_{j<k} a_j ≤ Σ_{j<k} b_j` for all
`k ≤ N`, then `Σ_{j<N} f (a_j) ≤ Σ_{j<N} f (b_j)` for every convex nondecreasing `f`. -/
theorem sum_le_sum_of_weak_majorization {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hfm : Monotone f)
    {a b : ℕ → ℝ} (N : ℕ) (ha : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hb : ∀ i j, i ≤ j → j < N → b j ≤ b i)
    (hab : ∀ k ≤ N, ∑ j ∈ Finset.range k, a j ≤ ∑ j ∈ Finset.range k, b j) :
    ∑ j ∈ Finset.range N, f (a j) ≤ ∑ j ∈ Finset.range N, f (b j) := by
  -- the difference quotients `c_j`, for `j` in the set `S` of the indices with `a_j ≠ b_j`
  set c : ℕ → ℝ := fun j => (f (b j) - f (a j)) / (b j - a j)
  set S : Set ℕ := {j | j < N ∧ a j ≠ b j}
  have hS : S.Finite := (Set.finite_lt_nat N).subset fun j hj => hj.1
  have hcS : AntitoneOn c S := fun i hi j hj hij =>
    slope_le_slope hf hj.2 hi.2 (ha i j hij hj.1) (hb i j hij hj.1)
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    rcases le_total (a j) (b j) with h | h
    · exact div_nonneg (sub_nonneg.2 (hfm h)) (sub_nonneg.2 h)
    · exact div_nonneg_of_nonpos (sub_nonpos.2 (hfm h)) (sub_nonpos.2 h)
  -- the equal entries do not contribute: extend `c` from `S` to a nonincreasing sequence
  obtain ⟨c', hc', hcc'⟩ := hcS.exists_antitone_extension (hS.image c).bddBelow
    (hS.image c).bddAbove
  have hmul : ∀ j ∈ Finset.range N, max (c' j) 0 * (b j - a j) = f (b j) - f (a j) := by
    intro j hj
    by_cases hjab : a j = b j
    · rw [hjab, sub_self, sub_self, mul_zero]
    · have hjS : j ∈ S := ⟨Finset.mem_range.1 hj, hjab⟩
      rw [← hcc' hjS, max_eq_left (hc0 j), div_mul_cancel₀ _ (sub_ne_zero.2 (Ne.symm hjab))]
  have h := sum_mul_nonneg_of_antitone (c := fun j => max (c' j) 0) (d := fun j => b j - a j)
    (fun i j hij => max_le_max_right 0 (hc' hij)) (fun j => le_max_right _ _) N fun k hk => by
      rw [Finset.sum_sub_distrib, sub_nonneg]
      exact hab k hk
  rwa [Finset.sum_congr rfl hmul, Finset.sum_sub_distrib, sub_nonneg] at h

/-! ### Hölder's inequality -/

omit [DecidableEq m] in
/-- `(Σ_{k < K} s_k^q)^{1/q} ≤ ‖A‖_{S_q}` for every `K`. -/
private theorem rpow_sum_sortedSingularValue_le {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, sortedSingularValue A k ^ q) ^ (1 / q) ≤
      schattenNorm (ENNReal.ofReal q) A := by
  have h0 : ∀ k, 0 ≤ sortedSingularValue A k ^ q := fun k =>
    Real.rpow_nonneg (sortedSingularValue_nonneg A k) q
  rw [schattenNorm_eq_sum_sortedSingularValue hq]
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => h0 k) ?_ (by positivity)
  calc ∑ k ∈ Finset.range K, sortedSingularValue A k ^ q
      ≤ ∑ k ∈ Finset.range (max K (Fintype.card n)), sortedSingularValue A k ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
          fun k _ _ => h0 k
    _ = ∑ k ∈ Finset.range (Fintype.card n), sortedSingularValue A k ^ q := by
        refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun k _ hk => ?_).symm
        rw [sortedSingularValue_eq_zero A (by simpa using hk), Real.zero_rpow hq.ne']

/-- (HNVW I, Corollary D.2.4, first step) `Σ_{k < K} s_k (A B)^p ≤ Σ_{k < K} (s_k (A) s_k (B))^p` if
the first `K` singular values of `A B` are positive: the logarithms of Horn's inequality and
Lemma D.1.4 with `f (t) = e^{p t}`. -/
private theorem sum_sortedSingularValue_mul_rpow_le {p : ℝ} (hp : 0 < p) (A : Matrix l m ℝ)
    (B : Matrix m n ℝ) {K : ℕ} (hK : ∀ k < K, 0 < sortedSingularValue (A * B) k) :
    ∑ k ∈ Finset.range K, sortedSingularValue (A * B) k ^ p ≤
      ∑ k ∈ Finset.range K, (sortedSingularValue A k * sortedSingularValue B k) ^ p := by
  -- `s_k (A) s_k (B) > 0` for `k < K`, from Horn's inequality
  have hAB : ∀ k < K, 0 < sortedSingularValue A k * sortedSingularValue B k := by
    intro k hk
    have h1 : 0 < ∏ j ∈ Finset.range (k + 1), sortedSingularValue (A * B) j :=
      Finset.prod_pos fun j hj => hK j ((Finset.mem_range_succ_iff.1 hj).trans_lt hk)
    have h2 := Finset.prod_ne_zero_iff.1
      (h1.trans_le (prod_sortedSingularValue_mul_le A B (k + 1))).ne' k
      (Finset.self_mem_range_succ k)
    exact (mul_nonneg (sortedSingularValue_nonneg A k)
      (sortedSingularValue_nonneg B k)).lt_of_ne' h2
  have hconv : ConvexOn ℝ Set.univ fun t : ℝ => Real.exp (p * t) := by
    simpa only [Set.preimage_univ] using! convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ p)
  have hmono : Monotone fun t : ℝ => Real.exp (p * t) := fun s t hst =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hst hp.le)
  have h := sum_le_sum_of_weak_majorization hconv hmono
    (a := fun k => Real.log (sortedSingularValue (A * B) k))
    (b := fun k => Real.log (sortedSingularValue A k * sortedSingularValue B k)) K
    (fun i j hij hj => Real.log_le_log (hK j hj) (antitone_sortedSingularValue _ hij))
    (fun i j hij hj => Real.log_le_log (hAB j hj) (mul_le_mul (antitone_sortedSingularValue A hij)
      (antitone_sortedSingularValue B hij) (sortedSingularValue_nonneg B j)
      (sortedSingularValue_nonneg A i)))
    fun k hk => by
      have hlt : ∀ j ∈ Finset.range k, j < K := fun j hj => (Finset.mem_range.1 hj).trans_le hk
      rw [← Real.log_prod fun j hj => (hK j (hlt j hj)).ne',
        ← Real.log_prod fun j hj => (hAB j (hlt j hj)).ne']
      exact Real.log_le_log (Finset.prod_pos fun j hj => hK j (hlt j hj))
        (prod_sortedSingularValue_mul_le A B k)
  refine (Finset.sum_congr rfl fun k hk => ?_).trans_le
    (h.trans_eq (Finset.sum_congr rfl fun k hk => ?_))
  · rw [Real.rpow_def_of_pos (hK k (Finset.mem_range.1 hk)), mul_comm]
  · rw [Real.rpow_def_of_pos (hAB k (Finset.mem_range.1 hk)), mul_comm]

/-- **Hölder's inequality** for Schatten norms (HNVW I, Corollary D.2.4):
`‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r`. -/
theorem schattenNorm_mul_le {p q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / p = 1 / q + 1 / r)
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal p) (A * B) ≤
      schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal r) B := by
  have hp : 0 < p := one_div_pos.1 (hpqr ▸ by positivity)
  have hT : q.HolderTriple r p := ⟨by simpa only [one_div] using hpqr.symm, hq, hr⟩
  -- the number `K` of nonzero singular values of `A B`
  have hex : ∃ k, sortedSingularValue (A * B) k = 0 :=
    ⟨Fintype.card n, sortedSingularValue_eq_zero _ le_rfl⟩
  classical
  set K := Nat.find hex with hKdef
  have hK : ∀ k < K, 0 < sortedSingularValue (A * B) k := fun k hk =>
    (sortedSingularValue_nonneg _ k).lt_of_ne' (Nat.find_min hex hk)
  have hK0 : ∀ k, K ≤ k → sortedSingularValue (A * B) k = 0 := fun k hk =>
    le_antisymm ((antitone_sortedSingularValue _ hk).trans (Nat.find_spec hex).le)
      (sortedSingularValue_nonneg _ k)
  have hKn : K ≤ Fintype.card n := Nat.find_min' hex (sortedSingularValue_eq_zero _ le_rfl)
  have hsum : ∑ k ∈ Finset.range (Fintype.card n), sortedSingularValue (A * B) k ^ p =
      ∑ k ∈ Finset.range K, sortedSingularValue (A * B) k ^ p := by
    refine (Finset.sum_subset (Finset.range_mono hKn) fun k _ hk => ?_).symm
    rw [hK0 k (by simpa using hk), Real.zero_rpow hp.ne']
  have hA0 : 0 ≤ ∑ k ∈ Finset.range K, sortedSingularValue A k ^ q :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (sortedSingularValue_nonneg A k) q
  have hB0 : 0 ≤ ∑ k ∈ Finset.range K, sortedSingularValue B k ^ r :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (sortedSingularValue_nonneg B k) r
  -- Horn's inequality, then the scalar Hölder inequality
  have h := (sum_sortedSingularValue_mul_rpow_le hp A B hK).trans
    (Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg (Finset.range K) hT
      (fun k _ => sortedSingularValue_nonneg A k) fun k _ => sortedSingularValue_nonneg B k)
  rw [schattenNorm_eq_sum_sortedSingularValue hp, hsum]
  calc (∑ k ∈ Finset.range K, sortedSingularValue (A * B) k ^ p) ^ (1 / p)
      ≤ ((∑ k ∈ Finset.range K, sortedSingularValue A k ^ q) ^ (p / q) *
          (∑ k ∈ Finset.range K, sortedSingularValue B k ^ r) ^ (p / r)) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun k _ =>
          Real.rpow_nonneg (sortedSingularValue_nonneg _ k) p) h (by positivity)
    _ = (∑ k ∈ Finset.range K, sortedSingularValue A k ^ q) ^ (1 / q) *
          (∑ k ∈ Finset.range K, sortedSingularValue B k ^ r) ^ (1 / r) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _),
          ← Real.rpow_mul hA0, ← Real.rpow_mul hB0]
        congr 2 <;> field_simp
    _ ≤ _ := mul_le_mul (rpow_sum_sortedSingularValue_le hq A K)
        (rpow_sum_sortedSingularValue_le hr B K) (Real.rpow_nonneg hB0 _) (schattenNorm_nonneg _ _)

/-! ### The trace -/

/-- (HNVW I, Corollary D.2.4, converse part, used for Proposition D.2.5) The factorization
`A = Vᵀ W` with `‖V‖_{S_2}² = ‖W‖_{S_2}² = ‖A‖_{S_1}`: with the singular value decomposition
`A = Σ_k s_k f_k e_kᵀ`, take `Vᵀ = Σ_k s_k^{1/2} f_k g_kᵀ` and `W = Σ_k s_k^{1/2} g_k e_kᵀ`, where
`(g_k)` is the standard basis. -/
private theorem exists_eq_transpose_mul (A : Matrix m n ℝ) :
    ∃ (V : Matrix n m ℝ) (W : Matrix n n ℝ), A = Vᵀ * W ∧
      schattenNorm 2 V ^ 2 = ∑ k, singularValue A k ∧
      schattenNorm 2 W ^ 2 = ∑ k, singularValue A k := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ) with hU
  have hU1 : Uᵀ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * Uᵀ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  -- the columns `s_k f_k = A e_k` of `F` are orthogonal, with norm `s_k`
  set F : Matrix m n ℝ := A * U with hF
  have hFF : Fᵀ * F = Matrix.diagonal hA.eigenvalues := by
    have h : Aᵀ * A = U * Matrix.diagonal hA.eigenvalues * Uᵀ :=
      eq_eigenvectorUnitary_mul_diagonal_mul_star hA
    have h' : Fᵀ * F = Uᵀ * (Aᵀ * A) * U := by
      simp only [hF, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [h', h, Matrix.mul_assoc, Matrix.mul_assoc, hU1, Matrix.mul_one, ← Matrix.mul_assoc, hU1,
      Matrix.one_mul]
  have hFk : ∀ k, ∑ i, F i k ^ 2 = singularValue A k ^ 2 := fun k => by
    have h := congrFun (congrFun hFF k) k
    rw [Matrix.diagonal_apply_eq, ← singularValue_sq, Matrix.mul_apply] at h
    simpa only [Matrix.transpose_apply, ← sq] using h
  have hUk : ∀ k, ∑ j, U j k ^ 2 = 1 := fun k => by
    have h := congrFun (congrFun hU1 k) k
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h
    simpa only [Matrix.transpose_apply, ← sq] using h
  set d : n → ℝ := fun k => √(singularValue A k) with hd
  have hd2 : ∀ k, d k ^ 2 = singularValue A k := fun k => Real.sq_sqrt (singularValue_nonneg A k)
  refine ⟨Matrix.diagonal d⁻¹ * Fᵀ, Matrix.diagonal d * Uᵀ, ?_, ?_, ?_⟩
  · -- `Vᵀ W = F Uᵀ = A U Uᵀ = A`, since `A e_k = 0` where `s_k = 0`
    have hFd : F * Matrix.diagonal (fun k => d⁻¹ k * d k) = F := by
      ext i k
      rw [Matrix.mul_diagonal, Pi.inv_apply]
      by_cases hk : d k = 0
      · have h0 : ∑ i, F i k ^ 2 = 0 := by rw [hFk, ← hd2, hk]; norm_num
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (F i k)).1 h0 i
          (Finset.mem_univ i)
        rw [pow_eq_zero_iff two_ne_zero] at h1
        rw [h1, zero_mul]
      · rw [inv_mul_cancel₀ hk, mul_one]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d⁻¹), Matrix.diagonal_mul_diagonal,
      ← Matrix.mul_assoc, hFd, hF, Matrix.mul_assoc, hU2, Matrix.mul_one]
  · rw [schattenNorm_two_sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diagonal_mul, Matrix.transpose_apply, Pi.inv_apply, mul_pow]
    rw [← Finset.mul_sum, hFk, ← hd2]
    rcases eq_or_ne (d k) 0 with hk | hk
    · simp [hk]
    · field_simp
  · rw [schattenNorm_two_sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diagonal_mul, Matrix.transpose_apply, mul_pow]
    rw [← Finset.mul_sum, hUk, hd2, mul_one]

omit [DecidableEq m] in
/-- The Cauchy–Schwarz inequality `|tr (Vᵀ W)| ≤ ‖V‖_{S_2} ‖W‖_{S_2}` for the Hilbert–Schmidt inner
product. -/
private theorem abs_trace_transpose_mul_le (V W : Matrix m n ℝ) :
    |(Vᵀ * W).trace| ≤ schattenNorm 2 V * schattenNorm 2 W := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n)) (fun i => V i.1 i.2)
    fun i => W i.1 i.2
  simp only [Fintype.sum_prod_type] at h
  rw [← schattenNorm_two_sq, ← schattenNorm_two_sq, ← mul_pow] at h
  have ht : (Vᵀ * W).trace = ∑ i, ∑ j, V i j * W i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [ht]
  exact abs_le_of_sq_le_sq h (mul_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _))

/-- (HNVW I, Proposition D.2.5) The trace is contractive on `S_1`. -/
theorem abs_trace_le_schattenNorm_one (A : Matrix n n ℝ) : |A.trace| ≤ schattenNorm 1 A := by
  obtain ⟨V, W, hA, hV, hW⟩ := exists_eq_transpose_mul A
  have h1 : schattenNorm 1 A = ∑ k, singularValue A k := by
    have h := schattenNorm_ofReal_rpow one_pos A
    simpa only [ENNReal.ofReal_one, Real.rpow_one] using h
  calc |A.trace| ≤ schattenNorm 2 V * schattenNorm 2 W := hA ▸ abs_trace_transpose_mul_le V W
    _ = schattenNorm 1 A := by
        have hVW : schattenNorm 2 V = schattenNorm 2 W :=
          (pow_left_inj₀ (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _) two_ne_zero).1
            (hV.trans hW.symm)
        rw [hVW, ← sq, hW, h1]

/-- `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`, `1/q + 1/q' = 1`, for rectangular matrices. -/
theorem abs_trace_mul_le {q q' : ℝ} (hq : q.HolderConjugate q') (A : Matrix n m ℝ)
    (B : Matrix m n ℝ) :
    |(A * B).trace| ≤ schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal q') B := by
  have h := schattenNorm_mul_le (p := 1) hq.pos hq.symm.pos
    (by rw [one_div, one_div, one_div, inv_one, hq.inv_add_inv_eq_one]) A B
  rw [ENNReal.ofReal_one] at h
  exact (abs_trace_le_schattenNorm_one _).trans h

end BanachProbability
