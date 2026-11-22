module

public import BanachProbability.Schatten.Basic
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Spectral tools for Schatten norms

Functional calculus on real symmetric matrices is Mathlib's `cfc`
(`Matrix.IsHermitian.instContinuousFunctionalCalculus`); since the spectrum is finite, every
function is continuous on it (`continuousOn_spectrum`), and `f (A)` is symmetric
(`isHermitian_cfc`; it is `0` when `A` is not symmetric). This file collects what the
Schatten-valued inequalities use:

* the eigenvalues of `f (A)` are a permutation of the `f (λ_i (A))`
  (`exists_equiv_eigenvalues_cfc_eq`, from the characteristic polynomial), so
  `Σ_i F (λ_i (f (A))) = Σ_i F (f (λ_i (A)))` (`sum_comp_eigenvalues_cfc`) and
  `tr f (A) = Σ f (λ_i (A))` (`trace_cfc_eq_sum`);
* `f (A) ⪰ 0` when `f ≥ 0` on the spectrum of `A` (`posSemidef_cfc`), and the spectrum of a
  positive semidefinite matrix is nonnegative (`spectrum_nonneg_of_posSemidef`);
* singular values of a symmetric matrix are the absolute values of its eigenvalues (since
  `Aᵀ A = A²`), so `‖A‖_{S_q}^q = Σ |λ_i (A)|^q` (`schattenNorm_rpow_of_isHermitian`,
  `schattenNorm_eq_of_isHermitian`), `‖f (A)‖_{S_r}^r = Σ |f (λ_i (A))|^r`
  (`schattenNorm_cfc_rpow`), `‖A‖_{S_1} = tr A` for `A ⪰ 0` (`schattenNorm_one_of_posSemidef`) and
  `‖A‖_{S_q}^q = tr (A h (A))` with `h (t) = t |t|^{q−2}` (`schattenNorm_rpow_eq_trace`);
* spectral projections `spectralProj A S = 1_S (A)`;
* the counting function `countAbove s A = #{i : s_i (A) > s}` (the distribution function of the
  singular values), with the rank perturbation bound
  `countAbove s (A + R) ≤ countAbove s A + rank R` and the subadditivity
  `countAbove (s + t) (A + B) ≤ countAbove s A + countAbove t B` (Weyl's inequalities for singular
  values, by the standard Courant–Fischer dimension count; a usual reference
  is R. Bhatia, *Matrix Analysis*, Ch. III), and Chebyshev's inequality;
* Loewner-order and trace lemmas: `A − P A P ⪰ 0` for a projection `P` commuting with `A ⪰ 0`,
  `tr (A B) ≥ 0` and `tr (A B) ≤ c tr B` for `0 ⪯ A ⪯ c` and `B ⪰ 0`, and monotonicity of the
  Hilbert–Schmidt norm on `0 ⪯ A ⪯ B`.
-/

@[expose] public section

open scoped ENNReal Matrix

open Module

namespace BanachProbability

/-- Two finite families with the same multiset of values differ by a bijection of the index
types. -/
theorem exists_equiv_apply_eq_of_map_univ_eq {ι κ γ : Type*} [Fintype ι] [Fintype κ]
    {f : ι → γ} {g : κ → γ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  classical
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq ?_),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
  have hc := congrArg (Multiset.count c) h
  rw [Multiset.count_map, Multiset.count_map] at hc
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa [Finset.card, Finset.filter_val, eq_comm] using hc

section Square

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every function is continuous on the real spectrum of a matrix, which is finite. -/
theorem continuousOn_spectrum (A : Matrix n n ℝ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- A function of a matrix is symmetric (for a non-symmetric matrix it is `0`, the junk value of
`cfc`). -/
theorem isHermitian_cfc (f : ℝ → ℝ) (A : Matrix n n ℝ) : (cfc f A).IsHermitian :=
  cfc_predicate f A

open Polynomial in
/-- The eigenvalues of a symmetric matrix with characteristic polynomial `∏ (X − g i)` are a
permutation of `g`. -/
theorem exists_equiv_eigenvalues_eq_of_charpoly_eq {B : Matrix n n ℝ} (hB : B.IsHermitian)
    {g : n → ℝ} (h : B.charpoly = ∏ i, (X - C (g i))) :
    ∃ e : n ≃ n, ∀ i, hB.eigenvalues (e i) = g i := by
  apply exists_equiv_apply_eq_of_map_univ_eq
  have h1 := hB.roots_charpoly_eq_eigenvalues
  rw [h, Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])] at h1
  simpa using h1

/-- The eigenvalues of `f (A)` are a permutation of the `f (λ_i (A))`. -/
theorem exists_equiv_eigenvalues_cfc_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hB : (cfc f A).IsHermitian) :
    ∃ e : n ≃ n, ∀ i, hB.eigenvalues (e i) = f (hA.eigenvalues i) :=
  exists_equiv_eigenvalues_eq_of_charpoly_eq hB (by simpa using hA.charpoly_cfc_eq f)

/-- Sums over the eigenvalues of `f (A)` are sums over the `f (λ_i (A))`:
`Σ_i F (λ_i (f (A))) = Σ_i F (f (λ_i (A)))`. -/
theorem sum_comp_eigenvalues_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : (cfc f A).IsHermitian) (F : ℝ → ℝ) :
    ∑ i, F (hf.eigenvalues i) = ∑ i, F (f (hA.eigenvalues i)) := by
  obtain ⟨e, he⟩ := exists_equiv_eigenvalues_cfc_eq hA f hf
  rw [← e.sum_comp]
  simp [he]

/-- The trace of a function of a symmetric matrix: `tr f (A) = Σ_i f (λ_i (A))`. -/
theorem trace_cfc_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  have hB : (cfc f A).IsHermitian := isHermitian_cfc f A
  obtain ⟨e, he⟩ := exists_equiv_eigenvalues_cfc_eq hA f hB
  rw [hB.trace_eq_sum_eigenvalues, ← e.sum_comp]
  simp [he]

/-- The spectrum of a positive semidefinite matrix is nonnegative. -/
theorem spectrum_nonneg_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ}
    (ht : t ∈ spectrum ℝ A) : 0 ≤ t := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hA.eigenvalues_nonneg i

/-- A function of a matrix that is nonnegative on its spectrum is positive semidefinite:
`f (A) = h (A)ᵀ h (A)` with `h = √f`. -/
theorem posSemidef_cfc {A : Matrix n n ℝ} {f : ℝ → ℝ} (hf : ∀ t ∈ spectrum ℝ A, 0 ≤ f t) :
    (cfc f A).PosSemidef := by
  have hC := isHermitian_cfc (fun t => Real.sqrt (f t)) A
  have hCC : cfc (fun t => Real.sqrt (f t)) A * cfc (fun t => Real.sqrt (f t)) A = cfc f A := by
    rw [← cfc_mul _ _ A (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
    exact cfc_congr fun t ht => Real.mul_self_sqrt (hf t ht)
  have h := Matrix.posSemidef_conjTranspose_mul_self (cfc (fun t => Real.sqrt (f t)) A)
  rwa [hC.eq, hCC] at h

/-- The singular values of a symmetric matrix are the absolute values of its eigenvalues, up to
a permutation. -/
theorem exists_equiv_singularValue_eq_abs_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ e : n ≃ n, ∀ i, singularValue A (e i) = |hA.eigenvalues i| := by
  -- `Aᵀ A = A² = (t ↦ t²) (A)`, whose eigenvalues are a permutation of the `λ_i²`.
  have hsq : Aᴴ * A = cfc (fun t : ℝ => t ^ 2) A := by
    have h := cfc_pow (id : ℝ → ℝ) 2 A (continuousOn_spectrum _ _) hA.isSelfAdjoint
    rw [cfc_id ℝ A hA.isSelfAdjoint] at h
    rw [hA.eq, ← sq]
    exact h.symm
  obtain ⟨e, he⟩ := exists_equiv_eigenvalues_eq_of_charpoly_eq
    (Matrix.isHermitian_conjTranspose_mul_self A) (g := fun i => hA.eigenvalues i ^ 2)
    (by rw [hsq]; exact hA.charpoly_cfc_eq (fun t : ℝ => t ^ 2))
  exact ⟨e, fun i => by rw [singularValue, he, Real.sqrt_sq_eq_abs]⟩

theorem schattenNorm_rpow_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) {q : ℝ}
    (hq : 0 < q) : schattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, |hA.eigenvalues i| ^ q := by
  obtain ⟨e, he⟩ := exists_equiv_singularValue_eq_abs_eigenvalues hA
  have h := schattenNorm_rpow (q := ENNReal.ofReal q) (by simpa using hq) ENNReal.ofReal_ne_top A
  rw [ENNReal.toReal_ofReal hq.le] at h
  rw [h, ← e.sum_comp]
  simp [he]

/-- The Schatten `q`-norm of a symmetric matrix from its eigenvalues:
`‖A‖_{S_q} = (Σ_i |λ_i|^q)^{1/q}`, `q > 0`. -/
theorem schattenNorm_eq_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) {q : ℝ}
    (hq : 0 < q) :
    schattenNorm (ENNReal.ofReal q) A = (∑ i, |hA.eigenvalues i| ^ q) ^ (1 / q) := by
  rw [← schattenNorm_rpow_of_isHermitian hA hq, ← Real.rpow_mul (schattenNorm_nonneg _ _),
    mul_one_div_cancel hq.ne', Real.rpow_one]

/-- `‖f (A)‖_{S_r}^r = Σ_i |f (λ_i (A))|^r` for a symmetric `A` and `r > 0`. -/
theorem schattenNorm_cfc_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    schattenNorm (ENNReal.ofReal r) (cfc f A) ^ r = ∑ i, |f (hA.eigenvalues i)| ^ r := by
  have hB := isHermitian_cfc f A
  rw [schattenNorm_rpow_of_isHermitian hB hr, sum_comp_eigenvalues_cfc hA f hB fun t => |t| ^ r]

/-- The `S_1` norm of a positive semidefinite matrix is its trace. -/
theorem schattenNorm_one_of_posSemidef {W : Matrix n n ℝ} (hW : W.PosSemidef) :
    schattenNorm (ENNReal.ofReal 1) W = W.trace := by
  have h := schattenNorm_rpow_of_isHermitian hW.isHermitian one_pos
  have h2 := trace_cfc_eq_sum hW.isHermitian id
  rw [cfc_id ℝ W (show IsSelfAdjoint W from hW.isHermitian)] at h2
  rw [Real.rpow_one] at h
  rw [h, h2]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.rpow_one, abs_of_nonneg (hW.eigenvalues_nonneg i), id]

/-- `‖A‖_{S_q}^q = tr (A h (A))` with `h (t) = t |t|^{q−2}`, for a symmetric `A`. -/
theorem schattenNorm_rpow_eq_trace {A : Matrix n n ℝ} (hA : A.IsHermitian) {q : ℝ} (hq : 0 < q) :
    schattenNorm (ENNReal.ofReal q) A ^ q = (A * cfc (fun t : ℝ => t * |t| ^ (q - 2)) A).trace := by
  -- `A h (A) = (t ↦ t · h t) (A)` and `t · t |t|^{q−2} = |t|^q` (also at `t = 0`, as `q > 0`).
  have hmul : A * cfc (fun t : ℝ => t * |t| ^ (q - 2)) A =
      cfc (fun t : ℝ => t * (t * |t| ^ (q - 2))) A := by
    have h := cfc_mul id (fun t : ℝ => t * |t| ^ (q - 2)) A (continuousOn_spectrum _ _)
      (continuousOn_spectrum _ _)
    rw [cfc_id ℝ A hA.isSelfAdjoint] at h
    exact h.symm
  rw [hmul, trace_cfc_eq_sum hA, schattenNorm_rpow_of_isHermitian hA hq]
  refine Finset.sum_congr rfl fun i _ => ?_
  set t := hA.eigenvalues i
  rcases eq_or_ne t 0 with ht | ht
  · simp [ht, Real.zero_rpow hq.ne']
  · have hpos : 0 < |t| := abs_pos.2 ht
    rw [← mul_assoc, ← sq, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_add hpos]
    norm_num

/-- The spectral projection `1_S (A)` of a symmetric matrix. -/
noncomputable def spectralProj (A : Matrix n n ℝ) (S : Set ℝ) : Matrix n n ℝ :=
  cfc (S.indicator (1 : ℝ → ℝ)) A

theorem spectralProj_mul_self (A : Matrix n n ℝ) (S : Set ℝ) :
    spectralProj A S * spectralProj A S = spectralProj A S := by
  rw [spectralProj, ← cfc_mul _ _ A (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  congr 1
  ext t
  by_cases ht : t ∈ S <;> simp [ht]

theorem spectralProj_transpose (A : Matrix n n ℝ) (S : Set ℝ) :
    (spectralProj A S)ᵀ = spectralProj A S := by
  have h : (spectralProj A S).IsHermitian := isHermitian_cfc _ A
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, h.eq]

/-- A matrix commutes with its spectral projections: for a symmetric matrix by the functional
calculus, and otherwise the spectral projection is `0` (the junk value of `cfc`). -/
theorem commute_spectralProj (A : Matrix n n ℝ) (S : Set ℝ) : Commute A (spectralProj A S) := by
  by_cases hA : A.IsHermitian
  · have h := cfc_commute_cfc (id : ℝ → ℝ) (S.indicator (1 : ℝ → ℝ)) A
    rwa [cfc_id ℝ A hA.isSelfAdjoint] at h
  · rw [spectralProj, cfc_apply_of_not_predicate A (show ¬ IsSelfAdjoint A from hA)]
    exact Commute.zero_right A

open scoped Classical in
theorem trace_spectralProj {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : Set ℝ) :
    (spectralProj A S).trace = ((Finset.univ.filter fun i => hA.eigenvalues i ∈ S).card : ℝ) := by
  rw [spectralProj, trace_cfc_eq_sum hA, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : hA.eigenvalues i ∈ S <;> simp [hi]

omit [DecidableEq n] in
/-- `A − P A P ⪰ 0` for an orthogonal projection `P` commuting with `A ⪰ 0`: it is
`(1 − P) A (1 − P)`. -/
theorem posSemidef_sub_mul_mul_of_commute {A P : Matrix n n ℝ} (hA : A.PosSemidef)
    (hP : P * P = P) (hPt : Pᵀ = P) (hc : Commute P A) : (A - P * A * P).PosSemidef := by
  classical
  have h : A - P * A * P = (1 - P)ᴴ * A * (1 - P) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, Matrix.transpose_one,
      hPt]
    have h1 : P * A * P = P * A := by rw [mul_assoc, ← hc.eq, ← mul_assoc, hP]
    have e : (1 - P) * A * (1 - P) = A - P * A - A * P + P * A * P := by noncomm_ring
    rw [e, ← hc.eq, h1]
    abel
  rw [h]
  exact hA.conjTranspose_mul_mul_same _

omit [DecidableEq n] in
/-- `tr (A B) = tr (B^{1/2} A B^{1/2}) ≥ 0` for `A, B ⪰ 0`. -/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  set C := cfc Real.sqrt B
  have hC : C.IsHermitian := isHermitian_cfc _ B
  have hCC : C * C = B := by
    rw [← cfc_mul _ _ B (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
    conv_rhs => rw [← cfc_id ℝ B hB.isHermitian.isSelfAdjoint]
    exact cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_posSemidef hB ht)
  rw [← hCC, ← mul_assoc, Matrix.trace_mul_cycle]
  have := hA.conjTranspose_mul_mul_same C
  rw [hC.eq] at this
  exact this.trace_nonneg

/-- `tr (A B) ≤ c tr B` for `A ⪯ c` and `B ⪰ 0`. -/
theorem trace_mul_le_of_le_smul_one {A B : Matrix n n ℝ} {c : ℝ}
    (hAc : (c • (1 : Matrix n n ℝ) - A).PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace ≤ c * B.trace := by
  have h := trace_mul_nonneg_of_posSemidef hAc hB
  rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul] at h
  linarith

omit [DecidableEq n] in
/-- The Hilbert–Schmidt norm is monotone on positive semidefinite matrices:
`tr (A²) ≤ tr (B²)` for `0 ⪯ A ⪯ B`. -/
theorem trace_mul_self_le_of_le {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hAB : (B - A).PosSemidef) : (A * A).trace ≤ (B * B).trace := by
  -- `tr (B²) − tr (A²) = tr ((B − A) B) + tr ((B − A) A)`.
  have hB : B.PosSemidef := by simpa using hAB.add hA
  have h1 := trace_mul_nonneg_of_posSemidef hAB hB
  have h2 := trace_mul_nonneg_of_posSemidef hAB hA
  rw [sub_mul, Matrix.trace_sub] at h1 h2
  rw [Matrix.trace_mul_comm B A] at h2
  linarith

end Square

section Count

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem countAbove_anti {s t : ℝ} (hst : s ≤ t) (A : Matrix m n ℝ) :
    countAbove t A ≤ countAbove s A :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hst.trans_lt hi

theorem countAbove_le_card (s : ℝ) (A : Matrix m n ℝ) : countAbove s A ≤ Fintype.card n :=
  (Finset.card_filter_le _ _).trans_eq Finset.card_univ

private theorem countAbove_of_neg {s : ℝ} (hs : s < 0) (A : Matrix m n ℝ) :
    countAbove s A = Fintype.card n := by
  rw [countAbove, Finset.filter_true_of_mem fun i _ => hs.trans_le (singularValue_nonneg A i),
    Finset.card_univ]

/-! ### The Courant–Fischer dimension count -/

omit [Fintype m] [DecidableEq n] in
/-- A vector in the span of `b_i`, `i ∈ S`, has no component along `b_j`, `j ∉ S`. -/
private theorem repr_eq_zero_of_mem_span {b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)}
    {S : Set n} {v : EuclideanSpace ℝ n} (hv : v ∈ Submodule.span ℝ (b '' S)) {j : n}
    (hj : j ∉ S) : b.repr v j = 0 := by
  rw [b.repr_apply_apply]
  have h : Submodule.span ℝ (b '' S) ≤ LinearMap.ker (innerₛₗ ℝ (b j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
    exact b.orthonormal.2 fun h => hj (h ▸ hi)
  exact h hv

omit [Fintype m] [DecidableEq n] in
/-- The span of the `b_i`, `i ∈ S`, has dimension `#S`. -/
private theorem finrank_span_image (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (S : Finset n) : finrank ℝ (Submodule.span ℝ (b '' (S : Set n))) = S.card := by
  have hli : LinearIndependent ℝ (fun i : (S : Set n) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have := finrank_span_eq_card hli
  rw [show Set.range (fun i : (S : Set n) => b i) = b '' (S : Set n) by ext x; simp] at this
  rw [this]
  simp

omit [Fintype m] [DecidableEq n] in
/-- `‖v‖² = Σ_i ⟨b_i, v⟩²`. -/
private theorem norm_sq_eq_sum_repr (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (v : EuclideanSpace ℝ n) : ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq]

/-- `‖A v‖² = Σ_i λ_i (Aᵀ A) ⟨b_i, v⟩²` in an orthonormal eigenbasis `(b_i)` of `Aᵀ A`. -/
private theorem norm_toEuclideanLin_sq (A : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      ∑ i, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i *
        ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis.repr v i) ^ 2 := by
  set hN := Matrix.isHermitian_conjTranspose_mul_self A
  set b := hN.eigenvectorBasis
  have h1 : ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      inner ℝ (Matrix.toEuclideanLin (Aᴴ * A) v) v := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec (WithLp.ofLp v) Aᵀ, Matrix.vecMul_transpose, dotProduct_comm]
  have h2 : Matrix.toEuclideanLin (Aᴴ * A) v = ∑ i, (b.repr v i * hN.eigenvalues i) • b i := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, mul_smul]
    congr 1
    rw [Matrix.toLpLin_apply, hN.mulVec_eigenvectorBasis i]
    rfl
  rw [h1, h2, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ← b.repr_apply_apply]
  ring

/-- The span of the eigenvectors `b_i` of `Aᵀ A` with `p i`. -/
private noncomputable abbrev eigenSpan (A : Matrix m n ℝ) (p : n → Prop) [DecidablePred p] :
    Submodule ℝ (EuclideanSpace ℝ n) :=
  Submodule.span ℝ ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis ''
    ↑(Finset.univ.filter p))

/-- On the span of the eigenvectors of `Aᵀ A` with `s_i (A) > s`, `‖A v‖ > s ‖v‖` for `v ≠ 0`. -/
private theorem mul_norm_lt_norm_toEuclideanLin {A : Matrix m n ℝ} {s : ℝ} (hs : 0 ≤ s)
    {v : EuclideanSpace ℝ n} (hv : v ∈ eigenSpan A fun i => s < singularValue A i)
    (hv0 : v ≠ 0) : s * ‖v‖ < ‖Matrix.toEuclideanLin A v‖ := by
  set hN := Matrix.isHermitian_conjTranspose_mul_self A
  set b := hN.eigenvectorBasis
  have hsq : (s * ‖v‖) ^ 2 < ‖Matrix.toEuclideanLin A v‖ ^ 2 := by
    rw [norm_toEuclideanLin_sq, mul_pow, norm_sq_eq_sum_repr b, Finset.mul_sum]
    obtain ⟨j, hj⟩ : ∃ j, b.repr v j ≠ 0 := by
      by_contra! h
      exact hv0 (b.repr.map_eq_zero_iff.1 (by ext j; simp [h j]))
    have hjS : s < singularValue A j := by
      by_contra h
      exact hj (repr_eq_zero_of_mem_span hv (by simpa using h))
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · by_cases hi : s < singularValue A i
      · exact mul_le_mul_of_nonneg_right ((Real.lt_sqrt hs).1 hi).le (sq_nonneg _)
      · rw [repr_eq_zero_of_mem_span hv (by simpa using hi)]
        simp
    · exact mul_lt_mul_of_pos_right ((Real.lt_sqrt hs).1 hjS) (by positivity)
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

/-- On the span of the eigenvectors of `Aᵀ A` with `s_i (A) ≤ s`, `‖A v‖ ≤ s ‖v‖`. -/
private theorem norm_toEuclideanLin_le {A : Matrix m n ℝ} {s : ℝ} (hs : 0 ≤ s)
    {v : EuclideanSpace ℝ n} (hv : v ∈ eigenSpan A fun i => ¬s < singularValue A i) :
    ‖Matrix.toEuclideanLin A v‖ ≤ s * ‖v‖ := by
  set hN := Matrix.isHermitian_conjTranspose_mul_self A
  set b := hN.eigenvectorBasis
  have hsq : ‖Matrix.toEuclideanLin A v‖ ^ 2 ≤ (s * ‖v‖) ^ 2 := by
    rw [norm_toEuclideanLin_sq, mul_pow, norm_sq_eq_sum_repr b, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : s < singularValue A i
    · rw [repr_eq_zero_of_mem_span hv (by simpa using hi)]
      simp
    · exact mul_le_mul_of_nonneg_right ((Real.sqrt_le_left hs).1 (not_lt.1 hi)) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

private theorem finrank_eigenSpan_lt (s : ℝ) (A : Matrix m n ℝ) :
    finrank ℝ (eigenSpan A fun i => s < singularValue A i) = countAbove s A :=
  finrank_span_image _ _

private theorem finrank_eigenSpan_not_lt_add_countAbove (s : ℝ) (A : Matrix m n ℝ) :
    finrank ℝ (eigenSpan A fun i => ¬s < singularValue A i) + countAbove s A =
      Fintype.card n := by
  rw [finrank_span_image, countAbove, add_comm, Finset.card_filter_add_card_filter_not,
    Finset.card_univ]

omit [Fintype m] [DecidableEq n] in
/-- Two subspaces whose dimensions add up to more than `#n` meet in a nonzero vector. -/
private theorem exists_ne_zero_mem_of_lt_finrank_add {U W : Submodule ℝ (EuclideanSpace ℝ n)}
    (h : Fintype.card n < finrank ℝ U + finrank ℝ W) : ∃ v ∈ U, v ∈ W ∧ v ≠ 0 := by
  have hUW : U ⊓ W ≠ ⊥ := by
    intro h0
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [h0, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_le (U ⊔ W)
    rw [finrank_euclideanSpace] at h2
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUW
  exact ⟨v, (Submodule.mem_inf.1 hv).1, (Submodule.mem_inf.1 hv).2, hv0⟩

omit [Fintype m] [DecidableEq n] in
/-- `dim U + dim W ≤ dim (U ∩ W) + #n`. -/
private theorem finrank_add_finrank_le_finrank_inf_add (U W : Submodule ℝ (EuclideanSpace ℝ n)) :
    finrank ℝ U + finrank ℝ W ≤ finrank ℝ ↥(U ⊓ W) + Fintype.card n := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_le (U ⊔ W)
  rw [finrank_euclideanSpace] at h2
  omega

omit [Fintype m] in
/-- `rank R + dim ker R = #n`. -/
private theorem rank_add_finrank_ker [Finite m] (R : Matrix m n ℝ) :
    R.rank + finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin R)) = Fintype.card n := by
  cases nonempty_fintype m
  rw [Matrix.rank_eq_finrank_range_toLin R (EuclideanSpace.basisFun m ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis, ← finrank_euclideanSpace (𝕜 := ℝ) (ι := n)]
  exact LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin R)

/-- **Rank perturbation**: `#{s_i (A + R) > s} ≤ #{s_i (A) > s} + rank R` (Weyl's inequality
`s_{i+k+1} (A + R) ≤ s_{i+1} (A)` for `rank R ≤ k`, by a Courant–Fischer dimension count). -/
theorem countAbove_add_le_add_rank (s : ℝ) (A R : Matrix m n ℝ) :
    countAbove s (A + R) ≤ countAbove s A + R.rank := by
  -- Courant–Fischer (the standard dimension count): if the claim fails, the span `U` of
  -- the eigenvectors of `(A + R)ᵀ (A + R)` with `s_i (A + R) > s` meets `W = ker R ∩` the span
  -- of the eigenvectors of `Aᵀ A` with `s_i (A) ≤ s`, by counting dimensions; on a common
  -- `v ≠ 0`, `s ‖v‖ < ‖(A + R) v‖ = ‖A v‖ ≤ s ‖v‖`. For `s < 0` the right side is `≥ #n`.
  rcases lt_or_ge s 0 with hs | hs
  · have := countAbove_le_card s (A + R)
    rw [countAbove_of_neg hs A]
    omega
  by_contra! hlt
  have hK := rank_add_finrank_ker R
  set K := LinearMap.ker (Matrix.toEuclideanLin R)
  have hU := finrank_eigenSpan_lt s (A + R)
  have hW := finrank_eigenSpan_not_lt_add_countAbove s A
  have hWK := finrank_add_finrank_le_finrank_inf_add
    (eigenSpan A fun i => ¬s < singularValue A i) K
  obtain ⟨v, hvU, hvW, hv0⟩ := exists_ne_zero_mem_of_lt_finrank_add
    (U := eigenSpan (A + R) fun i => s < singularValue (A + R) i)
    (W := (eigenSpan A fun i => ¬s < singularValue A i) ⊓ K) (by omega)
  have h1 := mul_norm_lt_norm_toEuclideanLin hs hvU hv0
  have h2 := norm_toEuclideanLin_le hs (Submodule.mem_inf.1 hvW).1
  have h3 : Matrix.toEuclideanLin (A + R) v = Matrix.toEuclideanLin A v := by
    rw [map_add, LinearMap.add_apply, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hvW).2, add_zero]
  rw [h3] at h1
  linarith

/-- **Subadditivity of the distribution function**:
`#{s_i (A + B) > s + t} ≤ #{s_i (A) > s} + #{s_i (B) > t}` (Weyl's inequality
`s_{i+j+1} (A + B) ≤ s_{i+1} (A) + s_{j+1} (B)`). -/
theorem countAbove_add_add_le (s t : ℝ) (A B : Matrix m n ℝ) :
    countAbove (s + t) (A + B) ≤ countAbove s A + countAbove t B := by
  -- Courant–Fischer (the standard dimension count), as in `countAbove_add_le_add_rank`,
  -- with `W = W_A ∩ W_B` and `‖(A + B) v‖ ≤ ‖A v‖ + ‖B v‖ ≤ (s + t) ‖v‖` on `W`.
  rcases lt_or_ge s 0 with hs | hs
  · have := countAbove_le_card (s + t) (A + B)
    rw [countAbove_of_neg hs A]
    omega
  rcases lt_or_ge t 0 with ht | ht
  · have := countAbove_le_card (s + t) (A + B)
    rw [countAbove_of_neg ht B]
    omega
  by_contra! hlt
  have hU := finrank_eigenSpan_lt (s + t) (A + B)
  have hWA := finrank_eigenSpan_not_lt_add_countAbove s A
  have hWB := finrank_eigenSpan_not_lt_add_countAbove t B
  have hW := finrank_add_finrank_le_finrank_inf_add
    (eigenSpan A fun i => ¬s < singularValue A i) (eigenSpan B fun i => ¬t < singularValue B i)
  obtain ⟨v, hvU, hvW, hv0⟩ := exists_ne_zero_mem_of_lt_finrank_add
    (U := eigenSpan (A + B) fun i => s + t < singularValue (A + B) i)
    (W := (eigenSpan A fun i => ¬s < singularValue A i) ⊓
      (eigenSpan B fun i => ¬t < singularValue B i)) (by omega)
  have h1 := mul_norm_lt_norm_toEuclideanLin (add_nonneg hs ht) hvU hv0
  have h2 := norm_toEuclideanLin_le hs (Submodule.mem_inf.1 hvW).1
  have h3 := norm_toEuclideanLin_le ht (Submodule.mem_inf.1 hvW).2
  have h4 : ‖Matrix.toEuclideanLin (A + B) v‖ ≤
      ‖Matrix.toEuclideanLin A v‖ + ‖Matrix.toEuclideanLin B v‖ := by
    rw [map_add, LinearMap.add_apply]
    exact norm_add_le _ _
  linarith

/-- **Chebyshev's inequality** for singular values: `s^q #{s_i (A) > s} ≤ ‖A‖_{S_q}^q`. -/
theorem countAbove_mul_rpow_le {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (A : Matrix m n ℝ) :
    (countAbove s A : ℝ) * s ^ q ≤ schattenNorm (ENNReal.ofReal q) A ^ q := by
  have h := schattenNorm_rpow (q := ENNReal.ofReal q) (by simpa using hq) ENNReal.ofReal_ne_top A
  rw [ENNReal.toReal_ofReal hq.le] at h
  rw [h]
  calc (countAbove s A : ℝ) * s ^ q
      = ∑ i ∈ Finset.univ.filter (fun i => s < singularValue A i), s ^ q := by
        rw [Finset.sum_const, nsmul_eq_mul, countAbove]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => s < singularValue A i), singularValue A i ^ q :=
        Finset.sum_le_sum fun i hi =>
          Real.rpow_le_rpow hs.le (Finset.mem_filter.1 hi).2.le hq.le
    _ ≤ ∑ i, singularValue A i ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
          Real.rpow_nonneg (singularValue_nonneg A i) q

theorem countAbove_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : ℝ) :
    countAbove s A = (Finset.univ.filter fun i => s < |hA.eigenvalues i|).card := by
  obtain ⟨e, he⟩ := exists_equiv_singularValue_eq_abs_eigenvalues hA
  rw [countAbove, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv fun i => by rw [he]).symm

end Count

end BanachProbability
