module

public import BanachProbability.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.MeanInequalities

/-!
# Schatten norms of real matrices

For a real `m × n` matrix `A`, the singular values `s_i (A) = √λ_i (Aᵀ A)`, `i : n`, are the
square roots of the eigenvalues of the positive semidefinite matrix `Aᵀ A` (`singularValue`; when
`n` is larger than `m` the extra ones are `0`, which changes no Schatten norm). The Schatten
`q`-norm is `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞` and `‖A‖_{S_∞} = max_i s_i`
(`schattenNorm`, with `q : ℝ≥0∞`). For `q ≥ 1` it is a norm (`schattenNorm_add_le`, in
`BanachProbability.Schatten.Triangle`), and `SchattenSpace q m n` is the corresponding normed
space (`BanachProbability.Schatten.Space`).

Basic facts: nonnegativity, homogeneity, definiteness, the Frobenius identity
`‖A‖_{S_2}² = Σ A_{ij}²`, invariance under transposition and orthogonal conjugation,
`‖Aᵀ A‖_{S_{q/2}} = ‖A‖_{S_q}²`, and the comparison of the norms for different exponents
(monotonicity of the `ℓ^p` norms in `p`, and the power-mean inequality).

The singular values enter the Schatten norms only through the multiset of the eigenvalues of
`Aᵀ A`, which is the multiset of roots of its characteristic polynomial
(`map_eigenvalues_eq_roots_charpoly`). Two symmetric matrices, possibly of different sizes, whose
characteristic polynomials agree up to powers of `X` have the same nonzero eigenvalues with
multiplicity (`filter_map_eigenvalues_eq_of_X_pow_mul_charpoly_eq`), and the Schatten norms see
only the nonzero singular values (`schattenNorm_eq_of_filter_map_singularValue_eq`); hence
`χ (A Aᵀ) X^{#n} = χ (Aᵀ A) X^{#m}` (`Matrix.charpoly_mul_comm'`) gives `‖Aᵀ‖_{S_q} = ‖A‖_{S_q}`
(`schattenNorm_eq_of_X_pow_mul_charpoly_eq`). If `B = U diag (μ) Uᵀ` with `U` orthogonal, the
eigenvalues of `B` are the `μ_i` up to order (`map_eigenvalues_eq_of_eq_mul_diagonal_mul_star`);
with the spectral theorem for `Aᵀ A` this computes the singular values of `c A` (the `|c| s_i`)
and of `Aᵀ A` (the `s_i²`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem singularValue_nonneg (A : Matrix m n ℝ) (i : n) : 0 ≤ singularValue A i :=
  Real.sqrt_nonneg _

/-! ### Mathlib's singular values -/

section SingularValues

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Mathlib's singular values of the linear map of a real or complex matrix between Euclidean
spaces. -/
theorem singularValues_toEuclideanLin_fin (A : Matrix m n 𝕜) (k : Fin (Fintype.card n)) :
    (Matrix.toEuclideanLin A).singularValues k =
      √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k) := by
  classical
  rw [LinearMap.singularValues_fin _ finrank_euclideanSpace, Matrix.IsHermitian.eigenvalues₀]
  congr
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul_same]

/-- A sum over the singular values `√λ_i (Aᴴ A)` in terms of Mathlib's. -/
theorem sum_comp_sqrt_eigenvalues_eq (A : Matrix m n 𝕜) (F : ℝ → ℝ) :
    ∑ i, F √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) =
      ∑ k ∈ Finset.range (Fintype.card n), F ((Matrix.toEuclideanLin A).singularValues k) := by
  rw [Finset.sum_range, ← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [singularValues_toEuclideanLin_fin, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- The largest singular value `max_i √λ_i (Aᴴ A)` in terms of Mathlib's. -/
theorem iSup_sqrt_eigenvalues_eq (A : Matrix m n 𝕜) :
    ⨆ i, √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) =
      (Matrix.toEuclideanLin A).singularValues 0 := by
  rcases isEmpty_or_nonempty n with h | h
  · rw [Real.iSup_of_isEmpty, LinearMap.singularValues_of_finrank_le]
    rw [finrank_euclideanSpace, Fintype.card_eq_zero]
  · have h0 : 0 < Fintype.card n := Fintype.card_pos
    set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with he
    have hk : ∀ k, √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues (e k)) =
        (Matrix.toEuclideanLin A).singularValues k := fun k => by
      rw [singularValues_toEuclideanLin_fin, Matrix.IsHermitian.eigenvalues, he,
        Equiv.symm_apply_apply]
    refine le_antisymm (ciSup_le fun i => ?_) ?_
    · rw [← e.apply_symm_apply i, hk]
      exact LinearMap.singularValues_antitone _ (Nat.zero_le _)
    · rw [show (0 : ℕ) = ((⟨0, h0⟩ : Fin (Fintype.card n)) : ℕ) from rfl, ← hk]
      exact le_ciSup (f := fun i => √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i))
        (Set.finite_range _).bddAbove _

end SingularValues

/-- The Schatten norm in terms of Mathlib's singular values, `0 < q < ∞`. -/
theorem schattenNorm_eq_sum_singularValues {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A = (∑ k ∈ Finset.range (Fintype.card n),
      (Matrix.toEuclideanLin A).singularValues k ^ q) ^ (1 / q) := by
  rw [schattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
  exact congrArg (· ^ (1 / q)) (sum_comp_sqrt_eigenvalues_eq A (· ^ q))

/-- `‖A‖_{S_∞}` is Mathlib's largest singular value. -/
theorem schattenNorm_top_eq_singularValues (A : Matrix m n ℝ) :
    schattenNorm ⊤ A = (Matrix.toEuclideanLin A).singularValues 0 := by
  rw [schattenNorm, ite_eq_left rfl]
  exact iSup_sqrt_eigenvalues_eq A

/-- `s_i (A)² = λ_i (Aᵀ A)`. -/
theorem singularValue_sq (A : Matrix m n ℝ) (i : n) :
    singularValue A i ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

/-! ### Finite families with the same values -/

section Multiset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Two finite families with the same multiset of values have the same sums. -/
theorem sum_comp_eq_of_map_eq {f : ι → ℝ} {g : κ → ℝ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) (F : ℝ → ℝ) :
    ∑ i, F (f i) = ∑ j, F (g j) := by
  have := congrArg (fun s => (Multiset.map F s).sum) h
  simpa only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using this

private theorem sum_map_filter_ne_zero (s : Multiset ℝ) {F : ℝ → ℝ} (hF : F 0 = 0) :
    (Multiset.map F (s.filter (· ≠ 0))).sum = (Multiset.map F s).sum := by
  have h0 : (Multiset.map F (s.filter fun a => ¬a ≠ 0)).sum = 0 := by
    refine Multiset.sum_eq_zero fun x hx => ?_
    simp only [Multiset.mem_map, Multiset.mem_filter, not_not] at hx
    obtain ⟨y, ⟨-, rfl⟩, rfl⟩ := hx
    exact hF
  conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) s]
  rw [Multiset.map_add, Multiset.sum_add, h0, add_zero]

/-- Two finite families with the same multiset of nonzero values have the same sums of `F`,
for every `F` with `F 0 = 0`. -/
theorem sum_comp_eq_of_filter_map_eq {f : ι → ℝ} {g : κ → ℝ}
    (h : (Multiset.map f Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map g Finset.univ.val).filter (· ≠ 0)) {F : ℝ → ℝ} (hF : F 0 = 0) :
    ∑ i, F (f i) = ∑ j, F (g j) := by
  have := congrArg (fun s => (Multiset.map F s).sum) h
  simp only [sum_map_filter_ne_zero _ hF, Multiset.map_map, Function.comp_def,
    ← Finset.sum_eq_multiset_sum] at this
  exact this

private theorem iSup_le_iSup_of_filter_map_eq {f : ι → ℝ} {g : κ → ℝ} (hg : ∀ j, 0 ≤ g j)
    (h : (Multiset.map f Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map g Finset.univ.val).filter (· ≠ 0)) :
    ⨆ i, f i ≤ ⨆ j, g j := by
  refine Real.iSup_le (fun i => ?_) (Real.iSup_nonneg hg)
  by_cases hi : f i = 0
  · rw [hi]
    exact Real.iSup_nonneg hg
  · have hmem : f i ∈ (Multiset.map g Finset.univ.val).filter (· ≠ 0) := by
      rw [← h]
      exact Multiset.mem_filter.2 ⟨Multiset.mem_map_of_mem _ (Finset.mem_univ_val i), hi⟩
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 (Multiset.mem_filter.1 hmem).1
    rw [← hj]
    exact le_ciSup (Finite.bddAbove_range g) j

/-- Two nonnegative finite families with the same multiset of nonzero values have the same
supremum. -/
theorem iSup_eq_of_filter_map_eq {f : ι → ℝ} {g : κ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ j, 0 ≤ g j)
    (h : (Multiset.map f Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map g Finset.univ.val).filter (· ≠ 0)) :
    ⨆ i, f i = ⨆ j, g j :=
  le_antisymm (iSup_le_iSup_of_filter_map_eq hg h) (iSup_le_iSup_of_filter_map_eq hf h.symm)

private theorem iSup_sq {ι : Type*} [Finite ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    ⨆ i, f i ^ 2 = (⨆ i, f i) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := f)
    rw [← hi₀]
    exact le_antisymm
      (ciSup_le fun i => pow_le_pow_left₀ (hf i)
        ((le_ciSup (Finite.bddAbove_range f) i).trans hi₀.ge) 2)
      (le_ciSup (Finite.bddAbove_range fun i => f i ^ 2) i₀)

end Multiset

/-! ### Eigenvalues as roots of the characteristic polynomial -/

section Eigenvalues

variable {k l : Type*} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l]

/-- Equal symmetric matrices have equal eigenvalues (whatever the proofs of symmetry). -/
theorem eigenvalues_eq_of_eq {A B : Matrix k k ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

/-- The eigenvalues of a real symmetric matrix, as a multiset, are the roots of its
characteristic polynomial. -/
theorem map_eigenvalues_eq_roots_charpoly {A : Matrix k k ℝ} (hA : A.IsHermitian) :
    Multiset.map hA.eigenvalues Finset.univ.val = A.charpoly.roots := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp

/-- The spectral theorem for a real symmetric matrix: `A = U diag (λ) Uᵀ`. -/
theorem eq_eigenvectorUnitary_mul_diagonal_mul_star {A : Matrix k k ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix k k ℝ) * Matrix.diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix k k ℝ) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rfl

/-- The eigenvalues of `B = U diag (μ) Uᵀ`, `U` orthogonal, are the `μ_i` up to order. -/
theorem map_eigenvalues_eq_of_eq_mul_diagonal_mul_star {B : Matrix k k ℝ} (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup k ℝ) (μ : k → ℝ)
    (h : B = (U : Matrix k k ℝ) * Matrix.diagonal μ * star (U : Matrix k k ℝ)) :
    Multiset.map hB.eigenvalues Finset.univ.val = Multiset.map μ Finset.univ.val := by
  have hc : B.charpoly = (Matrix.diagonal μ).charpoly := by
    rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
      Matrix.one_mul]
  rw [map_eigenvalues_eq_roots_charpoly, hc, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

open Polynomial in
/-- Two symmetric matrices (possibly of different sizes) whose characteristic polynomials agree up
to powers of `X` have the same nonzero eigenvalues, with multiplicity. -/
theorem filter_map_eigenvalues_eq_of_X_pow_mul_charpoly_eq {A : Matrix k k ℝ}
    {B : Matrix l l ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) {a b : ℕ}
    (h : X ^ a * A.charpoly = X ^ b * B.charpoly) :
    (Multiset.map hA.eigenvalues Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map hB.eigenvalues Finset.univ.val).filter (· ≠ 0) := by
  have key : ∀ (c : ℕ) {p : ℝ[X]}, p.Monic →
      (X ^ c * p).roots.filter (· ≠ 0) = p.roots.filter (· ≠ 0) := by
    intro c p hp
    have h0 : (c • ({0} : Multiset ℝ)).filter (· ≠ 0) = 0 := by
      refine Multiset.filter_eq_nil.2 fun x hx => ?_
      simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
      simp [hx.2]
    rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp.ne_zero), roots_X_pow,
      Multiset.filter_add, h0, zero_add]
  rw [map_eigenvalues_eq_roots_charpoly, map_eigenvalues_eq_roots_charpoly,
    ← key a A.charpoly_monic, h, key b B.charpoly_monic]

end Eigenvalues

/-! ### Comparing Schatten norms through the spectrum of `Aᵀ A` -/

private theorem filter_map_singularValue (A : Matrix m n ℝ) :
    (Multiset.map (singularValue A) Finset.univ.val).filter (· ≠ 0) =
      Multiset.map Real.sqrt
        ((Multiset.map (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues
          Finset.univ.val).filter (· ≠ 0)) := by
  have : singularValue A =
      Real.sqrt ∘ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := rfl
  rw [this, ← Multiset.map_map, Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
  simp only [Function.comp_apply, ne_eq]
  rw [Real.sqrt_eq_zero (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)]

/-- The Schatten norms depend only on the nonzero singular values. -/
theorem schattenNorm_eq_of_filter_map_singularValue_eq {m' n' : Type*} [Fintype m']
    [Fintype n'] [DecidableEq n'] {A : Matrix m n ℝ} {B : Matrix m' n' ℝ}
    (h : (Multiset.map (singularValue A) Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map (singularValue B) Finset.univ.val).filter (· ≠ 0)) (q : ℝ≥0∞) :
    schattenNorm q A = schattenNorm q B := by
  unfold schattenNorm
  split_ifs with hq
  · exact iSup_eq_of_filter_map_eq (singularValue_nonneg A) (singularValue_nonneg B) h
  · rcases eq_or_ne q.toReal 0 with h0 | h0
    · simp [h0]
    · rw [sum_comp_eq_of_filter_map_eq h (F := fun x => x ^ q.toReal) (Real.zero_rpow h0)]

open Polynomial in
/-- If the characteristic polynomials of `Aᵀ A` and `Bᵀ B` agree up to powers of `X`, then `A` and
`B` have the same nonzero singular values. -/
theorem filter_map_singularValue_eq_of_X_pow_mul_charpoly_eq {m' n' : Type*} [Fintype m']
    [Fintype n'] [DecidableEq n'] {A : Matrix m n ℝ} {B : Matrix m' n' ℝ} {a b : ℕ}
    (h : X ^ a * (Aᵀ * A).charpoly = X ^ b * (Bᵀ * B).charpoly) :
    (Multiset.map (singularValue A) Finset.univ.val).filter (· ≠ 0) =
      (Multiset.map (singularValue B) Finset.univ.val).filter (· ≠ 0) := by
  have h' : X ^ a * (Aᴴ * A).charpoly = X ^ b * (Bᴴ * B).charpoly := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  rw [filter_map_singularValue, filter_map_singularValue,
    filter_map_eigenvalues_eq_of_X_pow_mul_charpoly_eq _ _ h']

open Polynomial in
/-- If the characteristic polynomials of `Aᵀ A` and `Bᵀ B` agree up to powers of `X`, then `A` and
`B` have the same Schatten norms. -/
theorem schattenNorm_eq_of_X_pow_mul_charpoly_eq {m' n' : Type*} [Fintype m'] [Fintype n']
    [DecidableEq n'] {A : Matrix m n ℝ} {B : Matrix m' n' ℝ} {a b : ℕ}
    (h : X ^ a * (Aᵀ * A).charpoly = X ^ b * (Bᵀ * B).charpoly) (q : ℝ≥0∞) :
    schattenNorm q A = schattenNorm q B :=
  schattenNorm_eq_of_filter_map_singularValue_eq
    (filter_map_singularValue_eq_of_X_pow_mul_charpoly_eq h) q

/-- `Aᵀ` and `A` have the same nonzero singular values: the sums of `F (s_i)` agree if
`F (0) = 0`. -/
theorem sum_comp_singularValue_transpose [DecidableEq m] (A : Matrix m n ℝ) {F : ℝ → ℝ}
    (hF : F 0 = 0) : ∑ i, F (singularValue Aᵀ i) = ∑ i, F (singularValue A i) :=
  sum_comp_eq_of_filter_map_eq (filter_map_singularValue_eq_of_X_pow_mul_charpoly_eq
    (by simpa only [Matrix.transpose_transpose] using Matrix.charpoly_mul_comm' A Aᵀ)) hF

/-! ### Finite `ℓ^p` sums -/

private theorem le_sum_rpow_rpow_one_div {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) {p : ℝ} (hp : 0 < p) {j : ι} (hj : j ∈ s) :
    f j ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  calc f j = (f j ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (hf j), mul_one_div_cancel hp.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (hf j) _)
        (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hf i) p) hj) (by positivity)

/-- `ℓ^q ≤ ℓ^p` for `0 < p ≤ q` (finite sums of nonnegative terms). -/
private theorem sum_rpow_rpow_one_div_anti {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  set S := (∑ i ∈ s, f i ^ p) ^ (1 / p) with hS
  have hsum0 : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hS0 : 0 ≤ S := Real.rpow_nonneg hsum0 _
  have hSp : S ^ p = ∑ i ∈ s, f i ^ p := by
    rw [hS, ← Real.rpow_mul hsum0, one_div_mul_cancel hp.ne', Real.rpow_one]
  have hfi : ∀ i ∈ s, f i ≤ S := fun i hi => le_sum_rpow_rpow_one_div hf hp hi
  have key : ∑ i ∈ s, f i ^ q ≤ S ^ q := by
    calc ∑ i ∈ s, f i ^ q = ∑ i ∈ s, f i ^ p * f i ^ (q - p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.rpow_add' (hf i) (by linarith : p + (q - p) ≠ 0), add_sub_cancel]
      _ ≤ ∑ i ∈ s, f i ^ p * S ^ (q - p) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hf i) (hfi i hi) (by linarith)) (Real.rpow_nonneg (hf i) _)
      _ = S ^ p * S ^ (q - p) := by rw [← Finset.sum_mul, hSp]
      _ = S ^ q := by rw [← Real.rpow_add' hS0 (by linarith : p + (q - p) ≠ 0), add_sub_cancel]
  calc (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (S ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _) key
          (by positivity)
    _ = S := by rw [← Real.rpow_mul hS0, mul_one_div_cancel hq.ne', Real.rpow_one]

/-- The power-mean inequality: `ℓ^p ≤ |s|^{1/p − 1/q} ℓ^q` for `0 < p ≤ q`. -/
private theorem sum_rpow_rpow_one_div_le_card_mul {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) {p q : ℝ} (hp0 : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤
      (s.card : ℝ) ^ (1 / p - 1 / q) * (∑ i ∈ s, f i ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := hp0.trans_le hpq
  have hr : 1 ≤ q / p := (one_le_div hp0).2 hpq
  have hsum0 : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hsumq : 0 ≤ ∑ i ∈ s, f i ^ q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s) (f := fun i => f i ^ p) hr
    (fun i _ => Real.rpow_nonneg (hf i) _)
  have hpow : ∀ i, (f i ^ p) ^ (q / p) = f i ^ q := fun i => by
    rw [← Real.rpow_mul (hf i), mul_div_cancel₀ _ hp0.ne']
  simp only [hpow] at h
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hsum0 _) h (by positivity : (0 : ℝ) ≤ 1 / q)
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) = ((∑ i ∈ s, f i ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [← Real.rpow_mul hsum0]
        congr 1
        field_simp
    _ ≤ ((s.card : ℝ) ^ (q / p - 1) * ∑ i ∈ s, f i ^ q) ^ (1 / q) := h2
    _ = (s.card : ℝ) ^ (1 / p - 1 / q) * (∑ i ∈ s, f i ^ q) ^ (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hc0 _) hsumq, ← Real.rpow_mul hc0]
        congr 2
        field_simp

/-! ### The basic properties -/

theorem schattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n ℝ) : 0 ≤ schattenNorm q A := by
  unfold schattenNorm
  split_ifs
  · exact Real.iSup_nonneg (singularValue_nonneg A)
  · exact Real.rpow_nonneg
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _) _

theorem schattenNorm_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (A : Matrix m n ℝ) :
    schattenNorm q A ^ q.toReal = ∑ i, singularValue A i ^ q.toReal := by
  have hr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqt⟩
  rw [schattenNorm, ite_eq_right hqt, ← Real.rpow_mul
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _),
    one_div_mul_cancel hr, Real.rpow_one]

/-- `‖A‖_{S_q}^q = Σ_i s_i (A)^q` for a real exponent `q > 0`. -/
theorem schattenNorm_ofReal_rpow {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, singularValue A i ^ q := by
  have h := schattenNorm_rpow (q := ENNReal.ofReal q) (by simpa using hq) ENNReal.ofReal_ne_top A
  rwa [ENNReal.toReal_ofReal hq.le] at h

private theorem forall_singularValue_eq_zero_iff (A : Matrix m n ℝ) :
    (∀ i, singularValue A i = 0) ↔ A = 0 := by
  rw [← Matrix.conjTranspose_mul_self_eq_zero,
    ← (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues_eq_zero_iff, funext_iff]
  refine forall_congr' fun i => ?_
  rw [singularValue, Real.sqrt_eq_zero (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i),
    Pi.zero_apply]

theorem schattenNorm_eq_zero_iff {q : ℝ≥0∞} (hq : q ≠ 0) {A : Matrix m n ℝ} :
    schattenNorm q A = 0 ↔ A = 0 := by
  rw [← forall_singularValue_eq_zero_iff]
  unfold schattenNorm
  split_ifs with ht
  · constructor
    · intro h i
      exact le_antisymm ((le_ciSup (Finite.bddAbove_range _) i).trans h.le)
        (singularValue_nonneg A i)
    · intro h
      simp only [h, Real.iSup_const_zero]
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq ht
    have hs : 0 ≤ ∑ i, singularValue A i ^ q.toReal :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _
    rw [Real.rpow_eq_zero hs (by positivity), Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _)]
    simp only [Finset.mem_univ, true_imp_iff, Real.rpow_eq_zero (singularValue_nonneg A _) hr.ne']

@[simp] theorem schattenNorm_zero {q : ℝ≥0∞} (hq : q ≠ 0) :
    schattenNorm q (0 : Matrix m n ℝ) = 0 :=
  (schattenNorm_eq_zero_iff hq).2 rfl

/-- `s (c A) = |c| s (A)` as multisets: the eigenvalues of `(c A)ᵀ (c A) = c² Aᵀ A` are the
`c² λ_i`. -/
private theorem map_singularValue_smul (c : ℝ) (A : Matrix m n ℝ) :
    Multiset.map (singularValue (c • A)) Finset.univ.val =
      Multiset.map (fun i => |c| * singularValue A i) Finset.univ.val := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  have h : (c • A)ᴴ * (c • A) = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
    have hd : Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) =
        (c ^ 2) • Matrix.diagonal hA.eigenvalues := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← sq, hd, Matrix.mul_smul, Matrix.smul_mul, ← eq_eigenvectorUnitary_mul_diagonal_mul_star hA]
  have he := map_eigenvalues_eq_of_eq_mul_diagonal_mul_star
    (Matrix.isHermitian_conjTranspose_mul_self (c • A)) _ _ h
  change Multiset.map (Real.sqrt ∘ _) _ = _
  rw [← Multiset.map_map, he, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  rw [Function.comp_apply, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

theorem schattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : ℝ) (A : Matrix m n ℝ) :
    schattenNorm q (c • A) = |c| * schattenNorm q A := by
  have hmap := map_singularValue_smul c A
  unfold schattenNorm
  split_ifs with ht
  · rw [iSup_eq_of_filter_map_eq (singularValue_nonneg _)
      (fun i => mul_nonneg (abs_nonneg c) (singularValue_nonneg A i))
      (congrArg (Multiset.filter (· ≠ 0)) hmap), Real.mul_iSup_of_nonneg (abs_nonneg c)]
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq ht
    rw [sum_comp_eq_of_map_eq hmap (fun x => x ^ q.toReal)]
    simp only [Real.mul_rpow (abs_nonneg c) (singularValue_nonneg A _), ← Finset.mul_sum]
    rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _),
      ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hr.ne', Real.rpow_one]

theorem schattenNorm_neg (q : ℝ≥0∞) (A : Matrix m n ℝ) :
    schattenNorm q (-A) = schattenNorm q A := by
  have h : singularValue (-A) = singularValue A := by
    funext i
    unfold singularValue
    rw [eigenvalues_eq_of_eq _ (Matrix.isHermitian_conjTranspose_mul_self A) (by simp)]
  simp only [schattenNorm, h]

/-- The Frobenius identity `‖A‖_{S_2}² = Σ_{ij} A_{ij}² = tr (Aᵀ A)`. -/
theorem schattenNorm_two_sq (A : Matrix m n ℝ) :
    schattenNorm 2 A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hsum : ∑ k, singularValue A k ^ (2 : ℝ) = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [Real.rpow_two, singularValue_sq]
    have := (Matrix.isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [← this, Matrix.trace, Finset.sum_comm]
    simp [Matrix.mul_apply, sq]
  rw [schattenNorm, ite_eq_right ENNReal.ofNat_ne_top, h2, hsum, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity)]

theorem schattenNorm_transpose [DecidableEq m] (q : ℝ≥0∞) (A : Matrix m n ℝ) :
    schattenNorm q Aᵀ = schattenNorm q A :=
  schattenNorm_eq_of_X_pow_mul_charpoly_eq
    (by simpa only [Matrix.transpose_transpose] using Matrix.charpoly_mul_comm' A Aᵀ) q

/-- `s (Aᵀ A) = s (A)²` as multisets: the eigenvalues of `(Aᵀ A)²` are the `λ_i²`. -/
private theorem map_singularValue_transpose_mul_self (A : Matrix m n ℝ) :
    Multiset.map (singularValue (Aᵀ * A)) Finset.univ.val =
      Multiset.map (fun i => singularValue A i ^ 2) Finset.univ.val := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  have hU : star (hA.eigenvectorUnitary : Matrix n n ℝ) * (hA.eigenvectorUnitary : Matrix n n ℝ)
      = 1 := Unitary.coe_star_mul_self _
  have hG : Aᵀ * A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal hA.eigenvalues * star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact eq_eigenvectorUnitary_mul_diagonal_mul_star hA
  have h : (Aᵀ * A)ᴴ * (Aᵀ * A) = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => hA.eigenvalues i ^ 2) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
    have hd : Matrix.diagonal (fun i => hA.eigenvalues i ^ 2) =
        Matrix.diagonal hA.eigenvalues * Matrix.diagonal hA.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, hG, hd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star _) (hA.eigenvectorUnitary : Matrix n n ℝ), hU, Matrix.one_mul]
  have he := map_eigenvalues_eq_of_eq_mul_diagonal_mul_star
    (Matrix.isHermitian_conjTranspose_mul_self (Aᵀ * A)) _ _ h
  change Multiset.map (Real.sqrt ∘ _) _ = _
  rw [← Multiset.map_map, he, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  rw [Function.comp_apply, singularValue_sq]
  exact Real.sqrt_sq (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- `‖Aᵀ A‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem schattenNorm_transpose_mul_self {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℝ) :
    schattenNorm (q / 2) (Aᵀ * A) = schattenNorm q A ^ 2 := by
  have hmap := map_singularValue_transpose_mul_self A
  unfold schattenNorm
  by_cases ht : q = ⊤
  · have ht2 : q / 2 = ⊤ := by
      rw [ht]
      exact ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top
    rw [ite_eq_left ht2, ite_eq_left ht, iSup_eq_of_filter_map_eq (singularValue_nonneg _)
      (fun i => sq_nonneg _) (congrArg (Multiset.filter (· ≠ 0)) hmap),
      iSup_sq (singularValue_nonneg A)]
  · have ht2 : q / 2 ≠ ⊤ := ENNReal.div_ne_top ht two_ne_zero
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq ht
    have h2 : (q / 2).toReal = q.toReal / 2 := by
      rw [ENNReal.toReal_div]
      norm_num
    rw [ite_eq_right ht2, ite_eq_right ht, h2,
      sum_comp_eq_of_map_eq hmap (fun x => x ^ (q.toReal / 2))]
    have hpow : ∀ i, (singularValue A i ^ 2) ^ (q.toReal / 2) = singularValue A i ^ q.toReal :=
      fun i => by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (singularValue_nonneg A i)]
        congr 1
        push_cast
        ring
    simp only [hpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _)]
    congr 1
    push_cast
    field_simp

/-- Invariance under orthogonal conjugation: `‖U A Uᵀ‖_{S_q} = ‖A‖_{S_q}`. -/
theorem schattenNorm_conj {U : Matrix n n ℝ} (hU : U ∈ Matrix.orthogonalGroup n ℝ) (q : ℝ≥0∞)
    (A : Matrix n n ℝ) : schattenNorm q (U * A * Uᵀ) = schattenNorm q A := by
  have hUU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).1 hU
  refine schattenNorm_eq_of_X_pow_mul_charpoly_eq (a := 0) (b := 0) ?_ q
  simp only [pow_zero, one_mul]
  have h : (U * A * Uᵀ)ᵀ * (U * A * Uᵀ) = U * (Aᵀ * A) * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul]
  rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

/-- The Schatten norms decrease in the exponent: `‖A‖_{S_r} ≤ ‖A‖_{S_q}` for `0 < q ≤ r`. -/
theorem schattenNorm_anti {q r : ℝ≥0∞} (hq : q ≠ 0) (hqr : q ≤ r) (A : Matrix m n ℝ) :
    schattenNorm r A ≤ schattenNorm q A := by
  unfold schattenNorm
  by_cases hr : r = ⊤
  · rw [ite_eq_left hr]
    split_ifs with hqt
    · exact le_rfl
    · have hp : 0 < q.toReal := ENNReal.toReal_pos hq hqt
      exact Real.iSup_le
        (fun j => le_sum_rpow_rpow_one_div (singularValue_nonneg A) hp (Finset.mem_univ j))
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValue_nonneg A i) _) _)
  · have hqt : q ≠ ⊤ := ne_top_of_le_ne_top hr hqr
    rw [ite_eq_right hr, ite_eq_right hqt]
    exact sum_rpow_rpow_one_div_anti _ (singularValue_nonneg A) (ENNReal.toReal_pos hq hqt)
      (ENNReal.toReal_mono hr hqr)

/-- The reverse comparison: `‖A‖_{S_q} ≤ (#n)^{1/q − 1/r} ‖A‖_{S_r}` for `0 < q ≤ r < ∞`. -/
theorem schattenNorm_le_card_rpow_mul {q r : ℝ} (hq : 0 < q) (hqr : q ≤ r) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A ≤
      (Fintype.card n : ℝ) ^ (1 / q - 1 / r) * schattenNorm (ENNReal.ofReal r) A := by
  simp only [schattenNorm, ENNReal.ofReal_ne_top, ite_false, ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofReal (hq.le.trans hqr)]
  rw [← Finset.card_univ]
  exact sum_rpow_rpow_one_div_le_card_mul _ (singularValue_nonneg A) hq hqr

end BanachProbability
