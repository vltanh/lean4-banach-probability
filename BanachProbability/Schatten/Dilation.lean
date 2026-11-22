module

public import BanachProbability.Schatten.Spectral
public import Mathlib.Data.Matrix.Block

/-!
# The Hermitian dilation

The dilation of `A ∈ ℝ^{m×n}` is the symmetric matrix `D (A) = [[0, A], [Aᵀ, 0]]` on `m ⊕ n`
(`dilation`, through `Matrix.fromBlocks`). It is linear, `D (A) D (B) = diag (A Bᵀ, Aᵀ B)`, and its
eigenvalues are `±s_i (A)` (and zeros): `‖D (A)‖_{S_q}^q = 2 ‖A‖_{S_q}^q`
(`schattenNorm_dilation_rpow`), since `D (A)² = diag (A Aᵀ, Aᵀ A)` is block diagonal and `A Aᵀ` and
`Aᵀ A` have the same nonzero eigenvalues. This is how statements about symmetric matrices pass to
all real matrices (Mackey–Jordan–Chen–Farrell–Tropp, Ann. Probab. 42 (2014), §8; Randrianantoanina,
J. Funct. Anal. 194 (2002), for martingales).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Hermitian dilation `D (A) = [[0, A], [Aᵀ, 0]]`. -/
def dilation (A : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks 0 A Aᵀ 0

/-- The dilation as a linear map. -/
def dilationLinearMap : Matrix m n ℝ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℝ where
  toFun := dilation
  map_add' A B := by
    simp [dilation, Matrix.fromBlocks_add]
  map_smul' c A := by
    simp [dilation, Matrix.fromBlocks_smul]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem dilation_isHermitian (A : Matrix m n ℝ) : (dilation A).IsHermitian := by
  simp [dilation, Matrix.IsHermitian, Matrix.fromBlocks_transpose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

omit [DecidableEq m] [DecidableEq n] in
theorem dilation_mul_dilation (A B : Matrix m n ℝ) :
    dilation A * dilation B = Matrix.fromBlocks (A * Bᵀ) 0 0 (Aᵀ * B) := by
  simp [dilation, Matrix.fromBlocks_multiply]

/-- `‖A Aᵀ‖_{S_q} = ‖Aᵀ A‖_{S_q}`: the two have the same nonzero eigenvalues. -/
theorem schattenNorm_mul_transpose_self (q : ENNReal) (A : Matrix m n ℝ) :
    schattenNorm q (A * Aᵀ) = schattenNorm q (Aᵀ * A) := by
  refine schattenNorm_eq_of_X_pow_mul_charpoly_eq (a := Fintype.card n) (b := Fintype.card m)
    ?_ q
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
    Matrix.charpoly_mul_comm' A (Aᵀ * A * Aᵀ)

/-- The eigenvalues of a block-diagonal symmetric matrix `diag (P, Q)` are those of `P` together
with those of `Q` (`χ (diag (P, Q)) = χ (P) χ (Q)`). -/
theorem map_eigenvalues_eq_add_of_eq_fromBlocks {M : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hM : M.IsHermitian) {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (h : M = Matrix.fromBlocks P 0 0 Q) :
    Multiset.map hM.eigenvalues Finset.univ.val =
      Multiset.map hP.eigenvalues Finset.univ.val +
        Multiset.map hQ.eigenvalues Finset.univ.val := by
  rw [map_eigenvalues_eq_roots_charpoly, map_eigenvalues_eq_roots_charpoly,
    map_eigenvalues_eq_roots_charpoly, h, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero P.charpoly_monic.ne_zero Q.charpoly_monic.ne_zero)]

/-- If `Mᵀ M = diag (Xᵀ X, Yᵀ Y)`, the singular values of `M` are those of `X` together with
those of `Y`. -/
private theorem sum_singularValue_eq_add_of_eq_fromBlocks {k k' l : Type*} [Fintype k]
    [Fintype k'] [Fintype l] {M : Matrix l (m ⊕ n) ℝ} {X : Matrix k m ℝ} {Y : Matrix k' n ℝ}
    (h : Mᴴ * M = Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y)) (F : ℝ → ℝ) :
    ∑ i, F (singularValue M i) = ∑ i, F (singularValue X i) + ∑ j, F (singularValue Y j) := by
  have := congrArg (fun s => (Multiset.map (fun x => F √x) s).sum)
    (map_eigenvalues_eq_add_of_eq_fromBlocks (Matrix.isHermitian_conjTranspose_mul_self M)
      (Matrix.isHermitian_conjTranspose_mul_self X) (Matrix.isHermitian_conjTranspose_mul_self Y)
      h)
  simpa only [singularValue, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Function.comp_def, ← Finset.sum_eq_multiset_sum] using this

/-- The Schatten norm of a block-diagonal matrix:
`‖diag (B, C)‖_{S_q}^q = ‖B‖_{S_q}^q + ‖C‖_{S_q}^q`. -/
theorem schattenNorm_fromBlocks_rpow {q : ℝ} (hq : 0 < q) (B : Matrix m m ℝ) (C : Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.fromBlocks B 0 0 C) ^ q =
      schattenNorm (ENNReal.ofReal q) B ^ q + schattenNorm (ENNReal.ofReal q) C ^ q := by
  rw [schattenNorm_ofReal_rpow hq, schattenNorm_ofReal_rpow hq, schattenNorm_ofReal_rpow hq]
  refine sum_singularValue_eq_add_of_eq_fromBlocks ?_ (fun x => x ^ q)
  simp [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]

/-- `‖D (A)‖_{S_q}^q = 2 ‖A‖_{S_q}^q` (Mackey–Jordan–Chen–Farrell–Tropp 2014, §8, (8.2)):
`D (A)ᵀ D (A) = D (A)² = diag (A Aᵀ, Aᵀ A)`, so the singular values of `D (A)` are those of `Aᵀ`
together with those of `A`, and `‖Aᵀ‖_{S_q} = ‖A‖_{S_q}`. -/
theorem schattenNorm_dilation_rpow {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) (dilation A) ^ q =
      2 * schattenNorm (ENNReal.ofReal q) A ^ q := by
  rw [two_mul]
  nth_rewrite 1 [← schattenNorm_transpose (ENNReal.ofReal q) A]
  rw [schattenNorm_ofReal_rpow hq, schattenNorm_ofReal_rpow hq, schattenNorm_ofReal_rpow hq]
  refine sum_singularValue_eq_add_of_eq_fromBlocks ?_ (fun x => x ^ q)
  rw [(dilation_isHermitian A).eq, dilation_mul_dilation]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]

/-- The singular values of `D (A)` above a level `s ≥ 0` are those of `A`, each counted twice. -/
theorem countAbove_dilation {s : ℝ} (hs : 0 ≤ s) (A : Matrix m n ℝ) :
    countAbove s (dilation A) = 2 * countAbove s A := by
  have h := sum_singularValue_eq_add_of_eq_fromBlocks (M := dilation A) (X := Aᵀ) (Y := A)
    (by rw [(dilation_isHermitian A).eq, dilation_mul_dilation]
        simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose])
    fun t => if s < t then 1 else 0
  rw [sum_comp_singularValue_transpose A (F := fun t => if s < t then 1 else 0)
    (ite_eq_right (not_lt.2 hs))] at h
  have h' : (countAbove s (dilation A) : ℝ) = countAbove s A + countAbove s A := by
    simpa only [countAbove, Finset.natCast_card_filter] using h
  rw [two_mul]
  exact_mod_cast h'

omit [DecidableEq m] [DecidableEq n] in
/-- The square function of a family of dilations is block diagonal:
`Σ_i D (x_i)² = diag (Σ_i x_i x_iᵀ, Σ_i x_iᵀ x_i)`. -/
theorem sum_dilation_mul_self {ι : Type*} (s : Finset ι) (x : ι → Matrix m n ℝ) :
    ∑ i ∈ s, dilation (x i) * dilation (x i) =
      Matrix.fromBlocks (∑ i ∈ s, x i * (x i)ᵀ) 0 0 (∑ i ∈ s, (x i)ᵀ * x i) := by
  simp only [dilation_mul_dilation]
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ih, Matrix.fromBlocks_add]
    simp only [add_zero]

end BanachProbability
