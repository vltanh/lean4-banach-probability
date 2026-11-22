module

public import BanachProbability.Schatten.Horn
public import BanachProbability.Schatten.Space
public import BanachProbability.Noncommutative.SchattenUMD

/-!
# Schatten norms of complex matrices

For a complex `m × n` matrix `A`, the singular values `s_i (A) = √λ_i (Aᴴ A)`, `i : n`, and the
Schatten `q`-norm `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}`, `max_i s_i` for `q = ∞` (`complexSchattenNorm`),
as in the real case (`schattenNorm`). With the *realification*
`realify A = [[Re A, −Im A], [Im A, Re A]]`, a real `2m × 2n` matrix, every singular value of `A`
occurs twice, so `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}` (`complexSchattenNorm_eq_realify`), and
the facts about real Schatten norms carry over: norm axioms, adjoints,
`‖Aᴴ A‖_{S_{q/2}} = ‖A‖_{S_q}²`, Hölder's inequality. `ComplexSchattenSpace q m n` is the resulting
complex normed space; as a real space it embeds isometrically in `SchattenSpace q (m ⊕ m) (n ⊕ n)`,
so its UMD constants are at most those of the real space (`umdConst_complexSchattenSpace_le`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-! ### Realification -/

/-- The realification `[[Re A, −Im A], [Im A, Re A]]` of a complex matrix. -/
def realify (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-A.map Complex.im) (A.map Complex.im) (A.map Complex.re)

omit [Fintype m] [Fintype n] in
theorem realify_add (A B : Matrix m n ℂ) : realify (A + B) = realify A + realify B := by
  sorry

omit [Fintype m] [Fintype n] in
theorem realify_smul (c : ℝ) (A : Matrix m n ℂ) : realify (c • A) = c • realify A := by
  sorry

omit [Fintype l] [Fintype n] in
theorem realify_mul (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    realify (A * B) = realify A * realify B := by
  sorry

omit [Fintype m] [Fintype n] in
theorem realify_conjTranspose (A : Matrix m n ℂ) : realify Aᴴ = (realify A)ᵀ := by
  sorry

omit [Fintype m] [Fintype n] in
theorem realify_injective : Function.Injective (realify : Matrix m n ℂ → _) := by
  sorry

omit [Fintype n] in
theorem realify_one [DecidableEq n] : realify (1 : Matrix n n ℂ) = 1 := by
  sorry

/-! ### Schatten norms -/

section Norm

variable [DecidableEq n]

/-- The singular values of `A ∈ ℂ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᴴ A)`. -/
noncomputable def complexSingularValue (A : Matrix m n ℂ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm of a complex matrix: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`,
`‖A‖_{S_∞} = max_i s_i`. -/
noncomputable def complexSchattenNorm (q : ℝ≥0∞) (A : Matrix m n ℂ) : ℝ :=
  if q = ⊤ then ⨆ i, complexSingularValue A i
  else (∑ i, complexSingularValue A i ^ q.toReal) ^ (1 / q.toReal)

/-- `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}`: the realification has every singular value twice. -/
theorem complexSchattenNorm_eq_realify {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℂ) :
    complexSchattenNorm q A = (2 : ℝ) ^ (-(1 / q.toReal)) * schattenNorm q (realify A) := by
  sorry

/-- A real matrix has the same Schatten norms as a complex one. -/
theorem complexSchattenNorm_map_ofReal {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℝ) :
    complexSchattenNorm q (A.map Complex.ofReal) = schattenNorm q A := by
  sorry

theorem complexSchattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n ℂ) : 0 ≤ complexSchattenNorm q A := by
  sorry

theorem complexSchattenNorm_eq_zero_iff {q : ℝ≥0∞} (hq : q ≠ 0) {A : Matrix m n ℂ} :
    complexSchattenNorm q A = 0 ↔ A = 0 := by
  sorry

theorem complexSchattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : ℂ) (A : Matrix m n ℂ) :
    complexSchattenNorm q (c • A) = ‖c‖ * complexSchattenNorm q A := by
  sorry

theorem complexSchattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n ℂ) :
    complexSchattenNorm q (A + B) ≤ complexSchattenNorm q A + complexSchattenNorm q B := by
  sorry

theorem complexSchattenNorm_conjTranspose [DecidableEq m] (q : ℝ≥0∞) (A : Matrix m n ℂ) :
    complexSchattenNorm q Aᴴ = complexSchattenNorm q A := by
  sorry

/-- `‖Aᴴ A‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem complexSchattenNorm_conjTranspose_mul_self {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n ℂ) :
    complexSchattenNorm (q / 2) (Aᴴ * A) = complexSchattenNorm q A ^ 2 := by
  sorry

/-- `‖A Aᴴ‖_{S_{q/2}} = ‖A‖_{S_q}²`. -/
theorem complexSchattenNorm_mul_conjTranspose_self [DecidableEq m] {q : ℝ≥0∞} (hq : q ≠ 0)
    (A : Matrix m n ℂ) : complexSchattenNorm (q / 2) (A * Aᴴ) = complexSchattenNorm q A ^ 2 := by
  sorry

/-- **Hölder's inequality** (HNVW I, Corollary D.2.4): `‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`,
`1/p = 1/q + 1/r`. -/
theorem complexSchattenNorm_mul_le [DecidableEq m] {p q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / p = 1 / q + 1 / r) (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) (A * B) ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal r) B := by
  sorry

/-- `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`, `1/q + 1/q' = 1`. -/
theorem norm_trace_mul_le [DecidableEq m] {q q' : ℝ} (hq : q.HolderConjugate q')
    (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    ‖(A * B).trace‖ ≤
      complexSchattenNorm (ENNReal.ofReal q) A * complexSchattenNorm (ENNReal.ofReal q') B := by
  sorry

/-- If `A = U diag (c) Vᴴ` with `U`, `V` unitary and `c_i ∈ ℂ`, then
`‖A‖_{S_q} = (Σ_i |c_i|^q)^{1/q}`. -/
theorem complexSchattenNorm_unitary_mul_diagonal_mul {q : ℝ} (hq : 0 < q)
    {U V : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (c : n → ℂ) :
    complexSchattenNorm (ENNReal.ofReal q) (U * Matrix.diagonal c * Vᴴ) =
      (∑ i, ‖c i‖ ^ q) ^ (1 / q) := by
  sorry

/-- `‖A‖_{S_q}^q = Σ_i |λ_i|^q` for a Hermitian matrix. -/
theorem complexSchattenNorm_rpow_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) {q : ℝ}
    (hq : 0 < q) :
    complexSchattenNorm (ENNReal.ofReal q) A ^ q = ∑ i, |hA.eigenvalues i| ^ q := by
  sorry

theorem continuous_complexSchattenNorm {q : ℝ≥0∞} (hq : 1 ≤ q) :
    Continuous (complexSchattenNorm q : Matrix m n ℂ → ℝ) := by
  sorry

end Norm

/-! ### The normed space -/

/-- The complex `m × n` matrices with the Schatten `q`-norm. -/
def ComplexSchattenSpace (_q : ℝ≥0∞) (m n : Type*) : Type _ := Matrix m n ℂ

namespace ComplexSchattenSpace

variable {q : ℝ≥0∞}

instance {m n : Type*} : AddCommGroup (ComplexSchattenSpace q m n) :=
  inferInstanceAs (AddCommGroup (Matrix m n ℂ))

instance {m n : Type*} : Module ℂ (ComplexSchattenSpace q m n) :=
  inferInstanceAs (Module ℂ (Matrix m n ℂ))

/-- The identity map `Matrix m n ℂ → ComplexSchattenSpace q m n`, as a linear equivalence. -/
def ofMatrix {m n : Type*} : Matrix m n ℂ ≃ₗ[ℂ] ComplexSchattenSpace q m n := LinearEquiv.refl ℂ _

instance {m n : Type*} [Finite m] [Finite n] : FiniteDimensional ℂ (ComplexSchattenSpace q m n) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix m n ℂ))

variable [DecidableEq n]

noncomputable instance : Norm (ComplexSchattenSpace q m n) :=
  ⟨fun A => complexSchattenNorm q (ofMatrix.symm A)⟩

theorem norm_def (A : ComplexSchattenSpace q m n) : ‖A‖ = complexSchattenNorm q (ofMatrix.symm A) :=
  rfl

@[simp] theorem norm_ofMatrix (A : Matrix m n ℂ) :
    ‖(ofMatrix A : ComplexSchattenSpace q m n)‖ = complexSchattenNorm q A := rfl

theorem normedSpaceCore [hq : Fact (1 ≤ q)] :
    NormedSpace.Core ℂ (ComplexSchattenSpace q m n) where
  norm_nonneg A := complexSchattenNorm_nonneg q _
  norm_smul c A := by
    rw [norm_def, norm_def, map_smul, complexSchattenNorm_smul (zero_lt_one.trans_le hq.out).ne']
  norm_triangle A B := by
    rw [norm_def, norm_def, norm_def, map_add]
    exact complexSchattenNorm_add_le hq.out _ _
  norm_eq_zero_iff A := by
    rw [norm_def, complexSchattenNorm_eq_zero_iff (zero_lt_one.trans_le hq.out).ne',
      LinearEquiv.map_eq_zero_iff]

noncomputable instance [Fact (1 ≤ q)] : NormedAddCommGroup (ComplexSchattenSpace q m n) :=
  NormedAddCommGroup.ofCore normedSpaceCore

noncomputable instance [Fact (1 ≤ q)] : NormedSpace ℂ (ComplexSchattenSpace q m n) :=
  NormedSpace.ofCore normedSpaceCore

instance [Fact (1 ≤ q)] : CompleteSpace (ComplexSchattenSpace q m n) :=
  FiniteDimensional.complete ℂ _

end ComplexSchattenSpace

/-- The complex Schatten space embeds isometrically, over `ℝ`, in the real Schatten space of twice
the size (`A ↦ 2^{−1/q} realify A`), so its UMD constants are at most those of the real space. -/
theorem umdConst_complexSchattenSpace_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : Type*) [Fintype n]
    [DecidableEq n] (p : ℝ) :
    umdConst (ComplexSchattenSpace q n n) p ≤ umdConst (SchattenSpace q (n ⊕ n) (n ⊕ n)) p := by
  sorry

/-- **`UMD₂` of the complex Schatten classes**: there is `C` such that
`UMD₂ (S_q) ≤ C (q* − 1)` for all `1 < q < ∞` and all sizes. -/
theorem umdConst_two_complexSchattenSpace_le : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (ComplexSchattenSpace q n n) 2 ≤ ENNReal.ofReal (C * (pStar q.toReal - 1)) := by
  sorry

end BanachProbability
