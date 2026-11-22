module

public import BanachProbability.KConvexity.Basic
public import BanachProbability.TypeTwo.Schatten
public import BanachProbability.Schatten.CubeDuality

/-!
# The Rademacher projection on `L^q (Ω; S_q)`

For `q ≥ 2` the Rademacher projection is bounded on `L^q (Ω; S_q)`, real matrices, with norm at most
`√(π/2) √(q + 1)`, uniformly in the size (`lpNorm_rademacherProj_schattenNorm_le`), and, by duality,
with the same norm on `L^{q'} (Ω; S_{q'})` for symmetric matrices
(`lpNorm_rademacherProj_schattenNorm_conj_le`). The proof is G. Pisier's, *Non-commutative
vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998), p. 106: by
averaging, the norm on `L_q (X)` is at most `K (L_q (X))`, the K-convexity constant of `L_q (X)`;
for `X = S_q` this is `K (S_q)`, because `ℓ_q (S_q)` embeds isometrically in `S_q` (block diagonal
matrices); and `K (S_q)` is at most the type 2 constant (here up to the factor `√(π/2)`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Block diagonal matrices: `‖diag (A_1, …, A_k)‖_{S_q}^q = Σ ‖A_i‖_{S_q}^q`. -/
theorem schattenNorm_blockDiagonal_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ}
    (hq : 0 < q) (A : ι → Matrix n n ℝ) :
    schattenNorm (ENNReal.ofReal q) (Matrix.blockDiagonal A) ^ q =
      ∑ i, schattenNorm (ENNReal.ofReal q) (A i) ^ q := by
  have hA : ∀ i, ((A i)ᴴ * A i).IsHermitian := fun i =>
    Matrix.isHermitian_conjTranspose_mul_self (A i)
  -- diagonalise each block
  set U : Matrix (n × ι) (n × ι) ℝ :=
    Matrix.blockDiagonal fun i => ((hA i).eigenvectorUnitary : Matrix n n ℝ) with hU
  have hUs : star U =
      Matrix.blockDiagonal fun i => star ((hA i).eigenvectorUnitary : Matrix n n ℝ) := by
    simp only [hU, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose]
  have hUU : U ∈ Matrix.unitaryGroup (n × ι) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, hUs, hU, ← Matrix.blockDiagonal_mul]
    simp only [Unitary.mul_star_self_of_mem (hA _).eigenvectorUnitary.2]
    exact Matrix.blockDiagonal_one
  set μ : n × ι → ℝ := fun x => (hA x.2).eigenvalues x.1 with hμ
  have hdiag : Matrix.diagonal μ =
      Matrix.blockDiagonal fun i => Matrix.diagonal (hA i).eigenvalues := by
    rw [Matrix.blockDiagonal_diagonal]
  have h : (Matrix.blockDiagonal A)ᴴ * Matrix.blockDiagonal A =
      (⟨U, hUU⟩ : Matrix.unitaryGroup (n × ι) ℝ) * Matrix.diagonal μ *
        star ((⟨U, hUU⟩ : Matrix.unitaryGroup (n × ι) ℝ) : Matrix (n × ι) (n × ι) ℝ) := by
    change _ = U * Matrix.diagonal μ * star U
    rw [hUs, hdiag, hU, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    exact eq_eigenvectorUnitary_mul_diagonal_mul_star (hA i)
  have h1 := sum_comp_eq_of_map_eq (map_eigenvalues_eq_of_eq_mul_diagonal_mul_star
    (Matrix.isHermitian_conjTranspose_mul_self (Matrix.blockDiagonal A)) ⟨U, hUU⟩ μ h)
    fun x => √x ^ q
  rw [schattenNorm_ofReal_rpow hq]
  simp only [schattenNorm_ofReal_rpow hq, singularValue]
  rw [h1, Fintype.sum_prod_type_right]

private theorem kcs_mul_comm (ε η : Fin N → Bool) : mul ε η = mul η ε := by
  funext k
  simp only [mul]
  cases ε k <;> cases η k <;> rfl

/-- The expectation `E_ω ε_k (ω) f (ω η) = η_k E (ε_k f)`, by translation invariance. -/
private theorem kcs_sum_translate {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : (Fin N → Bool) → V) (η : Fin N → Bool) (k : Fin N) :
    ∑ ω, coin (ω k) • f (mul ω η) = coin (η k) • ∑ ω, coin (ω k) • f ω := by
  rw [← Equiv.sum_comp ((scb_mul_involutive η).toPerm _) fun ω => coin (ω k) • f ω,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  change _ = coin (η k) • coin (mul η ω k) • f (mul η ω)
  rw [coin_mul_apply, smul_smul, ← mul_assoc, coin_mul_self, one_mul, kcs_mul_comm]

/-- **The Rademacher projection on `L^q (Ω; S_q)`**, `q ≥ 2` (Pisier (1998), p. 106). -/
theorem lpNorm_rademacherProj_schattenNorm_le {q : ℝ} (hq : 2 ≤ q)
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q f := by
  have hq0 : 0 < q := by linarith
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  have hs0 : ∀ A : Matrix n n ℝ, 0 ≤ schattenNorm (ENNReal.ofReal q) A :=
    fun A => schattenNorm_nonneg _ A
  -- `ℓ^q (Ω; S_q)` embeds isometrically in `S_q`
  let B : ((Fin N → Bool) → Matrix n n ℝ) →ₗ[ℝ]
      SchattenSpace (ENNReal.ofReal q) (n × (Fin N → Bool)) (n × (Fin N → Bool)) :=
    { toFun := fun G => SchattenSpace.ofMatrix (Matrix.blockDiagonal G)
      map_add' := fun G H => by rw [Matrix.blockDiagonal_add, map_add]
      map_smul' := fun c G => by rw [Matrix.blockDiagonal_smul, map_smul, RingHom.id_apply] }
  have hB : ∀ G : (Fin N → Bool) → Matrix n n ℝ,
      ‖B G‖ ^ q = ∑ η, schattenNorm (ENNReal.ofReal q) (G η) ^ q := fun G =>
    schattenNorm_blockDiagonal_rpow hq0 G
  -- the norm of the block diagonal of the translates `g (ω ·)`
  have hBg : ∀ (g : (Fin N → Bool) → Matrix n n ℝ) (ω : Fin N → Bool),
      ‖B fun η => g (mul ω η)‖ = ((2 : ℝ) ^ N) ^ (1 / q) *
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q g := fun g ω => by
    have h1 : ‖B fun η => g (mul ω η)‖ ^ q =
        2 ^ N * avg fun η => schattenNorm (ENNReal.ofReal q) (g η) ^ q := by
      rw [hB, ← avg_mul_left ω, avg, mul_div_cancel₀ _ (by positivity)]
    rw [SignCube.lpNorm, ← Real.mul_rpow (by positivity)
      (avg_nonneg fun _ => Real.rpow_nonneg (hs0 _) _), ← h1, one_div,
      Real.rpow_rpow_inv (norm_nonneg _) hq0.ne']
  have hL2 : ∀ g : (Fin N → Bool) → Matrix n n ℝ,
      SignCube.lpNorm (fun y => ‖y‖) 2 (fun ω => B fun η => g (mul ω η)) =
        ((2 : ℝ) ^ N) ^ (1 / q) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q g :=
    fun g => by
      conv_lhs => rw [SignCube.lpNorm]
      simp only [hBg]
      rw [avg_const, one_div 2, Real.rpow_rpow_inv (mul_nonneg (by positivity)
        (lpNorm_nonneg hs0 _ _)) two_ne_zero]
  -- the Rademacher projection of the block diagonal of the translates
  have hP : rademacherProj (fun ω => B fun η => f (mul ω η)) = fun ω => B fun η =>
      ∑ k, coin (mul ω η k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η', coin (η' k) • f η' := by
    funext ω
    simp only [rademacherProj, rademacherCoeff, ← map_smul, ← map_sum]
    congr 1
    funext η
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [kcs_sum_translate, coin_mul_apply, smul_comm ((2 : ℝ) ^ N)⁻¹ (coin (η k)), smul_smul]
  have hK := (isTypeTwoBound_schattenSpace (n := n × (Fin N → Bool)) hq).isKConvexBound
    (Real.sqrt_nonneg _) N fun ω => B fun η => f (mul ω η)
  rw [hP, hL2 f, hL2 fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η,
    mul_left_comm] at hK
  exact le_of_mul_le_mul_left hK (by positivity)

omit [DecidableEq n] in
/-- For the self-adjointness of the Rademacher projection:
`E tr ((Σ_k ε_k c_k) Y) = Σ_k tr (c_k E (ε_k Y))`. -/
private theorem kcs_avg_trace (c : Fin N → Matrix n n ℝ) (Y : (Fin N → Bool) → Matrix n n ℝ) :
    (avg fun ε => ((∑ k, coin (ε k) • c k) * Y ε).trace) =
      ∑ k, (c k * (((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • Y η)).trace := by
  simp only [avg, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Finset.mul_sum, smul_eq_mul, div_eq_inv_mul]
  exact Finset.sum_comm

/-- The Rademacher projection on `L^{q'} (Ω; S_{q'})`, `q ≥ 2`, by duality (Pisier (1998), p. 106).
-/
theorem lpNorm_rademacherProj_schattenNorm_conj_le {q q' : ℝ} (hq : 2 ≤ q)
    (hqq' : q.HolderConjugate q') (f : (Fin N → Bool) → Matrix n n ℝ)
    (hf : ∀ ε, (f ε).IsHermitian) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q'
        (fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
  have hPf : ∀ ε : Fin N → Bool,
      (∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η).IsHermitian := fun ε => by
    have : ∀ ε, (f ε)ᴴ = f ε := hf
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, this,
      star_trivial]
  obtain ⟨Y, -, hY, hY'⟩ := exists_avg_trace_mul_eq_lpNorm hqq'.symm _ hPf
  rw [← hY', kcs_avg_trace]
  have h1 : ∑ k, ((((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • f η) *
      (((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • Y η)).trace =
      avg fun ε => (f ε * ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • Y η).trace := by
    simp only [Matrix.trace_mul_comm (f _)]
    rw [kcs_avg_trace]
    exact Finset.sum_congr rfl fun k _ => Matrix.trace_mul_comm _ _
  rw [h1]
  have h0 := lpNorm_nonneg (fun A : Matrix n n ℝ => schattenNorm_nonneg (ENNReal.ofReal q') A) q' f
  calc (avg fun ε => (f ε * ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • Y η).trace)
      ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f *
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε => ∑ k, coin (ε k) • ((2 : ℝ) ^ N)⁻¹ • ∑ η, coin (η k) • Y η) :=
        (le_abs_self _).trans (abs_avg_trace_mul_le hqq'.symm _ _)
    _ ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f *
          (√(Real.pi / 2) * √(q + 1) * 1) := by
        refine mul_le_mul_of_nonneg_left ((lpNorm_rademacherProj_schattenNorm_le hq Y).trans ?_) h0
        exact mul_le_mul_of_nonneg_left hY (by positivity)
    _ = _ := by ring

end BanachProbability
