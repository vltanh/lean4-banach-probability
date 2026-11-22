module

public import BanachProbability.KConvexity.Basic
public import BanachProbability.TypeTwo.Schatten
public import BanachProbability.Schatten.CubeDuality
import BanachProbability.Schatten.Block

/-!
# The Rademacher projection on `L^q (Ω; S_q)`

For `q ≥ 2` the Rademacher projection (real signs) is bounded on `L^q (Ω; S_q)`, real square
matrices, with norm at most `√(π/2) √(q + 1)`, uniformly in the size
(`lpNorm_rademacherProj_schattenNorm_le`), and, by duality, with the same bound on
`L^{q'} (Ω; S_{q'})` (`lpNorm_rademacherProj_schattenNorm_conj_le`). The proof is G. Pisier's,
*Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998),
p. 106, for the projection `P_1 ⊗ I_X`, `X = S_q`: by averaging, its norm on `L_q (X)` is at most
`K (L_q (X))`, the K-convexity constant of `L_q (X)`; this is `K (S_q)`, because `ℓ_q (S_q)` embeds
isometrically in `S_q` (block diagonal matrices); and `K (S_q)` is dominated by the type 2 constant
(here up to the factor `√(π/2)`). The second statement is implicit there: Pisier uses the duality
only with (8.4.4), the noncommutative Khintchine inequality for `1 ≤ p ≤ 2`, to get the inequality
for `p ≥ 2`. Here it follows from `E tr (Yᵀ π_N f) = E tr ((π_N Y)ᵀ f)` and the isometric duality of
`L^q (Ω; S_q)` and `L^{q'} (Ω; S_{q'})`, `BanachProbability.Schatten.CubeDuality`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of sign vectors is commutative. -/
private theorem kcs_mul_comm (ε η : Fin N → Bool) : mul ε η = mul η ε := by
  funext k
  simp only [mul]
  cases ε k <;> cases η k <;> rfl

/-- `E_ω ω_k f (ω η) = η_k E_ω ω_k f (ω)`, by translation invariance (stated for the sums over the
cube). -/
private theorem kcs_sum_translate {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : (Fin N → Bool) → V) (η : Fin N → Bool) (k : Fin N) :
    ∑ ω, coin (ω k) • f (mul ω η) = coin (η k) • ∑ ω, coin (ω k) • f ω := by
  rw [← Equiv.sum_comp ((scb_mul_involutive η).toPerm _) fun ω => coin (ω k) • f ω,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  change _ = coin (η k) • coin (mul η ω k) • f (mul η ω)
  rw [coin_mul_apply, smul_smul, ← mul_assoc, coin_mul_self, one_mul, kcs_mul_comm]

/-- **The Rademacher projection on `L^q (Ω; S_q)`**, `q ≥ 2` (Pisier (1998), p. 106): its norm is at
most `√(π/2) √(q + 1)`. -/
theorem lpNorm_rademacherProj_schattenNorm_le {q : ℝ} (hq : 2 ≤ q)
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (rademacherProj f) ≤
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
  have hP : rademacherProj (fun ω => B fun η => f (mul ω η)) =
      fun ω => B fun η => rademacherProj f (mul ω η) := by
    funext ω
    simp only [rademacherProj, rademacherCoeff, ← map_smul, ← map_sum]
    congr 1
    funext η
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [kcs_sum_translate, coin_mul_apply, smul_comm ((2 : ℝ) ^ N)⁻¹ (coin (η k)), smul_smul]
  have hK := (isTypeTwoBound_schattenSpace (n := n × (Fin N → Bool)) hq).isKConvexBound N
    fun ω => B fun η => f (mul ω η)
  rw [hP, hL2 f, hL2 (rademacherProj f), mul_left_comm] at hK
  exact le_of_mul_le_mul_left hK (by positivity)

omit [DecidableEq n] in
/-- `E tr ((Σ_k ε_k c_k) Y) = Σ_k tr (c_k E (ε_k Y))`. -/
theorem avg_trace_sum_coin_smul_mul (c : Fin N → Matrix n n ℝ)
    (Y : (Fin N → Bool) → Matrix n n ℝ) :
    (avg fun ε => ((∑ k, coin (ε k) • c k) * Y ε).trace) =
      ∑ k, (c k * rademacherCoeff Y k).trace := by
  simp only [rademacherCoeff, avg, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum, smul_eq_mul, div_eq_inv_mul]
  exact Finset.sum_comm

omit [DecidableEq n] in
/-- The Rademacher projection is self-adjoint for the trace duality:
`E tr ((π_N f) Y) = E tr (f (π_N Y))`. -/
private theorem kcs_avg_trace_comm (f Y : (Fin N → Bool) → Matrix n n ℝ) :
    (avg fun ε => (rademacherProj f ε * Y ε).trace) =
      avg fun ε => (f ε * rademacherProj Y ε).trace := by
  simp only [Matrix.trace_mul_comm (f _)]
  refine (avg_trace_sum_coin_smul_mul (rademacherCoeff f) Y).trans
    (Eq.trans ?_ (avg_trace_sum_coin_smul_mul (rademacherCoeff Y) f).symm)
  exact Finset.sum_congr rfl fun k _ => Matrix.trace_mul_comm _ _

/-- The Rademacher projection on `L^{q'} (Ω; S_{q'})`, `q ≥ 2`, by duality (it is implicit in Pisier
(1998), p. 106, where the duality is used only with (8.4.4)). -/
theorem lpNorm_rademacherProj_schattenNorm_conj_le {q q' : ℝ} (hq : 2 ≤ q)
    (hqq' : q.HolderConjugate q') (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
  obtain ⟨Y, hY, hY'⟩ := exists_avg_trace_transpose_mul_eq_lpNorm hqq'.symm (rademacherProj f)
  -- `E tr (Yᵀ π_N f) = E tr ((π_N Y)ᵀ f)`
  have hP : ∀ ε, rademacherProj (fun ε => (Y ε)ᵀ) ε = (rademacherProj Y ε)ᵀ := fun ε => by
    simp only [rademacherProj, rademacherCoeff, Matrix.transpose_sum, Matrix.transpose_smul]
  rw [← hY', ← kcs_avg_trace_comm fun ε => (Y ε)ᵀ]
  simp only [hP]
  have h0 := lpNorm_nonneg (fun A : Matrix n n ℝ => schattenNorm_nonneg (ENNReal.ofReal q') A) q' f
  calc (avg fun ε => ((rademacherProj Y ε)ᵀ * f ε).trace)
      ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (fun ε => (rademacherProj Y ε)ᵀ) *
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f :=
        (le_abs_self _).trans (abs_avg_trace_mul_le hqq' _ _)
    _ = SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (rademacherProj Y) *
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
        simp only [SignCube.lpNorm, schattenNorm_transpose]
    _ ≤ √(Real.pi / 2) * √(q + 1) * 1 *
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' f := by
        refine mul_le_mul_of_nonneg_right ((lpNorm_rademacherProj_schattenNorm_le hq Y).trans ?_) h0
        exact mul_le_mul_of_nonneg_left hY (by positivity)
    _ = _ := by rw [mul_one]

end BanachProbability
