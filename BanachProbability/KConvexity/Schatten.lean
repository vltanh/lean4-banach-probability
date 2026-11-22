module

public import BanachProbability.KConvexity.Basic
public import BanachProbability.TypeTwo.Schatten
public import BanachProbability.Schatten.CubeDuality
import BanachProbability.Schatten.Block

/-!
# The Rademacher projection on `L^q (Ω; S_q)`

Let `Ω = {±1}^N` be the sign cube, with the uniform probability. For `q ≥ 2` the Rademacher
projection (real signs) is bounded on `L^q (Ω; S_q)`, real square matrices, with norm at most
`√(π/2) √(q + 1)`, uniformly in `N` and in the size (`lpNorm_rademacherProj_schattenNorm_le`), and,
by duality, with the same bound on `L^{q'} (Ω; S_{q'})`
(`lpNorm_rademacherProj_schattenNorm_conj_le`). The proof is G. Pisier's, *Non-commutative vector
valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998), p. 106, for the
projection `P_1 ⊗ I_X`, `X = S_q`:

1. averaging: for every normed space `X`, its norm on `L_p (X)` is at most `K (L_p (X))`, the
   K-convexity constant, in `L²`, of `L_p (X)` (`isKConvexBound_of_piLp`);
2. `K (L_q (S_q)) = K (S_q)`, because `ℓ_q (S_q)` embeds isometrically in `S_q`, by block diagonal
   matrices (`schattenBlockDiagonal`), and the K-convexity constant of a subspace is at most that of
   the space (`IsKConvexBound.of_linearIsometry`); only `≤` is needed;
3. `K (S_q)` is dominated by the type 2 constant of `S_q`, here up to the factor `√(π/2)`
   (`IsTypeTwoBound.isKConvexBound`), and this is of order `√q`, by Tomczak-Jaegermann's theorem;
   `√(q + 1)` is the bound for it in `isTypeTwoBound_schattenSpace`.

The second statement is implicit there: Pisier uses the duality only with (8.4.4), the
noncommutative Khintchine inequality for `1 ≤ p ≤ 2`, to get the inequality for `p ≥ 2`. Here it
follows from `E tr (Yᵀ π_N f) = E tr ((π_N Y)ᵀ f)` and the isometric duality of `L^q (Ω; S_q)` and
`L^{q'} (Ω; S_{q'})`, `BanachProbability.Schatten.CubeDuality`.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

/-! ### Averaging, and subspaces -/

section General

variable {N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p K : ℝ}

/-- `E_ω ω_k f (ω η) = η_k E_ω ω_k f (ω)`, by translation invariance (stated for the sums over the
cube). -/
private theorem kcs_sum_translate (f : (Fin N → Bool) → X) (η : Fin N → Bool) (k : Fin N) :
    ∑ ω, coin (ω k) • f (mul ω η) = coin (η k) • ∑ ω, coin (ω k) • f ω := by
  rw [← Equiv.sum_comp ((scb_mul_involutive η).toPerm _) fun ω => coin (ω k) • f ω,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hc : mul ω η = mul η ω := funext fun _ => Bool.beq_comm
  change _ = coin (η k) • coin (mul η ω k) • f (mul η ω)
  rw [coin_mul_apply, smul_smul, ← mul_assoc, coin_mul_self, one_mul, hc]

/-- The first step of the source (Pisier (1998), p. 106, "by a standard averaging technique"): the
norm of the Rademacher projection on `L_p (Ω; X)` is at most the K-convexity constant, in `L²`, of
the spaces `L_p (Ω; X)`. These are taken with the counting measure on `Ω = {±1}^M`, as the constant
does not depend on the normalisation. The projection is applied to the function `ω ↦ f (ω ·)` with
values in `L_p (Ω; X)`, whose norm does not depend on `ω`. -/
theorem isKConvexBound_of_piLp [Fact (1 ≤ ENNReal.ofReal p)]
    (h : ∀ M : ℕ, IsKConvexBound (PiLp (ENNReal.ofReal p) fun _ : Fin M → Bool => X) 2 K) :
    IsKConvexBound X p K := by
  intro N f
  have hp : 0 < p := zero_lt_one.trans_le (ENNReal.one_le_ofReal.1 Fact.out)
  set F : ((Fin N → Bool) → X) → (Fin N → Bool) →
      PiLp (ENNReal.ofReal p) fun _ : Fin N → Bool => X := fun g ω =>
    WithLp.toLp _ fun η => g (mul ω η) with hFdef
  -- `‖g (ω ·)‖ = 2^{N/p} ‖g‖_{L^p}`
  have hF : ∀ g ω, ‖F g ω‖ = ((2 : ℝ) ^ N) ^ (1 / p) * SignCube.lpNorm (fun y => ‖y‖) p g :=
    fun g ω => by
      have h1 : ∑ η, ‖g (mul ω η)‖ ^ p = 2 ^ N * avg fun η => ‖g η‖ ^ p := by
        rw [← avg_mul_left ω, avg, mul_div_cancel₀ _ (by positivity)]
      rw [PiLp.norm_eq_sum (by rwa [ENNReal.toReal_ofReal hp.le]), ENNReal.toReal_ofReal hp.le, h1,
        Real.mul_rpow (by positivity) (avg_nonneg fun _ => by positivity), SignCube.lpNorm]
  have hL2 : ∀ g, SignCube.lpNorm (fun y => ‖y‖) 2 (F g) =
      ((2 : ℝ) ^ N) ^ (1 / p) * SignCube.lpNorm (fun y => ‖y‖) p g := fun g => by
    conv_lhs => rw [SignCube.lpNorm]
    simp only [hF]
    rw [avg_const, one_div 2, Real.rpow_rpow_inv (mul_nonneg (by positivity)
      (lpNorm_nonneg (fun _ => norm_nonneg _) _ _)) two_ne_zero]
  -- the projection of `ω ↦ f (ω ·)` is `ω ↦ (π_N f) (ω ·)`
  have hP : rademacherProj (F f) = F (rademacherProj f) := by
    funext ω
    ext η
    simp only [hFdef, rademacherProj, rademacherCoeff, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [kcs_sum_translate, coin_mul_apply, smul_comm ((2 : ℝ) ^ N)⁻¹ (coin (η k)), smul_smul]
  have hK := h N N (F f)
  rw [hP, hL2, hL2, mul_left_comm] at hK
  exact le_of_mul_le_mul_left hK (by positivity)

/-- The K-convexity constant of a space that embeds isometrically in `Y` is at most that of `Y`
(Pisier (1998), p. 106, for `ℓ_p (S_p)` and `S_p`). -/
theorem IsKConvexBound.of_linearIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (h : IsKConvexBound Y p K) (T : X →ₗᵢ[ℝ] Y) : IsKConvexBound X p K := by
  intro N f
  have hT : rademacherProj (fun ε => T (f ε)) = fun ε => T (rademacherProj f ε) := by
    funext ε
    simp only [rademacherProj, rademacherCoeff, map_sum, map_smul]
  simpa only [hT, SignCube.lpNorm, T.norm_map] using h N fun ε => T (f ε)

end General

/-! ### The Schatten classes -/

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Rademacher projection on `L^q (Ω; S_q)`**, `q ≥ 2` (Pisier (1998), p. 106): its norm is at
most `√(π/2) √(q + 1)`. -/
theorem lpNorm_rademacherProj_schattenNorm_le {q : ℝ} (hq : 2 ≤ q)
    (f : (Fin N → Bool) → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q (rademacherProj f) ≤
      √(Real.pi / 2) * √(q + 1) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q f := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  -- `K (S_q) ≤ √(π/2) √(q + 1)`, for matrices of every size, and `ℓ_q (S_q)` embeds in `S_q`
  have h : IsKConvexBound (SchattenSpace (ENNReal.ofReal q) n n) q (√(Real.pi / 2) * √(q + 1)) :=
    isKConvexBound_of_piLp fun M => (isTypeTwoBound_schattenSpace
      (n := n × (Fin M → Bool)) hq).isKConvexBound.of_linearIsometry (schattenBlockDiagonal q)
  exact h N f

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
