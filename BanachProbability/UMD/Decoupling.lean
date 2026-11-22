module

public import BanachProbability.UMD.Defs

/-!
# Decoupling of Paley–Walsh martingales in UMD spaces

For a Paley–Walsh martingale `Y_n = Σ_{k<n} ε_k ξ_k (ε)` with predictable `ξ` and an independent
copy `ε̃` of the signs, the decoupled sum `Ỹ_n = Σ_{k<n} ε̃_k ξ_k (ε)` satisfies
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`
(Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016), Proposition 4.2.3;
Cox–Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*, Electron.
Commun. Probab. 12 (2007), with the constant `β_{p,X}`, who credit the result for tangent
sequences to T. R. McConnell (1989) and, independently, P. Hitczenko, and the proof from the
definition used here to S. Montgomery-Smith).

The proof is the standard one from the definition. With `η_k = ε_k ε̃_k`, the map
`(ε, ε̃) ↦ (ε, η)` preserves the uniform measure (`SignCube.avg_mul_left`) and
`Σ ε̃_k ξ_k (ε) = Σ η_k ε_k ξ_k (ε)`. In the interleaved order `η₀, ε₀, η₁, ε₁, …` of the doubled
cube (`SignCube.interleave`), `A = Σ ε_k ξ_k (ε)` and `B = Σ ε_k (η_k ξ_k (ε))` are Paley–Walsh
martingales with increments at the `ε_k` steps only, and `η_k` is a predictable sign for the
`ε_k` step: `B` is the transform of `A` by the signs `η`, and `A` that of `B`. Both inequalities
follow, with the dyadic constant `UMD_p^Δ (X)`, hence with `UMD_p (X)`.

Since the dyadic constant is that of the space in which the `ξ_k` take values, the statement for a
subspace `V` (with the constant `UMD_p^Δ (V)`) is the statement for the normed space `V`.
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `L^p` norm `(E_ε E_{ε̃} ‖Σ_{k<n} ε̃_k ξ_k (ε)‖^p)^{1/p}` of the decoupled sum of a
predictable family `ξ`. -/
noncomputable def decoupledLpNorm {N : ℕ} (p : ℝ) (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) : ℝ :=
  avg (fun ε => avg fun ε' => ‖paleyWalsh (fun k _ => ξ k ε) n ε'‖ ^ p) ^ (1 / p)

/-! ### The doubled cube

A point `ω` of `Fin (N * 2) → Bool` is the interleaving of `(ε, η) = interleave.symm ω`: the
coordinate `2k` (`finProdFinEquiv (k, 0)`) is `η_k` and `2k + 1` (`finProdFinEquiv (k, 1)`) is
`ε_k`. -/

/-- The family on the doubled cube: `ζ_{2k+1} (ω) = ξ_k (ε)` and `ζ_{2k} = 0`. -/
private noncomputable def dblFam {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (i : Fin (N * 2))
    (ω : Fin (N * 2) → Bool) : X :=
  if (finProdFinEquiv.symm i).2 = 0 then 0 else ξ (finProdFinEquiv.symm i).1 (interleave.symm ω).1

/-- The signs on the doubled cube: `s_{2k+1} (ω) = η_k` and `s_{2k} = 1`. -/
private noncomputable def dblSign {N : ℕ} (i : Fin (N * 2)) (ω : Fin (N * 2) → Bool) : ℝ :=
  if (finProdFinEquiv.symm i).2 = 0 then 1
  else coin ((interleave.symm ω).2 (finProdFinEquiv.symm i).1)

private theorem interleave_symm_fst_apply {N : ℕ} (ω : Fin (N * 2) → Bool) (k : Fin N) :
    (interleave.symm ω).1 k = ω (finProdFinEquiv (k, 1)) := by
  conv_rhs => rw [← interleave.apply_symm_apply ω]
  rw [interleave_apply_odd]

private theorem interleave_symm_snd_apply {N : ℕ} (ω : Fin (N * 2) → Bool) (k : Fin N) :
    (interleave.symm ω).2 k = ω (finProdFinEquiv (k, 0)) := by
  conv_rhs => rw [← interleave.apply_symm_apply ω]
  rw [interleave_apply_even]

omit [NormedSpace ℝ X] in
private theorem dblFam_even {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (k : Fin N)
    (ω : Fin (N * 2) → Bool) : dblFam ξ (finProdFinEquiv (k, 0)) ω = 0 := by
  simp [dblFam, -finProdFinEquiv_symm_apply]

omit [NormedSpace ℝ X] in
private theorem dblFam_odd {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (k : Fin N)
    (ω : Fin (N * 2) → Bool) : dblFam ξ (finProdFinEquiv (k, 1)) ω = ξ k (interleave.symm ω).1 := by
  simp [dblFam, -finProdFinEquiv_symm_apply]

private theorem dblSign_odd {N : ℕ} (k : Fin N) (ω : Fin (N * 2) → Bool) :
    dblSign (finProdFinEquiv (k, 1)) ω = coin ((interleave.symm ω).2 k) := by
  simp [dblSign, -finProdFinEquiv_symm_apply]

/-- A Paley–Walsh sum on the doubled cube of a family vanishing at the even steps, at time `2n`,
is the sum of its odd steps `2k + 1`, `k < n`. -/
private theorem paleyWalsh_double {N : ℕ} {g : Fin (N * 2) → (Fin (N * 2) → Bool) → X}
    (hg : ∀ k ω, g (finProdFinEquiv (k, 0)) ω = 0) (n : ℕ) (ω : Fin (N * 2) → Bool) :
    paleyWalsh g (2 * n) ω = ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n),
      coin (ω (finProdFinEquiv (k, 1))) • g (finProdFinEquiv (k, 1)) ω := by
  unfold paleyWalsh
  rw [Finset.sum_filter, Finset.sum_filter, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_two, hg, smul_zero, ite_self, zero_add]
  refine if_congr ?_ rfl rfl
  simp only [finProdFinEquiv_apply_val, Fin.val_one]
  omega

omit [NormedSpace ℝ X] in
private theorem isPredictable_dblFam {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    (hξ : IsPredictable ξ) : IsPredictable (dblFam ξ) := by
  intro i ω ω' h
  obtain ⟨⟨k, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [dblFam, Equiv.symm_apply_apply]
  split_ifs with hb
  · rfl
  refine hξ k _ _ fun j hj => ?_
  rw [interleave_symm_fst_apply, interleave_symm_fst_apply]
  refine h _ ?_
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
  have := Fin.lt_def.mp hj
  simp only [Fin.val_one]
  omega

private theorem isPredictable_dblSign {N : ℕ} :
    IsPredictable (dblSign (N := N)) := by
  intro i ω ω' h
  obtain ⟨⟨k, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [dblSign, Equiv.symm_apply_apply]
  split_ifs with hb
  · rfl
  rw [interleave_symm_snd_apply, interleave_symm_snd_apply, h _ ?_]
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
  have : b.val ≠ 0 := fun h0 => hb (Fin.ext h0)
  simp only [Fin.val_zero]
  omega

private theorem dblSign_eq {N : ℕ} (i : Fin (N * 2)) (ω : Fin (N * 2) → Bool) :
    dblSign i ω = 1 ∨ dblSign i ω = -1 := by
  unfold dblSign
  split_ifs
  · exact Or.inl rfl
  · exact coin_eq_one_or_eq_neg_one _

/-- On the doubled cube, `Σ_{i<2n} ω_i ζ_i (ω) = Σ_{k<n} ε_k ξ_k (ε)`. -/
private theorem paleyWalsh_dblFam {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ)
    (ω : Fin (N * 2) → Bool) :
    paleyWalsh (dblFam ξ) (2 * n) ω = paleyWalsh ξ n (interleave.symm ω).1 := by
  rw [paleyWalsh_double (dblFam_even ξ)]
  unfold paleyWalsh
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dblFam_odd, interleave_symm_fst_apply]

/-- On the doubled cube, `Σ_{i<2n} ω_i s_i (ω) ζ_i (ω) = Σ_{k<n} (ε η)_k ξ_k (ε)`. -/
private theorem paleyWalsh_dblSign_smul {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ)
    (ω : Fin (N * 2) → Bool) :
    paleyWalsh (fun i ω => dblSign i ω • dblFam ξ i ω) (2 * n) ω =
      paleyWalsh (fun k _ => ξ k (interleave.symm ω).1) n
        (mul (interleave.symm ω).1 (interleave.symm ω).2) := by
  rw [paleyWalsh_double fun k ω => by rw [dblFam_even, smul_zero]]
  unfold paleyWalsh
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dblFam_odd, dblSign_odd, smul_smul, coin_mul_apply, interleave_symm_fst_apply]

private theorem lpNorm_paleyWalsh_dblFam {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (p : ℝ)
    (n : ℕ) :
    SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (dblFam ξ) (2 * n)) =
      SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n) := by
  unfold SignCube.lpNorm
  simp only [paleyWalsh_dblFam]
  rw [avg_interleave (fun ε _ => ‖paleyWalsh ξ n ε‖ ^ p)]
  simp only [avg_const]

private theorem lpNorm_paleyWalsh_dblSign_smul {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X)
    (p : ℝ) (n : ℕ) :
    SignCube.lpNorm (fun x => ‖x‖) p
        (paleyWalsh (fun i ω => dblSign i ω • dblFam ξ i ω) (2 * n)) =
      decoupledLpNorm p ξ n := by
  unfold SignCube.lpNorm decoupledLpNorm
  simp only [paleyWalsh_dblSign_smul]
  rw [avg_interleave (fun ε η => ‖paleyWalsh (fun k _ => ξ k ε) n (mul ε η)‖ ^ p)]
  congr 2
  funext ε
  exact avg_mul_left ε fun η => ‖paleyWalsh (fun k _ => ξ k ε) n η‖ ^ p

/-- **Decoupling** of Paley–Walsh martingales with the dyadic UMD constant:
`‖Ỹ_n‖_{L^p} ≤ UMD_p^Δ ‖Y_n‖_{L^p}` and `‖Y_n‖_{L^p} ≤ UMD_p^Δ ‖Ỹ_n‖_{L^p}`. -/
theorem decoupling_dyadic {p : ℝ} (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X)
    (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        dyadicUMDConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        dyadicUMDConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  have hu := isDyadicUMDBound_dyadicUMDConst (X := X) (p := p) (by linarith)
  have hζ := isPredictable_dblFam hξ
  have hs := isPredictable_dblSign (N := N)
  constructor
  · -- the decoupled sum is the transform of `Y` by the predictable signs `s`
    have h := hu (N * 2) (dblFam ξ) dblSign hζ hs dblSign_eq (2 * n)
    rwa [lpNorm_paleyWalsh_dblSign_smul, lpNorm_paleyWalsh_dblFam] at h
  · -- `Y` is the transform of the decoupled sum by the same signs, since `s² = 1`
    have h := hu (N * 2) (fun i ω => dblSign i ω • dblFam ξ i ω) dblSign (hs.smul hζ) hs
      dblSign_eq (2 * n)
    have hss : (fun i ω => dblSign i ω • dblSign i ω • dblFam ξ i ω) = dblFam ξ := by
      funext i ω
      rw [smul_smul]
      rcases dblSign_eq i ω with h1 | h1 <;> simp [h1]
    rwa [hss, lpNorm_paleyWalsh_dblSign_smul, lpNorm_paleyWalsh_dblFam] at h

/-- **Decoupling** (Hytönen–van Neerven–Veraar–Weis I, Proposition 4.2.3; Cox–Veraar 2007) for
Paley–Walsh martingales in a Banach space, with the constant `UMD_p (X)`:
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`. -/
theorem decoupling [CompleteSpace X] {p : ℝ} (hp : 1 < p) {N : ℕ}
    (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ) (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) := by
  have h := decoupling_dyadic hp ξ hξ n
  have hle := dyadicUMDConst_le_umdConst (X := X) hp
  exact ⟨h.1.trans (by gcongr), h.2.trans (by gcongr)⟩

end BanachProbability
