module

public import BanachProbability.UMD.ConvexHull
public import BanachProbability.ZigZag.Concave

/-!
# Burkholder's zig-zag concave function

The construction of a zig-zag concave function from the dyadic UMD property: the proof of
Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016) (HNVW), Theorem 4.5.6,
(2)⇒(3), p. 334–337 (Burkholder). The scalars are `𝕜 = ℝ` or `ℂ`, `1 ≤ p < ∞`, and `β ≥ 0` is a
dyadic `UMD_p` constant of `X` for the signs of `𝕜` (`IsSignDyadicUMDBound`); the best one,
`β = β^Δ_{p,X}`, is allowed, as in the book. With `F (x, y) = ‖y‖^p − β^p ‖x‖^p`, (4.35), let
`V (x, y)` (`bellmanValues`) be the set of the averages `E F (f_∞, g_∞)` over the pairs of
Paley–Walsh martingales `f = x + Σ ε_k ξ_k`, `g = y + Σ λ_k ε_k ξ_k` with *constants* `λ_k`,
and `U (x, y) = sup V (x, y)`.

* Step 1: `V (ε x, ε' y) = V (x, y)` for signs `ε`, `ε'` (`bellmanValues_smul`), and
  `F (x, y) ∈ V (x, y)` (`mem_bellmanValues_self`).
* Step 2: if `v_i ∈ V (x_i, y_i)` and `y_1 − y_2 = e (x_1 − x_2)`, then `(v_1 + v_2) / 2` is in `V`
  at the midpoint (`add_div_two_mem_bellmanValues`): the first sign decides which of the two pairs
  is followed, and the two pairs run on the even and on the odd ones of the remaining signs, so
  that the multipliers of the spliced pair are again constants. Hence `U` is midpoint zig-zag
  concave.
* Step 3: `U (0, 0) ≤ 0` by the dyadic UMD property, `U (x, x) ≤ 0`, and `U (x, y) + U (y, x) ≤ 0`
  by zig-zag concavity along `ε = −1` (`nonpos_of_mem_bellmanValues_zero`,
  `nonpos_of_mem_bellmanValues_self`, `add_nonpos_of_mem_bellmanValues`), so that `U < ∞`.
* Hence `U` is zig-zag concave by Lemma 4.5.2 (`concaveOn_sSup_bellmanValues`).

Two departures from the source. First, the multipliers `λ_k` are constants in the closed unit ball
of `𝕜`, not only signs, as in I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms
in infinite dimensions*, Indag. Math. 29 (2018), Proposition 3.7 (with his set `A` of scalars the
closed unit ball): `U` is then concave along `z ↦ (x + z, y + e z)` for all `‖e‖ ≤ 1`, as
`IsZigZagConcave` asks, and the argument is the same but for the bound `U (0, 0) ≤ 0`, where the
dyadic UMD property passes from signs to the unit ball by convexity (HNVW, Proposition 3.2.14).
Second, the order of the last steps: the source applies Lemma 4.5.2, which is stated for real-valued
functions, in Step 2, where `U` may still be `+∞`, and proves finiteness in Step 3; here midpoint
concavity comes first, then finiteness, which only uses midpoint concavity, and then Lemma 4.5.2.
To this end Steps 2 and 3 are phrased with the sets `V (x, y)` in place of their suprema.
-/

@[expose] public section

open scoped Topology

namespace BanachProbability

open SignCube

section Defs

variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]

/-- The dyadic UMD property in HNVW's form (Theorem 4.5.6 (2), p. 332) with constant `β`: transforms
of Paley–Walsh martingales by *deterministic* signs `l_k ∈ 𝕜`, `‖l_k‖ = 1`, satisfy
`‖Σ l_k ε_k ξ_k‖_p ≤ β ‖Σ ε_k ξ_k‖_p`. -/
def IsSignDyadicUMDBound (p β : ℝ) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (l : Fin N → 𝕜), IsPredictable ξ →
    (∀ k, ‖l k‖ = 1) →
      SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => l k • ξ k ε) N) ≤
        β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N)

variable {X}

/-- `V (x, y)`: the values `E [‖g_∞‖^p − β^p ‖f_∞‖^p]` of the pairs of Paley–Walsh martingales
`f = x + Σ ε_k ξ_k`, `g = y + Σ l_k ε_k ξ_k` (on any number of signs), `ξ` predictable, with
constants `l_k ∈ 𝕜`, `‖l_k‖ ≤ 1` (HNVW I, p. 334, where the pairs form the class `S (x, y)` and the
`l_k` are signs). -/
def bellmanValues (p β : ℝ) (x y : X) : Set ℝ :=
  {v | ∃ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (l : Fin N → 𝕜),
    IsPredictable ξ ∧ (∀ k, ‖l k‖ ≤ 1) ∧
      v = avg fun ε => ‖y + paleyWalsh (fun k ε => l k • ξ k ε) N ε‖ ^ p -
        β ^ p * ‖x + paleyWalsh ξ N ε‖ ^ p}

/-- The values of the pairs on `N` signs. -/
private def zzgVal (p β : ℝ) (x y : X) (N : ℕ) (v : ℝ) : Prop :=
  ∃ (ξ : Fin N → (Fin N → Bool) → X) (l : Fin N → 𝕜), IsPredictable ξ ∧ (∀ k, ‖l k‖ ≤ 1) ∧
    v = avg fun ε => ‖y + paleyWalsh (fun k ε => l k • ξ k ε) N ε‖ ^ p -
      β ^ p * ‖x + paleyWalsh ξ N ε‖ ^ p

variable {𝕜}

private theorem zzg_mem_bellmanValues {p β : ℝ} {x y : X} {v : ℝ} :
    v ∈ bellmanValues 𝕜 p β x y ↔ ∃ N, zzgVal 𝕜 p β x y N v :=
  Iff.rfl

end Defs

section Transform

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X]

/-- A Paley–Walsh martingale is linear over `𝕜`. -/
private theorem zzg_paleyWalsh_smul {N : ℕ} (c : 𝕜) (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ)
    (ε : Fin N → Bool) : paleyWalsh (fun k ε => c • ξ k ε) n ε = c • paleyWalsh ξ n ε := by
  simp only [paleyWalsh, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- The dyadic UMD property for deterministic multipliers in the closed unit ball: the vector of
the multipliers is in `(B_𝕜)^N = conv (S_𝕜^N)` (HNVW I, Proposition 3.2.14, p. 184,
`convexHull_pi_sphere`) and the `L^p` norm of the transform is a convex function of it. -/
theorem IsSignDyadicUMDBound.lpNorm_le {p β : ℝ} (hp : 1 ≤ p) (hD : IsSignDyadicUMDBound 𝕜 X p β)
    {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X} (hξ : IsPredictable ξ) {l : Fin N → 𝕜}
    (hl : ∀ k, ‖l k‖ ≤ 1) :
    SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => l k • ξ k ε) N) ≤
      β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N) := by
  have hmem : l ∈ convexHull ℝ (Set.univ.pi fun _ : Fin N => Metric.sphere (0 : 𝕜) 1) := by
    rw [convexHull_pi_sphere]
    simpa [Set.mem_univ_pi] using hl
  refine convexHull_min (t := {l : Fin N → 𝕜 | SignCube.lpNorm (fun x => ‖x‖) p
      (paleyWalsh (fun k ε => l k • ξ k ε) N) ≤
        β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N)}) (fun l hl => ?_) ?_ hmem
  · exact hD N ξ l hξ fun k => by simpa using hl k (Set.mem_univ k)
  · intro l hl l' hl' a b ha hb hab
    set S := lpSeminorm (normSeminorm ℝ X) p hp (N := N)
    change S (paleyWalsh (fun k ε => l k • ξ k ε) N) ≤ _ at hl
    change S (paleyWalsh (fun k ε => l' k • ξ k ε) N) ≤ _ at hl'
    change S (paleyWalsh (fun k ε => (a • l + b • l') k • ξ k ε) N) ≤ _
    have e : paleyWalsh (fun k ε => (a • l + b • l') k • ξ k ε) N =
        a • paleyWalsh (fun k ε => l k • ξ k ε) N +
          b • paleyWalsh (fun k ε => l' k • ξ k ε) N := by
      funext ε
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ← paleyWalsh_smul, ← paleyWalsh_smul,
        ← paleyWalsh_add]
      simp only [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc]
    rw [e]
    refine (map_add_le_add S _ _).trans ?_
    rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    calc _ ≤ a * (β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N)) +
          b * (β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N)) :=
        add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hl' hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

end Transform

section StepOne

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  {p β : ℝ}

/-- Step 1, property (c) (HNVW I, p. 335): the trivial pair `(x, y)` has the value `F (x, y)`. -/
theorem mem_bellmanValues_self (x y : X) :
    ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ∈ bellmanValues 𝕜 p β x y :=
  ⟨0, fun _ _ => 0, fun _ => 0, fun _ _ _ _ => rfl, fun _ => by simp, by simp⟩

variable [IsScalarTower ℝ 𝕜 X]

private theorem zzg_bellmanValues_smul_subset {ε ε' : 𝕜} (hε : ‖ε‖ = 1) (hε' : ‖ε'‖ = 1)
    (x y : X) : bellmanValues 𝕜 p β x y ⊆ bellmanValues 𝕜 p β (ε • x) (ε' • y) := by
  rintro v ⟨N, ξ, l, hξ, hl, rfl⟩
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  refine ⟨N, fun k η => ε • ξ k η, fun k => ε' * l k * ε⁻¹,
    fun k η η' h => by simp only [hξ k η η' h], fun k => ?_, ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hε, hε', inv_one, mul_one, one_mul]
    exact hl k
  · have e : (fun (k : Fin N) (η : Fin N → Bool) => (ε' * l k * ε⁻¹) • ε • ξ k η) =
        fun k η => ε' • l k • ξ k η := by
      funext k η
      rw [smul_smul, inv_mul_cancel_right₀ hε0, mul_smul]
    simp only [e, zzg_paleyWalsh_smul, ← smul_add, norm_smul, hε, hε', one_mul]

/-- Step 1, property (b) (HNVW I, p. 335): `V (ε x, ε' y) = V (x, y)` for signs `ε`, `ε'`, as
`(f, g) ∈ S (x, y)` if and only if `(ε f, ε' g) ∈ S (ε x, ε' y)`. -/
theorem bellmanValues_smul {ε ε' : 𝕜} (hε : ‖ε‖ = 1) (hε' : ‖ε'‖ = 1) (x y : X) :
    bellmanValues 𝕜 p β (ε • x) (ε' • y) = bellmanValues 𝕜 p β x y := by
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hε'0 : ε' ≠ 0 := fun h => by simp [h] at hε'
  refine Set.Subset.antisymm ?_ (zzg_bellmanValues_smul_subset hε hε' x y)
  have h := zzg_bellmanValues_smul_subset (p := p) (β := β) (ε := ε⁻¹) (ε' := ε'⁻¹)
    (by rw [norm_inv, hε, inv_one]) (by rw [norm_inv, hε', inv_one]) (ε • x) (ε' • y)
  rwa [inv_smul_smul₀ hε0, inv_smul_smul₀ hε'0] at h

end StepOne

section StepTwo

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  {p β : ℝ}

/-- A family on `N + 1` signs that is a family on the first `N` signs followed by `0` has the same
Paley–Walsh martingale. -/
private theorem zzg_paleyWalsh_pad {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ}
    (ζ : Fin (N + 1) → (Fin (N + 1) → Bool) → E) (ζ' : Fin N → (Fin N → Bool) → E)
    (h : ∀ i ω, ζ (Fin.castSucc i) ω = ζ' i (Fin.init ω)) (hl : ∀ ω, ζ (Fin.last N) ω = 0)
    (ω : Fin (N + 1) → Bool) : paleyWalsh ζ (N + 1) ω = paleyWalsh ζ' N (Fin.init ω) := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl, Fin.sum_univ_castSucc]
  simp [h, hl, Fin.init]

private theorem zzg_avg_init {N : ℕ} (G : (Fin N → Bool) → ℝ) :
    avg (fun ω : Fin (N + 1) → Bool => G (Fin.init ω)) = avg G := by
  rw [avg_succ_last]
  simp [Fin.init_snoc]

/-- Padding: a value on `N` signs is a value on `N + 1` signs. (In the source the martingales are
indexed by all of `ℕ` and have finitely nonzero difference sequences.) -/
private theorem zzgVal_succ {x y : X} {N : ℕ} {v : ℝ} (h : zzgVal 𝕜 p β x y N v) :
    zzgVal 𝕜 p β x y (N + 1) v := by
  obtain ⟨ξ, l, hξ, hl, rfl⟩ := h
  refine ⟨fun k ω => if hk : (k : ℕ) < N then ξ ⟨k, hk⟩ (Fin.init ω) else 0,
    fun k => if hk : (k : ℕ) < N then l ⟨k, hk⟩ else 0, fun k ω ω' h => ?_, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact hξ _ _ _ fun j hj => h (Fin.castSucc j) (by simpa [Fin.lt_def] using hj)
    · rfl
  · dsimp only
    split_ifs
    · exact hl _
    · simp
  · rw [← zzg_avg_init]
    congr 1
    funext ω
    rw [zzg_paleyWalsh_pad _ (fun k ε => l k • ξ k ε) (fun i ω => by simp) (fun ω => by simp),
      zzg_paleyWalsh_pad _ ξ (fun i ω => by simp) (fun ω => by simp)]

private theorem zzgVal_mono {x y : X} {N N' : ℕ} (hN : N ≤ N') {v : ℝ}
    (h : zzgVal 𝕜 p β x y N v) : zzgVal 𝕜 p β x y N' v := by
  induction N', hN using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact zzgVal_succ ih

/-- The sequence `(a_0, b_0, a_1, b_1, …)`. -/
private def zzgInterleave {E : Type*} {N : ℕ} (a b : Fin N → E) (i : Fin (N * 2)) : E :=
  if (finProdFinEquiv.symm i).2 = 0 then a (finProdFinEquiv.symm i).1
    else b (finProdFinEquiv.symm i).1

private theorem zzgInterleave_even {E : Type*} {N : ℕ} (a b : Fin N → E) (k : Fin N) :
    zzgInterleave a b (finProdFinEquiv (k, 0)) = a k := by
  simp [zzgInterleave, -finProdFinEquiv_symm_apply]

private theorem zzgInterleave_odd {E : Type*} {N : ℕ} (a b : Fin N → E) (k : Fin N) :
    zzgInterleave a b (finProdFinEquiv (k, 1)) = b k := by
  simp [zzgInterleave, -finProdFinEquiv_symm_apply]

/-- The spliced family on `1 + 2 N` signs `r_1, r_2, …` (HNVW I, p. 335–336): `d` at the first step,
then the differences of the two families alternately, the first one on the signs `r_2, r_4, …`
multiplied by `(1 + r_1) / 2`, the second one on the signs `r_3, r_5, …` multiplied by
`(1 − r_1) / 2`. -/
private def zzgSplice {E : Type*} [Zero E] {N : ℕ} (d : E) (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E) :
    Fin (N * 2 + 1) → (Fin (N * 2 + 1) → Bool) → E :=
  fun j ω => Fin.cons (α := fun _ => E) d
    (zzgInterleave (fun k => if ω 0 then ξ₁ k (interleave.symm (Fin.tail ω)).2 else 0)
      (fun k => if ω 0 then 0 else ξ₂ k (interleave.symm (Fin.tail ω)).1)) j

private theorem zzgSplice_isPredictable {E : Type*} [Zero E] {N : ℕ} (d : E)
    {ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E} (hξ₁ : IsPredictable ξ₁) (hξ₂ : IsPredictable ξ₂) :
    IsPredictable (zzgSplice d ξ₁ ξ₂) := by
  intro j ω ω' h
  induction j using Fin.cases with
  | zero => rfl
  | succ i =>
    have h0 : ω 0 = ω' 0 := h 0 (Fin.succ_pos i)
    obtain ⟨⟨k, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    have ht : ∀ j : Fin N, j < k → ω (finProdFinEquiv (j, b)).succ =
        ω' (finProdFinEquiv (j, b)).succ := fun j hj =>
      h _ (Fin.succ_lt_succ_iff.mpr (by
        rw [Fin.lt_def] at hj ⊢
        simp only [finProdFinEquiv_apply_val]
        omega))
    fin_cases b
    · simp only [zzgSplice, Fin.cons_succ, Fin.zero_eta, zzgInterleave_even, h0]
      split_ifs
      · exact hξ₁ k _ _ ht
      · rfl
    · simp only [zzgSplice, Fin.cons_succ, Fin.mk_one, zzgInterleave_odd, h0]
      split_ifs
      · rfl
      · exact hξ₂ k _ _ ht

/-- The final value of the spliced martingale (HNVW I, p. 336): `d` plus the first martingale, run
on the signs `r_2, r_4, …`, on `{r_1 = 1}`, and `−d` plus the second one, run on
`r_3, r_5, …`, on `{r_1 = −1}`. -/
private theorem zzg_paleyWalsh_splice {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ} (d : E)
    (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E) (b : Bool) (η : Fin (N * 2) → Bool) :
    paleyWalsh (zzgSplice d ξ₁ ξ₂) (N * 2 + 1) (Fin.cons b η) =
      coin b • d + if b then paleyWalsh ξ₁ N (interleave.symm η).2
        else paleyWalsh ξ₂ N (interleave.symm η).1 := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl,
    Fin.sum_univ_succ, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, zzgSplice, Fin.cons_zero, Fin.cons_succ, zzgInterleave_even,
    zzgInterleave_odd, Fin.tail_cons]
  cases b <;> simp [interleave, -finProdFinEquiv_symm_apply]

omit [NormedSpace ℝ X] in
/-- The transform of the spliced family by the deterministic multipliers
`e, l¹_1, l²_1, l¹_2, l²_2, …` is the splice of the transforms (HNVW I, p. 336:
`dg_n = ε⁰_n df_n` with `ε⁰_1 = ε_0`, `ε⁰_{2n} = ε¹_n`, `ε⁰_{2n+1} = ε²_n`). -/
private theorem zzg_smul_splice {N : ℕ} (e : 𝕜) (l₁ l₂ : Fin N → 𝕜) (d : X)
    (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → X) (j : Fin (N * 2 + 1)) (ω : Fin (N * 2 + 1) → Bool) :
    Fin.cons (α := fun _ => 𝕜) e (zzgInterleave l₁ l₂) j • zzgSplice d ξ₁ ξ₂ j ω =
      zzgSplice (e • d) (fun k ε => l₁ k • ξ₁ k ε) (fun k ε => l₂ k • ξ₂ k ε) j ω := by
  induction j using Fin.cases with
  | zero => simp [zzgSplice]
  | succ i =>
    obtain ⟨⟨k, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    fin_cases b
    · simp only [zzgSplice, Fin.cons_succ, Fin.zero_eta, zzgInterleave_even]
      split_ifs <;> simp
    · simp only [zzgSplice, Fin.cons_succ, Fin.mk_one, zzgInterleave_odd]
      split_ifs <;> simp

/-- The even signs of `2 N` signs are `N` signs. -/
private theorem zzg_avg_even {N : ℕ} (H : (Fin N → Bool) → ℝ) :
    avg (fun η : Fin (N * 2) → Bool => H (interleave.symm η).2) = avg H := by
  rw [avg_interleave fun _ η => H η, avg_const]

/-- The odd signs of `2 N` signs are `N` signs. -/
private theorem zzg_avg_odd {N : ℕ} (H : (Fin N → Bool) → ℝ) :
    avg (fun η : Fin (N * 2) → Bool => H (interleave.symm η).1) = avg H := by
  rw [avg_interleave fun η _ => H η]
  simp only [avg_const]

private theorem zzgVal_splice {N : ℕ} {x₁ x₂ y₁ y₂ : X} {e : 𝕜} (he : ‖e‖ ≤ 1)
    (hy : y₁ - y₂ = e • (x₁ - x₂)) [IsScalarTower ℝ 𝕜 X] {v₁ v₂ : ℝ}
    (h₁ : zzgVal 𝕜 p β x₁ y₁ N v₁) (h₂ : zzgVal 𝕜 p β x₂ y₂ N v₂) :
    zzgVal 𝕜 p β ((1 / 2 : ℝ) • (x₁ + x₂)) ((1 / 2 : ℝ) • (y₁ + y₂)) (N * 2 + 1)
      ((v₁ + v₂) / 2) := by
  obtain ⟨ξ₁, l₁, hξ₁, hl₁, rfl⟩ := h₁
  obtain ⟨ξ₂, l₂, hξ₂, hl₂, rfl⟩ := h₂
  refine ⟨zzgSplice ((1 / 2 : ℝ) • (x₁ - x₂)) ξ₁ ξ₂,
    Fin.cons (α := fun _ => 𝕜) e (zzgInterleave l₁ l₂), zzgSplice_isPredictable _ hξ₁ hξ₂,
    fun j => ?_, ?_⟩
  · induction j using Fin.cases with
    | zero => exact he
    | succ i =>
      obtain ⟨⟨k, b⟩, rfl⟩ := finProdFinEquiv.surjective i
      fin_cases b
      · simpa only [Fin.cons_succ, Fin.zero_eta, zzgInterleave_even] using hl₁ k
      · simpa only [Fin.cons_succ, Fin.mk_one, zzgInterleave_odd] using hl₂ k
  · have hd : e • (1 / 2 : ℝ) • (x₁ - x₂) = (1 / 2 : ℝ) • (y₁ - y₂) := by rw [smul_comm, hy]
    have e₁ : ∀ a b z : X, (1 / 2 : ℝ) • (a + b) + ((1 / 2 : ℝ) • (a - b) + z) = a + z :=
      fun a b z => by module
    have e₂ : ∀ a b z : X, (1 / 2 : ℝ) • (a + b) + (-((1 / 2 : ℝ) • (a - b)) + z) = b + z :=
      fun a b z => by module
    simp only [zzg_smul_splice, hd]
    rw [avg_succ]
    simp only [zzg_paleyWalsh_splice, coin_true, coin_false, one_smul, neg_one_smul,
      ↓reduceIte, Bool.false_eq_true, e₁, e₂]
    rw [zzg_avg_even fun ε => ‖y₁ + paleyWalsh (fun k ε => l₁ k • ξ₁ k ε) N ε‖ ^ p -
        β ^ p * ‖x₁ + paleyWalsh ξ₁ N ε‖ ^ p,
      zzg_avg_odd fun ε => ‖y₂ + paleyWalsh (fun k ε => l₂ k • ξ₂ k ε) N ε‖ ^ p -
        β ^ p * ‖x₂ + paleyWalsh ξ₂ N ε‖ ^ p]

variable [IsScalarTower ℝ 𝕜 X]

/-- **Step 2**, the splicing (HNVW I, p. 335–336): if `v_i ∈ V (x_i, y_i)`, `i = 1, 2`, and
`y_1 − y_2 = e (x_1 − x_2)`, `‖e‖ ≤ 1`, then `(v_1 + v_2) / 2 ∈ V (x_0, y_0)` at the midpoint
`(x_0, y_0)`. On the cube with `1 + 2 N` signs the spliced pair makes the step
`r_1 (x_1 − x_2) / 2`, with multiplier `e`, and continues with the first pair, run on the signs
`r_2, r_4, …`, if `r_1 = 1`, and with the second one, run on `r_3, r_5, …`, if `r_1 = −1`; the
multipliers `e, l¹_1, l²_1, l¹_2, l²_2, …` are constants. -/
theorem add_div_two_mem_bellmanValues {x₁ x₂ y₁ y₂ : X} {e : 𝕜} (he : ‖e‖ ≤ 1)
    (hy : y₁ - y₂ = e • (x₁ - x₂)) {v₁ v₂ : ℝ} (h₁ : v₁ ∈ bellmanValues 𝕜 p β x₁ y₁)
    (h₂ : v₂ ∈ bellmanValues 𝕜 p β x₂ y₂) :
    (v₁ + v₂) / 2 ∈ bellmanValues 𝕜 p β ((1 / 2 : ℝ) • (x₁ + x₂)) ((1 / 2 : ℝ) • (y₁ + y₂)) := by
  obtain ⟨N₁, h₁⟩ := zzg_mem_bellmanValues.mp h₁
  obtain ⟨N₂, h₂⟩ := zzg_mem_bellmanValues.mp h₂
  exact zzg_mem_bellmanValues.mpr ⟨_, zzgVal_splice he hy
    (zzgVal_mono (Nat.le_add_right N₁ N₂) h₁) (zzgVal_mono (Nat.le_add_left N₂ N₁) h₂)⟩

end StepTwo

section StepThree

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] {p β : ℝ}

/-- **Step 3** (HNVW I, p. 336–337), `U (0, 0) ≤ 0`: `E F (f_∞, g_∞) ≤ 0` for the pairs started at
`(0, 0)`, by the dyadic UMD property with the constant `β`. -/
theorem nonpos_of_mem_bellmanValues_zero (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hD : IsSignDyadicUMDBound 𝕜 X p β) {v : ℝ} (h : v ∈ bellmanValues 𝕜 p β (0 : X) 0) :
    v ≤ 0 := by
  obtain ⟨N, ξ, l, hξ, hl, rfl⟩ := h
  have hp0 : 0 < p := by linarith
  simp only [zero_add]
  rw [avg_sub, avg_const_mul, ← lpNorm_rpow (fun x : X => norm_nonneg x) hp0,
    ← lpNorm_rpow (fun x : X => norm_nonneg x) hp0, sub_nonpos,
    ← Real.mul_rpow hβ (lpNorm_nonneg (fun x : X => norm_nonneg x) p _)]
  exact Real.rpow_le_rpow (lpNorm_nonneg (fun x : X => norm_nonneg x) p _)
    (hD.lpNorm_le hp hξ hl) hp0.le

/-- **Step 3** (HNVW I, p. 337), `U (x, x) ≤ 0`, as in (4.34), p. 333:
`U (x, x) = ½ U (0 + x, 0 + x) + ½ U (0 − x, 0 − x) ≤ U (0, 0) ≤ 0`, by the symmetry
`V (−x, −x) = V (x, x)` and midpoint zig-zag concavity. -/
theorem nonpos_of_mem_bellmanValues_self (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hD : IsSignDyadicUMDBound 𝕜 X p β) {x : X} {v : ℝ} (h : v ∈ bellmanValues 𝕜 p β x x) :
    v ≤ 0 := by
  have h' : v ∈ bellmanValues 𝕜 p β (-x) (-x) := by
    have := bellmanValues_smul (p := p) (β := β) (ε := (-1 : 𝕜)) (ε' := -1) (by simp) (by simp) x x
    rw [neg_one_smul] at this
    rwa [this]
  have h0 := add_div_two_mem_bellmanValues (e := (1 : 𝕜)) (by simp) (by rw [one_smul]) h h'
  rw [add_neg_cancel, smul_zero] at h0
  linarith [nonpos_of_mem_bellmanValues_zero hp hβ hD h0]

/-- **Step 3** (HNVW I, p. 337), `U (x, y) + U (y, x) ≤ 2 U (a, a) ≤ 0`, `a = (x + y) / 2`, by
midpoint zig-zag concavity with `ε = −1` (`(x, y) = (a + b, a − b)`, `(y, x) = (a − b, a + b)`,
`b = (x − y) / 2`). -/
theorem add_nonpos_of_mem_bellmanValues (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hD : IsSignDyadicUMDBound 𝕜 X p β) {x y : X} {v₁ v₂ : ℝ}
    (h₁ : v₁ ∈ bellmanValues 𝕜 p β x y) (h₂ : v₂ ∈ bellmanValues 𝕜 p β y x) : v₁ + v₂ ≤ 0 := by
  have h := add_div_two_mem_bellmanValues (e := (-1 : 𝕜)) (by simp)
    (by rw [neg_one_smul, neg_sub]) h₁ h₂
  rw [add_comm y x] at h
  linarith [nonpos_of_mem_bellmanValues_self hp hβ hD h]

/-- Property (a) (HNVW I, p. 334 and 337), `U (x, y) < ∞`: `V (x, y)` is bounded above by
`−F (y, x)`. -/
theorem bddAbove_bellmanValues (hp : 1 ≤ p) (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound 𝕜 X p β)
    (x y : X) : BddAbove (bellmanValues 𝕜 p β x y) :=
  ⟨-(‖x‖ ^ p - β ^ p * ‖y‖ ^ p), fun _ hv => by
    linarith [add_nonpos_of_mem_bellmanValues hp hβ hD hv (mem_bellmanValues_self y x)]⟩

/-- Property (c): `U (x, y) ≥ F (x, y)`. -/
theorem le_sSup_bellmanValues (hp : 1 ≤ p) (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound 𝕜 X p β)
    (x y : X) : ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ sSup (bellmanValues 𝕜 p β x y) :=
  le_csSup (bddAbove_bellmanValues hp hβ hD x y) (mem_bellmanValues_self x y)

/-- `U (0, 0) = 0`. -/
theorem sSup_bellmanValues_zero (hp : 1 ≤ p) (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound 𝕜 X p β) :
    sSup (bellmanValues 𝕜 p β (0 : X) 0) = 0 := by
  refine le_antisymm (csSup_le ⟨_, mem_bellmanValues_self 0 0⟩ fun v hv =>
    nonpos_of_mem_bellmanValues_zero hp hβ hD hv) ?_
  simpa [Real.zero_rpow (by linarith : p ≠ 0)] using le_sSup_bellmanValues hp hβ hD (0 : X) 0

/-- **Step 2**, midpoint concavity (HNVW I, p. 335–336):
`½ (U (x_1, y_1) + U (x_2, y_2)) ≤ U (x_0, y_0)`, from the splicing: for `m_i < U (x_i, y_i)` pick
`v_i ∈ V (x_i, y_i)` with `v_i > m_i`. -/
private theorem zzg_sSup_midpoint (hp : 1 ≤ p) (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound 𝕜 X p β)
    {x₁ x₂ y₁ y₂ : X} {e : 𝕜} (he : ‖e‖ ≤ 1) (hy : y₁ - y₂ = e • (x₁ - x₂)) :
    (sSup (bellmanValues 𝕜 p β x₁ y₁) + sSup (bellmanValues 𝕜 p β x₂ y₂)) / 2 ≤
      sSup (bellmanValues 𝕜 p β ((1 / 2 : ℝ) • (x₁ + x₂)) ((1 / 2 : ℝ) • (y₁ + y₂))) := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨v₁, hv₁, h₁⟩ := exists_lt_of_lt_csSup ⟨_, mem_bellmanValues_self x₁ y₁⟩
    (sub_lt_self (sSup (bellmanValues 𝕜 p β x₁ y₁)) hδ)
  obtain ⟨v₂, hv₂, h₂⟩ := exists_lt_of_lt_csSup ⟨_, mem_bellmanValues_self x₂ y₂⟩
    (sub_lt_self (sSup (bellmanValues 𝕜 p β x₂ y₂)) hδ)
  have h := le_csSup (bddAbove_bellmanValues hp hβ hD _ _)
    (add_div_two_mem_bellmanValues he hy hv₁ hv₂)
  linarith

/-- Property (d) (HNVW I, p. 334–337), zig-zag concavity of `U (x, y) = sup V (x, y)`:
`z ↦ U (x + z, y + e z)` is concave for `‖e‖ ≤ 1`. It is midpoint concave by Step 2, and locally
bounded below by Step 1 (c), so that Lemma 4.5.2 applies. -/
theorem concaveOn_sSup_bellmanValues (hp : 1 ≤ p) (hβ : 0 ≤ β) (hD : IsSignDyadicUMDBound 𝕜 X p β)
    (x y : X) {e : 𝕜} (he : ‖e‖ ≤ 1) :
    ConcaveOn ℝ Set.univ fun z : X => sSup (bellmanValues 𝕜 p β (x + z) (y + e • z)) := by
  have hp0 : 0 ≤ p := by linarith
  refine (concaveOn_iff_midpoint fun z => ?_).mpr fun z₁ z₂ => ?_
  · -- locally bounded below by the continuous function `F (x + z, y + e z)`
    set ψ : X → ℝ := fun z => ‖y + e • z‖ ^ p - β ^ p * ‖x + z‖ ^ p with hψ
    have hψc : Continuous ψ := by
      have c1 : Continuous fun z : X => ‖y + e • z‖ := by fun_prop
      have c2 : Continuous fun z : X => ‖x + z‖ := by fun_prop
      exact (c1.rpow_const fun _ => Or.inr hp0).sub
        (continuous_const.mul (c2.rpow_const fun _ => Or.inr hp0))
    exact ⟨ψ ⁻¹' Set.Ioi (ψ z - 1), hψc.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by linarith)), ψ z - 1, fun w hw =>
        (le_of_lt hw).trans (le_sSup_bellmanValues hp hβ hD _ _)⟩
  · have h := zzg_sSup_midpoint hp hβ hD (x₁ := x + z₁) (x₂ := x + z₂) (y₁ := y + e • z₁)
      (y₂ := y + e • z₂) he (by rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, smul_sub])
    have e1 : (1 / 2 : ℝ) • (x + z₁ + (x + z₂)) = x + (1 / 2 : ℝ) • (z₁ + z₂) := by module
    have e2 : (1 / 2 : ℝ) • (y + e • z₁ + (y + e • z₂)) = y + e • (1 / 2 : ℝ) • (z₁ + z₂) := by
      rw [smul_comm e, smul_add e]
      module
    rwa [e1, e2] at h

end StepThree

end BanachProbability
