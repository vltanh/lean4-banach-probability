module

public import BanachProbability.Martingale.Burkholder.Function
public import BanachProbability.Martingale.Osekowski.Moment
public import BanachProbability.Martingale.Transform

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012: the inequality (3.59) of Theorem 3.5 (ii) and the inequalities (8.28) of
Theorem 8.6, by the arguments of the book. The same inequalities are Theorems 1.1 and 3.1 of
D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul Lévy
sur les processus stochastiques, Astérisque 157–158 (1988), whose function (1.6) is
`Martingale/Burkholder/Function.lean`.

## Main results

* `inequality` (Theorem 3.5 (ii)): for martingales `X`, `Y` with values in a separable real Hilbert
  space `H`, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` with `p* = max (p, p / (p − 1))`. The proof does not use
  the separability of `H`: `inequality_of_subordinate` is the same statement without it.
  `Osekowski.eLpNorm_le_of_subordinate` is the theorem in the form of the book (`‖X_0‖ ≤ ‖Y_0‖`
  instead of a start at `0`), and the constant `p* − 1` is the best possible
  (`Martingale/Osekowski/Sharpness.lean`).
* `squareFunction` (Theorem 8.6):
  `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
  `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}` (`squareFunction_of_martingale` without
  separability).

## The proofs

1. Theorem 3.5 (ii) (p. 53–54, 58), in `Martingale/Osekowski/`, by the integration method: with
   Burkholder's function `U_p (x, y) = α_p (|y| − (p* − 1)|x|)(|x| + |y|)^{p−1}` (`x` the position
   of the dominating martingale, `y` that of the subordinate one),
   `|y|^p − (p* − 1)^p |x|^p ≤ U_p (x, y)` (`burkholderU_ge`), and `U_p` is an integral
   `∫_0^∞ k (t) u (x / t, y / t) dt` with `k ≥ 0` and `u = U₁` (`1 < p < 2`) or `u = U_∞`
   (`p > 2`), two simple functions with `E u (Y_n / t, X_n / t) ≤ 0` (Burkholder's method,
   Theorem 2.7); so `E (|X_n|^p − (p* − 1)^p |Y_n|^p) ≤ E U_p (Y_n, X_n) ≤ 0` by Fubini's theorem.
   The case `p = 2` is orthogonality.
2. Theorem 8.6 (p. 414, by the device of Section 2.1.3, p. 16): in `K = ℓ² (H)`, the martingale
   `(X_m, 0, 0, …)` and `(dX_1, …, dX_m, 0, …)` have increments of equal norm, so each is
   differentially subordinate to the other, and the norm of the second is `𝒮_m X`; Theorem 3.5
   applies to both pairs.

The statements are for martingales that start at `0`, so the term `‖X_0‖²` of the square function of
the book vanishes, and are at a fixed time `n` rather than for `sup_n ‖·‖_p`. In step 2, up to time
`n` the two martingales take values in the first `n + 1` coordinates of `ℓ² (H)`; the proof works in
that subspace, `H^{n+1}` (`PiLp 2`), with `X` in the last coordinate and its increments in the first
`n`, and with both martingales stopped at `n`, which does not change them up to time `n`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace RealInnerProductSpace

namespace BanachProbability.Burkholder

/-! ### Burkholder's inequality -/

/-- Burkholder's inequality without the separability of `H` (which the proof does not use): the case
`X_0 = Y_0 = 0` of `Osekowski.eLpNorm_le_of_subordinate`. -/
theorem inequality_of_subordinate {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  Osekowski.eLpNorm_le_of_subordinate hp hY hX (Eventually.of_forall fun ω => by rw [hX0, hY0])
    hsub n

/-- **Burkholder's inequality** (Osękowski, *Sharp Martingale and Semimartingale Inequalities*
(2012), Theorem 3.5 (ii); Burkholder 1988, Theorem 1.1): for martingales `X`, `Y` with values in a
separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`. The argument
is that of the book, the integration method (`Osekowski.eLpNorm_le_of_subordinate`; the book's
martingales have `‖X_0‖ ≤ ‖Y_0‖` instead of a start at `0`). The separability of `H` is not used. -/
theorem inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  inequality_of_subordinate hp hX hY hX0 hY0 hsub n

/-! ### Burkholder's square function inequality -/

section SquareFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

omit [IsProbabilityMeasure μ] in
private theorem martingale_finset_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Finset ι) {M : ι → ℕ → Ω → E}
    (hM : ∀ i ∈ s, Martingale (M i) ℱ μ) :
    Martingale (fun m ω => ∑ i ∈ s, M i m ω) ℱ μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert martingale_zero E ℱ μ using 1
    funext m ω; simp
  | insert a s ha ih =>
    have := (hM a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hM i (Finset.mem_insert_of_mem hi))
    convert this using 1
    funext m ω; simp [Finset.sum_insert ha]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem norm_sum_single {n : ℕ} (v : Fin n → H) :
    ‖∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H) (Fin.castSucc i) (v i)‖ =
      √(∑ i : Fin n, ‖v i‖ ^ 2) := by
  classical
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_castSucc]
  congr 1
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply,
    Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [(Fin.castSucc_ne_last _).symm]

/-- Burkholder's square function inequality without the separability of `H`. -/
theorem squareFunction_of_martingale {X : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ := by
  classical
  -- the Hilbert space `H^{n+1}` with the `ℓ²` norm, and its coordinate embeddings
  let L : Fin (n + 1) → H →L[ℝ] PiLp 2 (fun _ : Fin (n + 1) => H) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => H)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => H) i)
  have hL : ∀ i x, L i x = PiLp.single 2 (β := fun _ : Fin (n + 1) => H) i x := fun _ _ => rfl
  -- `A_m = X_{n ∧ m} e_n` and `Z_m = Σ_{i < n} (X_{(i+1) ∧ m} − X_{i ∧ m}) e_i`
  set A : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) :=
    fun m ω => L (Fin.last n) (X (min n m) ω) with hAdef
  set Z : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) := fun m ω =>
    ∑ i : Fin n, L (Fin.castSucc i) (X (min ((i : ℕ) + 1) m) ω - X (min (i : ℕ) m) ω) with hZdef
  have hA : Martingale A ℱ μ :=
    martingale_map_continuousLinearMap (Osekowski.martingale_min hX n) _
  have hZ : Martingale Z ℱ μ := martingale_finset_sum Finset.univ fun i _ =>
    martingale_map_continuousLinearMap ((Osekowski.martingale_min hX ((i : ℕ) + 1)).sub
      (Osekowski.martingale_min hX i)) _
  have hA0 : ∀ ω, A 0 ω = 0 := fun ω => by simp [hAdef, hX0]
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by simp [hZdef]
  -- the increments: `‖dZ_m‖ = ‖dA_m‖ = 1_{m < n} ‖dX_m‖`
  have hinc : ∀ m ω, ‖Z (m + 1) ω - Z m ω‖ = ‖A (m + 1) ω - A m ω‖ := by
    intro m ω
    have hw : ∀ i : ℕ, (X (min (i + 1) (m + 1)) ω - X (min i (m + 1)) ω) -
        (X (min (i + 1) m) ω - X (min i m) ω) = if i = m then X (m + 1) ω - X m ω else 0 := by
      intro i
      rcases lt_trichotomy i m with h | rfl | h
      · rw [ite_eq_right h.ne, min_eq_left (by omega : i + 1 ≤ m + 1),
          min_eq_left (by omega : i ≤ m + 1),
          min_eq_left (by omega : i + 1 ≤ m), min_eq_left (by omega : i ≤ m)]
        simp
      · rw [ite_eq_left rfl, min_self, min_eq_left (by omega : i ≤ i + 1),
          min_eq_right (by omega : i ≤ i + 1), min_self]
        simp
      · rw [ite_eq_right h.ne', min_eq_right (by omega : m + 1 ≤ i + 1),
          min_eq_right (by omega : m + 1 ≤ i), min_eq_right (by omega : m ≤ i + 1),
          min_eq_right (by omega : m ≤ i)]
        simp
    have hZd : Z (m + 1) ω - Z m ω = ∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H)
        (Fin.castSucc i) (if (i : ℕ) = m then X (m + 1) ω - X m ω else 0) := by
      simp only [hZdef, ← Finset.sum_sub_distrib, hL, ← PiLp.single_sub, hw]
    rw [hZd, norm_sum_single]
    simp only [hAdef, hL, ← PiLp.single_sub, PiLp.norm_single]
    rcases lt_or_ge m n with h | h
    · rw [min_eq_right (by omega : m + 1 ≤ n), min_eq_right h.le]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 =
          ‖X (m + 1) ω - X m ω‖ ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => ‖(if i = m then X (m + 1) ω - X m ω else 0)‖ ^ 2) n,
          Finset.sum_eq_single m (fun b _ hb => by simp [hb])
            (fun hm => absurd (Finset.mem_range.2 h) hm)]
        simp
      rw [this, Real.sqrt_sq (norm_nonneg _)]
    · rw [min_eq_left (by omega : n ≤ m + 1), min_eq_left h]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have := i.isLt
          simp [show (i : ℕ) ≠ m by omega]
      rw [this]; simp
  -- at time `n`: `‖A_n‖ = ‖X_n‖` and `‖Z_n‖ = 𝒮_n X`
  have hAn : ∀ ω, ‖A n ω‖ = ‖X n ω‖ := fun ω => by simp [hAdef, hL, PiLp.norm_single]
  have hZn : ∀ ω, ‖Z n ω‖ = √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2) := by
    intro ω
    simp only [hZdef, hL]
    rw [norm_sum_single, ← Fin.sum_univ_eq_sum_range (fun k => ‖X (k + 1) ω - X k ω‖ ^ 2) n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have := i.isLt
    rw [min_eq_left (by omega : (i : ℕ) + 1 ≤ n), min_eq_left (by omega : (i : ℕ) ≤ n)]
  have eA : eLpNorm (A n) (ENNReal.ofReal p) μ = eLpNorm (X n) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (A n) (hA.integrable n).aestronglyMeasurable,
      ← eLpNorm_norm (X n) (hX.integrable n).aestronglyMeasurable]
    simp only [hAn]
  have eZ : eLpNorm (Z n) (ENNReal.ofReal p) μ = eLpNorm
      (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (Z n) (hZ.integrable n).aestronglyMeasurable]
    simp only [hZn]
  refine ⟨?_, ?_⟩
  · have := inequality_of_subordinate hp hZ hA hZ0 hA0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).le) n
    rwa [eZ, eA] at this
  · have := inequality_of_subordinate hp hA hZ hA0 hZ0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).ge) n
    rwa [eZ, eA] at this

/-- **Burkholder's square function inequality** (Osękowski, *Sharp Martingale and Semimartingale
Inequalities* (2012), Theorem 8.6, (8.28); Burkholder 1988, Theorem 3.1): for a martingale `X` with
values in a separable real Hilbert space, started at `0`, `p > 1` and
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`,
`‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.

The argument of the book (p. 414 and Section 2.1.3, p. 16): in the Hilbert space `H^{n+1}` with the
`ℓ²` norm, the martingale `Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k` has `‖Z_n‖ = 𝒮_n X` and
`‖dZ_m‖ = ‖dX_{m+1}‖ 1_{m < n}`, which is also the norm of the increments of `A_m = X_{n ∧ m} e_n`;
each of the two martingales is differentially subordinate to the other, and Theorem 3.5
(`inequality_of_subordinate`) applies to both pairs.

Up to time `n`, the martingales of the book take values in the first `n + 1` coordinates of
`ℓ² (H)`; the proof works in that subspace, `H^{n+1}` (`PiLp 2`), with `X` in the last coordinate
rather than the first and both martingales stopped at `n`, which leaves them unchanged up to time
`n`.
The separability of `H` is not used. -/
theorem squareFunction {X : ℕ → Ω → H} [TopologicalSpace.SeparableSpace H] {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  squareFunction_of_martingale hp hX hX0 n

end SquareFunction

end BanachProbability.Burkholder
