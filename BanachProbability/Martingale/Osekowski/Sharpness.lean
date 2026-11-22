module

public import BanachProbability.UMD.Hilbert
public import BanachProbability.ZigZag.Basic

/-!
# The sharpness of `p* − 1`

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012: Theorem 3.5 (the constant `p* − 1` of the moment inequality for `±1`-transforms is
the best possible), by the second approach of p. 56–57 for `1 < p ≤ 2` and by the duality of p. 59
for `p > 2`, and Theorem 3.34 (the best constants of the dyadic case are the same). For a real
Hilbert space `H ≠ 0` and `1 < p < ∞`, `UMD_p (H) = UMD_p^Δ (H) = p* − 1`,
`p* = max (p, p / (p − 1))`; the upper bound is Burkholder's theorem
(`umdConst_le_of_innerProductSpace`).

## Main results

* `dyadicValues`, `dyadicBellman`: the set of the values `E V (f, g)` of the dyadic pairs started
  at `(x, y)` and its supremum `W⁰ (x, y)`. If `E V (f, g) ≤ 0` for the pairs started at the points
  `(x, ±x)` (the condition (3.214)), then `W⁰` is finite (`bddAbove_dyadicValues`), `W⁰ ≥ V`
  (`le_dyadicBellman`), `W⁰` is concave along the lines of slope `±1` for `V` locally bounded from
  below (`concaveOn_dyadicBellman`), and `W⁰ (x, ±x) ≤ 0` (`dyadicBellman_nonpos`): the function of
  the proof of Theorem 3.34.
* `inv_sub_one_le_of_isDyadicUMDBound`: a dyadic `UMD_p` constant of `ℝ` is at least
  `1 / (p − 1)`; `isDyadicUMDBound_conjExponent`: it is one for the conjugate exponent;
  `sub_one_le_of_isDyadicUMDBound`: it is at least `p − 1`.
* `dyadicUMDConst_real`, `umdConst_real`, `dyadicUMDConst_of_innerProductSpace`,
  `umdConst_of_innerProductSpace`: the constants are `p* − 1`.
* `exists_lt_lpNorm_transform`: for `K < p* − 1` there are a real Paley–Walsh martingale `f` and a
  transform `g` of `f` by predictable signs with `K ‖f‖_p < ‖g‖_p`.

## The proof

Everything is on the sign cube, with the pairs `f = x + Σ ε_k ξ_k`, `g = y + Σ σ_k ε_k ξ_k` with
predictable `ξ_k` and predictable signs `σ_k`. Splicing two pairs by a first sign makes `W⁰`
midpoint concave along the lines of slope `±1`, hence concave there. (The book runs the second
approach on `U⁰`, the supremum over all the simple pairs, and Theorem 3.34 carries its result to the
dyadic ones by showing that `W⁰` has the properties 1°, 2°, 3° of `U⁰`; here the approach is run on
`W⁰` itself.)

For `V (x, y) = |y|^p − β^p |x|^p`, `β` a dyadic `UMD_p` constant of `ℝ`, the pairs started at
`(x, ±x)` have `E V ≤ 0` (`lpNorm_start_transform_le`, by one more sign), so `W⁰` exists. It is
homogeneous of order `p` and even in `y`, so `w (x) = W⁰ (x, 1 − x)` is concave on `ℝ` and
`w (x) = (2x − 1)^p w (x / (2x − 1))` for `x > 1`; hence `w' (1+) + w' (1−) = 2 p w (1)`. Since
`w (1 / (β + 1)) ≥ 0`, the chord from `1 / (β + 1)` to `1` has slope at most `w (1) (β + 1) / β`,
and at least `w' (1−) ≥ p w (1)`. As `w (1) < 0`, `(β + 1) / β ≤ p`, that is `β ≥ 1 / (p − 1)`.

By duality, `β` is also a constant for the conjugate exponent `q`, so `β ≥ 1 / (q − 1) = p − 1`.
-/

@[expose] public section

namespace BanachProbability.Osekowski

open SignCube

section Prepend

variable {E : Type*} {N : ℕ}

/-- The family on `N + 1` signs that starts with `d` and, after the first sign `ε₀`, goes on with
the family `ζ ε₀` of the remaining `N` signs. -/
private def prepend (d : E) (ζ : Bool → Fin N → (Fin N → Bool) → E) :
    Fin (N + 1) → (Fin (N + 1) → Bool) → E :=
  fun k ω => Fin.cons (α := fun _ => E) d (fun i => ζ (ω 0) i (Fin.tail ω)) k

/-- `prepend d ζ` is predictable if `ζ true` and `ζ false` are. -/
private theorem isPredictable_prepend (d : E) {ζ : Bool → Fin N → (Fin N → Bool) → E}
    (hζ : ∀ b, IsPredictable (ζ b)) : IsPredictable (prepend d ζ) := by
  intro k ω ω' h
  induction k using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [prepend, Fin.cons_succ, h 0 (Fin.succ_pos i)]
    exact hζ _ i _ _ fun j hj => h j.succ (Fin.succ_lt_succ_iff.mpr hj)

/-- `prepend e a` takes the values `±1` if `e`, `a true` and `a false` do. -/
private theorem prepend_sign {e : ℝ} (he : e = 1 ∨ e = -1)
    {a : Bool → Fin N → (Fin N → Bool) → ℝ} (ha : ∀ b k ε, a b k ε = 1 ∨ a b k ε = -1)
    (k : Fin (N + 1)) (ω : Fin (N + 1) → Bool) : prepend e a k ω = 1 ∨ prepend e a k ω = -1 := by
  induction k using Fin.cases with
  | zero => exact he
  | succ i => exact ha _ i _

variable [AddCommGroup E] [Module ℝ E]

/-- The transform of `prepend d ζ` by `prepend e a` is `prepend (e d) (a ζ)`. -/
private theorem smul_prepend (e : ℝ) (a : Bool → Fin N → (Fin N → Bool) → ℝ) (d : E)
    (ζ : Bool → Fin N → (Fin N → Bool) → E) :
    (fun k ω => prepend e a k ω • prepend d ζ k ω) =
      prepend (e • d) fun b k ε => a b k ε • ζ b k ε := by
  funext k ω
  induction k using Fin.cases <;> rfl

/-- The Paley–Walsh martingale of `prepend d ζ` is `ε₀ d` plus that of `ζ ε₀`. -/
private theorem paleyWalsh_prepend (d : E) (ζ : Bool → Fin N → (Fin N → Bool) → E) (b : Bool)
    (η : Fin N → Bool) :
    paleyWalsh (prepend d ζ) (N + 1) (Fin.cons b η) = coin b • d + paleyWalsh (ζ b) N η := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl, Fin.sum_univ_succ]
  simp [prepend]

end Prepend

section Bellman

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {V : X → X → ℝ}

/-- The values `E V (f, g)` of the dyadic pairs started at `(x, y)`: `f = x + Σ_{k<N} ε_k ξ_k`,
`g = y + Σ_{k<N} σ_k ε_k ξ_k`, with predictable `ξ_k` and predictable signs `σ_k = ±1`. The source
(Theorem 3.34) writes them as Haar series: on the sign cube, a coefficient and a sign for each Haar
function are a predictable `ξ_k` and a predictable `σ_k`. -/
def dyadicValues (V : X → X → ℝ) (x y : X) : Set ℝ :=
  {v | ∃ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ ∧ IsPredictable σ ∧ (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      v = avg fun ε => V (x + paleyWalsh ξ N ε) (y + paleyWalsh (fun k ε => σ k ε • ξ k ε) N ε)}

/-- The function `W⁰ (x, y) = sup E V (f, g)` of Theorem 3.34, the supremum over the dyadic pairs
started at `(x, y)`. -/
noncomputable def dyadicBellman (V : X → X → ℝ) (x y : X) : ℝ :=
  sSup (dyadicValues V x y)

/-- `v` is the value `E V (f, g)` of a dyadic pair on `N` signs started at `(x, y)`. -/
private def IsValue (V : X → X → ℝ) (x y : X) (N : ℕ) (v : ℝ) : Prop :=
  ∃ (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ ∧ IsPredictable σ ∧ (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      v = avg fun ε => V (x + paleyWalsh ξ N ε) (y + paleyWalsh (fun k ε => σ k ε • ξ k ε) N ε)

/-- Splicing on `N` signs: the pair starts with the step `ε₀ (d, e d)` and goes on with the second
pair if `ε₀ = 1` and with the first one if `ε₀ = −1`. -/
private theorem IsValue.splice {x y d : X} {e : ℝ} (he : e = 1 ∨ e = -1) {N : ℕ} {v₁ v₂ : ℝ}
    (h₁ : IsValue V (x - d) (y - e • d) N v₁) (h₂ : IsValue V (x + d) (y + e • d) N v₂) :
    IsValue V x y (N + 1) ((v₁ + v₂) / 2) := by
  obtain ⟨ξ₁, σ₁, hξ₁, hσ₁, hs₁, rfl⟩ := h₁
  obtain ⟨ξ₂, σ₂, hξ₂, hσ₂, hs₂, rfl⟩ := h₂
  refine ⟨prepend d fun b => bif b then ξ₂ else ξ₁, prepend e fun b => bif b then σ₂ else σ₁,
    isPredictable_prepend _ fun b => ?_, isPredictable_prepend _ fun b => ?_,
    prepend_sign he fun b => ?_, ?_⟩
  · cases b; exacts [hξ₁, hξ₂]
  · cases b; exacts [hσ₁, hσ₂]
  · cases b; exacts [hs₁, hs₂]
  · rw [smul_prepend, avg_succ, add_comm (avg _) (avg _)]
    simp only [paleyWalsh_prepend, coin_true, coin_false, one_smul, neg_one_smul, Bool.cond_true,
      Bool.cond_false, ← add_assoc, ← sub_eq_add_neg]

/-- Padding: a value on `N` signs is one on `N' ≥ N` signs (splice the pair with itself, with the
step `d = 0`). -/
private theorem IsValue.mono {x y : X} {N N' : ℕ} (hN : N ≤ N') {v : ℝ} (h : IsValue V x y N v) :
    IsValue V x y N' v := by
  induction N', hN using Nat.le_induction with
  | base => exact h
  | succ n _ ih =>
    have := IsValue.splice (x := x) (y := y) (d := 0) (Or.inl rfl) (by simpa using ih)
      (by simpa using ih)
    rwa [add_self_div_two] at this

/-- `V (x, y)` is a value at `(x, y)`: the pair with `N = 0`. -/
theorem self_mem_dyadicValues (V : X → X → ℝ) (x y : X) : V x y ∈ dyadicValues V x y :=
  ⟨0, fun _ _ => 0, fun _ _ => 1, umdd_isPredictable_const 0, umdd_isPredictable_const 1,
    fun _ _ => Or.inl rfl, by simp⟩

/-- **Splicing** (the proof of Theorem 2.2): if `v₁` is a value at `(x − d, y − e d)` and `v₂` one
at `(x + d, y + e d)`, `e = ±1`, then `(v₁ + v₂) / 2` is a value at `(x, y)`. -/
theorem midpoint_mem_dyadicValues {x y d : X} {e : ℝ} (he : e = 1 ∨ e = -1) {v₁ v₂ : ℝ}
    (h₁ : v₁ ∈ dyadicValues V (x - d) (y - e • d)) (h₂ : v₂ ∈ dyadicValues V (x + d) (y + e • d)) :
    (v₁ + v₂) / 2 ∈ dyadicValues V x y := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  exact ⟨_, IsValue.splice he (IsValue.mono (Nat.le_add_right N₁ N₂) h₁)
    (IsValue.mono (Nat.le_add_left N₂ N₁) h₂)⟩

variable (hV : ∀ (x : X) (e : ℝ), e = 1 ∨ e = -1 → ∀ v ∈ dyadicValues V x (e • x), v ≤ 0)
include hV

/-- The finiteness of `W⁰` (the proof of Theorem 2.3): if the values at the points `(x, ±x)` are
`≤ 0` (the condition (3.214)), those at `(x, y)` are at most `−V (y, x)`. The pair that starts at
`((x + y) / 2, (x + y) / 2)` and moves to `(y, x)`, where it stops, or to `(x, y)`, from where it
goes on as the given pair of value `v`, has the value `(V (y, x) + v) / 2 ≤ 0`. -/
theorem le_neg_of_mem_dyadicValues {x y : X} {v : ℝ} (hv : v ∈ dyadicValues V x y) :
    v ≤ -V y x := by
  have h := midpoint_mem_dyadicValues (V := V) (x := (2 : ℝ)⁻¹ • (x + y))
    (y := (1 : ℝ) • (2 : ℝ)⁻¹ • (x + y)) (d := (2 : ℝ)⁻¹ • (x - y)) (e := -1) (Or.inr rfl)
    (v₁ := V y x) (v₂ := v) ?_ ?_
  · linarith [hV _ 1 (Or.inl rfl) _ h]
  · convert self_mem_dyadicValues V y x using 2 <;> module
  · convert hv using 2 <;> module

/-- `W⁰` is finite. -/
theorem bddAbove_dyadicValues (x y : X) : BddAbove (dyadicValues V x y) :=
  ⟨-V y x, fun _ hv => le_neg_of_mem_dyadicValues hV hv⟩

/-- 1°: `V ≤ W⁰`. -/
theorem le_dyadicBellman (x y : X) : V x y ≤ dyadicBellman V x y :=
  le_csSup (bddAbove_dyadicValues hV x y) (self_mem_dyadicValues V x y)

/-- 3°: `W⁰ (x, ±x) ≤ 0`. -/
theorem dyadicBellman_nonpos (x : X) {e : ℝ} (he : e = 1 ∨ e = -1) :
    dyadicBellman V x (e • x) ≤ 0 :=
  csSup_le ⟨_, self_mem_dyadicValues V _ _⟩ (hV x e he)

/-- `W⁰` is midpoint concave along the lines of slope `±1`, by splicing. -/
theorem dyadicBellman_midpoint (x y d : X) {e : ℝ} (he : e = 1 ∨ e = -1) :
    (dyadicBellman V (x - d) (y - e • d) + dyadicBellman V (x + d) (y + e • d)) / 2 ≤
      dyadicBellman V x y := by
  have hne : ∀ x y, (dyadicValues V x y).Nonempty := fun x y => ⟨_, self_mem_dyadicValues V x y⟩
  have key : ∀ v₁ ∈ dyadicValues V (x - d) (y - e • d),
      ∀ v₂ ∈ dyadicValues V (x + d) (y + e • d), (v₁ + v₂) / 2 ≤ dyadicBellman V x y :=
    fun v₁ h₁ v₂ h₂ =>
      le_csSup (bddAbove_dyadicValues hV x y) (midpoint_mem_dyadicValues he h₁ h₂)
  have h : dyadicBellman V (x - d) (y - e • d) ≤
      2 * dyadicBellman V x y - dyadicBellman V (x + d) (y + e • d) :=
    csSup_le (hne _ _) fun v₁ hv₁ => le_sub_comm.mp <| csSup_le (hne _ _) fun v₂ hv₂ => by
      linarith [key v₁ hv₁ v₂ hv₂]
  linarith

/-- 2°: for `V` locally bounded from below, `t ↦ W⁰ (x + t z, y ± t z)` is concave on `ℝ`: it is
midpoint concave, and locally bounded from below by `V` (`concaveOn_of_midpoint`). -/
theorem concaveOn_dyadicBellman
    (hVb : ∀ q : X × X, ∃ U ∈ nhds q, ∃ C : ℝ, ∀ r ∈ U, C ≤ V r.1 r.2) (x y z : X) {e : ℝ}
    (he : e = 1 ∨ e = -1) :
    ConcaveOn ℝ Set.univ fun t : ℝ => dyadicBellman V (x + t • z) (y + e • t • z) := by
  refine concaveOn_of_midpoint (fun s t => ?_) fun t => ?_
  · convert dyadicBellman_midpoint hV (x + ((s + t) / 2) • z) (y + e • ((s + t) / 2) • z)
      (((t - s) / 2) • z) he using 4 <;> module
  · obtain ⟨U, hU, C, hC⟩ := hVb (x + t • z, y + e • t • z)
    have hc : Continuous fun s : ℝ => (x + s • z, y + e • s • z) := by fun_prop
    exact ⟨_, hc.continuousAt.preimage_mem_nhds hU, C, fun s hs =>
      (hC _ hs).trans (le_dyadicBellman hV _ _)⟩

end Bellman

section Start

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Martingales with a start: a dyadic `UMD_p` constant `β` gives
`‖e x + Σ σ_k ε_k ξ_k‖_p ≤ β ‖x + Σ ε_k ξ_k‖_p`, `e = ±1`. The martingales of the source start
anywhere, with `dg_0 = ±df_0`; those of `IsDyadicUMDBound` start at `0`. With one more sign `ε_0`,
the Paley–Walsh martingales of `(x, ε_0 ξ_0, ε_0 ξ_1, …)` and of its transform by the signs
`(e, σ_0, σ_1, …)` are `ε_0 (x + Σ ε_k ξ_k)` and `ε_0 (e x + Σ σ_k ε_k ξ_k)`. -/
theorem lpNorm_start_transform_le {p β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound X p (ENNReal.ofReal β)) {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    {σ : Fin N → (Fin N → Bool) → ℝ} (hξ : IsPredictable ξ) (hσ : IsPredictable σ)
    (hs : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (x : X) {e : ℝ} (he : e = 1 ∨ e = -1) :
    SignCube.lpNorm (fun x => ‖x‖) p
        (fun ε => e • x + paleyWalsh (fun k ε => σ k ε • ξ k ε) N ε) ≤
      β * SignCube.lpNorm (fun x => ‖x‖) p (fun ε => x + paleyWalsh ξ N ε) := by
  have key : ∀ (d : X) (ζ : Fin N → (Fin N → Bool) → X),
      SignCube.lpNorm (fun x => ‖x‖) p
          (paleyWalsh (prepend d fun b k ε => coin b • ζ k ε) (N + 1)) =
        SignCube.lpNorm (fun x => ‖x‖) p fun ε => d + paleyWalsh ζ N ε := by
    intro d ζ
    simp only [SignCube.lpNorm, avg_succ, paleyWalsh_prepend, paleyWalsh_smul, ← smul_add,
      norm_smul, Real.norm_eq_abs, abs_coin, one_mul, add_self_div_two]
  have h := hβ (N + 1) (prepend x fun b k ε => coin b • ξ k ε) (prepend e fun _ => σ)
    (isPredictable_prepend x fun b => (umdd_isPredictable_const (coin b)).smul hξ)
    (isPredictable_prepend e fun _ => hσ) (prepend_sign he fun _ => hs) (N + 1)
  rw [smul_prepend, ← ENNReal.ofReal_mul hβ0, ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hβ0 (lpNorm_nonneg (fun x => norm_nonneg x) p _)), key] at h
  simpa only [smul_comm (σ _ _) (coin _), key] using h

end Start

section SecondApproach

/-- The function `V (x, y) = |y|^p − β^p |x|^p` of the moment inequality `‖g‖_p ≤ β ‖f‖_p`; its
`W⁰` is the source's `U⁰` (3.63) for the dyadic pairs. -/
private noncomputable def momentFun (p β x y : ℝ) : ℝ := |y| ^ p - β ^ p * |x| ^ p

/-- The condition (3.214) for `V (x, y) = |y|^p − β^p |x|^p`, `β` a dyadic `UMD_p` constant of `ℝ`:
`E |g|^p ≤ β^p E |f|^p` for the dyadic pairs started at `(x, ±x)`. -/
private theorem momentFun_nonpos {p β : ℝ} (hp : 0 < p) (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) (x e : ℝ) (he : e = 1 ∨ e = -1) :
    ∀ v ∈ dyadicValues (momentFun p β) x (e • x), v ≤ 0 := by
  rintro v ⟨N, ξ, σ, hξ, hσ, hs, rfl⟩
  have h0 : ∀ F : (Fin N → Bool) → ℝ, 0 ≤ SignCube.lpNorm (fun x => ‖x‖) p F :=
    fun F => lpNorm_nonneg (fun x => norm_nonneg x) p F
  have h := Real.rpow_le_rpow (h0 _) (lpNorm_start_transform_le hβ0 hβ hξ hσ hs x he) hp.le
  rw [Real.mul_rpow hβ0 (h0 _), lpNorm_rpow (fun x => norm_nonneg x) hp,
    lpNorm_rpow (fun x => norm_nonneg x) hp] at h
  simp only [momentFun, avg_sub, avg_const_mul]
  exact sub_nonpos.mpr h

/-- `V (x, y) = |y|^p − β^p |x|^p` is continuous, so locally bounded from below. -/
private theorem momentFun_locallyBounded {p : ℝ} (hp : 0 < p) (β : ℝ) (q : ℝ × ℝ) :
    ∃ U ∈ nhds q, ∃ C : ℝ, ∀ r ∈ U, C ≤ momentFun p β r.1 r.2 := by
  have hc : Continuous fun r : ℝ × ℝ => momentFun p β r.1 r.2 :=
    ((Real.continuous_rpow_const hp.le).comp continuous_snd.abs).sub
      (continuous_const.mul ((Real.continuous_rpow_const hp.le).comp continuous_fst.abs))
  exact ⟨_, hc.continuousAt.eventually_const_le (sub_one_lt _), _, fun _ hr => hr⟩

/-- If `(f, g)` is a dyadic pair started at `(x, y)`, `(λ f, ±λ g)` is one started at
`(λ x, ±λ y)`, and `E V (λ f, ±λ g) = |λ|^p E V (f, g)`. -/
private theorem mul_mem_dyadicValues {p β x y v : ℝ} (l : ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hv : v ∈ dyadicValues (momentFun p β) x y) :
    |l| ^ p * v ∈ dyadicValues (momentFun p β) (l * x) (s * (l * y)) := by
  obtain ⟨N, ξ, σ, hξ, hσ, hσ1, rfl⟩ := hv
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  refine ⟨N, fun k ε => l • ξ k ε, fun k ε => s • σ k ε, (umdd_isPredictable_const l).smul hξ,
    (umdd_isPredictable_const s).smul hσ, fun k ε => ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hσ1 k ε with h | h <;> simp [h]
  · have e1 : (fun (k : Fin N) (ε : Fin N → Bool) => (s • σ k ε) • l • ξ k ε) =
        fun k ε => (s * l) • σ k ε • ξ k ε := by
      funext k ε
      simp only [smul_eq_mul]
      ring
    rw [e1, ← avg_const_mul]
    congr 1
    funext ε
    rw [paleyWalsh_smul, paleyWalsh_smul]
    simp only [momentFun, smul_eq_mul, mul_assoc, ← mul_add, abs_mul, hs1, one_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    ring

/-- **Homogeneity** (p. 56): `U⁰ (λ x, ±λ y) = |λ|^p U⁰ (x, y)` for `λ ≠ 0`. -/
private theorem dyadicBellman_mul {p β : ℝ} (hp : 0 < p) (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) {l s : ℝ} (hl : l ≠ 0)
    (hs : s = 1 ∨ s = -1) (x y : ℝ) :
    dyadicBellman (momentFun p β) (l * x) (s * (l * y)) =
      |l| ^ p * dyadicBellman (momentFun p β) x y := by
  have hle : ∀ l : ℝ, l ≠ 0 → ∀ x y, |l| ^ p * dyadicBellman (momentFun p β) x y ≤
      dyadicBellman (momentFun p β) (l * x) (s * (l * y)) := by
    intro l hl x y
    have hlp : 0 < |l| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hl) p
    rw [← le_div_iff₀' hlp]
    refine csSup_le ⟨_, self_mem_dyadicValues _ x y⟩ fun v hv => ?_
    rw [le_div_iff₀' hlp]
    exact le_csSup (bddAbove_dyadicValues (momentFun_nonpos hp hβ0 hβ) _ _)
      (mul_mem_dyadicValues l hs hv)
  refine le_antisymm ?_ (hle l hl x y)
  -- the other inequality is the first one for `λ⁻¹` at the point `(λ x, ±λ y)`
  have h := hle l⁻¹ (inv_ne_zero hl) (l * x) (s * (l * y))
  have e1 : s * (l⁻¹ * (s * (l * y))) = y := by
    rcases hs with rfl | rfl <;> field_simp
  rwa [e1, inv_mul_cancel_left₀ hl, abs_inv, Real.inv_rpow (abs_nonneg l),
    inv_mul_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.mpr hl) p)] at h

open Filter Topology in
/-- The one-sided derivatives at `1` (p. 56–57): if `w` is concave on `ℝ` and
`w (x) = (2x − 1)^p w (x / (2x − 1))` for `x > 1` (3.65), then `w' (1+) + w' (1−) = 2 p w (1)`: let
`x ↓ 1` in
`(w (x) − w (1)) / (x − 1) + (2x − 1)^{p−1} (w (1) − w (z)) / (1 − z) =
2 w (1) ((2x − 1)^p − 1) / ((2x − 1) − 1)`, `z = x / (2x − 1)`. The source prints `x / (2x + 1)` for
`z` in this display; here it is the `x / (2x − 1)` of (3.65). -/
private theorem rightDeriv_add_leftDeriv {p : ℝ} {w : ℝ → ℝ} (hw : ConcaveOn ℝ Set.univ w)
    (hrefl : ∀ x, 1 < x → w x = (2 * x - 1) ^ p * w (x / (2 * x - 1))) :
    derivWithin w (Set.Ioi 1) 1 + derivWithin w (Set.Iio 1) 1 = 2 * p * w 1 := by
  have h1 : (1 : ℝ) ∈ interior Set.univ := by simp
  -- the one-sided derivatives exist, by concavity
  have hR : Tendsto (slope w 1) (𝓝[>] 1) (𝓝 (derivWithin w (Set.Ioi 1) 1)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (by simpa using (hw.neg.differentiableWithinAt_Ioi_of_mem_interior h1).neg.hasDerivWithinAt)
  have hL : Tendsto (slope w 1) (𝓝[<] 1) (𝓝 (derivWithin w (Set.Iio 1) 1)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (by simpa using (hw.neg.differentiableWithinAt_Iio_of_mem_interior h1).neg.hasDerivWithinAt)
  -- `x / (2x − 1) ↑ 1` and `2x − 1 ↓ 1` as `x ↓ 1`
  have hz : Tendsto (fun x : ℝ => x / (2 * x - 1)) (𝓝[>] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
    · have : ContinuousAt (fun x : ℝ => x / (2 * x - 1)) 1 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      simpa [ContinuousAt, show (2 : ℝ) - 1 = 1 by norm_num] using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx : 1 < x := hx
      rw [Set.mem_Iio, div_lt_one (by linarith)]
      linarith
  have hs : Tendsto (fun x : ℝ => 2 * x - 1) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
    · have : ContinuousAt (fun x : ℝ => 2 * x - 1) 1 := by fun_prop
      simpa [ContinuousAt, show (2 : ℝ) - 1 = 1 by norm_num] using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx : 1 < x := hx
      exact (by linarith : (1 : ℝ) < 2 * x - 1).ne'
  have hpow : Tendsto (slope (fun t : ℝ => t ^ p) 1) (𝓝[≠] 1) (𝓝 p) := by
    simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl (one_ne_zero (α := ℝ)))).tendsto_slope
  have hpow' : Tendsto (fun x : ℝ => (2 * x - 1) ^ (p - 1)) (𝓝[>] 1) (𝓝 1) := by
    have := (Real.continuousAt_rpow_const (1 : ℝ) (p - 1) (Or.inl one_ne_zero)).tendsto.comp
      (hs.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  -- the limits of the two sides of the identity
  have hsum := hR.add (hpow'.mul (hL.comp hz))
  have hlim := (hpow.comp hs).const_mul (2 * w 1)
  rw [one_mul] at hsum
  rw [tendsto_nhds_unique (hsum.congr' ?_) hlim]
  · ring
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx : 1 < x := hx
    have hx0 : 2 * x - 1 ≠ 0 := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    simp only [Function.comp_apply, slope_def_field, Real.one_rpow, hrefl x hx,
      Real.rpow_sub_one hx0, div_sub_one hx0, show 2 * x - 1 - 1 = 2 * (x - 1) by ring,
      show x - (2 * x - 1) = -(x - 1) by ring]
    field_simp
    ring

/-- The end of the second approach: for `w` concave on `ℝ` with (3.65), (3.66)
`w (1 / (β + 1)) ≥ 0` and `w (0) ≥ 1`, `β ≥ 1 / (p − 1)`, by (3.67):
`((β + 1) / β) w (1) ≥ (w (1) − w (1 / (β + 1))) / (1 − 1 / (β + 1)) ≥ w' (1−) ≥
(w' (1−) + w' (1+)) / 2 = p w (1)`, and `w (1) < 0`. The source takes `w (1) < 0` from concavity,
(3.66) and `w (0) ≥ 1`, three facts that `w ≡ 1` has too; (3.66) is read as (3.65), which gives the
end of (3.67): `p w (1) ≤ w' (1−) ≤ w (1) − w (0) ≤ w (1) − 1`. -/
private theorem inv_sub_one_le_of_concaveOn {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {w : ℝ → ℝ}
    (hw : ConcaveOn ℝ Set.univ w)
    (hrefl : ∀ x, 1 < x → w x = (2 * x - 1) ^ p * w (x / (2 * x - 1)))
    (hβw : 0 ≤ w (β + 1)⁻¹) (h0 : 1 ≤ w 0) : (p - 1)⁻¹ ≤ β := by
  have h1 : (1 : ℝ) ∈ interior Set.univ := by simp
  have hdL : DifferentiableWithinAt ℝ w (Set.Iio 1) 1 := by
    simpa using (hw.neg.differentiableWithinAt_Iio_of_mem_interior h1).neg
  -- `w' (1+) ≤ w' (1−)`, so `p w (1) ≤ w' (1−)`
  have hsum := rightDeriv_add_leftDeriv hw hrefl
  have hRL : derivWithin w (Set.Ioi 1) 1 ≤ derivWithin w (Set.Iio 1) 1 := by
    have h := hw.neg.leftDeriv_le_rightDeriv_of_mem_interior h1
    rwa [derivWithin.neg, derivWithin.neg, neg_le_neg_iff] at h
  -- `w (1) < 0`: `w' (1−)` is at most the slope of the chord from `0` to `1`
  have hw1 : w 1 < 0 := by
    have hL0 := hw.leftDeriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hdL
    rw [slope_def_field, sub_zero, div_one] at hL0
    by_contra! h
    nlinarith
  -- `w' (1−)` is at most the slope of the chord from `1 / (β + 1)` to `1`
  have ha : (β + 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hL := hw.leftDeriv_le_slope (Set.mem_univ _) (Set.mem_univ _) ha hdL
  rw [slope_def_field, le_div_iff₀ (sub_pos.mpr ha)] at hL
  have hLβ : derivWithin w (Set.Iio 1) 1 * β ≤ w 1 * (β + 1) := by
    calc derivWithin w (Set.Iio 1) 1 * β
        = derivWithin w (Set.Iio 1) 1 * (1 - (β + 1)⁻¹) * (β + 1) := by field_simp; ring
      _ ≤ w 1 * (β + 1) := by gcongr; linarith
  have hpL : p * w 1 * β ≤ derivWithin w (Set.Iio 1) 1 * β := by gcongr; linarith
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  by_contra! h
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr h) hw1]

/-- **Sharpness for `1 < p ≤ 2`** (Theorem 3.5, the second approach; Theorem 3.34): a dyadic
`UMD_p` constant `β` of `ℝ` is at least `1 / (p − 1)`. The bound holds for every `p > 1` and is the
sharp one for `1 < p ≤ 2`. With `U⁰ = W⁰` for `V (x, y) = |y|^p − β^p |x|^p`, the function
`w (x) = U⁰ (x, 1 − x)` (3.64) satisfies the hypotheses of `inv_sub_one_le_of_concaveOn`. -/
theorem inv_sub_one_le_of_isDyadicUMDBound {p : ℝ} (hp : 1 < p) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) : (p - 1)⁻¹ ≤ β := by
  have hp0 : 0 < p := by linarith
  have hβ1 : 1 ≤ β := by simpa using umdd_one_le_of_isDyadicUMDBound hp0 hβ
  have hV := momentFun_nonpos hp0 hβ0 hβ
  have hconc := concaveOn_dyadicBellman hV (momentFun_locallyBounded hp0 β) 0 1 1
    (e := -1) (Or.inr rfl)
  simp only [smul_eq_mul, mul_one, zero_add, neg_one_mul, ← sub_eq_add_neg] at hconc
  refine inv_sub_one_le_of_concaveOn hp (by linarith) hconc (fun x hx => ?_) ?_ ?_
  · -- (3.65): `U⁰ (x, 1 − x) = U⁰ (x, x − 1) = (2x − 1)^p U⁰ (z, 1 − z)`, `z = x / (2x − 1)`
    have hx0 : 0 < 2 * x - 1 := by linarith
    have h := dyadicBellman_mul hp0 hβ0 hβ hx0.ne' (s := -1) (Or.inr rfl) (x / (2 * x - 1))
      (1 - x / (2 * x - 1))
    rw [abs_of_pos hx0, mul_one_sub, mul_div_cancel₀ _ hx0.ne'] at h
    rw [← h]
    congr 1
    ring
  · -- (3.66): `V (1 / (β + 1), 1 − 1 / (β + 1)) = 0`
    refine le_trans ?_ (le_dyadicBellman hV _ _)
    have h1 : 1 - (β + 1)⁻¹ = β * (β + 1)⁻¹ := by field_simp; ring
    rw [momentFun, h1, abs_mul, abs_of_nonneg hβ0, Real.mul_rpow hβ0 (abs_nonneg _), sub_self]
  · refine le_trans ?_ (le_dyadicBellman hV _ _)
    simp [momentFun, Real.zero_rpow hp0.ne']

end SecondApproach

section Duality

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Paley–Walsh martingale of `ξ` at time `n` is that of `1_{k < n} ξ_k` at time `N`. -/
private theorem paleyWalsh_cut {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (n : ℕ) :
    paleyWalsh (fun k ε => if k.val < n then ξ k ε else 0) N = paleyWalsh ξ n := by
  funext ε
  rw [paleyWalsh_of_le _ le_rfl]
  simp only [paleyWalsh, Finset.sum_filter, smul_ite, smul_zero]

/-- A dyadic `UMD_p` bound at the final times `n = N` is one at every time `n`: cut the family off
after `n`. -/
private theorem isDyadicUMDBound_of_final {p β : ℝ} (hβ0 : 0 ≤ β)
    (h : ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
      IsPredictable ξ → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) →
        SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) N) ≤
          β * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N)) :
    IsDyadicUMDBound X p (ENNReal.ofReal β) := by
  intro N ξ σ hξ hσ hs n
  rw [← ENNReal.ofReal_mul hβ0]
  refine ENNReal.ofReal_le_ofReal ?_
  have := h N (fun k ε => if k.val < n then ξ k ε else 0) σ (fun k ε ε' hk => ?_) hσ hs
  · simpa only [smul_ite, smul_zero, paleyWalsh_cut] using this
  · simp only [hξ k ε ε' hk]

/-- `E Σ ε_k a_k = 0` for a predictable `a`. -/
private theorem avg_paleyWalsh {N : ℕ} {a : Fin N → (Fin N → Bool) → ℝ} (ha : IsPredictable a) :
    avg (paleyWalsh a N) = 0 := by
  have h := congrFun (condAvg_paleyWalsh ha 0 N) fun _ => false
  rwa [condAvg_zero_real, Nat.zero_min, paleyWalsh_zero] at h

/-- Orthogonality of the martingale differences: `E (Σ ε_k a_k) (Σ ε_k b_k) = Σ E a_k b_k` for
predictable `a`, `b`. -/
private theorem avg_paleyWalsh_mul {N : ℕ} {a b : Fin N → (Fin N → Bool) → ℝ}
    (ha : IsPredictable a) (hb : IsPredictable b) :
    avg (fun ε => paleyWalsh a N ε * paleyWalsh b N ε) = ∑ k, avg fun ε => a k ε * b k ε := by
  simp only [paleyWalsh_of_le _ le_rfl, Finset.sum_mul_sum, avg_sum, smul_eq_mul]
  have hflip : ∀ {a : Fin N → (Fin N → Bool) → ℝ}, IsPredictable a → ∀ {k l : Fin N}, l ≤ k →
      ∀ ε, a l (SignCube.flip k ε) = a l ε := fun ha k l hl ε =>
    ha l _ _ fun j hj => flip_apply_of_ne (hj.trans_le hl).ne ε
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]
  · congr 1
    funext ε
    rw [mul_mul_mul_comm, coin_mul_self, one_mul]
  · -- flip the later of the two signs
    rcases lt_or_gt_of_ne hl with hl | hl
    · refine scb_avg_eq_zero_of_flip k fun ε => ?_
      rw [hflip ha le_rfl, hflip hb hl.le, flip_apply_self, flip_apply_of_ne hl.ne, coin_not]
      ring
    · refine scb_avg_eq_zero_of_flip l fun ε => ?_
      rw [hflip ha hl.le, hflip hb le_rfl, flip_apply_self, flip_apply_of_ne hl.ne, coin_not]
      ring

/-- A function on the cube is a constant plus a Paley–Walsh martingale at the final time: the
martingale `E [F | ℱ_k]`. -/
private theorem exists_eq_const_add_paleyWalsh {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    ∃ (c : ℝ) (ζ : Fin N → (Fin N → Bool) → ℝ), IsPredictable ζ ∧
      ∀ ε, F ε = c + paleyWalsh ζ N ε := by
  have hM : IsCubeMartingale fun k => condAvg k F := by
    refine ⟨fun k ε ε' h => ?_, fun n => condAvg_condAvg (Nat.le_succ n) F⟩
    simp only [condAvg]
    congr 1
    refine Finset.sum_congr rfl fun η _ => congrArg F (funext fun j => ?_)
    simp only [splice]
    split_ifs with hj
    exacts [h j hj, rfl]
  obtain ⟨ζ, hζ, h⟩ := exists_paleyWalsh_of_isCubeMartingale hM
  refine ⟨avg F, ζ, hζ, fun ε => ?_⟩
  rw [← condAvg_zero_real F ε, ← h N ε, condAvg_of_isAdapted fun ε ε' h => ?_]
  rw [funext fun j => h j j.isLt]

/-- **Hölder's inequality** on the cube: `E f h ≤ ‖f‖_p ‖h‖_q`. -/
private theorem avg_mul_le {N : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (f h : (Fin N → Bool) → ℝ) :
    avg (fun ε => f ε * h ε) ≤
      SignCube.lpNorm (fun x => ‖x‖) p f * SignCube.lpNorm (fun x => ‖x‖) q h := by
  have h1 : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
  rw [scb_lpNorm_eq_sum fun x => norm_nonneg x, scb_lpNorm_eq_sum fun x => norm_nonneg x,
    div_mul_div_comm, ← Real.rpow_add (by positivity), h1, Real.rpow_one]
  exact div_le_div_of_nonneg_right (Real.inner_le_Lp_mul_Lq _ f h hpq) (by positivity)

/-- **Duality** (p. 59): a dyadic `UMD_p` constant `β` of `ℝ` is a dyadic `UMD_q` constant for the
conjugate exponent `q = p / (p − 1)`. For `f = Σ ε_k φ_k` and `g = Σ σ_k ε_k φ_k` let
`ξ = |g|^{q−1} sgn g`, so that `‖ξ‖_p = ‖g‖_q^{q/p}`, and write `ξ = c + Σ ε_k ζ_k`; then, by
orthogonality of the martingale differences and Hölder's inequality,
`‖g‖_q^q = E g ξ = E f (c + Σ σ_k ε_k ζ_k) ≤ ‖f‖_q ‖c + Σ σ_k ε_k ζ_k‖_p ≤ ‖f‖_q β ‖ξ‖_p =
β ‖f‖_q ‖g‖_q^{q/p}`. -/
theorem isDyadicUMDBound_conjExponent {p : ℝ} (hp : 1 < p) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) :
    IsDyadicUMDBound ℝ (p / (p - 1)) (ENNReal.ofReal β) := by
  have hpq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  set q := p / (p - 1)
  have hq0 : 0 < q := hpq.pos
  refine isDyadicUMDBound_of_final hβ0 fun N φ σ hφ hσ hs => ?_
  set g := paleyWalsh (fun k ε => σ k ε • φ k ε) N with hg
  have h0 : ∀ (r : ℝ) (F : (Fin N → Bool) → ℝ), 0 ≤ SignCube.lpNorm (fun x => ‖x‖) r F :=
    fun r F => lpNorm_nonneg (fun x => norm_nonneg x) r F
  -- `ξ = |g|^{q−1} sgn g = c + Σ ε_k ζ_k`
  obtain ⟨c, ζ, hζ, hξ⟩ := exists_eq_const_add_paleyWalsh
    fun ε => |g ε| ^ (q - 1) * (SignType.sign (g ε) : ℝ)
  -- `E g ξ = ‖g‖_q^q`
  have h1 : avg (fun ε => g ε * (c + paleyWalsh ζ N ε)) =
      SignCube.lpNorm (fun x => ‖x‖) q g ^ q := by
    rw [lpNorm_rpow (fun x => norm_nonneg x) hq0]
    congr 1
    funext ε
    rw [← hξ, mul_left_comm, self_mul_sign, Real.norm_eq_abs, ← Real.rpow_add_one' (abs_nonneg _)
      (by simpa using hq0.ne'), sub_add_cancel]
  -- `‖ξ‖_p = ‖g‖_q^{q/p}`
  have h2 : SignCube.lpNorm (fun x => ‖x‖) p (fun ε => c + paleyWalsh ζ N ε) =
      SignCube.lpNorm (fun x => ‖x‖) q g ^ (q / p) := by
    rw [div_eq_mul_one_div, Real.rpow_mul (h0 _ _), lpNorm_rpow (fun x => norm_nonneg x) hq0,
      SignCube.lpNorm]
    congr 2
    funext ε
    rw [← hξ, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases eq_or_ne (g ε) 0 with h | h
    · simp [h, Real.zero_rpow hq0.ne', Real.zero_rpow hpq.symm.ne_zero]
    · have hsgn : |(SignType.sign (g ε) : ℝ)| = 1 := by
        rcases h.lt_or_gt with h | h <;> simp [h]
      rw [abs_mul, hsgn, mul_one, abs_of_nonneg (by positivity), ← Real.rpow_mul (abs_nonneg _),
        hpq.sub_one_mul_conj]
  -- `E g ξ = Σ E σ_k φ_k ζ_k = E f (c + Σ σ_k ε_k ζ_k)`
  have h3 : avg (fun ε => g ε * (c + paleyWalsh ζ N ε)) = avg fun ε => paleyWalsh φ N ε *
      ((1 : ℝ) • c + paleyWalsh (fun k ε => σ k ε • ζ k ε) N ε) := by
    simp only [mul_add, avg_add, hg, one_smul, mul_comm _ c, avg_const_mul]
    rw [avg_paleyWalsh (hσ.smul hφ), avg_paleyWalsh hφ, avg_paleyWalsh_mul (hσ.smul hφ) hζ,
      avg_paleyWalsh_mul hφ (hσ.smul hζ)]
    simp only [smul_eq_mul, mul_assoc, mul_left_comm]
  -- `‖g‖_q^q ≤ ‖f‖_q β ‖g‖_q^{q/p}`
  have h4 : SignCube.lpNorm (fun x => ‖x‖) q g ^ q ≤
      SignCube.lpNorm (fun x => ‖x‖) q (paleyWalsh φ N) *
        (β * SignCube.lpNorm (fun x => ‖x‖) q g ^ (q / p)) := by
    rw [← h1, h3, ← h2]
    exact (avg_mul_le hpq _ _).trans (mul_le_mul_of_nonneg_left
      (lpNorm_start_transform_le hβ0 hβ hζ hσ hs c (Or.inl rfl)) (h0 _ _))
  rcases (h0 q g).eq_or_lt with hG | hG
  · rw [← hG]
    exact mul_nonneg hβ0 (h0 _ _)
  · refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hG (q / p))
    calc SignCube.lpNorm (fun x => ‖x‖) q g * SignCube.lpNorm (fun x => ‖x‖) q g ^ (q / p)
        = SignCube.lpNorm (fun x => ‖x‖) q g ^ q := by
          rw [hpq.div_conj_eq_sub_one, Real.rpow_sub_one hG.ne', mul_div_cancel₀ _ hG.ne']
      _ ≤ _ := h4.trans_eq (by ring)

/-- `p / (p − 1) − 1 = 1 / (p − 1)`. -/
private theorem conjExponent_sub_one {p : ℝ} (hp : 1 < p) : p / (p - 1) - 1 = (p - 1)⁻¹ := by
  have : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Sharpness for `p ≥ 2`** (Theorem 3.5, p. 59; Theorem 3.34): a dyadic `UMD_p` constant `β` of
`ℝ` is at least `p − 1`: it is a constant for the conjugate exponent `q`, so
`β ≥ 1 / (q − 1) = p − 1`. The bound holds for every `p > 1`. -/
theorem sub_one_le_of_isDyadicUMDBound {p : ℝ} (hp : 1 < p) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) : p - 1 ≤ β := by
  have hq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have h := inv_sub_one_le_of_isDyadicUMDBound hq.lt hβ0 (isDyadicUMDBound_conjExponent hp hβ0 hβ)
  rwa [conjExponent_sub_one hp, inv_inv] at h

end Duality

section Constants

/-- A dyadic `UMD_p` constant of `ℝ` is at least `p* − 1 = max (p − 1, 1 / (p − 1))`. -/
private theorem pStar_sub_one_le {p : ℝ} (hp : 1 < p) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : IsDyadicUMDBound ℝ p (ENNReal.ofReal β)) : pStar p - 1 ≤ β := by
  rw [pStar, ← max_sub_sub_right, conjExponent_sub_one hp]
  exact max_le (sub_one_le_of_isDyadicUMDBound hp hβ0 hβ)
    (inv_sub_one_le_of_isDyadicUMDBound hp hβ0 hβ)

/-- `UMD_p^Δ (ℝ) ≥ p* − 1` (Theorems 3.5 and 3.34). -/
theorem le_dyadicUMDConst_real {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (pStar p - 1) ≤ dyadicUMDConst ℝ p := by
  rcases eq_or_ne (dyadicUMDConst ℝ p) ⊤ with h | h
  · simp [h]
  · refine ENNReal.ofReal_le_of_le_toReal (pStar_sub_one_le hp ENNReal.toReal_nonneg ?_)
    rw [ENNReal.ofReal_toReal h]
    exact isDyadicUMDBound_dyadicUMDConst (by linarith)

/-- **The dyadic `UMD_p` constant of `ℝ`** is `p* − 1` (Theorem 3.34, Remark 3.8). -/
theorem dyadicUMDConst_real {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst ℝ p = ENNReal.ofReal (pStar p - 1) :=
  le_antisymm (dyadicUMDConst_le_of_innerProductSpace hp) (le_dyadicUMDConst_real hp)

/-- **The `UMD_p` constant of `ℝ`** is `p* − 1` (Theorem 3.5). -/
theorem umdConst_real {p : ℝ} (hp : 1 < p) : umdConst ℝ p = ENNReal.ofReal (pStar p - 1) :=
  le_antisymm (umdConst_le_of_innerProductSpace hp)
    ((le_dyadicUMDConst_real hp).trans (dyadicUMDConst_le_umdConst hp))

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [Nontrivial H]

/-- `UMD_p^Δ (H) = p* − 1` for a real Hilbert space `H ≠ 0` (Theorem 3.34, Remark 3.8): `ℝ` embeds
isometrically, by a unit vector. -/
theorem dyadicUMDConst_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst H p = ENNReal.ofReal (pStar p - 1) := by
  obtain ⟨v, hv⟩ := exists_norm_eq H zero_le_one
  exact le_antisymm (dyadicUMDConst_le_of_innerProductSpace hp) ((le_dyadicUMDConst_real hp).trans
    (dyadicUMDConst_le_of_linearIsometry (LinearIsometry.toSpanSingleton ℝ H hv) p))

/-- `UMD_p (H) = p* − 1` for a real Hilbert space `H ≠ 0` (Theorem 3.5). -/
theorem umdConst_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    umdConst H p = ENNReal.ofReal (pStar p - 1) :=
  le_antisymm (umdConst_le_of_innerProductSpace hp)
    ((dyadicUMDConst_of_innerProductSpace hp).ge.trans (dyadicUMDConst_le_umdConst hp))

end Hilbert

/-- **No constant below `p* − 1`** holds in the moment inequality, even for dyadic martingales
(Theorems 3.5 and 3.34): for `K < p* − 1` there are a real Paley–Walsh martingale `f = Σ ε_k φ_k`
and a transform `g = Σ σ_k ε_k φ_k` of `f` by predictable signs with `K ‖f‖_p < ‖g‖_p`. -/
theorem exists_lt_lpNorm_transform {p K : ℝ} (hp : 1 < p) (hK : K < pStar p - 1) :
    ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧ IsPredictable σ ∧
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
        K * SignCube.lpNorm (fun x => |x|) p (paleyWalsh φ N) <
          SignCube.lpNorm (fun x => |x|) p (paleyWalsh (fun k ε => σ k ε * φ k ε) N) := by
  by_contra! h
  have hβ := pStar_sub_one_le hp (le_max_right K 0) (isDyadicUMDBound_of_final (le_max_right K 0)
    fun N φ σ hφ hσ hs => (h N φ σ hφ hσ hs).trans (mul_le_mul_of_nonneg_right (le_max_left K 0)
      (lpNorm_nonneg (fun x => abs_nonneg x) p _)))
  have h1 : 0 < pStar p - 1 := by
    have := le_max_left p (p / (p - 1))
    rw [pStar]
    linarith
  exact absurd hβ (not_le.mpr (max_lt hK h1))

end Constants

end BanachProbability.Osekowski
