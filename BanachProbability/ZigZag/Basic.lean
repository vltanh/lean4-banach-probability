module

public import BanachProbability.UMD.Maurey.Basic
public import Mathlib.Analysis.Convex.Function

/-!
# Burkholder's characterisation of UMD by zig-zag concave functions

A Banach space `X` is `UMD_p`, `p ∈ (1, ∞)`, if and only if there are `β > 0` and a function
`U : X × X → ℝ` with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, and zig-zag concave:
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]` (`IsZigZagConcave`); then
`UMD_p (X) ≤ β` (D. L. Burkholder, *A geometrical characterization of Banach spaces in which
martingale difference sequences are unconditional*, Ann. Probab. 9 (1981), and *Boundary value
problems and sharp inequalities for martingale transforms*, Ann. Probab. 12 (1984);
Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016), Theorem 4.5.6). For a
complex space and `ε` in the closed unit disc of `ℂ` (`IsComplexZigZagConcave`), `U` bounds the
complex constant `UMD_{ℂ,p} (X)` (I. Yaroslavtsev, *Even Fourier multipliers and martingale
transforms in infinite dimensions*, Indag. Math. 29 (2018), Proposition 3.7).

* `U ⇒ UMD_p ≤ β`: on the cube, midpoint concavity along `(± v, ± σ v)` gives
  `E U (f_n, g_n) ≤ U (0, 0) = 0` for a Paley–Walsh martingale `f` and its transform `g`, with no
  measurability needed (`dyadicUMDConst_le_of_isZigZagConcave`); Maurey's theorem gives the full
  constant (`umdConst_le_of_isZigZagConcave`), and its complex version the complex one.
* `UMD_p < ∞ ⇒ U` exists: for `β > UMD_p^Δ (X)`, the Bellman function
  `U (x, y) = sup E [‖y + g‖^p − β^p ‖x + f‖^p]` over Paley–Walsh pairs with predictable
  multipliers in `[−1, 1]` (`bellmanFunction`) is finite (by the contraction principle,
  `lpNorm_paleyWalsh_mul_le`), midpoint concave along zig-zag lines (by splicing) and locally
  bounded, hence concave there (Bernstein–Doetsch, `concaveOn_of_midpoint`).
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

/-- `U : X × X → ℝ` is zig-zag concave for the obstacle `‖y‖^p − β^p ‖x‖^p` (real scalars):
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]`, `U (0, 0) = 0`, and
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
def IsZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℝ), |ε| ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- The complex version: `ε` ranges over the closed unit disc. -/
def IsComplexZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℂ), ‖ε‖ ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- **Bernstein–Doetsch**: a midpoint concave function on `ℝ` that is locally bounded below is
concave. -/
theorem concaveOn_of_midpoint {f : ℝ → ℝ} (hmid : ∀ a b, (f a + f b) / 2 ≤ f ((a + b) / 2))
    (hbdd : ∀ x, ∃ U ∈ nhds x, ∃ C : ℝ, ∀ y ∈ U, C ≤ f y) : ConcaveOn ℝ Set.univ f := by
  sorry

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The contraction principle** for Paley–Walsh martingales: a dyadic `UMD_p` constant also
bounds the transforms by predictable multipliers with values in `[−1, 1]`. -/
theorem lpNorm_paleyWalsh_mul_le {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞} (hβ : IsDyadicUMDBound X p β)
    {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X} {a : Fin N → (Fin N → Bool) → ℝ}
    (hξ : IsPredictable ξ) (ha : IsPredictable a) (ha1 : ∀ k ε, |a k ε| ≤ 1) (n : ℕ) :
    ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => a k ε • ξ k ε) n)) ≤
      β * ENNReal.ofReal (lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) := by
  sorry

variable (X) in
/-- Burkholder's Bellman function
`U (x, y) = sup E [‖y + g‖^p − β^p ‖x + f‖^p]`, over Paley–Walsh martingales `f = Σ ε_k ξ_k` and
their transforms `g = Σ a_k ε_k ξ_k` by predictable multipliers with values in `[−1, 1]`. -/
noncomputable def bellmanFunction (p β : ℝ) (x y : X) : ℝ :=
  sSup {v | ∃ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (a : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ ∧ IsPredictable a ∧ (∀ k ε, |a k ε| ≤ 1) ∧
      v = avg fun ε => ‖y + paleyWalsh (fun k ε => a k ε • ξ k ε) N ε‖ ^ p -
        β ^ p * ‖x + paleyWalsh ξ N ε‖ ^ p}

/-- For `β > UMD_p^Δ (X)`, the Bellman function is zig-zag concave. -/
theorem isZigZagConcave_bellmanFunction {p β : ℝ} (hp : 1 < p)
    (hβ : dyadicUMDConst X p < ENNReal.ofReal β) : IsZigZagConcave p β (bellmanFunction X p β) := by
  sorry

/-- A zig-zag concave function bounds the dyadic UMD constant: `UMD_p^Δ (X) ≤ β`. -/
theorem dyadicUMDConst_le_of_isZigZagConcave {p β : ℝ} (hp : 1 < p) (hβ : 0 < β)
    {U : X → X → ℝ} (hU : IsZigZagConcave p β U) : dyadicUMDConst X p ≤ ENNReal.ofReal β := by
  sorry

variable [CompleteSpace X]

/-- A zig-zag concave function bounds the UMD constant: `UMD_p (X) ≤ β` (Burkholder; HNVW I,
Theorem 4.5.6). -/
theorem umdConst_le_of_isZigZagConcave {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ}
    (hU : IsZigZagConcave p β U) : umdConst X p ≤ ENNReal.ofReal β := by
  sorry

/-- **Burkholder's characterisation of UMD** (Burkholder 1981; HNVW I, Theorem 4.5.6):
`UMD_p (X) < ∞` if and only if a zig-zag concave function exists for some `β > 0`. -/
theorem umdConst_lt_top_iff_exists_isZigZagConcave {p : ℝ} (hp : 1 < p) :
    umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U := by
  sorry

end Real

/-- A complex zig-zag concave function bounds the complex UMD constant:
`UMD_{ℂ,p} (X) ≤ β` (Yaroslavtsev 2018, Proposition 3.7; HNVW I, Theorem 4.5.6). -/
theorem complexUMDConst_le_of_isComplexZigZagConcave {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ}
    (hU : IsComplexZigZagConcave p β U) : complexUMDConst X p ≤ ENNReal.ofReal β := by
  sorry

end BanachProbability
