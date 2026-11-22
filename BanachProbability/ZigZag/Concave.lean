module

public import BanachProbability.UMD.Maurey.FiniteModel
public import Mathlib.Analysis.Convex.Jensen

/-!
# Zig-zag concave functions

The concavity lemmas behind Burkholder's characterisation of UMD, following Hytönen–van
Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016) (HNVW), §4.5.a and the beginning of
§4.5.b, p. 330–333. The scalars are `𝕜 = ℝ` or `ℂ`; a *sign* of `𝕜` is an `ε ∈ 𝕜` with `‖ε‖ = 1`.

* Lemma 4.5.2 (`concaveOn_of_midpoint` on `ℝ`, `concaveOn_iff_midpoint` on a topological vector
  space): a midpoint concave function that is locally bounded below is concave.
* Definition 4.5.3 (`IsSignZigZagConcave`): `z ↦ u (x + z, y + ε z)` is concave for all `x`, `y`
  and all signs `ε`.
* Lemma 4.5.4 (`isSignZigZagConcave_iff`, `IsSignZigZagConcave.sum_le`): Jensen's inequality
  `E u (x + ξ, y + ε ξ) ≤ u (x, y)` for simple random variables `ξ` with `E ξ = 0`.
* Lemma 4.5.5 (`IsSignZigZagConcave.integral_le`): `E u (f_{n+1}, g_{n+1}) ≤ E u (f_n, g_n)` for a
  martingale `f` on a finite probability space and its transform `g` by predictable signs.
* The homogenisation (4.31) (`zigZagHomogenize`): `ũ = inf_{α ≠ 0} |α|^{−p} u (α x, α y)`, which
  has the same properties as `u`, is `p`-homogeneous, and vanishes at `(0, 0)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Topology

namespace BanachProbability

open SignCube

section Midpoint

/-- Iterating midpoint concavity (HNVW, proof of Lemma 4.5.2): if `u` is midpoint concave and
nonnegative at `0` and `1`, then `u ≥ 0` at the dyadic rationals `k / 2^j` of `[0, 1]`. -/
private theorem zzg_dyadic_nonneg {u : ℝ → ℝ} (hmid : ∀ a b, (u a + u b) / 2 ≤ u ((a + b) / 2))
    (h0 : 0 ≤ u 0) (h1 : 0 ≤ u 1) :
    ∀ j k : ℕ, k ≤ 2 ^ j → 0 ≤ u ((k : ℝ) / 2 ^ j) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    interval_cases k
    · simpa using h0
    · simpa using h1
  | succ j ih =>
    intro k hk
    rw [pow_succ] at hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · -- `2 m / 2^{j+1} = m / 2^j`
      have h := ih m (by omega)
      rwa [show ((2 * m : ℕ) : ℝ) / 2 ^ (j + 1) = m / 2 ^ j by
        rw [pow_succ]; push_cast; field_simp]
    · -- `(2 m + 1) / 2^{j+1}` is the midpoint of `m / 2^j` and `(m + 1) / 2^j`
      have ha := ih m (by omega)
      have hb := ih (m + 1) (by omega)
      have h := hmid ((m : ℝ) / 2 ^ j) (((m + 1 : ℕ) : ℝ) / 2 ^ j)
      rw [show ((m : ℝ) / 2 ^ j + ((m + 1 : ℕ) : ℝ) / 2 ^ j) / 2 =
        ((2 * m + 1 : ℕ) : ℝ) / 2 ^ (j + 1) by rw [pow_succ]; push_cast; field_simp; ring] at h
      linarith

/-- The doubling step (HNVW, proof of Lemma 4.5.2): for `0 < λ < 1` there is a dyadic rational
`t ∈ [0, 1]` so close to `λ` that `λ₁ = 2 λ − t` is in `(0, 1)`; as `λ = (λ₁ + t) / 2` and
`u (t) ≥ 0`, midpoint concavity gives `u (λ₁) ≤ 2 u (λ)`. -/
private theorem zzg_doubling {u : ℝ → ℝ} (hmid : ∀ a b, (u a + u b) / 2 ≤ u ((a + b) / 2))
    (hdy : ∀ j k : ℕ, k ≤ 2 ^ j → 0 ≤ u ((k : ℝ) / 2 ^ j)) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    ∃ l', 0 < l' ∧ l' < 1 ∧ u l' ≤ 2 * u l := by
  -- `t = ⌊2^j λ⌋ / 2^j` with `2^{-j} < 1 − λ`
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - l)) (one_lt_two : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rw [div_lt_iff₀ (by linarith)] at hj
  set k : ℕ := ⌊l * 2 ^ j⌋₊
  have hk1 : (k : ℝ) ≤ l * 2 ^ j := Nat.floor_le (by positivity)
  have hk2 : l * 2 ^ j < k + 1 := Nat.lt_floor_add_one _
  have hkle : k ≤ 2 ^ j := by
    have : (k : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  have ht1 : (k : ℝ) / 2 ^ j ≤ l := by rwa [div_le_iff₀ hpos]
  have ht2 : 2 * l - 1 < (k : ℝ) / 2 ^ j := by
    rw [lt_div_iff₀ hpos]
    nlinarith
  refine ⟨2 * l - k / 2 ^ j, by linarith, by linarith, ?_⟩
  have h := hmid (2 * l - k / 2 ^ j) (k / 2 ^ j)
  rw [show (2 * l - (k : ℝ) / 2 ^ j + k / 2 ^ j) / 2 = l by ring] at h
  linarith [hdy j k hkle]

/-- The contradiction of the proof of HNVW, Lemma 4.5.2: a midpoint concave function bounded below
on `[0, 1]` with `u (0) = u (1) = 0` is nonnegative on `(0, 1)`, since iterating the doubling step
from `λ` with `u (λ) < 0` gives `λ_n ∈ (0, 1)` with `u (λ_n) ≤ 2^n u (λ) → −∞`. -/
private theorem zzg_nonneg_of_midpoint {u : ℝ → ℝ}
    (hmid : ∀ a b, (u a + u b) / 2 ≤ u ((a + b) / 2)) (h0 : u 0 = 0) (h1 : u 1 = 0)
    {C : ℝ} (hC : ∀ t, 0 ≤ t → t ≤ 1 → C ≤ u t) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : 0 ≤ u l := by
  by_contra hneg
  rw [not_le] at hneg
  have hdy := zzg_dyadic_nonneg hmid h0.ge h1.ge
  have hseq : ∀ n : ℕ, ∃ l', 0 < l' ∧ l' < 1 ∧ u l' ≤ 2 ^ n * u l := by
    intro n
    induction n with
    | zero => exact ⟨l, hl0, hl1, by simp⟩
    | succ n ih =>
      obtain ⟨l₁, h₁0, h₁1, h₁⟩ := ih
      obtain ⟨l₂, h₂0, h₂1, h₂⟩ := zzg_doubling hmid hdy h₁0 h₁1
      exact ⟨l₂, h₂0, h₂1, by rw [pow_succ]; linarith⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / u l) (one_lt_two : (1 : ℝ) < 2)
  rw [div_lt_iff_of_neg hneg] at hn
  obtain ⟨l', h0', h1', h'⟩ := hseq n
  linarith [hC l' h0'.le h1'.le]

/-- A function that is locally bounded below is bounded below on compact sets. -/
private theorem zzg_bddBelow_of_isCompact {E : Type*} [TopologicalSpace E] {u : E → ℝ}
    (hbdd : ∀ x, ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ V, C ≤ u y) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ y ∈ K, C ≤ u y := by
  refine hK.induction_on (p := fun K => ∃ C : ℝ, ∀ y ∈ K, C ≤ u y)
    ⟨0, fun y hy => absurd hy (Set.notMem_empty y)⟩ (fun s t hst ⟨C, hC⟩ => ?_)
    (fun s t ⟨C, hC⟩ ⟨D, hD⟩ => ?_) (fun x _ => ?_)
  · exact ⟨C, fun y hy => hC y (hst hy)⟩
  · exact ⟨min C D, fun y hy => hy.elim (fun h => (min_le_left _ _).trans (hC y h))
      fun h => (min_le_right _ _).trans (hD y h)⟩
  · obtain ⟨V, hV, C, hC⟩ := hbdd x
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, C, hC⟩

/-- **HNVW I, Lemma 4.5.2** (p. 330), on the line: a midpoint concave function on `ℝ` that is
locally bounded below is concave. As in the book, reparametrise a segment on which concavity fails
by `[0, 1]`, where the function is bounded below by compactness, and subtract the affine function
with the same values at the end points, so that `u (0) = u (1) = 0` and `u (λ) < 0`; the dyadic
values are nonnegative (`zzg_dyadic_nonneg`), and the doubling argument
(`zzg_nonneg_of_midpoint`) contradicts the boundedness below. (The book's function is defined on a
Banach space; see `concaveOn_iff_midpoint`.) -/
theorem concaveOn_of_midpoint {f : ℝ → ℝ} (hmid : ∀ a b, (f a + f b) / 2 ≤ f ((a + b) / 2))
    (hbdd : ∀ x, ∃ U ∈ nhds x, ∃ C : ℝ, ∀ y ∈ U, C ≤ f y) : ConcaveOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  obtain rfl : s = 1 - t := by linarith
  simp only [smul_eq_mul]
  rcases ht.eq_or_lt with rfl | ht0
  · simp
  rcases hs.eq_or_lt with hs0 | hs0
  · obtain rfl : t = 1 := by linarith
    simp
  -- the reparametrised function minus the affine one
  set u : ℝ → ℝ := fun r => f ((1 - r) * a + r * b) - ((1 - r) * f a + r * f b) with hu
  have hu_mid : ∀ r r', (u r + u r') / 2 ≤ u ((r + r') / 2) := by
    intro r r'
    have h := hmid ((1 - r) * a + r * b) ((1 - r') * a + r' * b)
    rw [show ((1 - r) * a + r * b + ((1 - r') * a + r' * b)) / 2 =
      (1 - (r + r') / 2) * a + (r + r') / 2 * b by ring] at h
    simp only [hu]
    linarith
  obtain ⟨C, hC⟩ := zzg_bddBelow_of_isCompact hbdd
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image
      (f := fun r : ℝ => (1 - r) * a + r * b) (by fun_prop))
  have hu_bdd : ∀ r, 0 ≤ r → r ≤ 1 → C - (|f a| + |f b|) ≤ u r := by
    intro r hr0 hr1
    have h1 := hC _ ⟨r, ⟨hr0, hr1⟩, rfl⟩
    have h2 : (1 - r) * f a ≤ |f a| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)).trans
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith))
    have h3 : r * f b ≤ |f b| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) hr0).trans
        (mul_le_of_le_one_left (abs_nonneg _) hr1)
    simp only [hu]
    linarith
  have key := zzg_nonneg_of_midpoint hu_mid (by simp [hu]) (by simp [hu]) hu_bdd ht0 (by linarith)
  simp only [hu] at key
  linarith

/-- **HNVW I, Lemma 4.5.2** (p. 330): a function on a (topological vector) space that is locally
bounded below is concave if and only if it is midpoint concave (`concaveOn_of_midpoint` on each
line, the passage to a segment with which the book's proof begins). -/
theorem concaveOn_iff_midpoint {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] {u : E → ℝ}
    (hbdd : ∀ x, ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ V, C ≤ u y) :
    ConcaveOn ℝ Set.univ u ↔ ∀ x y, (u x + u y) / 2 ≤ u ((1 / 2 : ℝ) • (x + y)) := by
  constructor
  · intro h x y
    have := h.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [smul_add]
    simp only [smul_eq_mul] at this
    linarith
  · intro hmid
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    have hφmid : ∀ s t : ℝ, (u (z₁ + s • (z₂ - z₁)) + u (z₁ + t • (z₂ - z₁))) / 2 ≤
        u (z₁ + ((s + t) / 2) • (z₂ - z₁)) := by
      intro s t
      have h := hmid (z₁ + s • (z₂ - z₁)) (z₁ + t • (z₂ - z₁))
      rwa [show (1 / 2 : ℝ) • (z₁ + s • (z₂ - z₁) + (z₁ + t • (z₂ - z₁))) =
        z₁ + ((s + t) / 2) • (z₂ - z₁) by module] at h
    have hφbdd : ∀ t : ℝ, ∃ V ∈ 𝓝 t, ∃ C : ℝ, ∀ s ∈ V, C ≤ u (z₁ + s • (z₂ - z₁)) := by
      intro t
      obtain ⟨V, hV, C, hC⟩ := hbdd (z₁ + t • (z₂ - z₁))
      have hc : Continuous fun s : ℝ => z₁ + s • (z₂ - z₁) := by fun_prop
      exact ⟨_, hc.continuousAt.preimage_mem_nhds hV, C, fun s hs => hC _ hs⟩
    have := (concaveOn_of_midpoint hφmid hφbdd).2 (Set.mem_univ 0) (Set.mem_univ 1) ha hb hab
    obtain rfl : a = 1 - b := by linarith
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul] at this
    rwa [show z₁ + (z₂ - z₁) = z₂ by abel,
      show z₁ + b • (z₂ - z₁) = (1 - b) • z₁ + b • z₂ by module] at this

end Midpoint

section Jensen

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  {u : X → X → ℝ}

/-- **HNVW I, Lemma 4.5.4** (p. 331), the direct half: Jensen's inequality
`E u (x + ξ, y + ε ξ) ≤ u (x, y)` for a zig-zag concave `u`, a simple random variable `ξ` with
`E ξ = 0` (values `ξ_i` with probabilities `w_i`) and a sign `ε`; no continuity of `u` is
assumed. -/
theorem IsSignZigZagConcave.sum_le (hu : IsSignZigZagConcave 𝕜 u) {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) {ξ : ι → X}
    (hξ : ∑ i ∈ s, w i • ξ i = 0) (x y : X) {ε : 𝕜} (hε : ‖ε‖ = 1) :
    ∑ i ∈ s, w i * u (x + ξ i) (y + ε • ξ i) ≤ u x y := by
  have h := (hu x y ε hε).le_map_sum (p := ξ) hw hw1 fun i _ => Set.mem_univ _
  simpa only [hξ, smul_zero, add_zero, smul_eq_mul] using h

/-- **HNVW I, Lemma 4.5.4** (p. 331): `u` is zig-zag concave if and only if
`E u (x + ξ, y + ε ξ) ≤ u (x, y)` for all simple random variables `ξ` with `E ξ = 0` (values `ξ_i`
with probabilities `w_i`), all `x`, `y` and all signs `ε`. For the converse take `ξ` with the
values `z₁ − z`, `z₂ − z` with probabilities `a`, `b`, `z = a z₁ + b z₂`. -/
theorem isSignZigZagConcave_iff : IsSignZigZagConcave 𝕜 u ↔
    ∀ (n : ℕ) (w : Fin n → ℝ) (ξ : Fin n → X), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      ∑ i, w i • ξ i = 0 → ∀ (x y : X) (ε : 𝕜), ‖ε‖ = 1 →
        ∑ i, w i * u (x + ξ i) (y + ε • ξ i) ≤ u x y := by
  refine ⟨fun hu n w ξ hw hw1 hξ x y ε hε => hu.sum_le (fun i _ => hw i) hw1 hξ x y hε,
    fun h x y ε hε => ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩⟩
  set z : X := a • z₁ + b • z₂ with hz
  have hξ : a • (z₁ - z) + b • (z₂ - z) = 0 := by
    obtain rfl : a = 1 - b := by linarith
    rw [hz]
    module
  have key := h 2 ![a, b] ![z₁ - z, z₂ - z] (by simp [Fin.forall_fin_two, ha, hb])
    (by simpa using hab) (by simpa using hξ) (x + z) (y + ε • z) ε hε
  have e : ∀ z', x + z + (z' - z) = x + z' := fun z' => by abel
  have e' : ∀ z', y + ε • z + ε • (z' - z) = y + ε • z' := fun z' => by rw [smul_sub]; abel
  simpa [e, e'] using key

/-- The computation of **HNVW I, Lemma 4.5.5** (p. 331–332), on a finite set with weights `w`
partitioned by the map `c` (whose classes are the atoms of `ℱ_{n−1}`): if `f`, `g` and the signs
`φ` are constant on the classes, the increment `f' − f` has mean zero on each class and
`g' = g + φ (f' − f)`, then `Σ w u (f', g') ≤ Σ w u (f, g)`: on each class apply Lemma 4.5.4 with
the normalised weights (a class of weight `0` contributes `0`). -/
private theorem zzg_sum_step (hu : IsSignZigZagConcave 𝕜 u) {Ω ι : Type*} [Fintype Ω]
    [DecidableEq ι] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (c : Ω → ι) {f f' g g' : Ω → X} {φ : Ω → 𝕜}
    (hφ1 : ∀ ω, ‖φ ω‖ = 1) (hf : ∀ ω ω', c ω = c ω' → f ω = f ω')
    (hg : ∀ ω ω', c ω = c ω' → g ω = g ω') (hφ : ∀ ω ω', c ω = c ω' → φ ω = φ ω')
    (hmean : ∀ ω₀, ∑ ω with c ω = c ω₀, w ω • (f' ω - f ω) = 0)
    (hg' : ∀ ω, g' ω = g ω + φ ω • (f' ω - f ω)) :
    ∑ ω, w ω * u (f' ω) (g' ω) ≤ ∑ ω, w ω * u (f ω) (g ω) := by
  have hmaps : ∀ ω ∈ (Finset.univ : Finset Ω), c ω ∈ Finset.univ.image c := fun ω _ =>
    Finset.mem_image_of_mem c (Finset.mem_univ ω)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨ω₀, -, rfl⟩ := Finset.mem_image.mp hi
  have hB : ∀ ω ∈ Finset.univ.filter (fun ω => c ω = c ω₀), c ω = c ω₀ := fun ω hω =>
    (Finset.mem_filter.mp hω).2
  -- on the class of `ω₀`, `f`, `g` and `φ` are constant
  have e1 : ∀ ω ∈ Finset.univ.filter (fun ω => c ω = c ω₀), w ω * u (f' ω) (g' ω) =
      w ω * u (f ω₀ + (f' ω - f ω)) (g ω₀ + φ ω₀ • (f' ω - f ω)) := fun ω hω => by
    rw [← hφ ω ω₀ (hB ω hω), ← hf ω ω₀ (hB ω hω), ← hg ω ω₀ (hB ω hω), hg', add_sub_cancel]
  have e2 : ∀ ω ∈ Finset.univ.filter (fun ω => c ω = c ω₀), w ω * u (f ω) (g ω) =
      w ω * u (f ω₀) (g ω₀) := fun ω hω => by
    rw [hf ω ω₀ (hB ω hω), hg ω ω₀ (hB ω hω)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul]
  set B := Finset.univ.filter (fun ω => c ω = c ω₀)
  have hW0 : 0 ≤ ∑ ω ∈ B, w ω := Finset.sum_nonneg fun ω _ => hw ω
  rcases hW0.eq_or_lt with hW | hW
  · -- a class of weight `0`
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hw ω).mp hW.symm
    rw [← hW, zero_mul]
    exact (Finset.sum_eq_zero fun ω hω => by rw [h0 ω hω, zero_mul]).le
  · -- Lemma 4.5.4 with the normalised weights
    have key := hu.sum_le (s := B) (w := fun ω => w ω / ∑ ω ∈ B, w ω)
      (ξ := fun ω => f' ω - f ω) (fun ω _ => div_nonneg (hw ω) hW0)
      (by rw [← Finset.sum_div, div_self hW.ne']) (by
        simp only [div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
        rw [hmean ω₀, smul_zero]) (f ω₀) (g ω₀) (hφ1 ω₀)
    simp only [div_mul_eq_mul_div, ← Finset.sum_div] at key
    rwa [div_le_iff₀ hW, mul_comm (u _ _)] at key

variable [CompleteSpace X]

/-- **HNVW I, Lemma 4.5.5** (p. 331–332): `E u (f_{n+1}, g_{n+1}) ≤ E u (f_n, g_n)` for a zig-zag
concave `u`, a martingale `f` and its transform `g` by signs `φ`, by summing over the atoms of
`ℱ_n` and applying Lemma 4.5.4 on each, with the normalised measure. Departures from the source:
the signs may be predictable (`φ_{n+1}` is `ℱ_n`-measurable) instead of deterministic, the argument
being the same, since they are constant on the atoms of `ℱ_n`; the measure space is a finite
probability space, so that every σ-algebra is finite and the integrals make sense without
`u (0, 0) = 0`. -/
theorem IsSignZigZagConcave.integral_le (hu : IsSignZigZagConcave 𝕜 u) {Ω : Type*} [Finite Ω]
    {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {f g : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} (hf : Martingale f ℱ μ)
    (hg : ∀ n, StronglyMeasurable[ℱ n] (g n)) (hφ1 : ∀ n ω, ‖φ n ω‖ = 1)
    (hφ : ∀ n, StronglyMeasurable[ℱ n] (φ (n + 1)))
    (hgf : ∀ n ω, g (n + 1) ω = g n ω + φ (n + 1) ω • (f (n + 1) ω - f n ω)) (n : ℕ) :
    ∫ ω, u (f (n + 1) ω) (g (n + 1) ω) ∂μ ≤ ∫ ω, u (f n ω) (g n ω) ∂μ := by
  classical
  have := Fintype.ofFinite Ω
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
  have hmem : ∀ ω ω', atom (ℱ n) ω = atom (ℱ n) ω' → ω ∈ atom (ℱ n) ω' := fun ω ω' h =>
    h ▸ mem_atom_self _ ω
  refine zzg_sum_step hu (fun ω => measureReal_nonneg) (atom (ℱ n)) (hφ1 (n + 1))
    (fun ω ω' h => fpa_eq_of_mem_atom (hf.stronglyAdapted n) (hmem ω ω' h))
    (fun ω ω' h => fpa_eq_of_mem_atom (hg n) (hmem ω ω' h))
    (fun ω ω' h => fpa_eq_of_mem_atom (hφ n) (hmem ω ω' h)) (fun ω₀ => ?_) (hgf n)
  -- the increment has mean zero on the atom of `ω₀`
  have hA := measurableSet_atom (ℱ n) ω₀
  have hint := hf.setIntegral_eq n.le_succ hA
  rw [← integral_indicator (ℱ.le n _ hA), ← integral_indicator (ℱ.le n _ hA),
    integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite] at hint
  rw [Finset.sum_filter]
  have e : ∀ ω, (if atom (ℱ n) ω = atom (ℱ n) ω₀ then μ.real {ω} • (f (n + 1) ω - f n ω) else 0) =
      μ.real {ω} • (atom (ℱ n) ω₀).indicator (f (n + 1)) ω -
        μ.real {ω} • (atom (ℱ n) ω₀).indicator (f n) ω := by
    intro ω
    by_cases h : ω ∈ atom (ℱ n) ω₀
    · rw [ite_eq_left (fpa_atom_eq_of_mem h), Set.indicator_of_mem h, Set.indicator_of_mem h,
        smul_sub]
    · rw [ite_eq_right fun h' => h (hmem ω ω₀ h'), Set.indicator_of_notMem h,
        Set.indicator_of_notMem h, smul_zero, sub_zero]
  rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_sub_distrib, hint, sub_self]

/-- The iteration of Lemma 4.5.5 in the proof of HNVW I, Theorem 4.5.6, (3)⇒(1) (p. 333–334),
`E u (f_n, g_n) ≤ … ≤ E u (f_0, g_0) = u (0, 0)`, for a martingale `f` started at `0` and its
transform by predictable signs. -/
theorem IsSignZigZagConcave.integral_transform_le [IsScalarTower ℝ 𝕜 X]
    (hu : IsSignZigZagConcave 𝕜 u) {Ω : Type*} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} (hf : Martingale f ℱ μ) (hf0 : ∀ ω, f 0 ω = 0)
    (hφ1 : ∀ n ω, ‖φ n ω‖ = 1) (hφ : ∀ n, StronglyMeasurable[ℱ n] (φ (n + 1))) (n : ℕ) :
    ∫ ω, u (f n ω) (martingaleTransform φ f n ω) ∂μ ≤ u 0 0 := by
  induction n with
  | zero => simp [martingaleTransform, hf0]
  | succ n ih =>
    have hg := martingale_martingaleTransform hf hφ fun k => ⟨1, fun ω => (hφ1 (k + 1) ω).le⟩
    refine (hu.integral_le hf (fun n => hg.stronglyAdapted n) hφ1 hφ (fun n ω => ?_) n).trans ih
    simp only [martingaleTransform, Finset.sum_range_succ]

end Jensen

section Homogenize

variable (𝕜 : Type*) {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The homogenisation of `u` (HNVW I, p. 332–333):
`ũ (x, y) = inf_{α ≠ 0} |α|^{−p} u (α x, α y)`. -/
noncomputable def zigZagHomogenize (p : ℝ) (u : X → X → ℝ) (x y : X) : ℝ :=
  ⨅ α : {α : 𝕜 // α ≠ 0}, ‖(α : 𝕜)‖ ^ (-p) * u ((α : 𝕜) • x) ((α : 𝕜) • y)

variable {𝕜} {p β : ℝ} {u : X → X → ℝ}

/-- `u_α (x, y) = |α|^{−p} u (α x, α y)` satisfies (4.30) if `u` does. -/
private theorem zzg_le_smul (hF : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) (x y : X)
    (α : {α : 𝕜 // α ≠ 0}) : ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤
      ‖(α : 𝕜)‖ ^ (-p) * u ((α : 𝕜) • x) ((α : 𝕜) • y) := by
  have hα : 0 < ‖(α : 𝕜)‖ := norm_pos_iff.mpr α.2
  have h := mul_le_mul_of_nonneg_left (hF ((α : 𝕜) • x) ((α : 𝕜) • y))
    (Real.rpow_nonneg hα.le (-p))
  refine le_trans (le_of_eq ?_) h
  rw [norm_smul, norm_smul, Real.mul_rpow hα.le (norm_nonneg _),
    Real.mul_rpow hα.le (norm_nonneg _), Real.rpow_neg hα.le]
  have : ‖(α : 𝕜)‖ ^ p ≠ 0 := (Real.rpow_pos_of_pos hα p).ne'
  field_simp

private theorem zzg_bddBelow_smul (hF : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) (x y : X) :
    BddBelow (Set.range fun α : {α : 𝕜 // α ≠ 0} =>
      ‖(α : 𝕜)‖ ^ (-p) * u ((α : 𝕜) • x) ((α : 𝕜) • y)) :=
  ⟨_, Set.forall_mem_range.mpr fun α => zzg_le_smul hF x y α⟩

private theorem zzg_nonempty_ne_zero : Nonempty {α : 𝕜 // α ≠ 0} :=
  ⟨⟨1, one_ne_zero⟩⟩

/-- The homogenisation satisfies (4.30) if `u` does (HNVW I, p. 333). -/
theorem le_zigZagHomogenize (hF : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) (x y : X) :
    ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ zigZagHomogenize 𝕜 p u x y :=
  have := zzg_nonempty_ne_zero (𝕜 := 𝕜)
  le_ciInf fun α => zzg_le_smul hF x y α

/-- The homogenisation of a zig-zag concave function with (4.30) is zig-zag concave (HNVW I,
p. 333): it is the pointwise infimum, which is real-valued by (4.30), of the zig-zag concave
functions `u_α`. -/
theorem IsSignZigZagConcave.zigZagHomogenize [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    (hu : IsSignZigZagConcave 𝕜 u) (hF : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y) :
    IsSignZigZagConcave 𝕜 (zigZagHomogenize 𝕜 p u) := by
  have := zzg_nonempty_ne_zero (𝕜 := 𝕜)
  intro x y ε hε
  refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => le_ciInf fun α => ?_⟩
  -- `u_α` is zig-zag concave
  have h := (hu ((α : 𝕜) • x) ((α : 𝕜) • y) ε hε).2 (Set.mem_univ ((α : 𝕜) • z₁))
    (Set.mem_univ ((α : 𝕜) • z₂)) ha hb hab
  have e1 : ∀ z : X, (α : 𝕜) • (x + z) = (α : 𝕜) • x + (α : 𝕜) • z := fun z => smul_add _ _ _
  have e2 : ∀ z : X, (α : 𝕜) • (y + ε • z) = (α : 𝕜) • y + ε • (α : 𝕜) • z := fun z => by
    rw [smul_add, smul_comm]
  have e3 : (α : 𝕜) • (a • z₁ + b • z₂) = a • (α : 𝕜) • z₁ + b • (α : 𝕜) • z₂ := by
    rw [smul_add, smul_comm, smul_comm (α : 𝕜) b]
  have h0 : 0 ≤ ‖(α : 𝕜)‖ ^ (-p) := Real.rpow_nonneg (norm_nonneg _) _
  have h1 := mul_le_mul_of_nonneg_left (ciInf_le (zzg_bddBelow_smul hF (x + z₁) (y + ε • z₁)) α) ha
  have h2 := mul_le_mul_of_nonneg_left (ciInf_le (zzg_bddBelow_smul hF (x + z₂) (y + ε • z₂)) α) hb
  simp only [smul_eq_mul] at h ⊢
  rw [e1, e2, e3]
  rw [e1, e2] at h1 h2
  refine (add_le_add h1 h2).trans ((le_of_eq ?_).trans (mul_le_mul_of_nonneg_left h h0))
  ring

/-- **(4.31)** (HNVW I, p. 332–333) for `α ≠ 0`: `ũ (α x, α y) = |α|^p ũ (x, y)`, by a change of
variable in the infimum. -/
private theorem zzg_homogenize_smul (u : X → X → ℝ) {α : 𝕜} (hα : α ≠ 0) (x y : X) :
    zigZagHomogenize 𝕜 p u (α • x) (α • y) = ‖α‖ ^ p * zigZagHomogenize 𝕜 p u x y := by
  have hα' : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hsurj : Function.Surjective
      (fun δ : {δ : 𝕜 // δ ≠ 0} => (⟨δ * α, mul_ne_zero δ.2 hα⟩ : {δ : 𝕜 // δ ≠ 0})) := fun γ =>
    ⟨⟨γ * α⁻¹, mul_ne_zero γ.2 (inv_ne_zero hα)⟩, by ext; simp [hα]⟩
  rw [zigZagHomogenize, zigZagHomogenize, Real.mul_iInf_of_nonneg (by positivity)]
  refine hsurj.iInf_congr _ fun δ => ?_
  simp only [norm_mul, mul_smul]
  rw [Real.mul_rpow (norm_nonneg _) hα'.le, Real.rpow_neg hα'.le, ← mul_assoc,
    mul_comm (‖(δ : 𝕜)‖ ^ (-p)), ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hα' p).ne',
    one_mul]

/-- The homogenisation vanishes at the origin (HNVW I, p. 333):
`ũ (0, 0) = ũ (α 0, α 0) = |α|^p ũ (0, 0) → 0` as `α → 0`. -/
theorem zigZagHomogenize_zero (hp : 0 < p) (u : X → X → ℝ) : zigZagHomogenize 𝕜 p u 0 0 = 0 := by
  have hlim : Filter.Tendsto (fun t : ℝ => t ^ p * zigZagHomogenize 𝕜 p u 0 0) (𝓝[>] 0)
      (𝓝 (0 ^ p * zigZagHomogenize 𝕜 p u 0 0)) :=
    ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left
      nhdsWithin_le_nhds).mul_const _
  rw [Real.zero_rpow hp.ne', zero_mul] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Set.mem_Ioi] at ht
  have h := zzg_homogenize_smul (p := p) u (α := (t : 𝕜)) (by exact_mod_cast ht.ne') 0 0
  rwa [smul_zero, RCLike.norm_ofReal, abs_of_pos ht] at h

/-- **(4.31)** (HNVW I, p. 332–333): `ũ (α x, α y) = |α|^p ũ (x, y)` for all scalars `α`. -/
theorem zigZagHomogenize_smul (hp : 0 < p) (u : X → X → ℝ) (α : 𝕜) (x y : X) :
    zigZagHomogenize 𝕜 p u (α • x) (α • y) = ‖α‖ ^ p * zigZagHomogenize 𝕜 p u x y := by
  by_cases hα : α = 0
  · rw [hα, zero_smul, zero_smul, zigZagHomogenize_zero hp, norm_zero, Real.zero_rpow hp.ne',
      zero_mul]
  · exact zzg_homogenize_smul u hα x y

end Homogenize

end BanachProbability
