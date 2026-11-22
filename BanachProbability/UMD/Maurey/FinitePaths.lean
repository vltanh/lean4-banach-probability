module

public import BanachProbability.UMD.Maurey.FiniteModel

/-!
# Martingales on finite probability spaces

Finite models (`FiniteModel.lean`) with dyadic transition probabilities. This file defines

* `HasDyadicTransitions μ ℱ n`: the transition probabilities of the filtration `ℱ` up to time `n`
  (the masses of the atoms of `ℱ_0`, and the conditional masses of the atoms of `ℱ_{k+1}` inside
  those of `ℱ_k`) are dyadic rationals with a common denominator,

and proves the perturbation step of Maurey's theorem (Pisier, *Martingales in Banach spaces*
(2016), §5.6; lecture notes (2011), Lemma 8.30's approximation, Lemma 8.31's path-law estimate and
Remark 2.18; HNVW I, Theorem 4.2.5):

* the transition probabilities of a finite model are moved to dyadic rationals `j / 2^m` with the
  same sums and the same support (for `m` large; zeros stay zeros for every `m`): on each atom
  `A`, the conditional masses `μ {y} / μ (A)` are rounded down to multiples of `2^{-m}` but one,
  which takes the remainder and has positive mass (`fpa_exists_round`), and the transition from
  `A` to an atom `A' ⊆ A` of the next σ-algebra
  gets the sum over `A'` of the rounded masses; the new laws `μ'_m` live on the same finite space,
  and `μ'_m {ω} → μ {ω}` for every `ω` (`fpa_exists_dyadic_laws`);
* the martingale is corrected under the new law as in Remark 2.18,
  `Y'_k = Y_k − Σ_{j<k} E' [Y_{j+1} − Y_j | ℱ_j]`, a `μ'_m`-martingale started at `0`; by the atom
  averages, the corrections tend to `E [Y_{j+1} − Y_j | ℱ_j] = 0` on the support of `μ`;

so that both sides of the UMD inequality move by at most a prescribed `η` for `m` large
(`exists_hasDyadicTransitions_approx`, and `exists_hasDyadicTransitions_approx_gen` for
multipliers in an `RCLike` field; continuity in finitely many variables).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BanachProbability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The transition probabilities of `ℱ` up to time `n` are dyadic rationals with the common
denominator `2^m`: every atom of `ℱ_0` has mass `j / 2^m`, and every atom of `ℱ_{k+1}`, `k < n`,
has mass `j / 2^m` times that of the atom of `ℱ_k` containing it. -/
def HasDyadicTransitions {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (n : ℕ) : Prop :=
  ∃ m : ℕ, (∀ ω, ∃ j : ℕ, μ.real (atom (ℱ 0) ω) = j / 2 ^ m) ∧
    ∀ k < n, ∀ ω, ∃ j : ℕ, μ.real (atom (ℱ (k + 1)) ω) = j / 2 ^ m * μ.real (atom (ℱ k) ω)

/-! ### Sums over the atoms of a finite space -/

/-- Pulling out of a sum over a set `S` a factor that is constant on `S`. -/
private theorem fpa_sum_indicator_const_mul {Ω : Type*} [Fintype Ω] (S : Set Ω) {c g : Ω → ℝ}
    {c₀ : ℝ} (hc : ∀ z ∈ S, c z = c₀) :
    ∑ z, S.indicator (fun z => c z * g z) z = c₀ * ∑ z, S.indicator g z := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ∈ S
  · simp [Set.indicator_of_mem hz, hc z hz]
  · simp [Set.indicator_of_notMem hz]

private theorem fpa_sum_indicator_nonneg {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ x, 0 ≤ w x) (S : Set Ω) : 0 ≤ ∑ z, S.indicator w z :=
  Finset.sum_nonneg fun z _ => Set.indicator_nonneg (fun z _ => hw z) z

/-- A point of a set carries at most the total weight of the set. -/
private theorem fpa_le_sum_indicator {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    {S : Set Ω} {x : Ω} (hx : x ∈ S) : w x ≤ ∑ z, S.indicator w z := by
  have := Finset.single_le_sum (f := fun z => S.indicator w z)
    (fun z _ => Set.indicator_nonneg (fun z _ => hw z) z) (Finset.mem_univ x)
  simpa [Set.indicator_of_mem hx] using this

private theorem fpa_sum_indicator_mono {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    {S T : Set Ω} (h : S ⊆ T) : ∑ z, S.indicator w z ≤ ∑ z, T.indicator w z :=
  Finset.sum_le_sum fun z _ => Set.indicator_le_indicator_of_subset h (fun z => hw z) z

/-- Splitting a point `z₀ ∈ S` off a sum over `S`. -/
private theorem fpa_sum_indicator_split {Ω : Type*} [Fintype Ω] {S : Set Ω} {z₀ : Ω}
    (hz₀ : z₀ ∈ S) (f : Ω → ℝ) :
    ∑ z, S.indicator f z = f z₀ + ∑ z, (S \ {z₀}).indicator f z := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z₀), Set.indicator_of_mem hz₀,
    ← Finset.sum_erase Finset.univ (f := fun z => (S \ {z₀}).indicator f z) (a := z₀)
      (by simp)]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  have hne : z ≠ z₀ := Finset.ne_of_mem_erase hz
  by_cases h : z ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_sdiff_of_mem h hne)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem fun h' : z ∈ S \ {z₀} => h h'.1]

/-- Averaging over atoms: for a set `s` that is a union of `m`-atoms,
`Σ_{z ∈ s} F z = Σ_{x ∈ s} (#A(x))⁻¹ Σ_{y ∈ A(x)} F y`, `A(x)` the atom of `x`. -/
private theorem fpa_sum_eq_sum_avg {Ω : Type*} [Fintype Ω] (m : MeasurableSpace Ω) {s : Set Ω}
    (hs : ∀ x ∈ s, ∀ y ∈ atom m x, y ∈ s) (F : Ω → ℝ) :
    ∑ z, s.indicator F z =
      ∑ x, s.indicator (fun x => (∑ y, (atom m x).indicator (fun _ => (1 : ℝ)) y)⁻¹ *
        ∑ y, (atom m x).indicator F y) x := by
  obtain ⟨c, hc⟩ : ∃ c : Ω → ℝ, c = fun x => ∑ y, (atom m x).indicator (fun _ => (1 : ℝ)) y :=
    ⟨_, rfl⟩
  have hcx : ∀ x, c x = ∑ y, (atom m x).indicator (fun _ => (1 : ℝ)) y := fun x => by rw [hc]
  simp only [← hcx]
  have hcpos : ∀ x, 0 < c x := fun x => by
    have h1 : (1 : ℝ) ≤ c x := by
      rw [hcx]
      exact fpa_le_sum_indicator (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (mem_atom_self m x)
    linarith
  have hceq : ∀ x y, y ∈ atom m x → c y = c x := fun x y hy => by
    rw [hcx, hcx, fpa_atom_eq_of_mem hy]
  have hswap : ∀ x, s.indicator (fun x => (c x)⁻¹ * ∑ y, (atom m x).indicator F y) x =
      ∑ y, s.indicator (fun x => (c x)⁻¹ * (atom m x).indicator F y) x := by
    intro x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Finset.mul_sum]
    · simp only [Set.indicator_of_notMem hx, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun x _ => hswap x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hterm : ∀ x, s.indicator (fun x => (c x)⁻¹ * (atom m x).indicator F z) x =
      (atom m z).indicator (fun _ => (c z)⁻¹ * s.indicator F z) x := by
    intro x
    by_cases hxz : x ∈ atom m z
    · have hzx : z ∈ atom m x := fpa_mem_atom_comm.1 hxz
      rw [Set.indicator_of_mem hxz]
      by_cases hz : z ∈ s
      · simp only [Set.indicator_of_mem (hs z hz x hxz), Set.indicator_of_mem hzx,
          Set.indicator_of_mem hz, hceq z x hxz]
      · have hx : x ∉ s := fun hx => hz (hs x hx z hzx)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz, mul_zero]
    · have hzx : z ∉ atom m x := fun h => hxz (fpa_mem_atom_comm.1 h)
      rw [Set.indicator_of_notMem hxz]
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem hzx, mul_zero]
      · rw [Set.indicator_of_notMem hx]
  have hconst : ∑ x, (atom m z).indicator (fun _ => (c z)⁻¹ * s.indicator F z) x =
      c z * ((c z)⁻¹ * s.indicator F z) := by
    rw [hcx z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ atom m z
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [Finset.sum_congr rfl fun x _ => hterm x, hconst, mul_inv_cancel_left₀ (hcpos z).ne']

/-- Regrouping a sum over a union `s` of `m`-atoms: if `g` and `h` have the same sum over every
atom in `s`, they have the same sum over `s`. -/
private theorem fpa_sum_regroup {Ω : Type*} [Fintype Ω] (m : MeasurableSpace Ω) {s : Set Ω}
    (hs : ∀ x ∈ s, ∀ y ∈ atom m x, y ∈ s) {g h : Ω → ℝ}
    (hgh : ∀ y ∈ s, ∑ z, (atom m y).indicator g z = ∑ z, (atom m y).indicator h z) :
    ∑ z, s.indicator g z = ∑ z, s.indicator h z := by
  rw [fpa_sum_eq_sum_avg m hs g, fpa_sum_eq_sum_avg m hs h]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, hgh x hx]
  · simp only [Set.indicator_of_notMem hx]

/-! ### Dyadic transition probabilities -/

/-- **Dyadic rounding** of a probability vector `w` on a finite set `S` (the approximation in
Lemma 8.30): weights `j / 2^k` of total `1` on `S`, vanishing where `w` vanishes, converging to
`w` on `S` as `k → ∞`. All the weights but one are rounded down to a multiple of `2^{-k}`; the
remainder goes to a point of positive weight. -/
private theorem fpa_exists_round {Ω : Type*} [Fintype Ω] (S : Set Ω) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    ∃ δ : ℕ → Ω → ℝ, (∀ k z, 0 ≤ δ k z) ∧ (∀ k z, ∃ j : ℕ, δ k z = j / 2 ^ k) ∧
      (∀ k z, w z = 0 → δ k z = 0) ∧
      (∑ z, S.indicator w z = 1 → (∀ k, ∑ z, S.indicator (δ k) z = 1) ∧
        ∀ z ∈ S, Tendsto (fun k => δ k z) atTop (𝓝 (w z))) := by
  classical
  by_cases hS : ∑ z, S.indicator w z = 1
  swap
  · exact ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ => ⟨0, by simp⟩, fun _ _ _ => rfl,
      fun h => absurd h hS⟩
  -- a point of positive weight, which receives the rounding error
  obtain ⟨z₀, hz₀S, hz₀⟩ : ∃ z₀ ∈ S, w z₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ z, S.indicator w z = 0 := Finset.sum_eq_zero fun z _ => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, hcon z hz]
      · rw [Set.indicator_of_notMem hz]
    rw [hS] at h0
    exact one_ne_zero h0
  -- rounding down to a multiple of `2^{-k}`
  obtain ⟨rd, hrd⟩ : ∃ rd : ℕ → ℝ → ℝ, rd = fun k t => (⌊2 ^ k * t⌋₊ : ℝ) / 2 ^ k := ⟨_, rfl⟩
  have hrd_le : ∀ k t, 0 ≤ t → rd k t ≤ t := fun k t ht => by
    rw [hrd, div_le_iff₀ (by positivity), mul_comm]
    exact Nat.floor_le (by positivity)
  have hrd_nn : ∀ k t, 0 ≤ rd k t := fun k t => by rw [hrd]; positivity
  have hrd_ge : ∀ k t, t - (1 / 2) ^ k ≤ rd k t := fun k t => by
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have h := Nat.lt_floor_add_one (2 ^ k * t)
    rw [hrd, le_div_iff₀ h2, sub_mul, one_div_pow, one_div_mul_cancel h2.ne']
    nlinarith
  have hrd_lim : ∀ t, 0 ≤ t → Tendsto (fun k => rd k t) atTop (𝓝 t) := fun t ht => by
    have h0 : Tendsto (fun k : ℕ => t - (1 / 2 : ℝ) ^ k) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds (fun k => hrd_ge k t)
      (fun k => hrd_le k t ht)
  have hrd0 : ∀ k, rd k 0 = 0 := fun k => by simp [hrd]
  -- the rounded weights off `z₀`, and their total
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun k => ∑ z, (S \ {z₀}).indicator (fun z => rd k (w z)) z :=
    ⟨_, rfl⟩
  have hT_le : ∀ k, T k ≤ 1 := fun k => by
    calc T k ≤ ∑ z, (S \ {z₀}).indicator w z := by
          rw [hT]
          refine Finset.sum_le_sum fun z _ => ?_
          by_cases hz : z ∈ S \ {z₀}
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
            exact hrd_le k _ (hw z)
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      _ ≤ ∑ z, S.indicator w z := fpa_sum_indicator_mono hw Set.sdiff_subset
      _ = 1 := hS
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → Ω → ℝ, δ = fun k z => if z = z₀ then 1 - T k else rd k (w z) :=
    ⟨_, rfl⟩
  have hδoff : ∀ k z, z ≠ z₀ → δ k z = rd k (w z) := fun k z hz => by rw [hδ]; simp [hz]
  have hδon : ∀ k, δ k z₀ = 1 - T k := fun k => by rw [hδ]; simp
  have hδT : ∀ k, ∑ z, (S \ {z₀}).indicator (δ k) z = T k := fun k => by
    rw [hT]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ S \ {z₀}
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hδoff k z hz.2]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  refine ⟨δ, fun k z => ?_, fun k z => ?_, fun k z hz => ?_, fun _ => ⟨fun k => ?_, fun z hz => ?_⟩⟩
  · by_cases hz : z = z₀
    · rw [hz, hδon]
      linarith [hT_le k]
    · rw [hδoff k z hz]
      exact hrd_nn k _
  · by_cases hz : z = z₀
    · -- the remainder `1 - T k` is dyadic, as `T k` is
      obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ∑ z, if z ∈ S \ {z₀} then ⌊2 ^ k * w z⌋₊ else 0 := ⟨_, rfl⟩
      have hTJ : T k = J / 2 ^ k := by
        rw [hT, hJ]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hz : z ∈ S \ {z₀}
        · rw [Set.indicator_of_mem hz, ite_eq_left hz, hrd]
        · rw [Set.indicator_of_notMem hz, ite_eq_right hz, zero_div]
      have hJle : J ≤ 2 ^ k := by
        have h := hT_le k
        rw [hTJ, div_le_one (by positivity)] at h
        exact_mod_cast h
      refine ⟨2 ^ k - J, ?_⟩
      rw [hz, hδon, hTJ, Nat.cast_sub hJle]
      push_cast
      field_simp
    · exact ⟨⌊2 ^ k * w z⌋₊, by rw [hδoff k z hz, hrd]⟩
  · have hne : z ≠ z₀ := fun h => hz₀ (h ▸ hz)
    rw [hδoff k z hne, hz, hrd0]
  · rw [fpa_sum_indicator_split hz₀S, hδT, hδon]
    ring
  · by_cases hzz : z = z₀
    · -- the remainder converges to `1 - Σ_{S \ {z₀}} w = w z₀`
      have hlim : Tendsto T atTop (𝓝 (∑ z, (S \ {z₀}).indicator w z)) := by
        rw [hT]
        refine tendsto_finsetSum _ fun z _ => ?_
        by_cases h : z ∈ S \ {z₀}
        · simp only [Set.indicator_of_mem h]
          exact hrd_lim _ (hw z)
        · simp only [Set.indicator_of_notMem h]
          exact tendsto_const_nhds
      have hsplit := fpa_sum_indicator_split hz₀S w
      rw [hS] at hsplit
      rw [hzz, show w z₀ = 1 - ∑ z, (S \ {z₀}).indicator w z by linarith]
      simp only [hδon]
      exact tendsto_const_nhds.sub hlim
    · simp only [hδoff _ z hzz]
      exact hrd_lim _ (hw z)

/-- **Dyadic transitions** along levels `G_0 ≤ G_1 ≤ ⋯ ≤ G_N`, `G_0` with the single atom `Ω`
(Lemma 8.30's approximation, and the path law of Lemma 8.31): for every `m`, weights `q_m ≥ 0` of
total `1`, vanishing where `w` does, with `q_m → w` pointwise as `m → ∞`, whose transition
probabilities `q_m (A_{i+1}) / q_m (A_i)` from an atom `A_i` of `G_i` to an atom `A_{i+1} ⊆ A_i`
of `G_{i+1}` are dyadic rationals `j / 2^m` for `i < N`. Each atom `A` gets the rounded
conditional weights `δ^A_m ≈ w / w(A)` on `A` (`fpa_exists_round`), the transition
`A_i → A_{i+1}` the dyadic probability `R_i = δ^{A_i}_m (A_{i+1})` in place of
`w(A_{i+1}) / w(A_i)`, and `q_m = w · Π_{i<N} R_i w(A_i) / w(A_{i+1})` along the path of each
point. -/
private theorem fpa_exists_dyadic_weights {Ω : Type*} [Fintype Ω] (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ i, G i ≤ G (i + 1)) (hG0 : ∀ x, atom (G 0) x = Set.univ) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) (N : ℕ) :
    ∃ q : ℕ → Ω → ℝ, (∀ m x, 0 ≤ q m x) ∧ (∀ m, ∑ x, q m x = 1) ∧
      (∀ m x, w x = 0 → q m x = 0) ∧ (∀ x, Tendsto (fun m => q m x) atTop (𝓝 (w x))) ∧
      ∀ m, ∀ i < N, ∀ x, ∃ j : ℕ, ∑ y, (atom (G (i + 1)) x).indicator (q m) y =
        j / 2 ^ m * ∑ y, (atom (G i) x).indicator (q m) y := by
  classical
  -- the weight of a set
  obtain ⟨M, hM⟩ : ∃ M : Set Ω → ℝ, M = fun S => ∑ x, S.indicator w x := ⟨_, rfl⟩
  have hMx : ∀ S, M S = ∑ x, S.indicator w x := fun S => by rw [hM]
  have hMnn : ∀ S, 0 ≤ M S := fun S => by rw [hMx]; exact fpa_sum_indicator_nonneg hw S
  have hMle : ∀ {S x}, x ∈ S → w x ≤ M S := fun hx => by rw [hMx]; exact fpa_le_sum_indicator hw hx
  have hMmono : ∀ {S T}, S ⊆ T → M S ≤ M T := fun h => by
    rw [hMx, hMx]; exact fpa_sum_indicator_mono hw h
  have hsum1 : ∀ S, M S ≠ 0 → ∑ z, S.indicator (fun z => w z / M S) z = 1 := fun S hS => by
    have h : ∀ z, S.indicator (fun z => w z / M S) z = S.indicator w z / M S := fun z => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_div]
    rw [Finset.sum_congr rfl fun z _ => h z, ← Finset.sum_div, ← hMx, div_self hS]
  -- the atoms of the coarser levels
  have hGmono : Monotone G := monotone_nat_of_le_succ hG
  have hsub : ∀ {i j x y}, i ≤ j → y ∈ atom (G j) x → y ∈ atom (G i) x := fun hij hy =>
    fpa_mem_atom_of_le (hGmono hij) hy
  have hAeq : ∀ {i j x y}, i ≤ j → y ∈ atom (G j) x → atom (G i) y = atom (G i) x :=
    fun hij hy => fpa_atom_eq_of_mem (hsub hij hy)
  -- an atom of `G_i` is a union of atoms of `G_{i+1}`
  have hsat : ∀ i x, ∀ z ∈ atom (G i) x, ∀ y ∈ atom (G (i + 1)) z, y ∈ atom (G i) x :=
    fun i x z hz y hy => by
      rw [← fpa_atom_eq_of_mem hz]
      exact hsub (Nat.le_succ i) hy
  -- the rounded conditional weights on each set
  choose δ hδ0 hδj hδw hδ1 using fun S : Set Ω =>
    fpa_exists_round S (fun z => w z / M S) fun z => div_nonneg (hw z) (hMnn S)
  choose J hJ using hδj
  -- the dyadic transitions `R` and their ratios `ρ` to the true transitions
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℕ → Ω → ℝ,
      R = fun m i x => ∑ y, (atom (G (i + 1)) x).indicator (δ (atom (G i) x) m) y := ⟨_, rfl⟩
  have hRx : ∀ m i x, R m i x = ∑ y, (atom (G (i + 1)) x).indicator (δ (atom (G i) x) m) y :=
    fun m i x => by rw [hR]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ → Ω → ℝ,
      ρ = fun m i x => R m i x * M (atom (G i) x) / M (atom (G (i + 1)) x) := ⟨_, rfl⟩
  have hρx : ∀ m i x, ρ m i x = R m i x * M (atom (G i) x) / M (atom (G (i + 1)) x) :=
    fun m i x => by rw [hρ]
  obtain ⟨q, hq⟩ : ∃ q : ℕ → Ω → ℝ, q = fun m x => w x * ∏ i ∈ Finset.range N, ρ m i x :=
    ⟨_, rfl⟩
  have hqx : ∀ m x, q m x = w x * ∏ i ∈ Finset.range N, ρ m i x := fun m x => by rw [hq]
  -- `ρ_i` only depends on the atom of `G_{i+1}`
  have hρconst : ∀ m i j x y, i + 1 ≤ j → y ∈ atom (G j) x → ρ m i y = ρ m i x := by
    intro m i j x y hij hy
    rw [hρx, hρx, hRx, hRx, hAeq (by omega : i ≤ j) hy, hAeq hij hy]
  have hρnn : ∀ m i x, 0 ≤ ρ m i x := fun m i x => by
    rw [hρx, hRx]
    exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun y _ =>
      Set.indicator_nonneg (fun y _ => hδ0 _ _ _) y) (hMnn _)) (hMnn _)
  -- the transitions `R` sum to `1`: `Σ_{y ∈ A_i(x)} ρ_i(y) w(y) = w(A_i(x))`
  have hdesign : ∀ m i x,
      ∑ y, (atom (G i) x).indicator (fun y => ρ m i y * w y) y = M (atom (G i) x) := by
    intro m i x
    by_cases hS0 : M (atom (G i) x) = 0
    · rw [hS0]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y ∈ atom (G i) x
      · rw [Set.indicator_of_mem hy, le_antisymm (hS0 ▸ hMle hy) (hw y), mul_zero]
      · rw [Set.indicator_of_notMem hy]
    obtain ⟨hδsum, -⟩ := hδ1 _ (hsum1 _ hS0)
    -- regroup by the atoms of `G_{i+1}`
    have key : ∑ y, (atom (G i) x).indicator (fun y => ρ m i y * w y) y =
        ∑ y, (atom (G i) x).indicator (fun y => M (atom (G i) x) * δ (atom (G i) x) m y) y := by
      refine fpa_sum_regroup (G (i + 1)) (hsat i x) fun y hy => ?_
      have hAy : atom (G i) y = atom (G i) x := fpa_atom_eq_of_mem hy
      rw [fpa_sum_indicator_const_mul _ (c := ρ m i) (c₀ := ρ m i y)
          (fun z hz => hρconst m i (i + 1) y z le_rfl hz),
        fpa_sum_indicator_const_mul _ (c := fun _ => M (atom (G i) x)) (fun _ _ => rfl), ← hMx]
      by_cases hB : M (atom (G (i + 1)) y) = 0
      · -- an atom of weight `0` has rounded weight `0`
        have h0 : ∑ z, (atom (G (i + 1)) y).indicator (δ (atom (G i) x) m) z = 0 :=
          Finset.sum_eq_zero fun z _ => by
            by_cases hz : z ∈ atom (G (i + 1)) y
            · rw [Set.indicator_of_mem hz]
              exact hδw _ _ _ (by rw [le_antisymm (hB ▸ hMle hz) (hw z), zero_div])
            · rw [Set.indicator_of_notMem hz]
        rw [hB, mul_zero, h0, mul_zero]
      · rw [hρx, hRx, hAy, div_mul_cancel₀ _ hB, mul_comm]
    rw [key, fpa_sum_indicator_const_mul _ (c := fun _ => M (atom (G i) x)) (fun _ _ => rfl),
      hδsum m, mul_one]
  -- the tower property: `Σ_{y ∈ A_i(x)} w(y) Π_{i ≤ l < N} ρ_l(y) = w(A_i(x))`
  have htower : ∀ m d i, i + d = N → ∀ x, ∑ y, (atom (G i) x).indicator
      (fun y => w y * ∏ l ∈ Finset.Ico i N, ρ m l y) y = M (atom (G i) x) := by
    intro m d
    induction d with
    | zero =>
      intro i hi x
      obtain rfl : i = N := by omega
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one, hMx]
    | succ d ih =>
      intro i hi x
      have hiN : i < N := by omega
      simp_rw [Finset.prod_eq_prod_Ico_succ_bot hiN]
      rw [← hdesign m i x]
      refine fpa_sum_regroup (G (i + 1)) (hsat i x) fun y hy => ?_
      have e1 : ∀ z, w z * (ρ m i z * ∏ l ∈ Finset.Ico (i + 1) N, ρ m l z) =
          ρ m i z * (w z * ∏ l ∈ Finset.Ico (i + 1) N, ρ m l z) := fun z => by ring
      simp_rw [e1]
      rw [fpa_sum_indicator_const_mul _ (c := ρ m i) (c₀ := ρ m i y)
          (fun z hz => hρconst m i (i + 1) y z le_rfl hz),
        fpa_sum_indicator_const_mul _ (c := ρ m i) (c₀ := ρ m i y)
          (fun z hz => hρconst m i (i + 1) y z le_rfl hz),
        ih (i + 1) (by omega) y, hMx]
  -- the new weights of the atoms: `q_m (A_i(x)) = Π_{l < i} ρ_l(x) · w(A_i(x))`
  have hmass : ∀ m i, i ≤ N → ∀ x, ∑ y, (atom (G i) x).indicator (q m) y =
      (∏ l ∈ Finset.range i, ρ m l x) * M (atom (G i) x) := by
    intro m i hi x
    have e : q m = fun y => (∏ l ∈ Finset.range i, ρ m l y) *
        (w y * ∏ l ∈ Finset.Ico i N, ρ m l y) := funext fun y => by
      rw [hqx, ← Finset.prod_range_mul_prod_Ico _ hi]
      ring
    rw [e, fpa_sum_indicator_const_mul _ (c := fun y => ∏ l ∈ Finset.range i, ρ m l y)
      (fun y hy => Finset.prod_congr rfl fun l hl => hρconst m l i x y (Finset.mem_range.1 hl) hy),
      htower m (N - i) i (by omega) x]
  refine ⟨q, fun m x => ?_, fun m => ?_, fun m x hx => ?_, fun x => ?_, fun m i hi x => ?_⟩
  · rw [hqx]
    exact mul_nonneg (hw x) (Finset.prod_nonneg fun i _ => hρnn m i x)
  · -- the total weight
    obtain ⟨x₀⟩ : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hw1
    have h := hmass m 0 (Nat.zero_le _) x₀
    rw [hG0, Finset.prod_range_zero, one_mul, hMx] at h
    simpa [Set.indicator_univ, hw1] using h
  · rw [hqx, hx, zero_mul]
  · -- convergence: each ratio `ρ_l` tends to `1` at a point of positive weight
    by_cases hx : w x = 0
    · simp only [hqx, hx, zero_mul]
      exact tendsto_const_nhds
    have hxpos : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
    have hρlim : ∀ l, Tendsto (fun m => ρ m l x) atTop (𝓝 1) := by
      intro l
      have hBpos : 0 < M (atom (G (l + 1)) x) := lt_of_lt_of_le hxpos (hMle (mem_atom_self _ x))
      have hSpos : 0 < M (atom (G l) x) := lt_of_lt_of_le hxpos (hMle (mem_atom_self _ x))
      have hRlim : Tendsto (fun m => R m l x) atTop
          (𝓝 (M (atom (G (l + 1)) x) / M (atom (G l) x))) := by
        simp only [hRx]
        rw [hMx (atom (G (l + 1)) x), Finset.sum_div]
        refine tendsto_finsetSum _ fun y _ => ?_
        by_cases hy : y ∈ atom (G (l + 1)) x
        · simp only [Set.indicator_of_mem hy]
          exact (hδ1 _ (hsum1 _ hSpos.ne')).2 y (hsub (Nat.le_succ l) hy)
        · simp only [Set.indicator_of_notMem hy, zero_div]
          exact tendsto_const_nhds
      have h := (hRlim.mul_const (M (atom (G l) x))).div_const (M (atom (G (l + 1)) x))
      rw [div_mul_cancel₀ _ hSpos.ne', div_self hBpos.ne'] at h
      simpa only [hρx] using h
    have h := tendsto_finsetProd (Finset.range N) fun l _ => hρlim l
    rw [Finset.prod_const_one] at h
    simp only [hqx]
    simpa using h.const_mul (w x)
  · -- the dyadic transitions
    rw [hmass m (i + 1) hi x, hmass m i hi.le x, Finset.prod_range_succ]
    by_cases hB : M (atom (G (i + 1)) x) = 0
    · exact ⟨0, by rw [hB]; simp⟩
    refine ⟨∑ y, if y ∈ atom (G (i + 1)) x then J (atom (G i) x) m y else 0, ?_⟩
    have hR' : R m i x =
        (↑(∑ y, if y ∈ atom (G (i + 1)) x then J (atom (G i) x) m y else 0) : ℝ) / 2 ^ m := by
      rw [hRx]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y ∈ atom (G (i + 1)) x
      · rw [Set.indicator_of_mem hy, ite_eq_left hy, hJ]
      · rw [Set.indicator_of_notMem hy, ite_eq_right hy, zero_div]
    rw [← hR', hρx, mul_assoc, div_mul_cancel₀ _ hB]
    ring

/-- The levels of the transitions of a filtration: `G_0 = {∅, Ω}` and `G_{k+1} = ℱ_k`. -/
@[instance_reducible]
private def fpaLevel {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) :
    ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | k + 1 => ℱ k

/-- **Dyadic path laws** on a finite filtered probability space: probabilities `ν_m` with dyadic
transition probabilities for `ℱ` up to time `n` (with denominator `2^m`), vanishing where `μ`
does, with `ν_m {x} → μ {x}` for every `x`. -/
private theorem fpa_exists_dyadic_laws {Ω : Type*} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (n : ℕ) :
    ∃ ν : ℕ → Measure Ω, (∀ m, IsProbabilityMeasure (ν m)) ∧
      (∀ m, HasDyadicTransitions (ν m) ℱ n) ∧ (∀ m x, μ {x} = 0 → ν m {x} = 0) ∧
      ∀ x, Tendsto (fun m => (ν m).real {x}) atTop (𝓝 (μ.real {x})) := by
  classical
  have := Fintype.ofFinite Ω
  have hw1 : ∑ x, μ.real {x} = 1 := by
    rw [← Set.indicator_univ (f := fun x => μ.real {x})]
    exact (fpa_measureReal_eq_sum μ Set.univ).symm.trans probReal_univ
  obtain ⟨q, hq0, hq1, hqw, hqlim, hqdy⟩ := fpa_exists_dyadic_weights (fpaLevel ℱ)
    (fun i => by
      cases i with
      | zero => exact bot_le
      | succ k => exact ℱ.mono k.le_succ)
    (fun x => fpa_atom_bot x) (fun x => μ.real {x}) (fun x => measureReal_nonneg) hw1 (n + 1)
  -- the probabilities with the point masses `q_m`
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ → Measure Ω,
      ν = fun m => ∑ x, ENNReal.ofReal (q m x) • Measure.dirac x := ⟨_, rfl⟩
  have hqs : ∀ m (s : Set Ω), 0 ≤ ∑ x, s.indicator (q m) x := fun m s =>
    Finset.sum_nonneg fun x _ => Set.indicator_nonneg (fun x _ => hq0 m x) x
  have hνapply : ∀ m (s : Set Ω), ν m s = ENNReal.ofReal (∑ x, s.indicator (q m) x) := by
    intro m s
    simp only [hν, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ => Set.indicator_nonneg (fun x _ => hq0 m x) x]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ s <;> simp [hx]
  have hνreal : ∀ m (s : Set Ω), (ν m).real s = ∑ x, s.indicator (q m) x := fun m s => by
    rw [measureReal_def, hνapply, ENNReal.toReal_ofReal (hqs m s)]
  have hsing : ∀ m x, ∑ y, ({x} : Set Ω).indicator (q m) y = q m x := fun m x => by
    rw [Fintype.sum_eq_single x fun y hy => Set.indicator_of_notMem hy _,
      Set.indicator_of_mem (Set.mem_singleton x)]
  have hνP : ∀ m, IsProbabilityMeasure (ν m) := fun m =>
    ⟨by rw [hνapply, Set.indicator_univ, hq1, ENNReal.ofReal_one]⟩
  refine ⟨ν, hνP, fun m => ⟨m, fun ω => ?_, fun k hk ω => ?_⟩, fun m x hx => ?_, fun x => ?_⟩
  · obtain ⟨j, hj⟩ := hqdy m 0 (Nat.succ_pos n) ω
    have h0 : atom (fpaLevel ℱ 0) ω = Set.univ := fpa_atom_bot ω
    rw [h0, Set.indicator_univ, hq1, mul_one] at hj
    exact ⟨j, by rw [hνreal]; exact hj⟩
  · obtain ⟨j, hj⟩ := hqdy m (k + 1) (by omega) ω
    exact ⟨j, by rw [hνreal, hνreal]; exact hj⟩
  · rw [hνapply, hsing, hqw m x (by rw [measureReal_def, hx, ENNReal.toReal_zero]),
      ENNReal.ofReal_zero]
  · simp only [hνreal, hsing]
    exact hqlim x

/-! ### The martingale correction of Remark 2.18 -/

/-- **Martingale correction** (Pisier, Remark 2.18): for an adapted process `Y` on a finite
space and a finite measure `ν`, `Y'_k = Y_k − Σ_{j < k} E_ν [Y_{j+1} − Y_j | ℱ_j]` is a
`ν`-martingale, its increments being `dY_{j+1} − E_ν [dY_{j+1} | ℱ_j]`. -/
private theorem fpa_martingale_correction {Ω : Type*} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [MeasurableSingletonClass Ω] {ν : Measure Ω} [IsFiniteMeasure ν] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} (hY : StronglyAdapted ℱ Y) :
    Martingale (fun k ω => Y k ω -
      ∑ j ∈ Finset.range k, ν[fun x => Y (j + 1) x - Y j x | ℱ j] ω) ℱ ν := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_) (fun k => Integrable.of_finite)
    (fun i => ?_)
  · exact (hY k).sub (Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range.1 hj).le))
  · have hsucc : (fun ω => Y (i + 1) ω -
          ∑ j ∈ Finset.range (i + 1), ν[fun x => Y (j + 1) x - Y j x | ℱ j] ω) -
        (fun ω => Y i ω - ∑ j ∈ Finset.range i, ν[fun x => Y (j + 1) x - Y j x | ℱ j] ω) =
        (fun ω => Y (i + 1) ω - Y i ω) - ν[fun x => Y (i + 1) x - Y i x | ℱ i] := by
      funext ω
      simp only [Pi.sub_apply, Finset.sum_range_succ]
      abel
    rw [hsucc]
    filter_upwards [condExp_sub (Integrable.of_finite (f := fun ω => Y (i + 1) ω - Y i ω))
      (Integrable.of_finite (f := ν[fun x => Y (i + 1) x - Y i x | ℱ i])) (ℱ i)] with ω hω
    rw [hω, Pi.sub_apply, condExp_of_stronglyMeasurable (ℱ.le i) stronglyMeasurable_condExp
      integrable_condExp, sub_self, Pi.zero_apply]

/-- The increments of a martingale have conditional expectation `0` at every point of positive
mass. -/
private theorem fpa_condExp_increment_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X}
    (hY : Martingale Y ℱ μ) {ω : Ω} (hω : μ {ω} ≠ 0) (j : ℕ) :
    μ[fun x => Y (j + 1) x - Y j x | ℱ j] ω = 0 := by
  have hae : μ[fun x => Y (j + 1) x - Y j x | ℱ j] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hY.integrable (j + 1)) (hY.integrable j) (ℱ j),
      hY.condExp_ae_eq j.le_succ, hY.condExp_ae_eq (le_refl j)] with ω h1 h2 h3
    change μ[Y (j + 1) - Y j | ℱ j] ω = 0
    rw [h1, Pi.sub_apply, h2, h3, sub_self]
  by_contra h
  exact hω (measure_mono_null (Set.singleton_subset_iff.2 h) (ae_iff.1 hae))

/-- On a finite space, conditional expectations depend continuously on the point masses at a
point of positive mass (`condExp_eq_atom_average`). -/
private theorem fpa_tendsto_condExp {Ω : Type*} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {ν : ℕ → Measure Ω}
    [∀ k, IsFiniteMeasure (ν k)]
    (hν : ∀ x, Tendsto (fun k => (ν k).real {x}) atTop (𝓝 (μ.real {x})))
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f : Ω → X) {ω : Ω} (hω : μ {ω} ≠ 0) :
    Tendsto (fun k => (ν k)[f | m] ω) atTop (𝓝 (μ[f | m] ω)) := by
  have := Fintype.ofFinite Ω
  have hωpos : 0 < μ.real {ω} := ENNReal.toReal_pos hω (measure_ne_top μ _)
  have hev : ∀ᶠ k in atTop, ν k {ω} ≠ 0 :=
    ((hν ω).eventually (lt_mem_nhds hωpos)).mono fun k hk h => by
      rw [measureReal_def, h, ENNReal.toReal_zero] at hk
      exact lt_irrefl _ hk
  have hA : Tendsto (fun k => (ν k).real (atom m ω)) atTop (𝓝 (μ.real (atom m ω))) := by
    have e : ∀ k, (ν k).real (atom m ω) =
        ∑ x, (atom m ω).indicator (fun x => (ν k).real {x}) x := fun k =>
      fpa_measureReal_eq_sum (ν k) (atom m ω)
    simp only [e, fpa_measureReal_eq_sum μ (atom m ω)]
    refine tendsto_finsetSum _ fun x _ => ?_
    by_cases hx : x ∈ atom m ω
    · simp only [Set.indicator_of_mem hx]
      exact hν x
    · simp only [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds
  have hApos : μ.real (atom m ω) ≠ 0 :=
    (lt_of_lt_of_le hωpos (measureReal_mono
      (Set.singleton_subset_iff.2 (mem_atom_self m ω)))).ne'
  rw [condExp_eq_atom_average hm f hω]
  refine Tendsto.congr' (hev.mono fun k hk => (condExp_eq_atom_average hm f hk).symm) ?_
  refine (hA.inv₀ hApos).smul (tendsto_finsetSum _ fun x _ => ?_)
  by_cases hx : x ∈ atom m ω
  · simp only [Set.indicator_of_mem hx]
    exact (hν x).smul_const _
  · simp only [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds

/-! ### `L^p` norms on a finite space -/

/-- On a finite space, `‖G‖_{L^p (ν)} = (Σ_x ν {x} ‖G x‖^p)^{1/p}`. -/
private theorem fpa_eLpNorm_eq {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] {E : Type*}
    [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p) (G : Ω → E) :
    eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal p) ν =
      ENNReal.ofReal ((∑ x, ν.real {x} * ‖G x‖ ^ p) ^ (1 / p)) := by
  have hterm : ∀ x, 0 ≤ ν.real {x} * ‖G x‖ ^ p := fun x =>
    mul_nonneg measureReal_nonneg (by positivity)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
      StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_fintype,
    ENNReal.toReal_ofReal hp.le,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun x _ => hterm x) (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun x _ => hterm x]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal,
    Real.enorm_eq_ofReal (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
    mul_comm]

/-- The `L^p` norms on a finite space are continuous in the point masses and in the values at the
points of positive mass. -/
private theorem fpa_tendsto_lpSum {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ν : ℕ → Measure Ω} (hν0 : ∀ m x, μ {x} = 0 → ν m {x} = 0)
    (hν : ∀ x, Tendsto (fun m => (ν m).real {x}) atTop (𝓝 (μ.real {x}))) {E : Type*}
    [NormedAddCommGroup E] {G : ℕ → Ω → E} {G₀ : Ω → E}
    (hG : ∀ x, μ {x} ≠ 0 → Tendsto (fun m => G m x) atTop (𝓝 (G₀ x))) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun m => (∑ x, (ν m).real {x} * ‖G m x‖ ^ p) ^ (1 / p)) atTop
      (𝓝 ((∑ x, μ.real {x} * ‖G₀ x‖ ^ p) ^ (1 / p))) := by
  refine Tendsto.rpow_const (tendsto_finsetSum _ fun x _ => ?_) (Or.inr (by positivity))
  by_cases hx : μ {x} = 0
  · have h1 : ∀ m, (ν m).real {x} = 0 := fun m => by
      rw [measureReal_def, hν0 m x hx, ENNReal.toReal_zero]
    have h2 : μ.real {x} = 0 := by rw [measureReal_def, hx, ENNReal.toReal_zero]
    simp only [h1, h2, zero_mul]
    exact tendsto_const_nhds
  · exact (hν x).mul (((hG x hx).norm).rpow_const (Or.inr hp.le))

/-- **Dyadic perturbation** of a finite model, for general multipliers (Pisier, *Martingales in
Banach spaces* (2016), §5.6; lecture notes (2011), Lemma 8.30's approximation, Lemma 8.31's
path-law estimate and Remark 2.18): for `η > 0` there are a probability `μ'` on the same finite
space, with dyadic transition probabilities for `ℱ` up to time `n`, and a martingale `Y'` for `ℱ`
and `μ'` started at `0`, such that `‖Y'_n‖_{L^p (μ')} ≤ ‖Y_n‖_{L^p (μ)} + η` and
`‖(φ • Y)_n‖_{L^p (μ)} ≤ ‖(φ • Y')_n‖_{L^p (μ')} + η`.

The transition probabilities are moved to dyadic rationals `j / 2^m` with the same sums, vanishing
where they vanish (`fpa_exists_dyadic_laws`, laws `μ'_m` with `μ'_m {ω} → μ {ω}`), and `Y'` is the
martingale correction of Remark 2.18 under `μ'_m`: `Y'_k = Y_k − Σ_{j<k} E' [Y_{j+1} − Y_j | ℱ_j]`.
At a point of positive `μ`-mass, the corrections tend to `E [Y_{j+1} − Y_j | ℱ_j] = 0`
(`condExp_eq_atom_average`), so `Y'_k → Y_k` on the support of `μ`, and both `L^p` norms, finite
sums, converge; `m` is taken large. The multipliers `φ` are arbitrary: the perturbation does not
involve them. -/
theorem exists_hasDyadicTransitions_approx_gen {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 X]
    [IsScalarTower ℝ 𝕜 X] {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (μ' : Measure Ω) (_ : IsProbabilityMeasure μ') (Y' : ℕ → Ω → X),
      HasDyadicTransitions μ' ℱ n ∧ Martingale Y' ℱ μ' ∧ (∀ ω, Y' 0 ω = 0) ∧
      eLpNorm (fun ω => ‖Y' n ω‖) (ENNReal.ofReal p) μ' ≤
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ + ENNReal.ofReal η ∧
      eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun ω => ‖martingaleTransform φ Y' n ω‖) (ENNReal.ofReal p) μ' +
          ENNReal.ofReal η := by
  have := Fintype.ofFinite Ω
  have hp0 : 0 < p := by linarith
  -- the dyadic laws
  obtain ⟨ν, hνP, hνD, hν0, hν⟩ := fpa_exists_dyadic_laws μ ℱ n
  have _ : ∀ m, IsProbabilityMeasure (ν m) := hνP
  -- the martingale corrections of Remark 2.18 under the dyadic laws
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → ℕ → Ω → X, Y' = fun m k ω => Y k ω -
      ∑ j ∈ Finset.range k, (ν m)[fun x => Y (j + 1) x - Y j x | ℱ j] ω := ⟨_, rfl⟩
  have hmart : ∀ m, Martingale (Y' m) ℱ (ν m) := fun m => by
    rw [hY']
    exact fpa_martingale_correction hY.stronglyAdapted
  have hY'0 : ∀ m ω, Y' m 0 ω = 0 := fun m ω => by simp [hY', hY0]
  -- on the support of `μ`, the corrections vanish in the limit
  have hconv : ∀ ω, μ {ω} ≠ 0 → ∀ k, Tendsto (fun m => Y' m k ω) atTop (𝓝 (Y k ω)) := by
    intro ω hω k
    have h := tendsto_finsetSum (Finset.range k) fun j _ =>
      fpa_tendsto_condExp hν (ℱ.le j) (fun x => Y (j + 1) x - Y j x) hω
    simp only [fpa_condExp_increment_eq_zero hY hω, Finset.sum_const_zero] at h
    simpa [hY'] using (tendsto_const_nhds (x := Y k ω)).sub h
  have hconvT : ∀ ω, μ {ω} ≠ 0 → Tendsto (fun m => martingaleTransform φ (Y' m) n ω) atTop
      (𝓝 (martingaleTransform φ Y n ω)) := fun ω hω =>
    tendsto_finsetSum _ fun k _ => ((hconv ω hω (k + 1)).sub (hconv ω hω k)).const_smul _
  -- the two `L^p` norms converge
  have h1 := fpa_tendsto_lpSum hν0 hν (fun ω hω => hconv ω hω n) hp0
  have h2 := fpa_tendsto_lpSum hν0 hν hconvT hp0
  obtain ⟨m, hm1, hm2⟩ := (((tendsto_order.1 h1).2 _ (lt_add_of_pos_right _ hη)).and
    ((tendsto_order.1 h2).1 _ (sub_lt_self _ hη))).exists
  have hnn : ∀ (ν' : Measure Ω) (G : Ω → X), 0 ≤ (∑ x, ν'.real {x} * ‖G x‖ ^ p) ^ (1 / p) :=
    fun ν' G => Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg measureReal_nonneg (by positivity)) _
  refine ⟨ν m, hνP m, Y' m, hνD m, hmart m, hY'0 m, ?_, ?_⟩
  · rw [fpa_eLpNorm_eq (ν m) hp0, fpa_eLpNorm_eq μ hp0, ← ENNReal.ofReal_add (hnn _ _) hη.le]
    exact ENNReal.ofReal_le_ofReal hm1.le
  · rw [fpa_eLpNorm_eq (ν m) hp0, fpa_eLpNorm_eq μ hp0, ← ENNReal.ofReal_add (hnn _ _) hη.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Dyadic perturbation** of a finite model: for `η > 0` there are a probability `μ'` on the same
finite space, with dyadic transition probabilities for `ℱ` up to time `n`, and a martingale `Y'`
for `ℱ` and `μ'` started at `0` (the martingale correction of Remark 2.18 of `Y` under `μ'`,
`Y'_k = Y_k − Σ_{j<k} E' [Y_{j+1} − Y_j | ℱ_j]`), such that
`‖Y'_n‖_{L^p (μ')} ≤ ‖Y_n‖_{L^p (μ)} + η` and `‖(σ • Y)_n‖_{L^p (μ)} ≤ ‖(σ • Y')_n‖_{L^p (μ')} + η`.
The case of real multipliers (signs, in the applications) of
`exists_hasDyadicTransitions_approx_gen`. -/
theorem exists_hasDyadicTransitions_approx {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} {σ : ℕ → Ω → ℝ} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (μ' : Measure Ω) (_ : IsProbabilityMeasure μ') (Y' : ℕ → Ω → X),
      HasDyadicTransitions μ' ℱ n ∧ Martingale Y' ℱ μ' ∧ (∀ ω, Y' 0 ω = 0) ∧
      eLpNorm (fun ω => ‖Y' n ω‖) (ENNReal.ofReal p) μ' ≤
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ + ENNReal.ofReal η ∧
      eLpNorm (fun ω => ‖martingaleTransform σ Y n ω‖) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun ω => ‖martingaleTransform σ Y' n ω‖) (ENNReal.ofReal p) μ' +
          ENNReal.ofReal η := by
  exact exists_hasDyadicTransitions_approx_gen (𝕜 := ℝ) hY hY0 hp n hη

end BanachProbability
