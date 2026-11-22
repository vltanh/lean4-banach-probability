module

public import BanachProbability.UMD.CubeTransform
public import BanachProbability.Martingale.Doob

/-!
# The good-λ inequality for martingale transforms on the sign cube

For the transform `T = cubeTransform σ` by predictable signs `σ` on the sign cube, this file proves
Lemmas 3.5.13 and 3.5.14 of T. Hytönen, J. van Neerven, M. Veraar and L. Weis (HNVW), *Analysis in
Banach Spaces I* (2016), for the Paley–Walsh filtration `ℱ_n = σ (ε_0, …, ε_{n−1})`,
`n = 0, …, N` (the book's filtrations are indexed by `ℤ`, with `f_{−∞}` in the place of `f_0`).
Notation: `f_n = E [f | ℱ_n]`, `f* = max_n ‖f_n‖` (`cubeMax f`), `T* f = (T f)*`.

* `IsWeakTransformBound X σ q K`: `T` is bounded from `H^q (X)` to `L^{q,∞} (X)` with constant `K`.
  A bound on `L^q (X)` implies it (`IsTransformBound.isWeakTransformBound`; the trivial bounds in
  the proof of (3.48), p. 233).
* `IsWeakTransformBound.isLocalTransformBound`, HNVW, Lemma 3.5.13 (p. 229–230): the localized
  weak-type bound, `P (F ∩ {‖T (ᵏf)‖ > α ‖ᵏf‖_∞}) ≤ (K / α)^q P (F)` for events `F ∈ ℱ_k` and
  `ᵏf = f − f_k`; this is the condition (3.55) (`IsLocalTransformBound X σ α η`) with
  `η = (K / α)^q`.
* `IsLocalTransformBound.goodLambda`, HNVW, Lemma 3.5.14 (p. 230–231): the condition (3.55) implies
  the good-λ inequality `P (T* f > θ λ, f* ∨ w* ≤ δ λ) ≤ η P (T* f > λ)`,
  `δ ≤ (θ − 1) / (3 α + 1)`, `w` a predictable majorant of the differences `‖f_{n+1} − f_n‖`.

The stopping times of the book are first times `gdlTime`, where the value `N + 1` stands for `∞`,
and the stopped martingale `f^τ` is `cubeStop τ f`, the transform of `f` by the multipliers
`1_{k < τ}`; so `T f^τ = (T f)^τ` because transforms commute (`cubeTransform_cubeStop`).
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {N : ℕ}

section Prob

theorem gdl_prob_nonneg (s : Set (Fin N → Bool)) : 0 ≤ prob s :=
  avg_nonneg fun ε => Set.indicator_nonneg (fun _ _ => zero_le_one) ε

theorem gdl_prob_mono {s s' : Set (Fin N → Bool)} (h : s ⊆ s') : prob s ≤ prob s' :=
  avg_mono fun ε => Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) ε

/-- Chebyshev's inequality on the cube. -/
private theorem gdl_chebyshev {u : (Fin N → Bool) → ℝ} (hu : ∀ ε, 0 ≤ u ε) {t q : ℝ} (ht : 0 ≤ t)
    (hq : 0 ≤ q) : t ^ q * prob {ε | t < u ε} ≤ avg (fun ε => u ε ^ q) := by
  rw [prob, ← avg_const_mul]
  refine avg_mono fun ε => ?_
  by_cases hε : t < u ε
  · rw [Set.indicator_of_mem (show ε ∈ {ε | t < u ε} from hε), Pi.one_apply, mul_one]
    exact Real.rpow_le_rpow ht hε.le hq
  · rw [Set.indicator_of_notMem (show ε ∉ {ε | t < u ε} from hε), mul_zero]
    exact Real.rpow_nonneg (hu ε) _

/-- Splitting an event along the values `0, …, N` of a random variable. -/
private theorem gdl_prob_eq_sum {A : Set (Fin N → Bool)} {ρ : (Fin N → Bool) → ℕ}
    (hA : ∀ ε ∈ A, ρ ε ≤ N) :
    prob A = ∑ k ∈ Finset.range (N + 1), prob (A ∩ {ε | ρ ε = k}) := by
  simp only [prob]
  rw [← avg_sum]
  congr 1
  funext ε
  by_cases hε : ε ∈ A
  · rw [Set.indicator_of_mem hε, Finset.sum_eq_single_of_mem (ρ ε)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hA ε hε))) fun k _ hk =>
        Set.indicator_of_notMem (fun h : ε ∈ A ∩ {ε | ρ ε = k} => hk h.2.symm) _]
    exact (Set.indicator_of_mem (show ε ∈ A ∩ {ε' | ρ ε' = ρ ε} from ⟨hε, rfl⟩) _).symm
  · rw [Set.indicator_of_notMem hε]
    exact (Finset.sum_eq_zero fun k _ =>
      Set.indicator_of_notMem (fun h : ε ∈ A ∩ {ε | ρ ε = k} => hε h.1) _).symm

private theorem gdl_lt_runningMax_iff {Ω : Type*} {u : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} {t : ℝ} :
    t < runningMax u n ω ↔ ∃ k ≤ n, t < u k ω := by
  simp only [runningMax, Finset.lt_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]

theorem gdl_runningMax_le {Ω : Type*} {u : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} {a : ℝ}
    (h : ∀ k ≤ n, u k ω ≤ a) : runningMax u n ω ≤ a :=
  Finset.sup'_le _ _ fun k hk => h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

end Prob

section Maximal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Doob's maximal function `f* = max_{k ≤ N} ‖E [f | ℱ_k]‖` of a function on the sign cube. -/
noncomputable def cubeMax (f : (Fin N → Bool) → X) : (Fin N → Bool) → ℝ :=
  runningMax (fun k ε => ‖condAvg k f ε‖) N

theorem norm_condAvg_le_cubeMax (f : (Fin N → Bool) → X) (k : ℕ) (ε : Fin N → Bool) :
    ‖condAvg k f ε‖ ≤ cubeMax f ε := by
  rcases le_total k N with h | h
  · exact le_runningMax (fun k ε => ‖condAvg k f ε‖) h ε
  · rw [cbt_condAvg_of_le h, ← congrFun (cbt_condAvg_of_le le_rfl f) ε]
    exact le_runningMax (fun k ε => ‖condAvg k f ε‖) (le_refl N) ε

theorem norm_le_cubeMax (f : (Fin N → Bool) → X) (ε : Fin N → Bool) : ‖f ε‖ ≤ cubeMax f ε := by
  have h := norm_condAvg_le_cubeMax f N ε
  rwa [cbt_condAvg_of_le le_rfl] at h

theorem cubeMax_nonneg (f : (Fin N → Bool) → X) (ε : Fin N → Bool) : 0 ≤ cubeMax f ε :=
  (norm_nonneg _).trans (norm_le_cubeMax f ε)

/-- A conditional expectation of a function with `‖f‖_∞ ≤ a` has norm at most `a`. -/
private theorem gdl_norm_condAvg_le {f : (Fin N → Bool) → X} {a : ℝ} (hf : ∀ ε, ‖f ε‖ ≤ a) (k : ℕ)
    (ε : Fin N → Bool) : ‖condAvg k f ε‖ ≤ a := by
  refine (norm_condAvg_le k f ε).trans ?_
  have h : condAvg k (fun ε => ‖f ε‖) ε ≤ condAvg k (fun _ : Fin N → Bool => a) ε := by
    simp only [condAvg, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε' _ => hf _) (by positivity)
  rwa [condAvg_of_isAdapted (f := fun _ : Fin N → Bool => a) fun _ _ _ => rfl] at h

end Maximal

section Localized

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {σ : Fin N → (Fin N → Bool) → ℝ}

variable (X) in
/-- The transform by `σ` is bounded from `H^q (X)` to `L^{q,∞} (X)` with constant `K`:
`t^q P (‖T f‖ > t) ≤ K^q E (f*)^q` for every `f` and every `t > 0` (HNVW, p. 222: the martingale
Hardy space `H^q (X)` has the norm `‖f‖_{H^q} = ‖f*‖_q`). -/
def IsWeakTransformBound (σ : Fin N → (Fin N → Bool) → ℝ) (q K : ℝ) : Prop :=
  ∀ (f : (Fin N → Bool) → X) (t : ℝ), 0 < t →
    t ^ q * prob {ε | t < ‖cubeTransform σ f ε‖} ≤ K ^ q * avg (fun ε => cubeMax f ε ^ q)

/-- The trivial bound `‖T‖_{H^q → L^{q,∞}} ≤ ‖T‖_{L^q → L^q}` (HNVW, proof of (3.48), p. 233):
Chebyshev's inequality and `‖f‖ ≤ f*`. -/
theorem IsTransformBound.isWeakTransformBound {q K : ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    (h : IsTransformBound X σ q K) : IsWeakTransformBound X σ q K := by
  intro f t ht
  have hn : ∀ u : (Fin N → Bool) → X,
      SignCube.lpNorm (fun x => ‖x‖) q u ^ q = avg fun ε => ‖u ε‖ ^ q :=
    lpNorm_rpow (fun x => norm_nonneg x) hq
  have h0 : ∀ u : (Fin N → Bool) → X, 0 ≤ SignCube.lpNorm (fun x => ‖x‖) q u :=
    lpNorm_nonneg (fun x => norm_nonneg x) q
  calc t ^ q * prob {ε | t < ‖cubeTransform σ f ε‖}
      ≤ avg fun ε => ‖cubeTransform σ f ε‖ ^ q :=
        gdl_chebyshev (fun _ => norm_nonneg _) ht.le hq.le
    _ ≤ K ^ q * avg fun ε => ‖f ε‖ ^ q := by
        rw [← hn, ← hn, ← Real.mul_rpow hK (h0 f)]
        exact Real.rpow_le_rpow (h0 _) (h f) hq.le
    _ ≤ K ^ q * avg fun ε => cubeMax f ε ^ q :=
        mul_le_mul_of_nonneg_left (avg_mono fun ε =>
          Real.rpow_le_rpow (norm_nonneg _) (norm_le_cubeMax f ε) hq.le) (Real.rpow_nonneg hK q)

variable (X) in
/-- The condition (3.55) of HNVW (Lemma 3.5.14, p. 230) with parameters `α`, `η`: for every event
`F` depending only on the first `k` signs and every `f`, with `ᵏf = f − E [f | ℱ_k]`,
`P (F ∩ {‖T (ᵏf)‖ > α ‖ᵏf‖_∞}) ≤ η P (F)`. The norm `‖ᵏf‖_∞` may be replaced by any bound `a` of
`‖ᵏf‖`, which makes the event smaller. -/
def IsLocalTransformBound (σ : Fin N → (Fin N → Bool) → ℝ) (α η : ℝ) : Prop :=
  ∀ (k : ℕ) (F : Set (Fin N → Bool)) (f : (Fin N → Bool) → X) (a : ℝ),
    (∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → (ε ∈ F ↔ ε' ∈ F)) →
    (∀ ε, ‖f ε - condAvg k f ε‖ ≤ a) →
    prob (F ∩ {ε | α * a < ‖cubeTransform σ (f - condAvg k f) ε‖}) ≤ η * prob F

/-- `E [1_F ᵏf | ℱ_n] = 1_F E [ᵏf | ℱ_n]` for all `n` (for `n ≤ k` both vanish), in the proof of
HNVW, Lemma 3.5.13 (p. 230). -/
private theorem gdl_condAvg_indicator {k : ℕ} {F : Set (Fin N → Bool)}
    (hF : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → (ε ∈ F ↔ ε' ∈ F))
    (f : (Fin N → Bool) → X) (n : ℕ) :
    condAvg n (F.indicator (f - condAvg k f)) = F.indicator (condAvg n (f - condAvg k f)) := by
  classical
  set v : (Fin N → Bool) → ℝ := F.indicator 1 with hv
  have hind : ∀ u : (Fin N → Bool) → X, F.indicator u = fun ε => v ε • u ε := fun u => by
    funext ε
    by_cases hε : ε ∈ F <;> simp [hv, hε]
  have hvm : ∀ l, k ≤ l → ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < l → ε j = ε' j) →
      v ε = v ε' := by
    intro l hl ε ε' h
    have := hF ε ε' fun j hj => h j (hj.trans_le hl)
    by_cases hε : ε ∈ F
    · simp [hv, hε, this.mp hε]
    · simp [hv, hε, mt this.mpr hε]
  rw [hind, hind]
  rcases le_total k n with h | h
  · exact cbt_condAvg_smul (hvm n h) _
  · have h0 : ∀ l ≤ k, condAvg l (f - condAvg k f) = 0 := fun l hl => by
      rw [cbt_condAvg_sub, condAvg_condAvg hl, sub_self]
    rw [← condAvg_condAvg h, cbt_condAvg_smul (hvm k le_rfl), h0 k le_rfl, h0 n h]
    simp only [Pi.zero_apply, smul_zero]
    exact condAvg_of_isAdapted fun _ _ _ => rfl

/-- **HNVW, Lemma 3.5.13** (p. 229–230), the localized weak-type bound: if `T` is bounded from
`H^q (X)` to `L^{q,∞} (X)` with constant `K`, then for every `α > 0` and every event `F` depending
only on the first `k` signs, with `ᵏf = f − E [f | ℱ_k]`,
`P (F ∩ {‖T (ᵏf)‖ > α ‖ᵏf‖_∞}) ≤ (K / α)^q P (F)`. Indeed `1_F T (ᵏf) = T (1_F ᵏf)`, to which the
weak-type bound applies, and `‖1_F ᵏf‖_{H^q} ≤ P (F)^{1/q} ‖ᵏf‖_∞`. (If `‖ᵏf‖_∞ = 0`, where the
weak-type bound says nothing, then `T (ᵏf) = 0` and the event is empty.) -/
theorem IsWeakTransformBound.isLocalTransformBound {q K α : ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    (hα : 0 < α) (h : IsWeakTransformBound X σ q K) :
    IsLocalTransformBound X σ α ((K / α) ^ q) := by
  intro k F f a hF ha
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha fun _ => false)
  rcases ha0.eq_or_lt with ha0 | ha0
  · -- `ᵏf = 0`: the event is empty
    have hf0 : f - condAvg k f = 0 := by
      funext ε
      have := ha ε
      rw [← ha0] at this
      exact norm_le_zero_iff.mp this
    have hempty : F ∩ {ε | α * a < ‖cubeTransform σ (f - condAvg k f) ε‖} = ∅ := by
      rw [hf0, cubeTransform_zero, ← ha0]
      simp
    rw [hempty, prob]
    simpa using mul_nonneg (Real.rpow_nonneg (div_nonneg hK hα.le) q) (gdl_prob_nonneg F)
  set u := F.indicator (f - condAvg k f) with hu
  have hE := gdl_condAvg_indicator hF f
  -- `1_F T (ᵏf) = T (1_F ᵏf)`
  have hT : ∀ ε ∈ F, cubeTransform σ u ε = cubeTransform σ (f - condAvg k f) ε := by
    intro ε hε
    simp only [cubeTransform, hu, hE, Set.indicator_of_mem hε]
  -- `(1_F ᵏf)* ≤ a 1_F`
  have hmax : ∀ ε, cubeMax u ε ^ q ≤ a ^ q * F.indicator 1 ε := by
    intro ε
    by_cases hε : ε ∈ F
    · rw [Set.indicator_of_mem hε, Pi.one_apply, mul_one]
      refine Real.rpow_le_rpow (cubeMax_nonneg u ε) (gdl_runningMax_le fun n _ => ?_) hq.le
      rw [hu, hE, Set.indicator_of_mem hε]
      exact gdl_norm_condAvg_le ha n ε
    · have h0 : cubeMax u ε = 0 := by
        refine le_antisymm (gdl_runningMax_le fun n _ => ?_) (cubeMax_nonneg u ε)
        rw [hu, hE, Set.indicator_of_notMem hε, norm_zero]
      rw [Set.indicator_of_notMem hε, mul_zero, h0, Real.zero_rpow hq.ne']
  have hαa : 0 < α * a := mul_pos hα ha0
  have key : (α * a) ^ q * prob {ε | α * a < ‖cubeTransform σ u ε‖} ≤
      (α * a) ^ q * ((K / α) ^ q * prob F) := by
    calc (α * a) ^ q * prob {ε | α * a < ‖cubeTransform σ u ε‖}
        ≤ K ^ q * avg (fun ε => cubeMax u ε ^ q) := h u (α * a) hαa
      _ ≤ K ^ q * (a ^ q * prob F) := by
          rw [prob, ← avg_const_mul (a ^ q)]
          exact mul_le_mul_of_nonneg_left (avg_mono hmax) (Real.rpow_nonneg hK q)
      _ = (α * a) ^ q * ((K / α) ^ q * prob F) := by
          rw [← mul_assoc, ← mul_assoc, ← Real.mul_rpow hK ha0.le,
            ← Real.mul_rpow hαa.le (div_nonneg hK hα.le)]
          congr 2
          field_simp
  refine (gdl_prob_mono fun ε hε => ?_).trans
    (le_of_mul_le_mul_left key (Real.rpow_pos_of_pos hαa q))
  change α * a < ‖cubeTransform σ u ε‖
  rw [hT ε hε.1]
  exact hε.2

end Localized

section Stopping

/-! ### Stopping times and stopped martingales -/

open Classical in
/-- The first time `n ≤ N` at which the event `P n` happens; the value `N + 1` stands for `∞`
(the event never happens). -/
noncomputable def gdlTime (P : ℕ → Set (Fin N → Bool)) (ε : Fin N → Bool) : ℕ :=
  Nat.find (p := fun n => N < n ∨ ε ∈ P n) ⟨N + 1, Or.inl (Nat.lt_succ_self N)⟩

theorem gdl_notMem_of_lt_time {P : ℕ → Set (Fin N → Bool)} {ε : Fin N → Bool} {n : ℕ}
    (h : n < gdlTime P ε) : ε ∉ P n := fun hn => by
  classical
  exact Nat.find_min _ h (Or.inr hn)

theorem gdl_time_le_of_mem {P : ℕ → Set (Fin N → Bool)} {ε : Fin N → Bool} {n : ℕ}
    (h : ε ∈ P n) : gdlTime P ε ≤ n := by
  classical
  exact Nat.find_min' _ (Or.inr h)

theorem gdl_mem_time {P : ℕ → Set (Fin N → Bool)} {ε : Fin N → Bool} (h : gdlTime P ε ≤ N) :
    ε ∈ P (gdlTime P ε) := by
  classical
  exact (Nat.find_spec (p := fun n => N < n ∨ ε ∈ P n) ⟨N + 1, Or.inl (Nat.lt_succ_self N)⟩
    ).resolve_left (not_lt.mpr h)

theorem gdl_lt_time_iff {P : ℕ → Set (Fin N → Bool)} {ε : Fin N → Bool} {n : ℕ} (hn : n ≤ N) :
    n < gdlTime P ε ↔ ∀ j ≤ n, ε ∉ P j := by
  refine ⟨fun h j hj => gdl_notMem_of_lt_time (hj.trans_lt h), fun h => ?_⟩
  by_contra hlt
  have hle := not_lt.mp hlt
  exact h _ hle (gdl_mem_time (hle.trans hn))

theorem gdl_time_le_iff {P : ℕ → Set (Fin N → Bool)} {ε : Fin N → Bool} :
    gdlTime P ε ≤ N ↔ ∃ n ≤ N, ε ∈ P n := by
  constructor
  · exact fun h => ⟨_, h, gdl_mem_time h⟩
  · rintro ⟨n, hn, h⟩
    exact (gdl_time_le_of_mem h).trans hn

/-- The first time of an adapted sequence of events is a stopping time: whether it is later than
`n` is determined by the first `n` signs. -/
theorem gdl_lt_time_congr {P : ℕ → Set (Fin N → Bool)}
    (hP : ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) →
      (ε ∈ P n ↔ ε' ∈ P n)) {n : ℕ} (hn : n ≤ N) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < n → ε j = ε' j) : n < gdlTime P ε ↔ n < gdlTime P ε' := by
  rw [gdl_lt_time_iff hn, gdl_lt_time_iff hn]
  exact forall_congr' fun j => imp_congr_right fun hj =>
    not_congr (hP j ε ε' fun i hi => h i (hi.trans_le hj))

/-- The first time of an adapted sequence of events is a stopping time: whether it equals `k` is
determined by the first `k` signs. -/
theorem gdl_time_eq_congr {P : ℕ → Set (Fin N → Bool)}
    (hP : ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) →
      (ε ∈ P n ↔ ε' ∈ P n)) {k : ℕ} (hk : k ≤ N) {ε ε' : Fin N → Bool}
    (h : ∀ j : Fin N, j.val < k → ε j = ε' j) : gdlTime P ε = k ↔ gdlTime P ε' = k := by
  have h1 : ∀ n ≤ k, (n < gdlTime P ε ↔ n < gdlTime P ε') := fun n hn =>
    gdl_lt_time_congr hP (hn.trans hk) fun j hj => h j (hj.trans_le hn)
  have h2 := h1 k le_rfl
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · omega
  · have h3 := h1 (k - 1) (Nat.sub_le k 1)
    omega

/-- `τ` is a stopping time (with values in `ℕ`; every value `> N` stands for `∞`): for `k ≤ N`,
whether `k < τ` is determined by the first `k` signs. -/
def IsCubeStopping (τ : (Fin N → Bool) → ℕ) : Prop :=
  ∀ (k : ℕ) (ε ε' : Fin N → Bool), k ≤ N → (∀ j : Fin N, j.val < k → ε j = ε' j) →
    (k < τ ε ↔ k < τ ε')

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {σ : Fin N → (Fin N → Bool) → ℝ}

/-- The martingale generated by `f` stopped at `τ`, at the final time: the transform of `f` by the
multipliers `1_{k < τ}`. -/
noncomputable def cubeStop (τ : (Fin N → Bool) → ℕ) (f : (Fin N → Bool) → X) :
    (Fin N → Bool) → X :=
  cubeTransform (fun k ε => if k.val < τ ε then 1 else 0) f

/-- The multipliers `1_{k < τ}` of a stopping time are predictable. -/
theorem gdl_isPredictable_stop {τ : (Fin N → Bool) → ℕ}
    (hτ : IsCubeStopping τ) :
    IsPredictable fun (k : Fin N) ε => if k.val < τ ε then (1 : ℝ) else 0 := by
  intro k ε ε' h
  dsimp only
  rw [if_congr (hτ k.val ε ε' k.isLt.le fun j hj => h j (Fin.lt_def.mpr hj)) rfl rfl]

/-- The stopped martingale at time `n` is the martingale at time `n ∧ τ`. -/
theorem condAvg_cubeStop {τ : (Fin N → Bool) → ℕ}
    (hτ : IsCubeStopping τ) (f : (Fin N → Bool) → X) (n : ℕ) (ε : Fin N → Bool) :
    condAvg n (cubeStop τ f) ε = condAvg (min n (τ ε)) f ε := by
  have hv := gdl_isPredictable_stop hτ
  induction n with
  | zero => rw [Nat.zero_min, cubeStop, condAvg_zero_cubeTransform hv]
  | succ n ih =>
    have h : condAvg (n + 1) (cubeStop τ f) ε - condAvg n (cubeStop τ f) ε = _ :=
      condAvg_succ_sub_cubeTransform hv f n ε
    rw [← sub_add_cancel (condAvg (n + 1) (cubeStop τ f) ε) (condAvg n (cubeStop τ f) ε), h, ih]
    by_cases hn : n < N
    · rw [dite_eq_left hn]
      by_cases hτn : n < τ ε
      · rw [ite_eq_left hτn, one_smul, min_eq_left hτn.le, min_eq_left (Nat.succ_le_of_lt hτn),
          sub_add_cancel]
      · rw [ite_eq_right hτn, zero_smul, zero_add, min_eq_right (not_lt.mp hτn),
          min_eq_right (by omega)]
    · rw [dite_eq_right hn, zero_add]
      by_cases hτn : n < τ ε
      · rw [min_eq_left hτn.le, min_eq_left (Nat.succ_le_of_lt hτn),
          cbt_condAvg_of_le (not_lt.mp hn), cbt_condAvg_of_le (by omega)]
      · rw [min_eq_right (not_lt.mp hτn), min_eq_right (by omega)]

/-- The stopped martingale at the final time. -/
theorem cubeStop_apply {τ : (Fin N → Bool) → ℕ}
    (hτ : IsCubeStopping τ) (f : (Fin N → Bool) → X) (ε : Fin N → Bool) :
    cubeStop τ f ε = condAvg (min N (τ ε)) f ε := by
  rw [← condAvg_cubeStop hτ, cbt_condAvg_of_le le_rfl]

/-- The transform of the stopped martingale is the stopped transform (HNVW, proof of Lemma 3.5.14,
p. 231). -/
theorem cubeTransform_cubeStop (hσ : IsPredictable σ) {τ : (Fin N → Bool) → ℕ}
    (hτ : IsCubeStopping τ) (f : (Fin N → Bool) → X) :
    cubeTransform σ (cubeStop τ f) = cubeStop τ (cubeTransform σ f) := by
  rw [cubeStop, cubeStop, cubeTransform_cubeTransform σ (gdl_isPredictable_stop hτ),
    cubeTransform_cubeTransform _ hσ]
  simp only [mul_comm]

/-- The transform commutes with conditional expectations (stop at the constant time `k`). -/
theorem cubeTransform_condAvg (hσ : IsPredictable σ) (k : ℕ) (f : (Fin N → Bool) → X) :
    cubeTransform σ (condAvg k f) = condAvg k (cubeTransform σ f) := by
  have hc : ∀ u : (Fin N → Bool) → X, cubeStop (fun _ => k) u = condAvg k u := fun u => by
    funext ε
    rw [cubeStop_apply (fun _ _ _ _ _ => Iff.rfl)]
    rcases le_total N k with h | h
    · rw [min_eq_left h, cbt_condAvg_of_le le_rfl, cbt_condAvg_of_le h]
    · rw [min_eq_right h]
  rw [← hc, ← hc, cubeTransform_cubeStop hσ fun _ _ _ _ _ => Iff.rfl]

end Stopping

section GoodLambda

/-! ### Lemma 3.5.14: the good-λ inequality -/

theorem gdl_runningMax_congr {u : ℕ → (Fin N → Bool) → ℝ} (hu : IsAdapted u) {n : ℕ}
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < n → ε j = ε' j) :
    runningMax u n ε = runningMax u n ε' :=
  Finset.sup'_congr _ rfl fun k hk => hu k ε ε' fun j hj =>
    h j (hj.trans_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {σ : Fin N → (Fin N → Bool) → ℝ}

omit [NormedSpace ℝ X] in
/-- The first pointwise fact in the proof of HNVW, Lemma 3.5.14 (p. 231): if `‖u_j‖ ≤ a` and
`‖u_{j+1} − u_j‖ ≤ a` at all times `j < τ`, then `‖u_{n ∧ τ} − u_{m ∧ τ}‖ ≤ 3 a` for `m ≤ n`: the
difference vanishes if `τ ≤ m`, and otherwise `‖u_m‖ ≤ a` and
`‖u_{n ∧ τ}‖ ≤ ‖u_{(n ∧ τ) − 1}‖ + ‖u_{n ∧ τ} − u_{(n ∧ τ) − 1}‖ ≤ 2 a` (or `n ∧ τ = 0 = m`). -/
private theorem gdl_norm_stop_sub_le {u : ℕ → X} {a : ℝ} (ha : 0 ≤ a) {τ : ℕ}
    (hu : ∀ j < τ, ‖u j‖ ≤ a) (hd : ∀ j < τ, ‖u (j + 1) - u j‖ ≤ a) {m n : ℕ} (hmn : m ≤ n) :
    ‖u (min n τ) - u (min m τ)‖ ≤ 3 * a := by
  rcases le_or_gt τ m with hm | hm
  · rw [min_eq_right hm, min_eq_right (hm.trans hmn), sub_self, norm_zero]
    linarith
  rw [min_eq_left hm.le]
  rcases Nat.eq_zero_or_pos (min n τ) with h0 | h0
  · have hm0 : m = 0 := by omega
    rw [h0, hm0, sub_self, norm_zero]
    linarith
  · obtain ⟨e, he⟩ : ∃ e, min n τ = e + 1 := ⟨min n τ - 1, by omega⟩
    have heτ : e < τ := by omega
    rw [he]
    calc ‖u (e + 1) - u m‖ ≤ ‖u (e + 1)‖ + ‖u m‖ := norm_sub_le _ _
      _ ≤ (‖u e‖ + ‖u (e + 1) - u e‖) + ‖u m‖ := by
          gcongr
          exact norm_le_insert' _ _
      _ ≤ (a + a) + a := by
          gcongr
          · exact hu e heτ
          · exact hd e heτ
          · exact hu m hm
      _ = 3 * a := by ring

omit [NormedSpace ℝ X] in
/-- `‖g_ρ‖ ≤ λ + a` at the first time `ρ` with `‖g_ρ‖ > λ`, if the increments of `g` up to `ρ` and
the initial value have norm at most `a`: `g_ρ = g_{ρ−1} + dg_ρ` if `ρ > 0`, and at `ρ = 0`, where
`g_{ρ−1}` has no meaning, the initial value is bounded by `a`. -/
private theorem gdl_norm_first_le {u : ℕ → X} {a t : ℝ} (ht : 0 ≤ t) {ρ : ℕ}
    (hu : ∀ j < ρ, ‖u j‖ ≤ t) (h0 : ‖u 0‖ ≤ a) (hd : ∀ j < ρ, ‖u (j + 1) - u j‖ ≤ a) :
    ‖u ρ‖ ≤ t + a := by
  cases ρ with
  | zero => linarith
  | succ m =>
    have h1 := hu m (Nat.lt_succ_self m)
    have h2 := hd m (Nat.lt_succ_self m)
    linarith [norm_le_insert' (u (m + 1)) (u m)]

/-- **HNVW, Lemma 3.5.14** (p. 230–231), the good-λ inequality: if the transform `T` by predictable
signs satisfies (3.55) with parameters `α`, `η`, then for `θ > 1`,
`δ ≤ (θ − 1) / (3 α + 1)` and `λ = t > 0`,
`P (T* f > θ λ, f* ∨ w* ≤ δ λ) ≤ η P (T* f > λ)`,
where `w_k` is a majorant of `‖f_{k+1} − f_k‖` depending only on the first `k` signs (the book's
`w_{k+1}`) and `‖v‖_∞ = 1` for the sequence `v = σ` of the transform.

The proof is the book's. With `g = T f`, the stopping times are `ρ = inf {n : ‖g_n‖ > λ}`,
`ν = inf {n : ‖g_n‖ > θ λ}` and `s = inf {n : f*_n ∨ w*_n > δ λ}` (`σ` in the book). The stopped
martingale `h = f^{ν ∧ s}` satisfies `‖ᵏh‖ ≤ 3 δ λ`, and on `{ν < ∞, s = ∞}`, where `ρ ≤ ν`,
`‖T (^ρ h)‖ = ‖g_ν − g_ρ‖ > θ λ − λ − δ λ ≥ 3 α δ λ`. Apply (3.55) to `h` and the events `{ρ = k}`
and sum over `k`. (The book states the first fact for `^ρ h`; for the sum it is needed for `ᵏh`, at
all points, and the argument is the same.)

The source: the bound `‖g_ρ‖ ≤ ‖g_{ρ−1}‖ + ‖dg_ρ‖ ≤ λ + δ λ` has no meaning at the first index
(`ρ = −∞` in the book, with `dg_{−∞} = 0`; `ρ = 0` here), where `g_0 = f_0` need not vanish. There
`‖g_0‖ = ‖f_0‖ ≤ f* ≤ δ λ` on `{s = ∞}` gives the same bound. -/
theorem IsLocalTransformBound.goodLambda {α η θ δ t : ℝ} (hloc : IsLocalTransformBound X σ α η)
    (hσ : IsPredictable σ) (hσ1 : ∀ k ε, σ k ε = 1 ∨ σ k ε = -1) (hα : 0 ≤ α) (hθ : 1 < θ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ (θ - 1) / (3 * α + 1)) (ht : 0 < t) {f : (Fin N → Bool) → X}
    {w : ℕ → (Fin N → Bool) → ℝ} (hw : IsAdapted w)
    (hfw : ∀ k ε, ‖condAvg (k + 1) f ε - condAvg k f ε‖ ≤ w k ε) :
    prob {ε | θ * t < cubeMax (cubeTransform σ f) ε ∧
        max (cubeMax f ε) (runningMax w N ε) ≤ δ * t} ≤
      η * prob {ε | t < cubeMax (cubeTransform σ f) ε} := by
  set g := cubeTransform σ f with hg
  have hδt : 0 ≤ δ * t := mul_nonneg hδ0 ht.le
  -- the martingales `f_n`, `g_n` and the maximal function `f*_n` are adapted
  have hfA : IsAdapted fun k ε => condAvg k f ε := fun n ε ε' h =>
    cbt_condAvg_eq_of_agree n f ε ε' h
  have hgA : IsAdapted fun k ε => condAvg k g ε := fun n ε ε' h =>
    cbt_condAvg_eq_of_agree n g ε ε' h
  have hfn : IsAdapted fun k ε => ‖condAvg k f ε‖ := fun n ε ε' h => congrArg norm (hfA n ε ε' h)
  -- `‖dg_k‖ ≤ ‖df_k‖ ≤ w_k`
  have hgw : ∀ k ε, ‖condAvg (k + 1) g ε - condAvg k g ε‖ ≤ w k ε := by
    intro k ε
    refine le_trans ?_ (hfw k ε)
    rw [hg, condAvg_succ_sub_cubeTransform hσ]
    split_ifs with hk
    · rw [norm_smul]
      rcases hσ1 ⟨k, hk⟩ ε with h | h <;> simp [h]
    · simp
  -- the stopping times `ρ`, `ν`, `s`
  let Pρ : ℕ → Set (Fin N → Bool) := fun n => {ε | t < ‖condAvg n g ε‖}
  let Pν : ℕ → Set (Fin N → Bool) := fun n => {ε | θ * t < ‖condAvg n g ε‖}
  let Ps : ℕ → Set (Fin N → Bool) := fun n =>
    {ε | δ * t < max (runningMax (fun k ε => ‖condAvg k f ε‖) n ε) (runningMax w n ε)}
  have hPs' : ∀ n ε, ε ∈ Ps n ↔
      δ * t < max (runningMax (fun k ε => ‖condAvg k f ε‖) n ε) (runningMax w n ε) :=
    fun _ _ => Iff.rfl
  have hPρ : ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) →
      (ε ∈ Pρ n ↔ ε' ∈ Pρ n) := fun n ε ε' h => by
    simp only [Pρ, Set.mem_ofPred_eq, hgA n ε ε' h]
  have hPν : ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) →
      (ε ∈ Pν n ↔ ε' ∈ Pν n) := fun n ε ε' h => by
    simp only [Pν, Set.mem_ofPred_eq, hgA n ε ε' h]
  have hPs : ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) →
      (ε ∈ Ps n ↔ ε' ∈ Ps n) := fun n ε ε' h => by
    simp only [Ps, Set.mem_ofPred_eq, gdl_runningMax_congr hfn h, gdl_runningMax_congr hw h]
  let ρ := gdlTime Pρ
  let ν := gdlTime Pν
  let s := gdlTime Ps
  let τ : (Fin N → Bool) → ℕ := fun ε => min (ν ε) (s ε)
  have hτ : IsCubeStopping τ := fun k ε ε' hk h => by
    simp only [τ, lt_min_iff]
    exact and_congr (gdl_lt_time_congr hPν hk h) (gdl_lt_time_congr hPs hk h)
  -- before `s`, `f` and the increments of `f` and `g` are at most `δ t`
  have hs : ∀ ε, ∀ j < s ε, ‖condAvg j f ε‖ ≤ δ * t ∧ w j ε ≤ δ * t := by
    intro ε j hj
    have h := not_lt.mp (mt (hPs' j ε).mpr (gdl_notMem_of_lt_time hj))
    have h1 := le_runningMax (fun k ε => ‖condAvg k f ε‖) (le_refl j) ε
    have h2 := le_runningMax w (le_refl j) ε
    exact ⟨h1.trans ((le_max_left _ _).trans h), h2.trans ((le_max_right _ _).trans h)⟩
  -- the stopped martingale `h = f^{ν ∧ s}`; first fact: `‖ᵏh‖ ≤ 3 δ t`
  set h := cubeStop τ f with hh
  have hfact1 : ∀ k ≤ N, ∀ ε, ‖h ε - condAvg k h ε‖ ≤ 3 * (δ * t) := by
    intro k hk ε
    rw [hh, cubeStop_apply hτ, condAvg_cubeStop hτ]
    refine gdl_norm_stop_sub_le (u := fun n => condAvg n f ε) hδt (fun j hj => ?_)
      (fun j hj => ?_) hk
    · exact (hs ε j (hj.trans_le (min_le_right _ _))).1
    · exact (hfw j ε).trans (hs ε j (hj.trans_le (min_le_right _ _))).2
  -- the transform of `ᵏh` is `g_{ν ∧ s} − g_{k ∧ ν ∧ s}`
  have hT : ∀ k ε, cubeTransform σ (h - condAvg k h) ε =
      condAvg (min N (τ ε)) g ε - condAvg (min k (τ ε)) g ε := by
    intro k ε
    rw [cubeTransform_sub, cubeTransform_condAvg hσ, hh, cubeTransform_cubeStop hσ hτ,
      Pi.sub_apply, cubeStop_apply hτ, condAvg_cubeStop hτ]
  set E := {ε | θ * t < cubeMax g ε ∧ max (cubeMax f ε) (runningMax w N ε) ≤ δ * t} with hE
  -- on `E`, `ρ ≤ ν < ∞` and `s = ∞`
  have hEν : ∀ ε ∈ E, ν ε ≤ N := fun ε hε => gdl_time_le_iff.mpr (gdl_lt_runningMax_iff.mp hε.1)
  have hEs : ∀ ε ∈ E, N < s ε := by
    intro ε hε
    refine (gdl_lt_time_iff le_rfl).mpr fun j hj =>
      (not_congr (hPs' j ε)).mpr (not_lt.mpr (max_le ?_ ?_))
    · exact gdl_runningMax_le fun k _ =>
        (norm_condAvg_le_cubeMax f k ε).trans ((le_max_left _ _).trans hε.2)
    · exact gdl_runningMax_le fun k hk =>
        (le_runningMax w (hk.trans hj) ε).trans ((le_max_right _ _).trans hε.2)
  have hρν : ∀ ε ∈ E, ρ ε ≤ ν ε := by
    intro ε hε
    refine gdl_time_le_of_mem ?_
    have h1 : θ * t < ‖condAvg (ν ε) g ε‖ := gdl_mem_time (hEν ε hε)
    change t < ‖condAvg (ν ε) g ε‖
    nlinarith
  -- second fact: `‖T (ᵏh)‖ > 3 α δ t` on `E ∩ {ρ = k}`
  have hfact2 : ∀ k, E ∩ {ε | ρ ε = k} ⊆
      {ε | ρ ε = k} ∩ {ε | α * (3 * (δ * t)) < ‖cubeTransform σ (h - condAvg k h) ε‖} := by
    rintro k ε ⟨hε, rfl⟩
    refine ⟨rfl, ?_⟩
    have hτε : τ ε = ν ε := min_eq_left ((hEν ε hε).trans (hEs ε hε).le)
    change α * (3 * (δ * t)) < ‖cubeTransform σ (h - condAvg (ρ ε) h) ε‖
    rw [hT, hτε, min_eq_right (hEν ε hε), min_eq_left (hρν ε hε)]
    have hgν : θ * t < ‖condAvg (ν ε) g ε‖ := gdl_mem_time (hEν ε hε)
    have hgρ : ‖condAvg (ρ ε) g ε‖ ≤ t + δ * t := by
      have hρN : ρ ε ≤ N := (hρν ε hε).trans (hEν ε hε)
      refine gdl_norm_first_le (u := fun n => condAvg n g ε) ht.le
        (fun j hj => not_lt.mp (gdl_notMem_of_lt_time hj)) ?_ fun j hj => ?_
      · rw [hg, condAvg_zero_cubeTransform hσ]
        exact (hs ε 0 ((Nat.zero_le N).trans_lt (hEs ε hε))).1
      · exact (hgw j ε).trans (hs ε j ((hj.trans_le hρN).trans (hEs ε hε))).2
    have hδ' : δ * (3 * α + 1) ≤ θ - 1 := (le_div_iff₀ (by positivity)).mp hδ
    have h3 := norm_sub_norm_le (condAvg (ν ε) g ε) (condAvg (ρ ε) g ε)
    nlinarith
  -- sum over the events `{ρ = k}`
  have hρle : ∀ ε, ρ ε ≤ N ↔ ε ∈ {ε | t < cubeMax g ε} := fun ε =>
    ⟨fun hε => gdl_lt_runningMax_iff.mpr (gdl_time_le_iff.mp hε),
      fun hε => gdl_time_le_iff.mpr (gdl_lt_runningMax_iff.mp hε)⟩
  calc prob E = ∑ k ∈ Finset.range (N + 1), prob (E ∩ {ε | ρ ε = k}) :=
        gdl_prob_eq_sum fun ε hε => (hρν ε hε).trans (hEν ε hε)
    _ ≤ ∑ k ∈ Finset.range (N + 1), η * prob ({ε | t < cubeMax g ε} ∩ {ε | ρ ε = k}) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hset : {ε | t < cubeMax g ε} ∩ {ε | ρ ε = k} = {ε | ρ ε = k} :=
          Set.inter_eq_right.mpr fun ε hε => (hρle ε).mp (le_of_eq_of_le hε hkN)
        rw [hset]
        exact (gdl_prob_mono (hfact2 k)).trans (hloc k {ε | ρ ε = k} h (3 * (δ * t))
          (fun ε ε' hεε' => gdl_time_eq_congr hPρ hkN hεε') (hfact1 k hkN))
    _ = η * prob {ε | t < cubeMax g ε} := by
        rw [← Finset.mul_sum, ← gdl_prob_eq_sum fun ε hε => (hρle ε).mpr hε]

end GoodLambda

end BanachProbability
