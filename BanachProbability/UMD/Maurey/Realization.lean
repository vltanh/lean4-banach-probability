module

public import BanachProbability.UMD.Maurey.FinitePaths

/-!
# Finite models with dyadic transitions are Paley–Walsh martingales

The realization step of Maurey's theorem (Pisier, *Martingales in Banach spaces* (2016), §5.6;
HNVW I, Theorem 4.2.5): a finite model whose transition probabilities are dyadic rationals with
denominator `2^m` (`HasDyadicTransitions`) is the image of a Paley–Walsh martingale on a sign cube
under a measure-preserving map. Each step `k → k + 1` of the filtration is split into a block of
`m` coin flips, whose `2^m` outcomes are partitioned into groups of sizes `j` (the numerators of
the transition probabilities); the intermediate values are the conditional expectations within
the block, so the process on the cube is a Paley–Walsh martingale whose values at the ends of the
blocks are those of `Y`, and the signs `σ_{k+1}`, constant on each block, are predictable. The
`L^p` norms of the martingale and of its transform are therefore those of the finite model
(`exists_paleyWalsh_realization`).

The construction (Pisier, Lemma 8.30 (i), (ii), and the blocking argument in the proof of
Theorem 8.32) uses the cube of `m (n + 1)` signs, in blocks of `m`: block `0` chooses the atom of
`ℱ_0`, and block `k + 1` the atom of `ℱ_{k+1}` inside the current atom of `ℱ_k`, each atom `A'`
of positive mass inside `A` getting `2^m μ (A') / μ (A)` of the `2^m` outcomes; the sign vector
`ε` is sent to a point `ω (ε)` of positive mass of the atom of `ℱ_n` reached. At the end of
block `k`, the cube conditional expectation of `G ∘ ω` is `E [G | ℱ_k] ∘ ω` for every
`ℱ_n`-measurable `G`. The theorem holds for multipliers `φ` with values in any set `A ∋ 1` of
scalars of an `RCLike` field (`exists_paleyWalsh_realization_gen`): the multipliers on the cube
are `1` on block `0` and `φ_{k+1} ∘ ω` on block `k + 1`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

open SignCube

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ### Atoms -/

section Atoms

variable {Ω : Type*}

private theorem rlz_mem_atom_comm {m : MeasurableSpace Ω} {x y : Ω} :
    y ∈ atom m x ↔ x ∈ atom m y :=
  ⟨fun h s hs => (h s hs).symm, fun h s hs => (h s hs).symm⟩

private theorem rlz_atom_eq_of_mem {m : MeasurableSpace Ω} {x y : Ω} (h : y ∈ atom m x) :
    atom m y = atom m x := by
  ext z
  exact ⟨fun hz s hs => (h s hs).trans (hz s hs), fun hz s hs => (h s hs).symm.trans (hz s hs)⟩

private theorem rlz_atom_mono {m m' : MeasurableSpace Ω} (h : m ≤ m') (x : Ω) :
    atom m' x ⊆ atom m x :=
  fun _ hy s hs => hy s (h s hs)

private theorem rlz_atom_bot (x : Ω) : atom ⊥ x = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl <;> simp

/-- A function measurable for `m` is constant on the atoms of `m`. -/
private theorem rlz_eq_of_mem_atom {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.MetrizableSpace E] {m : MeasurableSpace Ω} {G : Ω → E}
    (hG : StronglyMeasurable[m] G) {x y : Ω} (h : y ∈ atom m x) : G y = G x :=
  (h _ (hG.measurableSet_eq_fun stronglyMeasurable_const)).mp (rfl : G x = G x)

variable {mΩ : MeasurableSpace Ω}

/-- Almost-everywhere equal functions agree at the points of positive mass. -/
private theorem rlz_apply_of_ae_eq {β : Type*} {μ : Measure Ω} {f g : Ω → β} (h : f =ᵐ[μ] g)
    {x : Ω} (hx : μ {x} ≠ 0) : f x = g x := by
  by_contra hne
  exact hx (measure_mono_null (Set.singleton_subset_iff.mpr hne) (ae_iff.mp h))

private theorem rlz_measureReal_atom_pos {μ : Measure Ω} [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) {x : Ω} (hx : μ {x} ≠ 0) : 0 < μ.real (atom m x) :=
  (ENNReal.toReal_pos hx (measure_ne_top μ _)).trans_le
    (measureReal_mono (Set.singleton_subset_iff.mpr (mem_atom_self m x)))

variable [DiscreteMeasurableSpace Ω]

private theorem rlz_le (m : MeasurableSpace Ω) : m ≤ mΩ :=
  fun s _ => @MeasurableSet.of_discrete Ω mΩ _ s

variable [Fintype Ω]

private theorem rlz_sum_indicator_measureReal (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) :
    ∑ y, S.indicator (fun y => μ.real {y}) y = μ.real S := by
  classical
  have h := Finset.sum_indicator_subset (fun y => μ.real {y}) (Finset.subset_univ S.toFinset)
  rw [Set.coe_toFinset, sum_measureReal_singleton, Set.coe_toFinset] at h
  exact h

end Atoms

/-! ### One block: the transition law inside an atom

Inside the atom `A` of `x` for `a`, the atoms `B ⊆ A` for `b ≥ a` of positive mass get
`2^m μ (B) / μ (A)` of the `2^m` outcomes of a block of `m` signs (an integer when the transition
probabilities are dyadic), each group of outcomes leading to a chosen point of positive mass of
its atom (Pisier, Lemma 8.30 (i)). -/

section Step

variable {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω]
  [Nonempty Ω] (μ : Measure Ω)

/-- A point of positive mass in the atom of `z` for `b` (any point if there is none); it depends
only on the atom. -/
private noncomputable def rlzRep (b : MeasurableSpace Ω) (z : Ω) : Ω :=
  Classical.epsilon fun y => y ∈ atom b z ∧ μ {y} ≠ 0

open Classical in
/-- The number of the `2^m` outcomes of a block that lead from the atom `A` of `x` for `a` to the
point `z`: `2^m μ (B) / μ (A)` if `z` is the chosen point of its atom `B` for `b`, of positive
mass and inside `A`, and `0` otherwise. -/
private noncomputable def rlzWt (a b : MeasurableSpace Ω) (m : ℕ) (x z : Ω) : ℕ :=
  if z ∈ atom a x ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0 then
    ⌊2 ^ m * μ.real (atom b z) / μ.real (atom a x)⌋₊
  else 0

open Classical in
/-- A block of `m` signs realizing the transition law from the atom of `x` for `a` to the atoms
for `b`: a map whose fibres have the sizes `rlzWt` (when these sum to `2^m`). -/
private noncomputable def rlzStep (a b : MeasurableSpace Ω) (m : ℕ) (x : Ω) :
    (Fin m → Bool) → Ω :=
  if h : ∃ f : (Fin m → Bool) → Ω, ∀ z, (Finset.univ.filter fun η => f η = z).card =
      rlzWt μ a b m x z then h.choose else fun _ => x

variable {μ}

omit [Fintype Ω] [DiscreteMeasurableSpace Ω] in
private theorem rlzRep_spec (b : MeasurableSpace Ω) {y : Ω} (hy : μ {y} ≠ 0) :
    rlzRep μ b y ∈ atom b y ∧ μ {rlzRep μ b y} ≠ 0 :=
  Classical.epsilon_spec (p := fun y' => y' ∈ atom b y ∧ μ {y'} ≠ 0) ⟨y, mem_atom_self b y, hy⟩

omit [Fintype Ω] [DiscreteMeasurableSpace Ω] in
private theorem rlzRep_congr (b : MeasurableSpace Ω) {y z : Ω} (h : z ∈ atom b y) :
    rlzRep μ b z = rlzRep μ b y := by
  unfold rlzRep
  rw [rlz_atom_eq_of_mem h]

omit [Fintype Ω] [DiscreteMeasurableSpace Ω] in
private theorem rlzWt_cast {a b : MeasurableSpace Ω} {m : ℕ} {x z : Ω}
    (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z))
    (hx : μ.real (atom a x) ≠ 0) (hz : z ∈ atom a x ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0) :
    (rlzWt μ a b m x z : ℝ) = 2 ^ m * μ.real (atom b z) / μ.real (atom a x) := by
  obtain ⟨i, hi⟩ := hdy z
  have h1 : 2 ^ m * μ.real (atom b z) / μ.real (atom a x) = i := by
    rw [hi, rlz_atom_eq_of_mem hz.1]
    field_simp
  rw [rlzWt, ite_eq_left hz, h1, Nat.floor_natCast]

/-- The weights reproduce the conditional law: for `G` constant on the atoms for `b`,
`Σ_z w (z) G (z) = 2^m μ (A)⁻¹ Σ_{y ∈ A} μ {y} G (y)`; each point `y` of positive mass is
counted once, through the chosen point of its atom. -/
private theorem rlz_sum_wt_smul [IsFiniteMeasure μ] {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b : MeasurableSpace Ω} (hab : a ≤ b) {m : ℕ} {x : Ω} (hx : μ.real (atom a x) ≠ 0)
    (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z))
    {G : Ω → E} (hG : ∀ y z, z ∈ atom b y → G z = G y) :
    ∑ z, (rlzWt μ a b m x z : ℝ) • G z =
      (2 ^ m / μ.real (atom a x)) • ∑ y, (atom a x).indicator (fun y => μ.real {y} • G y) y := by
  classical
  set A := atom a x with hA
  set F : Ω → E := fun y => μ.real {y} • G y with hF
  have hterm : ∀ z, (rlzWt μ a b m x z : ℝ) • G z = (2 ^ m / μ.real A) •
      ∑ y, if z ∈ A ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0 then (atom b z).indicator F y else 0 := by
    intro z
    by_cases hz : z ∈ A ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0
    · simp only [ite_eq_left hz]
      have hsum : ∑ y, (atom b z).indicator F y = μ.real (atom b z) • G z := by
        rw [← rlz_sum_indicator_measureReal μ (atom b z), Finset.sum_smul]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : y ∈ atom b z
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          simp only [hF, hG z y hy]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_smul]
      rw [rlzWt_cast hdy hx hz, hsum, smul_smul]
      congr 1
      ring
    · simp only [ite_eq_right hz, Finset.sum_const_zero, smul_zero]
      rw [rlzWt, ite_eq_right hz, Nat.cast_zero, zero_smul]
  have hcount : ∀ y, (∑ z, if z ∈ A ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0 then
      (atom b z).indicator F y else 0) = A.indicator F y := by
    intro y
    by_cases hy : μ {y} = 0
    · have hFy : F y = 0 := by simp [hF, measureReal_def, hy]
      refine (Finset.sum_eq_zero fun z _ => ?_).trans (by simp [Set.indicator_apply, hFy])
      split_ifs <;> simp [Set.indicator_apply, hFy]
    obtain ⟨hr, hr0⟩ := rlzRep_spec b hy
    set r := rlzRep μ b y with hrdef
    rw [Finset.sum_eq_single r]
    · by_cases hyA : y ∈ A
      · have hrA : r ∈ A := by
          rw [hA, ← rlz_atom_eq_of_mem hyA]
          exact rlz_atom_mono hab y hr
        have hrr : rlzRep μ b r = r := rlzRep_congr b hr
        rw [ite_eq_left ⟨hrA, hrr, hr0⟩, Set.indicator_of_mem (rlz_mem_atom_comm.mp hr),
          Set.indicator_of_mem hyA]
      · rw [Set.indicator_of_notMem hyA]
        split_ifs with h
        · refine (hyA ?_).elim
          rw [hA, ← rlz_atom_eq_of_mem h.1]
          exact rlz_atom_mono hab r (rlz_mem_atom_comm.mp hr)
        · rfl
    · intro z _ hzr
      split_ifs with h
      · rw [Set.indicator_of_notMem]
        intro hyz
        exact hzr (h.2.1.symm.trans ((rlzRep_congr b hyz).symm.trans hrdef.symm))
      · rfl
    · intro h
      exact (h (Finset.mem_univ r)).elim
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.smul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun y _ => hcount y]

private theorem rlz_sum_wt [IsFiniteMeasure μ] {a b : MeasurableSpace Ω} (hab : a ≤ b) {m : ℕ}
    {x : Ω} (hx : μ {x} ≠ 0)
    (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z)) :
    ∑ z, rlzWt μ a b m x z = Fintype.card (Fin m → Bool) := by
  have hpA := rlz_measureReal_atom_pos a hx
  have h := rlz_sum_wt_smul hab hpA.ne' hdy (G := fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  simp only [smul_eq_mul, mul_one] at h
  rw [rlz_sum_indicator_measureReal, div_mul_cancel₀ _ hpA.ne'] at h
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact_mod_cast h

omit [Fintype Ω] [DiscreteMeasurableSpace Ω] [Nonempty Ω] in
open Classical in
/-- A finite set `T` can be partitioned into groups of prescribed sizes `w s` summing to `#T`. -/
private theorem rlz_exists_fiber {T S : Type*} [Fintype T] [Fintype S] (w : S → ℕ)
    (hw : ∑ s, w s = Fintype.card T) :
    ∃ f : T → S, ∀ s, (Finset.univ.filter fun t => f t = s).card = w s := by
  let e : T ≃ Σ s, Fin (w s) := Fintype.equivOfCardEq (by simp [Fintype.card_sigma, hw])
  refine ⟨fun t => (e t).1, fun s => ?_⟩
  rw [Finset.card_equiv e (t := Finset.univ.filter fun σ : Σ s, Fin (w s) => σ.1 = s)
    (by simp), Finset.card_filter, Fintype.sum_sigma]
  simp [apply_ite Finset.card]

open Classical in
private theorem rlzStep_card [IsFiniteMeasure μ] {a b : MeasurableSpace Ω} (hab : a ≤ b)
    {m : ℕ} {x : Ω} (hx : μ {x} ≠ 0)
    (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z)) (z : Ω) :
    (Finset.univ.filter fun η => rlzStep μ a b m x η = z).card = rlzWt μ a b m x z := by
  have h : ∃ f : (Fin m → Bool) → Ω, ∀ z, (Finset.univ.filter fun η => f η = z).card =
      rlzWt μ a b m x z := rlz_exists_fiber _ (rlz_sum_wt hab hx hdy)
  rw [rlzStep, dite_eq_left h]
  exact h.choose_spec z

/-- Every outcome of the block leads to a point of positive mass of the atom of `x`. -/
private theorem rlzStep_mem [IsFiniteMeasure μ] {a b : MeasurableSpace Ω} (hab : a ≤ b)
    {m : ℕ} {x : Ω} (hx : μ {x} ≠ 0)
    (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z))
    (η : Fin m → Bool) : rlzStep μ a b m x η ∈ atom a x ∧ μ {rlzStep μ a b m x η} ≠ 0 := by
  classical
  set z := rlzStep μ a b m x η with hz
  have h1 : 0 < rlzWt μ a b m x z := by
    rw [← rlzStep_card hab hx hdy z]
    exact Finset.card_pos.mpr ⟨η, by simp [z]⟩
  by_contra hne
  have h2 : ¬ (z ∈ atom a x ∧ rlzRep μ b z = z ∧ μ {z} ≠ 0) := fun h => hne ⟨h.1, h.2.2⟩
  rw [rlzWt, ite_eq_right h2] at h1
  exact lt_irrefl 0 h1

/-- **The block realizes the conditional law**: the average over the block of a function
measurable for `b` is its conditional expectation given `a` at `x`. -/
private theorem rlzStep_avg [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : MeasurableSpace Ω} (hab : a ≤ b) {m : ℕ} {x : Ω}
    (hx : μ {x} ≠ 0) (hdy : ∀ z, ∃ i : ℕ, μ.real (atom b z) = i / 2 ^ m * μ.real (atom a z))
    {G : Ω → E} (hG : StronglyMeasurable[b] G) :
    ((2 : ℝ) ^ m)⁻¹ • ∑ η, G (rlzStep μ a b m x η) = μ[G | a] x := by
  classical
  have hpA := rlz_measureReal_atom_pos a hx
  have hfib : ∑ η, G (rlzStep μ a b m x η) = ∑ z, (rlzWt μ a b m x z : ℝ) • G z := by
    rw [← Finset.sum_fiberwise Finset.univ (rlzStep μ a b m x)
      (fun η => G (rlzStep μ a b m x η))]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_congr rfl fun η hη => by rw [(Finset.mem_filter.mp hη).2], Finset.sum_const,
      ← rlzStep_card hab hx hdy z, Nat.cast_smul_eq_nsmul]
  rw [hfib, rlz_sum_wt_smul hab hpA.ne' hdy (fun y z h => rlz_eq_of_mem_atom hG h), smul_smul,
    condExp_eq_atom_average (mΩ := mΩ) (rlz_le a) G hx]
  congr 1
  field_simp

end Step

/-! ### Conditional expectations on a cube split into two blocks of signs -/

section Cube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `E [f | ℱ_l]` depends only on the signs `ε_j`, `j < l`. -/
private theorem rlz_condAvg_congr {N : ℕ} (l : ℕ) (f : (Fin N → Bool) → E)
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < l → ε j = ε' j) :
    condAvg l f ε = condAvg l f ε' := by
  simp only [condAvg]
  congr 1
  refine Finset.sum_congr rfl fun ε'' _ => ?_
  congr 1
  funext j
  simp only [splice]
  split_ifs with hj
  · exact h j hj
  · rfl

/-- On the cube of `L + m` signs, for `l ≤ L`, `E [f | ℱ_l]` is the conditional expectation, on
the cube of the first `L` signs, of the average of `f` over the last `m` signs. -/
private theorem rlz_condAvg_append {L m l : ℕ} (hl : l ≤ L) (f : (Fin (L + m) → Bool) → E)
    (ε : Fin (L + m) → Bool) :
    condAvg l f ε = condAvg l (fun α => ((2 : ℝ) ^ m)⁻¹ • ∑ η, f (Fin.append α η))
      (fun i => ε (Fin.castAdd m i)) := by
  have hsplice : ∀ α η, splice l ε (Fin.append α η) =
      Fin.append (splice l (fun i => ε (Fin.castAdd m i)) α) η := by
    intro α η
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [splice]
    · have : ¬ (L + i.val < l) := by omega
      simp [splice, this]
  have happ : ∀ (α : Fin L → Bool) (η : Fin m → Bool),
      Fin.appendEquiv L m (α, η) = Fin.append α η := fun _ _ => rfl
  simp only [condAvg]
  rw [← (Fin.appendEquiv L m).sum_comp, Fintype.sum_prod_type]
  simp only [happ, hsplice, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun η _ => ?_
  rw [pow_add, mul_inv]

end Cube

/-! ### The realization of a tree with dyadic transitions

For `𝒢 0 ≤ 𝒢 1 ≤ ⋯` and a point `x₀` of positive mass, `rlzMap μ 𝒢 m x₀ k` maps the cube of
`m k` signs to `Ω`: block `j < k` (the signs `m j, …, m j + m − 1`) chooses, inside the current
atom for `𝒢 j`, an atom for `𝒢 (j + 1)` with the transition law (Pisier, Lemma 8.30 (ii)). At the
block ends the cube conditional expectations are the conditional expectations given `𝒢 j`
(`rlzMap_condAvg`). -/

section Map

variable {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω]
  [Nonempty Ω] (μ : Measure Ω)

/-- The realization of the first `k` transitions of the tree of atoms of `𝒢` on the cube of
`m k` signs, started at `x₀`. -/
private noncomputable def rlzMap (𝒢 : ℕ → MeasurableSpace Ω) (m : ℕ) (x₀ : Ω) :
    (k : ℕ) → (Fin (m * k) → Bool) → Ω
  | 0 => fun _ => x₀
  | k + 1 => fun ε => rlzStep μ (𝒢 k) (𝒢 (k + 1)) m
      (rlzMap 𝒢 m x₀ k fun i => ε (Fin.castAdd m i)) fun i => ε (Fin.natAdd (m * k) i)

omit [DiscreteMeasurableSpace Ω] in
private theorem rlzMap_append (𝒢 : ℕ → MeasurableSpace Ω) (m : ℕ) (x₀ : Ω) (k : ℕ)
    (α : Fin (m * k) → Bool) (η : Fin m → Bool) :
    rlzMap μ 𝒢 m x₀ (k + 1) (Fin.append α η : Fin (m * k + m) → Bool) =
      rlzStep μ (𝒢 k) (𝒢 (k + 1)) m (rlzMap μ 𝒢 m x₀ k α) η := by
  simp only [rlzMap, Fin.append_left, Fin.append_right]

variable {μ}

/-- The realization takes values of positive mass. -/
private theorem rlzMap_pos [IsFiniteMeasure μ] {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Monotone 𝒢)
    {m : ℕ} {x₀ : Ω} (hx₀ : μ {x₀} ≠ 0) {K : ℕ}
    (hdy : ∀ j < K, ∀ z, ∃ i : ℕ, μ.real (atom (𝒢 (j + 1)) z) = i / 2 ^ m * μ.real (atom (𝒢 j) z))
    {k : ℕ} (hk : k ≤ K) (ε : Fin (m * k) → Bool) : μ {rlzMap μ 𝒢 m x₀ k ε} ≠ 0 := by
  induction k with
  | zero => exact hx₀
  | succ k ih => exact (rlzStep_mem (h𝒢 k.le_succ) (ih (by omega) _) (hdy k (by omega)) _).2

/-- **The realization at the block ends** (Pisier, Lemma 8.30 (ii)): for `G` measurable for
`𝒢 k` and `j ≤ k`, the cube conditional expectation `E [G ∘ ω | ℱ_{m j}]` is `E [G | 𝒢 j] ∘ ω`. -/
private theorem rlzMap_condAvg [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Monotone 𝒢) {m : ℕ}
    {x₀ : Ω} (hx₀ : μ {x₀} ≠ 0) {K : ℕ}
    (hdy : ∀ j < K, ∀ z, ∃ i : ℕ, μ.real (atom (𝒢 (j + 1)) z) = i / 2 ^ m * μ.real (atom (𝒢 j) z))
    {k : ℕ} (hk : k ≤ K) {G : Ω → E} (hG : StronglyMeasurable[𝒢 k] G) {j : ℕ} (hj : j ≤ k)
    (ε : Fin (m * k) → Bool) :
    condAvg (m * j) (fun ε => G (rlzMap μ 𝒢 m x₀ k ε)) ε = μ[G | 𝒢 j] (rlzMap μ 𝒢 m x₀ k ε) := by
  induction k generalizing G j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [condAvg_of_isAdapted (fun _ _ _ => rfl),
      condExp_of_stronglyMeasurable (rlz_le _) hG Integrable.of_finite]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · -- an earlier block end: average over the last block first
      have hpos := rlzMap_pos h𝒢 hx₀ hdy (k := k) (by omega)
      have hstep : (fun α => ((2 : ℝ) ^ m)⁻¹ • ∑ η,
          G (rlzMap μ 𝒢 m x₀ (k + 1) (Fin.append α η : Fin (m * k + m) → Bool))) =
          fun α => μ[G | 𝒢 k] (rlzMap μ 𝒢 m x₀ k α) := by
        funext α
        simp only [rlzMap_append]
        exact rlzStep_avg (h𝒢 k.le_succ) (hpos α) (hdy k (by omega)) hG
      refine (rlz_condAvg_append (L := m * k) (m := m) (Nat.mul_le_mul_left m (by omega)) _
        ε).trans ?_
      rw [hstep, ih (by omega) stronglyMeasurable_condExp (by omega),
        rlz_apply_of_ae_eq (condExp_condExp_of_le (h𝒢 (by omega : j ≤ k)) (rlz_le _)) (hpos _)]
      -- the point reached after the last block is in the same atom for `𝒢 k`
      exact (rlz_eq_of_mem_atom (stronglyMeasurable_condExp.mono (h𝒢 (by omega : j ≤ k)))
        (rlzStep_mem (h𝒢 k.le_succ) (hpos _) (hdy k (by omega)) _).1).symm
    · obtain rfl : j = k + 1 := by omega
      rw [condAvg_of_isAdapted (fun ε ε' h => by rw [show ε = ε' from funext fun i => h i i.isLt]),
        condExp_of_stronglyMeasurable (rlz_le _) hG Integrable.of_finite]

end Map

/-! ### Blocking: the Paley–Walsh martingale, its multipliers and the norms -/

section Assembly

/-- `L^p` norms on a finite space are finite sums. -/
private theorem rlz_eLpNorm_fintype {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] (f : Ω → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∑ x, μ.real {x} * ‖f x‖ ^ p) ^ (1 / p)) := by
  have hnn : ∀ x, 0 ≤ μ.real {x} * ‖f x‖ ^ p := fun x =>
    mul_nonneg measureReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp.le, lintegral_fintype,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun x _ => hnn x) (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun x _ => hnn x]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, mul_comm]

omit [CompleteSpace X] in
/-- Multipliers equal to `c` on the signs `l ≤ i < l'` multiply the increment of the Paley–Walsh
martingale between `l` and `l'` by `c`. -/
private theorem rlz_paleyWalsh_block {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 X]
    [IsScalarTower ℝ 𝕜 X] {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X)
    (s : Fin N → (Fin N → Bool) → 𝕜) (ε : Fin N → Bool) (c : 𝕜) {l l' : ℕ} (hll' : l ≤ l')
    (hs : ∀ i : Fin N, l ≤ i.val → i.val < l' → s i ε = c) :
    paleyWalsh (fun k ε => s k ε • ξ k ε) l' ε - paleyWalsh (fun k ε => s k ε • ξ k ε) l ε =
      c • (paleyWalsh ξ l' ε - paleyWalsh ξ l ε) := by
  induction l', hll' using Nat.le_induction with
  | base => simp
  | succ l' hll' ih =>
    have ih' := ih fun i h1 h2 => hs i h1 (by omega)
    rw [paleyWalsh_succ, paleyWalsh_succ]
    split_ifs with h
    · rw [hs ⟨l', h⟩ hll' (Nat.lt_succ_self l'), smul_comm (coin _) c, add_sub_right_comm, ih',
        add_sub_right_comm, smul_add]
    · simpa using ih'

/-- The filtration `⊥, ℱ 0, ℱ 1, …`: block `0` of the cube chooses the atom of `ℱ 0`. -/
@[instance_reducible]
private def rlzShift {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) :
    ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | j + 1 => ℱ j

private theorem rlzShift_mono {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) :
    Monotone (rlzShift ℱ) := by
  refine monotone_nat_of_le_succ fun j => ?_
  cases j with
  | zero => exact bot_le
  | succ j => exact ℱ.mono j.le_succ

omit [CompleteSpace X] in
/-- **Blocking** (Pisier, proof of Theorem 8.32): let `ω` map the cube of `m (n + 1)` signs to the
points of positive mass, carry the uniform law to `μ` on `ℱ_n`-measurable functions, and have
the conditional expectations given `ℱ_k` as cube conditional expectations at the block ends
`m (k + 1)`. Then the cube martingale of `Y_n ∘ ω` is a Paley–Walsh martingale with the norms of
`Y_n`, and the multipliers `1` on block `0` and `φ_{k+1} ∘ ω` on block `k + 1` are predictable and
give the norms of the transform `(φ • Y)_n`. -/
private theorem rlz_assemble {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X]
    {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} {A : Set 𝕜}
    (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0) (hA : (1 : 𝕜) ∈ A)
    (hφA : ∀ n ω, φ n ω ∈ A) (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) {n m : ℕ}
    {p : ℝ} (hp : 0 < p) (ω : (Fin (m * (n + 1)) → Bool) → Ω) (hω : ∀ ε, μ {ω ε} ≠ 0)
    (hX : ∀ G : Ω → X, StronglyMeasurable[ℱ n] G → ∀ k ≤ n, ∀ ε,
      condAvg (m * (k + 1)) (fun ε => G (ω ε)) ε = μ[G | ℱ k] (ω ε))
    (h𝕜 : ∀ G : Ω → 𝕜, StronglyMeasurable[ℱ n] G → ∀ k ≤ n, ∀ ε,
      condAvg (m * (k + 1)) (fun ε => G (ω ε)) ε = μ[G | ℱ k] (ω ε))
    (hℝ : ∀ g : Ω → ℝ, StronglyMeasurable[ℱ n] g → avg (fun ε => g (ω ε)) = ∫ x, g x ∂μ) :
    ∃ (ξ : Fin (m * (n + 1)) → (Fin (m * (n + 1)) → Bool) → X)
      (s : Fin (m * (n + 1)) → (Fin (m * (n + 1)) → Bool) → 𝕜),
      IsPredictable ξ ∧ IsPredictable s ∧ (∀ k ε, s k ε ∈ A) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ (m * (n + 1)))) =
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
        (paleyWalsh (fun k ε => s k ε • ξ k ε) (m * (n + 1)))) =
        eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ := by
  have := Fintype.ofFinite Ω
  -- the norms of `ℱ_n`-measurable functions are those of their images on the cube
  have hnorm : ∀ G : Ω → X, StronglyMeasurable[ℱ n] G →
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε => G (ω ε))) =
        eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal p) μ := by
    intro G hG
    have hg : StronglyMeasurable[ℱ n] fun x => ‖G x‖ ^ p :=
      (continuous_norm.rpow_const fun _ => Or.inr hp.le).comp_stronglyMeasurable hG
    rw [rlz_eLpNorm_fintype _ hp, SignCube.lpNorm, hℝ _ hg,
      integral_fintype Integrable.of_finite]
    simp only [norm_norm, smul_eq_mul]
  -- the cube martingale of `Y_n ∘ ω` is `Y_k ∘ ω` at the end of block `k`, and starts at `0`
  set F : (Fin (m * (n + 1)) → Bool) → X := fun ε => Y n (ω ε) with hF
  have hblock : ∀ k ≤ n, ∀ ε, condAvg (m * (k + 1)) F ε = Y k (ω ε) := fun k hk ε =>
    (hX (Y n) (hY.stronglyAdapted n) k hk ε).trans
      (rlz_apply_of_ae_eq (hY.condExp_ae_eq hk) (hω ε))
  have hcm : IsCubeMartingale fun i => condAvg i F :=
    ⟨fun i _ _ h => rlz_condAvg_congr i F h, fun i => condAvg_condAvg i.le_succ F⟩
  obtain ⟨ξ, hξ, hM⟩ := exists_paleyWalsh_of_isCubeMartingale hcm
  have h0 : ∀ ε, condAvg 0 F ε = 0 := by
    intro ε
    have h1 : condAvg (m * (0 + 1)) F = fun _ => 0 :=
      funext fun ε => by rw [hblock 0 (Nat.zero_le n) ε, hY0]
    rw [← condAvg_condAvg (Nat.zero_le (m * (0 + 1))) F, h1]
    simp [condAvg]
  have hPW : ∀ i ε, paleyWalsh ξ i ε = condAvg i F ε := fun i ε => by
    have h := hM i ε
    simp only [h0, zero_add] at h
    exact h.symm
  -- the multipliers: `1` on block `0`, `φ_{k+1} ∘ ω` on block `k + 1`
  set s : Fin (m * (n + 1)) → (Fin (m * (n + 1)) → Bool) → 𝕜 :=
    fun i ε => if i.val < m then 1 else φ (i.val / m) (ω ε) with hsdef
  -- `φ_{c+1} ∘ ω` depends only on the first `m (c + 1)` signs, as `φ_{c+1}` is `ℱ_c`-measurable
  have hφω : ∀ c ≤ n, ∀ ε ε' : Fin (m * (n + 1)) → Bool,
      (∀ j : Fin (m * (n + 1)), j.val < m * (c + 1) → ε j = ε' j) →
        φ (c + 1) (ω ε) = φ (c + 1) (ω ε') := by
    intro c hc ε ε' h
    have key : ∀ ε, condAvg (m * (c + 1)) (fun ε => φ (c + 1) (ω ε)) ε = φ (c + 1) (ω ε) :=
      fun ε => (h𝕜 _ ((hφm c).mono (ℱ.mono hc)) c hc ε).trans
        (congrFun (condExp_of_stronglyMeasurable (rlz_le _) (hφm c) Integrable.of_finite) _)
    rw [← key ε, ← key ε', rlz_condAvg_congr _ _ h]
  have hs : IsPredictable s := by
    intro i ε ε' h
    simp only [hsdef]
    split_ifs with hi
    · rfl
    · have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by
        have := i.isLt
        simp [h0] at this
      obtain ⟨c, hc⟩ : ∃ c, i.val / m = c + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rw [Ne, Nat.div_eq_zero_iff]; omega)
      have hci : m * (c + 1) ≤ i.val := hc ▸ Nat.mul_div_le i.val m
      have hcn : c ≤ n := by
        have h1 : i.val / m < n + 1 :=
          (Nat.div_lt_iff_lt_mul hm).mpr (i.isLt.trans_eq (Nat.mul_comm _ _))
        omega
      rw [hc]
      exact hφω c hcn ε ε' fun j hj => h j (Fin.lt_def.mpr (by omega))
  have hsA : ∀ i ε, s i ε ∈ A := by
    intro i ε
    simp only [hsdef]
    split_ifs
    exacts [hA, hφA _ _]
  -- the transform at the block ends is the transform of `Y`
  have hT : ∀ k ≤ n, ∀ ε, paleyWalsh (fun i ε => s i ε • ξ i ε) (m * (k + 1)) ε =
      martingaleTransform φ Y k (ω ε) := by
    intro k
    induction k with
    | zero =>
      intro _ ε
      have h := rlz_paleyWalsh_block ξ s ε 1 (Nat.zero_le (m * (0 + 1))) fun i _ hi => by
        simp only [hsdef]
        rw [ite_eq_left (by simpa using hi)]
      rw [paleyWalsh_zero, paleyWalsh_zero, sub_zero, sub_zero, one_smul, hPW,
        hblock 0 (Nat.zero_le n), hY0] at h
      rw [h]
      simp [martingaleTransform]
    | succ k ih =>
      intro hk ε
      have hsk : ∀ i : Fin (m * (n + 1)), m * (k + 1) ≤ i.val → i.val < m * (k + 1 + 1) →
          s i ε = φ (k + 1) (ω ε) := by
        intro i h1 h2
        have hmk : m ≤ m * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        have hi : ¬ i.val < m := by omega
        have hdiv : i.val / m = k + 1 :=
          Nat.div_eq_of_lt_le ((Nat.mul_comm _ _).trans_le h1) (h2.trans_eq (Nat.mul_comm _ _))
        simp only [hsdef]
        rw [ite_eq_right hi, hdiv]
      have h := rlz_paleyWalsh_block ξ s ε (φ (k + 1) (ω ε))
        (Nat.mul_le_mul_left m (Nat.le_succ (k + 1))) hsk
      rw [sub_eq_iff_eq_add, ih (by omega), hPW, hPW, hblock (k + 1) hk, hblock k (by omega)] at h
      rw [h]
      simp only [martingaleTransform, Finset.sum_range_succ]
      abel
  -- the transform is `ℱ_n`-measurable
  have hmT : StronglyMeasurable[ℱ n] (martingaleTransform φ Y n) := by
    change StronglyMeasurable[ℱ n]
      (fun ω => ∑ k ∈ Finset.range n, φ (k + 1) ω • (Y (k + 1) ω - Y k ω))
    refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
    have hk' : k + 1 ≤ n := Finset.mem_range.mp hk
    exact ((hφm k).mono (ℱ.mono (by omega))).smul
      (((hY.stronglyAdapted (k + 1)).mono (ℱ.mono hk')).sub
        ((hY.stronglyAdapted k).mono (ℱ.mono (by omega))))
  refine ⟨ξ, s, hξ, hs, hsA, ?_, ?_⟩
  · have : paleyWalsh ξ (m * (n + 1)) = fun ε => Y n (ω ε) :=
      funext fun ε => (hPW _ ε).trans (hblock n le_rfl ε)
    rw [this, hnorm _ (hY.stronglyAdapted n)]
  · have : paleyWalsh (fun i ε => s i ε • ξ i ε) (m * (n + 1)) =
        fun ε => martingaleTransform φ Y n (ω ε) :=
      funext fun ε => hT n le_rfl ε
    rw [this, hnorm _ hmT]

end Assembly

/-- **Blocked realization, general multipliers**: a finite model with dyadic transition
probabilities up to time `n` is realized by a Paley–Walsh martingale on a sign cube, with
predictable multipliers taking their values in the set `A ∋ 1` of the values of `φ`, with the same
`L^p` norms of the martingale at time `n` and of its transform by `φ`. -/
theorem exists_paleyWalsh_realization_gen {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 X]
    [IsScalarTower ℝ 𝕜 X] {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} {φ : ℕ → Ω → 𝕜} {A : Set 𝕜} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    (hA : (1 : 𝕜) ∈ A) (hφA : ∀ n ω, φ n ω ∈ A)
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) {n : ℕ} (hdy : HasDyadicTransitions μ ℱ n)
    {p : ℝ} (hp : 0 < p) :
    ∃ (M : ℕ) (ξ : Fin M → (Fin M → Bool) → X) (s : Fin M → (Fin M → Bool) → 𝕜),
      IsPredictable ξ ∧ IsPredictable s ∧ (∀ k ε, s k ε ∈ A) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ M)) =
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => s k ε • ξ k ε) M)) =
        eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ := by
  have := Fintype.ofFinite Ω
  obtain ⟨m, hdy0, hdy⟩ := hdy
  obtain ⟨x₀, hx₀⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    have h1 : μ (↑(Finset.univ : Finset Ω)) = 0 := by
      rw [← sum_measure_singleton]
      exact Finset.sum_eq_zero fun x _ => h x
    rw [Finset.coe_univ, measure_univ] at h1
    exact one_ne_zero h1
  have : Nonempty Ω := ⟨x₀⟩
  -- the transition probabilities of `⊥, ℱ 0, ℱ 1, …, ℱ n` are dyadic
  have hdy' : ∀ j < n + 1, ∀ z, ∃ i : ℕ,
      μ.real (atom (rlzShift ℱ (j + 1)) z) = i / 2 ^ m * μ.real (atom (rlzShift ℱ j) z) := by
    intro j hj z
    cases j with
    | zero =>
      obtain ⟨i, hi⟩ := hdy0 z
      refine ⟨i, ?_⟩
      rw [show rlzShift ℱ 0 = ⊥ from rfl, rlz_atom_bot, probReal_univ, mul_one]
      exact hi
    | succ k => exact hdy k (by omega) z
  have hmono := rlzShift_mono ℱ
  refine ⟨m * (n + 1), rlz_assemble hY hY0 hA hφA hφm hp (rlzMap μ (rlzShift ℱ) m x₀ (n + 1))
    (rlzMap_pos hmono hx₀ hdy' le_rfl)
    (fun G hG k hk ε => rlzMap_condAvg hmono hx₀ hdy' le_rfl hG (by omega) ε)
    (fun G hG k hk ε => rlzMap_condAvg hmono hx₀ hdy' le_rfl hG (by omega) ε) fun g hg => ?_⟩
  -- the plain average is the conditional expectation given `⊥`
  have h := rlzMap_condAvg hmono hx₀ hdy' le_rfl hg (Nat.zero_le _) (fun _ => false)
  rw [show rlzShift ℱ 0 = ⊥ from rfl, condExp_bot, Nat.mul_zero, condAvg_zero_real] at h
  exact h

/-- **Blocked realization**: a finite model with dyadic transition probabilities up to time `n` is
realized by a Paley–Walsh martingale with predictable signs on a sign cube, with the same `L^p`
norms of the martingale at time `n` and of its transform. -/
theorem exists_paleyWalsh_realization {Ω : Type} [Finite Ω] {mΩ : MeasurableSpace Ω}
    [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → X} {σ : ℕ → Ω → ℝ} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    (hσ : ∀ n ω, σ n ω = 1 ∨ σ n ω = -1) (hσm : ∀ k, StronglyMeasurable[ℱ k] (σ (k + 1)))
    {n : ℕ} (hdy : HasDyadicTransitions μ ℱ n) {p : ℝ} (hp : 0 < p) :
    ∃ (M : ℕ) (ξ : Fin M → (Fin M → Bool) → X) (s : Fin M → (Fin M → Bool) → ℝ),
      IsPredictable ξ ∧ IsPredictable s ∧ (∀ k ε, s k ε = 1 ∨ s k ε = -1) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ M)) =
        eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => s k ε • ξ k ε) M)) =
        eLpNorm (fun ω => ‖martingaleTransform σ Y n ω‖) (ENNReal.ofReal p) μ := by
  obtain ⟨M, ξ, s, hξ, hs, hsA, h1, h2⟩ := exists_paleyWalsh_realization_gen (𝕜 := ℝ)
    (A := {1, -1}) hY hY0 (by simp) (fun n ω => by simpa using hσ n ω) hσm hdy hp
  exact ⟨M, ξ, s, hξ, hs, fun k ε => by simpa using hsA k ε, h1, h2⟩

end BanachProbability
