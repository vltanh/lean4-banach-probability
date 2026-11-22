module

public import BanachProbability.UMD.ConvexHull
public import BanachProbability.UMD.Maurey.StepApprox

/-!
# Deterministic and predictable multipliers

Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach Spaces I* (2016), define the UMD
constant `β_{p,X}` with *deterministic* multipliers: for all scalars `|ε_n| = 1`,
`‖Σ_{n ≤ N} ε_n df_n‖_{L^p} ≤ β ‖Σ_{n ≤ N} df_n‖_{L^p}` (Definition 4.2.1, p. 281; here
`IsDeterministicUMDBound 𝕜 X p β`). Their Theorem 4.2.25 (Burkholder, p. 300–301) says that the same
constant bounds the transforms by all *predictable* multipliers of modulus at most one. This file
follows its proof:

* Lemma 3.6.18 (p. 257–258, `exists_incremental_filtration`): on a finite probability space, a
  martingale `f` and predictable multipliers `v` with respect to a filtration `ℱ` are samples of a
  martingale `g` and of *constant* multipliers `λ_j` with respect to a filtration `𝒢` that is
  *incremental*, `#𝒢_{j+1}^* = #𝒢_j^* + 1`, where `𝒢_j^*` is the set of the atoms of `𝒢_j`
  (`atoms`). Between `ℱ_k` and `ℱ_{k+1}` one puts `𝒢_{j+1} = σ (𝒢_j, A)`, with `A` any atom of
  `ℱ_{k+1}` that is not an atom of `𝒢_j`, until `ℱ_{k+1}` is reached (`inc_exists_chain`,
  `inc_exists_filtration`), and `g_j = E [f_n | 𝒢_j]`. As `#𝒢_{j+1}^* = #𝒢_j^* + 1`, the atoms of
  `𝒢_j` are atoms of `𝒢_{j+1}`, except one, `B`, that is the union of two atoms of `𝒢_{j+1}`
  (`inc_exists_split`). From `E [dg_{j+1} | 𝒢_j] = 0` it follows that `dg_{j+1}` is supported on
  `B` (`inc_sub_eq_zero`), and `v_{k+1}`, being `ℱ_k`-measurable, is a constant `λ_{j+1}` on `B`;
* the proof of Theorem 4.2.25: constants `|λ_j| ≤ 1` lie in the convex hull of the unimodular
  sequences (Proposition 3.2.14, `convexHull_pi_sphere`), so that the deterministic inequality
  holds for them by the convexity of the norm (`IsDeterministicUMDBound.eLpNorm_le_of_norm_le_one`),
  hence for predictable multipliers on finite probability spaces
  (`IsDeterministicUMDBound.eLpNorm_transform_le_of_finite`), hence on all probability spaces
  (`IsDeterministicUMDBound.eLpNorm_transform_le`) by the approximation of Lemma 3.6.17
  (p. 256–257): the predictable multipliers are first approximated uniformly by finitely-valued
  ones of modulus at most one (`inc_exists_round`), and then the martingale by a martingale on a
  finite probability space (`stp_of_finite_gen`).

Departure from the source: the spaces are probability spaces instead of σ-finite measure spaces,
and the martingales have `f_0 = 0`, as everywhere in this library (`IsUMDBound`). The term `v_0 f_0`
of the transforms of the book vanishes, and with it the step of the proof of Theorem 4.2.25 that
restricts the martingale to the atoms of `𝒢_0`, on which `v_0` is constant.

Consequently the constants `umdConst` and `complexUMDConst` of this library, defined with
predictable signs and predictable unimodular multipliers, are the best constants for deterministic
ones (`isUMDBound_iff_isDeterministicUMDBound`, `isComplexUMDBound_iff_isDeterministicUMDBound`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

/-! ### Atoms and incremental refinements -/

section Atoms

variable {Ω : Type*}

/-- The set `m^*` of the atoms of a σ-algebra `m`. -/
def atoms (m : MeasurableSpace Ω) : Set (Set Ω) := Set.range (atom m)

theorem atom_mem_atoms (m : MeasurableSpace Ω) (ω : Ω) : atom m ω ∈ atoms m := ⟨ω, rfl⟩

/-- The σ-algebra of the sets that do not separate `x` from `y`. -/
private abbrev inc_nonsep (x y : Ω) : MeasurableSpace Ω where
  MeasurableSet' s := x ∈ s ↔ y ∈ s
  measurableSet_empty := Iff.rfl
  measurableSet_compl _ hs := not_congr hs
  measurableSet_iUnion f hf := by
    simp only [Set.mem_iUnion]
    exact exists_congr hf

private theorem inc_mem_atom_iff_le {m : MeasurableSpace Ω} {x y : Ω} :
    y ∈ atom m x ↔ m ≤ inc_nonsep x y :=
  Iff.rfl

/-- The atoms of `σ (m, A)`: two points are in the same atom if they are in the same atom of `m`
and `A` does not separate them. -/
private theorem inc_mem_atom_sup {m : MeasurableSpace Ω} {A : Set Ω} {x y : Ω} :
    y ∈ atom (m ⊔ MeasurableSpace.generateFrom {A}) x ↔ y ∈ atom m x ∧ (x ∈ A ↔ y ∈ A) := by
  rw [inc_mem_atom_iff_le, sup_le_iff, ← inc_mem_atom_iff_le, MeasurableSpace.generateFrom_le_iff,
    Set.singleton_subset_iff]
  exact Iff.rfl

/-- On a finite space a σ-algebra `m` is coarser than `m'` if its atoms are unions of atoms
of `m'`. -/
private theorem inc_le_of_atom_subset [Finite Ω] {m m' : MeasurableSpace Ω}
    (h : ∀ ω, atom m' ω ⊆ atom m ω) : m ≤ m' := by
  intro s hs
  have : s = ⋃ ω ∈ s, atom m' ω := by
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun hy => ⟨y, hy, mem_atom_self m' y⟩, fun ⟨ω, hω, hy⟩ => (h ω hy s hs).1 hω⟩
  rw [this]
  exact Set.Finite.measurableSet_biUnion (Set.toFinite s) fun ω _ => measurableSet_atom m' ω

/-- The atom of `m` that contains a given atom `B` of a finer σ-algebra. -/
private def inc_coarse (m : MeasurableSpace Ω) (B : Set Ω) : Set Ω := ⋃ ω ∈ B, atom m ω

private theorem inc_coarse_atom {m m' : MeasurableSpace Ω} (h : m ≤ m') (ω : Ω) :
    inc_coarse m (atom m' ω) = atom m ω := by
  ext y
  simp only [inc_coarse, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hx, hy⟩
    rwa [fpa_atom_eq_of_mem (fpa_mem_atom_of_le h hx)] at hy
  · exact fun hy => ⟨ω, mem_atom_self m' ω, hy⟩

private theorem inc_image_coarse {m m' : MeasurableSpace Ω} (h : m ≤ m') :
    inc_coarse m '' atoms m' = atoms m := by
  ext B
  constructor
  · rintro ⟨_, ⟨ω, rfl⟩, rfl⟩
    exact ⟨ω, (inc_coarse_atom h ω).symm⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨_, ⟨ω, rfl⟩, inc_coarse_atom h ω⟩

private theorem inc_ncard_atoms_le [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m') :
    (atoms m).ncard ≤ (atoms m').ncard := by
  rw [← inc_image_coarse h]
  exact Set.ncard_image_le (Set.toFinite _)

/-- If `m ≤ m'` and `m'` has one atom more than `m`, then `m` and `m'` share the same atoms,
except that one atom `B` of `m` is the union of two atoms of `m'` (HNVW I, proof of Lemma 3.6.18,
p. 258). -/
theorem inc_exists_split [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m')
    (hcard : (atoms m').ncard = (atoms m).ncard + 1) :
    ∃ B ∈ atoms m, (∀ ω, ω ∉ B → atom m' ω = atom m ω) ∧
      ∃ A₀ ∈ atoms m', ∃ A₁ ∈ atoms m', A₀ ≠ A₁ ∧ B = A₀ ∪ A₁ := by
  -- two atoms `A₀ ≠ A₁` of `m'` are in the same atom of `m`
  have hninj : ¬ Set.InjOn (inc_coarse m) (atoms m') := fun hinj => by
    have := hinj.ncard_image
    rw [inc_image_coarse h] at this
    omega
  simp only [Set.InjOn, not_forall] at hninj
  obtain ⟨A₀, hA₀, A₁, hA₁, hA, hne⟩ := hninj
  -- the map of the atoms of `m'` other than `A₁` to the atoms of `m` is one to one
  have himg : inc_coarse m '' (atoms m' \ {A₁}) = atoms m := by
    refine Set.Subset.antisymm ((Set.image_mono Set.sdiff_subset).trans (inc_image_coarse h).le)
      ?_
    rw [← inc_image_coarse h]
    rintro _ ⟨C, hC, rfl⟩
    by_cases hC1 : C = A₁
    · exact ⟨A₀, ⟨hA₀, hne⟩, by rw [hA, hC1]⟩
    · exact ⟨C, ⟨hC, hC1⟩, rfl⟩
  have hinj : Set.InjOn (inc_coarse m) (atoms m' \ {A₁}) := by
    refine Set.injOn_of_ncard_image_eq ?_ (Set.toFinite _)
    have := Set.ncard_sdiff_singleton_add_one hA₁ (Set.toFinite _)
    rw [himg]
    omega
  obtain ⟨ω₀, rfl⟩ := hA₀
  obtain ⟨ω₁, rfl⟩ := hA₁
  rw [inc_coarse_atom h, inc_coarse_atom h] at hA
  -- so are two points of the same atom of `m` whose atoms in `m'` are not `A₁`
  have key : ∀ x y, y ∈ atom m x → atom m' x ≠ atom m' ω₁ → atom m' y ≠ atom m' ω₁ →
      y ∈ atom m' x := by
    intro x y hy hx1 hy1
    have : atom m' y = atom m' x := hinj ⟨atom_mem_atoms m' y, hy1⟩ ⟨atom_mem_atoms m' x, hx1⟩ (by
      rw [inc_coarse_atom h, inc_coarse_atom h, fpa_atom_eq_of_mem hy])
    rw [← this]
    exact mem_atom_self m' y
  -- an atom of `m'` outside `B` is not `A₁`
  have hout : ∀ x, x ∉ atom m ω₀ → atom m' x ≠ atom m' ω₁ := by
    intro x hx hx1
    refine hx ?_
    rw [hA]
    exact fpa_mem_atom_of_le h (by rw [← hx1]; exact mem_atom_self m' x)
  refine ⟨atom m ω₀, atom_mem_atoms m ω₀, fun ω hω => ?_, atom m' ω₀, atom_mem_atoms m' ω₀,
    atom m' ω₁, atom_mem_atoms m' ω₁, hne, ?_⟩
  · refine Set.Subset.antisymm (fun y hy => fpa_mem_atom_of_le h hy) fun y hy => ?_
    refine key ω y hy (hout ω hω) (hout y fun hy0 => hω ?_)
    rw [← fpa_atom_eq_of_mem hy0, fpa_atom_eq_of_mem hy]
    exact mem_atom_self m ω
  · refine Set.Subset.antisymm (fun y hy => ?_) (Set.union_subset
      (fun y hy => fpa_mem_atom_of_le h hy) fun y hy => ?_)
    · by_cases hy1 : atom m' y = atom m' ω₁
      · exact Or.inr (by rw [← hy1]; exact mem_atom_self m' y)
      · exact Or.inl (key ω₀ y hy hne hy1)
    · rw [hA]
      exact fpa_mem_atom_of_le h hy

/-- Adding to a σ-algebra `m` an atom `A` of a finer σ-algebra that is not an atom of `m` gives a
σ-algebra `σ (m, A)` with one atom more (HNVW I, proof of Lemma 3.6.18, p. 258). -/
private theorem inc_ncard_atoms_sup [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m')
    {A : Set Ω} (hA : A ∈ atoms m') (hA' : A ∉ atoms m) :
    (atoms (m ⊔ MeasurableSpace.generateFrom {A})).ncard = (atoms m).ncard + 1 := by
  obtain ⟨a, rfl⟩ := hA
  set A := atom m' a
  set m₁ := m ⊔ MeasurableSpace.generateFrom {A}
  have hm₁ : m ≤ m₁ := le_sup_left
  have hAB : A ⊆ atom m a := fun y hy => fpa_mem_atom_of_le h hy
  -- the atom of a point of `A` in `m₁` is `A`
  have hin : ∀ x ∈ A, atom m₁ x = A := by
    intro x hx
    have hxa : atom m x = atom m a := fpa_atom_eq_of_mem (hAB hx)
    ext y
    rw [inc_mem_atom_sup, hxa]
    exact ⟨fun hy => hy.2.1 hx, fun hy => ⟨hAB hy, fun _ => hy, fun _ => hx⟩⟩
  -- a point of the atom of `m` containing `A` outside `A`
  obtain ⟨b, hb, hbA⟩ : ∃ b ∈ atom m a, b ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hA' ⟨a, Set.Subset.antisymm hcon hAB⟩
  have hne : ∀ x, x ∉ A → atom m₁ x ≠ A := fun x hx hxA =>
    hx (by rw [← hxA]; exact mem_atom_self m₁ x)
  -- the atoms of `m₁` other than `A` correspond to the atoms of `m`
  have himg : inc_coarse m '' (atoms m₁ \ {A}) = atoms m := by
    refine Set.Subset.antisymm ((Set.image_mono Set.sdiff_subset).trans (inc_image_coarse hm₁).le)
      ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ A
    · refine ⟨atom m₁ b, ⟨atom_mem_atoms m₁ b, hne b hbA⟩, ?_⟩
      rw [inc_coarse_atom hm₁, fpa_atom_eq_of_mem hb, fpa_atom_eq_of_mem (hAB hx)]
    · exact ⟨atom m₁ x, ⟨atom_mem_atoms m₁ x, hne x hx⟩, inc_coarse_atom hm₁ x⟩
  have hinj : Set.InjOn (inc_coarse m) (atoms m₁ \ {A}) := by
    rintro _ ⟨⟨x, rfl⟩, hx⟩ _ ⟨⟨y, rfl⟩, hy⟩ hxy
    rw [inc_coarse_atom hm₁, inc_coarse_atom hm₁] at hxy
    have hx' : x ∉ A := fun hxA => hx (hin x hxA)
    have hy' : y ∉ A := fun hyA => hy (hin y hyA)
    refine (fpa_atom_eq_of_mem (inc_mem_atom_sup.2 ⟨?_, iff_of_false hx' hy'⟩)).symm
    rw [hxy]
    exact mem_atom_self m y
  have hAm₁ : A ∈ atoms m₁ := ⟨a, hin a (mem_atom_self m' a)⟩
  rw [← himg, hinj.ncard_image, Set.ncard_sdiff_singleton_add_one hAm₁ (Set.toFinite _)]

/-- `σ (m, A) ≤ m'` for an atom `A` of `m' ≥ m`. -/
private theorem inc_sup_le [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m') {A : Set Ω}
    (hA : A ∈ atoms m') : m ⊔ MeasurableSpace.generateFrom {A} ≤ m' := by
  obtain ⟨a, rfl⟩ := hA
  refine sup_le h (MeasurableSpace.generateFrom_le fun s hs => ?_)
  rw [Set.mem_singleton_iff.1 hs]
  exact measurableSet_atom m' a

/-- If `m ≤ m'` are different, some atom of `m'` is not an atom of `m`. -/
private theorem inc_exists_atom [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m') (hne : m ≠ m') :
    ∃ A ∈ atoms m', A ∉ atoms m := by
  by_contra hcon
  push Not at hcon
  refine hne (le_antisymm h (inc_le_of_atom_subset fun ω => ?_))
  obtain ⟨x, hx⟩ := hcon _ (atom_mem_atoms m' ω)
  have hω : ω ∈ atom m x := by rw [hx]; exact mem_atom_self m' ω
  rw [fpa_atom_eq_of_mem hω, hx]

/-- The intermediate σ-algebras of HNVW I, proof of Lemma 3.6.18 (p. 258): between `m ≤ m'` there
is a finite chain of σ-algebras, each with one atom more than the preceding one. The recursion is
that of the book: `𝒢_{j+1} = σ (𝒢_j, A)`, with `A` any atom of `m'` that is not an atom of `𝒢_j`,
until `m'` is reached; the number of steps is `#m'^* − #m^*`. -/
private theorem inc_exists_chain [Finite Ω] {m m' : MeasurableSpace Ω} (h : m ≤ m') :
    ∃ (N : ℕ) (H : ℕ → MeasurableSpace Ω), H 0 = m ∧ Monotone H ∧ (∀ j, N ≤ j → H j = m') ∧
      ∀ j < N, (atoms (H (j + 1))).ncard = (atoms (H j)).ncard + 1 := by
  obtain ⟨d, hd⟩ : ∃ d, (atoms m').ncard ≤ (atoms m).ncard + d := ⟨_, Nat.le_add_left _ _⟩
  induction d generalizing m with
  | zero =>
    by_cases hm : m = m'
    · exact ⟨0, fun _ => m, rfl, monotone_const, fun _ _ => hm,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · -- one atom more than `m` is too many
      obtain ⟨A, hA, hA'⟩ := inc_exists_atom h hm
      have h1 := inc_ncard_atoms_sup h hA hA'
      have h2 := inc_ncard_atoms_le (inc_sup_le h hA)
      omega
  | succ d ih =>
    by_cases hm : m = m'
    · exact ⟨0, fun _ => m, rfl, monotone_const, fun _ _ => hm,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · obtain ⟨A, hA, hA'⟩ := inc_exists_atom h hm
      have h1 := inc_ncard_atoms_sup h hA hA'
      obtain ⟨N, H, hH0, hHm, hHN, hHinc⟩ := ih (inc_sup_le h hA) (by omega)
      refine ⟨N + 1, fun j => Nat.casesOn j m H, rfl, monotone_nat_of_le_succ fun j => ?_,
        fun j hj => ?_, fun j hj => ?_⟩
      · cases j with
        | zero => exact le_sup_left.trans_eq hH0.symm
        | succ j => exact hHm (Nat.le_succ j)
      · cases j with
        | zero => omega
        | succ j => exact hHN j (by omega)
      · cases j with
        | zero =>
          change (atoms (H 0)).ncard = _
          rw [hH0]
          exact h1
        | succ j => exact hHinc j (by omega)

/-- The incremental refinement of a filtration `ℱ` up to time `n` (HNVW I, proof of Lemma 3.6.18,
p. 258): an increasing sequence `𝒢` of σ-algebras and increasing indices `τ` with `𝒢_{τ k} = ℱ_k`,
`k ≤ n`, and `#𝒢_{j+1}^* = #𝒢_j^* + 1` for `j < τ n` (so that `τ k = #ℱ_k^* − #ℱ_0^*`). The chains
of `inc_exists_chain` between the `ℱ_k` and `ℱ_{k+1}` are put one after the other. -/
private theorem inc_exists_filtration [Finite Ω] {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (n : ℕ) :
    ∃ (τ : ℕ → ℕ) (G : ℕ → MeasurableSpace Ω), τ 0 = 0 ∧ Monotone τ ∧ Monotone G ∧
      (∀ k ≤ n, G (τ k) = ℱ k) ∧ (∀ j, τ n ≤ j → G j = ℱ n) ∧
      ∀ j < τ n, (atoms (G (j + 1))).ncard = (atoms (G j)).ncard + 1 := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, fun _ => ℱ 0, rfl, monotone_const, monotone_const, fun k hk => ?_,
      fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rw [Nat.le_zero.1 hk]
  | succ n ih =>
    obtain ⟨τ, G, hτ0, hτ, hG, hGτ, hGn, hinc⟩ := ih
    obtain ⟨M, H, hH0, hH, hHM, hHinc⟩ := inc_exists_chain (ℱ.mono n.le_succ)
    set τ' : ℕ → ℕ := fun k => if k ≤ n then τ k else τ n + M with hτ'
    set G' : ℕ → MeasurableSpace Ω := fun j => if j ≤ τ n then G j else H (j - τ n) with hG'
    have hτ'1 : ∀ k ≤ n, τ' k = τ k := fun k hk => by simp [hτ', hk]
    have hτ'2 : τ' (n + 1) = τ n + M := by simp [hτ']
    have hG'1 : ∀ j ≤ τ n, G' j = G j := fun j hj => by simp [hG', hj]
    have hG'2 : ∀ j, τ n ≤ j → G' j = H (j - τ n) := by
      intro j hj
      rcases hj.eq_or_lt with rfl | hj'
      · rw [hG'1 _ le_rfl, hGn _ le_rfl, Nat.sub_self, hH0]
      · simp [hG', hj'.not_ge]
    refine ⟨τ', G', (hτ'1 0 n.zero_le).trans hτ0, monotone_nat_of_le_succ fun k => ?_,
      monotone_nat_of_le_succ fun j => ?_, fun k hk => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rcases lt_trichotomy k n with hk | rfl | hk
      · rw [hτ'1 k hk.le, hτ'1 (k + 1) hk]
        exact hτ k.le_succ
      · rw [hτ'1 k le_rfl, hτ'2]
        exact Nat.le_add_right _ _
      · simp [hτ', hk.not_ge, (hk.trans k.lt_succ_self).not_ge]
    · rcases Nat.lt_or_ge j (τ n) with hj | hj
      · rw [hG'1 j hj.le, hG'1 (j + 1) hj]
        exact hG j.le_succ
      · rw [hG'2 j hj, hG'2 (j + 1) (hj.trans j.le_succ)]
        exact hH (by omega)
    · rcases hk.eq_or_lt with rfl | hk'
      · rw [hτ'2, hG'2 _ (Nat.le_add_right _ _), hHM _ (by omega)]
      · have hk'' : k ≤ n := Nat.lt_succ_iff.1 hk'
        rw [hτ'1 k hk'', hG'1 _ (hτ hk''), hGτ k hk'']
    · rw [hτ'2] at hj
      rw [hG'2 j (by omega), hHM _ (by omega)]
    · rw [hτ'2] at hj
      rcases Nat.lt_or_ge j (τ n) with hj' | hj'
      · rw [hG'1 j hj'.le, hG'1 (j + 1) hj']
        exact hinc j hj'
      · rw [hG'2 j hj', hG'2 (j + 1) (hj'.trans j.le_succ),
          show j + 1 - τ n = j - τ n + 1 by omega]
        exact hHinc _ (by omega)

end Atoms

/-! ### HNVW I, Lemma 3.6.18 -/

section Lemma3618

variable {Ω : Type*} [Finite Ω] {m m' mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X]

/-- The increment `D` of a martingale from a σ-algebra `m` to a finer one `m'` vanishes on the
common atoms of `m` and `m'`, a.e.: `D` is constant on such an atom `C`, and its value is the
average over `C`, which is `E [D | m] = 0` (HNVW I, proof of Lemma 3.6.18, p. 258). -/
private theorem inc_sub_eq_zero {D : Ω → X} (hD : StronglyMeasurable[m'] D)
    (hD0 : μ[D | m] =ᵐ[μ] 0) {ω : Ω} (hω : μ {ω} ≠ 0) (hatom : atom m' ω = atom m ω) : D ω = 0 := by
  classical
  have := Fintype.ofFinite Ω
  have hm : m ≤ mΩ := fun s _ => MeasurableSet.of_discrete
  have h0 : μ[D | m] ω = 0 := by
    rw [Filter.EventuallyEq, ae_iff_of_countable] at hD0
    exact hD0 ω hω
  have hpos : 0 < μ.real (atom m ω) :=
    lt_of_lt_of_le (ENNReal.toReal_pos hω (measure_ne_top μ _))
      (measureReal_mono (Set.singleton_subset_iff.2 (mem_atom_self m ω)))
  rw [condExp_eq_atom_average hm D hω] at h0
  have hconst : ∑ ω', (atom m ω).indicator (fun ω' => μ.real {ω'} • D ω') ω' =
      μ.real (atom m ω) • D ω := by
    rw [fpa_measureReal_eq_sum μ (atom m ω), Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ atom m ω
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        fpa_eq_of_mem_atom hD (by rwa [hatom])]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  rwa [hconst, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at h0

/-- **HNVW I, Lemma 3.6.18** (p. 257–258). On a finite probability space, let `Y` be a martingale
and `φ` predictable multipliers (`φ_{k+1}` is `ℱ_k`-measurable), and let `n ≥ 0`. There are a
filtration `𝒢` that is incremental up to time `N`, `#𝒢_{j+1}^* = #𝒢_j^* + 1` for `j < N`, a
`𝒢`-martingale `g` with `g_0 = Y_0`, constants `λ_j` among the values of `φ` (here `c j`), and
increasing indices `τ`, `τ 0 = 0`, `τ n = N`, such that for `k ≤ n`
`𝒢_{τ k} = ℱ_k`, `g_{τ k} = Y_k` a.e. and
`Σ_{j < τ k} λ_{j+1} (g_{j+1} − g_j) = Σ_{i < k} φ_{i+1} (Y_{i+1} − Y_i)` a.e.

As in the book, `𝒢` is the refinement of `ℱ` by one atom at a time (`inc_exists_filtration`) and
`g_j = E [Y_n | 𝒢_j]` (with `g_0` replaced by its version `Y_0`). For `τ k ≤ j < τ (k + 1)`, one
atom `B` of `𝒢_j` is split in `𝒢_{j+1}` (`inc_exists_split`); the increment `dg_{j+1}` is supported
on `B` (`inc_sub_eq_zero`), on which the `ℱ_k`-measurable `φ_{k+1}` has a constant value
`λ_{j+1}`; and `φ_{k+1} (Y_{k+1} − Y_k) = Σ_{τ k ≤ j < τ (k+1)} φ_{k+1} dg_{j+1}`.

Departure from the source: in the book the transforms have a further term `v_0 f_0`, equal to
`w_0 g_0` with `w_0 = v_0`; as `f_0 = 0` in the applications here, it is left out, and with it the
addendum that `𝒢_0` may be taken trivial for a constant `v_0`. The source has a misprint: the range
of `k` in (iii) is `0, …, n`, not `0, …, N`. -/
theorem exists_incremental_filtration {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 X]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) [Nonempty Ω] {φ : ℕ → Ω → 𝕜}
    (hφ : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    ∃ (N : ℕ) (τ : ℕ → ℕ) (G : Filtration ℕ mΩ) (g : ℕ → Ω → X) (c : ℕ → 𝕜),
      τ 0 = 0 ∧ Monotone τ ∧ τ n = N ∧ (∀ k ≤ n, G (τ k) = ℱ k) ∧
      (∀ j < N, (atoms (G (j + 1))).ncard = (atoms (G j)).ncard + 1) ∧
      Martingale g G μ ∧ g 0 = Y 0 ∧ (∀ k ≤ n, g (τ k) =ᵐ[μ] Y k) ∧
      (∀ j, ∃ k ω, c j = φ (k + 1) ω) ∧
      ∀ k ≤ n, (fun ω => ∑ j ∈ Finset.range (τ k), c (j + 1) • (g (j + 1) ω - g j ω)) =ᵐ[μ]
        martingaleTransform φ Y k := by
  classical
  obtain ⟨τ, G₀, hτ0, hτ, hG₀, hGτ, -, hinc⟩ := inc_exists_filtration ℱ n
  let G : Filtration ℕ mΩ := ⟨G₀, hG₀, fun _ s _ => MeasurableSet.of_discrete⟩
  have hGτ' : ∀ k ≤ n, G (τ k) = ℱ k := hGτ
  have hinc' : ∀ j < τ n, (atoms (G (j + 1))).ncard = (atoms (G j)).ncard + 1 := hinc
  have hG0 : ℱ 0 ≤ G 0 := by rw [← hGτ' 0 n.zero_le, hτ0]
  -- the martingale `g_j = E (Y_n | 𝒢_j)`, with the version `Y_0` of `g_0`
  set f : ℕ → Ω → X := fun j => μ[Y n | G j] with hf
  have hfm : Martingale f G μ := martingale_condExp (Y n) G μ
  set g : ℕ → Ω → X := fun j => f j - (f 0 - Y 0) with hg
  have hgm : Martingale g G μ :=
    hfm.sub (martingale_const_fun G μ
      ((hfm.stronglyAdapted 0).sub ((hY.stronglyAdapted 0).mono hG0))
      ((hfm.integrable 0).sub (hY.integrable 0)))
  have hfτ : ∀ k ≤ n, f (τ k) =ᵐ[μ] Y k := by
    intro k hk
    simp only [hf, hGτ' k hk]
    exact hY.condExp_ae_eq hk
  have hf0 : f 0 =ᵐ[μ] Y 0 := by simpa only [hτ0] using hfτ 0 n.zero_le
  have hgτ : ∀ k ≤ n, g (τ k) =ᵐ[μ] Y k := by
    intro k hk
    filter_upwards [hfτ k hk, hf0] with ω h1 h2
    simp only [hg, Pi.sub_apply, h1, h2, sub_self, sub_zero]
  -- the constants `λ_{j+1}`: the value of `φ_{k+1}` on the atom of `𝒢_j` that is split
  have hc : ∀ j, ∃ a : 𝕜, (∃ k ω, a = φ (k + 1) ω) ∧ ∀ k < n, τ k ≤ j → j < τ (k + 1) →
      (fun ω => φ (k + 1) ω • (g (j + 1) ω - g j ω)) =ᵐ[μ]
        fun ω => a • (g (j + 1) ω - g j ω) := by
    intro j
    by_cases hj : ∃ k < n, τ k ≤ j ∧ j < τ (k + 1)
    · obtain ⟨k, hk, hkj, hjk⟩ := hj
      obtain ⟨B, ⟨ω₀, rfl⟩, hB, -⟩ := inc_exists_split (G.mono j.le_succ)
        (hinc' j (hjk.trans_le (hτ hk)))
      refine ⟨φ (k + 1) ω₀, ⟨k, ω₀, rfl⟩, fun k' hk' hkj' hjk' => ?_⟩
      -- `k` is the only index with `τ k ≤ j < τ (k + 1)`
      obtain rfl : k' = k := by
        rcases lt_trichotomy k' k with h | h | h
        · exact absurd (hτ (show k' + 1 ≤ k from h)) (by omega)
        · exact h
        · exact absurd (hτ (show k + 1 ≤ k' from h)) (by omega)
      have hφB : ∀ ω ∈ atom (G j) ω₀, φ (k' + 1) ω = φ (k' + 1) ω₀ := fun ω hω =>
        fpa_eq_of_mem_atom ((hφ k').mono ((hGτ' k' hk.le).symm.le.trans (G.mono hkj))) hω
      have hD : StronglyMeasurable[G (j + 1)] (g (j + 1) - g j) :=
        (hgm.stronglyAdapted (j + 1)).sub ((hgm.stronglyAdapted j).mono (G.mono j.le_succ))
      have hD0 : μ[g (j + 1) - g j | G j] =ᵐ[μ] 0 := by
        filter_upwards [condExp_sub (hgm.integrable (j + 1)) (hgm.integrable j) (G j),
          hgm.condExp_ae_eq j.le_succ, hgm.condExp_ae_eq (le_refl j)] with ω h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3, sub_self, Pi.zero_apply]
      rw [Filter.EventuallyEq, ae_iff_of_countable]
      intro ω hω
      by_cases hωB : ω ∈ atom (G j) ω₀
      · rw [hφB ω hωB]
      · have := inc_sub_eq_zero hD hD0 hω (hB ω hωB)
        rw [Pi.sub_apply] at this
        rw [this, smul_zero, smul_zero]
    · exact ⟨φ 1 (Classical.arbitrary Ω), ⟨0, _, rfl⟩,
        fun k hk h1 h2 => absurd ⟨k, hk, h1, h2⟩ hj⟩
  choose a hav ha using hc
  refine ⟨τ n, τ, G, g, fun j => a (j - 1), hτ0, hτ, rfl, hGτ', hinc', hgm, ?_, hgτ,
    fun j => hav (j - 1), fun k hk => ?_⟩
  · funext ω
    simp [hg]
  · -- the transforms, by induction on `k`
    induction k with
    | zero => exact Filter.Eventually.of_forall fun ω => by simp [hτ0, martingaleTransform]
    | succ k ih =>
      have hsum : ∀ᵐ ω ∂μ, ∀ j, τ k ≤ j → j < τ (k + 1) →
          φ (k + 1) ω • (g (j + 1) ω - g j ω) = a j • (g (j + 1) ω - g j ω) := by
        rw [ae_all_iff]
        intro j
        by_cases hj : τ k ≤ j ∧ j < τ (k + 1)
        · filter_upwards [ha j k hk hj.1 hj.2] with ω hω _ _ using hω
        · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hj
      filter_upwards [ih (k.le_succ.trans hk), hsum, hgτ k (k.le_succ.trans hk),
        hgτ (k + 1) hk] with ω h1 h2 h3 h4
      have h5 : ∑ j ∈ Finset.Ico (τ k) (τ (k + 1)), a j • (g (j + 1) ω - g j ω) =
          φ (k + 1) ω • (Y (k + 1) ω - Y k ω) := by
        rw [← h3, ← h4, ← Finset.sum_Ico_sub (fun j => g j ω) (hτ k.le_succ), Finset.smul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        exact (h2 j hj.1 hj.2).symm
      simp only [martingaleTransform, Nat.add_sub_cancel] at h1 ⊢
      rw [Finset.sum_range_succ, ← h1, ← h5, Finset.sum_range_add_sum_Ico _ (hτ k.le_succ)]

end Lemma3618

/-! ### HNVW I, Theorem 4.2.25 -/

section Deterministic

variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace 𝕜 X]

/-- `β` is a UMD constant of `X` for *deterministic* multipliers (HNVW I, Definition 4.2.1,
p. 281): for every `X`-valued martingale `Y` with `Y_0 = 0` on a probability space and all scalars
`ε_k ∈ 𝕜` with `|ε_k| = 1`, `‖Σ_{k<n} ε_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. In the book
the martingales are on σ-finite measure spaces, and do not have to start at `0`; but only their
increments enter the inequality, so this is the inequality for `f_n − f_0`. -/
def IsDeterministicUMDBound (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (ε : ℕ → 𝕜),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n, ‖ε n‖ = 1) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, ε (k + 1) • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

variable {𝕜 X}

/-- The cube instance: the martingale `Y_1 = ε_0 x` on the one-sign cube, transformed by `1`,
shows that every UMD constant for deterministic multipliers of a nonzero space is at least `1`. -/
private theorem inc_one_le [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 0 < p) {β : ℝ≥0∞}
    (h : IsDeterministicUMDBound 𝕜 X p β) : 1 ≤ β := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have key := h (Fin 1 → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (SignCube.filtration 1) (fun k => SignCube.paleyWalsh (fun _ _ => x) k) (fun _ => 1)
    (SignCube.martingale_paleyWalsh _ (umdd_isPredictable_const x))
    (fun ω => SignCube.paleyWalsh_zero _ ω) (fun _ => norm_one) 1
  simp only [Finset.sum_range_one, one_smul, zero_add, SignCube.paleyWalsh_zero, sub_zero] at key
  rw [umdd_eLpNorm_norm_uniformOn _ hp,
    umdd_lpNorm_of_norm_eq (norm_nonneg x) (umdd_norm_paleyWalsh_const x) hp] at key
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by simpa using hx
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).mp (by simpa using key)

variable [IsScalarTower ℝ 𝕜 X]

/-- The convexity step of the proof of HNVW I, Theorem 4.2.25 (p. 300–301): deterministic
multipliers `|a_k| ≤ 1` satisfy the same inequality as unimodular ones. The sequences
`(a_1, …, a_n)` that satisfy it form a convex set, by the convexity of the norm; it contains the
unimodular sequences, hence `conv (S_𝕜^n) = B_𝕜^n` (Proposition 3.2.14,
`convexHull_pi_sphere`). -/
theorem IsDeterministicUMDBound.eLpNorm_le_of_norm_le_one {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞}
    (h : IsDeterministicUMDBound 𝕜 X p β) {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ)
    (hY0 : ∀ ω, Y 0 ω = 0) {a : ℕ → 𝕜} (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) :
    eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, a (k + 1) • (Y (k + 1) ω - Y k ω)‖)
        (ENNReal.ofReal p) μ ≤ β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set C := β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ
  -- the transform as a function of the sequence of multipliers
  set T : (Fin n → 𝕜) → Ω → X := fun u ω => ∑ j : Fin n, u j • (Y (j + 1) ω - Y j ω) with hT
  have hTm : ∀ u, AEStronglyMeasurable (T u) μ := fun u =>
    (Finset.stronglyMeasurable_fun_sum _ fun j _ => (stronglyMeasurable_const (b := u j)).smul
      (((hY.stronglyAdapted (j + 1)).mono (ℱ.le _)).sub
        ((hY.stronglyAdapted j).mono (ℱ.le _)))).aestronglyMeasurable
  have hTadd : ∀ (s t : ℝ) (u v : Fin n → 𝕜), T (s • u + t • v) = s • T u + t • T v := by
    intro s t u v
    funext ω
    simp only [hT, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_assoc,
      Finset.smul_sum]
  -- the sequences that satisfy the inequality form a convex set
  have hconv : Convex ℝ {u : Fin n → 𝕜 | eLpNorm (T u) (ENNReal.ofReal p) μ ≤ C} := by
    intro u hu v hv s t hs ht hst
    change eLpNorm (T (s • u + t • v)) (ENNReal.ofReal p) μ ≤ C
    rw [hTadd]
    calc eLpNorm (s • T u + t • T v) (ENNReal.ofReal p) μ
        ≤ ‖s‖ₑ * eLpNorm (T u) (ENNReal.ofReal p) μ +
            ‖t‖ₑ * eLpNorm (T v) (ENNReal.ofReal p) μ := by
          refine (eLpNorm_add_le hp1).trans ?_
          rw [eLpNorm_const_smul, eLpNorm_const_smul]
      _ ≤ ‖s‖ₑ * C + ‖t‖ₑ * C := by
          gcongr
          exacts [hu, hv]
      _ = C := by
          rw [← add_mul, Real.enorm_of_nonneg hs, Real.enorm_of_nonneg ht,
            ← ENNReal.ofReal_add hs ht, hst, ENNReal.ofReal_one, one_mul]
  -- it contains the unimodular sequences
  have hsphere : (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : 𝕜) 1) ⊆
      {u : Fin n → 𝕜 | eLpNorm (T u) (ENNReal.ofReal p) μ ≤ C} := by
    intro u hu
    have hu1 : ∀ j, ‖u j‖ = 1 := by simpa [Set.mem_univ_pi] using hu
    have key := h Ω mΩ μ ℱ Y (fun i => if hi : i - 1 < n then u ⟨i - 1, hi⟩ else 1) hY hY0
      (fun i => by split_ifs <;> simp [hu1]) n
    have e : (fun ω => ∑ k ∈ Finset.range n, (fun i => if hi : i - 1 < n then u ⟨i - 1, hi⟩ else 1)
        (k + 1) • (Y (k + 1) ω - Y k ω)) = T u := by
      funext ω
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun j _ => by simp
    change eLpNorm (T u) (ENNReal.ofReal p) μ ≤ C
    rw [← eLpNorm_norm _ (hTm u), ← e]
    exact key
  -- hence all sequences of modulus at most one
  have hmem := convexHull_min hsphere hconv
  rw [convexHull_pi_sphere] at hmem
  have key : eLpNorm (T fun j => a (j + 1)) (ENNReal.ofReal p) μ ≤ C :=
    hmem (by simpa [Set.mem_univ_pi] using fun j : Fin n => ha (j + 1))
  rw [← eLpNorm_norm _ (hTm _)] at key
  simpa only [hT, Finset.sum_range] using key

/-- **HNVW I, Theorem 4.2.25** (Burkholder, p. 300–301), on finite probability spaces: a UMD bound
for deterministic multipliers bounds the transforms by all predictable multipliers
`‖φ_k‖ ≤ 1`. By Lemma 3.6.18 (`exists_incremental_filtration`) the transform is one by constant
multipliers `|λ_j| ≤ 1` of a martingale with the same last value, with respect to an incremental
filtration. -/
theorem IsDeterministicUMDBound.eLpNorm_transform_le_of_finite [CompleteSpace X] {p : ℝ}
    (hp : 1 ≤ p) {β : ℝ≥0∞} (h : IsDeterministicUMDBound 𝕜 X p β) {Ω : Type} [Finite Ω]
    {mΩ : MeasurableSpace Ω} [DiscreteMeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    {φ : ℕ → Ω → 𝕜} (hφ : ∀ n ω, ‖φ n ω‖ ≤ 1)
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨N, τ, G, g, c, -, -, rfl, -, -, hg, hg0, hgτ, hc, hcτ⟩ :=
    exists_incremental_filtration hY hφm n
  have hc1 : ∀ j, ‖c j‖ ≤ 1 := by
    intro j
    obtain ⟨k, ω, hj⟩ := hc j
    rw [hj]
    exact hφ _ ω
  have key := h.eLpNorm_le_of_norm_le_one hp hg (fun ω => by rw [hg0, hY0]) hc1 (τ n)
  have e1 : (fun ω => ‖∑ k ∈ Finset.range (τ n), c (k + 1) • (g (k + 1) ω - g k ω)‖) =ᵐ[μ]
      fun ω => ‖martingaleTransform φ Y n ω‖ := by
    filter_upwards [hcτ n le_rfl] with ω hω
    rw [hω]
  have e2 : (fun ω => ‖g (τ n) ω‖) =ᵐ[μ] fun ω => ‖Y n ω‖ := by
    filter_upwards [hgτ n le_rfl] with ω hω
    rw [hω]
  rwa [eLpNorm_congr_ae e1, eLpNorm_congr_ae e2] at key

/-- **Rounding multipliers** (HNVW I, proof of Lemma 3.6.17, p. 257: simple multipliers `w_k` with
`‖w_k − v_k‖_∞ < δ` and `‖w_k‖_∞ ≤ ‖v_k‖_∞`): for `δ > 0` there is a measurable map `r` of `𝕜` to
its closed unit ball, with finitely many values, such that `‖z − r z‖ ≤ δ` on the closed unit ball,
the nearest point of a finite `δ`-net. -/
private theorem inc_exists_round (𝕜 : Type*) [RCLike 𝕜] {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : 𝕜 → 𝕜, Measurable r ∧ (Set.range r).Finite ∧ (∀ z, ‖r z‖ ≤ 1) ∧
      ∀ z, ‖z‖ ≤ 1 → ‖z - r z‖ ≤ δ := by
  obtain ⟨t, ht, htfin, hcov⟩ := (isCompact_closedBall (0 : 𝕜) 1).finite_cover_balls hδ
  -- enumerate the net
  obtain ⟨M, e, -, rfl⟩ := htfin.fin_param
  set e' : ℕ → 𝕜 := fun i => if hi : i < M then e ⟨i, hi⟩ else 0 with he'
  have he'1 : ∀ i, ‖e' i‖ ≤ 1 := by
    intro i
    simp only [he']
    split_ifs with hi
    · simpa using ht ⟨⟨i, hi⟩, rfl⟩
    · simp
  refine ⟨SimpleFunc.nearestPt e' M, (SimpleFunc.nearestPt e' M).measurable,
    (SimpleFunc.nearestPt e' M).finite_range, fun z => he'1 _, fun z hz => ?_⟩
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Set.mem_iUnion₂.1 (hcov (by simpa using hz))
  have h1 := SimpleFunc.edist_nearestPt_le e' z (k := i) (N := M) i.2.le
  have h2 : e' i = e i := by simp [he']
  rw [h2, edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h1
  rw [← dist_eq_norm, dist_comm]
  rw [Metric.mem_ball, dist_comm] at hi
  exact h1.trans hi.le

/-- **HNVW I, Theorem 4.2.25** (Burkholder, p. 300–301): a UMD bound for deterministic unimodular
multipliers bounds, with the same constant, the transforms by all predictable multipliers with
`‖φ_k‖ ≤ 1`.

As in the book, by the approximation of Lemma 3.6.17 the case of finite probability spaces
(`IsDeterministicUMDBound.eLpNorm_transform_le_of_finite`) is enough: the multipliers are
approximated uniformly within `δ` by finitely-valued ones of modulus at most one
(`inc_exists_round`), which moves the transform by at most `2 n δ ‖Y_n‖_p`
(`stp_eLpNorm_transform_sub_le`), and for finitely-valued multipliers the martingale is
approximated on finite probability spaces (`stp_of_finite_gen`). If `‖Y_n‖_p = ∞`, the right side is
infinite, as `β ≥ 1` on a nonzero space. -/
theorem IsDeterministicUMDBound.eLpNorm_transform_le {𝕜 : Type} {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [IsScalarTower ℝ 𝕜 X] {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞} (h : IsDeterministicUMDBound 𝕜 X p β)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → X} (hY : Martingale Y ℱ μ) (hY0 : ∀ ω, Y 0 ω = 0)
    {φ : ℕ → Ω → 𝕜} (hφ : ∀ n ω, ‖φ n ω‖ ≤ 1)
    (hφm : ∀ k, StronglyMeasurable[ℱ k] (φ (k + 1))) (n : ℕ) :
    eLpNorm (fun ω => ‖martingaleTransform φ Y n ω‖) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hYnm : AEStronglyMeasurable (Y n) μ :=
    ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable
  -- the corner `‖Y_n‖_p = ∞`
  by_cases hYn : eLpNorm (Y n) (ENNReal.ofReal p) μ = ⊤
  · by_cases hβ : β = 0
    · rcases subsingleton_or_nontrivial X with hX | hX
      · simp [norm_of_subsingleton]
      · exact absurd hβ (zero_lt_one.trans_le (inc_one_le (by linarith) h)).ne'
    · rw [eLpNorm_norm _ hYnm, hYn, ENNReal.mul_top hβ]
      exact le_top
  refine stp_le_mul (fun h0 => stp_eLpNorm_norm_transform_eq_zero hY hp0 h0 φ) fun η hη => ?_
  -- round the multipliers within `δ`, with `2 n δ ‖Y_n‖_p ≤ η`
  obtain ⟨δ, hδ, hδη⟩ := stp_exists_pos_mul_le (C := 2 * n * eLpNorm (Y n) (ENNReal.ofReal p) μ)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)) hYn) hη
  obtain ⟨r, hrm, hrfin, hr1, hr⟩ := inc_exists_round 𝕜 hδ
  set ψ : ℕ → Ω → 𝕜 := fun n ω => r (φ n ω) with hψ
  have hψm : ∀ k, StronglyMeasurable[ℱ k] (ψ (k + 1)) := fun k =>
    (hrm.comp (hφm k).measurable).stronglyMeasurable
  have hψfin : ∀ k, (Set.range (ψ (k + 1))).Finite := fun k =>
    hrfin.subset (Set.range_subset_iff.2 fun ω => ⟨_, rfl⟩)
  -- the bound for the rounded multipliers, by finite models
  have hB : eLpNorm (martingaleTransform ψ Y n) (ENNReal.ofReal p) μ ≤
      β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm _ (stp_aestronglyMeasurable_transform hY hψm n)]
    exact stp_of_finite_gen (A := {z : 𝕜 | ‖z‖ ≤ 1}) hp
      (fun Ω _ mΩ _ μ _ ℱ Y φ hY hY0 hφ hφm n =>
        h.eLpNorm_transform_le_of_finite hp hY hY0 hφ hφm n)
      hY hY0 (fun n ω => hr1 _) hψfin hψm n hYn
  have herr := stp_eLpNorm_transform_sub_le hY hφm hψm (fun n ω => hr _ (hφ n ω)) hp1 n
  have hsplit : martingaleTransform φ Y n = martingaleTransform ψ Y n +
      fun ω => martingaleTransform φ Y n ω - martingaleTransform ψ Y n ω := by
    funext ω
    simp
  rw [eLpNorm_norm _ (stp_aestronglyMeasurable_transform hY hφm n)]
  calc eLpNorm (martingaleTransform φ Y n) (ENNReal.ofReal p) μ
      ≤ eLpNorm (martingaleTransform ψ Y n) (ENNReal.ofReal p) μ +
          eLpNorm (fun ω => martingaleTransform φ Y n ω - martingaleTransform ψ Y n ω)
            (ENNReal.ofReal p) μ :=
        (le_of_eq (congrArg (eLpNorm · (ENNReal.ofReal p) μ) hsplit)).trans (eLpNorm_add_le hp1)
    _ ≤ β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ + ENNReal.ofReal η :=
        add_le_add hB (herr.trans hδη)
    _ ≤ β * (eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ + ENNReal.ofReal η) +
          ENNReal.ofReal η := by
        gcongr
        exact le_self_add

end Deterministic

/-! ### The UMD constants -/

section Constants

/-- The bounds for predictable signs `±1` (`IsUMDBound`) and for deterministic signs (HNVW I,
Definition 4.2.1) are the same, by Theorem 4.2.25. -/
theorem isUMDBound_iff_isDeterministicUMDBound {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞} :
    IsUMDBound X p β ↔ IsDeterministicUMDBound ℝ X p β := by
  constructor
  · intro h Ω mΩ μ _ ℱ Y ε hY hY0 hε n
    exact h Ω mΩ μ ℱ Y (fun n _ => ε n) hY hY0 (fun n _ => eq_or_eq_neg_of_abs_eq (hε n))
      (fun _ => stronglyMeasurable_const) n
  · intro h Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm n
    exact h.eLpNorm_transform_le hp hY hY0
      (fun n ω => by rcases hσ n ω with h1 | h1 <;> simp [h1]) hσm n

/-- The bounds for predictable unimodular complex multipliers (`IsComplexUMDBound`) and for
deterministic ones (HNVW I, Definition 4.2.1) are the same, by Theorem 4.2.25. -/
theorem isComplexUMDBound_iff_isDeterministicUMDBound {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞} :
    IsComplexUMDBound X p β ↔ IsDeterministicUMDBound ℂ X p β := by
  constructor
  · intro h Ω mΩ μ _ ℱ Y ε hY hY0 hε n
    have hYm : ∀ k, StronglyMeasurable (Y k) := fun k => (hY.stronglyAdapted k).mono (ℱ.le k)
    have hT : AEStronglyMeasurable
        (fun ω => ∑ k ∈ Finset.range n, ε (k + 1) • (Y (k + 1) ω - Y k ω)) μ :=
      (Finset.stronglyMeasurable_fun_sum _ fun k _ =>
        (stronglyMeasurable_const (b := ε (k + 1))).smul
          ((hYm (k + 1)).sub (hYm k))).aestronglyMeasurable
    rw [eLpNorm_norm _ hT, eLpNorm_norm _ (hYm n).aestronglyMeasurable]
    exact h Ω mΩ μ ℱ Y (fun n _ => ε n) hY hY0 (fun n _ => hε n)
      (fun _ => stronglyMeasurable_const) n
  · intro h Ω mΩ μ _ ℱ Y c hY hY0 hc hcm n
    have key := h.eLpNorm_transform_le hp hY hY0 (fun n ω => (hc n ω).le) hcm n
    rwa [eLpNorm_norm _ (stp_aestronglyMeasurable_transform hY hcm n),
      eLpNorm_norm _ ((hY.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable] at key

/-- The constant `umdConst`, defined with predictable signs, is the best constant `β_{p,X}` for
deterministic signs (HNVW I, Definition 4.2.1 and Theorem 4.2.25). -/
theorem umdConst_eq_sInf_isDeterministicUMDBound (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) :
    umdConst X p = sInf {β | IsDeterministicUMDBound ℝ X p β} := by
  simp only [umdConst, isUMDBound_iff_isDeterministicUMDBound hp]

/-- The constant `complexUMDConst`, defined with predictable unimodular multipliers, is the best
constant `β_{p,X}` for deterministic ones (HNVW I, Definition 4.2.1 and Theorem 4.2.25). -/
theorem complexUMDConst_eq_sInf_isDeterministicUMDBound (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) :
    complexUMDConst X p = sInf {β | IsDeterministicUMDBound ℂ X p β} := by
  simp only [complexUMDConst, isComplexUMDBound_iff_isDeterministicUMDBound hp]

end Constants

end BanachProbability
