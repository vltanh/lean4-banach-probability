module

public import BanachProbability.SignCube.LpSeminorm

/-!
# Paley–Walsh martingales on the sign cube

On the sign cube `Fin N → Bool` with the filtration `ℱ_k = σ (ε₀, …, ε_{k−1})`:

* `IsPredictable ξ`: the `k`-th term of a family `ξ` depends only on the signs `ε_j`, `j < k`;
* `IsAdapted M`: `M n` depends only on the signs `ε_j`, `j < n`;
* `paleyWalsh ξ n = Σ_{k<n} ε_k ξ_k`, the Paley–Walsh martingale of a predictable family `ξ`;
* `condAvg k f`: the conditional expectation `E [f | ℱ_k]`, the average of `f` over the signs
  `ε_j`, `j ≥ k`;
* `IsCubeMartingale M`: an adapted process with `E [M (n + 1) | ℱ_n] = M n`.

Every martingale on the cube is a Paley–Walsh martingale started at its constant initial value
(`exists_paleyWalsh_of_isCubeMartingale`), and its jumps `‖ξ_k‖` are predictable
(`norm_paleyWalsh_succ_sub`).
-/

@[expose] public section

namespace BanachProbability.SignCube

variable {N : ℕ} {E : Type*}

/-- A family `ξ k` of functions of the signs is predictable: `ξ k` depends only on the signs
`ε j` with `j < k`. -/
def IsPredictable (ξ : Fin N → (Fin N → Bool) → E) : Prop :=
  ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) → ξ k ε = ξ k ε'

/-- A process `M n` on the signs is adapted: `M n` depends only on the signs `ε j` with
`j < n`. -/
def IsAdapted (M : ℕ → (Fin N → Bool) → E) : Prop :=
  ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) → M n ε = M n ε'

/-- The sign vector that agrees with `ε` on the coordinates `j < k` and with `ε'` on the others. -/
def splice (k : ℕ) (ε ε' : Fin N → Bool) : Fin N → Bool :=
  fun j => if j.val < k then ε j else ε' j

/-- The truncation `ε ↦ (ε₀, …, ε_{k−1}, false, …, false)`. -/
def trunc (k : ℕ) (ε : Fin N → Bool) : Fin N → Bool :=
  splice k ε fun _ => false

private theorem splice_zero (ε ε' : Fin N → Bool) : splice 0 ε ε' = ε' := by
  funext j
  simp [splice]

/-- Splicing at `k` then at `l ≥ k` is splicing at `k` a spliced vector. -/
private theorem splice_splice_of_le {k l : ℕ} (h : k ≤ l) (ε ε' ε'' : Fin N → Bool) :
    splice l (splice k ε ε') ε'' = splice k ε (splice l ε' ε'') := by
  funext j
  simp only [splice]
  split_ifs <;> first | rfl | omega

private theorem splice_splice_self (l : ℕ) (a b : Fin N → Bool) :
    splice l (splice l a b) (splice l b a) = a := by
  funext j
  simp only [splice]
  split_ifs <;> rfl

/-- The reindexing lemma for `splice`: `(ε', ε'') ↦ (splice l ε' ε'', splice l ε'' ε')` is a
bijection of pairs of sign vectors, so
`Σ_{ε'} Σ_{ε''} g (splice l ε' ε'') = Σ_{ε'} Σ_{ε''} g ε'`. -/
private theorem sum_sum_splice {M : Type*} [AddCommMonoid M] (l : ℕ) (g : (Fin N → Bool) → M) :
    ∑ ε' : Fin N → Bool, ∑ ε'' : Fin N → Bool, g (splice l ε' ε'') =
      ∑ ε' : Fin N → Bool, ∑ _ε'' : Fin N → Bool, g ε' := by
  let e : (Fin N → Bool) × (Fin N → Bool) ≃ (Fin N → Bool) × (Fin N → Bool) :=
    { toFun := fun x => (splice l x.1 x.2, splice l x.2 x.1)
      invFun := fun x => (splice l x.1 x.2, splice l x.2 x.1)
      left_inv := fun x => Prod.ext (splice_splice_self l x.1 x.2) (splice_splice_self l x.2 x.1)
      right_inv := fun x =>
        Prod.ext (splice_splice_self l x.1 x.2) (splice_splice_self l x.2 x.1) }
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Equiv.sum_comp e (fun x => g x.1)

/-- Two sign vectors agreeing on the coordinates `j < k` and on `k` agree on `j < k + 1`. -/
private theorem agree_succ {k : Fin N} {a b : Fin N → Bool}
    (hlt : ∀ j : Fin N, j.val < k.val → a j = b j) (hk : a k = b k) :
    ∀ j : Fin N, j.val < k.val + 1 → a j = b j := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · exact hlt j hj
  · rw [show j = k from Fin.ext hj]
    exact hk

section Module

variable [AddCommGroup E] [Module ℝ E]

private theorem sum_const_cube (c : E) : ∑ _ε : Fin N → Bool, c = (2 : ℝ) ^ N • c := by
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  simp

/-- A sum that changes sign under the flip of one coordinate vanishes. -/
private theorem sum_eq_zero_of_flip (k : Fin N) {g : (Fin N → Bool) → E}
    (hg : ∀ ε, g (SignCube.flip k ε) = -g ε) : ∑ ε, g ε = 0 := by
  have h : ∑ ε, g ε = -∑ ε, g ε := by
    conv_lhs => rw [← Equiv.sum_comp (flip_involutive k).toPerm g]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ε _ => hg ε
  have h2 : (2 : ℝ) • ∑ ε, g ε = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  rw [← inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0) (∑ ε, g ε), h2, smul_zero]

/-- The Paley–Walsh martingale `n ↦ Σ_{k < n} ε_k ξ_k` of a family `ξ` (predictable in the
applications), started at `0`, at time `n`. -/
noncomputable def paleyWalsh (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) : E :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n), coin (ε k) • ξ k ε

/-- The conditional expectation `E [f | ℱ_k]` on the sign cube: the average of `f` over the signs
`ε_j` with `j ≥ k`, the signs `ε_j`, `j < k`, being fixed. -/
noncomputable def condAvg (k : ℕ) (f : (Fin N → Bool) → E) (ε : Fin N → Bool) : E :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ ε', f (splice k ε ε')

/-- A martingale on the sign cube for the filtration `ℱ_n = σ (ε₀, …, ε_{n−1})`. -/
def IsCubeMartingale (M : ℕ → (Fin N → Bool) → E) : Prop :=
  IsAdapted M ∧ ∀ n, condAvg n (M (n + 1)) = M n

@[simp] theorem paleyWalsh_zero (ξ : Fin N → (Fin N → Bool) → E) (ε : Fin N → Bool) :
    paleyWalsh ξ 0 ε = 0 := by
  simp [paleyWalsh]

theorem paleyWalsh_succ (ξ : Fin N → (Fin N → Bool) → E) (k : ℕ) (ε : Fin N → Bool) :
    paleyWalsh ξ (k + 1) ε =
      paleyWalsh ξ k ε + if h : k < N then coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε else 0 := by
  unfold paleyWalsh
  split_ifs with h
  · rw [show Finset.univ.filter (fun j : Fin N => j.val < k + 1) =
        insert ⟨k, h⟩ (Finset.univ.filter (fun j : Fin N => j.val < k)) from ?_,
      Finset.sum_insert (by simp)]
    · abel
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
  · rw [add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem paleyWalsh_of_le (ξ : Fin N → (Fin N → Bool) → E) {n : ℕ} (hn : N ≤ n)
    (ε : Fin N → Bool) : paleyWalsh ξ n ε = ∑ k, coin (ε k) • ξ k ε := by
  simp only [paleyWalsh]
  rw [Finset.filter_true_of_mem fun k _ => lt_of_lt_of_le k.isLt hn]

theorem paleyWalsh_add (ξ ζ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    paleyWalsh (fun k ε => ξ k ε + ζ k ε) n ε = paleyWalsh ξ n ε + paleyWalsh ζ n ε := by
  simp only [paleyWalsh, smul_add, Finset.sum_add_distrib]

theorem paleyWalsh_smul (c : ℝ) (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    paleyWalsh (fun k ε => c • ξ k ε) n ε = c • paleyWalsh ξ n ε := by
  simp only [paleyWalsh, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- The image of a Paley–Walsh martingale under a linear map. -/
theorem map_paleyWalsh {F : Type*} [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F)
    (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    T (paleyWalsh ξ n ε) = paleyWalsh (fun k ε => T (ξ k ε)) n ε := by
  simp only [paleyWalsh, map_sum, map_smul]

set_option linter.unusedSectionVars false in
theorem IsPredictable.add {ξ ζ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    (hζ : IsPredictable ζ) : IsPredictable fun k ε => ξ k ε + ζ k ε := by
  intro k ε ε' h
  dsimp only
  rw [hξ k ε ε' h, hζ k ε ε' h]

theorem IsPredictable.smul {σ : Fin N → (Fin N → Bool) → ℝ} {ξ : Fin N → (Fin N → Bool) → E}
    (hσ : IsPredictable σ) (hξ : IsPredictable ξ) : IsPredictable fun k ε => σ k ε • ξ k ε := by
  intro k ε ε' h
  dsimp only
  rw [hσ k ε ε' h, hξ k ε ε' h]

/-- The `n`-th value of a Paley–Walsh martingale of a predictable family depends only on the signs
`ε_j`, `j < n`. -/
theorem IsPredictable.isAdapted_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E}
    (hξ : IsPredictable ξ) : IsAdapted (paleyWalsh ξ) := by
  intro k ε ε' h
  unfold paleyWalsh
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val < k := (Finset.mem_filter.mp hj).2
  rw [h j hj', hξ j ε ε' fun i hi => h i (lt_trans (Fin.lt_def.mp hi) hj')]

private theorem condAvg_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → (Fin N → Bool) → E)
    (ε : Fin N → Bool) :
    condAvg k (fun ε => ∑ i ∈ s, f i ε) ε = ∑ i ∈ s, condAvg k (f i) ε := by
  simp only [condAvg, ← Finset.smul_sum]
  rw [Finset.sum_comm]

/-- The average over the signs `ε_j`, `j ≥ n`, of `ε_k h`, `k ≥ n`, with `h` depending only on
the signs `ε_j`, `j < k`, vanishes: pair `ε` with its flip at `k`. -/
private theorem condAvg_coin_smul_eq_zero {n : ℕ} {k : Fin N} (hk : n ≤ k.val)
    {h : (Fin N → Bool) → E}
    (hh : ∀ ε ε' : Fin N → Bool, (∀ j, j < k → ε j = ε' j) → h ε = h ε') (ε : Fin N → Bool) :
    condAvg n (fun ε => coin (ε k) • h ε) ε = 0 := by
  simp only [condAvg]
  refine smul_eq_zero_of_right _ (sum_eq_zero_of_flip k fun ε' => ?_)
  have hk' : ¬ k.val < n := by omega
  have h1 : splice n ε (SignCube.flip k ε') k = !(splice n ε ε' k) := by simp [splice, hk']
  have h2 : h (splice n ε (SignCube.flip k ε')) = h (splice n ε ε') := hh _ _ fun j hj => by
    simp only [splice]
    split_ifs
    · rfl
    · exact flip_apply_of_ne (Fin.ne_of_lt hj) ε'
  rw [h1, h2, coin_not, neg_smul]

/-- For `g` depending only on the signs `ε_j`, `j ≤ k`, the average over the signs `ε_j`, `j ≥ k`,
is the average of `g` over the two values of `ε_k`: `2 E [g | ℱ_k] (ε) = g ε + g (flip k ε)`. -/
private theorem two_smul_condAvg_of_succ {k : Fin N} {g : (Fin N → Bool) → E}
    (hg : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k.val + 1 → ε j = ε' j) → g ε = g ε')
    (ε : Fin N → Bool) :
    (2 : ℝ) • condAvg k g ε = g ε + g (SignCube.flip k ε) := by
  have s1 : ∀ η : Fin N → Bool, ∀ j : Fin N, j.val < k.val → splice k ε η j = ε j :=
    fun η j hj => by simp [splice, hj]
  have s2 : ∀ η : Fin N → Bool, splice k ε η k = η k := fun η => by simp [splice]
  have f1 : ∀ j : Fin N, j.val < k.val → splice k ε (SignCube.flip k ε) j = SignCube.flip k ε j :=
    fun j hj => by rw [s1 _ j hj, flip_apply_of_ne (Fin.ne_of_lt hj)]
  have hpair : ∀ ε', g (splice k ε ε') + g (splice k ε (SignCube.flip k ε')) =
      g ε + g (SignCube.flip k ε) := by
    intro ε'
    have f1' : ∀ η : Fin N → Bool, ∀ j : Fin N, j.val < k.val →
        splice k ε η j = SignCube.flip k ε j := fun η j hj => by
      rw [s1 η j hj, flip_apply_of_ne (Fin.ne_of_lt hj)]
    rcases Bool.eq_or_eq_not (ε' k) (ε k) with h | h
    · rw [hg _ _ (agree_succ (s1 ε') ((s2 ε').trans h)),
        hg _ (SignCube.flip k ε) (agree_succ (f1' _) (by rw [s2, flip_apply_self,
          flip_apply_self, h]))]
    · rw [hg _ (SignCube.flip k ε) (agree_succ (f1' ε') (by rw [s2, h, flip_apply_self])),
        hg _ ε (agree_succ (s1 _) (by rw [s2, flip_apply_self, h, Bool.not_not])), add_comm]
  have hsum : (2 : ℝ) • ∑ ε', g (splice k ε ε') = (2 : ℝ) ^ N • (g ε + g (SignCube.flip k ε)) := by
    calc (2 : ℝ) • ∑ ε', g (splice k ε ε')
        = ∑ ε', g (splice k ε ε') + ∑ ε', g (splice k ε (SignCube.flip k ε')) := by
          rw [two_smul]
          congr 1
          exact (Equiv.sum_comp (flip_involutive k).toPerm (fun ε' => g (splice k ε ε'))).symm
      _ = ∑ _ε' : Fin N → Bool, (g ε + g (SignCube.flip k ε)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ε' _ => hpair ε'
      _ = _ := sum_const_cube _
  simp only [condAvg]
  rw [smul_comm, hsum, inv_smul_smul₀ (by positivity)]

/-- The tower property for the cube conditional expectation. -/
theorem condAvg_condAvg {k l : ℕ} (h : k ≤ l) (f : (Fin N → Bool) → E) :
    condAvg k (condAvg l f) = condAvg k f := by
  funext ε
  have h1 : ∀ ε', condAvg l f (splice k ε ε') =
      ((2 : ℝ) ^ N)⁻¹ • ∑ ε'', (fun η => f (splice k ε η)) (splice l ε' ε'') := by
    intro ε'
    simp only [condAvg, splice_splice_of_le h]
  change ((2 : ℝ) ^ N)⁻¹ • ∑ ε', condAvg l f (splice k ε ε') =
    ((2 : ℝ) ^ N)⁻¹ • ∑ ε', f (splice k ε ε')
  simp_rw [h1]
  rw [← Finset.smul_sum, sum_sum_splice l (fun η => f (splice k ε η))]
  simp_rw [sum_const_cube]
  rw [← Finset.smul_sum, inv_smul_smul₀ (by positivity)]

/-- An `ℱ_k`-measurable function is its own conditional expectation. -/
theorem condAvg_of_isAdapted {k : ℕ} {f : (Fin N → Bool) → E}
    (hf : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε') :
    condAvg k f = f := by
  funext ε
  simp only [condAvg]
  rw [Finset.sum_congr rfl fun ε' _ => hf (splice k ε ε') ε fun j hj => by simp [splice, hj],
    sum_const_cube, inv_smul_smul₀ (by positivity)]

/-- The conditional expectation `E [· | ℱ_0]` is the plain average. -/
theorem condAvg_zero_real (f : (Fin N → Bool) → ℝ) (ε : Fin N → Bool) :
    condAvg 0 f ε = avg f := by
  simp only [condAvg, avg, splice_zero, smul_eq_mul]
  rw [inv_mul_eq_div]

/-- A Paley–Walsh martingale of a predictable family is a martingale:
`E [M_m | ℱ_n] = M_{min n m}`. -/
theorem condAvg_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ) (n m : ℕ) :
    condAvg n (paleyWalsh ξ m) = paleyWalsh ξ (min n m) := by
  funext ε
  have hF : Finset.univ.filter (fun k : Fin N => k.val < min n m) =
      (Finset.univ.filter (fun k : Fin N => k.val < m)).filter (fun k : Fin N => k.val < n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_min_iff]
    exact and_comm
  unfold paleyWalsh
  rw [condAvg_sum, hF, Finset.sum_filter (s := Finset.univ.filter fun k : Fin N => k.val < m)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · -- `j < n`: the term is `ℱ_n`-measurable
    refine congrFun (condAvg_of_isAdapted fun ε ε' h => ?_) ε
    rw [h k hk, hξ k ε ε' fun j hj => h j (lt_trans (Fin.lt_def.mp hj) hk)]
  · -- `j ≥ n`: the term averages to `0` over the sign `ε_j`
    exact condAvg_coin_smul_eq_zero (not_lt.mp hk) (hξ k) ε

theorem IsPredictable.isCubeMartingale_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E}
    (hξ : IsPredictable ξ) : IsCubeMartingale (paleyWalsh ξ) := by
  refine ⟨hξ.isAdapted_paleyWalsh, fun n => ?_⟩
  rw [condAvg_paleyWalsh hξ, min_eq_left (Nat.le_succ n)]

/-- Every martingale on the sign cube is a Paley–Walsh martingale started at its (constant)
initial value: `M n = M 0 + Σ_{k<n} ε_k ξ_k` with `ξ_k = ε_k (M (k + 1) − M k)` predictable. -/
theorem exists_paleyWalsh_of_isCubeMartingale {M : ℕ → (Fin N → Bool) → E}
    (hM : IsCubeMartingale M) :
    ∃ ξ : Fin N → (Fin N → Bool) → E, IsPredictable ξ ∧
      ∀ n ε, M n ε = M 0 ε + paleyWalsh ξ n ε := by
  obtain ⟨hA, hC⟩ := hM
  refine ⟨fun k ε => coin (ε k) • (M (k.val + 1) ε - M k.val ε), ?_, ?_⟩
  · -- `ξ` is predictable: `M (k + 1) − M k` is `ε_k` times a function of `ε_j`, `j < k`
    intro k ε ε' h
    dsimp only
    have hMk : M k.val ε' = M k.val ε := hA k.val ε' ε fun j hj => (h j hj).symm
    rcases Bool.eq_or_eq_not (ε' k) (ε k) with hk | hk
    · rw [hk, hMk, hA (k.val + 1) ε' ε (agree_succ (fun j hj => (h j hj).symm) hk)]
    · have h2 := two_smul_condAvg_of_succ (g := M (k.val + 1)) (hA (k.val + 1)) ε
      rw [hC k.val, two_smul] at h2
      have hflip : M (k.val + 1) ε' = M (k.val + 1) (SignCube.flip k ε) :=
        hA _ _ _ (agree_succ (fun j hj => by
          rw [flip_apply_of_ne (Fin.ne_of_lt hj)]
          exact (h j hj).symm) (by rw [hk, flip_apply_self]))
      have hd : M (k.val + 1) (SignCube.flip k ε) - M k.val ε =
          -(M (k.val + 1) ε - M k.val ε) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm]
      rw [hk, coin_not, hMk, hflip, hd, neg_smul, smul_neg, neg_neg]
  · intro n ε
    induction n with
    | zero => simp
    | succ n ih =>
      rw [paleyWalsh_succ]
      split_ifs with hn
      · simp only [smul_smul, coin_mul_self, one_smul]
        rw [← add_assoc, ← ih, add_sub_cancel]
      · -- for `n ≥ N`, `E [· | ℱ_n]` is the identity, so `M (n + 1) = M n`
        have hid : condAvg n (M (n + 1)) = M (n + 1) := condAvg_of_isAdapted fun ε ε' h => by
          rw [show ε = ε' from funext fun j => h j (lt_of_lt_of_le j.isLt (not_lt.mp hn))]
        rw [add_zero, ← ih, ← hC n, hid]

set_option linter.unusedSectionVars false in
/-- The family `ξ` cut off where a predictable event fails: if the event `A k` depends only on the
signs `ε_j`, `j < k`, then `k ↦ 1_{A k} ξ_k` is predictable. -/
theorem IsPredictable.indicator {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    {A : Fin N → Set (Fin N → Bool)}
    (hA : ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) → (ε ∈ A k ↔ ε' ∈ A k)) :
    IsPredictable fun k ε => (A k).indicator (ξ k) ε := by
  intro k ε ε' h
  dsimp only
  by_cases hε : ε ∈ A k
  · rw [Set.indicator_of_mem hε, Set.indicator_of_mem ((hA k ε ε' h).mp hε), hξ k ε ε' h]
  · rw [Set.indicator_of_notMem hε, Set.indicator_of_notMem fun h' => hε ((hA k ε ε' h).mpr h')]

end Module

section Normed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jumps of a Paley–Walsh martingale are predictable: `‖M_{k+1} − M_k‖ = ‖ξ_k‖`. -/
theorem norm_paleyWalsh_succ_sub (ξ : Fin N → (Fin N → Bool) → E) (k : Fin N)
    (ε : Fin N → Bool) :
    ‖paleyWalsh ξ (k.val + 1) ε - paleyWalsh ξ k.val ε‖ = ‖ξ k ε‖ := by
  rw [paleyWalsh_succ, dite_eq_left k.isLt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_coin, one_mul]

/-- The norm of a conditional expectation is at most the conditional expectation of the norm
(the triangle inequality for the average). -/
theorem norm_condAvg_le (k : ℕ) (f : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    ‖condAvg k f ε‖ ≤ condAvg k (fun ε => ‖f ε‖) ε := by
  simp only [condAvg, smul_eq_mul]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end Normed

end BanachProbability.SignCube
