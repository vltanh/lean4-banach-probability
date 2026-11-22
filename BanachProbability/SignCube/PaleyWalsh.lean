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
* `IsCubeMartingale M`: an adapted process with `E [M (n + 1) | ℱ_n] = M n`;
* `IsStoppingTime τ`: the event `{τ ≤ n}` depends only on the signs `ε_j`, `j < n`;
* `transform σ f`: the martingale transform `E [f | ℱ_0] + Σ_k σ_k (E [f | ℱ_{k+1}] − E [f | ℱ_k])`
  of the final value `f`.

Every martingale on the cube is a Paley–Walsh martingale started at its constant initial value
(`exists_paleyWalsh_of_isCubeMartingale`); a Paley–Walsh martingale stopped at a stopping time is
the Paley–Walsh martingale of a predictable family (`paleyWalsh_stopped`), and its jumps
`‖ξ_k‖` are predictable (`norm_paleyWalsh_succ_sub`).
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

/-- A time `τ : (Fin N → Bool) → ℕ` is a stopping time: whether `τ ≤ n` depends only on the signs
`ε j` with `j < n`. -/
def IsStoppingTime (τ : (Fin N → Bool) → ℕ) : Prop :=
  ∀ (n : ℕ) (ε ε' : Fin N → Bool), (∀ j : Fin N, j.val < n → ε j = ε' j) → (τ ε ≤ n ↔ τ ε' ≤ n)

/-- The sign vector that agrees with `ε` on the coordinates `j < k` and with `ε'` on the others. -/
def splice (k : ℕ) (ε ε' : Fin N → Bool) : Fin N → Bool :=
  fun j => if j.val < k then ε j else ε' j

/-- The truncation `ε ↦ (ε₀, …, ε_{k−1}, false, …, false)`. -/
def trunc (k : ℕ) (ε : Fin N → Bool) : Fin N → Bool :=
  splice k ε fun _ => false

section Module

variable [AddCommGroup E] [Module ℝ E]

/-- The Paley–Walsh martingale `n ↦ Σ_{k < n} ε_k ξ_k` of a family `ξ` (predictable in the
applications), started at `0`, at time `n`. -/
noncomputable def paleyWalsh (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) : E :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n), coin (ε k) • ξ k ε

/-- The conditional expectation `E [f | ℱ_k]` on the sign cube: the average of `f` over the signs
`ε_j` with `j ≥ k`, the signs `ε_j`, `j < k`, being fixed. -/
noncomputable def condAvg (k : ℕ) (f : (Fin N → Bool) → E) (ε : Fin N → Bool) : E :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ ε', f (splice k ε ε')

/-- The martingale transform of `f` by a family `σ` of scalars (predictable signs in the
applications): `T_σ f = E [f | ℱ_0] + Σ_k σ_k (E [f | ℱ_{k+1}] − E [f | ℱ_k])`. -/
noncomputable def transform (σ : Fin N → (Fin N → Bool) → ℝ) (f : (Fin N → Bool) → E) :
    (Fin N → Bool) → E :=
  fun ε => condAvg 0 f ε + ∑ k : Fin N, σ k ε • (condAvg (k.val + 1) f ε - condAvg k.val f ε)

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
  sorry

theorem paleyWalsh_smul (c : ℝ) (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    paleyWalsh (fun k ε => c • ξ k ε) n ε = c • paleyWalsh ξ n ε := by
  sorry

/-- The image of a Paley–Walsh martingale under a linear map. -/
theorem map_paleyWalsh {F : Type*} [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F)
    (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    T (paleyWalsh ξ n ε) = paleyWalsh (fun k ε => T (ξ k ε)) n ε := by
  sorry

theorem IsPredictable.add {ξ ζ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    (hζ : IsPredictable ζ) : IsPredictable fun k ε => ξ k ε + ζ k ε := by
  sorry

theorem IsPredictable.smul {σ : Fin N → (Fin N → Bool) → ℝ} {ξ : Fin N → (Fin N → Bool) → E}
    (hσ : IsPredictable σ) (hξ : IsPredictable ξ) : IsPredictable fun k ε => σ k ε • ξ k ε := by
  sorry

/-- The `n`-th value of a Paley–Walsh martingale of a predictable family depends only on the signs
`ε_j`, `j < n`. -/
theorem IsPredictable.isAdapted_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E}
    (hξ : IsPredictable ξ) : IsAdapted (paleyWalsh ξ) := by
  intro k ε ε' h
  unfold paleyWalsh
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val < k := (Finset.mem_filter.mp hj).2
  rw [h j hj', hξ j ε ε' fun i hi => h i (lt_trans (Fin.lt_def.mp hi) hj')]

/-- The tower property for the cube conditional expectation. -/
theorem condAvg_condAvg {k l : ℕ} (h : k ≤ l) (f : (Fin N → Bool) → E) :
    condAvg k (condAvg l f) = condAvg k f := by
  sorry

/-- An `ℱ_k`-measurable function is its own conditional expectation. -/
theorem condAvg_of_isAdapted {k : ℕ} {f : (Fin N → Bool) → E}
    (hf : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε') :
    condAvg k f = f := by
  sorry

/-- The conditional expectation `E [· | ℱ_0]` is the plain average. -/
theorem condAvg_zero_real (f : (Fin N → Bool) → ℝ) (ε : Fin N → Bool) :
    condAvg 0 f ε = avg f := by
  sorry

/-- A Paley–Walsh martingale of a predictable family is a martingale:
`E [M_m | ℱ_n] = M_{min n m}`. -/
theorem condAvg_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ) (n m : ℕ) :
    condAvg n (paleyWalsh ξ m) = paleyWalsh ξ (min n m) := by
  sorry

theorem IsPredictable.isCubeMartingale_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E}
    (hξ : IsPredictable ξ) : IsCubeMartingale (paleyWalsh ξ) := by
  sorry

/-- The transform of the final value of a Paley–Walsh martingale is the Paley–Walsh martingale
of the transformed family: `T_σ (Σ_k ε_k ξ_k) = Σ_k σ_k ε_k ξ_k`. -/
theorem transform_paleyWalsh {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    {σ : Fin N → (Fin N → Bool) → ℝ} (hσ : IsPredictable σ) :
    transform σ (paleyWalsh ξ N) = paleyWalsh (fun k ε => σ k ε • ξ k ε) N := by
  sorry

/-- Every martingale on the sign cube is a Paley–Walsh martingale started at its (constant)
initial value: `M n = M 0 + Σ_{k<n} ε_k ξ_k` with `ξ_k = ε_k (M (k + 1) − M k)` predictable. -/
theorem exists_paleyWalsh_of_isCubeMartingale {M : ℕ → (Fin N → Bool) → E}
    (hM : IsCubeMartingale M) :
    ∃ ξ : Fin N → (Fin N → Bool) → E, IsPredictable ξ ∧
      ∀ n ε, M n ε = M 0 ε + paleyWalsh ξ n ε := by
  sorry

/-- The family `ξ` cut off where a predictable event fails: if the event `A k` depends only on the
signs `ε_j`, `j < k`, then `k ↦ 1_{A k} ξ_k` is predictable. -/
theorem IsPredictable.indicator {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    {A : Fin N → Set (Fin N → Bool)}
    (hA : ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) → (ε ∈ A k ↔ ε' ∈ A k)) :
    IsPredictable fun k ε => (A k).indicator (ξ k) ε := by
  sorry

/-- A Paley–Walsh martingale stopped at a stopping time is the Paley–Walsh martingale of the
predictable family `k ↦ 1_{k < τ} ξ_k`. -/
theorem IsPredictable.stopped {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    {τ : (Fin N → Bool) → ℕ} (hτ : IsStoppingTime τ) :
    IsPredictable fun k ε => if k.val < τ ε then ξ k ε else 0 := by
  sorry

theorem paleyWalsh_stopped (ξ : Fin N → (Fin N → Bool) → E) (τ : (Fin N → Bool) → ℕ) (n : ℕ)
    (ε : Fin N → Bool) :
    paleyWalsh ξ (min n (τ ε)) ε =
      paleyWalsh (fun k ε => if k.val < τ ε then ξ k ε else 0) n ε := by
  sorry

end Module

section Normed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jumps of a Paley–Walsh martingale are predictable: `‖M_{k+1} − M_k‖ = ‖ξ_k‖`. -/
theorem norm_paleyWalsh_succ_sub (ξ : Fin N → (Fin N → Bool) → E) (k : Fin N)
    (ε : Fin N → Bool) :
    ‖paleyWalsh ξ (k.val + 1) ε - paleyWalsh ξ k.val ε‖ = ‖ξ k ε‖ := by
  sorry

/-- The norm of a conditional expectation is at most the conditional expectation of the norm
(the triangle inequality for the average). -/
theorem norm_condAvg_le (k : ℕ) (f : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    ‖condAvg k f ε‖ ≤ condAvg k (fun ε => ‖f ε‖) ε := by
  sorry

end Normed

end BanachProbability.SignCube
