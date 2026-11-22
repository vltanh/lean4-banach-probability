module

public import BanachProbability.Defs
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The sign cube

`N` independent fair signs are realised on the finite set `Fin N → Bool` (the *sign cube*) with
the uniform probability. This file sets up the elementary objects on the cube that the rest of the
library uses (`coin` and `avg` are defined in `BanachProbability.Defs`):

* `SignCube.coin`: the sign `±1` of a coin, `coin true = 1`, `coin false = -1`;
* `SignCube.avg`: the expectation `2^{-N} Σ_ε g (ε)` over the cube;
* `SignCube.prob`: the probability of a set of sign vectors;
* `SignCube.flip`: the flip of one sign, a measure-preserving involution;
* `SignCube.mul`: the pointwise product of two sign vectors (`coin (mul ε η k) = coin (ε k) coin
  (η k)`), a measure-preserving translation;
* `SignCube.interleave`: the bijection `(Fin N → Bool) × (Fin N → Bool) ≃ (Fin (N * 2) → Bool)`,
  `(ε, η) ↦ (η₀, ε₀, η₁, ε₁, …)`, which turns a double average into a single one.

Everything is a finite sum; the bridge to Mathlib's probability theory is in
`BanachProbability.SignCube.Bridge`.
-/

@[expose] public section

open scoped BigOperators

namespace BanachProbability.SignCube

@[simp] theorem coin_true : coin true = 1 := rfl

@[simp] theorem coin_false : coin false = -1 := rfl

theorem coin_not (b : Bool) : coin (!b) = -coin b := by
  cases b <;> simp [coin]

theorem coin_mul_self (b : Bool) : coin b * coin b = 1 := by
  cases b <;> simp [coin]

theorem coin_eq_one_or_eq_neg_one (b : Bool) : coin b = 1 ∨ coin b = -1 := by
  cases b <;> simp

theorem abs_coin (b : Bool) : |coin b| = 1 := by
  cases b <;> simp

variable {N : ℕ}

/-- The probability that `N` fair signs fall in `s`. -/
noncomputable def prob (s : Set (Fin N → Bool)) : ℝ :=
  avg (s.indicator 1)

theorem avg_eq_expect (g : (Fin N → Bool) → ℝ) : avg g = 𝔼 ε, g ε := by
  simp [avg, Fintype.expect_eq_sum_div_card]

theorem avg_add (f g : (Fin N → Bool) → ℝ) : avg (fun ε => f ε + g ε) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem avg_sub (f g : (Fin N → Bool) → ℝ) : avg (fun ε => f ε - g ε) = avg f - avg g := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem avg_const_mul (c : ℝ) (g : (Fin N → Bool) → ℝ) : avg (fun ε => c * g ε) = c * avg g := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

theorem avg_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin N → Bool) → ℝ) :
    avg (fun ε => ∑ i ∈ s, g i ε) = ∑ i ∈ s, avg (g i) := by
  simp only [avg, div_eq_mul_inv]
  rw [Finset.sum_comm, Finset.sum_mul]

@[simp] theorem avg_const (c : ℝ) : avg (fun _ : Fin N → Bool => c) = c := by
  simp [avg]

theorem avg_mono {f g : (Fin N → Bool) → ℝ} (h : ∀ ε, f ε ≤ g ε) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ => h ε) (by positivity)

theorem avg_nonneg {g : (Fin N → Bool) → ℝ} (h : ∀ ε, 0 ≤ g ε) : 0 ≤ avg g :=
  div_nonneg (Finset.sum_nonneg fun ε _ => h ε) (by positivity)

/-- Each sign vector has probability `2^{-N}`: `g ε ≤ 2^N avg g` for `g ≥ 0`. -/
theorem le_two_pow_mul_avg {g : (Fin N → Bool) → ℝ} (h : ∀ ε, 0 ≤ g ε) (ε : Fin N → Bool) :
    g ε ≤ 2 ^ N * avg g := by
  rw [avg, mul_div_cancel₀ _ (by positivity)]
  exact Finset.single_le_sum (fun i _ => h i) (Finset.mem_univ ε)

/-- Averages are invariant under every bijection of the cube (the uniform measure is invariant
under every permutation). -/
theorem avg_comp_equiv (e : (Fin N → Bool) ≃ (Fin N → Bool)) (g : (Fin N → Bool) → ℝ) :
    avg (fun ε => g (e ε)) = avg g := by
  simp only [avg, e.sum_comp g]

/-- The flip of the `k`-th sign. -/
protected def flip (k : Fin N) (ε : Fin N → Bool) : Fin N → Bool :=
  Function.update ε k (!ε k)

theorem flip_involutive (k : Fin N) : Function.Involutive (SignCube.flip k) := by
  intro ε
  funext j
  by_cases h : j = k
  · subst h; simp [SignCube.flip]
  · simp [SignCube.flip, Function.update_of_ne h]

@[simp] theorem flip_apply_self (k : Fin N) (ε : Fin N → Bool) :
    SignCube.flip k ε k = !ε k := by
  simp [SignCube.flip]

theorem flip_apply_of_ne {k j : Fin N} (h : j ≠ k) (ε : Fin N → Bool) :
    SignCube.flip k ε j = ε j := by
  simp [SignCube.flip, h]

theorem avg_flip (k : Fin N) (g : (Fin N → Bool) → ℝ) :
    avg (fun ε => g (SignCube.flip k ε)) = avg g :=
  avg_comp_equiv ((flip_involutive k).toPerm _) g

/-- The pointwise product of two sign vectors: `coin (mul ε η k) = coin (ε k) * coin (η k)`. -/
def mul (ε η : Fin N → Bool) : Fin N → Bool :=
  fun k => ε k == η k

theorem coin_mul_apply (ε η : Fin N → Bool) (k : Fin N) :
    coin (mul ε η k) = coin (ε k) * coin (η k) := by
  simp only [mul]
  cases ε k <;> cases η k <;> simp [coin]

theorem scb_mul_involutive (ε : Fin N → Bool) : Function.Involutive (mul ε) := by
  intro η
  funext k
  simp only [mul]
  cases ε k <;> cases η k <;> rfl

/-- Translation invariance of the uniform measure on the group `{±1}^N`. -/
theorem avg_mul_left (ε : Fin N → Bool) (g : (Fin N → Bool) → ℝ) :
    avg (fun η => g (mul ε η)) = avg g :=
  avg_comp_equiv ((scb_mul_involutive ε).toPerm _) g

/-- An average vanishes when flipping one sign changes the sign of the function (pairing `ε`
with `flip k ε`). -/
theorem scb_avg_eq_zero_of_flip (k : Fin N) {g : (Fin N → Bool) → ℝ}
    (hg : ∀ ε, g (SignCube.flip k ε) = -g ε) : avg g = 0 := by
  have h := avg_flip k g
  simp only [hg] at h
  have h2 : avg (fun ε => -g ε) = -avg g := by
    simpa using avg_const_mul (-1) g
  linarith

theorem avg_coin (i : Fin N) : avg (fun ε => coin (ε i)) = 0 :=
  scb_avg_eq_zero_of_flip i fun ε => by simp [coin_not]

/-- Orthonormality of the signs: `E ε_i ε_j = δ_{ij}`. -/
theorem avg_coin_mul_coin (i j : Fin N) :
    avg (fun ε => coin (ε i) * coin (ε j)) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    simp [coin_mul_self]
  · exact scb_avg_eq_zero_of_flip i fun ε => by
      simp [coin_not, flip_apply_of_ne (Ne.symm h)]

/-- Splitting off the first sign: `E g = (E g (1, ·) + E g (−1, ·)) / 2`. -/
theorem avg_succ (g : (Fin (N + 1) → Bool) → ℝ) :
    avg g = (avg (fun ε => g (Fin.cons true ε)) + avg (fun ε => g (Fin.cons false ε))) / 2 := by
  simp only [avg]
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, pow_succ]
  ring

/-- Splitting off the last sign. -/
theorem avg_succ_last (g : (Fin (N + 1) → Bool) → ℝ) :
    avg g = (avg (fun ε => g (Fin.snoc ε true)) + avg (fun ε => g (Fin.snoc ε false))) / 2 := by
  simp only [avg]
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.snocEquiv_apply, pow_succ]
  ring

/-- The interleaving `(ε, η) ↦ (η₀, ε₀, η₁, ε₁, …)` of two sign vectors: the coordinate `2k` of
the result is `η k` and the coordinate `2k + 1` is `ε k` (through `finProdFinEquiv`,
`(k, j) ↦ j + 2k`). -/
def interleave : (Fin N → Bool) × (Fin N → Bool) ≃ (Fin (N * 2) → Bool) where
  toFun x i := if (finProdFinEquiv.symm i).2 = 0 then x.2 (finProdFinEquiv.symm i).1
    else x.1 (finProdFinEquiv.symm i).1
  invFun ω := (fun k => ω (finProdFinEquiv (k, 1)), fun k => ω (finProdFinEquiv (k, 0)))
  left_inv x := by
    ext k <;> simp
  right_inv ω := by
    funext i
    obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective i
    fin_cases j <;> simp

/-- The interleaving carries the uniform measure on pairs to the uniform measure on the doubled
cube: a double average is a single average over `Fin (N * 2) → Bool`. -/
theorem avg_interleave (G : (Fin N → Bool) → (Fin N → Bool) → ℝ) :
    avg (fun ω => G (interleave.symm ω).1 (interleave.symm ω).2) =
      avg (fun ε => avg fun η => G ε η) := by
  simp only [avg]
  rw [interleave.symm.sum_comp (fun x => G x.1 x.2), Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_assoc, ← mul_inv, ← pow_add, mul_two]

end BanachProbability.SignCube
