module

public import BanachProbability.SignCube.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Walsh functions

The Walsh functions on the sign cube are `w_α = Π_{i ∈ α} ε_i`, `α ⊆ {1, …, N}` (`walsh`). They are
orthonormal, `E w_α w_β = δ_{αβ}` (`avg_walsh_mul_walsh`), and every function `f` on the cube with
values in a real vector space is `f = Σ_α w_α x_α` with `x_α = E (w_α f)` (`walshCoeff`,
`sum_walsh_smul_walshCoeff`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces II* (2017), §6.2.a,
p. 18: "by induction one checks that a basis of functions on `D^N` is given by the Walsh functions";
"it is immediate that these functions are orthonormal"; "thus any function `f : D^N → X` can be
written as `f = Σ_α w_α x_α`, `x_α = E (w_α f)`". The induction here is on the set of the signs on
which the function depends.
-/

@[expose] public section

namespace BanachProbability.SignCube

variable {N : ℕ}

/-- The Walsh function `w_α = Π_{i ∈ α} ε_i`, `α ⊆ {1, …, N}` (HNVW II, p. 18). -/
def walsh (α : Finset (Fin N)) (ε : Fin N → Bool) : ℝ :=
  ∏ i ∈ α, coin (ε i)

/-- `w_∅ = 1`. -/
@[simp] theorem walsh_empty (ε : Fin N → Bool) : walsh ∅ ε = 1 :=
  Finset.prod_empty

/-- `w_{i} = ε_i`. -/
@[simp] theorem walsh_singleton (i : Fin N) (ε : Fin N → Bool) : walsh {i} ε = coin (ε i) :=
  Finset.prod_singleton _ _

/-- `w_{α ∪ {i}} = ε_i w_α` for `i ∉ α`. -/
theorem walsh_insert {α : Finset (Fin N)} {i : Fin N} (hi : i ∉ α) (ε : Fin N → Bool) :
    walsh (insert i α) ε = coin (ε i) * walsh α ε :=
  Finset.prod_insert hi

/-- `w_α² = 1`. -/
theorem walsh_mul_self (α : Finset (Fin N)) (ε : Fin N → Bool) : walsh α ε * walsh α ε = 1 := by
  simp only [walsh, ← Finset.prod_mul_distrib, coin_mul_self, Finset.prod_const_one]

/-- `w_α` does not depend on the signs outside `α`. -/
theorem walsh_update {α : Finset (Fin N)} {i : Fin N} (hi : i ∉ α) (ε : Fin N → Bool) (b : Bool) :
    walsh α (Function.update ε i b) = walsh α ε :=
  Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

/-- The flip of the `i`-th sign changes the sign of `w_α` if `i ∈ α`. -/
theorem walsh_flip {α : Finset (Fin N)} {i : Fin N} (hi : i ∈ α) (ε : Fin N → Bool) :
    walsh α (SignCube.flip i ε) = -walsh α ε := by
  rw [← Finset.insert_erase hi, walsh_insert (Finset.notMem_erase i α),
    walsh_insert (Finset.notMem_erase i α), flip_apply_self, coin_not, SignCube.flip,
    walsh_update (Finset.notMem_erase i α), neg_mul]

/-- The flip of the `i`-th sign does not change `w_α` if `i ∉ α`. -/
theorem walsh_flip_of_notMem {α : Finset (Fin N)} {i : Fin N} (hi : i ∉ α) (ε : Fin N → Bool) :
    walsh α (SignCube.flip i ε) = walsh α ε :=
  walsh_update hi ε _

/-- The Walsh functions are orthonormal: `E w_α w_β = δ_{αβ}` (HNVW II, p. 18). -/
theorem avg_walsh_mul_walsh (α β : Finset (Fin N)) :
    avg (fun ε => walsh α ε * walsh β ε) = if α = β then 1 else 0 := by
  split_ifs with h
  · subst h
    simp only [walsh_mul_self, avg_const]
  · -- a sign that occurs in exactly one of `w_α`, `w_β`
    obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ α ↔ i ∈ β) := by
      by_contra hc
      push Not at hc
      exact h (Finset.ext hc)
    refine scb_avg_eq_zero_of_flip i fun ε => ?_
    by_cases hα : i ∈ α
    · have hβ : i ∉ β := fun hβ => hi (iff_of_true hα hβ)
      rw [walsh_flip hα, walsh_flip_of_notMem hβ, neg_mul]
    · have hβ : i ∈ β := by
        by_contra hβ
        exact hi (iff_of_false hα hβ)
      rw [walsh_flip hβ, walsh_flip_of_notMem hα, mul_neg]

section Expansion

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Walsh coefficient `x_α = E (w_α f)` of a function on the sign cube with values in a real
vector space (HNVW II, p. 18). -/
noncomputable def walshCoeff (f : (Fin N → Bool) → V) (α : Finset (Fin N)) : V :=
  ((2 : ℝ) ^ N)⁻¹ • ∑ η, walsh α η • f η

/-- The induction in HNVW II, p. 18 ("by induction one checks that a basis of functions on `D^N` is
given by the Walsh functions"): a function of the signs in `s` is a combination of the Walsh
functions `w_α`, `α ⊆ s`, as a function of one sign is `x + ε_i y`. -/
private theorem exists_piecewise_eq_sum_walsh_smul (s : Finset (Fin N))
    (f : (Fin N → Bool) → V) :
    ∃ y : Finset (Fin N) → V, ∀ ε,
      f (s.piecewise ε fun _ => true) = ∑ α ∈ s.powerset, walsh α ε • y α := by
  induction s using Finset.induction generalizing f with
  | empty => exact ⟨fun _ => f fun _ => true, fun ε => by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy⟩ := ih fun ε => f (Function.update ε i true)
    obtain ⟨z, hz⟩ := ih fun ε => f (Function.update ε i false)
    refine ⟨fun α => if i ∈ α then (1 / 2 : ℝ) • (y (α.erase i) - z (α.erase i)) else
      (1 / 2 : ℝ) • (y α + z α), fun ε => ?_⟩
    have hα : ∀ α ∈ s.powerset, i ∉ α := fun α hα h => hi (Finset.mem_powerset.1 hα h)
    -- `g (ε_i) = (g (1) + g (−1)) / 2 + ε_i (g (1) − g (−1)) / 2`
    have hg : ∀ (b : Bool) (g : Bool → V), g b = (1 / 2 : ℝ) • (g true + g false) +
        coin b • (1 / 2 : ℝ) • (g true - g false) := fun b g => by
      cases b <;> simp only [coin_true, coin_false] <;> module
    rw [Finset.piecewise_insert, hg (ε i) fun b => f (Function.update _ i b), hy, hz,
      Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine congrArg₂ _ (Finset.sum_congr rfl fun α h => ?_) (Finset.sum_congr rfl fun α h => ?_)
    · beta_reduce
      rw [ite_eq_right (hα α h)]
      module
    · beta_reduce
      rw [ite_eq_left (Finset.mem_insert_self i α), Finset.erase_insert (hα α h),
        walsh_insert (hα α h)]
      module

/-- The Walsh expansion `f = Σ_α w_α x_α`, `x_α = E (w_α f)`, of a function on the sign cube with
values in a real vector space (HNVW II, p. 18). -/
theorem sum_walsh_smul_walshCoeff (f : (Fin N → Bool) → V) (ε : Fin N → Bool) :
    ∑ α, walsh α ε • walshCoeff f α = f ε := by
  obtain ⟨y, hy⟩ := exists_piecewise_eq_sum_walsh_smul Finset.univ f
  simp only [Finset.piecewise_univ, Finset.powerset_univ] at hy
  -- the coefficients are `E (w_α f)`, by the orthonormality
  have hcoeff : ∀ α, walshCoeff f α = y α := fun α => by
    have h : ∀ β, ((2 : ℝ) ^ N)⁻¹ • ∑ η : Fin N → Bool, walsh α η • walsh β η • y β =
        if α = β then y β else 0 := fun β => by
      simp only [smul_smul, ← Finset.sum_smul]
      rw [← div_eq_inv_mul, ← avg, avg_walsh_mul_walsh, ite_smul, one_smul, zero_smul]
    simp only [walshCoeff, hy, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [hcoeff, hy]

end Expansion

end BanachProbability.SignCube
