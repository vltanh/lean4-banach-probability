module

public import BanachProbability.SignCube.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# `L^p` norms of functions on the sign cube

For a function `nrm : E → ℝ` (a norm or seminorm of the values) and `p > 0`,
`SignCube.lpNorm nrm p X = (E nrm (X ε)^p)^{1/p}` is the `L^p` norm of a random variable `X` on
the sign cube. For a seminorm `N` on a real vector space and `p ≥ 1` it is a seminorm on
`(Fin n → Bool) → E` (Minkowski's inequality), `lpSeminorm N p`; it is nondecreasing in `p`
(the power-mean inequality).
-/

@[expose] public section

namespace BanachProbability.SignCube

variable {N : ℕ} {E : Type*}

/-- The `L^p` norm `(E nrm (X ε)^p)^{1/p}` of a random variable `X` on the sign cube, the values
measured with `nrm`. -/
protected noncomputable def lpNorm (nrm : E → ℝ) (p : ℝ) (X : (Fin N → Bool) → E) : ℝ :=
  avg (fun ε => nrm (X ε) ^ p) ^ (1 / p)

theorem lpNorm_nonneg {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) (p : ℝ) (X : (Fin N → Bool) → E) :
    0 ≤ SignCube.lpNorm nrm p X := by
  sorry

/-- The power-mean inequality: `‖X‖_p ≤ ‖X‖_q` for `0 < p ≤ q`. -/
theorem lpNorm_mono_exponent {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (X : (Fin N → Bool) → E) : SignCube.lpNorm nrm p X ≤ SignCube.lpNorm nrm q X := by
  sorry

/-- Every value is bounded by `2^{N/p}` times the `L^p` norm. -/
theorem le_lpNorm {nrm : E → ℝ} (hnrm : ∀ x, 0 ≤ nrm x) {p : ℝ} (hp : 0 < p)
    (X : (Fin N → Bool) → E) (ε : Fin N → Bool) :
    nrm (X ε) ≤ (2 : ℝ) ^ ((N : ℝ) / p) * SignCube.lpNorm nrm p X := by
  sorry

section Seminorm

variable [AddCommGroup E] [Module ℝ E]

/-- Minkowski's inequality on the sign cube. -/
theorem lpNorm_add_le (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p) (X Y : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (X + Y) ≤ SignCube.lpNorm S p X + SignCube.lpNorm S p Y := by
  sorry

theorem lpNorm_smul (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) (c : ℝ) (X : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (c • X) = ‖c‖ * SignCube.lpNorm S p X := by
  sorry

/-- The `L^p` seminorm `X ↦ (E S (X ε)^p)^{1/p}` on `E`-valued functions on the sign cube, for a
seminorm `S` on `E` and `p ≥ 1`. -/
noncomputable def lpSeminorm (S : Seminorm ℝ E) (p : ℝ) (hp : 1 ≤ p) :
    Seminorm ℝ ((Fin N → Bool) → E) :=
  Seminorm.of (SignCube.lpNorm S p) (lpNorm_add_le S hp)
    (fun c X => lpNorm_smul S (zero_lt_one.trans_le hp) c X)

@[simp] theorem lpSeminorm_apply (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p)
    (X : (Fin N → Bool) → E) : lpSeminorm S p hp X = SignCube.lpNorm S p X :=
  rfl

end Seminorm

end BanachProbability.SignCube
