module

public import BanachProbability.Noncommutative.Distribution

/-!
# Marcinkiewicz interpolation on the matrix cube

A linear map `T` on matrix-valued functions on the sign cube that is of weak type `(p_j, p_j)`
with constant `K_j` on symmetric-matrix-valued functions, `j = 0, 1`, `p₀ < p₁`, is of strong
type `(r, r)` for `p₀ < r < p₁`:
`‖T x‖_{L^r}^r ≤ 2^r r (K₀^{p₀} / (r − p₀) + K₁^{p₁} / (p₁ − r)) ‖x‖_{L^r}^r`
(`marcinkiewicz`; J. Marcinkiewicz, C. R. Acad. Sci. Paris 208 (1939); for noncommutative `L^p`
spaces, e.g. Randrianantoanina (2002), the interpolation step of Theorem 4.3). The proof is the
classical one, with the spectral truncations: split `x` at level `s` into
`x 1_{(s, ∞)} (|x|)` and `x 1_{[0, s]} (|x|)` pointwise (`truncAbove`, `truncBelow`), use the
subadditivity of the distribution function (`distribution_add_add_le`), and integrate with the
layer-cake formula (`avg_schattenNorm_rpow_eq_integral`).
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- `T` is of weak type `(p, p)` with constant `K` on symmetric-matrix-valued functions:
`s^p λ_s (T x) ≤ K^p ‖x‖_{L^p}^p`. -/
def IsWeakType (T : ((Fin N → Bool) → Matrix n n ℝ) → ((Fin N → Bool) → Matrix n n ℝ))
    (p K : ℝ) : Prop :=
  ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) → ∀ s : ℝ, 0 < s →
    s ^ p * distribution s (T x) ≤ K ^ p * avg fun ε => schattenNorm (ENNReal.ofReal p) (x ε) ^ p

/-- A strong type `(p, p)` bound gives the weak type `(p, p)` bound with the same constant
(Chebyshev). -/
theorem isWeakType_of_lpNorm_le
    {T : ((Fin N → Bool) → Matrix n n ℝ) → ((Fin N → Bool) → Matrix n n ℝ)} {p K : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K)
    (h : ∀ x : (Fin N → Bool) → Matrix n n ℝ, (∀ ε, (x ε).IsHermitian) →
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p (T x) ≤
        K * SignCube.lpNorm (schattenNorm (ENNReal.ofReal p)) p x) :
    IsWeakType T p K := by
  sorry

/-- **Marcinkiewicz interpolation** on the matrix cube, with two endpoints `p₀ < r < p₁`. -/
theorem marcinkiewicz (T : ((Fin N → Bool) → Matrix n n ℝ) →ₗ[ℝ] ((Fin N → Bool) → Matrix n n ℝ))
    {p₀ p₁ K₀ K₁ r : ℝ} (hp₀ : 0 < p₀) (hp₀r : p₀ < r) (hrp₁ : r < p₁) (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (h₀ : IsWeakType T p₀ K₀) (h₁ : IsWeakType T p₁ K₁)
    (x : (Fin N → Bool) → Matrix n n ℝ) (hx : ∀ ε, (x ε).IsHermitian) :
    (avg fun ε => schattenNorm (ENNReal.ofReal r) (T x ε) ^ r) ≤
      2 ^ r * r * (K₀ ^ p₀ / (r - p₀) + K₁ ^ p₁ / (p₁ - r)) *
        avg fun ε => schattenNorm (ENNReal.ofReal r) (x ε) ^ r := by
  sorry

end BanachProbability
