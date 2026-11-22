module

public import BanachProbability.NoncommutativeKhintchine.Symmetric
public import BanachProbability.NoncommutativeKhintchine.Lower
public import BanachProbability.Schatten.Dilation

/-!
# The noncommutative Khintchine inequality

For real `n × n` matrices `x_1, …, x_k`, `q ∈ [2, ∞)` and independent fair signs `ε_i`:

* upper bound (`ncKhintchine_upper`):
  `(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) max (‖Σ_i x_i x_iᵀ‖_{S_{q/2}},
  ‖Σ_i x_iᵀ x_i‖_{S_{q/2}})^{1/2}`, from the symmetric case applied to the Hermitian dilations
  `D (x_i) = [[0, x_i], [x_iᵀ, 0]]` (Mackey–Jordan–Chen–Farrell–Tropp, Ann. Probab. 42 (2014),
  §8): `‖D (S)‖_q^q = 2 ‖S‖_q^q` and `Σ_i D (x_i)² = diag (Σ_i x_i x_iᵀ, Σ_i x_iᵀ x_i)`;
* for normal `x_i` (`x_i x_iᵀ = x_iᵀ x_i`), both bounds together (`ncKhintchine_normal`):
  `‖(Σ_i x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤
  √2 √q ‖(Σ_i x_i x_iᵀ)^{1/2}‖_{S_q}`; this is the noncommutative Khintchine inequality of
  F. Lust-Piquard (1986), F. Lust-Piquard and G. Pisier (1991) and G. Pisier and Q. Xu,
  *Non-commutative `L^p`-spaces* (2003), Theorem 6.1, with the constant `C √q`, `C = √2`
  (`pisierXu_khintchine`).

Here `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} = ‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2}`, which is how the statements are
written.
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

open SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Noncommutative Khintchine inequality, upper bound**, for real square matrices:
`(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1)) max (‖Σ x_i x_iᵀ‖_{S_{q/2}},
‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`, `q ≥ 2`. -/
theorem ncKhintchine_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    lpNorm (schattenNorm (ENNReal.ofReal q)) q (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) := by
  sorry

/-- **Noncommutative Khintchine inequality for normal matrices**, both bounds:
`‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2} ≤ (E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q}` and
`(E ‖Σ_i ε_i x_i‖_{S_q}^q)^{1/q} ≤ √2 √q ‖Σ x_i x_iᵀ‖_{S_{q/2}}^{1/2}`, `q ≥ 2`. -/
theorem ncKhintchine_normal {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ)
    (hx : ∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
        lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      lpNorm (schattenNorm (ENNReal.ofReal q)) q (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        √2 * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  sorry

/-- **The noncommutative Khintchine inequality** (Lust-Piquard 1986; Lust-Piquard–Pisier 1991;
Pisier–Xu 2003, Theorem 6.1), for real normal matrices, with an absolute constant: there is
`C > 0` such that for every `q ∈ [2, ∞)`, every dimension and every family of normal `x_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ C √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`.
The proof (`ncKhintchine_normal`) gives `C = √2`. -/
theorem pisierXu_khintchine : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ), 2 ≤ q → ∀ (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
      (x : Fin k → Matrix n n ℝ), (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
        lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) :=
  ⟨√2, by positivity, fun _q hq _n _ _ _k x hx => ncKhintchine_normal hq x hx⟩

end BanachProbability
