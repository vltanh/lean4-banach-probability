module

public import BanachProbability.TypeTwo.Even
public import BanachProbability.Schatten.ThreeLines
public import BanachProbability.Schatten.Space

/-!
# Type 2 of the Schatten classes

For `q ≥ 2` the Schatten class `S_q` has type 2 with a constant of order `√q`, uniformly in the
size, even in the stronger form with the norm of `L^q (Ω; S_q)` on the left:

`(E ‖Σ ε_i A_i‖_{S_q}^q)^{1/q} ≤ √(q + 1) (Σ ‖A_i‖_{S_q}²)^{1/2}`

(`lpNorm_complexSchattenNorm_le`, `lpNorm_schattenNorm_le`, `isTypeTwoBound_schattenSpace`).

Source: N. Tomczak-Jaegermann, *The moduli of smoothness and convexity and the Rademacher averages
of trace classes `S_p` (`1 ≤ p < ∞`)*, Studia Math. 50 (1974) 163–182, Theorem 3.1 (ii), pp.
178–179: for `2k ≤ q ≤ 2k + 2` the even case (`TypeTwo.Even`) at `2k` and `2k + 2` is interpolated
by Proposition 1.2 (`Schatten.ThreeLines`), applied to the analytic families
`φ_i (z) a_{ij} = α_{ij}^{q/p(z)} ‖A_i‖_q^{1 − q/p(z)} a'_{ij}`, where `A_i a_{ij} = α_{ij} a'_{ij}`
is the singular value decomposition and `1/p(z) = (1 − z)/(2k) + z/(2k + 2)`; in terms of the polar
decomposition, `φ_i (z) = ‖A_i‖_q U_i (Δ_i / ‖A_i‖_q)^{q/p(z)}` (`polarPower`). The constant is
`M_{2k}^{1−θ} M_{2k+2}^θ` (`lpNorm_complexSchattenNorm_le_interp`), at most `√(q + 1)`.
-/

@[expose] public section

open Complex.HadamardThreeLines
open scoped ENNReal Matrix

namespace BanachProbability

open SignCube

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

private theorem evenKhintchineConst_nonneg (k : ℕ) : 0 ≤ evenKhintchineConst k := by
  unfold evenKhintchineConst
  positivity

/-! ### The analytic families of the source -/

/-- `1/p(z) = (1 − z)/(2k) + z/(2k + 2)`. -/
private noncomputable def interpExponent (k : ℕ) (z : ℂ) : ℂ :=
  (1 - z) / (2 * k : ℝ) + z / (2 * k + 2 : ℝ)

private theorem re_interpExponent (k : ℕ) (z : ℂ) :
    (interpExponent k z).re = (1 - z.re) / (2 * k) + z.re / (2 * k + 2) := by
  rw [interpExponent, Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sub_re,
    Complex.one_re]

/-- `φ (z) a_j = α_j^{q/p(z)} ‖A‖_q^{1 − q/p(z)} a'_j`, where `A a_j = α_j a'_j` is the singular
value decomposition (Tomczak-Jaegermann (1974), p. 178), that is,
`φ (z) = ‖A‖_{S_q} U (Δ / ‖A‖_{S_q})^{q/p(z)}` for the polar decomposition `A = U Δ`; `φ (z) = 0` on
the kernel of `A`. -/
private noncomputable def interpFamily (k : ℕ) (q : ℝ) (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (complexSchattenNorm (ENNReal.ofReal q) A : ℂ) • polarPower q A (q * interpExponent k z)

/-- `‖φ (μ + iy)‖_{S_{p_μ}} ≤ ‖A‖_{S_q}`. -/
private theorem complexSchattenNorm_interpFamily_le {k : ℕ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (A : Matrix n n ℂ) {z : ℂ} (hz : (interpExponent k z).re = 1 / p) :
    complexSchattenNorm (ENNReal.ofReal p) (interpFamily k q A z) ≤
      complexSchattenNorm (ENNReal.ofReal q) A := by
  rw [interpFamily, complexSchattenNorm_smul (ENNReal.ofReal_pos.2 hp).ne', Complex.norm_real,
    Real.norm_of_nonneg (complexSchattenNorm_nonneg _ _)]
  refine mul_le_of_le_one_right (complexSchattenNorm_nonneg _ _)
    (complexSchattenNorm_polarPower_le_one hp hq A ?_)
  rw [Complex.re_ofReal_mul, hz, mul_one_div]

/-- `φ (θ) = A` if `1/p(θ) = 1/q`. -/
private theorem interpFamily_eq {k : ℕ} {q : ℝ} (hq : 0 < q) (A : Matrix n n ℂ) {z : ℂ}
    (hz : interpExponent k z = (1 / q : ℝ)) : interpFamily k q A z = A := by
  rw [interpFamily, hz, ← Complex.ofReal_mul, mul_one_div_cancel hq.ne', Complex.ofReal_one,
    smul_polarPower_one hq]

/-- The entries of `φ` are entire functions. -/
private theorem differentiable_interpFamily (k : ℕ) (q : ℝ) (A : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun z => interpFamily k q A z i j := by
  have h : Differentiable ℂ fun z => polarPower q A (q * interpExponent k z) i j :=
    (differentiable_polarPower q A i j).comp (by unfold interpExponent; fun_prop)
  exact h.fun_const_smul (complexSchattenNorm (ENNReal.ofReal q) A : ℂ)

/-- The entries of `φ` are bounded on the strip. -/
private theorem exists_norm_interpFamily_le (k : ℕ) {q : ℝ} (hq : 0 < q) (A : Matrix n n ℂ) :
    ∃ B : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ∀ i j, ‖interpFamily k q A z i j‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_polarPower_le hq A
  refine ⟨complexSchattenNorm (ENNReal.ofReal q) A * B, fun z hz i j => ?_⟩
  rw [interpFamily, Matrix.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (complexSchattenNorm_nonneg _ _)]
  refine mul_le_mul_of_nonneg_left (hB _ ?_ i j) (complexSchattenNorm_nonneg _ _)
  rw [Complex.re_ofReal_mul, re_interpExponent]
  exact mul_nonneg hq.le (add_nonneg (div_nonneg (sub_nonneg.2 hz.2) (by positivity))
    (div_nonneg hz.1 (by positivity)))

/-- The even case (3.15) on one of the lines: if `‖φ_m‖_{S_{2k}} ≤ ‖A_m‖_{S_q}`, then
`‖Σ ε_m φ_m‖_{L^{2k} (S_{2k})} ≤ M_{2k} (Σ ‖A_m‖_{S_q}²)^{1/2}`. -/
private theorem lpNorm_even_le {k : ℕ} (hk : 1 ≤ k) {p q : ℝ} (hp : 2 * (k : ℝ) = p)
    {x y : Fin N → Matrix n n ℂ} (h : ∀ i, complexSchattenNorm (ENNReal.ofReal p) (y i) ≤
      complexSchattenNorm (ENNReal.ofReal q) (x i)) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal p)) p
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • y i) ≤
      evenKhintchineConst k * √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  subst hp
  refine (lpNorm_complexSchattenNorm_le_of_even hk y).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)) (evenKhintchineConst_nonneg k))
  exact pow_le_pow_left₀ (complexSchattenNorm_nonneg _ _) (h i) 2

/-- The interpolation parameter `θ = (2k + 2) (q − 2k) / (2q)`: `0 ≤ θ ≤ 1` and
`1/q = (1 − θ)/(2k) + θ/(2k + 2)`. -/
private theorem interp_theta {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hkq : 2 * k ≤ q) (hqk : q ≤ 2 * k + 2) :
    0 ≤ (2 * k + 2) * (q - 2 * k) / (2 * q) ∧ (2 * k + 2) * (q - 2 * k) / (2 * q) ≤ 1 ∧
      1 / q = (1 - (2 * k + 2) * (q - 2 * k) / (2 * q)) / (2 * k) +
        (2 * k + 2) * (q - 2 * k) / (2 * q) / (2 * k + 2) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 < q := by linarith
  refine ⟨div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith), ?_, ?_⟩
  · rw [div_le_one (by linarith)]
    nlinarith
  · have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (2 * k + 2 : ℝ) ≠ 0 := by positivity
    have h3 : (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Type 2 -/

/-- **Type 2 of `S_q`**, complex matrices, with the constant of the source (Tomczak-Jaegermann
(1974), end of the proof of Theorem 3.1 (ii), p. 179): for `2k ≤ q ≤ 2k + 2` and
`θ = (2k + 2) (q − 2k) / (2q)`, `(E ‖Σ ε_i
A_i‖_{S_q}^q)^{1/q} ≤ M_{2k}^{1−θ} M_{2k+2}^θ (Σ ‖A_i‖_{S_q}²)^{1/2}`. -/
theorem lpNorm_complexSchattenNorm_le_interp {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hkq : 2 * k ≤ q)
    (hqk : q ≤ 2 * k + 2) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      evenKhintchineConst k ^ (1 - (2 * k + 2) * (q - 2 * k) / (2 * q)) *
        evenKhintchineConst (k + 1) ^ ((2 * k + 2) * (q - 2 * k) / (2 * q)) *
        √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 < q := by linarith
  obtain ⟨hθ0, hθ1, hθ⟩ := interp_theta hk hkq hqk
  set θ : ℝ := (2 * k + 2) * (q - 2 * k) / (2 * q)
  set B : ℝ := √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have h := lpNorm_complexSchattenNorm_le_of_verticalStrip (N := N) (p₀ := 2 * k) (p₁ := 2 * k + 2)
    (by linarith) (by linarith)
    (Φ := fun z ε => ∑ i, coin (ε i) • interpFamily k q (x i) z) (fun ε i j => ?_) ?_
    (M₀ := evenKhintchineConst k * B) (M₁ := evenKhintchineConst (k + 1) * B) (fun y => ?_)
    (fun y => ?_) (z := θ) ⟨by simpa using hθ0, by simpa using hθ1⟩ (r := q) (by simpa using hθ)
  · -- `φ_m (θ) = A_m`
    have he : interpExponent k θ = (1 / q : ℝ) := by
      rw [hθ, interpExponent]
      push_cast
      rfl
    simp only [interpFamily_eq hq _ he, Complex.ofReal_re] at h
    refine h.trans_eq ?_
    rw [Real.mul_rpow (evenKhintchineConst_nonneg k) hB0, Real.mul_rpow
      (evenKhintchineConst_nonneg _) hB0, mul_mul_mul_comm, ← Real.rpow_add_of_nonneg hB0
      (sub_nonneg.2 hθ1) hθ0, sub_add_cancel, Real.rpow_one]
  · -- analyticity
    refine Differentiable.diffContOnCl ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    exact Differentiable.fun_sum fun m _ =>
      (differentiable_interpFamily k q (x m) i j).fun_const_smul (coin (ε m))
  · -- boundedness
    choose C hC using fun m => exists_norm_interpFamily_le k hq (x m)
    refine ⟨∑ m, C m, fun z hz ε i j => ?_⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_coin, one_mul]
    exact hC m z hz i j
  · -- the line `Re z = 0`
    refine lpNorm_even_le hk rfl fun i => complexSchattenNorm_interpFamily_le (by linarith) hq _ ?_
    rw [re_interpExponent]
    simp
  · -- the line `Re z = 1`
    refine lpNorm_even_le (Nat.le_add_left 1 k) (by push_cast; ring) fun i =>
      complexSchattenNorm_interpFamily_le (by linarith) hq _ ?_
    rw [re_interpExponent]
    simp

/-- `M_{2k}^{1−θ} M_{2k+2}^θ ≤ √(q + 1)`, as `M_{2k} ≤ √(2k − 1)` and `M_{2k+2} ≤ √(2k + 1)`. -/
private theorem evenKhintchineConst_interp_le {k : ℕ} (hk : 1 ≤ k) {q θ : ℝ} (hkq : 2 * k ≤ q)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    evenKhintchineConst k ^ (1 - θ) * evenKhintchineConst (k + 1) ^ θ ≤ √(q + 1) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e₀ : evenKhintchineConst k ≤ √(q + 1) :=
    (evenKhintchineConst_le hk).trans (Real.sqrt_le_sqrt (by linarith))
  have e₁ : evenKhintchineConst (k + 1) ≤ √(q + 1) :=
    (evenKhintchineConst_le (Nat.le_add_left 1 k)).trans (Real.sqrt_le_sqrt (by
      push_cast
      linarith))
  calc evenKhintchineConst k ^ (1 - θ) * evenKhintchineConst (k + 1) ^ θ
      ≤ √(q + 1) ^ (1 - θ) * √(q + 1) ^ θ :=
        mul_le_mul (Real.rpow_le_rpow (evenKhintchineConst_nonneg _) e₀ (sub_nonneg.2 h1))
          (Real.rpow_le_rpow (evenKhintchineConst_nonneg _) e₁ h0)
          (Real.rpow_nonneg (evenKhintchineConst_nonneg _) _)
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ = √(q + 1) := by
        rw [← Real.rpow_add_of_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 h1) h0, sub_add_cancel,
          Real.rpow_one]

/-- **Type 2 of `S_q`**, `q ≥ 2`, complex matrices, with the constant `√(q + 1)`. -/
theorem lpNorm_complexSchattenNorm_le {q : ℝ} (hq : 2 ≤ q) (x : Fin N → Matrix n n ℂ) :
    SignCube.lpNorm (complexSchattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q + 1) * √(∑ i, complexSchattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  -- `k = [q/2]`
  have hk : 1 ≤ ⌊q / 2⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hkq : 2 * (⌊q / 2⌋₊ : ℝ) ≤ q := by
    linarith [Nat.floor_le (show 0 ≤ q / 2 by linarith)]
  have hqk : q ≤ 2 * (⌊q / 2⌋₊ : ℝ) + 2 := by
    linarith [Nat.lt_floor_add_one (q / 2)]
  obtain ⟨hθ0, hθ1, -⟩ := interp_theta hk hkq hqk
  exact (lpNorm_complexSchattenNorm_le_interp hk hkq hqk x).trans (mul_le_mul_of_nonneg_right
    (evenKhintchineConst_interp_le hk hkq hθ0 hθ1) (Real.sqrt_nonneg _))

/-- **Type 2 of `S_q`**, `q ≥ 2`, real matrices, with the constant `√(q + 1)`. -/
theorem lpNorm_schattenNorm_le {q : ℝ} (hq : 2 ≤ q) (x : Fin N → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin N → Bool => ∑ i, coin (ε i) • x i) ≤
      √(q + 1) * √(∑ i, schattenNorm (ENNReal.ofReal q) (x i) ^ 2) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hs : ∀ ε : Fin N → Bool, (∑ i, coin (ε i) • x i).map Complex.ofReal =
      ∑ i, coin (ε i) • (x i).map Complex.ofReal := fun ε => by
    ext a b
    simp [Matrix.sum_apply]
  have h := lpNorm_complexSchattenNorm_le hq fun i => (x i).map Complex.ofReal
  simpa only [SignCube.lpNorm, ← hs, complexSchattenNorm_map_ofReal hq0] using h

/-- **Type 2 of the Schatten classes** (Tomczak-Jaegermann (1974), Theorem 3.1 (ii)): for `q ≥ 2`,
`S_q` has type 2 with a constant; here `√(q + 1)`, for real square matrices of every size. -/
theorem isTypeTwoBound_schattenSpace {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)] :
    IsTypeTwoBound (SchattenSpace (ENNReal.ofReal q) n n) √(q + 1) := fun _ x =>
  (lpNorm_mono_exponent (fun _ => norm_nonneg _) two_pos hq _).trans
    (lpNorm_schattenNorm_le hq fun i => SchattenSpace.ofMatrix.symm (x i))

end BanachProbability
