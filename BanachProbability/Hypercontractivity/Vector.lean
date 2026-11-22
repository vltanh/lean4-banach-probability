module

public import BanachProbability.Hypercontractivity.TwoPoint
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.MeanInequalities

/-!
# Hypercontractivity of Rademacher sums in seminormed spaces

For a seminorm `S` on a real vector space `E` (no completeness, no quotient), `1 < p ≤ q` and
`ρ = √((p − 1) / (q − 1))`:

* the vector two-point inequality `‖a + ρ b ε‖_{L^q (S)} ≤ ‖a + b ε‖_{L^p (S)}`
  (`twoPoint_seminorm`): with `α = S (a + b)`, `β = S (a − b)`, the triangle inequality applied to
  `a ± ρ b = ((1 ± ρ)/2)(a + b) + ((1 ∓ ρ)/2)(a − b)` gives `S (a ± ρ b) ≤ A ± ρ B` with
  `A = (α + β)/2`, `B = (α − β)/2`, `|B| ≤ A`, and the scalar inequality (`twoPoint`) for
  `A + B ε` concludes;
* the affine hypercontractive inequality
  `‖c + ρ Σ_i ε_i x_i‖_{L^q (S)} ≤ ‖c + Σ_i ε_i x_i‖_{L^p (S)}` (`hypercontractive_affine`), by
  induction on the number of signs: split off the first sign, bound the inner `L^q` norm by the
  induction hypothesis with the constant `c + ρ η x₀`, and close the step with the vector
  two-point inequality in the space of functions of the remaining signs with the seminorm
  `L^p` (Minkowski's inequality, `Real.Lp_add_le`; the seminorm is built here, together with the
  splitting of the cube average along the first sign).

This is vector-valued hypercontractivity, due to C. Borell, *On the integrability of Banach space
valued Walsh polynomials*, Séminaire de Probabilités XIII (1979). The scalar two-point inequality
is that of R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1 (real-valued functions
only); its passage to seminormed spaces through the triangle inequality and the tensorisation on
affine Rademacher sums are the standard argument, with no noise operator.
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The cube average and `L^p` norms of `E`-valued functions -/

/-- Splitting off the first sign: `E g = (E g (1, ·) + E g (−1, ·)) / 2`. -/
private theorem avg_cons {N : ℕ} (g : (Fin (N + 1) → Bool) → ℝ) :
    avg g = (avg (fun ε => g (Fin.cons true ε)) + avg (fun ε => g (Fin.cons false ε))) / 2 := by
  unfold avg
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp g, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, pow_succ]
  ring

private theorem avg_const' {N : ℕ} (k : ℝ) : avg (fun _ : Fin N → Bool => k) = k := by
  simp [avg, Finset.card_univ, Fintype.card_bool]

private theorem lpNorm_nonneg' (S : Seminorm ℝ E) (p : ℝ) {N : ℕ} (X : (Fin N → Bool) → E) :
    0 ≤ SignCube.lpNorm S p X :=
  Real.rpow_nonneg (avg_nonneg fun _ => Real.rpow_nonneg (apply_nonneg S _) _) _

private theorem lpNorm_rpow (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) {N : ℕ}
    (X : (Fin N → Bool) → E) : SignCube.lpNorm S p X ^ p = avg (fun ε => S (X ε) ^ p) := by
  rw [SignCube.lpNorm, one_div,
    Real.rpow_inv_rpow (avg_nonneg fun _ => Real.rpow_nonneg (apply_nonneg S _) _) hp.ne']

/-- The `L^p` norm over `N + 1` signs, from the `L^p` norms of the two restrictions. -/
private theorem lpNorm_cons (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) {N : ℕ}
    (X : (Fin (N + 1) → Bool) → E) :
    SignCube.lpNorm S p X = ((SignCube.lpNorm S p (fun ε => X (Fin.cons true ε)) ^ p +
      SignCube.lpNorm S p (fun ε => X (Fin.cons false ε)) ^ p) / 2) ^ (1 / p) := by
  rw [lpNorm_rpow S hp, lpNorm_rpow S hp, SignCube.lpNorm, avg_cons]

private theorem lpNorm_const (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) {N : ℕ} (c : E) :
    SignCube.lpNorm S p (fun _ : Fin N → Bool => c) = S c := by
  rw [SignCube.lpNorm, avg_const', one_div, Real.rpow_rpow_inv (apply_nonneg S c) hp.ne']

/-- Minkowski's inequality for the `L^p` norm on the cube. -/
private theorem lpNorm_add_le' (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p) {N : ℕ}
    (X Y : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (X + Y) ≤ SignCube.lpNorm S p X + SignCube.lpNorm S p Y := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have key : ∀ Z : (Fin N → Bool) → E, SignCube.lpNorm S p Z =
      (∑ ε, |S (Z ε)| ^ p) ^ (1 / p) * ((2 : ℝ) ^ N)⁻¹ ^ (1 / p) := fun Z => by
    simp only [SignCube.lpNorm, avg, abs_of_nonneg (apply_nonneg S _), div_eq_mul_inv]
    exact Real.mul_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (apply_nonneg S _) _)
      (by positivity)
  rw [key, key, key, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (∑ ε, |S ((X + Y) ε)| ^ p) ^ (1 / p)
      ≤ (∑ ε, |S (X ε) + S (Y ε)| ^ p) ^ (1 / p) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
          (Finset.sum_le_sum fun ε _ => Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le)
          (by positivity)
        rw [abs_of_nonneg (apply_nonneg S _),
          abs_of_nonneg (add_nonneg (apply_nonneg S _) (apply_nonneg S _)), Pi.add_apply]
        exact map_add_le_add S _ _
    _ ≤ (∑ ε, |S (X ε)| ^ p) ^ (1 / p) + (∑ ε, |S (Y ε)| ^ p) ^ (1 / p) :=
        Real.Lp_add_le _ _ _ hp

private theorem lpNorm_smul' (S : Seminorm ℝ E) {p : ℝ} (hp : 0 < p) {N : ℕ} (c : ℝ)
    (X : (Fin N → Bool) → E) :
    SignCube.lpNorm S p (c • X) = ‖c‖ * SignCube.lpNorm S p X := by
  have e : ∀ ε, S ((c • X) ε) ^ p = ‖c‖ ^ p * S (X ε) ^ p := fun ε => by
    rw [Pi.smul_apply, map_smul_eq_mul, Real.mul_rpow (norm_nonneg c) (apply_nonneg S _)]
  simp only [SignCube.lpNorm, e, avg_const_mul]
  rw [Real.mul_rpow (by positivity) (avg_nonneg fun _ => Real.rpow_nonneg (apply_nonneg S _) _),
    ← Real.rpow_mul (norm_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `L^p` seminorm `X ↦ (E S (X ε)^p)^{1/p}` on `E`-valued functions of `N` signs, `p ≥ 1`. -/
private noncomputable def cubeLpSeminorm (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p) (N : ℕ) :
    Seminorm ℝ ((Fin N → Bool) → E) :=
  Seminorm.of (SignCube.lpNorm S p) (lpNorm_add_le' S hp)
    (lpNorm_smul' S (zero_lt_one.trans_le hp))

private theorem cubeLpSeminorm_apply (S : Seminorm ℝ E) {p : ℝ} (hp : 1 ≤ p) {N : ℕ}
    (X : (Fin N → Bool) → E) : cubeLpSeminorm S hp N X = SignCube.lpNorm S p X :=
  rfl

/-! ### The vector two-point inequality and its tensorisation -/

/-- **The vector two-point inequality** for a seminorm `S`:
`((S (a + ρb)^q + S (a − ρb)^q) / 2)^{1/q} ≤ ((S (a + b)^p + S (a − b)^p) / 2)^{1/p}`. -/
theorem twoPoint_seminorm (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (a b : E) :
    ((S (a + √((p - 1) / (q - 1)) • b) ^ q + S (a - √((p - 1) / (q - 1)) • b) ^ q) / 2) ^ (1 / q) ≤
      ((S (a + b) ^ p + S (a - b) ^ p) / 2) ^ (1 / p) := by
  set ρ := √((p - 1) / (q - 1)) with hρ
  have hq1 : 0 < q - 1 := by linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    exact (Real.sqrt_le_sqrt ((div_le_one hq1).2 (by linarith))).trans_eq Real.sqrt_one
  have hα := apply_nonneg S (a + b)
  have hβ := apply_nonneg S (a - b)
  -- `a ± ρ b = ((1 ± ρ)/2)(a + b) + ((1 ∓ ρ)/2)(a − b)` and the triangle inequality
  have hcomb : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s • (a + b) + t • (a - b)) ≤
      s * S (a + b) + t * S (a - b) := fun s t hs ht => by
    refine (map_add_le_add S _ _).trans_eq ?_
    rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hplus : S (a + ρ • b) ≤
      (S (a + b) + S (a - b)) / 2 + ρ * ((S (a + b) - S (a - b)) / 2) := by
    have e : a + ρ • b = ((1 + ρ) / 2) • (a + b) + ((1 - ρ) / 2) • (a - b) := by module
    rw [e]
    refine (hcomb _ _ (by linarith) (by linarith)).trans_eq ?_
    ring
  have hminus : S (a - ρ • b) ≤
      (S (a + b) + S (a - b)) / 2 - ρ * ((S (a + b) - S (a - b)) / 2) := by
    have e : a - ρ • b = ((1 - ρ) / 2) • (a + b) + ((1 + ρ) / 2) • (a - b) := by module
    rw [e]
    refine (hcomb _ _ (by linarith) (by linarith)).trans_eq ?_
    ring
  -- the scalar two-point inequality for `A + B ε`, `A = (α + β)/2`, `B = (α − β)/2`
  have hAB : |(S (a + b) - S (a - b)) / 2| ≤ (S (a + b) + S (a - b)) / 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have key := twoPoint hp hpq hAB
  rw [twoPointNorm, twoPointNorm, ← hρ,
    show (S (a + b) + S (a - b)) / 2 + (S (a + b) - S (a - b)) / 2 = S (a + b) by ring,
    show (S (a + b) + S (a - b)) / 2 - (S (a + b) - S (a - b)) / 2 = S (a - b) by ring] at key
  have hq0 : 0 ≤ q := by linarith
  refine le_trans (Real.rpow_le_rpow ?_ ?_ (div_nonneg zero_le_one hq0)) key
  · exact div_nonneg (add_nonneg (Real.rpow_nonneg (apply_nonneg S _) _)
      (Real.rpow_nonneg (apply_nonneg S _) _)) zero_le_two
  · exact div_le_div_of_nonneg_right (add_le_add
      (Real.rpow_le_rpow (apply_nonneg S _) hplus hq0)
      (Real.rpow_le_rpow (apply_nonneg S _) hminus hq0)) zero_le_two

/-- **Affine hypercontractivity** of Rademacher sums in a seminormed space:
`‖c + ρ Σ_i ε_i x_i‖_{L^q} ≤ ‖c + Σ_i ε_i x_i‖_{L^p}`, `ρ = √((p − 1) / (q − 1))`. -/
theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set ρ := √((p - 1) / (q - 1)) with hρ
  induction n generalizing c with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, add_zero,
      lpNorm_const S hq0, lpNorm_const S hp0, le_refl]
  | succ n ih =>
    -- split off the first sign `η`; the remaining sum is `Σ' (ε) = Σ_i ε_i x_{i+1}`
    have hsplit : ∀ (r : ℝ) (η : Bool) (ε : Fin n → Bool),
        c + r • ∑ i, coin ((Fin.cons η ε : Fin (n + 1) → Bool) i) • x i =
          (c + (r * coin η) • x 0) + r • ∑ i, coin (ε i) • x i.succ := fun r η ε => by
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, smul_add, mul_smul]
      abel
    have hsplit1 : ∀ (η : Bool) (ε : Fin n → Bool),
        c + ∑ i, coin ((Fin.cons η ε : Fin (n + 1) → Bool) i) • x i =
          (c + coin η • x 0) + ∑ i, coin (ε i) • x i.succ := fun η ε => by
      simpa using hsplit 1 η ε
    -- the space of functions of the remaining signs, with the `L^p` seminorm
    set N := cubeLpSeminorm S (le_of_lt hp) n
    set u : (Fin n → Bool) → E := fun ε => c + ∑ i, coin (ε i) • x i.succ
    set v : (Fin n → Bool) → E := fun _ => x 0
    -- the induction hypothesis with the constant `c + ρ η x₀`
    have hih : ∀ η : Bool, SignCube.lpNorm S q (fun ε : Fin n → Bool =>
        c + ρ • ∑ i, coin ((Fin.cons η ε : Fin (n + 1) → Bool) i) • x i) ≤
          N (u + (ρ * coin η) • v) := fun η => by
      have h := ih (c + (ρ * coin η) • x 0) (fun i => x i.succ)
      simp only [← hsplit] at h
      refine h.trans_eq ?_
      rw [cubeLpSeminorm_apply]
      congr 1
      funext ε
      simp only [u, v, Pi.add_apply, Pi.smul_apply]
      abel
    have hval : ∀ η : Bool, SignCube.lpNorm S p (fun ε : Fin n → Bool =>
        c + ∑ i, coin ((Fin.cons η ε : Fin (n + 1) → Bool) i) • x i) = N (u + coin η • v) :=
      fun η => by
        rw [cubeLpSeminorm_apply]
        congr 1
        funext ε
        simp only [u, v, hsplit1, Pi.add_apply, Pi.smul_apply]
        abel
    rw [lpNorm_cons S hq0, lpNorm_cons S hp0]
    rw [hval true, hval false, coin_true, coin_false, one_smul, neg_one_smul, ← sub_eq_add_neg]
    -- the vector two-point inequality in `((Fin n → Bool) → E, N)`
    have h2 := twoPoint_seminorm N hp hpq u v
    refine le_trans ?_ h2
    refine Real.rpow_le_rpow (div_nonneg (add_nonneg (Real.rpow_nonneg (lpNorm_nonneg' S q _) _)
      (Real.rpow_nonneg (lpNorm_nonneg' S q _) _)) zero_le_two) ?_ (div_nonneg zero_le_one hq0.le)
    have ht := hih true
    have hf := hih false
    rw [coin_true, mul_one] at ht
    rw [coin_false, mul_neg_one, neg_smul, ← sub_eq_add_neg] at hf
    exact div_le_div_of_nonneg_right (add_le_add
      (Real.rpow_le_rpow (lpNorm_nonneg' S q _) ht hq0.le)
      (Real.rpow_le_rpow (lpNorm_nonneg' S q _) hf hq0.le)) zero_le_two

end BanachProbability
