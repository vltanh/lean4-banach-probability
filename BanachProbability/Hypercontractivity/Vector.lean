module

public import BanachProbability.Hypercontractivity.TwoPoint
public import BanachProbability.SignCube.LpSeminorm
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Hypercontractivity of Rademacher sums in seminormed spaces

C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire de
Probabilités XIII, Lecture Notes in Math. 721 (1979), 1–3: the inequality (1.1) of Theorem 1.1,
by the argument of its §2, for Walsh polynomials of degree at most `1` (the closure `W̄_d (E)`,
the degrees `d ≥ 2`, exponents `p ≤ 1` and the exponential integrability are not formalized).
For a seminorm `S` on a real vector space `E` (no completeness, no quotient), `1 < p ≤ q` and
`ρ = √((p − 1) / (q − 1))`, the largest admissible value of Borell's `λ` (`|λ| ≤ ρ`):

* Borell's operator on functions of one sign, with the kernel
  `K (x, y) = e₀ (x) e₀ (y) + ρ e₁ (x) e₁ (y) = 1 + ρ x y`: `K̄ g (x) = E_y [K (x, y) g (y)]`
  (`kBar`), and its tensor powers `⊗ⁿ K̄` on functions of `n` signs, with the kernel
  `Π_i (1 + ρ x_i y_i)` (`kBarTensor`: `⊗ⁿ K̄` in the last `n` signs, then `K̄` in the first);
* the elementary inequality `‖K̄ g‖_{L^q} ≤ ‖g‖_{L^p}` for real `g` (`kBar_twoPoint`): with
  `c₀ = (g (1) + g (−1)) / 2`, `c₁ = (g (1) − g (−1)) / 2`, it is
  `[(|c₀ + ρ c₁|^q + |c₀ − ρ c₁|^q) / 2]^{1/q} ≤ [(|c₀ + c₁|^p + |c₀ − c₁|^p) / 2]^{1/p}`;
* `‖(⊗ⁿ K̄) f‖_{L^q} ≤ ‖f‖_{L^p}` for real `f` (`kBarTensor_lpNorm_le_real`), which Borell
  obtains from the elementary inequality by the Segal lemma; here by induction on `n`: the
  elementary inequality in the first sign, Minkowski's inequality in `L^{q/p}` to exchange the
  `L^p` norm over the first sign with the `L^q` norm over the others (`avg_twoPoint_le`), and the
  induction hypothesis;
* `K ≥ 0`: `S ((⊗ⁿ K̄) f (ε)) ≤ (⊗ⁿ K̄) (S ∘ f) (ε)` (`seminorm_kBarTensor_le`), so the Segal
  lemma applied to `S ∘ f` gives `‖(⊗ⁿ K̄) f‖_{L^q (S)} ≤ ‖f‖_{L^p (S)}` for `E`-valued `f`
  (`kBarTensor_lpNorm_le`);
* Borell's eigenvalue relation `(⊗ⁿ K̄) e_α = ρ^{|α|} e_α` for `|α| ≤ 1`:
  `(⊗ⁿ K̄) (c + Σ_i ε_i x_i) = c + ρ Σ_i ε_i x_i` (`kBarTensor_affine`), so
  `‖c + ρ Σ_i ε_i x_i‖_{L^q (S)} ≤ ‖c + Σ_i ε_i x_i‖_{L^p (S)}` (`hypercontractive_affine`),
  Borell's (2.1) for `E`-valued coefficients supported on `|α| ≤ 1`; its case `c = 0` is (1.1) for
  `d = 1`, the statement of `kahaneKhintchine_hypercontractive`, which is proved in
  `KahaneKhintchine/Basic.lean` by another tensorisation (`Hypercontractivity/HeatSemigroup.lean`).

The vector two-point inequality `‖a + ρ b ε‖_{L^q (S)} ≤ ‖a + b ε‖_{L^p (S)}`
(`twoPoint_seminorm`) is the case of one sign: `K ≥ 0`, that is, the triangle inequality applied
to `a ± ρ b = ((1 ± ρ)/2)(a + b) + ((1 ∓ ρ)/2)(a − b)`, and the scalar two-point inequality
(`twoPoint`) for the nonnegative two-point function `A + B ε`, `A = (S (a + b) + S (a − b))/2`,
`B = (S (a + b) − S (a − b))/2`. For `S = |·|` it is the elementary inequality for all real `c₀`,
`c₁`.

Borell cites the elementary inequality as well known (L. Gross, *Logarithmic Sobolev
inequalities*, Amer. J. Math. 97 (1975), Theorem 3; W. Beckner, *Inequalities in Fourier
analysis*, Ann. of Math. 102 (1975), p. 180) and the Segal lemma from Beckner (Lemma 2); neither
was obtained. The elementary inequality is proved from its case of nonnegative functions
(`twoPoint`: A. Bonami (1970), in R. O'Donnell's proof, *Analysis of Boolean Functions* (2014),
§10.1, after S. Janson) by `K ≥ 0`, the reduction of O'Donnell's Exercise 9.7; the tensorisation
by the induction of O'Donnell's Exercise 10.3 (the one-variable inequality, then Minkowski's
inequality in the form of his Exercise 10.1,
`‖ ‖f (X, Y)‖_{p, Y} ‖_{q, X} ≤ ‖ ‖f (X, Y)‖_{q, X} ‖_{p, Y}` for `p ≤ q`, then the induction
hypothesis).
-/

@[expose] public section

namespace BanachProbability

open SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The vector two-point inequality -/

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

/-! ### Borell's operator `K̄` and its tensor powers -/

theorem kBarTensor_zero (ρ : ℝ) (f : (Fin 0 → Bool) → E) : kBarTensor ρ 0 f = f := rfl

theorem kBarTensor_succ (ρ : ℝ) {n : ℕ} (f : (Fin (n + 1) → Bool) → E) (ε : Fin (n + 1) → Bool) :
    kBarTensor ρ (n + 1) f ε =
      kBar ρ (fun η => kBarTensor ρ n (fun ε' => f (Fin.cons η ε')) (Fin.tail ε)) (ε 0) := rfl

/-- Borell's `(⊗ⁿ K̄) e_α = ρ^{|α|} e_α` for the Walsh functions of degree at most `1`:
`(⊗ⁿ K̄) (c + Σ_i ε_i x_i) = c + ρ Σ_i ε_i x_i`. -/
theorem kBarTensor_affine (ρ : ℝ) {n : ℕ} (c : E) (x : Fin n → E) :
    kBarTensor ρ n (fun ε => c + ∑ i, coin (ε i) • x i) =
      fun ε => c + ρ • ∑ i, coin (ε i) • x i := by
  induction n generalizing c with
  | zero => funext ε; simp [kBarTensor_zero]
  | succ n ih =>
    funext ε
    -- split off the first sign: `c + Σ_i ε_i x_i = (c + ε₀ x₀) + Σ_i ε_{i+1} x_{i+1}`
    have hf : ∀ (η : Bool) (ε' : Fin n → Bool),
        c + ∑ i, coin ((Fin.cons η ε' : Fin (n + 1) → Bool) i) • x i =
          (c + coin η • x 0) + ∑ i, coin (ε' i) • x i.succ := fun η ε' => by
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      abel
    have hT : ∀ η : Bool, kBarTensor ρ n
        (fun ε' => c + ∑ i, coin ((Fin.cons η ε' : Fin (n + 1) → Bool) i) • x i) (Fin.tail ε) =
          (c + coin η • x 0) + ρ • ∑ i : Fin n, coin (ε i.succ) • x i.succ := fun η => by
      simp only [hf]
      exact congrFun (ih (c + coin η • x 0) (fun i => x i.succ)) (Fin.tail ε)
    rw [kBarTensor_succ]
    simp only [hT, kBar, coin_true, coin_false, Fin.sum_univ_succ (f := fun i => coin (ε i) • x i)]
    module

/-- **Borell's elementary inequality**, `‖K̄ g‖_{L^q} ≤ ‖g‖_{L^p}` for real `g` and `1 < p ≤ q`,
`ρ = √((p − 1) / (q − 1))`: with `c₀ = (g (1) + g (−1)) / 2`, `c₁ = (g (1) − g (−1)) / 2`,
`K̄ g (±1) = c₀ ± ρ c₁` and `g (±1) = c₀ ± c₁`, and this is `twoPoint_seminorm` for the absolute
value. -/
theorem kBar_twoPoint {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (g : Bool → ℝ) :
    ((|kBar √((p - 1) / (q - 1)) g true| ^ q + |kBar √((p - 1) / (q - 1)) g false| ^ q) / 2) ^
        (1 / q) ≤ ((|g true| ^ p + |g false| ^ p) / 2) ^ (1 / p) := by
  have h := twoPoint_seminorm (normSeminorm ℝ ℝ) hp hpq ((g true + g false) / 2)
    ((g true - g false) / 2)
  have e1 : kBar √((p - 1) / (q - 1)) g true =
      (g true + g false) / 2 + √((p - 1) / (q - 1)) • ((g true - g false) / 2) := by
    simp only [kBar, coin_true, smul_eq_mul]; ring
  have e2 : kBar √((p - 1) / (q - 1)) g false =
      (g true + g false) / 2 - √((p - 1) / (q - 1)) • ((g true - g false) / 2) := by
    simp only [kBar, coin_false, smul_eq_mul]; ring
  rw [show (g true + g false) / 2 + (g true - g false) / 2 = g true by ring,
    show (g true + g false) / 2 - (g true - g false) / 2 = g false by ring] at h
  simpa only [e1, e2, coe_normSeminorm, Real.norm_eq_abs] using h

/-- **Minkowski's inequality in `L^{q/p}`**, exchanging the `L^p` norm over one sign with the
`L^q` norm over `n` signs (O'Donnell (2014), Exercise 10.1): for `0 < p ≤ q` and real `u`, `v`,
`(E_ε ((|u ε|^p + |v ε|^p) / 2)^{q/p})^{1/q} ≤ ((‖u‖_q^p + ‖v‖_q^p) / 2)^{1/p}`. -/
theorem avg_twoPoint_le {n : ℕ} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (u v : (Fin n → Bool) → ℝ) :
    avg (fun ε => ((|u ε| ^ p + |v ε| ^ p) / 2) ^ (q / p)) ^ (1 / q) ≤
      ((SignCube.lpNorm (normSeminorm ℝ ℝ) q u ^ p +
        SignCube.lpNorm (normSeminorm ℝ ℝ) q v ^ p) / 2) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  set r := q / p with hr_def
  have hr : 1 ≤ r := (one_le_div hp).2 hpq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set N := normSeminorm ℝ ℝ
  have hN : ∀ t : ℝ, N t = |t| := fun t => by simp [N]
  set a : (Fin n → Bool) → ℝ := fun ε => |u ε| ^ p
  set b : (Fin n → Bool) → ℝ := fun ε => |v ε| ^ p
  have ha : ∀ ε, 0 ≤ a ε := fun ε => Real.rpow_nonneg (abs_nonneg _) _
  have hb : ∀ ε, 0 ≤ b ε := fun ε => Real.rpow_nonneg (abs_nonneg _) _
  -- `‖a‖_r = ‖u‖_q^p` and `‖b‖_r = ‖v‖_q^p`
  have hpow : ∀ w : (Fin n → Bool) → ℝ,
      SignCube.lpNorm N r (fun ε => |w ε| ^ p) = SignCube.lpNorm N q w ^ p := fun w => by
    unfold SignCube.lpNorm
    have hA : 0 ≤ avg (fun ε => N (w ε) ^ q) := avg_nonneg fun _ => Real.rpow_nonneg (by simp) _
    have e : ∀ ε, N (|w ε| ^ p) ^ r = N (w ε) ^ q := fun ε => by
      rw [hN, hN, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _),
        hr_def, mul_div_cancel₀ _ hp.ne']
    simp only [e]
    rw [← Real.rpow_mul hA, hr_def]
    congr 1
    field_simp
  -- Minkowski's inequality in `L^r`
  have hM : SignCube.lpNorm N r (fun ε => (a ε + b ε) / 2) ≤
      (SignCube.lpNorm N r a + SignCube.lpNorm N r b) / 2 := by
    have h := lpNorm_add_le N hr ((1 / 2 : ℝ) • a) ((1 / 2 : ℝ) • b)
    rw [← smul_add, lpNorm_smul N hr0, lpNorm_smul N hr0, lpNorm_smul N hr0] at h
    have e : (fun ε => (a ε + b ε) / 2) = (1 / 2 : ℝ) • (a + b) := by
      funext ε; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [e, lpNorm_smul N hr0]
    have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h2] at h ⊢
    linarith
  rw [hpow u, hpow v] at hM
  -- the left side is `‖(a + b) / 2‖_r^{1/p}`
  have hAB : 0 ≤ avg (fun ε => ((a ε + b ε) / 2) ^ r) :=
    avg_nonneg fun ε => Real.rpow_nonneg (by linarith [ha ε, hb ε]) _
  have eL : avg (fun ε => ((|u ε| ^ p + |v ε| ^ p) / 2) ^ (q / p)) ^ (1 / q) =
      SignCube.lpNorm N r (fun ε => (a ε + b ε) / 2) ^ (1 / p) := by
    unfold SignCube.lpNorm
    have e : ∀ ε, N ((a ε + b ε) / 2) ^ r = ((a ε + b ε) / 2) ^ r := fun ε => by
      rw [hN, abs_of_nonneg (by linarith [ha ε, hb ε])]
    simp only [e]
    rw [← Real.rpow_mul hAB]
    congr 1
    rw [hr_def]; field_simp
  rw [eL]
  exact Real.rpow_le_rpow (lpNorm_nonneg (fun t => by simp [hN]) _ _) hM (by positivity)

/-- **`⊗ⁿ K̄` from `L^p` to `L^q`**, which Borell derives from the elementary inequality by the
Segal lemma (W. Beckner (1975), Lemma 2, not obtained): for `1 < p ≤ q`,
`ρ = √((p − 1) / (q − 1))` and real `f` on `n` signs, `‖(⊗ⁿ K̄) f‖_{L^q} ≤ ‖f‖_{L^p}`. By
induction on `n`, as in O'Donnell's Exercise 10.3: with `h (y₀, x) = (⊗ⁿ K̄) (f (y₀, ·)) (x)`,
`‖(⊗ⁿ⁺¹ K̄) f‖_q = ‖ ‖K̄ h (·, x)‖_{q, x₀} ‖_{q, x} ≤ ‖ ‖h (·, x)‖_{p, x₀} ‖_{q, x}` (the elementary
inequality, `kBar_twoPoint`) `≤ ‖ ‖h (x₀, ·)‖_{q, x} ‖_{p, x₀}` (Minkowski, `avg_twoPoint_le`)
`≤ ‖ ‖f (x₀, ·)‖_{p, x} ‖_{p, x₀} = ‖f‖_p` (the induction hypothesis). -/
theorem kBarTensor_lpNorm_le_real {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {n : ℕ}
    (f : (Fin n → Bool) → ℝ) :
    SignCube.lpNorm (normSeminorm ℝ ℝ) q (kBarTensor √((p - 1) / (q - 1)) n f) ≤
      SignCube.lpNorm (normSeminorm ℝ ℝ) p f := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set ρ := √((p - 1) / (q - 1)) with hρ
  set N := normSeminorm ℝ ℝ
  have hN : ∀ t : ℝ, N t = |t| := fun t => by simp [N]
  have hN0 : ∀ t : ℝ, 0 ≤ N t := fun t => by simp [hN]
  induction n with
  | zero =>
    -- functions of no signs are constants
    have e : f = fun _ => f Fin.elim0 := funext fun ε => congrArg f (Subsingleton.elim _ _)
    rw [kBarTensor_zero, e, lpNorm_const (hN0 _) hq0, lpNorm_const (hN0 _) hp0]
  | succ n ih =>
    set h : Bool → (Fin n → Bool) → ℝ := fun η => kBarTensor ρ n (fun ε' => f (Fin.cons η ε'))
    -- `‖(⊗ⁿ⁺¹ K̄) f‖_q^q = E_x (|K̄ h (·, x) (1)|^q + |K̄ h (·, x) (−1)|^q) / 2`
    have hL : SignCube.lpNorm N q (kBarTensor ρ (n + 1) f) = avg (fun ε =>
        (|kBar ρ (fun η => h η ε) true| ^ q + |kBar ρ (fun η => h η ε) false| ^ q) / 2) ^
          (1 / q) := by
      unfold SignCube.lpNorm
      rw [avg_succ]
      congr 1
      simp only [kBarTensor_succ, Fin.cons_zero, Fin.tail_cons, hN]
      rw [← avg_add, div_eq_mul_inv, mul_comm (avg _), ← avg_const_mul]
      congr 1
      funext ε
      ring
    -- the elementary inequality for each `x`
    have h1 : ∀ ε, (|kBar ρ (fun η => h η ε) true| ^ q + |kBar ρ (fun η => h η ε) false| ^ q) / 2
        ≤ ((|h true ε| ^ p + |h false ε| ^ p) / 2) ^ (q / p) := fun ε => by
      have k := kBar_twoPoint hp hpq (fun η => h η ε)
      have hX : 0 ≤ (|kBar ρ (fun η => h η ε) true| ^ q +
          |kBar ρ (fun η => h η ε) false| ^ q) / 2 := by positivity
      have hY : 0 ≤ (|h true ε| ^ p + |h false ε| ^ p) / 2 := by positivity
      have k' := Real.rpow_le_rpow (Real.rpow_nonneg hX _) k hq0.le
      rwa [← Real.rpow_mul hX, one_div_mul_cancel hq0.ne', Real.rpow_one, ← Real.rpow_mul hY,
        one_div_mul_eq_div] at k'
    -- the induction hypothesis for each first sign
    have h2 : ∀ η, SignCube.lpNorm N q (h η) ≤ SignCube.lpNorm N p (fun ε => f (Fin.cons η ε)) :=
      fun η => ih _
    rw [hL, lpNorm_succ hN0 hp0]
    calc avg (fun ε => (|kBar ρ (fun η => h η ε) true| ^ q +
          |kBar ρ (fun η => h η ε) false| ^ q) / 2) ^ (1 / q)
        ≤ avg (fun ε => ((|h true ε| ^ p + |h false ε| ^ p) / 2) ^ (q / p)) ^ (1 / q) :=
          Real.rpow_le_rpow (avg_nonneg fun ε => by positivity) (avg_mono h1) (by positivity)
      _ ≤ ((SignCube.lpNorm N q (h true) ^ p + SignCube.lpNorm N q (h false) ^ p) / 2) ^ (1 / p) :=
          avg_twoPoint_le hp0 hpq _ _
      _ ≤ _ :=
          Real.rpow_le_rpow (div_nonneg (add_nonneg
            (Real.rpow_nonneg (lpNorm_nonneg hN0 _ _) _)
            (Real.rpow_nonneg (lpNorm_nonneg hN0 _ _) _)) zero_le_two)
            (div_le_div_of_nonneg_right (add_le_add
              (Real.rpow_le_rpow (lpNorm_nonneg hN0 _ _) (h2 true) hp0.le)
              (Real.rpow_le_rpow (lpNorm_nonneg hN0 _ _) (h2 false) hp0.le)) zero_le_two)
            (by positivity)

/-- **`K ≥ 0`**: for `0 ≤ ρ ≤ 1` the kernel `Π_i (1 + ρ x_i y_i)` is nonnegative, so for a seminorm
`S`, `S ((⊗ⁿ K̄) f (ε)) ≤ (⊗ⁿ K̄) (S ∘ f) (ε)`: by induction on `n`, the triangle inequality for
`K̄` (whose weights `(1 ± ρ x) / 2` are nonnegative) and its monotonicity. -/
theorem seminorm_kBarTensor_le (S : Seminorm ℝ E) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {n : ℕ}
    (f : (Fin n → Bool) → E) (ε : Fin n → Bool) :
    S (kBarTensor ρ n f ε) ≤ kBarTensor ρ n (fun ε => S (f ε)) ε := by
  have hw : ∀ x : Bool, 0 ≤ 1 + ρ * coin x ∧ 0 ≤ 1 - ρ * coin x := fun x => by
    rcases coin_eq_one_or_eq_neg_one x with h | h <;> rw [h] <;> constructor <;> linarith
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [kBarTensor_succ, kBarTensor_succ]
    obtain ⟨h1, h2⟩ := hw (ε 0)
    -- the triangle inequality for `K̄`, then its monotonicity and the induction hypothesis
    calc S (kBar ρ (fun η => kBarTensor ρ n (fun ε' => f (Fin.cons η ε')) (Fin.tail ε)) (ε 0))
        ≤ (1 / 2) * ((1 + ρ * coin (ε 0)) *
            S (kBarTensor ρ n (fun ε' => f (Fin.cons true ε')) (Fin.tail ε)) +
          (1 - ρ * coin (ε 0)) *
            S (kBarTensor ρ n (fun ε' => f (Fin.cons false ε')) (Fin.tail ε))) := by
          unfold kBar
          rw [map_smul_eq_mul, Real.norm_of_nonneg (by norm_num)]
          gcongr
          refine (map_add_le_add S _ _).trans_eq ?_
          rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg h1, Real.norm_of_nonneg h2]
      _ ≤ (1 / 2) * ((1 + ρ * coin (ε 0)) *
            kBarTensor ρ n (fun ε' => S (f (Fin.cons true ε'))) (Fin.tail ε) +
          (1 - ρ * coin (ε 0)) *
            kBarTensor ρ n (fun ε' => S (f (Fin.cons false ε'))) (Fin.tail ε)) := by
          gcongr
          · exact ih _ _
          · exact ih _ _
      _ = _ := by simp only [kBar, smul_eq_mul]

/-- **Borell's inequality** for the operator `⊗ⁿ K̄` in a seminormed space (Borell 1979, the
operator form of (2.1), for `E`-valued functions): for a seminorm `S`, `1 < p ≤ q`,
`ρ = √((p − 1) / (q − 1))` and
`f : {±1}ⁿ → E`, `‖(⊗ⁿ K̄) f‖_{L^q (S)} ≤ ‖f‖_{L^p (S)}`. Since `K ≥ 0`,
`S ((⊗ⁿ K̄) f) ≤ (⊗ⁿ K̄) (S ∘ f)` (`seminorm_kBarTensor_le`), and the Segal lemma
(`kBarTensor_lpNorm_le_real`) applies to the real function `S ∘ f`. -/
theorem kBarTensor_lpNorm_le (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {n : ℕ}
    (f : (Fin n → Bool) → E) :
    SignCube.lpNorm S q (kBarTensor √((p - 1) / (q - 1)) n f) ≤ SignCube.lpNorm S p f := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ √((p - 1) / (q - 1)) := Real.sqrt_nonneg _
  have hρ1 : √((p - 1) / (q - 1)) ≤ 1 :=
    Real.sqrt_le_one.2 ((div_le_one (by linarith)).2 (by linarith))
  have hS : ∀ x, 0 ≤ S x := apply_nonneg S
  calc SignCube.lpNorm S q (kBarTensor √((p - 1) / (q - 1)) n f)
      ≤ SignCube.lpNorm (normSeminorm ℝ ℝ) q
          (kBarTensor √((p - 1) / (q - 1)) n (fun ε => S (f ε))) := by
        unfold SignCube.lpNorm
        refine Real.rpow_le_rpow (avg_nonneg fun _ => Real.rpow_nonneg (hS _) _)
          (avg_mono fun ε => Real.rpow_le_rpow (hS _) ?_ hq0.le) (by positivity)
        rw [coe_normSeminorm, Real.norm_eq_abs]
        exact (seminorm_kBarTensor_le S hρ0 hρ1 f ε).trans (le_abs_self _)
    _ ≤ SignCube.lpNorm (normSeminorm ℝ ℝ) p (fun ε => S (f ε)) :=
        kBarTensor_lpNorm_le_real hp hpq _
    _ = SignCube.lpNorm S p f := by
        unfold SignCube.lpNorm
        simp only [coe_normSeminorm, Real.norm_eq_abs, abs_of_nonneg (hS _)]

/-- **Affine hypercontractivity** of Rademacher sums in a seminormed space (Borell 1979, (2.1)
for coefficients supported on `|α| ≤ 1`):
`‖c + ρ Σ_i ε_i x_i‖_{L^q} ≤ ‖c + Σ_i ε_i x_i‖_{L^p}`, `ρ = √((p − 1) / (q − 1))`: the case
`f = c + Σ_i ε_i x_i` of `kBarTensor_lpNorm_le`, with `(⊗ⁿ K̄) f = c + ρ Σ_i ε_i x_i`
(`kBarTensor_affine`). -/
theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) := by
  have h := kBarTensor_lpNorm_le S hp hpq (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i)
  rwa [kBarTensor_affine] at h

end BanachProbability
