module

public import BanachProbability.UMD.Maurey.Basic
public import Mathlib.Analysis.Convex.Function

/-!
# Burkholder's characterisation of UMD by zig-zag concave functions

A Banach space `X` is `UMD_p`, `p ∈ (1, ∞)`, if and only if there are `β > 0` and a function
`U : X × X → ℝ` with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, and zig-zag concave:
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]` (`IsZigZagConcave`); then
`UMD_p (X) ≤ β` (D. L. Burkholder, *A geometrical characterization of Banach spaces in which
martingale difference sequences are unconditional*, Ann. Probab. 9 (1981), and *Boundary value
problems and sharp inequalities for martingale transforms*, Ann. Probab. 12 (1984);
Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach spaces I* (2016), Theorem 4.5.6). For a
complex space and `ε` in the closed unit disc of `ℂ` (`IsComplexZigZagConcave`), `U` bounds the
complex constant `UMD_{ℂ,p} (X)` (I. Yaroslavtsev, *Even Fourier multipliers and martingale
transforms in infinite dimensions*, Indag. Math. 29 (2018), Proposition 3.7).

* `U ⇒ UMD_p ≤ β`: on the cube, midpoint concavity along `(± v, ± σ v)` gives
  `E U (f_n, g_n) ≤ U (0, 0) = 0` for a Paley–Walsh martingale `f` and its transform `g`, with no
  measurability needed (`dyadicUMDConst_le_of_isZigZagConcave`); Maurey's theorem gives the full
  constant (`umdConst_le_of_isZigZagConcave`), and its complex version the complex one.
* `UMD_p < ∞ ⇒ U` exists: for `β > UMD_p^Δ (X)`, the Bellman function
  `U (x, y) = sup E [‖y + g‖^p − β^p ‖x + f‖^p]` over Paley–Walsh pairs with predictable
  multipliers in `[−1, 1]` (`bellmanFunction`) is finite (by the contraction principle,
  `lpNorm_paleyWalsh_mul_le`), midpoint concave along zig-zag lines (by splicing) and locally
  bounded, hence concave there (Bernstein–Doetsch, `concaveOn_of_midpoint`).
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

open SignCube

/-- `U : X × X → ℝ` is zig-zag concave for the obstacle `‖y‖^p − β^p ‖x‖^p` (real scalars):
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]`, `U (0, 0) = 0`, and
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
def IsZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℝ), |ε| ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- The complex version: `ε` ranges over the closed unit disc. -/
def IsComplexZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℂ), ‖ε‖ ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

section BernsteinDoetsch

/-- Jensen's inequality for dyadic weights: a midpoint concave function satisfies
`f (t a + (1 − t) b) ≥ t f a + (1 − t) f b` for `t = k / 2^m ∈ [0, 1]` (induction on `m`: the
weights with this property contain `0` and `1` and are closed under midpoints). -/
private theorem zzg_dyadic {f : ℝ → ℝ} (hmid : ∀ a b, (f a + f b) / 2 ≤ f ((a + b) / 2)) :
    ∀ (m k : ℕ), k ≤ 2 ^ m → ∀ a b : ℝ,
      (k / 2 ^ m : ℝ) * f a + (1 - k / 2 ^ m) * f b ≤ f (k / 2 ^ m * a + (1 - k / 2 ^ m) * b) := by
  have hD : ∀ s t : ℝ, (∀ a b, s * f a + (1 - s) * f b ≤ f (s * a + (1 - s) * b)) →
      (∀ a b, t * f a + (1 - t) * f b ≤ f (t * a + (1 - t) * b)) →
      ∀ a b, (s + t) / 2 * f a + (1 - (s + t) / 2) * f b ≤
        f ((s + t) / 2 * a + (1 - (s + t) / 2) * b) := by
    intro s t hs ht a b
    have h := hmid (s * a + (1 - s) * b) (t * a + (1 - t) * b)
    rw [show (s * a + (1 - s) * b + (t * a + (1 - t) * b)) / 2 =
      (s + t) / 2 * a + (1 - (s + t) / 2) * b by ring] at h
    linarith [hs a b, ht a b]
  have h0 : ∀ a b, (0 : ℝ) * f a + (1 - 0) * f b ≤ f (0 * a + (1 - 0) * b) := fun a b => by simp
  have h1 : ∀ a b, (1 : ℝ) * f a + (1 - 1) * f b ≤ f (1 * a + (1 - 1) * b) := fun a b => by simp
  intro m
  induction m with
  | zero =>
    intro k hk a b
    interval_cases k <;> simp
  | succ m ih =>
    intro k hk
    by_cases hkm : k ≤ 2 ^ m
    · have := hD _ _ (ih k hkm) h0
      rwa [show ((k : ℝ) / 2 ^ m + 0) / 2 = k / 2 ^ (m + 1) by rw [pow_succ]; ring] at this
    · have hk' : k - 2 ^ m ≤ 2 ^ m := by rw [pow_succ] at hk; omega
      have := hD _ _ (ih _ hk') h1
      rwa [show (((k - 2 ^ m : ℕ) : ℝ) / 2 ^ m + 1) / 2 = k / 2 ^ (m + 1) by
        rw [Nat.cast_sub (by omega), pow_succ]; push_cast; field_simp; ring] at this

/-- The Bernstein–Doetsch estimate: a midpoint concave function bounded below by `C` on the ball
of radius `δ` about `x` satisfies `|f (x + h / 2^m) − f x| ≤ (f x − C) / 2^m` for `|h| < δ`; in
particular it is continuous. -/
private theorem zzg_continuous_of_midpoint {f : ℝ → ℝ}
    (hmid : ∀ a b, (f a + f b) / 2 ≤ f ((a + b) / 2))
    (hbdd : ∀ x, ∃ U ∈ nhds x, ∃ C : ℝ, ∀ y ∈ U, C ≤ f y) : Continuous f := by
  have hdy := zzg_dyadic hmid
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨V, hV, C, hC⟩ := hbdd x
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hmem : ∀ h : ℝ, |h| < δ → C ≤ f (x + h) := fun h hh =>
    hC _ (hball (by simpa [Metric.mem_ball, Real.dist_eq] using hh))
  have key : ∀ (m : ℕ) (h : ℝ), |h| < δ → |f (x + h / 2 ^ m) - f x| ≤ (f x - C) / 2 ^ m := by
    intro m h hh
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    have ht := hdy m 1 Nat.one_le_two_pow
    simp only [Nat.cast_one] at ht
    have e1 : ∀ h' : ℝ, 1 / 2 ^ m * (x + h') + (1 - 1 / 2 ^ m) * x = x + h' / 2 ^ m := by
      intro h'; field_simp; ring
    have hp := ht (x + h) x
    have hn := ht (x + -h) x
    rw [e1] at hp hn
    have hm := hmid (x + h / 2 ^ m) (x + -h / 2 ^ m)
    rw [show (x + h / 2 ^ m + (x + -h / 2 ^ m)) / 2 = x by ring] at hm
    have ht0 : (0 : ℝ) ≤ 1 / 2 ^ m := by positivity
    have hCp := mul_le_mul_of_nonneg_left (hmem h hh) ht0
    have hCn := mul_le_mul_of_nonneg_left (hmem (-h) (by rwa [abs_neg])) ht0
    rw [abs_le, show (f x - C) / 2 ^ m = 1 / 2 ^ m * f x - 1 / 2 ^ m * C by ring]
    constructor <;> linarith
  rw [Metric.continuousAt_iff]
  intro e he
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((f x - C) / e) (one_lt_two : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨δ / 2 ^ m, by positivity, fun y hy => ?_⟩
  have hh : |2 ^ m * (y - x)| < δ := by
    rw [abs_mul, abs_of_pos hpos, ← lt_div_iff₀' hpos]
    rwa [Real.dist_eq] at hy
  have := key m _ hh
  rw [mul_div_cancel_left₀ _ hpos.ne', add_sub_cancel] at this
  rw [Real.dist_eq]
  calc |f y - f x| ≤ (f x - C) / 2 ^ m := this
    _ < e := by rw [div_lt_iff₀ hpos]; rwa [div_lt_iff₀ he, mul_comm] at hm

/-- **Bernstein–Doetsch**: a midpoint concave function on `ℝ` that is locally bounded below is
concave (F. Bernstein, G. Doetsch, *Zur Theorie der konvexen Funktionen*, Math. Ann. 76 (1915)):
midpoint concavity gives Jensen's inequality for dyadic weights, local boundedness below then gives
continuity, and concavity follows by density of the dyadic weights. -/
theorem concaveOn_of_midpoint {f : ℝ → ℝ} (hmid : ∀ a b, (f a + f b) / 2 ≤ f ((a + b) / 2))
    (hbdd : ∀ x, ∃ U ∈ nhds x, ∃ C : ℝ, ∀ y ∈ U, C ≤ f y) : ConcaveOn ℝ Set.univ f := by
  have hdy := zzg_dyadic hmid
  have hcont := zzg_continuous_of_midpoint hmid hbdd
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  obtain rfl : t = 1 - s := by linarith
  simp only [smul_eq_mul]
  have hs1 : s ≤ 1 := by linarith
  set φ : ℝ → ℝ := fun r => f (r * a + (1 - r) * b) - (r * f a + (1 - r) * f b) with hφ
  have hφc : Continuous φ := (hcont.comp (by fun_prop)).sub (by fun_prop)
  -- the dyadic approximations `⌊s 2^m⌋ / 2^m` of `s` from below
  set r : ℕ → ℝ := fun m => (⌊s * 2 ^ m⌋₊ : ℝ) / 2 ^ m with hr
  have hr_le : ∀ m, r m ≤ s := fun m => by
    rw [hr, div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hr_ge : ∀ m, s - (1 / 2) ^ m ≤ r m := fun m => by
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    rw [hr, le_div_iff₀ hpos, sub_mul, one_div_pow, one_div_mul_cancel hpos.ne']
    linarith [Nat.lt_floor_add_one (s * 2 ^ m)]
  have hlim : Filter.Tendsto r Filter.atTop (nhds s) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hr_ge hr_le
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hφr : ∀ m, 0 ≤ φ (r m) := fun m => by
    have hk : ⌊s * 2 ^ m⌋₊ ≤ 2 ^ m := Nat.floor_le_of_le (by
      push_cast
      exact mul_le_of_le_one_left (by positivity) hs1)
    have := hdy m _ hk a b
    simp only [hφ, hr]
    linarith
  have := ge_of_tendsto ((hφc.tendsto s).comp hlim) (Filter.Eventually.of_forall hφr)
  simp only [hφ] at this
  linarith

end BernsteinDoetsch

section Cube

/-- `E ‖F‖^p = ‖F‖_p^p`. -/
private theorem zzg_avg_rpow {E : Type*} [SeminormedAddCommGroup E] {N : ℕ} {p : ℝ} (hp : 0 < p)
    (F : (Fin N → Bool) → E) :
    avg (fun ε => ‖F ε‖ ^ p) = SignCube.lpNorm (fun x => ‖x‖) p F ^ p := by
  rw [SignCube.lpNorm, ← Real.rpow_mul (avg_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Midpoint concavity at `0` of a concave function: `g v + g (−v) ≤ 2 g 0`. -/
private theorem zzg_mid_of_concaveOn {g : E → ℝ} (hg : ConcaveOn ℝ Set.univ g) (v : E) :
    g v + g (-v) ≤ 2 * g 0 := by
  have h := hg.2 (Set.mem_univ v) (Set.mem_univ (-v)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [smul_neg, add_neg_cancel, smul_eq_mul, smul_eq_mul] at h
  linarith

/-- Burkholder's step on the cube: if `U (x + v, y + w) + U (x − v, y − w) ≤ 2 U (x, y)` for the
increments `(v, w) = (ξ_k (ε), ζ_k (ε))`, then `n ↦ E U (f_n, g_n)` is nonincreasing for the
Paley–Walsh martingales `f = Σ ε_k ξ_k` and `g = Σ ε_k ζ_k` (pair `ε` with its flip at `k`:
`f_k`, `g_k`, `ξ_k`, `ζ_k` do not change and `ε_k` changes sign), so `E U (f_n, g_n) ≤ U (0, 0)`;
no measurability is involved. -/
private theorem zzg_avg_le_of_mid {N : ℕ} {U : E → E → ℝ} {ξ ζ : Fin N → (Fin N → Bool) → E}
    (hξ : IsPredictable ξ) (hζ : IsPredictable ζ)
    (hmid : ∀ k ε (x y : E), U (x + ξ k ε) (y + ζ k ε) + U (x - ξ k ε) (y - ζ k ε) ≤ 2 * U x y)
    (n : ℕ) : avg (fun ε => U (paleyWalsh ξ n ε) (paleyWalsh ζ n ε)) ≤ U 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    simp only [paleyWalsh_succ]
    split_ifs with hn
    · generalize hK : (⟨n, hn⟩ : Fin N) = K
      have hKn : K.val = n := by rw [← hK]
      set F : (Fin N → Bool) → ℝ := fun ε => U (paleyWalsh ξ n ε + coin (ε K) • ξ K ε)
        (paleyWalsh ζ n ε + coin (ε K) • ζ K ε) with hF
      have hpt : ∀ ε, F ε + F (SignCube.flip K ε) ≤
          2 * U (paleyWalsh ξ n ε) (paleyWalsh ζ n ε) := by
        intro ε
        have hlt : ∀ j : Fin N, j.val < n → SignCube.flip K ε j = ε j := fun j hj =>
          flip_apply_of_ne (fun h => by subst h; omega) ε
        have hf := hξ.isAdapted_paleyWalsh n _ _ hlt
        have hg := hζ.isAdapted_paleyWalsh n _ _ hlt
        have hξK := hξ K _ _ fun j hj => flip_apply_of_ne (ne_of_lt hj) ε
        have hζK := hζ K _ _ fun j hj => flip_apply_of_ne (ne_of_lt hj) ε
        have hm := hmid K ε (paleyWalsh ξ n ε) (paleyWalsh ζ n ε)
        rw [sub_eq_add_neg, sub_eq_add_neg] at hm
        simp only [hF, hf, hg, hξK, hζK, flip_apply_self, coin_not]
        rcases coin_eq_one_or_eq_neg_one (ε K) with h | h <;>
          simp only [h, one_smul, neg_smul, neg_neg] <;> linarith
      have h1 := avg_flip K F
      have h2 := avg_mono hpt
      rw [avg_add, avg_const_mul] at h2
      linarith
    · simp

/-- The majorization step: if `‖y‖^p − β^p ‖x‖^p ≤ U (x, y)` and `E U (f, g) ≤ 0`, then
`‖g‖_p ≤ β ‖f‖_p`. -/
private theorem zzg_ofReal_lpNorm_le {F : Type*} [SeminormedAddCommGroup F] {N : ℕ} {p β : ℝ}
    (hp : 0 < p) (hβ : 0 < β) {U : F → F → ℝ} (hU : ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y)
    {f g : (Fin N → Bool) → F} (h : avg (fun ε => U (f ε) (g ε)) ≤ 0) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p g) ≤
      ENNReal.ofReal β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p f) := by
  have h1 := avg_mono fun ε => hU (f ε) (g ε)
  rw [avg_sub, avg_const_mul, zzg_avg_rpow hp, zzg_avg_rpow hp] at h1
  have hf0 := lpNorm_nonneg (fun x : F => norm_nonneg x) p f
  have hg0 := lpNorm_nonneg (fun x : F => norm_nonneg x) p g
  have h2 : SignCube.lpNorm (fun x => ‖x‖) p g ^ p ≤
      (β * SignCube.lpNorm (fun x => ‖x‖) p f) ^ p := by
    rw [Real.mul_rpow hβ.le hf0]
    linarith
  rw [← ENNReal.ofReal_mul hβ.le]
  exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_rpow_iff hg0 (by positivity) hp).mp h2)

end Cube

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section Contraction

/-- Minkowski's inequality for the norm on the cube. -/
private theorem zzg_lpNorm_add_le {N : ℕ} {p : ℝ} (hp : 1 ≤ p) (F G : (Fin N → Bool) → X) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => F ε + G ε) ≤
      SignCube.lpNorm (fun x => ‖x‖) p F + SignCube.lpNorm (fun x => ‖x‖) p G :=
  lpNorm_add_le (normSeminorm ℝ X) hp F G

/-- Convexity in one real parameter: `‖F + c G‖_p ≤ max (‖F + G‖_p, ‖F − G‖_p)` for `|c| ≤ 1`
(write `F + c G` as the convex combination `(1 + c)/2 (F + G) + (1 − c)/2 (F − G)`). -/
private theorem zzg_lpNorm_add_smul_le {N : ℕ} {p : ℝ} (hp : 1 ≤ p) (F G : (Fin N → Bool) → X)
    {c : ℝ} (hc : |c| ≤ 1) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => F ε + c • G ε) ≤
      max (SignCube.lpNorm (fun x => ‖x‖) p (fun ε => F ε + G ε))
        (SignCube.lpNorm (fun x => ‖x‖) p (fun ε => F ε - G ε)) := by
  set S := lpSeminorm (normSeminorm ℝ X) p hp (N := N)
  have hS : ∀ Z, S Z = SignCube.lpNorm (fun x => ‖x‖) p Z := fun Z => rfl
  have e : (fun ε => F ε + c • G ε) =
      ((1 + c) / 2) • (fun ε => F ε + G ε) + ((1 - c) / 2) • (fun ε => F ε - G ε) := by
    funext ε
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have h0 : 0 ≤ (1 + c) / 2 := by linarith
  have h0' : 0 ≤ (1 - c) / 2 := by linarith
  rw [← hS, ← hS, ← hS, e]
  have h1 := mul_le_mul_of_nonneg_left
    (le_max_left (S (fun ε => F ε + G ε)) (S (fun ε => F ε - G ε))) h0
  have h2 := mul_le_mul_of_nonneg_left
    (le_max_right (S (fun ε => F ε + G ε)) (S (fun ε => F ε - G ε))) h0'
  calc S _ ≤ S (((1 + c) / 2) • fun ε => F ε + G ε) + S (((1 - c) / 2) • fun ε => F ε - G ε) :=
        map_add_le_add S _ _
    _ = (1 + c) / 2 * S (fun ε => F ε + G ε) + (1 - c) / 2 * S (fun ε => F ε - G ε) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h0']
    _ ≤ _ := by linarith

/-- The family `a` with its values on the prefix class of `(k, η)` (the sign vectors `ε` with
`ε_i = η_i` for `i < k`) at time `k` replaced by `c`. -/
private def zzgModify {N : ℕ} (a : Fin N → (Fin N → Bool) → ℝ) (k : Fin N) (η : Fin N → Bool)
    (c : ℝ) : Fin N → (Fin N → Bool) → ℝ :=
  fun j ε => if j = k ∧ ∀ i, i < k → ε i = η i then c else a j ε

private theorem zzgModify_isPredictable {N : ℕ} {a : Fin N → (Fin N → Bool) → ℝ}
    (ha : IsPredictable a) (k : Fin N) (η : Fin N → Bool) (c : ℝ) :
    IsPredictable (zzgModify a k η c) := by
  intro j ε ε' h
  simp only [zzgModify]
  have hiff : (j = k ∧ ∀ i, i < k → ε i = η i) ↔ (j = k ∧ ∀ i, i < k → ε' i = η i) := by
    constructor
    · rintro ⟨rfl, h2⟩
      exact ⟨rfl, fun i hi => (h i hi).symm.trans (h2 i hi)⟩
    · rintro ⟨rfl, h2⟩
      exact ⟨rfl, fun i hi => (h i hi).trans (h2 i hi)⟩
  by_cases hc : j = k ∧ ∀ i, i < k → ε i = η i
  · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
  · rw [ite_eq_right hc, ite_eq_right (mt hiff.mpr hc), ha j ε ε' h]

/-- A predictable family is unchanged by putting back its own value on a prefix class. -/
private theorem zzgModify_self {N : ℕ} {a : Fin N → (Fin N → Bool) → ℝ} (ha : IsPredictable a)
    (k : Fin N) (η : Fin N → Bool) : zzgModify a k η (a k η) = a := by
  funext j ε
  simp only [zzgModify]
  split_ifs with hc
  · obtain ⟨rfl, h2⟩ := hc
    exact (ha j ε η h2).symm
  · rfl

/-- The transform by the modified family is affine in the new value `c`. -/
private theorem zzgModify_paleyWalsh {N : ℕ} (a : Fin N → (Fin N → Bool) → ℝ)
    (ξ : Fin N → (Fin N → Bool) → X) (k : Fin N) (η : Fin N → Bool) (c : ℝ) (n : ℕ)
    (ε : Fin N → Bool) :
    paleyWalsh (fun j ε => zzgModify a k η c j ε • ξ j ε) n ε =
      paleyWalsh (fun j ε => zzgModify a k η 0 j ε • ξ j ε) n ε +
        c • paleyWalsh (fun j ε =>
          (if j = k ∧ ∀ i, i < k → ε i = η i then (1 : ℝ) else 0) • ξ j ε) n ε := by
  rw [← paleyWalsh_smul, ← paleyWalsh_add]
  refine congrArg (fun F => paleyWalsh F n ε) (funext fun j => funext fun ε' => ?_)
  simp only [zzgModify]
  split_ifs <;> simp

/-- The extreme-point step of the contraction principle: replacing, one prefix class at a time,
the values of `a` in `[−1, 1]` by `±1` (whichever does not decrease the `L^p` norm, by convexity)
gives a predictable `±1` family `σ` with `‖Σ a_k ε_k ξ_k‖_p ≤ ‖Σ σ_k ε_k ξ_k‖_p`; induction over
a finite set `S` of pairs `(k, η)` outside which `a = ±1`. -/
private theorem zzg_exists_sign_le {N : ℕ} {p : ℝ} (hp : 1 ≤ p) (ξ : Fin N → (Fin N → Bool) → X)
    (n : ℕ) (S : Finset (Fin N × (Fin N → Bool))) :
    ∀ a : Fin N → (Fin N → Bool) → ℝ, IsPredictable a → (∀ k ε, |a k ε| ≤ 1) →
      (∀ k ε, (k, ε) ∉ S → a k ε = 1 ∨ a k ε = -1) →
      ∃ σ : Fin N → (Fin N → Bool) → ℝ, IsPredictable σ ∧ (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
        SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => a k ε • ξ k ε) n) ≤
          SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) n) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun a ha _ hS => ⟨a, ha, fun k ε => hS k ε (Finset.notMem_empty _), le_rfl⟩
  | insert x S hx ih =>
    intro a ha ha1 hS
    obtain ⟨k, η⟩ := x
    -- the two extreme modifications on the prefix class of `(k, η)`
    have hext : ∀ c : ℝ, (c = 1 ∨ c = -1) →
        ∃ σ : Fin N → (Fin N → Bool) → ℝ, IsPredictable σ ∧ (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
          SignCube.lpNorm (fun x => ‖x‖) p
              (paleyWalsh (fun j ε => zzgModify a k η c j ε • ξ j ε) n) ≤
            SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => σ k ε • ξ k ε) n) := by
      intro c hc
      refine ih (zzgModify a k η c) (zzgModify_isPredictable ha k η c) (fun j ε => ?_)
        (fun j ε hjε => ?_)
      · simp only [zzgModify]
        split_ifs
        · rcases hc with rfl | rfl <;> simp
        · exact ha1 j ε
      · simp only [zzgModify]
        split_ifs with hcond
        · exact hc
        · refine hS j ε ?_
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => hcond ?_, hjε⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact ⟨rfl, fun i _ => rfl⟩
    obtain ⟨σ₁, hσ₁, hσ₁1, h₁⟩ := hext 1 (Or.inl rfl)
    obtain ⟨σ₂, hσ₂, hσ₂1, h₂⟩ := hext (-1) (Or.inr rfl)
    -- convexity in the value on the class
    set F := paleyWalsh (fun j ε => zzgModify a k η 0 j ε • ξ j ε) n with hF
    set G := paleyWalsh (fun j ε =>
      (if j = k ∧ ∀ i, i < k → ε i = η i then (1 : ℝ) else 0) • ξ j ε) n with hG
    have e : ∀ c, paleyWalsh (fun j ε => zzgModify a k η c j ε • ξ j ε) n =
        fun ε => F ε + c • G ε := fun c => funext fun ε => zzgModify_paleyWalsh a ξ k η c n ε
    have hconv : SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => a k ε • ξ k ε) n) ≤
        max (SignCube.lpNorm (fun x => ‖x‖) p
            (paleyWalsh (fun j ε => zzgModify a k η 1 j ε • ξ j ε) n))
          (SignCube.lpNorm (fun x => ‖x‖) p
            (paleyWalsh (fun j ε => zzgModify a k η (-1) j ε • ξ j ε) n)) := by
      have ea : paleyWalsh (fun k ε => a k ε • ξ k ε) n =
          paleyWalsh (fun j ε => zzgModify a k η (a k η) j ε • ξ j ε) n := by
        rw [zzgModify_self ha]
      rw [ea, e, e, e]
      simpa [one_smul, neg_one_smul, ← sub_eq_add_neg] using
        zzg_lpNorm_add_smul_le hp F G (ha1 k η)
    rcases le_total (SignCube.lpNorm (fun x => ‖x‖) p
        (paleyWalsh (fun j ε => zzgModify a k η 1 j ε • ξ j ε) n))
      (SignCube.lpNorm (fun x => ‖x‖) p
        (paleyWalsh (fun j ε => zzgModify a k η (-1) j ε • ξ j ε) n)) with h | h
    · exact ⟨σ₂, hσ₂, hσ₂1, hconv.trans ((max_eq_right h).le.trans h₂)⟩
    · exact ⟨σ₁, hσ₁, hσ₁1, hconv.trans ((max_eq_left h).le.trans h₁)⟩

end Contraction

/-- **The contraction principle** for Paley–Walsh martingales: a dyadic `UMD_p` constant also
bounds the transforms by predictable multipliers with values in `[−1, 1]` (Pisier, (8.14) and
Remark 8.11: the `L^p` norm of the transform is a convex function of the finitely many values of
the multipliers on the prefix classes, so it is at most its value at a predictable `±1` family,
where `β` applies). -/
theorem lpNorm_paleyWalsh_mul_le {p : ℝ} (hp : 1 ≤ p) {β : ℝ≥0∞} (hβ : IsDyadicUMDBound X p β)
    {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X} {a : Fin N → (Fin N → Bool) → ℝ}
    (hξ : IsPredictable ξ) (ha : IsPredictable a) (ha1 : ∀ k ε, |a k ε| ≤ 1) (n : ℕ) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => a k ε • ξ k ε) n)) ≤
      β * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) := by
  obtain ⟨σ, hσ, hσ1, hle⟩ := zzg_exists_sign_le hp ξ n Finset.univ a ha ha1
    fun k ε h => absurd (Finset.mem_univ _) h
  exact (ENNReal.ofReal_le_ofReal hle).trans (hβ N ξ σ hξ hσ hσ1 n)

variable (X) in
/-- Burkholder's Bellman function
`U (x, y) = sup E [‖y + g‖^p − β^p ‖x + f‖^p]`, over Paley–Walsh martingales `f = Σ ε_k ξ_k` and
their transforms `g = Σ a_k ε_k ξ_k` by predictable multipliers with values in `[−1, 1]`. -/
noncomputable def bellmanFunction (p β : ℝ) (x y : X) : ℝ :=
  sSup {v | ∃ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (a : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ ∧ IsPredictable a ∧ (∀ k ε, |a k ε| ≤ 1) ∧
      v = avg fun ε => ‖y + paleyWalsh (fun k ε => a k ε • ξ k ε) N ε‖ ^ p -
        β ^ p * ‖x + paleyWalsh ξ N ε‖ ^ p}

section Bellman

variable (X) in
/-- `v` is the Bellman average `E [‖y + g_N‖^p − β^p ‖x + f_N‖^p]` of a Paley–Walsh pair on `N`
signs. -/
private def zzgRep (p β : ℝ) (x y : X) (N : ℕ) (v : ℝ) : Prop :=
  ∃ (ξ : Fin N → (Fin N → Bool) → X) (a : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ ∧ IsPredictable a ∧ (∀ k ε, |a k ε| ≤ 1) ∧
      v = avg fun ε => ‖y + paleyWalsh (fun k ε => a k ε • ξ k ε) N ε‖ ^ p -
        β ^ p * ‖x + paleyWalsh ξ N ε‖ ^ p

private theorem zzg_bellman_eq (p β : ℝ) (x y : X) :
    bellmanFunction X p β x y = sSup {v | ∃ N, zzgRep X p β x y N v} :=
  rfl

/-- The trivial pair (`N = 0`) has the value `‖y‖^p − β^p ‖x‖^p`. -/
private theorem zzgRep_zero (p β : ℝ) (x y : X) :
    zzgRep X p β x y 0 (‖y‖ ^ p - β ^ p * ‖x‖ ^ p) :=
  ⟨fun _ _ => 0, fun _ _ => 0, umdd_isPredictable_const 0, umdd_isPredictable_const 0,
    fun _ _ => by simp, by simp⟩

/-- A family on `N + 1` signs that is a family on the first `N` signs followed by `0` has the same
Paley–Walsh martingale. -/
private theorem zzg_paleyWalsh_pad {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ}
    (ζ : Fin (N + 1) → (Fin (N + 1) → Bool) → E) (ζ' : Fin N → (Fin N → Bool) → E)
    (h : ∀ i ω, ζ (Fin.castSucc i) ω = ζ' i (Fin.init ω)) (hl : ∀ ω, ζ (Fin.last N) ω = 0)
    (ω : Fin (N + 1) → Bool) : paleyWalsh ζ (N + 1) ω = paleyWalsh ζ' N (Fin.init ω) := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl, Fin.sum_univ_castSucc]
  simp [h, hl, Fin.init]

private theorem zzg_avg_init {N : ℕ} (G : (Fin N → Bool) → ℝ) :
    avg (fun ω : Fin (N + 1) → Bool => G (Fin.init ω)) = avg G := by
  rw [avg_succ_last]
  simp [Fin.init_snoc]

private theorem zzg_isPredictable_pad {E : Type*} [Zero E] {N : ℕ}
    {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ) :
    IsPredictable (fun (k : Fin (N + 1)) (ω : Fin (N + 1) → Bool) =>
      if hk : (k : ℕ) < N then ξ ⟨k, hk⟩ (Fin.init ω) else 0) := by
  intro k ω ω' h
  dsimp only
  split_ifs with hk
  · exact hξ _ _ _ fun j hj => h (Fin.castSucc j) (by simpa [Fin.lt_def] using hj)
  · rfl

/-- Padding: a value on `N` signs is a value on `N + 1` signs. -/
private theorem zzgRep_succ {p β : ℝ} {x y : X} {N : ℕ} {v : ℝ} (h : zzgRep X p β x y N v) :
    zzgRep X p β x y (N + 1) v := by
  obtain ⟨ξ, a, hξ, ha, ha1, rfl⟩ := h
  refine ⟨_, _, zzg_isPredictable_pad hξ, zzg_isPredictable_pad ha, fun k ω => ?_, ?_⟩
  · split_ifs
    · exact ha1 _ _
    · simp
  · rw [← zzg_avg_init]
    congr 1
    funext ω
    rw [zzg_paleyWalsh_pad _ (fun k ε => a k ε • ξ k ε) (fun i ω => by simp) (fun ω => by simp),
      zzg_paleyWalsh_pad _ ξ (fun i ω => by simp) (fun ω => by simp)]

private theorem zzgRep_mono {p β : ℝ} {x y : X} {N N' : ℕ} (hN : N ≤ N') {v : ℝ}
    (h : zzgRep X p β x y N v) : zzgRep X p β x y N' v := by
  induction N', hN using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact zzgRep_succ ih

/-- The spliced family on `N + 1` signs: `d` at time `0`, then, in the remaining signs, the family
`ξ₂` if the first sign is `+1` and `ξ₁` if it is `−1`. -/
private def zzgSplice {E : Type*} {N : ℕ} (d : E) (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E) :
    Fin (N + 1) → (Fin (N + 1) → Bool) → E :=
  fun k ω => Fin.cons (α := fun _ => E) d
    (fun i => if ω 0 then ξ₂ i (Fin.tail ω) else ξ₁ i (Fin.tail ω)) k

private theorem zzgSplice_zero {E : Type*} {N : ℕ} (d : E) (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E)
    (ω : Fin (N + 1) → Bool) : zzgSplice d ξ₁ ξ₂ 0 ω = d :=
  rfl

private theorem zzgSplice_succ_cons {E : Type*} {N : ℕ} (d : E)
    (ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E) (i : Fin N) (b : Bool) (η : Fin N → Bool) :
    zzgSplice d ξ₁ ξ₂ i.succ (Fin.cons b η) = if b then ξ₂ i η else ξ₁ i η := by
  simp [zzgSplice]

private theorem zzgSplice_isPredictable {E : Type*} {N : ℕ} (d : E)
    {ξ₁ ξ₂ : Fin N → (Fin N → Bool) → E} (hξ₁ : IsPredictable ξ₁) (hξ₂ : IsPredictable ξ₂) :
    IsPredictable (zzgSplice d ξ₁ ξ₂) := by
  intro k ω ω' h
  induction k using Fin.cases with
  | zero => rfl
  | succ i =>
    have h0 : ω 0 = ω' 0 := h 0 (Fin.succ_pos i)
    have ht : ∀ j, j < i → Fin.tail ω j = Fin.tail ω' j := fun j hj =>
      h j.succ (Fin.succ_lt_succ_iff.mpr hj)
    simp only [zzgSplice, Fin.cons_succ, h0]
    split_ifs
    · exact hξ₂ i _ _ ht
    · exact hξ₁ i _ _ ht

/-- Splitting off the first sign of a Paley–Walsh martingale on `N + 1` signs. -/
private theorem zzg_paleyWalsh_cons {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ}
    (ζ : Fin (N + 1) → (Fin (N + 1) → Bool) → E) (b : Bool) (η : Fin N → Bool) :
    paleyWalsh ζ (N + 1) (Fin.cons b η) =
      coin b • ζ 0 (Fin.cons b η) + paleyWalsh (fun i η' => ζ i.succ (Fin.cons b η')) N η := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl, Fin.sum_univ_succ]
  simp

/-- **Splicing**: if `v₁` is a value at `(x − d, y − e d)` and `v₂` one at `(x + d, y + e d)` on
`N` signs, `|e| ≤ 1`, then `(v₁ + v₂) / 2` is a value at `(x, y)` on `N + 1` signs: the pair
starts with the step `ε₀ (d, e d)` and continues with pair `2` if `ε₀ = 1`, pair `1` if
`ε₀ = −1`. -/
private theorem zzgRep_splice {p β : ℝ} {N : ℕ} {x y d : X} {e : ℝ} (he : |e| ≤ 1) {v₁ v₂ : ℝ}
    (h₁ : zzgRep X p β (x - d) (y - e • d) N v₁) (h₂ : zzgRep X p β (x + d) (y + e • d) N v₂) :
    zzgRep X p β x y (N + 1) ((v₁ + v₂) / 2) := by
  obtain ⟨ξ₁, a₁, hξ₁, ha₁, ha₁1, rfl⟩ := h₁
  obtain ⟨ξ₂, a₂, hξ₂, ha₂, ha₂1, rfl⟩ := h₂
  refine ⟨zzgSplice d ξ₁ ξ₂, zzgSplice e a₁ a₂, zzgSplice_isPredictable d hξ₁ hξ₂,
    zzgSplice_isPredictable e ha₁ ha₂, fun k ω => ?_, ?_⟩
  · induction k using Fin.cases with
    | zero => exact he
    | succ i =>
      simp only [zzgSplice, Fin.cons_succ]
      split_ifs
      · exact ha₂1 _ _
      · exact ha₁1 _ _
  · have key : ∀ b : Bool, (fun η : Fin N → Bool =>
        ‖y + paleyWalsh (fun k ω => zzgSplice e a₁ a₂ k ω • zzgSplice d ξ₁ ξ₂ k ω) (N + 1)
          (Fin.cons b η)‖ ^ p -
          β ^ p * ‖x + paleyWalsh (zzgSplice d ξ₁ ξ₂) (N + 1) (Fin.cons b η)‖ ^ p) =
        fun η => ‖(y + coin b • (e • d)) + paleyWalsh (fun k ω =>
            (if b then a₂ k ω else a₁ k ω) • (if b then ξ₂ k ω else ξ₁ k ω)) N η‖ ^ p -
          β ^ p * ‖(x + coin b • d) +
            paleyWalsh (fun k ω => if b then ξ₂ k ω else ξ₁ k ω) N η‖ ^ p := by
      intro b
      funext η
      rw [zzg_paleyWalsh_cons, zzg_paleyWalsh_cons]
      simp only [zzgSplice_zero, zzgSplice_succ_cons, add_assoc]
    rw [avg_succ, add_comm (avg _) (avg _), key true, key false]
    simp [sub_eq_add_neg]

/-- Minkowski's inequality with a constant: `‖c + F‖_p ≤ ‖c‖ + ‖F‖_p`. -/
private theorem zzg_lpNorm_const_add_le {N : ℕ} {p : ℝ} (hp : 1 ≤ p) (c : X)
    (F : (Fin N → Bool) → X) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => c + F ε) ≤
      ‖c‖ + SignCube.lpNorm (fun x => ‖x‖) p F := by
  have h := zzg_lpNorm_add_le hp (fun _ => c) F
  rwa [umdd_lpNorm_of_norm_eq (norm_nonneg c) (fun _ => rfl) (by linarith)] at h

/-- The contraction principle with a real constant `u`: `‖Σ a_k ε_k ξ_k‖_p ≤ u ‖Σ ε_k ξ_k‖_p`. -/
private theorem zzg_lpNorm_transform_le {p u : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u)
    (hD : IsDyadicUMDBound X p (ENNReal.ofReal u)) {N : ℕ} {ξ : Fin N → (Fin N → Bool) → X}
    {a : Fin N → (Fin N → Bool) → ℝ} (hξ : IsPredictable ξ) (ha : IsPredictable a)
    (ha1 : ∀ k ε, |a k ε| ≤ 1) (n : ℕ) :
    SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh (fun k ε => a k ε • ξ k ε) n) ≤
      u * SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n) := by
  have h := lpNorm_paleyWalsh_mul_le hp hD hξ ha ha1 n
  rw [← ENNReal.ofReal_mul hu] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hu (lpNorm_nonneg (fun _ => norm_nonneg _) p _))).mp h

/-- `(A + u t)^p − β^p t^p ≤ (A + u A / (β − u))^p` for `t ≥ 0`, `0 ≤ u < β`, `A ≥ 0`: for
`t ≤ A / (β − u)` bound the first term, for larger `t` the difference is `≤ 0`. -/
private theorem zzg_real_bound {p A u β t : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huβ : u < β) (ht : 0 ≤ t) :
    (A + u * t) ^ p - β ^ p * t ^ p ≤ (A + u * (A / (β - u))) ^ p := by
  have hβu : 0 < β - u := by linarith
  have hβ : 0 ≤ β := by linarith
  have hT : 0 ≤ A / (β - u) := div_nonneg hA hβu.le
  by_cases h : t ≤ A / (β - u)
  · have h1 : (A + u * t) ^ p ≤ (A + u * (A / (β - u))) ^ p :=
      Real.rpow_le_rpow (by positivity) (by linarith [mul_le_mul_of_nonneg_left h hu]) hp.le
    have h2 : 0 ≤ β ^ p * t ^ p := by positivity
    linarith
  · rw [not_le, div_lt_iff₀ hβu] at h
    have h3 : A + u * t ≤ β * t := by nlinarith
    have h4 : (A + u * t) ^ p ≤ β ^ p * t ^ p := by
      rw [← Real.mul_rpow hβ ht]
      exact Real.rpow_le_rpow (by positivity) h3 hp.le
    have h5 : 0 ≤ (A + u * (A / (β - u))) ^ p := by positivity
    linarith

/-- The Bellman averages are bounded above: with `u < β` a dyadic `UMD_p` constant,
`‖g‖_p ≤ u ‖f‖_p ≤ u (t + ‖x‖)`, `t = ‖x + f‖_p` (contraction principle), so every value at
`(x, y)` is at most `(A + u t)^p − β^p t^p ≤ (A + u A / (β − u))^p`, `A = ‖y‖ + u ‖x‖`. -/
private theorem zzgRep_le {p β u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (huβ : u < β)
    (hD : IsDyadicUMDBound X p (ENNReal.ofReal u)) {x y : X} {N : ℕ} {v : ℝ}
    (h : zzgRep X p β x y N v) :
    v ≤ (‖y‖ + u * ‖x‖ + u * ((‖y‖ + u * ‖x‖) / (β - u))) ^ p := by
  obtain ⟨ξ, a, hξ, ha, ha1, rfl⟩ := h
  have hp0 : 0 < p := by linarith
  have hg := zzg_lpNorm_transform_le hp.le hu hD hξ ha ha1 N
  have hf : SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ N) ≤
      SignCube.lpNorm (fun x => ‖x‖) p (fun ε => x + paleyWalsh ξ N ε) + ‖x‖ := by
    have h := zzg_lpNorm_add_le hp.le (fun ε => x + paleyWalsh ξ N ε) (fun _ => -x)
    have e : (fun ε => x + paleyWalsh ξ N ε + -x) = paleyWalsh ξ N := funext fun ε => by abel
    rwa [e, umdd_lpNorm_of_norm_eq (norm_nonneg x) (fun _ => norm_neg x) hp0] at h
  have hyg := zzg_lpNorm_const_add_le hp.le y (paleyWalsh (fun k ε => a k ε • ξ k ε) N)
  rw [avg_sub, avg_const_mul, zzg_avg_rpow hp0, zzg_avg_rpow hp0]
  have ht := lpNorm_nonneg (fun x : X => norm_nonneg x) p (fun ε => x + paleyWalsh ξ N ε)
  have h1 : SignCube.lpNorm (fun x => ‖x‖) p
        (fun ε => y + paleyWalsh (fun k ε => a k ε • ξ k ε) N ε) ≤
      ‖y‖ + u * ‖x‖ + u * SignCube.lpNorm (fun x => ‖x‖) p (fun ε => x + paleyWalsh ξ N ε) := by
    nlinarith [mul_le_mul_of_nonneg_left hf hu]
  have h2 := Real.rpow_le_rpow (lpNorm_nonneg (fun x : X => norm_nonneg x) p _) h1 hp0.le
  have h3 := zzg_real_bound hp0 (by positivity : 0 ≤ ‖y‖ + u * ‖x‖) hu huβ ht
  linarith

/-- At `(0, 0)` every value is `≤ 0`: `E ‖g‖^p ≤ u^p E ‖f‖^p ≤ β^p E ‖f‖^p`. -/
private theorem zzgRep_zero_le {p β u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (huβ : u ≤ β)
    (hD : IsDyadicUMDBound X p (ENNReal.ofReal u)) {N : ℕ} {v : ℝ}
    (h : zzgRep X p β 0 0 N v) : v ≤ 0 := by
  obtain ⟨ξ, a, hξ, ha, ha1, rfl⟩ := h
  have hp0 : 0 < p := by linarith
  simp only [zero_add]
  rw [avg_sub, avg_const_mul, zzg_avg_rpow hp0, zzg_avg_rpow hp0]
  have hf0 := lpNorm_nonneg (fun x : X => norm_nonneg x) p (paleyWalsh ξ N)
  have hg := zzg_lpNorm_transform_le hp.le hu hD hξ ha ha1 N
  have h1 := Real.rpow_le_rpow (lpNorm_nonneg (fun x : X => norm_nonneg x) p _) hg hp0.le
  have h2 := Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right huβ hf0) hp0.le
  rw [Real.mul_rpow (show 0 ≤ β by linarith) hf0] at h2
  linarith

/-- The Bellman function is midpoint concave along zig-zag segments, by splicing. -/
private theorem zzg_bellman_midpoint {p β u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (huβ : u < β)
    (hD : IsDyadicUMDBound X p (ENNReal.ofReal u)) {e : ℝ} (he : |e| ≤ 1) (x y d : X) :
    bellmanFunction X p β (x - d) (y - e • d) + bellmanFunction X p β (x + d) (y + e • d) ≤
      2 * bellmanFunction X p β x y := by
  have hne : ∀ x y : X, ({v | ∃ N, zzgRep X p β x y N v} : Set ℝ).Nonempty := fun x y =>
    ⟨_, 0, zzgRep_zero p β x y⟩
  have hbdd : ∀ x y : X, BddAbove {v | ∃ N, zzgRep X p β x y N v} := fun x y =>
    ⟨_, fun v ⟨N, hv⟩ => zzgRep_le hp hu huβ hD hv⟩
  simp only [zzg_bellman_eq]
  set S₁ := {v | ∃ N, zzgRep X p β (x - d) (y - e • d) N v}
  set S₂ := {v | ∃ N, zzgRep X p β (x + d) (y + e • d) N v}
  set S := {v | ∃ N, zzgRep X p β x y N v}
  have key : ∀ v₁ ∈ S₁, ∀ v₂ ∈ S₂, v₁ + v₂ ≤ 2 * sSup S := by
    rintro v₁ ⟨N₁, h₁⟩ v₂ ⟨N₂, h₂⟩
    have := le_csSup (hbdd x y) ⟨N₁ + N₂ + 1, zzgRep_splice he
      (zzgRep_mono (Nat.le_add_right N₁ N₂) h₁) (zzgRep_mono (Nat.le_add_left N₂ N₁) h₂)⟩
    linarith
  have h1 : ∀ v₂ ∈ S₂, sSup S₁ + v₂ ≤ 2 * sSup S := fun v₂ hv₂ => by
    have := csSup_le (hne _ _) fun v₁ hv₁ =>
      (by linarith [key v₁ hv₁ v₂ hv₂] : v₁ ≤ 2 * sSup S - v₂)
    linarith
  have := csSup_le (hne _ _) fun v₂ hv₂ =>
    (by linarith [h1 v₂ hv₂] : v₂ ≤ 2 * sSup S - sSup S₁)
  linarith

end Bellman

/-- Concavity along zig-zag lines from midpoint concavity: if `U` is midpoint concave along the
segments of direction `(w, e w)` and bounded below by `‖y‖^p − β^p ‖x‖^p`, then
`z ↦ U (x + z, y + e z)` is concave (`concaveOn_of_midpoint` on each line
`t ↦ U (x + z₁ + t w, y + e z₁ + t e w)`, `w = z₂ − z₁`, which is locally bounded below by a
continuous function). -/
private theorem zzg_concaveOn_of_midpoint {p β : ℝ} (hp : 0 < p) {U : X → X → ℝ} {e : ℝ}
    (hmid : ∀ x y d : X, U (x - d) (y - e • d) + U (x + d) (y + e • d) ≤ 2 * U x y)
    (hlow : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y) (x y : X) :
    ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + e • z) := by
  refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
  set φ : ℝ → ℝ := fun t => U (x + (z₁ + t • (z₂ - z₁))) (y + e • (z₁ + t • (z₂ - z₁))) with hφ
  have hφmid : ∀ s t, (φ s + φ t) / 2 ≤ φ ((s + t) / 2) := by
    intro s t
    have h := hmid (x + (z₁ + ((s + t) / 2) • (z₂ - z₁))) (y + e • (z₁ + ((s + t) / 2) • (z₂ - z₁)))
      (((t - s) / 2) • (z₂ - z₁))
    have e1 : x + (z₁ + ((s + t) / 2) • (z₂ - z₁)) - ((t - s) / 2) • (z₂ - z₁) =
        x + (z₁ + s • (z₂ - z₁)) := by module
    have e2 : y + e • (z₁ + ((s + t) / 2) • (z₂ - z₁)) - e • ((t - s) / 2) • (z₂ - z₁) =
        y + e • (z₁ + s • (z₂ - z₁)) := by module
    have e3 : x + (z₁ + ((s + t) / 2) • (z₂ - z₁)) + ((t - s) / 2) • (z₂ - z₁) =
        x + (z₁ + t • (z₂ - z₁)) := by module
    have e4 : y + e • (z₁ + ((s + t) / 2) • (z₂ - z₁)) + e • ((t - s) / 2) • (z₂ - z₁) =
        y + e • (z₁ + t • (z₂ - z₁)) := by module
    rw [e1, e2, e3, e4] at h
    simp only [hφ]
    linarith
  have hφbdd : ∀ t, ∃ V ∈ nhds t, ∃ C : ℝ, ∀ s ∈ V, C ≤ φ s := by
    intro t
    set ψ : ℝ → ℝ := fun s => ‖y + e • (z₁ + s • (z₂ - z₁))‖ ^ p -
      β ^ p * ‖x + (z₁ + s • (z₂ - z₁))‖ ^ p with hψ
    have hψc : Continuous ψ := by
      have c1 : Continuous fun s : ℝ => ‖y + e • (z₁ + s • (z₂ - z₁))‖ := by fun_prop
      have c2 : Continuous fun s : ℝ => ‖x + (z₁ + s • (z₂ - z₁))‖ := by fun_prop
      exact (c1.rpow_const fun _ => Or.inr hp.le).sub
        (continuous_const.mul (c2.rpow_const fun _ => Or.inr hp.le))
    refine ⟨ψ ⁻¹' Set.Ioi (ψ t - 1),
      hψc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith)), ψ t - 1, fun s hs => ?_⟩
    exact (le_of_lt hs).trans (hlow _ _)
  have hφc := concaveOn_of_midpoint hφmid hφbdd
  obtain rfl : a = 1 - b := by linarith
  have := hφc.2 (Set.mem_univ 0) (Set.mem_univ 1) ha hb hab
  simp only [hφ, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul] at this
  have e5 : z₁ + (z₂ - z₁) = z₂ := by abel
  have e6 : z₁ + b • (z₂ - z₁) = (1 - b) • z₁ + b • z₂ := by module
  rw [e5, e6] at this
  simpa only [smul_eq_mul] using this

/-- For `β > UMD_p^Δ (X)`, the Bellman function is zig-zag concave (Burkholder): it is finite
(the contraction principle, `lpNorm_paleyWalsh_mul_le`), at least `‖y‖^p − β^p ‖x‖^p` (the
trivial pair), `0` at the origin, and midpoint concave along zig-zag lines (splicing), hence
concave along them (Bernstein–Doetsch). -/
theorem isZigZagConcave_bellmanFunction {p β : ℝ} (hp : 1 < p)
    (hβ : dyadicUMDConst X p < ENNReal.ofReal β) : IsZigZagConcave p β (bellmanFunction X p β) := by
  have hp0 : 0 < p := by linarith
  have hDt : dyadicUMDConst X p ≠ ⊤ := ne_top_of_lt hβ
  set u := (dyadicUMDConst X p).toReal with hu_def
  have hu : 0 ≤ u := ENNReal.toReal_nonneg
  have hDu : dyadicUMDConst X p = ENNReal.ofReal u := (ENNReal.ofReal_toReal hDt).symm
  have huβ : u < β := by
    rw [hDu] at hβ
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp hβ).1
  have hD : IsDyadicUMDBound X p (ENNReal.ofReal u) := by
    rw [← hDu]
    exact isDyadicUMDBound_dyadicUMDConst hp0
  have hbdd : ∀ x y : X, BddAbove {v | ∃ N, zzgRep X p β x y N v} := fun x y =>
    ⟨_, fun v ⟨N, hv⟩ => zzgRep_le hp hu huβ hD hv⟩
  have hlow : ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ bellmanFunction X p β x y := fun x y =>
    le_csSup (hbdd x y) ⟨0, zzgRep_zero p β x y⟩
  refine ⟨fun x y e he => zzg_concaveOn_of_midpoint hp0
    (zzg_bellman_midpoint hp hu huβ hD he) hlow x y, le_antisymm ?_ ?_, hlow⟩
  · exact csSup_le ⟨_, 0, zzgRep_zero p β 0 0⟩ fun v ⟨N, hv⟩ =>
      zzgRep_zero_le hp hu huβ.le hD hv
  · simpa [Real.zero_rpow hp0.ne'] using hlow 0 0

/-- A zig-zag concave function bounds the dyadic UMD constant: `UMD_p^Δ (X) ≤ β` (Burkholder's
argument on the cube: for a Paley–Walsh martingale `f` and its transform `g` by predictable signs,
midpoint concavity of `z ↦ U (f_k + z, g_k + σ_k z)` at `± ξ_k` gives
`E U (f_{k+1}, g_{k+1}) ≤ E U (f_k, g_k)`, so `E U (f_n, g_n) ≤ U (0, 0) = 0`, and the
majorization `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` gives `‖g_n‖_p ≤ β ‖f_n‖_p`). -/
theorem dyadicUMDConst_le_of_isZigZagConcave {p β : ℝ} (hp : 1 < p) (hβ : 0 < β)
    {U : X → X → ℝ} (hU : IsZigZagConcave p β U) : dyadicUMDConst X p ≤ ENNReal.ofReal β := by
  refine dyadicUMDConst_le_of_isDyadicUMDBound fun N ξ σ hξ hσ hσ1 n => ?_
  refine zzg_ofReal_lpNorm_le (by linarith) hβ hU.2.2 ?_
  have h := zzg_avg_le_of_mid (U := U) hξ (hσ.smul hξ) (fun k ε x y => ?_) n
  · rwa [hU.2.1] at h
  · have hc := hU.1 x y (σ k ε) (by rcases hσ1 k ε with h | h <;> simp [h])
    simpa [sub_eq_add_neg, smul_neg] using zzg_mid_of_concaveOn hc (ξ k ε)

variable [CompleteSpace X]

/-- A zig-zag concave function bounds the UMD constant: `UMD_p (X) ≤ β` (Burkholder; HNVW I,
Theorem 4.5.6). -/
theorem umdConst_le_of_isZigZagConcave {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ}
    (hU : IsZigZagConcave p β U) : umdConst X p ≤ ENNReal.ofReal β := by
  rw [← dyadicUMDConst_eq_umdConst hp]
  exact dyadicUMDConst_le_of_isZigZagConcave hp hβ hU

/-- **Burkholder's characterisation of UMD** (Burkholder 1981; HNVW I, Theorem 4.5.6):
`UMD_p (X) < ∞` if and only if a zig-zag concave function exists for some `β > 0`. -/
theorem umdConst_lt_top_iff_exists_isZigZagConcave {p : ℝ} (hp : 1 < p) :
    umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U := by
  constructor
  · -- `β = UMD_p^Δ (X) + 1` and the Bellman function
    intro h
    have hD : dyadicUMDConst X p ≠ ⊤ := ((dyadicUMDConst_le_umdConst hp).trans_lt h).ne
    refine ⟨(dyadicUMDConst X p).toReal + 1, by positivity, bellmanFunction X p _,
      isZigZagConcave_bellmanFunction hp ?_⟩
    calc dyadicUMDConst X p = ENNReal.ofReal (dyadicUMDConst X p).toReal :=
          (ENNReal.ofReal_toReal hD).symm
      _ < ENNReal.ofReal ((dyadicUMDConst X p).toReal + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (lt_add_one _)
  · rintro ⟨β, hβ, U, hU⟩
    exact (umdConst_le_of_isZigZagConcave hp hβ hU).trans_lt ENNReal.ofReal_lt_top

end Real

/-- A complex zig-zag concave function bounds the complex UMD constant:
`UMD_{ℂ,p} (X) ≤ β` (Yaroslavtsev 2018, Proposition 3.7; HNVW I, Theorem 4.5.6). -/
theorem complexUMDConst_le_of_isComplexZigZagConcave {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ}
    (hU : IsComplexZigZagConcave p β U) : complexUMDConst X p ≤ ENNReal.ofReal β := by
  have hB : IsComplexDyadicUMDBound X p (ENNReal.ofReal β) := by
    intro N ξ c hξ hc hc1 n
    refine zzg_ofReal_lpNorm_le (by linarith) hβ hU.2.2 ?_
    have hcξ : IsPredictable fun k ε => c k ε • ξ k ε := fun k ε ε' h => by
      simp only [hc k ε ε' h, hξ k ε ε' h]
    have h := zzg_avg_le_of_mid (U := U) hξ hcξ (fun k ε x y => ?_) n
    · rwa [hU.2.1] at h
    · have hcc := hU.1 x y (c k ε) (hc1 k ε).le
      simpa [sub_eq_add_neg, smul_neg] using zzg_mid_of_concaveOn hcc (ξ k ε)
  rw [← complexDyadicUMDConst_eq_complexUMDConst hp]
  exact sInf_le hB

end BanachProbability
