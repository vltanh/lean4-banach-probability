# Shorter proofs

Arguments shorter than those of the sources, noticed while following them. The library follows the
sources unless the status says "in the library". Sizes are in lines of Lean, docstrings included.

Status:

- "in the library": the library uses the argument, or has it beside the source's;
- "history at `<commit>`": proved in the library at that commit, and replaced since by the source's
  proof;
- "Lean at `<commit>`": checked in a file outside the library against that commit (no `sorry`);
- "Lean": the same, against the version of the library in which the row was added;
- "on paper": written out, not compiled.

Full references are in [REFERENCES.md](REFERENCES.md); HNVW is Hytönen–van Neerven–Veraar–Weis,
*Analysis in Banach Spaces*.

## Burkholder's inequality (Osękowski 2012, Burkholder 1988)

| # | Result | Shorter proof | Size | Status |
| --- | --- | --- | --- | --- |
| 1 | Osękowski, Theorem 3.5 (ii), every `p > 1`, martingales started at `0` | Burkholder's proof of Theorem 1.1 (1988): (1.12) on lines on which neither coordinate vanishes (`G (1) ≤ G (0) + G' (0)`, `G` concave by (1.14)), the shift of the martingales by an orthogonal vector in `H ⊕ ℝ`, the martingale property, `δ → 0` by dominated convergence, `E U_p ≤ U_p (0, 0) = 0` | 527 beyond the lemmas on `U_p`, which stay for (1.10) and Remark 1.2, against 1,120 for the integration method | history at `250cd49` |
| 2 | Burkholder 1988, Remark 1.2, every `p > 1` | a function with an affine majorant touching it at every point of a line is concave on it, so 2° of `U₁` and of `U_∞` give their concavity along the lines `‖k‖ ≤ ‖h‖`; an integral `∫ k (t) U (·/t, ·/t) dt`, `k ≥ 0`, of concave functions is concave; `p = 2` is the identity `U_2 = ‖y‖² − ‖x‖²` | 90 against 307 | Lean at `25b96a3` |
| 3 | Osękowski, Theorem 3.5 (ii), every `p > 1`, any start with `‖g_0‖ ≤ ‖f_0‖` | Remark 1.2 and the one-sided derivatives of `U_p` in the norms give a tangent majorant of `U_p` at every point (with zero slope in a coordinate that vanishes), so Theorem 2.7 applies to `U_p` itself: no shift, no integral formulas | 60 to 100 (estimate) | on paper |
| 4 | sharpness for `p > 2`: `p − 1 ≤ β` for a dyadic `UMD_p` constant `β` of `ℝ` (the proof works for every `p > 1`) | the second approach on `w (x) = U⁰ (1 − x, x)`, with the homogeneity at `λ = −(2x − 1)`: the chord from `1 − 1/(β + 1)` to `1` gives `p w (1) ≤ (β + 1) w (1)`, and `w (1) = U⁰ (0, 1) ≥ 1 > 0`. No duality, no sign step. The book mentions this "reasoning similar to that in the case `1 < p < 2`" (p. 59) and uses duality | 41 against 137, given the lemmas of the case `1 < p ≤ 2` | Lean at `25b96a3` |
| 5 | the end of the second approach, `1 < p ≤ 2` | both slopes at `1` in the display before (3.67) are at most the slope of the chord from `1/(β + 1)` to `1`, so `(1 + s^{p−1}) (β + 1)/β ≤ 2 (s^p − 1)/(s − 1)` for `s > 1`; let `s ↓ 1`. With `w (1) < 0` from 3° (`w (1) ≤ 2 w (1/2) − w (0) ≤ −1`) no one-sided derivative is left | about 85 against 96 | Lean at `25b96a3` |
| 6 | dyadic sharpness | the second approach run on `W⁰` of Theorem 3.34, which has the properties 1°, 2°, 3° used: the dyadic sharpness follows at once, and the general one from `UMD_p^Δ ≤ UMD_p`; the book runs it on `U⁰` and then proves Theorem 3.34 | (in the code) | in the library |

## UMD constants and random sums (HNVW I, 2016, and II, 2017)

| # | Result | Shorter proof | Size | Status |
| --- | --- | --- | --- | --- |
| 1 | I, Proposition 4.2.10, `UMD_{ℂ,p} ≤ (π/2) UMD_p` for predictable multipliers, every `p > 1` | let `z_1, …, z_m` be the values of the multipliers `φ_1, …, φ_n` (finitely many); Proposition 3.2.14 gives `z_i = Σ_ε c (ε) ε_i` with `Σ ‖c‖ ≤ π/2`; with `i (k, ω)` the index of `φ_k (ω)`, `σ^ε_k = ε_{i (k, ·)}` is a predictable sign and `φ • Y = Σ_ε c (ε) (σ^ε • Y)`; triangle inequality and the real UMD inequality. No Lemma 3.6.18 and no Theorem 4.2.25; it does not give that deterministic and predictable signs have the same constant | 88 against 911 | Lean at `67f48bf` |
| 2 | I, Proposition 4.2.10 | for `λ = e^{iθ}`, `(1/2π) ∫ sgn cos (θ − φ) e^{iφ} dφ = (2/π) λ`; for each `φ` the signs `sgn cos (θ_k − φ)` are predictable; `M` equally spaced `φ`, error `O (1/M)`. No Hahn–Banach and no finite models. Longer than item 1 | 517 against 1,242 | history at `250cd49` |
| 3 | I, Theorem 4.2.25, real signs `±1`, `p ≥ 1` | the deterministic bound, applied on the cube to Paley–Walsh martingales, is `IsSignDyadicUMDBound`, and Theorem 4.5.6, (2)⇒(3)⇒(1), ends with predictable signs. No Lemma 3.6.18. The complex case is the same | 12 | Lean at `67f48bf` |
| 4 | I, Theorem 4.2.25, predictable multipliers in the closed unit ball | the function `U` of (2)⇒(3) is concave along `z ↦ (x + z, y + e z)` for all `‖e‖ ≤ 1`, so Lemma 4.5.5 holds verbatim for predictable multipliers (constant on the atoms of `ℱ_{n−1}`); then the reduction to finite models and the rounding | about 60 (estimate) | on paper |
| 5 | I, Theorem 4.2.25 | refine along the level sets `V_i = {φ_{k+1} = z_i} ∈ ℱ_k` of the multipliers, one at a time: `𝒢_i = {S ∈ ℱ_{k+1} : S \ (V_1 ∪ … ∪ V_i) ∈ ℱ_k}` and `g_i = Y_k + 1_{V_1 ∪ … ∪ V_i} (Y_{k+1} − Y_k)`; the increment `1_{V_i} dY_{k+1}` has the constant multiplier `z_i`. On any probability space: no finite model, no counting of atoms. Replaces Lemma 3.6.18 | 150 to 200 (estimate), against about 500 | on paper |
| 5a | I, Theorem 4.2.25 for Paley–Walsh martingales and real signs (`isSignDyadicUMDBound_iff_isDyadicUMDBound`) | split the step `k` into two, with independent signs `r_{k,+}`, `r_{k,−}`, the coefficients `1_{σ_k = ±1} ξ_k` (with `ξ_k` and `σ_k` taken at `(ε_j)_{j<k}`) and the multipliers `±1`: with `ε_k = r_{k,σ_k}` the pair has the law of `(Σ ε_k ξ_k, Σ σ_k ε_k ξ_k)`. For finitely many values of the multipliers, one step for each value. No zig-zag concave function and no incremental filtration | about 60 (estimate) | on paper |
| 6 | I, Theorem 4.5.6, (3)⇒(1) without `u (0, 0) = 0` | apply `E F (f_n, g_n) ≤ u (0, 0)` to `t f`, whose transform is `t g`: `t^p E F (f_n, g_n) ≤ u (0, 0)` for all `t > 0`, so `E F (f_n, g_n) ≤ 0`. Replaces (4.31) for martingales started at `0` | about 10 against 101 | on paper |
| 7 | I, (4.31), `ũ (0, 0) = 0` | `ũ (0, 0) = ũ (2·0, 2·0) = 2^p ũ (0, 0)` and `2^p ≠ 1`, instead of the limit `α → 0` | a few lines | on paper |
| 8 | I, Theorem 4.5.6, Step 2 | splice on blocks: on `1 + N₁ + N₂` signs run the first pair on the first block on `{r_1 = 1}` and the second pair on the second block on `{r_1 = −1}`; the multipliers stay constants, with no padding to a common `N` and no interleaving | about 125 against 185 | on paper |
| 9 | I, Lemmas 3.5.13 and 3.5.14 | good-λ without localization: for `h = ^ρ f^{ν∧σ}`, `h* ≤ 3δλ 1_{ρ<∞}` and `‖T h‖ > 3αδλ` on `{ν < ∞, σ = ∞}`, so the `H^q → L^{q,∞}` bound for this one function gives `η = (K/α)^q`. No Lemma 3.5.13, no (3.55), no sum over `{ρ = k}` | about 100 less | on paper; a variant with a strong bound and `4δλ` in the history at `250cd49` |
| 10 | I, Lemma 3.5.3 (the adjoint) | `T = E_0 + Σ_k M_{σ_k} D_k`, `D_k = E_{k+1} − E_k` self-adjoint and commuting with the multiplication by the `ℱ_k`-measurable `σ_k`, so `⟨σ_k D_k f, g⟩ = ⟨f, σ_k D_k g⟩` for each `k`: no cross terms | about 40 less | on paper |
| 11 | II, Lemma 6.2.3 (Bonami) | after the reduction by positivity `S (T g) ≤ T (S g)`, the scalar lemma is used only for `S g ≥ 0`, that is for `x + ε y` with `\|y\| ≤ x`: neither the case `\|y\| > 1` nor the duality for signed functions is needed (`twoPoint`, `twoPoint_seminorm`) | 123 less | in the library, for Borell's proof |
| 12 | II, Theorem 6.2.4, `1 < p ≤ q` | `hypercontractive_affine` (Borell 1979, (2.1)) with `c = 0` | about 10, given `Hypercontractivity/Vector` | Lean at `67f48bf` |
| 13 | I, Theorems 4.2.5 and 4.5.6 | the book's alternative proof (p. 334) in place of Maurey's dyadic perturbation and realization: Theorem 4.2.5, both halves of Theorem 4.5.6 and its final clause, over `ℝ` and `ℂ` | 2,345 against 3,222 (real halves, and the bound (3)⇒(1) over `ℂ`) | in the library; Maurey's route in the history at `250cd49` |

## Noncommutative Khintchine

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 1 | the noncommutative Khintchine inequality in `S_q`, `q ≥ 2`, real matrices (Lust-Piquard 1986; Lust-Piquard–Pisier 1991; Pisier–Xu 2003, Theorem 6.1) | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp 2014): Lemma 2.4, the mean-value trace inequality of Lemma 3.4, trace Hölder; non-symmetric matrices by the Hermitian dilation. Remark 7.2 needs a variant of Lemma 3.4 for `2 < q < 3` which the source does not prove; it is `trace_mean_value` | in the library; the original route is in [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis) |

## Schatten classes, type 2, K-convexity (HNVW I, Appendix D; HNVW II, §6.2.a and Chapter 7; Tomczak-Jaegermann 1974; Pisier 1998)

| # | Result | Shorter proof | Size | Status |
| --- | --- | --- | --- | --- |
| 1 | type 2 of `S_q`, `q ≥ 2` (Tomczak-Jaegermann 1974, Theorem 3.1 (ii)) | `ncKhintchine_symmetric_upper` for the dilations, and `‖Σ D_k²‖_{S_{q/2}} ≤ Σ ‖D_k‖²_{S_q}`; the factors `2^{1/q}` cancel. Constants `√(q − 1)` for `q ≥ 3` and `√(2 (q − 1))` for `q < 3`, both at most `√(q + 1)`, even in `L^q`. No Horn inequality, interpolation or complex matrices. (Pisier deduces the Khintchine inequality from type 2, so this reverses his order) | about 40 against 1,095 | on paper |
| 1a | the same, even `q = 2k` | bound each `\|tr C\|` by `Π ‖C_ν‖_{S_{2k}}` (iterated Hölder inequality; HNVW II, Lemma 7.1.12), so `E ‖Σ ε_i A_i‖^{2k} ≤ E (Σ ε_i ‖A_i‖)^{2k}`; no general Horn inequality, no `ℓ_k` triangle inequality, the same constant | about 190 against 399 | history at `8962532` |
| 1b | the same, other `q` | symmetric matrices, duality and the three lines theorem for `E tr (Φ Σ ε_k x_k)` with analytic families through `Φ` and the `x_k`; then the dilation. No three lines theorem for operators, no block diagonal matrices | about 440 against 696 and the lemmas on singular value decompositions and block diagonal matrices | history at `8962532` |
| 2 | the Rademacher projection on `L^q (S_q)`, `q ≥ 2` (Pisier 1998, p. 106) | `ncKhintchine_upper` and the operator Bessel inequality `Σ z_kᵀ z_k ⪯ E fᵀ f`: constant `√(2 (q − 1))`. The same caveat | about 40 | on paper |
| 3 | HNVW I, Lemma D.1.4 | take `c_j` the right derivative of `f` at `a_j`: `f (b_j) − f (a_j) ≥ c_j (b_j − a_j)`, and `c` is nonincreasing; no equal entries to remove, no monotonicity of `b` | about 60 less | on paper |
| 4 | HNVW I, Proposition D.2.5 | `\|tr A\| = \|Σ ⟨e_k, A e_k⟩\| ≤ Σ ‖A e_k‖ = Σ s_k` in the eigenbasis of `Aᵀ A` | a few lines | on paper |
| 5 | `\|tr (A B)\| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}` for rectangular matrices | the symmetric case (`abs_trace_mul_le_of_isHermitian`) applied to the dilations of `A` and `Bᵀ`; no Horn's inequality | a few lines | on paper |
| 6 | HNVW II, Propositions 7.4.21, 7.4.22, the covariance domination | for `P` an orthogonal projection, `T (P g) = ½ (T (g) + T (R g))` with the reflection `R = 2P − 1`, which preserves the Gaussian measure, so `‖T ∘ P‖_{L²} ≤ ‖T‖_{L²}`; no Walsh functions, no contraction principle for Gaussian sums | 466 against 672 (with `SignCube/Walsh`) | history at `8962532` |
| 7 | `ncKhintchine_lower_col` | from `complexSchattenNorm_blockCol_sq_le_avg`, `complexSchattenNorm_map_ofReal` and `L² ≤ L^q` | 44 against 64 | Lean, in [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis) |
| 8 | the Walsh expansion (HNVW II, p. 18) | `Σ_α w_α (ε) w_α (η) = Π_i (1 + ε_i η_i) = 2^N δ_{εη}`, put in `Σ_α w_α (ε) E (w_α f)`; no induction, no orthonormality | 17 against 47 | Lean |
| 9 | the general Horn inequality (Tomczak-Jaegermann 1974, Lemma 1.1), at least one factor | the multiplicative inequality `Π_{k<N} s_k (A_1 ⋯ A_r) ≤ Π_{k<N} s_k (A_1) ⋯ s_k (A_r)` by induction, then `sum_rpow_le_sum_rpow_of_weak_log_majorization` with `p = 1`; no Abel transform, no additive Horn inequality | 32 against 43 | Lean |
| 10 | `M_{2k} ≤ √(2k − 1)` (`evenKhintchineConst_le`) | `M_{2k} ≤ √k`, which is sharper, from `(2k)! ≤ (2k)^k k!` (Mathlib's `Nat.factorial_two_mul_le`) | 13 against 29 | Lean |
| 11 | HNVW II, Proposition 7.4.22, the second inequality | Proposition 6.1.5: `Σ_n g_{n} x_{n} = ½ (Σ_α g_α x_α + Σ_α η_α g_α x_α)` with `η_α = 1` at the singletons and `−1` at the other `α`, and the two sums have the same law; no contraction principle | 36 against 48 and the contraction principle for Rademacher sums | Lean |
