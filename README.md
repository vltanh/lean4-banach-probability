# BanachProbability

[![Lean Action CI](https://github.com/vltanh/lean4-banach-probability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-banach-probability/actions/workflows/lean_action_ci.yml)

A Lean 4 library of probability in Banach spaces:

- Burkholder's inequality for Hilbert-space-valued martingales, its square function inequality, and
  the sharpness of the constant `p* − 1`;
- UMD constants: the reduction to Paley–Walsh martingales, extrapolation, the randomised UMD
  property and decoupling, real against complex constants, and Burkholder's zig-zag concave
  functions;
- hypercontractivity on the cube and the Kahane–Khintchine inequality in seminormed spaces;
- Schatten classes: the Schatten norms, Hölder's inequality, the noncommutative Khintchine inequality,
  martingale transforms with values in matrices, and the UMD property and type 2 of `S_q`, uniformly in
  the dimension;
- random sums: Kahane's contraction principle, type 2, K-convexity.

**Status.** Every result below is proved, and no theorem takes an unproved result as a hypothesis.
The library builds with no `sorry` and no axiom beyond Lean's standard [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice)
and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound); [`scripts/Audit.lean`](scripts/Audit.lean) checks this for every declaration and fails otherwise.

**Not formalized.** The equality cases of Burkholder's inequality and the sharpness clauses of the
square function inequality; σ-finite measure spaces (the constants are defined with probability
spaces in `Type` and martingales started at `0`); extrapolation and the randomised UMD property over
complex scalars; the converse of the randomised UMD property for Paley–Walsh martingales; the
necessity of the condition on the exponents in the hypercontractive inequality; Borell's theorem for
Walsh polynomials of degree `≥ 2`; complex Rademacher variables; rectangular or complex matrices and
exponents below `2` in the noncommutative Khintchine inequality; general semifinite von Neumann
algebras and non-scalar multipliers in the noncommutative martingale results.

**Planned extensions.** Kahane–Khintchine for Rademacher sums on a probability space; the
noncommutative Khintchine inequality for rectangular and complex matrices (a proof of it along the route
of Lust-Piquard and Pisier is in the package `VectorValuedHarmonicAnalysis`, *placeholder: not published
yet*); Randrianantoanina's Theorem 3.1 for general semifinite von Neumann algebras and non-scalar
multipliers.

## Results

`UMD_p (X)` is `umdConst X p`, the best `β ∈ [0, ∞]` in
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}` over all `X`-valued martingales `Y` (Mathlib's
`MeasureTheory.Martingale`) with `Y_0 = 0` and all predictable signs `σ`; `UMD_{ℂ,p} (X)` is the same
with predictable unimodular complex multipliers, and `UMD_p^Δ`, `UMD_{ℂ,p}^Δ` are the restrictions to
Paley–Walsh martingales on sign cubes `Fin N → Bool`. Moreover `1 < p < ∞`, `p' = p/(p − 1)`,
`p* = max (p, p')`, the `ε_i` are independent fair signs, and `‖·‖_p` is an `L^p` norm. All
declarations are in the namespace [`BanachProbability`](BanachProbability); modules are relative to
[`BanachProbability/`](BanachProbability). HNVW is Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach Spaces*; the full
references are in [docs/REFERENCES.md](docs/REFERENCES.md).

### Martingales in Hilbert spaces

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| Burkholder's inequality: for martingales `f`, `g` in a real Hilbert space with `‖g_0‖ ≤ ‖f_0‖` and `‖g_{n+1} − g_n‖ ≤ ‖f_{n+1} − f_n‖` a.s., `‖g_n‖_p ≤ (p* − 1) ‖f_n‖_p` | [`Osekowski.eLpNorm_le_of_subordinate`](BanachProbability/Martingale/Osekowski/Moment.lean#L312); started at `0`: [`Burkholder.inequality_of_subordinate`](BanachProbability/Martingale/Burkholder/Inequality.lean#L65) | Osękowski (2012), Thm 3.5 (ii); Burkholder (1988), Thm 1.1 | [`Martingale/Osekowski/Moment`](BanachProbability/Martingale/Osekowski/Moment.lean), [`Martingale/Burkholder/Inequality`](BanachProbability/Martingale/Burkholder/Inequality.lean) |
| Sharpness: for `K < p* − 1` there are a real Paley–Walsh martingale `f` and a transform `g` of it by predictable signs with `K ‖f‖_p < ‖g‖_p`; for every real Hilbert space `H ≠ 0`, `UMD_p (H) = UMD_p^Δ (H) = p* − 1` | [`Osekowski.exists_lt_lpNorm_transform`](BanachProbability/Martingale/Osekowski/Sharpness.lean#L685), [`Osekowski.umdConst_of_innerProductSpace`](BanachProbability/Martingale/Osekowski/Sharpness.lean#L675), [`Osekowski.dyadicUMDConst_of_innerProductSpace`](BanachProbability/Martingale/Osekowski/Sharpness.lean#L668) | Osękowski (2012), Thm 3.5, Rem 3.8 | [`Martingale/Osekowski/Sharpness`](BanachProbability/Martingale/Osekowski/Sharpness.lean) |
| Square function, `𝒮_n X = (Σ_{k<n} ‖X_{k+1} − X_k‖²)^{1/2}`: `‖𝒮_n X‖_p ≤ (p* − 1) ‖X_n‖_p` and `‖X_n‖_p ≤ (p* − 1) ‖𝒮_n X‖_p` for a martingale `X` in a real Hilbert space with `X_0 = 0` | [`Burkholder.squareFunction_of_martingale`](BanachProbability/Martingale/Burkholder/Inequality.lean#L127) | Osękowski (2012), Thm 8.6; Burkholder (1988), Thm 3.1 | [`Martingale/Burkholder/Inequality`](BanachProbability/Martingale/Burkholder/Inequality.lean) |
| Burkholder's function `u_p (x, y) = p (1 − 1/p*)^{p−1} (‖y‖ − (p* − 1) ‖x‖) (‖x‖ + ‖y‖)^{p−1}`: `u_p (x, y) ≥ ‖y‖^p − (p* − 1)^p ‖x‖^p`, and `t ↦ u_p (x + t h, y + t k)` is concave for `‖k‖ ≤ ‖h‖` in a real inner product space | [`Burkholder.burkholderFun_ge`](BanachProbability/Martingale/Burkholder/Function.lean#L794), [`Burkholder.burkholderFun_concaveOn_line`](BanachProbability/Martingale/Burkholder/Function.lean#L802) | Burkholder (1988), (1.6), (1.10), Rem 1.2 | [`Martingale/Burkholder/Function`](BanachProbability/Martingale/Burkholder/Function.lean) |
| Doob, Banach-space-valued martingales: `‖max_{k≤n} ‖Y_k‖‖_p ≤ p' ‖Y_n‖_p` | [`eLpNorm_runningMax_norm_le`](BanachProbability/Martingale/Doob.lean#L188) | standard argument | [`Martingale/Doob`](BanachProbability/Martingale/Doob.lean) |

### UMD constants

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| `UMD_p^Δ (X) = UMD_p (X)` and `UMD_{ℂ,p}^Δ (X) = UMD_{ℂ,p} (X)` | [`dyadicUMDConst_eq_umdConst`](BanachProbability/UMD/Maurey/Basic.lean#L86), [`complexDyadicUMDConst_eq_complexUMDConst`](BanachProbability/UMD/Maurey/Basic.lean#L134) | Maurey (1974–75); HNVW I, Thm 4.2.5 | [`UMD/Maurey/Basic`](BanachProbability/UMD/Maurey/Basic.lean) |
| Deterministic and predictable multipliers give the same constants, real and complex | [`umdConst_eq_sInf_isDeterministicUMDBound`](BanachProbability/UMD/Incremental.lean#L756), [`complexUMDConst_eq_sInf_isDeterministicUMDBound`](BanachProbability/UMD/Incremental.lean#L764) | HNVW I, Thm 4.2.25 | [`UMD/Incremental`](BanachProbability/UMD/Incremental.lean) |
| Extrapolation, `p, q ∈ (1, ∞)`: `UMD_p ≤ 100 (p/q + p'/q') UMD_q` (for the transforms the proof gives `80` in place of `100`: [`IsTransformBound.extrapolation`](BanachProbability/UMD/Extrapolation.lean#L424)); `UMD₂ ≤ 200 UMD_p`, `UMD_p ≤ 50 (p + p') UMD₂ ≤ 100 p* UMD₂`; finite for one `p` implies finite for all | [`umdConst_le_mul_umdConst`](BanachProbability/UMD/Extrapolation.lean#L551), [`umdConst_two_le_mul`](BanachProbability/UMD/Extrapolation.lean#L580), [`umdConst_le_fifty_mul_umdConst_two`](BanachProbability/UMD/Extrapolation.lean#L565), [`umdConst_le_mul_umdConst_two`](BanachProbability/UMD/Extrapolation.lean#L572), [`umdConst_lt_top_of_lt_top`](BanachProbability/UMD/Extrapolation.lean#L559) | HNVW I, Thm 4.2.7 | [`UMD/Extrapolation`](BanachProbability/UMD/Extrapolation.lean) |
| Randomised UMD property: a `UMD_p` constant `β` satisfies `β⁻¹ ‖Y_n‖_p ≤ ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`; two such inequalities with constants `β⁻`, `β⁺` give the `UMD_p` constant `β⁻ β⁺` | [`IsUMDBound.isLowerRandomisedUMDBound`](BanachProbability/UMD/Decoupling.lean#L213), [`IsUMDBound.isUpperRandomisedUMDBound`](BanachProbability/UMD/Decoupling.lean#L200), [`isUMDBound_of_randomised`](BanachProbability/UMD/Decoupling.lean#L266) | HNVW I, Prop 4.2.3 | [`UMD/Decoupling`](BanachProbability/UMD/Decoupling.lean) |
| Decoupling of a Paley–Walsh martingale `Y_n = Σ_{k<n} ε_k ξ_k`, with `Ỹ_n = Σ_{k<n} ε̃_k ξ_k` for an independent copy `ε̃` of the signs: `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p`, also with `UMD_p^Δ` | [`decoupling`](BanachProbability/UMD/Decoupling.lean#L379), [`decoupling_dyadic`](BanachProbability/UMD/Decoupling.lean#L354) | HNVW I, Prop 4.2.3 (cf. McConnell (1989); Cox–Veraar (2007)) | [`UMD/Decoupling`](BanachProbability/UMD/Decoupling.lean) |
| `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π/2) UMD_p (X)`, `X` complex | [`umdConst_le_complexUMDConst_le`](BanachProbability/UMD/Complex.lean#L135) | HNVW I, Prop 4.2.10 | [`UMD/Complex`](BanachProbability/UMD/Complex.lean), [`UMD/ConvexHull`](BanachProbability/UMD/ConvexHull.lean) |
| `UMD_p (L^p (μ; B)) ≤ UMD_p (B)` for every measure `μ`; `UMD_p (L^p (μ; ℂ)) ≤ p* − 1` | [`umdConst_Lp_le`](BanachProbability/UMD/Lp.lean#L143), [`umdConst_Lp_complex_le`](BanachProbability/UMD/Lp.lean#L151) | Pisier (2016), Cor 5.22 | [`UMD/Lp`](BanachProbability/UMD/Lp.lean) |
| `UMD_p (X) < ∞` if and only if, for some `β > 0`, there is `U : X × X → ℝ` with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` and `z ↦ U (x + z, y + ε z)` concave for `ε ∈ [−1, 1]`; the least such `β ≥ 0` is `UMD_p (X)`. The same over `ℂ`, with `ε` in the closed unit disc and `UMD_{ℂ,p}` | [`umdConst_lt_top_iff_exists_isZigZagConcave`](BanachProbability/ZigZag/Basic.lean#L215), [`isLeast_umdConst_isZigZagConcave`](BanachProbability/ZigZag/Basic.lean#L233), [`complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave`](BanachProbability/ZigZag/Basic.lean#L351), [`isLeast_complexUMDConst_isComplexZigZagConcave`](BanachProbability/ZigZag/Basic.lean#L368) | Burkholder (1981, 1986); HNVW I, Thm 4.5.6; Yaroslavtsev (2018), Prop 3.7 | [`ZigZag/Basic`](BanachProbability/ZigZag/Basic.lean) |

### Hypercontractivity and Kahane–Khintchine

The values are in a real vector space with a seminorm; completeness is not needed.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| The discrete heat semigroup on functions of `n` signs: `‖T (t) f‖_q ≤ ‖f‖_p` for `1 < p ≤ q` and `e^{−t} ≤ √((p−1)/(q−1))` | [`heatSemigroup_lpNorm_le`](BanachProbability/Hypercontractivity/HeatSemigroup.lean#L391); one sign: [`bonami_seminorm`](BanachProbability/Hypercontractivity/HeatSemigroup.lean#L277) | HNVW II, Thm 6.2.2 and Lemma 6.2.3 ("if" parts) | [`Hypercontractivity/HeatSemigroup`](BanachProbability/Hypercontractivity/HeatSemigroup.lean) |
| Borell's operator `⊗ⁿ K̄` (kernel `Π_i (1 + ρ x_i y_i)`, `ρ = √((p−1)/(q−1))`), `1 < p ≤ q`: `‖(⊗ⁿ K̄) f‖_q ≤ ‖f‖_p`, hence `‖c + ρ Σ ε_i x_i‖_q ≤ ‖c + Σ ε_i x_i‖_p` | [`kBarTensor_lpNorm_le`](BanachProbability/Hypercontractivity/Vector.lean#L337), [`hypercontractive_affine`](BanachProbability/Hypercontractivity/Vector.lean#L364) | Borell (1979), (2.1) | [`Hypercontractivity/Vector`](BanachProbability/Hypercontractivity/Vector.lean) |
| Kahane–Khintchine: `‖Σ ε_i x_i‖_q ≤ √((q−1)/(p−1)) ‖Σ ε_i x_i‖_p` for `1 < p ≤ q`; `‖Σ ε_i x_i‖_p ≤ max (1, √((p−1)/(q−1))) ‖Σ ε_i x_i‖_q` for all `p, q > 1`; with some constant depending only on `p` and `q` for all `p, q ∈ (0, ∞)` | [`kahaneKhintchine_hypercontractive`](BanachProbability/KahaneKhintchine/Basic.lean#L50), [`kahaneKhintchine`](BanachProbability/KahaneKhintchine/Basic.lean#L84), [`exists_kahaneKhintchine`](BanachProbability/KahaneKhintchine/Basic.lean#L211) | Kahane (1964); HNVW II, Thm 6.2.4 | [`KahaneKhintchine/Basic`](BanachProbability/KahaneKhintchine/Basic.lean) |

### Random sums, type 2, K-convexity

`X` is a normed space (complex where the scalars are), `E` the average over independent fair signs.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| Kahane's contraction principle, `1 ≤ p < ∞`: `‖Σ ε_k c_k x_k‖_p ≤ ‖Σ ε_k x_k‖_p` for real `\|c_k\| ≤ 1`; with the factor `π/2` for complex `\|c_k\| ≤ 1` | [`lpNorm_sum_coin_smul_le`](BanachProbability/RandomSums/Contraction.lean#L71), [`lpNorm_sum_coin_smul_le_pi_div_two_mul`](BanachProbability/RandomSums/Contraction.lean#L84) | HNVW I, Prop 3.2.10; HNVW II, Thm 6.1.13 | `RandomSums/Contraction` |
| Type 2 of the Schatten classes, `q ≥ 2`, real or complex square matrices of every size: `‖Σ ε_k x_k‖_{L^q (S_q)} ≤ √(q + 1) (Σ ‖x_k‖²_{S_q})^{1/2}`; for `2k ≤ q ≤ 2k + 2` with `M_{2k}^{1−θ} M_{2k+2}^θ`, `M_{2k} = ((2k)!/(2^k k!))^{1/2k}` | [`lpNorm_schattenNorm_le`](BanachProbability/TypeTwo/Schatten.lean#L219), [`lpNorm_complexSchattenNorm_le_interp`](BanachProbability/TypeTwo/Schatten.lean#L132), [`isTypeTwoBound_schattenSpace`](BanachProbability/TypeTwo/Schatten.lean#L233); even `q`: [`lpNorm_schattenNorm_le_of_even`](BanachProbability/TypeTwo/Even.lean#L330) | Tomczak-Jaegermann (1974), Thm 3.1 (ii) | `TypeTwo/Schatten`, `TypeTwo/Even` |
| The three lines theorem for Schatten norms, and for `L^p (Ω; S_p)` on the sign cube, finite exponents | [`complexSchattenNorm_le_of_verticalStrip`](BanachProbability/Schatten/ThreeLines.lean#L432), [`lpNorm_complexSchattenNorm_le_of_verticalStrip`](BanachProbability/Schatten/ThreeLines.lean#L536) | Gohberg–Krein (1965), §13, and Tomczak-Jaegermann (1974), Prop 1.2; proof of Sutter–Berta–Tomamichel (2017), Thm 3.1 | `Schatten/ThreeLines` |
| A space of type 2 with constant `τ` is K-convex in `L²` with constant `√(π/2) τ`; Gaussian sums and orthonormal systems (finite measure spaces) in a space of type 2 | [`IsTypeTwoBound.isKConvexBound`](BanachProbability/KConvexity/Basic.lean#L472) | HNVW II, Prop 7.4.22 | `KConvexity/Basic` |
| The Rademacher projection on `L^q (Ω; S_q)`, `q ≥ 2`, real matrices: norm at most `√(π/2) √(q + 1)`; the same on `L^{q'} (Ω; S_{q'})` | [`lpNorm_rademacherProj_schattenNorm_le`](BanachProbability/KConvexity/Schatten.lean#L54), [`lpNorm_rademacherProj_schattenNorm_conj_le`](BanachProbability/KConvexity/Schatten.lean#L127) | Pisier (1998), p. 106 | `KConvexity/Schatten` |

### Schatten classes

The matrices are real where not said otherwise; `S_q` is the norm [`schattenNorm`](BanachProbability/Schatten/Basic.lean#L52), defined from the
eigenvalues of `Aᵀ A` ([`complexSchattenNorm`](BanachProbability/Schatten/Complex.lean#L92) for complex matrices). On
`L^∞ (Ω) ⊗ M_n (ℝ)`, `τ = ∫ tr`, and `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` is the martingale
transform by predictable scalar multipliers `|c_k| ≤ 1`, for a general filtration.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| `‖A + B‖_{S_q} ≤ ‖A‖_{S_q} + ‖B‖_{S_q}`, `q ∈ [1, ∞]`, `m × n` matrices | [`schattenNorm_add_le`](BanachProbability/Schatten/Triangle.lean#L210) | Bourin–Zhang (2026), Prop 3.13, Rem 3.14 | `Schatten/Triangle` |
| Horn's inequality `Π_{k<N} s_k (A B) ≤ Π_{k<N} s_k (A) s_k (B)`; Hölder's inequality `‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r`, `0 < q, r < ∞`, real and complex rectangular matrices; `\|tr (A B)\| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}` | [`prod_sortedSingularValue_mul_le`](BanachProbability/Schatten/Horn.lean#L337), [`schattenNorm_mul_le`](BanachProbability/Schatten/Horn.lean#L488), [`complexSchattenNorm_mul_le`](BanachProbability/Schatten/Complex.lean#L298), [`abs_trace_mul_le`](BanachProbability/Schatten/Horn.lean#L622) | HNVW I, Prop D.2.3, Cor D.2.4, Thm D.2.6 | `Schatten/Horn`, `Schatten/Complex` |
| Complex matrices: `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}`, the norm axioms, `UMD₂ (S_q) ≤ C (q* − 1)` | [`complexSchattenNorm_eq_realify`](BanachProbability/Schatten/Complex.lean#L175), [`umdConst_two_complexSchattenSpace_le`](BanachProbability/Noncommutative/ComplexSchattenUMD.lean#L48) | — | `Schatten/Complex`, `Noncommutative/ComplexSchattenUMD` |
| Row and column square functions as norms of block rows and columns; `‖(Σ a_kᴴ a_k)^{1/2}‖²_{S_q} ≤ E ‖Σ ε_k a_k‖²_{S_q}`, `q ≥ 2`, and for rows | [`complexSchattenNorm_blockCol_sq`](BanachProbability/Schatten/Block.lean#L88), [`complexSchattenNorm_blockCol_sq_le_avg`](BanachProbability/Schatten/Block.lean#L195), [`complexSchattenNorm_blockRow_sq_le_avg`](BanachProbability/Schatten/Block.lean#L217) | Lust-Piquard–Pisier (1991), (I.2)–(I.7) | `Schatten/Block` |
| `\|tr (A B)\| ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}` for symmetric `A`, `B` and `r > 1` | [`abs_trace_mul_le_of_isHermitian`](BanachProbability/Schatten/Holder.lean#L108) | Mackey et al. (2014), Prop 7.5 | `Schatten/Holder` |
| Noncommutative Khintchine, upper bound, `q ≥ 2`: `‖Σ ε_i x_i‖_{L^q (S_q)} ≤ √(2(q−1)) max (‖Σ x_i x_iᵀ‖_{S_{q/2}}, ‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`; the constant is `√(q−1)` for symmetric `x_i` and `q ≥ 3` | [`ncKhintchine_upper`](BanachProbability/NoncommutativeKhintchine/Basic.lean#L41), [`ncKhintchine_symmetric_upper`](BanachProbability/NoncommutativeKhintchine/Symmetric.lean#L370), [`ncKhintchine_symmetric_upper_of_three_le`](BanachProbability/NoncommutativeKhintchine/Symmetric.lean#L352) | Lust-Piquard (1986), Pisier–Xu (2003), Thm 6.1; proof of Mackey et al. (2014), Cor 7.3 | `NoncommutativeKhintchine/Basic`, `NoncommutativeKhintchine/Symmetric` |
| Lower bound with constant `1`, rows and columns, `q ≥ 2`; both bounds for normal `x_i`, the upper one with `√2 √q` | [`ncKhintchine_lower_row`](BanachProbability/NoncommutativeKhintchine/Lower.lean#L105), [`ncKhintchine_lower_col`](BanachProbability/NoncommutativeKhintchine/Lower.lean#L40), [`ncKhintchine_normal`](BanachProbability/NoncommutativeKhintchine/Basic.lean#L121), [`pisierXu_khintchine`](BanachProbability/NoncommutativeKhintchine/Basic.lean#L145) | Lust-Piquard (1986); Pisier–Xu (2003), Thm 6.1 | `NoncommutativeKhintchine/Lower`, `NoncommutativeKhintchine/Basic` |
| Weak type `(1, 1)`: `λ τ (1_{(λ,∞)} (\|T_c x\|)) ≤ 52 ‖x‖_{L¹ (τ)}` for symmetric `x`, and with `26` for `x ⪰ 0` (the source's constant for `x ⪰ 0`, printed as `14√3/3 + 28`, is the infimum `26 + 8√3`) | [`weakType_one_one`](BanachProbability/Noncommutative/WeakType.lean#L618), [`weakType_one_one_of_posSemidef`](BanachProbability/Noncommutative/WeakType.lean#L577) | Randrianantoanina (2002), Thm 3.1 | `Noncommutative/WeakType` |
| `‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}`, `1 < r < ∞`, `K = 192 · 864³` | [`eLpNorm_ncTransform_le`](BanachProbability/Noncommutative/SchattenUMD.lean#L340) | Randrianantoanina (2002), Thm 4.3 | `Noncommutative/SchattenUMD` |
| `UMD_q (S_q^{n×n}) ≤ K q*` and `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)`, with `K` and `C` independent of `q ∈ (1, ∞)` and `n` | [`umdConst_schattenSpace_le`](BanachProbability/Noncommutative/SchattenUMD.lean#L439), [`isUMDBound_schattenSpace`](BanachProbability/Noncommutative/SchattenUMD.lean#L366) (`K = 192 · 864³`), [`umdConst_two_schattenSpace_le`](BanachProbability/Noncommutative/SchattenUMD.lean#L447) | Randrianantoanina (2002), Cor 4.5, Rem 4.6 (1) | `Noncommutative/SchattenUMD` |

## Method

Results about Paley–Walsh martingales are proved on the sign cube, where expectations are finite
sums. The module docstrings describe each argument, name its source and record where it departs from
or completes that source.

- **Burkholder's inequality.** Osękowski's integration method: Burkholder's function is an integral
  `∫_0^∞ k (t) u (x/t, y/t) dt`, `k ≥ 0`, of one of two simple functions, `U₁` for `p < 2` and `U_∞` for
  `p > 2`. Burkholder's method gives `E u (f_n/t, g_n/t) ≤ 0`; Fubini's theorem and the majorization
  `u_p ≥ ‖y‖^p − (p* − 1)^p ‖x‖^p` finish; `p = 2` is orthogonality. Sharpness: the book's second
  approach for `1 < p ≤ 2`, run on the dyadic function `W⁰` of its Theorem 3.34, and duality for
  `p > 2`. The square function inequality is the first one, applied in `ℓ² (H)`.
- **UMD constants.** HNVW I. The dyadic inequality gives a zig-zag concave function (Theorem 4.5.6,
  (2)⇒(3)), and this function bounds the constant ((3)⇒(1), on finite models, then in general by
  Lemma 3.6.17). This is also the book's alternative proof of Theorem 4.2.5 (p. 334). Extrapolation
  is a good-λ inequality (Lemmas 3.5.13 to 3.5.15) with Doob's inequality and duality. The complex
  constant uses the convex hulls of sign vectors (Proposition 3.2.14) and, for predictable
  multipliers, incremental filtrations (Lemma 3.6.18, Theorem 4.2.25).
- **Hypercontractivity.** HNVW II: Bonami's two-point inequality with seminorm values, tensorised by
  induction on the signs. Borell's proof (scalar tensorisation and positivity of the kernel) is kept
  beside it.
- **Noncommutative Khintchine.** Exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp) for symmetric
  matrices, then the Hermitian dilation. For `2 < q < 3` their Remark 7.2 needs a variant of their
  Lemma 3.4 that they do not prove; it is proved here ([`trace_mean_value`](BanachProbability/Schatten/Trace.lean#L364)). This is a shorter proof
  than the original one (Lust-Piquard; Lust-Piquard and Pisier), which is followed in the package
  `VectorValuedHarmonicAnalysis`.
- **Type 2 and K-convexity.** Tomczak-Jaegermann: for even `q` the trace is expanded and compared, singular
  value by singular value, with the scalar Khintchine inequality, by the general Horn inequality; the other
  exponents by the three lines theorem for analytic families of matrices. Type 2 gives K-convexity by HNVW
  II, Proposition 7.4.22 (Maurey and Pisier state it without proof): the Walsh functions, Gaussian sums and
  their rotation invariance. Hölder's and Horn's inequalities by determinants of compressions (HNVW I,
  Appendix D). Complex matrices by realification.
- **Schatten norms.** The triangle inequality by the Hermitian dilation and von Neumann's convexity
  inequality (Bourin and Zhang, Remark 3.14), the latter by Peierls's argument. Weyl's inequalities
  for singular values by the Courant–Fischer dimension count.
- **Noncommutative martingales.** Randrianantoanina's route, for general filtrations: Cuculescu's
  projections, taken pointwise, and a rank count in place of Lemma 3.2 give the weak type `(1, 1)`.
  Interpolation and duality, in three regimes so that the constant stays uniform near `r = 2` (a
  detail that the source leaves out), give Theorem 4.3, and Corollary 4.5 follows for martingales on
  any filtered probability space, without the reduction to Paley–Walsh martingales.

### Sources

These were read, and the results taken from them follow their proofs, except where the last column
says otherwise.

| Source | Read | Used for | Departures and completions |
| --- | --- | --- | --- |
| Osękowski (2012) | the book | Burkholder's inequality, its sharpness, the square function | the two integral formulas, stated there without proof, are proved, one of them with a corrected constant; Theorem 3.34 itself is not formalized, only its function `W⁰` |
| Burkholder (1988) | [Numdam, `AST_1988__157-158__75_0`](http://www.numdam.org/item/AST_1988__157-158__75_0/) | Burkholder's function: (1.10), Remark 1.2 | Remark 1.2, stated there without proof, is completed from (1.14) |
| HNVW I (2016) | the book | Props 4.2.3, 4.2.10; Thms 4.2.5, 4.2.7, 4.2.25, 4.5.6; Prop 3.2.10; Appendix D | in Theorem 4.5.6, Steps 2 and 3 are reordered, and the multipliers lie in the closed unit ball, as in Yaroslavtsev (2018); Corollary D.2.4 is completed for zero singular values and holds for all positive exponents |
| HNVW II (2017) | the book | Thms 6.2.2, 6.2.4; 6.1.13, 6.1.15; Props 7.1.18, 7.4.22, Thm 7.1.20 (2) | an edge case of Lemma 6.2.3 by continuity; Theorem 7.1.20 for orthonormal systems on finite measure spaces |
| Tomczak-Jaegermann (1974) | Studia Math. 50 | Lemma 1.1, Prop 1.2, Thm 3.1 (ii) | finite matrices, the complex ones by realification; finite exponents, and the boundedness that Prop 1.2 needs; the theorem of Gohberg–Krein (§13, not obtained) is proved by the argument of Sutter–Berta–Tomamichel (2017) |
| Maurey–Pisier (1976) | Studia Math. 58 | Remark 2.10, stated without proof | proved by HNVW II, Prop 7.4.22 |
| Lust-Piquard–Pisier (1991) | Ark. Mat. 29 | (I.1)–(I.7) | finite matrices; the trace form of (I.3); (I.7) with signs |
| Pisier (1998) | [Numdam, `AST_1998__247__R1_0`](https://www.numdam.org/item/AST_1998__247__R1_0/) | p. 106 | the statement on `L^{q'} (Ω; S_{q'})` is implicit there |
| Borell (1979) | [Numdam, `SPS_1979__13__1_0`](http://www.numdam.org/item/SPS_1979__13__1_0/) | `⊗ⁿ K̄`, the affine inequality | the two results that Borell cites (Gross; Beckner) are proved by O'Donnell's arguments |
| O'Donnell (2014) | the book | two-point inequality and tensorisation (§10.1, Exercises 9.7, 10.1, 10.3) | none |
| Randrianantoanina (2002) | [arXiv:math/0111264](https://arxiv.org/abs/math/0111264) | Thms 3.1, 4.3, Cor 4.5, Rem 4.6 (1) | a rank count for Lemma 3.2; the interpolation is written out |
| Mackey et al. (2014) | [arXiv:1201.6002](https://arxiv.org/abs/1201.6002) | noncommutative Khintchine, trace Hölder | the variant of Lemma 3.4 for `2 < q < 3` is proved |
| Bourin–Zhang (2026) | [arXiv:2610.30538](https://arxiv.org/abs/2610.30538) | the triangle inequality | real `m × n` matrices; von Neumann's inequality, quoted there, is proved by Peierls's argument (its Jensen step is in the proof of Fehr (2021), Thm 7.1) |
| Burkholder (1973, 1981) | Ann. Probab. | origin of the good-λ method and of the characterization of UMD | not followed: the proofs are HNVW's |

Cited for a statement or its origin, with another argument here: Maurey (1974–75); Burkholder
(1984); Kahane (1964); Bonami (1970); Gohberg–Krein (1965); Lust-Piquard (1986); Lust-Piquard–Pisier (1991), for the Khintchine inequality; Pisier–Xu (2003), which states its Theorem 6.1 without proof; Pisier (2016), Cor 5.22, proved here on
Paley–Walsh martingales. Burkholder (1986) is followed through HNVW I. Not used: Bhatia (1997) and
Carlen (2010), the usual references for the triangle inequality, Weyl's inequalities and Peierls's
inequality. Not obtained: Gross (1975) and Beckner (1975), which Borell cites.

## Literature

Reviewed on 2026-11-22 in Crossref, zbMATH, arXiv and Numdam. Preprints are reported as claims of
their authors.

| Result | Origin | State of the question |
| --- | --- | --- |
| Burkholder's inequality | Burkholder 1966 (martingale transforms), 1984 (sharp constant, real martingales), 1988 (Hilbert-valued, differential subordination); Osękowski 2012 (monograph) | `p* − 1` is best possible; in the square function inequality it is best possible in two of the four cases, and in the other two the best constants were unknown in 1988 (Burkholder, Rem. 3.1) and in 2012 (Osękowski, Thm 8.6) |
| UMD constants | Maurey 1974–75 (Paley–Walsh martingales), Burkholder 1981 (geometric characterization), Bourgain 1983 (Hilbert transform); monographs: HNVW 2016, 2017, 2023, Pisier 2016 | whether `UMD_p = UMD_{ℂ,p}` was an open question in 2018 (Yaroslavtsev); linear bounds between the UMD constant and the norm of the Hilbert transform fail in both directions, according to a 2026 preprint of Lorist and van Neerven ([REFERENCES](docs/REFERENCES.md)) |
| Kahane–Khintchine, hypercontractivity | Kahane 1964; Bonami 1970, Beckner 1975; Borell 1979 | scalar best constants: Haagerup 1981; the best `L²`–`L¹` constant in normed spaces is `√2` (Latała–Oleszkiewicz 1994); the constants here are not claimed to be sharp |
| UMD of Schatten classes | Pisier–Xu 1997 (noncommutative martingale inequalities); Randrianantoanina 2002 (weak type `(1, 1)`, optimal order in `p`) | no exact value of `UMD_p (S_p)` was found |
| Noncommutative Khintchine | Lust-Piquard 1986; Lust-Piquard–Pisier 1991 (`p = 1`); Buchholz 2001, 2005; Mackey et al. 2014 | best constants known for even `q` (Buchholz); `√(q − 1)`, for `q = 2` and `q ≥ 3`, is within a factor `√e` of them (Mackey et al.); a sharp `p = 1` Rademacher constant is claimed in a preprint of Chuah, Liu and Mei ([REFERENCES](docs/REFERENCES.md)) |

### Related formalizations

Searched on 2026-11-22: GitHub repository and code search, the Mathlib source, Loogle, the
Palomar registry, the Archive of Formal Proofs, Rocq and HOL4 libraries, Lean Zulip topic titles, and
arXiv. Third-party code was read as text; none of it was built or audited. The projects are in Lean
unless said otherwise.

| Project | Overlap | Not seen there |
| --- | --- | --- |
| [SmaniaD/Burkholder](https://github.com/SmaniaD/Burkholder) | `‖w ⋆ f‖_p ≤ (p* − 1) ‖f‖_p` for real martingales on finite measure spaces and predictable `\|w\| ≤ 1` | Hilbert-valued martingales, differential subordination, square function, sharpness |
| [elorist/UMD_Hilberttransform](https://github.com/elorist/UMD_Hilberttransform) | a UMD constant (σ-finite filtrations), the dyadic reduction at `p = 2`, Burkholder's inequality at `p = 3` for dyadic Hilbert-valued martingales | other `p`, extrapolation, decoupling, `UMD_ℂ ≤ (π/2) UMD`, zig-zag functions, `L^p (B)` |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | Kahane–Khintchine for all exponents `p, q > 0` in real normed spaces; `p* − 1` for real signed Haar sums; the Schatten triangle inequality; Doob's `L^p` inequality for Banach-valued martingales with `p/(p − 1)` | UMD constants, differential subordination, noncommutative Khintchine, vector-valued hypercontractivity |
| [openai/math](https://github.com/openai/math), [AxiomMath/BandMatrixQUE](https://github.com/AxiomMath/BandMatrixQUE), [formal-applied-math/formal-mathfin](https://github.com/formal-applied-math/formal-mathfin), [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean) | Banach-valued Khintchine `L²`–`L¹` with constant `4`, Schatten triangle and Hölder at even exponents; Doob's `L^p` inequality; Doob's `L²` inequality, type and cotype 2 of Hilbert spaces | the other exponents and the UMD theory |
| [Polarnova/FABL](https://github.com/Polarnova/FABL) | Kahane–Khintchine `L²`–`L¹` in real normed spaces with the sharp `√2`, which this package does not have; scalar Khintchine; scalar hypercontractivity for `1 ≤ p ≤ 2 ≤ q`, and two-function forms on product spaces | vector-valued sums for other exponents |
| [Shilun-Allan-Li/tcslib](https://github.com/Shilun-Allan-Li/tcslib) | scalar hypercontractivity on the cube for `1 ≤ p ≤ q`, and two-function, reverse, Gaussian and product-space forms | vector-valued statements |
| [roos-j/lean-trilinearht](https://github.com/roos-j/lean-trilinearht), [ZephyrZhng/khintchine-lean](https://github.com/ZephyrZhng/khintchine-lean), [leanprover-community/add-combi](https://github.com/leanprover-community/add-combi) | Khintchine's upper bound in Hilbert spaces; sharp scalar `L^p`–`L¹` constants; Marcinkiewicz–Zygmund for independent variables in inner product spaces | general normed spaces |
| [BuxinSu/LearningTheoryFormalizations](https://github.com/BuxinSu/LearningTheoryFormalizations), [xf-shi/Tensor_Norm](https://github.com/xf-shi/Tensor_Norm) | matrix Khintchine in operator norm with a factor `√log` of the dimension; an `L¹` noncommutative Khintchine inequality with Haar unitary coefficients | the dimension-free Rademacher inequality in `S_q` |
| [Timeroot/Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo), [savarin/hlawka-schatten](https://github.com/savarin/hlawka-schatten) | Schatten norms of complex square matrices with Hölder, and the trace norm; Schatten norms of linear maps and the Hermitian dilation | in the first, the triangle inequality of `S_q` for all `q` |
| [fpvandoorn/carleson](https://github.com/fpvandoorn/carleson), [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | real (Marcinkiewicz) interpolation; continuous-time martingales, with the `L^p` maximal inequality stated with `sorry` | interpolation on matrices; a proof of Doob's `L^p` inequality |
| Mathlib | martingales, Doob's weak maximal inequality, Hoeffding, Azuma | no declaration for Khintchine, UMD, Burkholder, hypercontractivity, Schatten norms or Doob's `L^p` inequality |
| [Archive of Formal Proofs](https://www.isa-afp.org) (Isabelle); [FormalML](https://github.com/IBM/FormalML), [MathComp-Analysis](https://github.com/math-comp/analysis) (Rocq); [HOL4](https://github.com/HOL-Theorem-Prover/HOL) | martingales and their convergence, optional stopping, concentration inequalities | none of the results above was found |

## Shorter proofs

Shorter arguments than the sources' were noticed for some of the results. They are in
[docs/SHORTER_PROOFS.md](docs/SHORTER_PROOFS.md), each with a sketch, its scope and its status: in the
library, checked in Lean (in a file outside the library, at the commit named), or on paper. The main
ones:

| Result | Shorter proof | Status |
| --- | --- | --- |
| Osękowski, Theorem 3.5 (ii) | Burkholder's own proof (1988, Theorem 1.1): (1.12), a shift by an orthogonal vector, dominated convergence | Lean, in the history at `250cd49` |
| Burkholder 1988, Remark 1.2 | integration of the tangent majorants of `U₁` and `U_∞` | Lean, at `25b96a3` |
| sharpness of `p* − 1` for `p > 2` | the second approach on `x ↦ U⁰ (1 − x, x)` instead of duality | Lean, at `25b96a3` |
| `UMD_{ℂ,p} ≤ (π/2) UMD_p` | Proposition 3.2.14 applied to the vector of the values of the predictable multipliers, with no reduction to deterministic ones | Lean, at `67f48bf` |
| HNVW I, Theorem 4.2.25, signs `±1` | from Theorem 4.5.6 on the cube | Lean, at `67f48bf` |
| noncommutative Khintchine | exchangeable pairs, in place of the route of Lust-Piquard and Pisier | Lean, in the library |

## Using the library

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`, the module system. In a [`lakefile.toml`](lakefile.toml), with `<commit>`
replaced by the full hash of the commit to use:

```toml
[[require]]
name = "BanachProbability"
git = "https://github.com/vltanh/lean4-banach-probability"
rev = "<commit>"
```

Build with `lake build`; audit the axioms with `lake env lean scripts/Audit.lean` (it fails if a
declaration of the library depends on `sorry` or on any axiom beyond [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice)
and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)).

| Directory | Contents |
| --- | --- |
| [`SignCube/`](BanachProbability/SignCube) | signs on `Fin N → Bool`, averages, predictable families, Paley–Walsh martingales, the bridge to Mathlib's martingales |
| [`Martingale/`](BanachProbability/Martingale) | martingale transforms, Doob's inequality, Burkholder's function and inequality, Osękowski's method |
| [`UMD/`](BanachProbability/UMD), [`ZigZag/`](BanachProbability/ZigZag) | UMD constants; zig-zag concave functions |
| [`Hypercontractivity/`](BanachProbability/Hypercontractivity), [`KahaneKhintchine/`](BanachProbability/KahaneKhintchine) | two-point inequality, heat semigroup, Borell's operator; Kahane–Khintchine |
| [`Schatten/`](BanachProbability/Schatten) | singular values, Schatten norms and spaces (real and complex), Horn's and Hölder's inequalities, block rows and columns, Hermitian dilation, trace inequalities, duality on the sign cube, measurability |
| [`RandomSums/`](BanachProbability/RandomSums), [`TypeTwo/`](BanachProbability/TypeTwo), [`KConvexity/`](BanachProbability/KConvexity) | the contraction principle; type 2, the Schatten classes; K-convexity, the Rademacher projection on `L^q (S_q)` |
| [`NoncommutativeKhintchine/`](BanachProbability/NoncommutativeKhintchine), [`Noncommutative/`](BanachProbability/Noncommutative) | the noncommutative Khintchine inequality; conditional expectations, Cuculescu's projections, transforms, interpolation, Schatten UMD |

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## Licence

Apache 2.0 ([`LICENSE`](LICENSE)).
