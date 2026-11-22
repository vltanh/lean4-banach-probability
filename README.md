# BanachProbability

[![Lean Action CI](https://github.com/vltanh/lean4-banach-probability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-banach-probability/actions/workflows/lean_action_ci.yml)

A Lean 4 library of probability in Banach spaces:

- Burkholder's inequality for Hilbert-space-valued martingales, its square function inequality, and
  the sharpness of the constant `p* − 1`;
- UMD constants: the reduction to Paley–Walsh martingales, extrapolation, the randomised UMD
  property and decoupling, real against complex constants, and Burkholder's zig-zag concave
  functions;
- hypercontractivity on the cube and the Kahane–Khintchine inequality in seminormed spaces;
- Schatten classes: the Schatten norms, the noncommutative Khintchine inequality, martingale
  transforms with values in matrices, and the UMD property of `S_q`, uniformly in the dimension.

**Status.** Every result below is proved, and no theorem takes an unproved result as a hypothesis.
The library builds with no `sorry` and no axiom beyond Lean's standard `propext`, `Classical.choice`
and `Quot.sound`; `scripts/Audit.lean` checks this for every declaration and fails otherwise.

**Not formalized.** The equality cases of Burkholder's inequality and the sharpness clauses of the
square function inequality; σ-finite measure spaces (the constants are defined with probability
spaces in `Type` and martingales started at `0`); extrapolation and the randomised UMD property over
complex scalars; the converse of the randomised UMD property for Paley–Walsh martingales; the
necessity of the condition on the exponents in the hypercontractive inequality; Borell's theorem for
Walsh polynomials of degree `≥ 2`; complex Rademacher variables; rectangular or complex matrices and
exponents below `2` in the noncommutative Khintchine inequality; general semifinite von Neumann
algebras and non-scalar multipliers in the noncommutative martingale results.

**Planned extensions.** Kahane–Khintchine for Rademacher sums on a probability space; the
noncommutative Khintchine inequality for rectangular and complex matrices, and, in a separate package,
a proof of it along the route of Lust-Piquard and Pisier; Randrianantoanina's Theorem 3.1 for general
semifinite von Neumann algebras and non-scalar multipliers.

## Results

`UMD_p (X)` is `umdConst X p`, the best `β ∈ [0, ∞]` in
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}` over all `X`-valued martingales `Y` (Mathlib's
`MeasureTheory.Martingale`) with `Y_0 = 0` and all predictable signs `σ`; `UMD_{ℂ,p} (X)` is the same
with predictable unimodular complex multipliers, and `UMD_p^Δ`, `UMD_{ℂ,p}^Δ` are the restrictions to
Paley–Walsh martingales on sign cubes `Fin N → Bool`. Moreover `1 < p < ∞`, `p' = p/(p − 1)`,
`p* = max (p, p')`, the `ε_i` are independent fair signs, and `‖·‖_p` is an `L^p` norm. All
declarations are in the namespace `BanachProbability`; modules are relative to
`BanachProbability/`. HNVW is Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach Spaces*; the full
references are in [docs/REFERENCES.md](docs/REFERENCES.md).

### Martingales in Hilbert spaces

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| Burkholder's inequality: for martingales `f`, `g` in a real Hilbert space with `‖g_0‖ ≤ ‖f_0‖` and `‖g_{n+1} − g_n‖ ≤ ‖f_{n+1} − f_n‖` a.s., `‖g_n‖_p ≤ (p* − 1) ‖f_n‖_p` | `Osekowski.eLpNorm_le_of_subordinate`; started at `0`: `Burkholder.inequality_of_subordinate` | Osękowski (2012), Thm 3.5 (ii); Burkholder (1988), Thm 1.1 | `Martingale/Osekowski/Moment`, `Martingale/Burkholder/Inequality` |
| Sharpness: for `K < p* − 1` there are a real Paley–Walsh martingale `f` and a transform `g` of it by predictable signs with `K ‖f‖_p < ‖g‖_p`; for every real Hilbert space `H ≠ 0`, `UMD_p (H) = UMD_p^Δ (H) = p* − 1` | `Osekowski.exists_lt_lpNorm_transform`, `Osekowski.umdConst_of_innerProductSpace`, `Osekowski.dyadicUMDConst_of_innerProductSpace` | Osękowski (2012), Thm 3.5, Rem 3.8 | `Martingale/Osekowski/Sharpness` |
| Square function, `𝒮_n X = (Σ_{k<n} ‖X_{k+1} − X_k‖²)^{1/2}`: `‖𝒮_n X‖_p ≤ (p* − 1) ‖X_n‖_p` and `‖X_n‖_p ≤ (p* − 1) ‖𝒮_n X‖_p` for a martingale `X` in a real Hilbert space with `X_0 = 0` | `Burkholder.squareFunction_of_martingale` | Osękowski (2012), Thm 8.6; Burkholder (1988), Thm 3.1 | `Martingale/Burkholder/Inequality` |
| Burkholder's function `u_p (x, y) = p (1 − 1/p*)^{p−1} (‖y‖ − (p* − 1) ‖x‖) (‖x‖ + ‖y‖)^{p−1}`: `u_p (x, y) ≥ ‖y‖^p − (p* − 1)^p ‖x‖^p`, and `t ↦ u_p (x + t h, y + t k)` is concave for `‖k‖ ≤ ‖h‖` in a real inner product space | `Burkholder.burkholderFun_ge`, `Burkholder.burkholderFun_concaveOn_line` | Burkholder (1988), (1.6), (1.10), Rem 1.2 | `Martingale/Burkholder/Function` |
| Doob, Banach-space-valued martingales: `‖max_{k≤n} ‖Y_k‖‖_p ≤ p' ‖Y_n‖_p` | `eLpNorm_runningMax_norm_le` | standard argument | `Martingale/Doob` |

### UMD constants

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| `UMD_p^Δ (X) = UMD_p (X)` and `UMD_{ℂ,p}^Δ (X) = UMD_{ℂ,p} (X)` | `dyadicUMDConst_eq_umdConst`, `complexDyadicUMDConst_eq_complexUMDConst` | Maurey (1974–75); HNVW I, Thm 4.2.5 | `UMD/Maurey/Basic` |
| Deterministic and predictable multipliers give the same constants, real and complex | `umdConst_eq_sInf_isDeterministicUMDBound`, `complexUMDConst_eq_sInf_isDeterministicUMDBound` | HNVW I, Thm 4.2.25 | `UMD/Incremental` |
| Extrapolation, `p, q ∈ (1, ∞)`: `UMD_p ≤ 100 (p/q + p'/q') UMD_q` (for the transforms the proof gives `80` in place of `100`: `IsTransformBound.extrapolation`); `UMD₂ ≤ 200 UMD_p`, `UMD_p ≤ 50 (p + p') UMD₂ ≤ 100 p* UMD₂`; finite for one `p` implies finite for all | `umdConst_le_mul_umdConst`, `umdConst_two_le_mul`, `umdConst_le_fifty_mul_umdConst_two`, `umdConst_le_mul_umdConst_two`, `umdConst_lt_top_of_lt_top` | HNVW I, Thm 4.2.7 | `UMD/Extrapolation` |
| Randomised UMD property: a `UMD_p` constant `β` satisfies `β⁻¹ ‖Y_n‖_p ≤ ‖Σ_{k<n} ε_k (Y_{k+1} − Y_k)‖_p ≤ β ‖Y_n‖_p`; two such inequalities with constants `β⁻`, `β⁺` give the `UMD_p` constant `β⁻ β⁺` | `IsUMDBound.isLowerRandomisedUMDBound`, `IsUMDBound.isUpperRandomisedUMDBound`, `isUMDBound_of_randomised` | HNVW I, Prop 4.2.3 | `UMD/Decoupling` |
| Decoupling of a Paley–Walsh martingale `Y_n = Σ_{k<n} ε_k ξ_k`, with `Ỹ_n = Σ_{k<n} ε̃_k ξ_k` for an independent copy `ε̃` of the signs: `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p`, also with `UMD_p^Δ` | `decoupling`, `decoupling_dyadic` | HNVW I, Prop 4.2.3 (cf. McConnell (1989); Cox–Veraar (2007)) | `UMD/Decoupling` |
| `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π/2) UMD_p (X)`, `X` complex | `umdConst_le_complexUMDConst_le` | HNVW I, Prop 4.2.10 | `UMD/Complex`, `UMD/ConvexHull` |
| `UMD_p (L^p (μ; B)) ≤ UMD_p (B)` for every measure `μ`; `UMD_p (L^p (μ; ℂ)) ≤ p* − 1` | `umdConst_Lp_le`, `umdConst_Lp_complex_le` | Pisier (2016), Cor 5.22 | `UMD/Lp` |
| `UMD_p (X) < ∞` if and only if, for some `β > 0`, there is `U : X × X → ℝ` with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` and `z ↦ U (x + z, y + ε z)` concave for `ε ∈ [−1, 1]`; the least such `β ≥ 0` is `UMD_p (X)`. The same over `ℂ`, with `ε` in the closed unit disc and `UMD_{ℂ,p}` | `umdConst_lt_top_iff_exists_isZigZagConcave`, `isLeast_umdConst_isZigZagConcave`, `complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave`, `isLeast_complexUMDConst_isComplexZigZagConcave` | Burkholder (1981, 1986); HNVW I, Thm 4.5.6; Yaroslavtsev (2018), Prop 3.7 | `ZigZag/Basic` |

### Hypercontractivity and Kahane–Khintchine

The values are in a real vector space with a seminorm; completeness is not needed.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| The discrete heat semigroup on functions of `n` signs: `‖T (t) f‖_q ≤ ‖f‖_p` for `1 < p ≤ q` and `e^{−t} ≤ √((p−1)/(q−1))` | `heatSemigroup_lpNorm_le`; one sign: `bonami_seminorm` | HNVW II, Thm 6.2.2 and Lemma 6.2.3 ("if" parts) | `Hypercontractivity/HeatSemigroup` |
| Borell's operator `⊗ⁿ K̄` (kernel `Π_i (1 + ρ x_i y_i)`, `ρ = √((p−1)/(q−1))`), `1 < p ≤ q`: `‖(⊗ⁿ K̄) f‖_q ≤ ‖f‖_p`, hence `‖c + ρ Σ ε_i x_i‖_q ≤ ‖c + Σ ε_i x_i‖_p` | `kBarTensor_lpNorm_le`, `hypercontractive_affine` | Borell (1979), (2.1) | `Hypercontractivity/Vector` |
| Kahane–Khintchine: `‖Σ ε_i x_i‖_q ≤ √((q−1)/(p−1)) ‖Σ ε_i x_i‖_p` for `1 < p ≤ q`; `‖Σ ε_i x_i‖_p ≤ max (1, √((p−1)/(q−1))) ‖Σ ε_i x_i‖_q` for all `p, q > 1`; with some constant depending only on `p` and `q` for all `p, q ∈ (0, ∞)` | `kahaneKhintchine_hypercontractive`, `kahaneKhintchine`, `exists_kahaneKhintchine` | Kahane (1964); HNVW II, Thm 6.2.4 | `KahaneKhintchine/Basic` |

### Schatten classes

The matrices are real; `S_q` is the norm `schattenNorm`, defined from the eigenvalues of `Aᵀ A`. On
`L^∞ (Ω) ⊗ M_n (ℝ)`, `τ = ∫ tr`, and `T_c x = E_0 x + Σ_{k<N} c_k (E_{k+1} x − E_k x)` is the martingale
transform by predictable scalar multipliers `|c_k| ≤ 1`, for a general filtration.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| `‖A + B‖_{S_q} ≤ ‖A‖_{S_q} + ‖B‖_{S_q}`, `q ∈ [1, ∞]`, `m × n` matrices | `schattenNorm_add_le` | Bourin–Zhang (2026), Prop 3.13, Rem 3.14 | `Schatten/Triangle` |
| `\|tr (A B)\| ≤ ‖A‖_{S_r} ‖B‖_{S_{r'}}` for symmetric `A`, `B` and `r > 1` | `abs_trace_mul_le_of_isHermitian` | Mackey et al. (2014), Prop 7.5 | `Schatten/Holder` |
| Noncommutative Khintchine, upper bound, `q ≥ 2`: `‖Σ ε_i x_i‖_{L^q (S_q)} ≤ √(2(q−1)) max (‖Σ x_i x_iᵀ‖_{S_{q/2}}, ‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`; the constant is `√(q−1)` for symmetric `x_i` and `q ≥ 3` | `ncKhintchine_upper`, `ncKhintchine_symmetric_upper`, `ncKhintchine_symmetric_upper_of_three_le` | Lust-Piquard (1986), Pisier–Xu (2003), Thm 6.1; proof of Mackey et al. (2014), Cor 7.3 | `NoncommutativeKhintchine/Basic`, `NoncommutativeKhintchine/Symmetric` |
| Lower bound with constant `1`, rows and columns, `q ≥ 2`; both bounds for normal `x_i`, the upper one with `√2 √q` | `ncKhintchine_lower_row`, `ncKhintchine_lower_col`, `ncKhintchine_normal`, `pisierXu_khintchine` | Lust-Piquard (1986); Pisier–Xu (2003), Thm 6.1 | `NoncommutativeKhintchine/Lower`, `NoncommutativeKhintchine/Basic` |
| Weak type `(1, 1)`: `λ τ (1_{(λ,∞)} (\|T_c x\|)) ≤ 52 ‖x‖_{L¹ (τ)}` for symmetric `x`, and with `26` for `x ⪰ 0` (the source has `14√3/3 + 28`) | `weakType_one_one`, `weakType_one_one_of_posSemidef` | Randrianantoanina (2002), Thm 3.1 | `Noncommutative/WeakType` |
| `‖T_c x‖_{L^r (S_r)} ≤ K r* ‖x‖_{L^r (S_r)}`, `1 < r < ∞`, `K = 192 · 864³` | `eLpNorm_ncTransform_le` | Randrianantoanina (2002), Thm 4.3 | `Noncommutative/SchattenUMD` |
| `UMD_q (S_q^{n×n}) ≤ K q*` and `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)`, with `K` and `C` independent of `q ∈ (1, ∞)` and `n` | `umdConst_schattenSpace_le`, `isUMDBound_schattenSpace` (`K = 192 · 864³`), `umdConst_two_schattenSpace_le` | Randrianantoanina (2002), Cor 4.5, Rem 4.6 (1) | `Noncommutative/SchattenUMD` |

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
  Lemma 3.4 that they do not prove; it is proved here (`trace_mean_value`). This is a shorter proof
  than the original one (Lust-Piquard; Lust-Piquard and Pisier); a proof along the original route is
  planned in a separate package.
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
| Burkholder (1988) | Numdam, `AST_1988__157-158__75_0` | Burkholder's function: (1.10), Remark 1.2 | Remark 1.2, stated there without proof, is completed from (1.14) |
| HNVW I (2016) | the book | Props 4.2.3, 4.2.10; Thms 4.2.5, 4.2.7, 4.2.25, 4.5.6 | in Theorem 4.5.6, Steps 2 and 3 are reordered, and the multipliers lie in the closed unit ball, as in Yaroslavtsev (2018) |
| HNVW II (2017) | the book | Thms 6.2.2, 6.2.4 | an edge case of Lemma 6.2.3 by continuity |
| Borell (1979) | Numdam, `SPS_1979__13__1_0` | `⊗ⁿ K̄`, the affine inequality | the two results that Borell cites (Gross; Beckner) are proved by O'Donnell's arguments |
| O'Donnell (2014) | the book | two-point inequality and tensorisation (§10.1, Exercises 9.7, 10.1, 10.3) | none |
| Randrianantoanina (2002) | arXiv:math/0111264 | Thms 3.1, 4.3, Cor 4.5, Rem 4.6 (1) | a rank count for Lemma 3.2; the interpolation is written out |
| Mackey et al. (2014) | arXiv:1201.6002 | noncommutative Khintchine, trace Hölder | the variant of Lemma 3.4 for `2 < q < 3` is proved |
| Bourin–Zhang (2026) | arXiv:2610.30538 | the triangle inequality | real `m × n` matrices; von Neumann's inequality, quoted there, is proved by Peierls's argument (its Jensen step is in the proof of Fehr (2021), Thm 7.1) |
| Burkholder (1973, 1981) | Ann. Probab. | origin of the good-λ method and of the characterization of UMD | not followed: the proofs are HNVW's |

Cited for a statement or its origin, with another argument here: Maurey (1974–75); Burkholder
(1984); Kahane (1964); Bonami (1970); Lust-Piquard (1986); Lust-Piquard–Pisier (1991); Pisier–Xu
(2003), which states its Theorem 6.1 without proof; Pisier (2016), Cor 5.22, proved here on
Paley–Walsh martingales. Burkholder (1986) is followed through HNVW I. Not used: Bhatia (1997) and
Carlen (2010), the usual references for the triangle inequality, Weyl's inequalities and Peierls's
inequality. Not obtained: Gross (1975) and Beckner (1975), which Borell cites.

## Literature

Reviewed on 2026-11-22 in Crossref, zbMATH, arXiv and Numdam. Preprints are reported as claims of
their authors.

| Result | Origin | State of the question |
| --- | --- | --- |
| Burkholder's inequality | Burkholder 1966 (martingale transforms), 1984 (sharp constant, real martingales), 1988 (Hilbert-valued, differential subordination); Osękowski 2012 (monograph) | `p* − 1` is best possible; in the square function inequality it is best possible in two of the four cases, and in the other two the best constants were unknown in 1988 (Burkholder, Rem. 3.1) and in 2012 (Osękowski, Thm 8.6) |
| UMD constants | Maurey 1974–75 (Paley–Walsh martingales), Burkholder 1981 (geometric characterization), Bourgain 1983 (Hilbert transform); monographs: HNVW 2016, 2017, 2023, Pisier 2016 | whether `UMD_p = UMD_{ℂ,p}` was an open question in 2018 (Yaroslavtsev); linear bounds between the UMD constant and the norm of the Hilbert transform fail in both directions, according to a 2026 preprint of Lorist and van Neerven |
| Kahane–Khintchine, hypercontractivity | Kahane 1964; Bonami 1970, Beckner 1975; Borell 1979 | scalar best constants: Haagerup 1981; the best `L²`–`L¹` constant in normed spaces is `√2` (Latała–Oleszkiewicz 1994); the constants here are not claimed to be sharp |
| UMD of Schatten classes | Pisier–Xu 1997 (noncommutative martingale inequalities); Randrianantoanina 2002 (weak type `(1, 1)`, optimal order in `p`) | no exact value of `UMD_p (S_p)` was found |
| Noncommutative Khintchine | Lust-Piquard 1986; Lust-Piquard–Pisier 1991 (`p = 1`); Buchholz 2001, 2005; Mackey et al. 2014 | best constants known for even `q` (Buchholz); `√(q − 1)`, for `q = 2` and `q ≥ 3`, is within a factor `√e` of them (Mackey et al.); a sharp `p = 1` Rademacher constant is claimed in a preprint of Chuah, Liu and Mei |

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
| Archive of Formal Proofs (Isabelle); FormalML, MathComp-Analysis (Rocq); HOL4 | martingales and their convergence, optional stopping, concentration inequalities | none of the results above was found |

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

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`, the module system. In a `lakefile.toml`, with `<commit>`
replaced by the full hash of the commit to use:

```toml
[[require]]
name = "BanachProbability"
git = "https://github.com/vltanh/lean4-banach-probability"
rev = "<commit>"
```

Build with `lake build`; audit the axioms with `lake env lean scripts/Audit.lean` (it fails if a
declaration of the library depends on `sorry` or on any axiom beyond `propext`, `Classical.choice`
and `Quot.sound`).

| Directory | Contents |
| --- | --- |
| `SignCube/` | signs on `Fin N → Bool`, averages, predictable families, Paley–Walsh martingales, the bridge to Mathlib's martingales |
| `Martingale/` | martingale transforms, Doob's inequality, Burkholder's function and inequality, Osękowski's method |
| `UMD/`, `ZigZag/` | UMD constants; zig-zag concave functions |
| `Hypercontractivity/`, `KahaneKhintchine/` | two-point inequality, heat semigroup, Borell's operator; Kahane–Khintchine |
| `Schatten/` | singular values, Schatten norms and spaces, Hermitian dilation, trace inequalities, measurability |
| `NoncommutativeKhintchine/`, `Noncommutative/` | the noncommutative Khintchine inequality; conditional expectations, Cuculescu's projections, transforms, interpolation, Schatten UMD |

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## Licence

Apache 2.0 (`LICENSE`).
