# BanachProbability

A Lean 4 library of probability in Banach spaces: Rademacher sums and the Kahane–Khintchine
inequality, martingales and the UMD property, and their Schatten-class (noncommutative) versions.

**Status.** The definitions and the statements of all results below are written, and the library
builds. Burkholder's inequalities, the bridge from the sign cube to Mathlib's martingales and a
few elementary lemmas are proved; every other theorem is still proved by `sorry`
(`scripts/Audit.lean` lists them).

## Contents

| Area | Directory | Main declarations |
| --- | --- | --- |
| Sign cube | `SignCube/` | `coin`, `avg`, `lpNorm`, `IsPredictable`, `paleyWalsh`, `condAvg`, `transform`, `filtration` |
| Martingales | `Martingale/` | `martingaleTransform`, `runningMax`, `Burkholder.inequality`, `Burkholder.squareFunction` |
| UMD | `UMD/` | `umdConst`, `dyadicUMDConst`, `complexUMDConst`, `pStar` |
| Schatten classes | `Schatten/` | `singularValue`, `schattenNorm`, `SchattenSpace`, `dilation`, `normingElement` |
| Hypercontractivity | `Hypercontractivity/` | `twoPointNorm`, `twoPoint`, `hypercontractive_affine` |
| Kahane–Khintchine | `KahaneKhintchine/` | `kahaneKhintchine`, `kahaneKhintchine_hypercontractive` |
| Noncommutative Khintchine | `NoncommutativeKhintchine/` | `ncKhintchine_upper`, `ncKhintchine_normal`, `pisierXu_khintchine` |
| Noncommutative martingales | `Noncommutative/` | `cubeTrace`, `cuculescu`, `weakType_one_one`, `umdConst_two_schattenSpace_le` |
| Zig-zag concavity | `ZigZag/` | `IsZigZagConcave`, `bellmanFunction`, `umdConst_lt_top_iff_exists_isZigZagConcave` |

All declarations are in the namespace `BanachProbability`; the sign cube is
`BanachProbability.SignCube`.

## Main results

`N` fair signs live on `Fin N → Bool` with the uniform probability; `‖·‖_{L^p}` is
`SignCube.lpNorm`. `UMD_p (X)` is `umdConst X p`, the best constant in
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}` over all `X`-valued martingales (Mathlib's
`MeasureTheory.Martingale`) and predictable signs; `UMD_p^Δ` is its restriction to Paley–Walsh
martingales; `p* = max (p, p / (p − 1))`.

| Result | Lean | Source | Proof |
| --- | --- | --- | --- |
| Burkholder: `‖X_n‖_p ≤ (p* − 1) ‖Y_n‖_p` for differentially subordinate Hilbert-space martingales, and the square function inequality | `Burkholder.inequality_of_subordinate`, `Burkholder.squareFunction_of_martingale` | Burkholder (1984); Osękowski (2012), Thms 3.5, 8.6 | proved |
| Hilbert spaces: `UMD_p (H) ≤ p* − 1` | `umdConst_le_of_innerProductSpace` | Burkholder (1984) | open |
| Maurey: `UMD_p^Δ (X) = UMD_p (X)` | `dyadicUMDConst_eq_umdConst` | Maurey (1975); HNVW I, Thm 4.2.5 | open |
| Extrapolation: `UMD_p < ∞` for all `p` once for one; `UMD₂ ≤ 200 UMD_p`, `UMD_p ≤ 100 p* UMD₂` | `umdConst_lt_top_of_lt_top`, `umdConst_two_le_mul`, `umdConst_le_mul_umdConst_two` | HNVW I, Thm 4.2.7; Burkholder's good-λ method (1973, 1981) | open |
| Decoupling: `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p` for Paley–Walsh martingales | `decoupling`, `decoupling_dyadic` | HNVW I, Prop 4.2.3; Cox–Veraar (2007) | open |
| Complex constants: `UMD_p ≤ UMD_{ℂ,p} ≤ (π/2) UMD_p` | `umdConst_le_complexUMDConst_le` | HNVW I, Prop 4.2.10; Yaroslavtsev (2018), Lemma 3.2 | open |
| `UMD_p (L^p (μ; B)) ≤ UMD_p (B)`; the complex `L^p (μ)` is UMD, any measure | `umdConst_Lp_le`, `umdConst_Lp_complex_lt_top` | Pisier (2016), Cor 5.22 | open |
| Schatten classes: `UMD_q (S_q^{n×n}) ≤ K q*`, `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)`, uniformly in `n` | `umdConst_schattenSpace_le`, `umdConst_two_schattenSpace_le` | Randrianantoanina (2002), Thm 3.1, Thm 4.3, Cor 4.5, Rem 4.6 | open |
| Hypercontractive Kahane–Khintchine: `‖Σ ε_i x_i‖_q ≤ √((q−1)/(p−1)) ‖Σ ε_i x_i‖_p`, any seminorm | `kahaneKhintchine_hypercontractive` | Bonami (1970); Borell (1979); O'Donnell (2014), §10.1 | open |
| Kahane–Khintchine: `‖Σ ε_i x_i‖_p ≤ κ_{p,q} ‖Σ ε_i x_i‖_q` | `kahaneKhintchine` | Kahane (1964); HNVW II, Thm 6.2.4 | open |
| Noncommutative Khintchine, `q ≥ 2`: `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ ‖Σ ε_i x_i‖_{L^q (S_q)} ≤ √2 √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}` for normal `x_i` | `ncKhintchine_normal`, `pisierXu_khintchine` | Lust-Piquard (1986); Pisier–Xu (2003), Thm 6.1; proof of Mackey–Jordan–Chen–Farrell–Tropp (2014) | open |
| Zig-zag concave functions characterise UMD | `umdConst_lt_top_iff_exists_isZigZagConcave` | Burkholder (1981); HNVW I, Thm 4.5.6; Yaroslavtsev (2018), Prop 3.7 | open |

Where a proof gives an explicit constant different from its source's, the docstring says so (for
example `√(2 (q − 1))` in the noncommutative Khintchine inequality).

## Method

Every result about Paley–Walsh martingales is proved on the finite sign cube, where expectations
are finite sums; Maurey's theorem then passes to arbitrary filtrations. The Schatten norm is
defined from the eigenvalues of `Aᵀ A` (`singularValue`), and the noncommutative martingale
results are proved on the finite-dimensional algebra of matrix-valued functions on the cube. The
module docstrings describe each argument and name its source.

References:

- A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst. Fourier 20
  (1970).
- C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire de
  Probabilités XIII, LNM 721 (1979).
- D. L. Burkholder, *Distribution function inequalities for martingales*, Ann. Probab. 1 (1973);
  *A geometrical characterization of Banach spaces in which martingale difference sequences are
  unconditional*, Ann. Probab. 9 (1981); *Boundary value problems and sharp inequalities for
  martingale transforms*, Ann. Probab. 12 (1984).
- S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*,
  Electron. Commun. Probab. 12 (2007).
- T. Hytönen, J. van Neerven, M. Veraar, L. Weis (HNVW), *Analysis in Banach spaces I* (2016) and
  *II* (2017).
- J.-P. Kahane, *Sur les sommes vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964).
- F. Lust-Piquard, *Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303
  (1986).
- L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration inequalities
  via the method of exchangeable pairs*, Ann. Probab. 42 (2014).
- B. Maurey, *Système de Haar*, Séminaire Maurey–Schwartz 1974–1975.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press (2014).
- A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser (2012).
- G. Pisier, *Martingales in Banach spaces*, Cambridge University Press (2016).
- G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach Spaces 2
  (2003).
- N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002).
- I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite dimensions*,
  Indag. Math. 29 (2018).

## Using the library

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`, the module system. In a `lakefile.toml`:

```toml
[[require]]
name = "BanachProbability"
git = "<placeholder: repository URL, not published yet>"
rev = "<placeholder: full commit hash>"
```

Build with `lake build`; audit the axioms with `lake env lean scripts/Audit.lean` (it lists the
declarations that still depend on `sorry`, and fails on any other non-standard axiom).

## Credits

Maintainers: <placeholder: names to be settled>.

Written with the AI system Claude (Anthropic), used through Claude Code; the AI system is not an
author or maintainer.

## Licence

Apache 2.0 (`LICENSE`).
