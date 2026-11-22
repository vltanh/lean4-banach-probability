# BanachProbability

<placeholder: CI badge, once the repository is published>

A Lean 4 library of probability in Banach spaces: Rademacher sums and the Kahane–Khintchine
inequality, martingales and the UMD property, and their Schatten-class (noncommutative) versions.

**Status.** Every result below is proved. The library builds with no `sorry` and no axiom beyond
Lean's standard `propext`, `Classical.choice` and `Quot.sound`; `scripts/Audit.lean` checks this
for every declaration and fails otherwise.

## Contents

| Area | Directory | Main declarations |
| --- | --- | --- |
| Sign cube | `SignCube/` | `coin`, `avg`, `lpNorm`, `IsPredictable`, `paleyWalsh`, `condAvg`, `filtration` |
| Martingales | `Martingale/` | `martingaleTransform`, `runningMax`, `Burkholder.inequality`, `Burkholder.squareFunction`, `Burkholder.burkholderFun` |
| UMD | `UMD/` | `umdConst`, `dyadicUMDConst`, `complexUMDConst`, `pStar` |
| Schatten classes | `Schatten/` | `singularValue`, `schattenNorm`, `SchattenSpace`, `dilation`, `normingElement`, `spectralProj` |
| Hypercontractivity | `Hypercontractivity/` | `twoPointNorm`, `twoPoint`, `hypercontractive_affine` |
| Kahane–Khintchine | `KahaneKhintchine/` | `kahaneKhintchine`, `kahaneKhintchine_hypercontractive` |
| Noncommutative Khintchine | `NoncommutativeKhintchine/` | `ncKhintchine_upper`, `ncKhintchine_normal`, `pisierXu_khintchine` |
| Noncommutative martingales | `Noncommutative/` | `matrixCondExp`, `matrixTrace`, `ncTransform`, `cuculescu`, `weakType_one_one`, `umdConst_two_schattenSpace_le` |
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
| Burkholder's function `u_p (x, y) = p (1 − 1/p*)^{p−1} (‖y‖ − (p* − 1) ‖x‖) (‖x‖ + ‖y‖)^{p−1}`: `u_p (x, y) ≥ ‖y‖^p − (p* − 1)^p ‖x‖^p`, and `t ↦ u_p (x + t h, y + t k)` is concave for `‖k‖ ≤ ‖h‖` in a real inner product space | `Burkholder.burkholderFun_ge`, `Burkholder.burkholderFun_concaveOn_line` | Burkholder (1984); Burkholder (1988), proof of Thm 1.1 | proved |
| Hilbert spaces: `UMD_p (H) ≤ p* − 1` | `umdConst_le_of_innerProductSpace` | Burkholder (1984) | proved |
| Maurey: `UMD_p^Δ (X) = UMD_p (X)` | `dyadicUMDConst_eq_umdConst` | Maurey (1975); HNVW I, Thm 4.2.5 | proved |
| Extrapolation: `UMD_p < ∞` for all `p` once for one; `UMD₂ ≤ 200 UMD_p`, `UMD_p ≤ 100 p* UMD₂` | `umdConst_lt_top_of_lt_top`, `umdConst_two_le_mul`, `umdConst_le_mul_umdConst_two` | HNVW I, Thm 4.2.7; Burkholder's good-λ method (1973, 1981) | proved |
| Decoupling: `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p` for Paley–Walsh martingales | `decoupling`, `decoupling_dyadic` | HNVW I, Prop 4.2.3; McConnell (1989), Hitczenko (unpublished manuscript); Cox–Veraar (2007) | proved |
| Complex constants: `UMD_p ≤ UMD_{ℂ,p} ≤ (π/2) UMD_p` | `umdConst_le_complexUMDConst_le` | HNVW I, Prop 4.2.10; Yaroslavtsev (2018), Lemma 3.2 | proved |
| `UMD_p (L^p (μ; B)) ≤ UMD_p (B)`; the complex `L^p (μ)` is UMD, any measure | `umdConst_Lp_le`, `umdConst_Lp_complex_lt_top` | Pisier (2016), Cor 5.22 | proved |
| Weak type `(1, 1)` of noncommutative martingale transforms on `L^∞ (Ω) ⊗ M_n`, general filtrations: `λ τ (1_{(λ,∞)} (\|T_c x\|)) ≤ 52 ‖x‖_{L¹ (τ)}` | `weakType_one_one`, `weakType_one_one_of_posSemidef` | Randrianantoanina (2002), Thm 3.1 | proved |
| Schatten classes: `UMD_q (S_q^{n×n}) ≤ K q*`, `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)`, uniformly in `n` | `umdConst_schattenSpace_le`, `umdConst_two_schattenSpace_le` | Randrianantoanina (2002), Thm 4.3, Cor 4.5, Rem 4.6 | proved |
| Hypercontractive Kahane–Khintchine: `‖Σ ε_i x_i‖_q ≤ √((q−1)/(p−1)) ‖Σ ε_i x_i‖_p`, any seminorm | `kahaneKhintchine_hypercontractive` | Borell (1979); scalar two-point inequality: Bonami (1970), O'Donnell (2014), §10.1 | proved |
| Kahane–Khintchine: `‖Σ ε_i x_i‖_p ≤ κ_{p,q} ‖Σ ε_i x_i‖_q` | `kahaneKhintchine` | Kahane (1964); HNVW II, Thm 6.2.4 | proved |
| Noncommutative Khintchine, `q ≥ 2`: `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ ‖Σ ε_i x_i‖_{L^q (S_q)} ≤ √2 √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}` for normal `x_i` | `ncKhintchine_normal`, `pisierXu_khintchine` | Lust-Piquard (1986); Pisier–Xu (2003), Thm 6.1; proof of Mackey–Jordan–Chen–Farrell–Tropp (2014) | proved |
| Zig-zag concave functions characterise UMD | `umdConst_lt_top_iff_exists_isZigZagConcave` | Burkholder (1981); HNVW I, Thm 4.5.6; Yaroslavtsev (2018), Prop 3.7 | proved |

### Constants

| Result | Constant in the statement | Constant the proof gives |
| --- | --- | --- |
| Extrapolation, `UMD_r ≤ c UMD₂` | `100 r*` | `76 r` for `r ≥ 2`, `48 r′` for `r < 2` |
| Extrapolation, `UMD₂ ≤ c UMD_p` | `200` | `180` |
| Weak type `(1, 1)` (Theorem 3.1) | `26` (positive `x`), `52` (symmetric `x`) | the same; the source has `14√3/3 + 28` |
| Schatten classes, `UMD_q (S_q) ≤ K q*` | `∃ K` | `K = 192 · 864³` (`isUMDBound_schattenSpace`) |
| Noncommutative Khintchine, normal `x_i` | `√2 √q` (`pisierXu_khintchine`) | `√(2 (q − 1))` |
| Noncommutative Khintchine, symmetric `A_i` | `√(2 (q − 1))`, `q ≥ 2` (`ncKhintchine_symmetric_upper`) | `√(q − 1)` for `q ≥ 3` (`ncKhintchine_symmetric_upper_of_three_le`), the source's |
| Kahane–Khintchine | `κ_{p,q} = max (1, √((p − 1)/(q − 1)))` | the same |

## Method

Every result about Paley–Walsh martingales is proved on the finite sign cube, where expectations
are finite sums; Maurey's theorem then passes to arbitrary filtrations. The Schatten norm is
defined from the eigenvalues of `Aᵀ A` (`singularValue`). The noncommutative martingale results
follow Randrianantoanina's route on the von Neumann algebra `L^∞ (Ω) ⊗ M_n (ℝ)` of a filtered
probability space, with `τ = ∫ tr` and the conditional expectations `𝔼 [· | ℱ_k] ⊗ Id`
(`matrixCondExp`): Cuculescu's projections, taken pointwise as random projections, give the weak
type `(1, 1)` (Theorem 3.1); Marcinkiewicz interpolation and duality give the `L^r` bounds
(Theorem 4.3, in three regimes so that the constant stays uniform near `r = 2`, a detail the
source leaves out); Corollary 4.5 follows for martingales on any probability space, without
Maurey's theorem. Real matrices are reached from symmetric ones through the Hermitian dilation.
The module docstrings describe each argument, name its source, and record where a proof reads or
completes its source.

Some sources could not be consulted: HNVW I and II (Hytönen–van Neerven–Veraar–Weis), Bhatia's
*Matrix Analysis*, Lust-Piquard (1986), Pisier–Xu (2003), Burkholder (1973, 1981, 1984, 1988), and
Osękowski (2012). The results they are cited for are proved by named arguments from accessible
sources, and Burkholder's results by Burkholder's method in its standard form:

| Source not consulted | Result | Argument used |
| --- | --- | --- |
| HNVW I, Thm 4.2.5 | Maurey's theorem | finite models, dyadic perturbation and realization on a sign cube (Pisier's lecture notes (2011), Lemmas 8.29–8.31, Thm 8.32) |
| HNVW I, Thm 4.2.7; Burkholder (1973, 1981) | extrapolation | Burkholder's good-λ inequality as in Pisier's lecture notes (Lemma 8.20, second proof of Thm 8.12), layer cake and Doob's inequality |
| HNVW I, Prop 4.2.3 | decoupling | the argument from the definition (Montgomery-Smith, as credited by Cox–Veraar (2007)) |
| HNVW I, Prop 4.2.10 | complex constants | averaging `sgn cos (θ − φ)` over `φ`, with Riemann sums |
| HNVW I, Thm 4.5.6; Burkholder (1981) | zig-zag concavity | the standard Bellman-function argument: the supremum over Paley–Walsh pairs, splicing, and Bernstein–Doetsch for midpoint concavity |
| HNVW II, Thm 6.2.4 | Kahane–Khintchine | hypercontractivity (Bonami (1970), Borell (1979); O'Donnell (2014), §10.1) |
| Lust-Piquard (1986); Pisier–Xu (2003), Thm 6.1 | noncommutative Khintchine | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp (2014), Lemma 3.4, Cor 7.3, Rem 7.2, §8) |
| Bhatia (1997) | Weyl's inequalities, the Schatten triangle and Hölder inequalities | Courant–Fischer dimension counts; doubly substochastic matrices; overlaps `⟨u_j, v_k⟩²` (Mackey et al. (2014), Prop 7.5) |
| Burkholder (1984, 1988); Osękowski (2012), Thms 3.5, 8.6 | Burkholder's inequality and function, the square function inequality, `UMD_p (H) ≤ p* − 1` | Burkholder's method: the majorization `U ≥ V`, the concavity of `U` along lines (its pieces glued through one-sided derivatives at the kinks), and the integration of the concavity along the martingale |

## References

- A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst. Fourier 20
  (1970).
- C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire de
  Probabilités XIII, LNM 721 (1979).
- D. L. Burkholder, *Distribution function inequalities for martingales*, Ann. Probab. 1 (1973);
  *A geometrical characterization of Banach spaces in which martingale difference sequences are
  unconditional*, Ann. Probab. 9 (1981); *Boundary value problems and sharp inequalities for
  martingale transforms*, Ann. Probab. 12 (1984); *Sharp inequalities for martingales and
  stochastic integrals*, Astérisque 157–158 (1988).
- R. Bhatia, *Matrix Analysis*, Springer (1997).
- S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*,
  Electron. Commun. Probab. 12 (2007).
- I. Cuculescu, *Martingales on von Neumann algebras*, J. Multivariate Anal. 1 (1971).
- P. Hitczenko, *On tangent sequences of UMD-space valued random vectors*, unpublished manuscript
  (Cox–Veraar (2007) cite it without a year).
- T. Hytönen, J. van Neerven, M. Veraar, L. Weis (HNVW), *Analysis in Banach spaces I* (2016) and
  *II* (2017).
- S. Janson, *Gaussian Hilbert Spaces*, Cambridge University Press (1997).
- J.-P. Kahane, *Sur les sommes vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964).
- F. Lust-Piquard, *Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303
  (1986).
- F. Lust-Piquard, G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark. Mat. 29
  (1991).
- L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration inequalities
  via the method of exchangeable pairs*, Ann. Probab. 42 (2014).
- J. Marcinkiewicz, *Sur l'interpolation d'opérations*, C. R. Acad. Sci. Paris 208 (1939).
- B. Maurey, *Système de Haar*, Séminaire Maurey–Schwartz 1974–1975.
- T. R. McConnell, *Decoupling and stochastic integration in UMD Banach spaces*, Probab. Math.
  Statist. 10 (1989).
- S. Montgomery-Smith, *Concrete representation of martingales*, Electron. J. Probab. 3 (1998).
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press (2014).
- A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser (2012).
- G. Pisier, *Martingales in Banach spaces*, Cambridge University Press (2016); the lecture notes
  *Martingales in Banach spaces (in connection with type and cotype)*, IHP (2011).
- G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach Spaces 2
  (2003).
- N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002).
- I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite dimensions*,
  Indag. Math. 29 (2018).

Planned extensions, not stated yet: hypercontractivity of the noise operator for all functions on
the cube; Kahane–Khintchine for Rademacher sums on a probability space and for exponents
`p ∈ (0, 1]`; the noncommutative Khintchine inequality for rectangular and complex matrices;
Theorem 3.1 of Randrianantoanina for general semifinite von Neumann algebras and non-scalar
multipliers.

## Using the library

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`, the module system. In a `lakefile.toml`:

```toml
[[require]]
name = "BanachProbability"
git = "<placeholder: repository URL, not published yet>"
rev = "<placeholder: full commit hash>"
```

Build with `lake build`; audit the axioms with `lake env lean scripts/Audit.lean` (it fails if a
declaration of the library depends on `sorry` or on any axiom beyond `propext`, `Classical.choice`
and `Quot.sound`).

## Credits

Maintainers: <placeholder: names to be settled>.

Written with the AI system Claude (Anthropic), used through Claude Code; the AI system is not an
author or maintainer.

## Licence

Apache 2.0 (`LICENSE`).
