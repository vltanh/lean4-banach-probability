module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library and per Solution of `palomar/`, so that the proofs
-- are visible (the module system hides them from a plain `import`). Generate the lines with
--   { find BanachProbability -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- No Challenge is imported: each holds a copy of definitions of the library.
import all BanachProbability.Defs
import all BanachProbability.Hypercontractivity.Binomial
import all BanachProbability.Hypercontractivity.HeatSemigroup
import all BanachProbability.Hypercontractivity.TwoPoint
import all BanachProbability.Hypercontractivity.Vector
import all BanachProbability.KConvexity.Basic
import all BanachProbability.KConvexity.Schatten
import all BanachProbability.KahaneKhintchine.Basic
import all BanachProbability.Martingale.Burkholder.Function
import all BanachProbability.Martingale.Burkholder.Inequality
import all BanachProbability.Martingale.Doob
import all BanachProbability.Martingale.Osekowski.Integral
import all BanachProbability.Martingale.Osekowski.Method
import all BanachProbability.Martingale.Osekowski.Moment
import all BanachProbability.Martingale.Osekowski.Sharpness
import all BanachProbability.Martingale.Osekowski.SimpleFunctions
import all BanachProbability.Martingale.Transform
import all BanachProbability.Noncommutative.ComplexSchattenUMD
import all BanachProbability.Noncommutative.CondExp
import all BanachProbability.Noncommutative.Cuculescu
import all BanachProbability.Noncommutative.Distribution
import all BanachProbability.Noncommutative.Duality
import all BanachProbability.Noncommutative.Interpolation
import all BanachProbability.Noncommutative.MatrixUMD
import all BanachProbability.Noncommutative.SchattenUMD
import all BanachProbability.Noncommutative.Transform
import all BanachProbability.Noncommutative.WeakType
import all BanachProbability.NoncommutativeKhintchine.Basic
import all BanachProbability.NoncommutativeKhintchine.Lower
import all BanachProbability.NoncommutativeKhintchine.Symmetric
import all BanachProbability.RandomSums.Contraction
import all BanachProbability.Schatten.Basic
import all BanachProbability.Schatten.Block
import all BanachProbability.Schatten.Complex
import all BanachProbability.Schatten.CubeDuality
import all BanachProbability.Schatten.Dilation
import all BanachProbability.Schatten.Holder
import all BanachProbability.Schatten.Horn
import all BanachProbability.Schatten.Measurable
import all BanachProbability.Schatten.Space
import all BanachProbability.Schatten.Spectral
import all BanachProbability.Schatten.ThreeLines
import all BanachProbability.Schatten.Trace
import all BanachProbability.Schatten.Triangle
import all BanachProbability.SignCube.Basic
import all BanachProbability.SignCube.Bridge
import all BanachProbability.SignCube.LpSeminorm
import all BanachProbability.SignCube.PaleyWalsh
import all BanachProbability.SignCube.Walsh
import all BanachProbability.TypeTwo.Basic
import all BanachProbability.TypeTwo.Even
import all BanachProbability.TypeTwo.Schatten
import all BanachProbability.UMD.Complex
import all BanachProbability.UMD.ConvexHull
import all BanachProbability.UMD.CubeTransform
import all BanachProbability.UMD.Decoupling
import all BanachProbability.UMD.Defs
import all BanachProbability.UMD.Extrapolation
import all BanachProbability.UMD.GoodLambda
import all BanachProbability.UMD.Hilbert
import all BanachProbability.UMD.Incremental
import all BanachProbability.UMD.Lp
import all BanachProbability.UMD.Maurey.Basic
import all BanachProbability.UMD.Maurey.FiniteModel
import all BanachProbability.UMD.Maurey.StepApprox
import all BanachProbability.ZigZag.Basic
import all BanachProbability.ZigZag.Bellman
import all BanachProbability.ZigZag.Concave
import all Burkholder.Solution
import all Decoupling.Solution
import all KahaneKhintchine.Solution
import all NoncommutativeKhintchine.Solution
import all SchattenClasses.Solution
import all TypeTwo.Solution
import all UMD.Solution
import all ZigZag.Solution

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Checks every declaration of the library and of the Solutions in `palomar/`, including private and
auxiliary ones: the run fails if one depends on an axiom other than Lean's standard `propext`,
`Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`, and fails the run too
(`allowSorry := false`); with `allowSorry := true`, for work in progress, the declarations that depend
on `sorryAx` are listed instead. (The Challenges in `palomar/`, whose theorems are stated with
`sorry`, are not imported.) Prints the axioms on which the theorems of the Solutions depend.
-/

open Lean Elab Command

namespace Audit

/-- Whether declarations may still depend on `sorryAx`. -/
meta def allowSorry : Bool := false

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The theorems of the Challenges in `palomar/`, as proved in the Solutions. -/
meta def solutionResults : List Name :=
  [``BurkholderChallenge.burkholder_inequality,
   ``BurkholderChallenge.squareFunction_inequality,
   ``BurkholderChallenge.burkholder_sharp,
   ``BurkholderChallenge.martingale_paleyWalsh,
   ``BurkholderChallenge.burkholderFun_majorizes,
   ``BurkholderChallenge.burkholderFun_concave,
   ``DecouplingChallenge.randomisedUMD,
   ``DecouplingChallenge.umd_of_randomised,
   ``DecouplingChallenge.decoupling,
   ``DecouplingChallenge.eLpNorm_uniformOn,
   ``KahaneKhintchineChallenge.lpNorm_eq_eLpNorm,
   ``KahaneKhintchineChallenge.heatSemigroup_walsh,
   ``KahaneKhintchineChallenge.heatSemigroup_hypercontractive,
   ``KahaneKhintchineChallenge.bonami,
   ``KahaneKhintchineChallenge.hypercontractive_affine,
   ``KahaneKhintchineChallenge.kahaneKhintchine,
   ``KahaneKhintchineChallenge.exists_kahaneKhintchine,
   ``KahaneKhintchineChallenge.contraction_real,
   ``KahaneKhintchineChallenge.contraction_complex,
   ``NoncommutativeKhintchineChallenge.khintchine,
   ``NoncommutativeKhintchineChallenge.khintchine_symmetric,
   ``NoncommutativeKhintchineChallenge.schattenNorm_transpose_mul_self,
   ``NoncommutativeKhintchineChallenge.schattenNorm_two_sq,
   ``SchattenClassesChallenge.schattenNorm_eq_singularValues,
   ``SchattenClassesChallenge.complexSchattenNorm_eq_singularValues,
   ``SchattenClassesChallenge.schattenNorm_triangle,
   ``SchattenClassesChallenge.horn_prod,
   ``SchattenClassesChallenge.horn_sum,
   ``SchattenClassesChallenge.schattenNorm_holder,
   ``SchattenClassesChallenge.abs_trace_mul_le,
   ``SchattenClassesChallenge.weakType_posSemidef,
   ``SchattenClassesChallenge.weakType,
   ``SchattenClassesChallenge.transform_bounded,
   ``SchattenClassesChallenge.umd_schatten,
   ``SchattenClassesChallenge.umd_two_schatten,
   ``TypeTwoChallenge.typeTwo_hilbert,
   ``TypeTwoChallenge.gaussianTypeTwo_of_typeTwo,
   ``TypeTwoChallenge.typeTwo_of_gaussianTypeTwo,
   ``TypeTwoChallenge.kConvex_of_gaussianTypeTwo,
   ``TypeTwoChallenge.kConvex_of_typeTwo,
   ``TypeTwoChallenge.kConvex_of_piLp,
   ``TypeTwoChallenge.typeTwo_schatten_interp,
   ``TypeTwoChallenge.typeTwo_schatten,
   ``TypeTwoChallenge.rademacherProj_schatten,
   ``TypeTwoChallenge.rademacherProj_schatten_conj,
   ``UMDChallenge.isUMDBound_iff_deterministic,
   ``UMDChallenge.dyadicUMDConst_eq_umdConst,
   ``UMDChallenge.umdConst_extrapolation,
   ``UMDChallenge.umdConst_two_comparison,
   ``UMDChallenge.umdConst_Lp_le,
   ``UMDChallenge.umdConst_Lp_eq,
   ``UMDChallenge.umdConst_hilbert,
   ``UMDChallenge.deterministic_transform_le,
   ``UMDChallenge.isComplexUMDBound_iff_deterministic,
   ``UMDChallenge.complexDyadicUMDConst_eq_complexUMDConst,
   ``UMDChallenge.umdConst_le_complexUMDConst_le,
   ``ZigZagChallenge.umd_iff_signZigZag,
   ``ZigZagChallenge.isLeast_signZigZag,
   ``ZigZagChallenge.umd_iff_zigZag,
   ``ZigZagChallenge.isLeast_zigZag,
   ``ZigZagChallenge.complexUMD_iff_signZigZag,
   ``ZigZagChallenge.isLeast_complexSignZigZag,
   ``ZigZagChallenge.complexUMD_iff_zigZag,
   ``ZigZagChallenge.isLeast_complexZigZag]

/-- Whether `m` is a module of the library or a Solution of `palomar/`. -/
meta def isLibraryModule (m : Name) : Bool :=
  [`BanachProbability, `Burkholder, `Decoupling, `KahaneKhintchine, `NoncommutativeKhintchine,
    `SchattenClasses, `TypeTwo, `UMD, `ZigZag].any (·.isPrefixOf m)

/-- The constants declared in the library and in the Solutions. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut s : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.push c
  return s

elab "#audit" : command => do
  let env ← getEnv
  let mut rows : Array String := #[]
  for n in solutionResults do
    let axs ← liftCoreM <| collectAxioms n
    rows := rows.push s!"{n}: {axs.toList}"
  logInfo ("\n".intercalate rows.toList)
  let library := libraryConstants env
  let mut bad : Array Name := #[]
  let mut sorries : Array Name := #[]
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    let other := axs.filter (!standardAxioms.contains ·)
    if other.isEmpty then continue
    if other.all (· == ``sorryAx) then
      unless c.isInternal do sorries := sorries.push c
    else
      bad := bad.push c
  let sorted := sorries.qsort (·.toString < ·.toString)
  logInfo (s!"Checked {library.size} declarations of the library and the Solutions.\n" ++
    s!"{sorted.size} public declarations depend on `sorryAx`:\n" ++
    "\n".intercalate (sorted.toList.map toString))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"
  if !allowSorry && !sorries.isEmpty then
    throwError m!"declarations depend on `sorryAx`: {sorted}"

end Audit

#audit
