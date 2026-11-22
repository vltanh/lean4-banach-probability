module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that the proofs are visible (the module
-- system hides them from a plain `import`). Generate the lines with
--   find BanachProbability -name '*.lean' | sed 's/\.lean$//; s#/#.#g; s/^/import all /' | sort
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

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Checks every declaration of the library: the run fails if one depends on an axiom other than
Lean's standard `propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom
`sorryAx`, and fails the run too (`allowSorry := false`); with `allowSorry := true`, for work in
progress, the declarations that depend on `sorryAx` are listed instead.
-/

open Lean Elab Command

namespace Audit

/-- Whether declarations may still depend on `sorryAx`. -/
meta def allowSorry : Bool := false

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`BanachProbability).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut s : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.push c
  return s

elab "#audit" : command => do
  let env ← getEnv
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
  logInfo (s!"Checked {library.size} declarations of the library.\n" ++
    s!"{sorted.size} public declarations depend on `sorryAx`:\n" ++
    "\n".intercalate (sorted.toList.map toString))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"
  if !allowSorry && !sorries.isEmpty then
    throwError m!"declarations depend on `sorryAx`: {sorted}"

end Audit

#audit
