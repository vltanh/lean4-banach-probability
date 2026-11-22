module

public import BanachProbability.Noncommutative.SchattenUMD
public import BanachProbability.Schatten.Complex

/-!
# UMD constants of the complex Schatten classes

The space `ComplexSchattenSpace q n n` of complex `n × n` matrices with the Schatten `q`-norm is, as
a real space, isometric to a subspace of the real space `SchattenSpace q (n ⊕ n) (n ⊕ n)`, so its
UMD constants are at most those of the real space (`umdConst_complexSchattenSpace_le`), and
`UMD₂ (S_q) ≤ C (q* − 1)` uniformly in the size (`umdConst_two_complexSchattenSpace_le`, from
`umdConst_two_schattenSpace_le`). These are the UMD constants for real signs `±1` (`umdConst`, of
the underlying real Banach space); those for unimodular complex multipliers (`complexUMDConst`) are
at most `π/2` times larger (`umdConst_le_complexUMDConst_le`).
-/

@[expose] public section

open scoped ENNReal

namespace BanachProbability

/-- The complex Schatten space embeds isometrically, over `ℝ`, in the real Schatten space of twice
the size (`A ↦ 2^{−1/q} realify A`), so its UMD constants, for real signs, are at most those of the
real space. -/
theorem umdConst_complexSchattenSpace_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : Type*) [Fintype n]
    [DecidableEq n] (p : ℝ) :
    umdConst (ComplexSchattenSpace q n n) p ≤ umdConst (SchattenSpace q (n ⊕ n) (n ⊕ n)) p := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  refine umdConst_le_of_linearIsometry
    { toFun := fun A => SchattenSpace.ofMatrix
        ((2 : ℝ) ^ (-(1 / q.toReal)) • realify (ComplexSchattenSpace.ofMatrix.symm A))
      map_add' := fun A B => ?_
      map_smul' := fun c A => ?_
      norm_map' := fun A => ?_ } p
  · rw [map_add, realify_add, smul_add, map_add]
  · have h : ComplexSchattenSpace.ofMatrix.symm (c • A) =
        c • ComplexSchattenSpace.ofMatrix.symm A := rfl
    rw [h, realify_smul, smul_comm, map_smul, RingHom.id_apply]
  · rw [ComplexSchattenSpace.norm_def, complexSchattenNorm_eq_realify hq,
      ← abs_of_nonneg (Real.rpow_nonneg zero_le_two (-(1 / q.toReal))), ← schattenNorm_smul hq,
      abs_of_nonneg (Real.rpow_nonneg zero_le_two _)]
    exact SchattenSpace.norm_ofMatrix _

/-- **`UMD₂` of the complex Schatten classes**, for real signs: there is an absolute `C` such that
`UMD₂ (S_q) ≤ C (q* − 1)` for all `1 < q < ∞` and all sizes. -/
theorem umdConst_two_complexSchattenSpace_le : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (ComplexSchattenSpace q n n) 2 ≤ ENNReal.ofReal (C * (pStar q.toReal - 1)) := by
  obtain ⟨C, hC, h⟩ := umdConst_two_schattenSpace_le
  exact ⟨C, hC, fun q _ hq1 hqt n _ _ =>
    (umdConst_complexSchattenSpace_le q n 2).trans (h q hq1 hqt (n ⊕ n))⟩

end BanachProbability
