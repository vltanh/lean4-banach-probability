module

public import BanachProbability.Noncommutative.ComplexSchattenUMD

/-!
# The UMD inequality for matrix-valued martingales

The UMD inequality of the Schatten classes, for matrix-valued martingales with the Schatten norms
(`IsMatrixUMDBound`, in `BanachProbability.Defs`) instead of martingales with values in the normed
space `SchattenSpace`. A matrix-valued process is a martingale with values in `SchattenSpace q n n`
if and only if each of its entries is a martingale, as the space is finite-dimensional, so the two
are the same (`isMatrixUMDBound_schattenNorm_iff`).

* `isMatrixUMDBound_schattenNorm`, `isMatrixUMDBound_complexSchattenNorm`: the bound `K q*` in
  `L^q (S_q)`, `K = 192 · 864³`, of N. Randrianantoanina, *Non-commutative martingale transforms*,
  J. Funct. Anal. 194 (2002), Corollary 4.5, for real and for complex matrices;
* `isMatrixUMDBound_two`: the bound `C (q* − 1)` in `L² (S_q)` (Remark 4.6 (1) there).

The complex case is the real one for the realifications `[[Re A, −Im A], [Im A, Re A]]`, whose
entries are real martingales, as `‖A‖_{S_q} = 2^{−1/q} ‖realify A‖_{S_q}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BanachProbability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix-valued process whose entries are martingales is a martingale with values in the
Schatten space. -/
theorem martingale_ofMatrix {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {q : ℝ≥0∞} [Fact (1 ≤ q)] {Y : ℕ → Ω → Matrix n n ℝ}
    (hY : ∀ i j, Martingale (fun k ω => Y k ω i j) ℱ μ) :
    Martingale (fun k ω => (SchattenSpace.ofMatrix (Y k ω) : SchattenSpace q n n)) ℱ μ := by
  have e : (fun k ω => (SchattenSpace.ofMatrix (Y k ω) : SchattenSpace q n n)) = fun k ω =>
      ∑ i, ∑ j, ContinuousLinearMap.toSpanSingleton ℝ
        (SchattenSpace.ofMatrix (Matrix.single i j 1) : SchattenSpace q n n) (Y k ω i j) := by
    funext k ω
    conv_lhs => rw [Matrix.matrix_eq_sum_single (Y k ω)]
    simp only [map_sum, ContinuousLinearMap.toSpanSingleton_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact martingale_finsetSum _ fun i _ => martingale_finsetSum _ fun j _ =>
    martingale_map_continuousLinearMap (hY i j) _

/-- The UMD inequality for matrix-valued martingales with the Schatten norm is the one of the
Schatten space. -/
theorem isMatrixUMDBound_schattenNorm_iff {q : ℝ≥0∞} [Fact (1 ≤ q)] {p : ℝ} {β : ℝ≥0∞} :
    IsMatrixUMDBound (schattenNorm q : Matrix n n ℝ → ℝ) p β ↔
      IsUMDBound (SchattenSpace q n n) p β := by
  constructor
  · intro h Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm N
    refine h Ω mΩ μ ℱ (fun k ω => (SchattenSpace.ofMatrix (q := q)).symm (Y k ω)) σ
      (fun i j => ?_) (fun ω => by rw [hY0, map_zero]) hσ hσm N
    exact martingale_map_continuousLinearMap hY (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℝ i j).comp (SchattenSpace.ofMatrix (q := q)).symm.toLinearMap))
  · intro h Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm N
    exact h Ω mΩ μ ℱ (fun k ω => SchattenSpace.ofMatrix (Y k ω)) σ (martingale_ofMatrix hY)
      (fun ω => by rw [hY0, map_zero]) hσ hσm N

/-- The UMD inequality for the realifications is one for complex matrices. -/
theorem IsMatrixUMDBound.complexSchattenNorm {q : ℝ≥0∞} (hq : q ≠ 0) {p : ℝ} {β : ℝ≥0∞}
    (h : IsMatrixUMDBound (schattenNorm q : Matrix (n ⊕ n) (n ⊕ n) ℝ → ℝ) p β) :
    IsMatrixUMDBound (complexSchattenNorm q : Matrix n n ℂ → ℝ) p β := by
  intro Ω mΩ μ _ ℱ Y σ hY hY0 hσ hσm N
  -- the entries of `realify Y` are real martingales
  have hre := fun i j => martingale_map_continuousLinearMap (hY i j) Complex.reCLM
  have him := fun i j => martingale_map_continuousLinearMap (hY i j) Complex.imCLM
  have hZ : ∀ i j, Martingale (fun k ω => realify (Y k ω) i j) ℱ μ := by
    rintro (i | i) (j | j)
    · exact hre i j
    · exact (him i j).neg
    · exact him i j
    · exact hre i j
  have key := h Ω mΩ μ ℱ (fun k ω => realify (Y k ω)) σ hZ
    (fun ω => by rw [hY0]; ext (i | i) (j | j) <;> simp [realify]) hσ hσm N
  -- `realify` is linear
  have hT : ∀ ω, ∑ k ∈ Finset.range N, σ (k + 1) ω • (realify (Y (k + 1) ω) - realify (Y k ω)) =
      realify (∑ k ∈ Finset.range N, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)) := fun ω => by
    let L : Matrix n n ℂ →+ Matrix (n ⊕ n) (n ⊕ n) ℝ := AddMonoidHom.mk' realify realify_add
    change _ = L _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = realify (σ (k + 1) ω • _)
    rw [realify_smul]
    exact congrArg _ (map_sub L _ _).symm
  simp only [hT] at key
  -- the factor `2^{−1/q}`
  have hc : ∀ f : Ω → Matrix n n ℂ, eLpNorm (fun ω => BanachProbability.complexSchattenNorm q (f ω))
      (ENNReal.ofReal p) μ = ‖(2 : ℝ) ^ (-(1 / q.toReal))‖ₑ *
        eLpNorm (fun ω => schattenNorm q (realify (f ω))) (ENNReal.ofReal p) μ := fun f => by
    simp only [complexSchattenNorm_eq_realify hq]
    exact eLpNorm_const_smul ((2 : ℝ) ^ (-(1 / q.toReal))) _ _ _
  rw [hc, hc, mul_left_comm]
  gcongr

/-- **Schatten classes are UMD**, real matrices (Randrianantoanina 2002, Theorem 4.3 and Corollary
4.5): the bound `K q*` in `L^q (S_q)`, `K = 192 · 864³`, uniformly in the size. -/
theorem isMatrixUMDBound_schattenNorm {q : ℝ} (hq : 1 < q) (n : Type) [Fintype n]
    [DecidableEq n] : IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) q
      (ENNReal.ofReal (192 * 864 ^ 3 * pStar q)) := by
  have hq0 : 0 ≤ q := by linarith
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 hq.le⟩
  have h := isUMDBound_schattenSpace (ENNReal.ofReal q) (ENNReal.one_lt_ofReal.2 hq)
    ENNReal.ofReal_ne_top n
  rw [ENNReal.toReal_ofReal hq0] at h
  exact isMatrixUMDBound_schattenNorm_iff.2 h

/-- **Schatten classes are UMD**, complex matrices: the bound `K q*` in `L^q (S_q)`,
`K = 192 · 864³`, uniformly in the size. -/
theorem isMatrixUMDBound_complexSchattenNorm {q : ℝ} (hq : 1 < q) (n : Type) [Fintype n]
    [DecidableEq n] : IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) q
      (ENNReal.ofReal (192 * 864 ^ 3 * pStar q)) :=
  (isMatrixUMDBound_schattenNorm hq (n ⊕ n)).complexSchattenNorm
    (ENNReal.ofReal_pos.2 (by linarith)).ne'

/-- **The UMD inequality of the Schatten classes in `L²`** (Randrianantoanina 2002, Remark 4.6 (1)),
real and complex matrices: there is an absolute `C` such that `C (q* − 1)` is a constant in
`L² (S_q)` for every `1 < q < ∞` and every size. -/
theorem isMatrixUMDBound_two : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℝ, 1 < q → ∀ (n : Type) [Fintype n] [DecidableEq n],
      IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) 2
          (ENNReal.ofReal (C * (pStar q - 1))) ∧
        IsMatrixUMDBound (complexSchattenNorm (ENNReal.ofReal q) : Matrix n n ℂ → ℝ) 2
          (ENNReal.ofReal (C * (pStar q - 1))) := by
  obtain ⟨C, hC, h⟩ := umdConst_two_schattenSpace_le
  have key : ∀ q : ℝ, 1 < q → ∀ (n : Type) [Fintype n] [DecidableEq n],
      IsMatrixUMDBound (schattenNorm (ENNReal.ofReal q) : Matrix n n ℝ → ℝ) 2
        (ENNReal.ofReal (C * (pStar q - 1))) := fun q hq n _ _ => by
    have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 hq.le⟩
    have h1 := h (ENNReal.ofReal q) (ENNReal.one_lt_ofReal.2 hq) ENNReal.ofReal_ne_top n
    rw [ENNReal.toReal_ofReal (by linarith)] at h1
    exact isMatrixUMDBound_schattenNorm_iff.2 ((isUMDBound_umdConst one_lt_two).mono h1)
  exact ⟨C, hC, fun q hq n _ _ => ⟨key q hq n, (key q hq (n ⊕ n)).complexSchattenNorm
    (ENNReal.ofReal_pos.2 (by linarith)).ne'⟩⟩

end BanachProbability
