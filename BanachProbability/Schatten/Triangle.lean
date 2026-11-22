module

public import BanachProbability.Schatten.Dilation
public import BanachProbability.Schatten.Trace

/-!
# The triangle inequality for Schatten norms

For `q ∈ [1, ∞]`, `‖A + B‖_{S_q} ≤ ‖A‖_{S_q} + ‖B‖_{S_q}` (`schattenNorm_add_le`). The usual
reference, R. Bhatia, *Matrix Analysis* (1997), Chapter IV, was not accessible. The proof follows
J.-C. Bourin and T. Zhang, *Matrix triangle inequalities: past, present, and future*,
arXiv:2610.30538 (2026), Proposition 3.13, by the third proof of their Remark 3.14: the second
part of the proof of Proposition 3.13, rerun on the Hermitian dilations `A₀ = [[0, A], [Aᵀ, 0]]`,
`B₀ = [[0, B], [Bᵀ, 0]]` with the convex function `t ↦ |t|^p`, `p = q < ∞`.

* **von Neumann's convexity inequality**, the source's (1.1) (`trace_cfc_smul_add_smul_le`). The
  source states it at the midpoint, for `g` convex on an interval containing the spectra, quotes it
  without proof, and uses it in the proof of Proposition 3.13 for a convex combination:
  `Tr g (t X + (1 − t) Y) ≤ t Tr g (X) + (1 − t) Tr g (Y)`, `t ∈ [0, 1]`. That form is proved here
  for `g` convex on all of `ℝ` (enough for `|·|^p`), by the standard argument of Peierls: in an
  orthonormal eigenbasis `(w_k)` of `Z = t X + (1 − t) Y`,
  `λ_k (Z) = ⟨w_k, Z w_k⟩ = t ⟨w_k, X w_k⟩ + (1 − t) ⟨w_k, Y w_k⟩`
  (`eigenvalues_eq_sum_eigenvectorBasis_mul`), so the convexity of `g` gives
  `Tr g (Z) ≤ t Σ_k g (⟨w_k, X w_k⟩) + (1 − t) Σ_k g (⟨w_k, Y w_k⟩)`; and
  `Σ_k g (⟨w_k, X w_k⟩) ≤ Tr g (X)` (Peierls's inequality, `sum_apply_diag_le_sum_eigenvalues`):
  `⟨w_k, X w_k⟩ = Σ_j ⟨u_j, w_k⟩² λ_j (X)` (`sum_eigenvectorBasis_mul_cfc_mul`), whose weights sum
  to `1` over `j` and over `k` (`sum_overlap_left`, `sum_overlap_right`), and Jensen's inequality.
  This Jensen step is written out, for `g = |·|^p`, in the proof of Theorem 7.1 of S. Fehr's
  lecture notes *Quantum Information Theory* (2021), Chapter 7; the usual reference for Peierls's
  inequality, E. Carlen's notes *Trace inequalities and quantum entropy* (2010), was not
  accessible.
* **The normalized case** (`schattenNorm_smul_add_smul_le_one`): if `‖A‖_{S_p} = ‖B‖_{S_p} = 1`
  and `t ∈ [0, 1]`, then `‖t A + (1 − t) B‖_{S_p} ≤ 1`, as
  `2 ‖t A + (1 − t) B‖_{S_p}^p = Tr |t A₀ + (1 − t) B₀|^p ≤ t Tr |A₀|^p + (1 − t) Tr |B₀|^p = 2`.
  The source's "arguing as in" leaves implicit the three facts used here: the dilation `D` is linear
  (`dilationLinearMap`), `‖D (C)‖_{S_p}^p = 2 ‖C‖_{S_p}^p` (`schattenNorm_dilation_rpow`), and
  `‖X‖_{S_p}^p = Tr |X|^p` for a symmetric `X` (`schattenNorm_rpow_of_isHermitian`,
  `trace_cfc_eq_sum`). The normalized matrices are `A` and `B`, so that `Tr |A₀|^p = 2`.
* **The general case** (`schattenNorm_add_le`, `q < ∞`): for `A, B ≠ 0`, the normalized case for
  `A / ‖A‖_{S_p}`, `B / ‖B‖_{S_p}` and `t = ‖A‖_{S_p} / (‖A‖_{S_p} + ‖B‖_{S_p})`. The source leaves
  out `A = 0` or `B = 0`: if `‖A‖_{S_p} = 0`, then `A = 0` (`schattenNorm_eq_zero_iff`) and the
  inequality is an equality, and likewise for `B`.
* **`q = ∞`**, which the source calls well known and does not prove (`schattenNorm_top_add_le`):
  `s_1 (A + B) ≤ s_1 (A) + s_1 (B)`, the first of Weyl's inequalities for singular values
  (`countAbove_add_add_le`, by a Courant–Fischer dimension count) with `s = ‖A‖_{S_∞}` and
  `t = ‖B‖_{S_∞}`. No singular value of `A` exceeds `s` and none of `B` exceeds `t`, so the
  dimension count is vacuous and what remains is `‖(A + B) v‖ ≤ ‖A v‖ + ‖B v‖ ≤ (s + t) ‖v‖`, the
  triangle inequality of the spectral norm as an operator norm.

**Departure from the source.** Proposition 3.13 and (1.1) are about complex square matrices and
complex Hermitian matrices; the statements here are about real `m × n` matrices and real
symmetric ones. The argument is the same over `ℝ`: the eigenbases are real orthonormal bases, and
the dilation of an `m × n` matrix is a symmetric matrix on `m ⊕ n` with
`‖D (C)‖_{S_p}^p = 2 ‖C‖_{S_p}^p`. The complex statements are not formalized.
-/

@[expose] public section

open scoped ENNReal Matrix

namespace BanachProbability

/-! ### von Neumann's convexity inequality -/

section Convexity

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The eigenvalues as diagonal entries: `λ_i (Q) = ⟨w_i, Q w_i⟩` for the orthonormal eigenbasis
`(w_i)` of a symmetric `Q`. -/
theorem eigenvalues_eq_sum_eigenvectorBasis_mul {Q : Matrix k k ℝ} (hQ : Q.IsHermitian) (i : k) :
    hQ.eigenvalues i = ∑ a, ∑ b, hQ.eigenvectorBasis i a * Q a b * hQ.eigenvectorBasis i b := by
  have h := sum_eigenvectorBasis_mul_cfc_mul hQ hQ id i
  rw [cfc_id ℝ Q hQ.isSelfAdjoint] at h
  rw [h]
  have ho : ∀ j, overlap hQ hQ j i = if j = i then 1 else 0 := fun j => by
    rw [overlap, orthonormal_iff_ite.mp hQ.eigenvectorBasis.orthonormal j i]
    split_ifs <;> norm_num
  simp [ho]

/-- **Peierls's inequality** in the eigenbasis `(w_i)` of a symmetric `Q`: for a symmetric `P` and
a convex `g`, `Σ_i g (⟨w_i, P w_i⟩) ≤ Σ_j g (λ_j (P)) = Tr g (P)`. With the eigenbasis `(u_j)` of
`P`, `⟨w_i, P w_i⟩ = Σ_j ⟨u_j, w_i⟩² λ_j (P)`; Jensen's inequality for the weights `⟨u_j, w_i⟩²`,
which sum to `1` over `j`, and the sum over `i`, where they sum to `1` again. -/
theorem sum_apply_diag_le_sum_eigenvalues {P Q : Matrix k k ℝ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) :
    ∑ i, g (∑ a, ∑ b, hQ.eigenvectorBasis i a * P a b * hQ.eigenvectorBasis i b) ≤
      ∑ j, g (hP.eigenvalues j) := by
  have hdiag : ∀ i, ∑ a, ∑ b, hQ.eigenvectorBasis i a * P a b * hQ.eigenvectorBasis i b =
      ∑ j, overlap hP hQ j i * hP.eigenvalues j := fun i => by
    have h := sum_eigenvectorBasis_mul_cfc_mul hP hQ id i
    rw [cfc_id ℝ P hP.isSelfAdjoint] at h
    simpa only [id] using h
  calc ∑ i, g (∑ a, ∑ b, hQ.eigenvectorBasis i a * P a b * hQ.eigenvectorBasis i b)
      ≤ ∑ i, ∑ j, overlap hP hQ j i * g (hP.eigenvalues j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hdiag i]
        simpa only [smul_eq_mul] using hg.map_sum_le (fun j _ => overlap_nonneg hP hQ j i)
          (sum_overlap_left hP hQ i) (fun j _ => Set.mem_univ (hP.eigenvalues j))
    _ = ∑ j, g (hP.eigenvalues j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, sum_overlap_right, one_mul]

/-- **von Neumann's convexity inequality** (Bourin–Zhang, (1.1), for a convex combination, real
symmetric matrices and `g` convex on `ℝ`): for symmetric `X`, `Y`, `t ∈ [0, 1]` and a convex `g`,
`Tr g (t X + (1 − t) Y) ≤ t Tr g (X) + (1 − t) Tr g (Y)`. Peierls's argument: in the eigenbasis
`(w_i)` of `Z = t X + (1 − t) Y`, `λ_i (Z) = t ⟨w_i, X w_i⟩ + (1 − t) ⟨w_i, Y w_i⟩`; the convexity
of `g`, then Peierls's inequality for `X` and for `Y`. -/
theorem trace_cfc_smul_add_smul_le {X Y : Matrix k k ℝ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) :
    (cfc g (t • X + (1 - t) • Y)).trace ≤ t * (cfc g X).trace + (1 - t) * (cfc g Y).trace := by
  have hZ : (t • X + (1 - t) • Y).IsHermitian :=
    (hX.smul (IsSelfAdjoint.all t)).add (hY.smul (IsSelfAdjoint.all (1 - t)))
  have ht1' : 0 ≤ 1 - t := by linarith
  rw [trace_cfc_eq_sum hZ, trace_cfc_eq_sum hX, trace_cfc_eq_sum hY]
  set w := hZ.eigenvectorBasis
  have hlin : ∀ i, hZ.eigenvalues i = t * ∑ a, ∑ b, w i a * X a b * w i b +
      (1 - t) * ∑ a, ∑ b, w i a * Y a b * w i b := fun i => by
    rw [eigenvalues_eq_sum_eigenvectorBasis_mul hZ i]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  calc ∑ i, g (hZ.eigenvalues i)
      ≤ ∑ i, (t * g (∑ a, ∑ b, w i a * X a b * w i b) +
          (1 - t) * g (∑ a, ∑ b, w i a * Y a b * w i b)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hlin i]
        simpa only [smul_eq_mul] using
          hg.2 (Set.mem_univ _) (Set.mem_univ _) ht0 ht1' (by ring)
    _ = t * ∑ i, g (∑ a, ∑ b, w i a * X a b * w i b) +
          (1 - t) * ∑ i, g (∑ a, ∑ b, w i a * Y a b * w i b) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ t * ∑ j, g (hX.eigenvalues j) + (1 - t) * ∑ j, g (hY.eigenvalues j) :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_apply_diag_le_sum_eigenvalues hX hZ hg) ht0)
          (mul_le_mul_of_nonneg_left (sum_apply_diag_le_sum_eigenvalues hY hZ hg) ht1')

end Convexity

/-! ### The triangle inequality -/

section Triangle

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The normalized case** (Bourin–Zhang, Remark 3.14, with the second part of the proof of
Proposition 3.13): if `‖A‖_{S_p} = ‖B‖_{S_p} = 1`, `p ≥ 1` and `t ∈ [0, 1]`, then
`‖t A + (1 − t) B‖_{S_p} ≤ 1`. With the dilations `A₀ = D (A)`, `B₀ = D (B)`,
`2 ‖t A + (1 − t) B‖_{S_p}^p = ‖t A₀ + (1 − t) B₀‖_{S_p}^p = Tr |t A₀ + (1 − t) B₀|^p
≤ t Tr |A₀|^p + (1 − t) Tr |B₀|^p = 2`, by von Neumann's convexity inequality for `|·|^p`. -/
theorem schattenNorm_smul_add_smul_le_one {p : ℝ} (hp : 1 ≤ p)
    {A B : Matrix m n ℝ} (hA : schattenNorm (ENNReal.ofReal p) A = 1)
    (hB : schattenNorm (ENNReal.ofReal p) B = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    schattenNorm (ENNReal.ofReal p) (t • A + (1 - t) • B) ≤ 1 := by
  classical
  have hp0 : 0 < p := by linarith
  have hD : dilation (t • A + (1 - t) • B) = t • dilation A + (1 - t) • dilation B := by
    change dilationLinearMap (t • A + (1 - t) • B) = _
    rw [map_add, map_smul, map_smul]
    rfl
  -- `‖X‖_{S_p}^p = Tr |X|^p` for a symmetric `X`
  have htr : ∀ {X : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hX : X.IsHermitian),
      schattenNorm (ENNReal.ofReal p) X ^ p = (cfc (fun x : ℝ => |x| ^ p) X).trace :=
    fun hX => by rw [schattenNorm_rpow_of_isHermitian hX hp0, trace_cfc_eq_sum hX]
  have hZ : (t • dilation A + (1 - t) • dilation B).IsHermitian :=
    hD ▸ dilation_isHermitian (t • A + (1 - t) • B)
  have key : 2 * schattenNorm (ENNReal.ofReal p) (t • A + (1 - t) • B) ^ p ≤ 2 := by
    rw [← schattenNorm_dilation_rpow hp0, hD, htr hZ]
    calc (cfc (fun x : ℝ => |x| ^ p) (t • dilation A + (1 - t) • dilation B)).trace
        ≤ t * (cfc (fun x : ℝ => |x| ^ p) (dilation A)).trace +
            (1 - t) * (cfc (fun x : ℝ => |x| ^ p) (dilation B)).trace :=
          trace_cfc_smul_add_smul_le (dilation_isHermitian A) (dilation_isHermitian B) ht0 ht1
            (convexOn_abs_rpow hp)
      _ = 2 := by
          rw [← htr (dilation_isHermitian A), ← htr (dilation_isHermitian B),
            schattenNorm_dilation_rpow hp0, schattenNorm_dilation_rpow hp0, hA, hB,
            Real.one_rpow]
          ring
  have h1 : schattenNorm (ENNReal.ofReal p) (t • A + (1 - t) • B) ^ p ≤ 1 := by linarith
  by_contra hlt
  linarith [Real.one_lt_rpow (not_le.mp hlt) hp0]

/-- `q = ∞`, which the source calls well known: `s_1 (A + B) ≤ s_1 (A) + s_1 (B)`, the first of
Weyl's inequalities for singular values (`countAbove_add_add_le`): no singular value of `A` exceeds
`‖A‖_{S_∞}` and none of `B` exceeds `‖B‖_{S_∞}`, hence none of `A + B` exceeds their sum. -/
theorem schattenNorm_top_add_le (A B : Matrix m n ℝ) :
    schattenNorm ⊤ (A + B) ≤ schattenNorm ⊤ A + schattenNorm ⊤ B := by
  simp only [schattenNorm, ite_true]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Real.iSup_of_isEmpty, add_zero, le_refl]
  set s := ⨆ i, singularValue A i
  set t := ⨆ i, singularValue B i
  have hA : countAbove s A = 0 := by
    rw [countAbove, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => not_lt.2 (le_ciSup (Set.finite_range _).bddAbove i)
  have hB : countAbove t B = 0 := by
    rw [countAbove, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => not_lt.2 (le_ciSup (Set.finite_range _).bddAbove i)
  have h := countAbove_add_add_le s t A B
  rw [hA, hB] at h
  have h0 : countAbove (s + t) (A + B) = 0 := by omega
  rw [countAbove, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact ciSup_le fun i => not_lt.1 (h0 (Finset.mem_univ i))

/-- **The triangle inequality for Schatten norms**, `q ∈ [1, ∞]` (Bourin–Zhang, Proposition 3.13,
by Remark 3.14). For `q < ∞` and `A, B ≠ 0`, the normalized case for `A / ‖A‖_{S_q}`,
`B / ‖B‖_{S_q}` and `t = ‖A‖_{S_q} / (‖A‖_{S_q} + ‖B‖_{S_q})`, for which
`t A / ‖A‖_{S_q} + (1 − t) B / ‖B‖_{S_q} = (A + B) / (‖A‖_{S_q} + ‖B‖_{S_q})`; if `A = 0` or
`B = 0` the inequality is an equality; `q = ∞` by Weyl's inequality. -/
theorem schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  classical
  rcases eq_or_ne q ⊤ with rfl | hqt
  · exact schattenNorm_top_add_le A B
  obtain ⟨p, rfl⟩ : ∃ p : ℝ, q = ENNReal.ofReal p := ⟨q.toReal, (ENNReal.ofReal_toReal hqt).symm⟩
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.mp hq
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  rcases (schattenNorm_nonneg (ENNReal.ofReal p) A).eq_or_lt with ha | ha
  · rw [(schattenNorm_eq_zero_iff hq0).1 ha.symm, zero_add, schattenNorm_zero hq0, zero_add]
  rcases (schattenNorm_nonneg (ENNReal.ofReal p) B).eq_or_lt with hb | hb
  · rw [(schattenNorm_eq_zero_iff hq0).1 hb.symm, add_zero, schattenNorm_zero hq0, add_zero]
  set a := schattenNorm (ENNReal.ofReal p) A
  set b := schattenNorm (ENNReal.ofReal p) B
  have hab : 0 < a + b := add_pos ha hb
  have hA1 : schattenNorm (ENNReal.ofReal p) (a⁻¹ • A) = 1 := by
    rw [schattenNorm_smul hq0, abs_of_pos (inv_pos.2 ha), inv_mul_cancel₀ ha.ne']
  have hB1 : schattenNorm (ENNReal.ofReal p) (b⁻¹ • B) = 1 := by
    rw [schattenNorm_smul hq0, abs_of_pos (inv_pos.2 hb), inv_mul_cancel₀ hb.ne']
  have ht0 : 0 ≤ a / (a + b) := div_nonneg ha.le hab.le
  have ht1 : a / (a + b) ≤ 1 := (div_le_one hab).2 (by linarith)
  have h := schattenNorm_smul_add_smul_le_one hp hA1 hB1 ht0 ht1
  have e : (a / (a + b)) • (a⁻¹ • A) + (1 - a / (a + b)) • (b⁻¹ • B) =
      (a + b)⁻¹ • (A + B) := by
    have h1 : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
    rw [h1, smul_smul, smul_smul, smul_add]
    congr 2 <;> field_simp
  rw [e, schattenNorm_smul hq0, abs_of_pos (inv_pos.2 hab)] at h
  rwa [inv_mul_le_iff₀ hab, mul_one] at h

end Triangle

end BanachProbability
