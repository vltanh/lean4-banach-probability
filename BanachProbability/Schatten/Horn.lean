module

public import BanachProbability.Schatten.Dilation
public import BanachProbability.Schatten.Holder

/-!
# Horn's inequality and Hölder's inequality for Schatten norms

For real matrices `A`, `B` with singular values in decreasing order,
`Π_{k < N} s_k (A B) ≤ Π_{k < N} s_k (A) s_k (B)` for every `N` (`prod_sortedSingularValue_mul_le`,
Horn's inequality), and hence **Hölder's inequality**
`‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r` (`schattenNorm_mul_le`), for all
`0 < q, r < ∞`; also `|tr A| ≤ ‖A‖_{S_1}` and `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`.

The proofs are those of Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I*
(2016), Appendix D: Lemma D.1.4 (p. 568), Lemmas D.2.1–D.2.2 (p. 570), Proposition D.2.3 (p. 571),
Corollary D.2.4 and Proposition D.2.5 (p. 572).
-/

@[expose] public section

open scoped Matrix

namespace BanachProbability

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The singular values of `A` in decreasing order, `s_0 ≥ s_1 ≥ …`, extended by `0`. -/
noncomputable def sortedSingularValue (A : Matrix m n ℝ) (k : ℕ) : ℝ :=
  if h : k < Fintype.card n then
    √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ ⟨k, h⟩) else 0

theorem sortedSingularValue_nonneg (A : Matrix m n ℝ) (k : ℕ) : 0 ≤ sortedSingularValue A k := by
  sorry

theorem antitone_sortedSingularValue (A : Matrix m n ℝ) : Antitone (sortedSingularValue A) := by
  sorry

/-- The Schatten norm in terms of the sorted singular values. -/
theorem schattenNorm_eq_sum_sortedSingularValue {q : ℝ} (hq : 0 < q) (A : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal q) A =
      (∑ k ∈ Finset.range (Fintype.card n), sortedSingularValue A k ^ q) ^ (1 / q) := by
  sorry

/-- (HNVW I, Lemma D.2.2) `det (Φᵀ Aᵀ A Φ) ≤ Π_{k < N} s_k (A)² · det (Φᵀ Φ)` for every `Φ` with `N`
columns. -/
theorem det_conj_transpose_mul_self_le (A : Matrix m n ℝ) {N : ℕ} (Φ : Matrix n (Fin N) ℝ) :
    ((A * Φ)ᵀ * (A * Φ)).det ≤
      (∏ k ∈ Finset.range N, sortedSingularValue A k ^ 2) * (Φᵀ * Φ).det := by
  sorry

/-- **Horn's inequality** (HNVW I, Proposition D.2.3):
`Π_{k<N} s_k (A B) ≤ Π_{k<N} s_k (A) s_k (B)`. -/
theorem prod_sortedSingularValue_mul_le (A : Matrix l m ℝ) (B : Matrix m n ℝ) (N : ℕ) :
    ∏ k ∈ Finset.range N, sortedSingularValue (A * B) k ≤
      ∏ k ∈ Finset.range N, sortedSingularValue A k * sortedSingularValue B k := by
  sorry

/-- (HNVW I, Lemma D.1.4) If `a`, `b` are nonincreasing with `Σ_{j<k} a_j ≤ Σ_{j<k} b_j` for all
`k ≤ N`, then `Σ_{j<N} f (a_j) ≤ Σ_{j<N} f (b_j)` for every convex nondecreasing `f`. -/
theorem sum_le_sum_of_weak_majorization {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hfm : Monotone f)
    {a b : ℕ → ℝ} (N : ℕ) (ha : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hb : ∀ i j, i ≤ j → j < N → b j ≤ b i)
    (hab : ∀ k ≤ N, ∑ j ∈ Finset.range k, a j ≤ ∑ j ∈ Finset.range k, b j) :
    ∑ j ∈ Finset.range N, f (a j) ≤ ∑ j ∈ Finset.range N, f (b j) := by
  sorry

/-- **Hölder's inequality** for Schatten norms (HNVW I, Corollary D.2.4):
`‖A B‖_{S_p} ≤ ‖A‖_{S_q} ‖B‖_{S_r}`, `1/p = 1/q + 1/r`. -/
theorem schattenNorm_mul_le {p q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / p = 1 / q + 1 / r)
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    schattenNorm (ENNReal.ofReal p) (A * B) ≤
      schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal r) B := by
  sorry

/-- (HNVW I, Proposition D.2.5) The trace is contractive on `S_1`. -/
theorem abs_trace_le_schattenNorm_one (A : Matrix n n ℝ) : |A.trace| ≤ schattenNorm 1 A := by
  sorry

/-- `|tr (A B)| ≤ ‖A‖_{S_q} ‖B‖_{S_{q'}}`, `1/q + 1/q' = 1`, for rectangular matrices. -/
theorem abs_trace_mul_le {q q' : ℝ} (hq : q.HolderConjugate q') (A : Matrix n m ℝ)
    (B : Matrix m n ℝ) :
    |(A * B).trace| ≤ schattenNorm (ENNReal.ofReal q) A * schattenNorm (ENNReal.ofReal q') B := by
  sorry

end BanachProbability
