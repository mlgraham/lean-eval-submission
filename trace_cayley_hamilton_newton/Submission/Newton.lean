import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Submission.CharpolyDerivative

/-!
# Newton's identities for the characteristic polynomial (Faddeev–LeVerrier)

Write `χ_A(X) = ∑ₘ χₘ Xᵐ` (degree `N = card n`) and `cₖ := χ_{N−k}` (so `c₀ = 1`, `cₖ = 0` for
`k > N`). Let `B(X) := adjugate (X•1 − A) = ∑ⱼ Dⱼ Xʲ` with matrix coefficients `Dⱼ`. From
`(X•1 − A)·B(X) = χ_A(X)·1` we get `Dⱼ = A·Dⱼ₊₁ + χⱼ₊₁·1`, `D_{N−1} = 1`, `Dⱼ = 0` for `j ≥ N`,
and `A·D₀ + χ₀·1 = 0`. Hence the Faddeev–LeVerrier matrices `Pₖ := ∑_{i≤k} cᵢ A^{k−i}` satisfy
`Pₖ = D_{N−1−k}` for `k < N` and `Pₖ = 0` for `k ≥ N`. Taking traces and using
`χ_A' = trace B` (`derivative_charpoly`) gives `trace Pₖ = (N − k) cₖ` for every `k`, which is
Newton's identity `k cₖ + ∑_{j=1}^{k} trace(Aʲ) c_{k−j} = 0`.
-/

open Polynomial Matrix

namespace Submission

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The descending coefficients `cₖ = χ_{N−k}` (zero for `k > N`). -/
noncomputable def cdesc (A : Matrix n n R) (k : ℕ) : R :=
  if k ≤ Fintype.card n then (charpoly A).coeff (Fintype.card n - k) else 0

/-- The Faddeev–LeVerrier matrices `Pₖ = ∑_{i ≤ k} cᵢ A^{k−i}`. -/
noncomputable def faddeev (A : Matrix n n R) (k : ℕ) : Matrix n n R :=
  ∑ i ∈ Finset.range (k + 1), cdesc A i • A ^ (k - i)

lemma faddeev_zero (A : Matrix n n R) : faddeev A 0 = cdesc A 0 • 1 := by
  simp [faddeev]

lemma faddeev_succ (A : Matrix n n R) (k : ℕ) :
    faddeev A (k + 1) = A * faddeev A k + cdesc A (k + 1) • 1 := by
  simp only [faddeev, Finset.sum_range_succ _ (k + 1), Nat.sub_self, pow_zero, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Matrix.mul_smul, ← pow_succ', show k + 1 - i = k - i + 1 by omega]

lemma trace_faddeev (A : Matrix n n R) (k : ℕ) :
    trace (faddeev A k) = ∑ i ∈ Finset.range (k + 1), cdesc A i * trace (A ^ (k - i)) := by
  simp [faddeev, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

section Main

variable [Nontrivial R] (A : Matrix n n R)

local notation "N" => Fintype.card n

/-- The adjugate of the characteristic matrix as a polynomial with matrix coefficients. -/
noncomputable abbrev adjPoly : (Matrix n n R)[X] := matPolyEquiv (adjugate (charmatrix A))

lemma X_sub_C_mul_adjPoly :
    (X - C A) * adjPoly A = (charpoly A).map (algebraMap R (Matrix n n R)) := by
  rw [← matPolyEquiv_charmatrix, ← map_mul, mul_adjugate, ← matPolyEquiv_smul_one]
  rfl

/-- The coefficient recursion `Dⱼ − A·Dⱼ₊₁ = χⱼ₊₁ • 1`. -/
lemma adjPoly_coeff_succ (j : ℕ) :
    (adjPoly A).coeff j - A * (adjPoly A).coeff (j + 1) =
      (charpoly A).coeff (j + 1) • (1 : Matrix n n R) := by
  have h := congrArg (fun p => Polynomial.coeff p (j + 1)) (X_sub_C_mul_adjPoly A)
  simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_map,
    Algebra.algebraMap_eq_smul_one] at h
  exact h

/-- The constant-coefficient relation `−A·D₀ = χ₀ • 1`. -/
lemma adjPoly_coeff_zero :
    -(A * (adjPoly A).coeff 0) = (charpoly A).coeff 0 • (1 : Matrix n n R) := by
  have h := congrArg (fun p => Polynomial.coeff p 0) (X_sub_C_mul_adjPoly A)
  simp only [sub_mul, coeff_sub, coeff_C_mul, coeff_map, Algebra.algebraMap_eq_smul_one] at h
  rw [Polynomial.coeff_X_mul_zero] at h  -- `coeff (X * p) 0 = 0`
  simpa using h

/-- `trace Dⱼ = (j+1) χⱼ₊₁`, from `χ' = trace (adjugate (charmatrix A))`. -/
lemma trace_adjPoly_coeff (j : ℕ) :
    trace ((adjPoly A).coeff j) = (charpoly A).coeff (j + 1) * (j + 1) := by
  have h := congrArg (fun p => Polynomial.coeff p j) (derivative_charpoly A)
  simp only [coeff_derivative] at h
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, adjPoly, matPolyEquiv_coeff_apply,
    Polynomial.finsetSum_coeff]

/-- `Dⱼ = 0` for `j ≥ N`. -/
lemma adjPoly_coeff_eq_zero_of_le {j : ℕ} (hj : N ≤ j) : (adjPoly A).coeff j = 0 := by
  -- downward induction from a large index
  set M := max (Polynomial.natDegree (adjPoly A) + 1) N with hM
  have hbig : ∀ i, M ≤ i → (adjPoly A).coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hstep : ∀ i, N ≤ i → (adjPoly A).coeff i = A * (adjPoly A).coeff (i + 1) := by
    intro i hi
    have h := adjPoly_coeff_succ A i
    have hχ : (charpoly A).coeff (i + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim]; omega)
    rw [hχ, zero_smul, sub_eq_zero] at h
    exact h
  have key : ∀ d, ∀ i, N ≤ i → M ≤ i + d → (adjPoly A).coeff i = 0 := by
    intro d
    induction d with
    | zero => intro i _ hi; exact hbig i (by omega)
    | succ d ih =>
      intro i hi hid
      by_cases hMi : M ≤ i
      · exact hbig i hMi
      · rw [hstep i hi, ih (i + 1) (by omega) (by omega), mul_zero]
  exact key (M - j) j hj (by omega)

/-- `Pₖ = D_{N−1−k}` for `k < N`. -/
lemma faddeev_eq_adjPoly_coeff {k : ℕ} (hk : k < N) :
    faddeev A k = (adjPoly A).coeff (N - 1 - k) := by
  induction k with
  | zero =>
    rw [faddeev_zero]
    have h := adjPoly_coeff_succ A (N - 1)
    rw [show N - 1 + 1 = N by omega, adjPoly_coeff_eq_zero_of_le A le_rfl, mul_zero,
      sub_zero] at h
    rw [Nat.sub_zero, h, cdesc, if_pos (Nat.zero_le _), Nat.sub_zero]
  | succ k ih =>
    rw [faddeev_succ, ih (by omega)]
    have h := adjPoly_coeff_succ A (N - 1 - (k + 1))
    rw [show N - 1 - (k + 1) + 1 = N - 1 - k by omega, sub_eq_iff_eq_add] at h
    rw [h, cdesc, if_pos (by omega), show N - (k + 1) = N - 1 - k by omega, add_comm]

/-- `Pₖ = 0` for `k ≥ N`. -/
lemma faddeev_eq_zero_of_le {k : ℕ} (hk : N ≤ k) : faddeev A k = 0 := by
  induction k with
  | zero =>
    -- `N = 0`: the matrix ring is trivial
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp (by omega)
    exact Subsingleton.elim _ _
  | succ k ih =>
    rw [faddeev_succ]
    rcases Nat.lt_or_ge k N with hlt | hge
    · -- `k = N - 1`
      have hkN : k = N - 1 := by omega
      rw [faddeev_eq_adjPoly_coeff A hlt, hkN, Nat.sub_self, cdesc, if_pos (by omega),
        show N - (N - 1 + 1) = 0 by omega]
      have h := adjPoly_coeff_zero A
      rw [← h]; ring_nf
      simp
    · rw [ih hge, mul_zero, zero_add, cdesc, if_neg (by omega), zero_smul]

/-- **Unified trace identity**: `trace Pₖ = (N − k) cₖ` for every `k`. -/
lemma trace_faddeev_eq (k : ℕ) :
    trace (faddeev A k) = ((N : R) - k) * cdesc A k := by
  rcases Nat.lt_or_ge k N with hlt | hge
  · rw [faddeev_eq_adjPoly_coeff A hlt, trace_adjPoly_coeff, cdesc, if_pos hlt.le,
      show N - 1 - k + 1 = N - k by omega]
    have : ((N - 1 - k : ℕ) : R) + 1 = (N : R) - k := by
      rw [show N - 1 - k = N - k - 1 by omega, Nat.cast_sub (by omega : 1 ≤ N - k),
        Nat.cast_sub hlt.le]
      push_cast; ring
    rw [this]; ring
  · rw [faddeev_eq_zero_of_le A hge, trace_zero]
    rcases Nat.eq_or_lt_of_le hge with h | h
    · rw [← h]; ring
    · rw [cdesc, if_neg (by omega), mul_zero]

end Main

/-- **Newton's trace identity** for the characteristic polynomial. -/
theorem newton_trace_identity (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * cdesc A k + ∑ j ∈ Finset.Icc 1 k, trace (A ^ j) * cdesc A (k - j) = 0 := by
  nontriviality R
  have h := trace_faddeev_eq A k
  rw [trace_faddeev] at h
  -- reindex `∑_{i ≤ k} cᵢ tr(A^{k−i})` as `∑_{j ≤ k} tr(Aʲ) c_{k−j}` and split off `j = 0`
  have hre : ∑ i ∈ Finset.range (k + 1), cdesc A i * trace (A ^ (k - i)) =
      ∑ j ∈ Finset.range (k + 1), trace (A ^ j) * cdesc A (k - j) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega, mul_comm]
  have hsplit : ∑ j ∈ Finset.range (k + 1), trace (A ^ j) * cdesc A (k - j) =
      trace (A ^ 0) * cdesc A k + ∑ j ∈ Finset.Icc 1 k, trace (A ^ j) * cdesc A (k - j) := by
    have hI : Finset.Ico 1 (k + 1) = Finset.Icc 1 k := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI, Nat.sub_zero]
  rw [hre, hsplit, pow_zero, Matrix.trace_one] at h
  linear_combination h

end Submission
