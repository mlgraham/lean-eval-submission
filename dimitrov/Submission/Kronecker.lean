import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Kronecker's criterion for Hankel determinants

Let `a : ℕ → F` be a sequence in a field and `hankel a k := (a (i + j))_{i,j < k}` its `k × k`
Hankel matrices. **Kronecker's theorem** (the direction needed for Pólya/Bertrandias-type
rationality theorems): if `det (hankel a r) ≠ 0` and `det (hankel a k) = 0` for every `k > r`,
then `a` satisfies a linear recurrence of order `r`, hence `∑ aₙ Xⁿ` is a rational function.

Proof. Solve `c ᵥ* hankel a r = (a (r + j))ⱼ` (possible since `det ≠ 0`); the recurrence defect
`e n := a (n + r) − ∑ₜ cₜ a (n + t)` then vanishes for `n < r`. If `n₀ ≥ r` were the least index
with `e n₀ ≠ 0`, row-reduce the `(n₀+1) × (n₀+1)` Hankel matrix by the recurrence: the result is
block upper triangular with blocks `hankel a r` and an anti-triangular block whose anti-diagonal
is `e n₀`, so its determinant is `det (hankel a r) · (± e n₀ ^ N) ≠ 0`, contradicting the
hypothesis.
-/

open Matrix Finset

namespace Submission

variable {F : Type*} [Field F]

/-- The `k × k` Hankel matrix of a sequence. -/
def hankel (a : ℕ → F) (k : ℕ) : Matrix (Fin k) (Fin k) F := of fun i j => a (i + j)

section Index

variable (r N : ℕ)

/-- The natural index of `Fin r ⊕ Fin N`, viewing it as `{0, …, r + N - 1}`. -/
def idx : Fin r ⊕ Fin N → ℕ := Sum.elim (fun t => (t : ℕ)) (fun i => r + i)

/-- The position of index `i + t` in `Fin r ⊕ Fin N`, for `i < N`, `t < r`. -/
def φ (i : Fin N) (t : Fin r) : Fin r ⊕ Fin N :=
  if h : (i : ℕ) + t < r then Sum.inl ⟨i + t, h⟩ else Sum.inr ⟨i + t - r, by omega⟩

lemma idx_φ (i : Fin N) (t : Fin r) : idx r N (φ r N i t) = i + t := by
  unfold φ
  split_ifs with h
  · simp [idx]
  · simp only [idx, Sum.elim_inr]; omega

lemma φ_ne_inr {i i' : Fin N} (t : Fin r) (h : (i : ℕ) ≤ i') : φ r N i t ≠ Sum.inr i' := by
  unfold φ
  split_ifs with h'
  · simp
  · intro heq
    have := Sum.inr_injective heq
    have := congrArg Fin.val this
    simp at this
    omega

lemma idx_finSumFinEquiv (x : Fin r ⊕ Fin N) : idx r N x = (finSumFinEquiv x : ℕ) := by
  rcases x with t | i <;> simp [idx]

end Index

/-- **Kronecker's criterion.** If `det (hankel a r) ≠ 0` and all larger Hankel determinants
vanish, then `a` satisfies a linear recurrence of order `r`. -/
theorem exists_recurrence_of_hankel_det (a : ℕ → F) (r : ℕ)
    (hr : (hankel a r).det ≠ 0) (hzero : ∀ k, r < k → (hankel a k).det = 0) :
    ∃ c : Fin r → F, ∀ n, a (n + r) = ∑ t, c t * a (n + t) := by
  classical
  have hunit : IsUnit (hankel a r).det := isUnit_iff_ne_zero.mpr hr
  set w : Fin r → F := fun j => a (r + j) with hw
  set c : Fin r → F := w ᵥ* (hankel a r)⁻¹ with hc
  have hcw : c ᵥ* hankel a r = w := by
    rw [hc, vecMul_vecMul, nonsing_inv_mul _ hunit, vecMul_one]
  set e : ℕ → F := fun n => a (n + r) - ∑ t, c t * a (n + t) with he
  have he_lt : ∀ n < r, e n = 0 := by
    intro n hn
    have h := congrFun hcw ⟨n, hn⟩
    simp only [vecMul, dotProduct, hankel, of_apply, hw] at h
    simp only [he, sub_eq_zero]
    rw [add_comm n r, ← h]
    exact Finset.sum_congr rfl fun t _ => by rw [add_comm (n : ℕ) t]
  refine ⟨c, fun n => ?_⟩
  by_contra hne
  have hex : ∃ n, e n ≠ 0 := ⟨n, fun h => hne (sub_eq_zero.mp h)⟩
  set n₀ := Nat.find hex with hn₀
  have hn₀ne : e n₀ ≠ 0 := Nat.find_spec hex
  have hn₀min : ∀ m < n₀, e m = 0 := fun m hm => by
    have := Nat.find_min hex hm
    simpa using this
  have hrn₀ : r ≤ n₀ := by
    by_contra h
    exact hn₀ne (he_lt n₀ (by omega))
  set N := n₀ + 1 - r with hN
  have hNpos : 0 < N := by omega
  -- the big Hankel matrix, indexed by `Fin r ⊕ Fin N`
  set M' : Matrix (Fin r ⊕ Fin N) (Fin r ⊕ Fin N) F :=
    of fun i j => a (idx r N i + idx r N j) with hM'
  have hM'det : M'.det = 0 := by
    have h1 : M' = (hankel a (r + N)).submatrix finSumFinEquiv finSumFinEquiv := by
      ext i j
      simp only [hM', of_apply, submatrix_apply, hankel, idx_finSumFinEquiv]
    rw [h1, det_submatrix_equiv_self]
    exact hzero _ (by omega)
  -- the row-reduction matrix
  set L : Matrix (Fin r ⊕ Fin N) (Fin r ⊕ Fin N) F := of fun i l =>
    Sum.elim (fun i₁ => if l = Sum.inl i₁ then (1 : F) else 0)
      (fun i₂ => (if l = Sum.inr i₂ then (1 : F) else 0) +
        ∑ t, if l = φ r N i₂ t then -c t else 0) i with hL
  have hLM_inl : ∀ i j, (L * M') (Sum.inl i) j = M' (Sum.inl i) j := by
    intro i j
    simp [hL, mul_apply, ite_mul]
  have hLM_inr : ∀ i j, (L * M') (Sum.inr i) j = e (i + idx r N j) := by
    intro i j
    simp only [mul_apply, hL, of_apply, Sum.elim_inr, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hM', of_apply, idx_φ, he, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
    have hidx : idx r N (Sum.inr i) = r + i := rfl
    rw [hidx, show r + (i : ℕ) + idx r N j = (i : ℕ) + idx r N j + r by omega]
    congr 2
    exact Finset.sum_congr rfl fun t _ => by
      rw [show (i : ℕ) + t + idx r N j = (i : ℕ) + idx r N j + t by omega]
  -- block structure of `L * M'`
  have h11 : (L * M').toBlocks₁₁ = hankel a r := by
    ext i j
    simp only [toBlocks₁₁, of_apply]
    rw [hLM_inl]
    simp [hM', idx, hankel]
  have h21 : (L * M').toBlocks₂₁ = 0 := by
    ext i j
    simp only [toBlocks₂₁, of_apply, hLM_inr, Matrix.zero_apply]
    apply hn₀min
    simp only [idx, Sum.elim_inl]
    omega
  have hdet_LM : (L * M').det = (hankel a r).det * ((L * M').toBlocks₂₂).det := by
    conv_lhs => rw [← fromBlocks_toBlocks (L * M')]
    rw [h21, det_fromBlocks_zero₂₁, h11]
  -- `det L = 1`
  have hL11 : L.toBlocks₁₁ = 1 := by
    ext i j
    simp [toBlocks₁₁, hL, one_apply, eq_comm]
  have hL12 : L.toBlocks₁₂ = 0 := by
    ext i j
    simp [toBlocks₁₂, hL]
  have hL22_apply : ∀ i j : Fin N, L.toBlocks₂₂ i j =
      (if j = i then (1 : F) else 0) + ∑ t, if Sum.inr j = φ r N i t then -c t else 0 := by
    intro i j
    simp [toBlocks₂₂, hL]
  have hL22_lower : L.toBlocks₂₂.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    rw [hL22_apply, if_neg (ne_of_gt hij')]
    simp only [zero_add]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    exact fun h => φ_ne_inr r N t (le_of_lt hij') h.symm
  have hL22_diag : ∀ i, L.toBlocks₂₂ i i = 1 := by
    intro i
    rw [hL22_apply, if_pos rfl]
    have : (∑ t, if Sum.inr i = φ r N i t then -c t else 0) = 0 :=
      Finset.sum_eq_zero fun t _ => by
        rw [if_neg]; exact fun h => φ_ne_inr r N t le_rfl h.symm
    rw [this, add_zero]
  have hLdet : L.det = 1 := by
    rw [← fromBlocks_toBlocks L, hL12, det_fromBlocks_zero₁₂, hL11, det_one, one_mul,
      det_of_isLowerTriangular _ hL22_lower]
    simp [hL22_diag]
  -- hence `det (toBlocks₂₂ (L * M')) = 0`
  have hB22 : ((L * M').toBlocks₂₂).det = 0 := by
    have h := hdet_LM
    rw [det_mul, hLdet, one_mul, hM'det] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hr
    · exact h'
  -- but it is `± (e n₀) ^ N ≠ 0`
  set B := (L * M').toBlocks₂₂ with hB
  have hB_apply : ∀ i j : Fin N, B i j = e (i + (r + j)) := by
    intro i j
    simp [hB, toBlocks₂₂, hLM_inr, idx]
  set P := B.submatrix id Fin.revPerm with hP
  have hP_apply : ∀ i j : Fin N, P i j = e (i + (r + (N - (j + 1)))) := by
    intro i j
    simp [hP, submatrix_apply, hB_apply, Fin.revPerm_apply, Fin.val_rev]
  have hP_lower : P.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    rw [hP_apply]
    apply hn₀min
    have := j.isLt
    have := i.isLt
    omega
  have hP_diag : ∀ i, P i i = e n₀ := by
    intro i
    rw [hP_apply]
    congr 1
    have := i.isLt
    omega
  have hPdet : P.det = e n₀ ^ N := by
    rw [det_of_isLowerTriangular _ hP_lower]
    simp [hP_diag]
  have hPdet' : P.det = Equiv.Perm.sign Fin.revPerm * B.det := det_permute' _ _
  rw [hB22, mul_zero, hPdet] at hPdet'
  exact pow_ne_zero N hn₀ne hPdet'

end Submission

namespace Submission

variable {F : Type*} [Field F]

open Matrix Finset

/-- If all Hankel determinants of `a` from some index on vanish, then `a` satisfies a linear
recurrence (of some order `r ≤ k₀`). -/
theorem exists_recurrence_of_hankel_det_eventually (a : ℕ → F) (k₀ : ℕ)
    (h : ∀ k, k₀ ≤ k → (hankel a k).det = 0) :
    ∃ r, r ≤ k₀ ∧ ∃ c : Fin r → F, ∀ n, a (n + r) = ∑ t, c t * a (n + t) := by
  classical
  set P : ℕ → Prop := fun k => (hankel a k).det ≠ 0 with hP
  have h0 : P 0 := by simp [hP, hankel, det_isEmpty]
  set r := Nat.findGreatest P k₀ with hr
  refine ⟨r, Nat.findGreatest_le k₀, exists_recurrence_of_hankel_det a r ?_ ?_⟩
  · exact Nat.findGreatest_spec (Nat.zero_le k₀) h0
  · intro k hk
    by_cases hkk : k ≤ k₀
    · have := Nat.findGreatest_is_greatest (P := P) hk hkk
      simpa [hP] using this
    · exact h k (by omega)

/-- A sequence satisfying a linear recurrence has a rational generating function:
`(∑ aₙ Xⁿ) · Q = P` with `Q(0) = 1` and `deg P < r`. -/
theorem exists_polynomial_mul_eq_of_recurrence (a : ℕ → F) (r : ℕ) (c : Fin r → F)
    (hrec : ∀ n, a (n + r) = ∑ t, c t * a (n + t)) :
    ∃ (P Q : Polynomial F), Q.coeff 0 = 1 ∧ Q.natDegree ≤ r ∧
      PowerSeries.mk a * (Q : PowerSeries F) = (P : PowerSeries F) := by
  classical
  set Qs : PowerSeries F := 1 - ∑ t : Fin r, PowerSeries.C (c t) * PowerSeries.X ^ (r - t)
    with hQs
  set Qp : Polynomial F := 1 - ∑ t : Fin r, Polynomial.C (c t) * Polynomial.X ^ (r - t)
    with hQp
  have hQcoe : (Qp : PowerSeries F) = Qs := by
    rw [hQp, hQs, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sub, map_one, map_sum]
    simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.coe_X]
  -- the coefficients of `mk a * Qs` vanish from `r` on
  have hcoeff : ∀ m, r ≤ m → PowerSeries.coeff m (PowerSeries.mk a * Qs) = 0 := by
    intro m hm
    rw [hQs, mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, Finset.mul_sum, map_sum]
    have hterm : ∀ t : Fin r,
        PowerSeries.coeff m (PowerSeries.mk a * (PowerSeries.C (c t) * PowerSeries.X ^ (r - t)))
          = c t * a (m - r + t) := by
      intro t
      rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', if_pos (by omega),
        PowerSeries.coeff_mk]
      congr 2
      omega
    simp only [hterm]
    have := hrec (m - r)
    rw [show m - r + r = m by omega] at this
    rw [this, sub_self]
  refine ⟨PowerSeries.trunc r (PowerSeries.mk a * Qs), Qp, ?_, ?_, ?_⟩
  · rw [hQp, Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_zero (fun t _ => by rw [if_neg (by omega), mul_zero]), sub_zero]
  · rw [hQp]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine (Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ => ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · rw [hQcoe]
    ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hmr
    · rfl
    · exact hcoeff m (by omega)

end Submission
