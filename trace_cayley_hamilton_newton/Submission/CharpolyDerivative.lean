import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The derivative of the characteristic polynomial

`derivative (charpoly A) = trace (adjugate (charmatrix A))` (Jacobi's formula for the
characteristic polynomial). Proof: translate the variable, `χ(X + Y) = det ((X•1 − A) + Y•1)`,
expand the determinant multilinearly in the rows, and read off the coefficient of `Y`: it is
`∑ᵢ det (M.updateRow i (Pi.single i 1)) = trace (adjugate M)` with `M = charmatrix A`; on the
other side `(taylor X χ).coeff 1 = χ'`.
-/

open Polynomial Matrix

namespace Submission

variable {n : Type*} [Fintype n] [DecidableEq n]

section CoeffOne

variable {S : Type*} [CommRing S]

/-- Replacing the rows in a singleton `{i}` by the corresponding rows of `1` is `updateRow`. -/
lemma piecewise_singleton_one (M : Matrix n n S) (i : n) :
    ({i} : Finset n).piecewise (1 : Matrix n n S) M = M.updateRow i (Pi.single i 1) := by
  ext a b
  simp only [Finset.piecewise, Finset.mem_singleton, updateRow_apply]
  split_ifs with h
  · subst h; simp [one_apply, Pi.single_apply, eq_comm]
  · rfl

/-- The coefficient of `X` in `det (M + X • 1)` is the trace of the adjugate of `M`. -/
theorem coeff_one_det_map_C_add_X_smul_one (M : Matrix n n S) :
    (det (M.map C + (X : S[X]) • (1 : Matrix n n S[X]))).coeff 1 = trace (adjugate M) := by
  simp only [det]
  let D := (detRowAlternating : (n → S[X]) [⋀^n]→ₗ[S[X]] S[X])
  rw [add_comm]
  change (D (fun i => ((X : S[X]) • (1 : Matrix n n S[X])) i + (M.map C) i)).coeff 1 = _
  conv_lhs => rw [show (fun i ↦ ((X : S[X]) • (1 : Matrix n n S[X])) i + (M.map C) i) =
      (fun i => ((X : S[X]) • (1 : Matrix n n S[X])) i) + (fun i => (M.map C) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  have h_map : ∀ s : Finset n,
        (s.piecewise (fun i ↦ (1 : Matrix n n S[X]) i) (fun i ↦ (M.map C) i) : Matrix n n S[X]) =
        Matrix.map (s.piecewise (1 : Matrix n n S) M) C := by
      intro s; funext i j
      have hR : Matrix.map (s.piecewise (1 : Matrix n n S) M) C i j =
          C (if i ∈ s then (1 : Matrix n n S) i j else M i j) := by
        simp only [Matrix.map, Matrix.of_apply, Finset.piecewise]
        split_ifs <;> rfl
      rw [hR]
      simp only [Finset.piecewise]
      split_ifs with h
      · simp [Matrix.one_apply, apply_ite C]
      · rfl
  have h_det : ∀ s : Finset n,
      D (s.piecewise (fun i ↦ (1 : Matrix n n S[X]) i) (fun i ↦ (M.map C) i)) =
      C (det (s.piecewise (1 : Matrix n n S) M)) := by
    intro s; change det _ = _
    rw [h_map]; exact (RingHom.map_det C _).symm
  calc (∑ s : Finset n, D (Finset.piecewise s (fun i ↦ ((X : S[X]) • (1 : Matrix n n S[X])) i)
            (fun i ↦ (M.map C) i))).coeff 1
      _ = (∑ s : Finset n, (X : S[X]) ^ s.card •
            D (s.piecewise (fun i ↦ (1 : Matrix n n S[X]) i) (fun i ↦ (M.map C) i))).coeff 1 := by
        congr 2 with s
        have h_smul : s.piecewise (fun i ↦ ((X : S[X]) • (1 : Matrix n n S[X])) i)
            (fun i ↦ (M.map C) i) =
            fun i => (if i ∈ s then (X : S[X]) else 1) •
              s.piecewise (fun i ↦ (1 : Matrix n n S[X]) i) (fun i ↦ (M.map C) i) i := by
          funext i j
          simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul, ite_mul, one_mul]
          split_ifs <;> rfl
        rw [h_smul, D.map_smul_univ]
        congr 1
        simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      _ = ∑ s : Finset n, ((X : S[X]) ^ s.card •
            D (Finset.piecewise s (fun i ↦ (1 : Matrix n n S[X]) i) (fun i ↦ (M.map C) i))).coeff 1 := by
        simp only [Polynomial.finsetSum_coeff]
      _ = ∑ s ∈ Finset.univ.powersetCard 1, det (s.piecewise (1 : Matrix n n S) M) := by
        simp_rw [h_det, smul_eq_mul, mul_comm (X ^ _) (C _)]
        simp_rw [C_mul_X_pow_eq_monomial, coeff_monomial]
        rw [← Finset.sum_filter]
        congr 1
        ext s; simp [Finset.mem_powersetCard]
      _ = trace (adjugate M) := by
        rw [Finset.powersetCard_one, Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk, piecewise_singleton_one, Matrix.trace,
          Matrix.diag_apply, adjugate_apply]

end CoeffOne

section Derivative

variable {R : Type*} [CommRing R]

/-- **Jacobi's formula for the characteristic polynomial**:
`χ_A' = trace (adjugate (X • 1 − A))`. -/
theorem derivative_charpoly (A : Matrix n n R) :
    derivative (charpoly A) = trace (adjugate (charmatrix A)) := by
  -- work over `S := R[X]`, with a fresh variable `Y` for `S[Y]`
  set S := R[X] with hS
  set f : S[X] := (charpoly A).map (C : R →+* S) with hf
  -- the Taylor shift of `f` by `X ∈ S`
  have h1 : (taylor (X : S) f).coeff 1 = derivative (charpoly A) := by
    rw [taylor_coeff_one, hf, derivative_map, eval_map, eval₂_C_X]
  -- the Taylor shift is the determinant of `(charmatrix A).map C + Y • 1`
  have h2 : taylor (X : S) f =
      det ((charmatrix A).map (C : S → S[X]) + (X : S[X]) • (1 : Matrix n n S[X])) := by
    rw [taylor_apply, hf, ← charpoly_map, charpoly]
    rw [show (det (charmatrix (A.map (C : R →+* S)))).comp (X + C X) =
        compRingHom (X + C X) (det (charmatrix (A.map (C : R →+* S)))) from rfl, RingHom.map_det]
    congr 1
    funext i j
    by_cases hij : i = j
    · subst hij
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, charmatrix_apply_eq, coe_compRingHom,
        sub_comp, X_comp, C_comp, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one, map_sub]
      ring
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, charmatrix_apply_ne _ _ _ hij,
        coe_compRingHom, neg_comp, C_comp, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hij, smul_eq_mul, mul_zero, add_zero]
      exact (map_neg C _).symm
  rw [← h1, h2, coeff_one_det_map_C_add_X_smul_one]

end Derivative

end Submission
