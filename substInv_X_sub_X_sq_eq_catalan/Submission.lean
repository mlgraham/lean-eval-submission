import Mathlib
import Submission.Helpers

open PowerSeries

namespace Submission

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  let _ : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]
    exact invertibleOne
  let S : ℚ⟦X⟧ := substInv ((X : ℚ⟦X⟧) - X ^ 2)
  let C : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries
  let Q : ℚ⟦X⟧ := X * C
  have hC : C ^ 2 * X + 1 = C := by
    simpa [C] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
  have hQ : Q - Q ^ 2 = X := by
    have hC' : C - C ^ 2 * X = 1 := by
      apply sub_eq_iff_eq_add.mpr
      simpa [add_comm] using hC.symm
    calc
      Q - Q ^ 2 = X * (C - C ^ 2 * X) := by simp only [Q]; ring
      _ = X := by rw [hC', mul_one]
  have hP0 : ((X : ℚ⟦X⟧) - X ^ 2).constantCoeff = 0 := by simp
  have hQ0 : Q.constantCoeff = 0 := by simp [Q]
  have hPQ : ((X : ℚ⟦X⟧) - X ^ 2).subst Q = X := by
    let hQs := HasSubst.of_constantCoeff_zero hQ0
    calc
      ((X : ℚ⟦X⟧) - X ^ 2).subst Q = Q - Q ^ 2 := by
        rw [subst_sub hQs, subst_X hQs, subst_pow hQs, subst_X hQs]
      _ = X := hQ
  have hQP : S.subst ((X : ℚ⟦X⟧) - X ^ 2) = X := by
    dsimp [S]
    exact subst_substInv_left ((X : ℚ⟦X⟧) - X ^ 2) hP0
  have hcomp :
      PowerSeries.subst Q (PowerSeries.subst ((X : ℚ⟦X⟧) - X ^ 2) S) =
        PowerSeries.subst (PowerSeries.subst Q ((X : ℚ⟦X⟧) - X ^ 2)) S := by
    exact subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := ℚ) (υ := Unit)
      (a := (X : ℚ⟦X⟧) - X ^ 2) (b := Q)
      (HasSubst.of_constantCoeff_zero hP0)
      (HasSubst.of_constantCoeff_zero hQ0) S
  have hEq : Q = S := by
    calc
      Q = X.subst Q := (subst_X (HasSubst.of_constantCoeff_zero hQ0)).symm
      _ = PowerSeries.subst Q (PowerSeries.subst ((X : ℚ⟦X⟧) - X ^ 2) S) := by rw [hQP]
      _ = PowerSeries.subst (PowerSeries.subst Q ((X : ℚ⟦X⟧) - X ^ 2)) S := hcomp
      _ = S := by rw [hPQ, X_subst]
  change coeff (n + 1) S = _
  rw [← hEq]
  simp only [Q, coeff_succ_X_mul, C, coeff_map, catalanSeries_coeff]
  rw [eq_div_iff]
  · have hnat : catalan n * (n + 1) = Nat.choose (2 * n) n := by
      simpa [Nat.centralBinom_eq_two_mul_choose, mul_comm] using
        succ_mul_catalan_eq_centralBinom n
    simpa using congrArg (fun k : ℕ => (k : ℚ)) hnat
  · positivity

end Submission
