import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# 2-adic integrality of square roots of power series

The formal power series `√(1 + 4X)` has integer coefficients: explicitly
`√(1 + 4X) = 1 + 2 X · C(-X)` where `C` is the Catalan generating function, because
`C(X)² X + 1 = C(X)`. Consequently, if `Q ∈ ℤ⟦X⟧` has `Q(0) = 1` and is a perfect square
modulo `4`, i.e. `Q = U² + 4V` with `U(0) = 1`, then `Q` has a square root in `1 + X ℤ⟦X⟧`.

This is Proposition 2.2 of V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on
polynomials* (2019); the Catalan route replaces the binomial-series argument there.
-/

open PowerSeries

namespace Submission

/-- The Catalan generating function with integer coefficients. -/
noncomputable def catalanZ : ℤ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℤ) catalanSeries

theorem catalanZ_sq_mul_X_add_one : catalanZ ^ 2 * X + 1 = catalanZ := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  simpa [catalanZ, map_add, map_mul, map_pow, PowerSeries.map_X] using h

/-- `√(1 + 4X) = 1 + 2 X C(-X)` as an integer power series. -/
noncomputable def sqrtOneAddFourX : ℤ⟦X⟧ := 1 + 2 * X * rescale (-1) catalanZ

theorem sqrtOneAddFourX_sq : sqrtOneAddFourX ^ 2 = 1 + 4 * X := by
  have h := congrArg (rescale (-1 : ℤ)) catalanZ_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, rescale_neg_one_X] at h
  unfold sqrtOneAddFourX
  linear_combination (-4 * X) * h

@[simp] theorem constantCoeff_sqrtOneAddFourX : constantCoeff sqrtOneAddFourX = 1 := by
  simp [sqrtOneAddFourX]

/-- **Dimitrov, Prop. 2.2.** If `Q = U² + 4V` with `U(0) = 1` (so `Q(0) = 1` and `Q` is a
square mod `4`), then `Q` has a square root in `1 + X ℤ⟦X⟧`. -/
theorem exists_sq_eq_of_sq_add_four_mul (U V : ℤ⟦X⟧) (hU : constantCoeff U = 1)
    (hV : constantCoeff V = 0) :
    ∃ g : ℤ⟦X⟧, g ^ 2 = U ^ 2 + 4 * V ∧ constantCoeff g = 1 := by
  set Uinv := invOfUnit U 1 with hUinv
  have hUU : U * Uinv = 1 := mul_invOfUnit U 1 (by simpa using hU)
  set W := V * Uinv ^ 2 with hW
  have hWc : constantCoeff W = 0 := by simp [hW, hV]
  have hsub : HasSubst W := HasSubst.of_constantCoeff_zero' hWc
  refine ⟨U * subst W sqrtOneAddFourX, ?_, ?_⟩
  · have h1 : subst W (sqrtOneAddFourX ^ 2) = subst W ((1 : ℤ⟦X⟧) + 4 * X) := by
      rw [sqrtOneAddFourX_sq]
    rw [subst_pow hsub, subst_add hsub, subst_mul hsub, subst_X hsub] at h1
    have h4 : subst W (4 : ℤ⟦X⟧) = 4 := by
      have : (4 : ℤ⟦X⟧) = C 4 := by simp
      rw [this, subst_C]; simp
    have h1' : subst W (1 : ℤ⟦X⟧) = 1 := by
      have : (1 : ℤ⟦X⟧) = C 1 := by simp
      rw [this, subst_C]; simp
    rw [h4, h1'] at h1
    calc (U * subst W sqrtOneAddFourX) ^ 2 = U ^ 2 * subst W sqrtOneAddFourX ^ 2 := by ring
      _ = U ^ 2 * (1 + 4 * W) := by rw [h1]
      _ = U ^ 2 + 4 * V * (U * Uinv) ^ 2 := by rw [hW]; ring
      _ = U ^ 2 + 4 * V := by rw [hUU]; ring
  · have hS₀ : constantCoeff (2 * X * rescale (-1 : ℤ) catalanZ) = 0 := by simp
    have h0 : constantCoeff (subst W (2 * X * rescale (-1 : ℤ) catalanZ)) = 0 :=
      constantCoeff_subst_eq_zero hWc _ hS₀
    have h1' : subst W (1 : ℤ⟦X⟧) = 1 := by
      have : (1 : ℤ⟦X⟧) = C 1 := by simp
      rw [this, subst_C]; simp
    rw [map_mul, hU, one_mul]
    unfold sqrtOneAddFourX
    rw [subst_add hsub, h1', map_add, h0]
    simp
