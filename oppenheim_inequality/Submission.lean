import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers

open scoped MatrixOrder Matrix
open Matrix

namespace Submission

universe u

/-! ### Monotonicity of the determinant under adding a positive semidefinite matrix -/

section DetMono

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every eigenvalue of `1 + Z` is at least `1` when `Z` is positive semidefinite. -/
lemma one_le_eigenvalues_one_add {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) (j : n) :
    1 ≤ (isHermitian_one.add hZ.1).eigenvalues j := by
  set H : (1 + Z).IsHermitian := isHermitian_one.add hZ.1
  set v : n → ℝ := ⇑(H.eigenvectorBasis j) with hv_def
  have hv : (1 + Z) *ᵥ v = H.eigenvalues j • v := H.mulVec_eigenvectorBasis j
  have hvv : v ⬝ᵥ v = 1 := by
    have h := orthonormal_iff_ite.mp (H.eigenvectorBasis).orthonormal j j
    rw [if_pos rfl, EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [hv_def] using h
  have h1 : v ⬝ᵥ ((1 + Z) *ᵥ v) = H.eigenvalues j := by
    rw [hv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
  have h2 : v ⬝ᵥ ((1 + Z) *ᵥ v) = 1 + v ⬝ᵥ (Z *ᵥ v) := by
    rw [add_mulVec, one_mulVec, dotProduct_add, hvv]
  have h3 : 0 ≤ v ⬝ᵥ (Z *ᵥ v) := by simpa using hZ.dotProduct_mulVec_nonneg v
  linarith

/-- `det (1 + Z) ≥ 1` for `Z` positive semidefinite. -/
lemma one_le_det_one_add {Z : Matrix n n ℝ} (hZ : Z.PosSemidef) : 1 ≤ (1 + Z).det := by
  have H : (1 + Z).IsHermitian := isHermitian_one.add hZ.1
  rw [H.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, H.eigenvalues i :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => one_le_eigenvalues_one_add hZ i)

/-- The determinant is monotone under adding a positive semidefinite matrix. -/
lemma det_le_det_add {X Y : Matrix n n ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    X.det ≤ (X + Y).det := by
  by_cases hdet : X.det = 0
  · rw [hdet]; exact (hX.add hY).det_nonneg
  · set R := CFC.sqrt X with hR
    have hRps : R.PosSemidef := (CFC.sqrt_nonneg X).posSemidef
    have hRR : R * R = X := by rw [← sq]; exact CFC.sq_sqrt X hX.nonneg
    have hXdet : X.det = R.det * R.det := by rw [← hRR, det_mul]
    have hRdet : R.det ≠ 0 := by
      intro h; apply hdet; rw [hXdet, h, zero_mul]
    have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
    have hRinv : R⁻¹.IsHermitian := hRps.1.inv
    set Z := R⁻¹ * Y * R⁻¹ with hZ
    have hZps : Z.PosSemidef := by
      have := hY.conjTranspose_mul_mul_same R⁻¹
      rwa [hRinv.eq] at this
    have hXY : X + Y = R * (1 + Z) * R := by
      rw [mul_add, add_mul, mul_one, hRR, hZ, ← mul_assoc, ← mul_assoc,
        mul_nonsing_inv _ hRunit, one_mul, mul_assoc, nonsing_inv_mul _ hRunit, mul_one]
    rw [hXY, det_mul, det_mul, hXdet]
    have h1 := one_le_det_one_add hZps
    have hRdetpos : 0 < R.det := lt_of_le_of_ne hRps.det_nonneg (Ne.symm hRdet)
    have hRR' : 0 < R.det * R.det := mul_pos hRdetpos hRdetpos
    nlinarith

end DetMono

/-! ### One-by-one blocks -/

section Unique

variable {m : Type*} [Fintype m] [DecidableEq m] [Unique m]

lemma inv_unique_apply (M : Matrix m m ℝ) (i j : m) : M⁻¹ i j = (M i j)⁻¹ := by
  rw [inv_subsingleton]
  obtain rfl := Subsingleton.elim i j
  simp [Ring.inverse_eq_inv]

lemma mul_inv_mul_apply {p : Type*} (X : Matrix p m ℝ) (M : Matrix m m ℝ) (Y : Matrix m p ℝ)
    (i j : p) :
    (X * M⁻¹ * Y) i j = X i default * (M default default)⁻¹ * Y default j := by
  simp [mul_apply, inv_unique_apply]

lemma posDef_of_unique {M : Matrix m m ℝ} (h : 0 < M default default) : M.PosDef := by
  have hM : M = diagonal (fun _ => M default default) := by
    ext i j
    obtain rfl := Subsingleton.elim i j
    obtain rfl := Subsingleton.elim i default
    simp
  rw [hM]
  exact posDef_diagonal_iff.mpr (fun _ => h)

end Unique

/-! ### Oppenheim's inequality by induction on the size -/

theorem oppenheim_aux (k : ℕ) :
    ∀ {n : Type u} [Fintype n] [DecidableEq n], Fintype.card n = k →
      ∀ {A B : Matrix n n ℝ}, A.PosSemidef → B.PosSemidef →
        A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  induction k with
  | zero =>
    intro n _ _ hcard A B _ _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard
    simp [det_isEmpty]
  | succ k ih =>
    intro n _ _ hcard A B hA hB
    by_cases hAdet : A.det = 0
    · rw [hAdet, zero_mul]; exact (hA.hadamard hB).det_nonneg
    by_cases hBprod : ∏ i, B i i = 0
    · rw [hBprod, mul_zero]; exact (hA.hadamard hB).det_nonneg
    have hApd : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hAdet
    have hBdiag : ∀ i, 0 < B i i := fun i =>
      lt_of_le_of_ne hB.diag_nonneg
        (Ne.symm (Finset.prod_ne_zero_iff.mp hBprod i (Finset.mem_univ i)))
    obtain ⟨i₀⟩ : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    -- reindex along `{i // i = i₀} ⊕ {i // ¬ i = i₀} ≃ n`
    set e := Equiv.sumCompl (fun i : n => i = i₀) with he
    set A' := A.submatrix e e with hA'def
    set B' := B.submatrix e e with hB'def
    have hA' : A'.PosSemidef := hA.submatrix e
    have hB' : B'.PosSemidef := hB.submatrix e
    have hdetA : A'.det = A.det := det_submatrix_equiv_self e A
    have hdetAB : (A' ⊙ B').det = (A ⊙ B).det := by
      rw [hA'def, hB'def, ← submatrix_hadamard]; exact det_submatrix_equiv_self e _
    -- blocks
    set A₁₁ := A'.toBlocks₁₁ with hA₁₁
    set A₁₂ := A'.toBlocks₁₂ with hA₁₂
    set A₂₁ := A'.toBlocks₂₁ with hA₂₁
    set A₂₂ := A'.toBlocks₂₂ with hA₂₂
    set B₁₁ := B'.toBlocks₁₁ with hB₁₁
    set B₁₂ := B'.toBlocks₁₂ with hB₁₂
    set B₂₁ := B'.toBlocks₂₁ with hB₂₁
    set B₂₂ := B'.toBlocks₂₂ with hB₂₂
    have hAblk : fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ = A' := fromBlocks_toBlocks A'
    have hBblk : fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ = B' := fromBlocks_toBlocks B'
    have hA21 : A₂₁ = A₁₂ᴴ := by
      ext i j
      simp only [hA₂₁, hA₁₂, toBlocks₂₁, toBlocks₁₂, of_apply, conjTranspose_apply]
      exact (hA'.1.apply _ _).symm
    have hB21 : B₂₁ = B₁₂ᴴ := by
      ext i j
      simp only [hB₂₁, hB₁₂, toBlocks₂₁, toBlocks₁₂, of_apply, conjTranspose_apply]
      exact (hB'.1.apply _ _).symm
    -- the pivot entries
    have hα : 0 < A₁₁ default default := hApd.diag_pos
    have hβ : 0 < B₁₁ default default := hBdiag _
    have hA11pd : A₁₁.PosDef := posDef_of_unique hα
    have hB11pd : B₁₁.PosDef := posDef_of_unique hβ
    haveI : Invertible A₁₁ :=
      invertibleOfIsUnitDet _ (by rw [det_unique]; exact isUnit_iff_ne_zero.mpr hα.ne')
    haveI : Invertible B₁₁ :=
      invertibleOfIsUnitDet _ (by rw [det_unique]; exact isUnit_iff_ne_zero.mpr hβ.ne')
    haveI : Invertible (A₁₁ ⊙ B₁₁) :=
      invertibleOfIsUnitDet _ (by
        rw [det_unique, hadamard_apply]; exact isUnit_iff_ne_zero.mpr (mul_pos hα hβ).ne')
    -- Schur complements
    set SA := A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂ with hSA
    set SB := B₂₂ - B₂₁ * B₁₁⁻¹ * B₁₂ with hSB
    set SAB := A₂₂ ⊙ B₂₂ - (A₂₁ ⊙ B₂₁) * (A₁₁ ⊙ B₁₁)⁻¹ * (A₁₂ ⊙ B₁₂) with hSAB
    have hSApsd : SA.PosSemidef := by
      have hblk : (fromBlocks A₁₁ A₁₂ A₁₂ᴴ A₂₂).PosSemidef := by
        rw [← hA21, hAblk]; exact hA'
      have := (PosDef.fromBlocks₁₁ A₁₂ A₂₂ hA11pd).mp hblk
      rwa [← hA21] at this
    have hSBpsd : SB.PosSemidef := by
      have hblk : (fromBlocks B₁₁ B₁₂ B₁₂ᴴ B₂₂).PosSemidef := by
        rw [← hB21, hBblk]; exact hB'
      have := (PosDef.fromBlocks₁₁ B₁₂ B₂₂ hB11pd).mp hblk
      rwa [← hB21] at this
    have hB22psd : B₂₂.PosSemidef := hB'.submatrix Sum.inr
    -- determinants via the Schur complement
    have hdetA' : A'.det = A₁₁ default default * SA.det := by
      rw [← hAblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique]
    have hhad : A' ⊙ B' = fromBlocks (A₁₁ ⊙ B₁₁) (A₁₂ ⊙ B₁₂) (A₂₁ ⊙ B₂₁) (A₂₂ ⊙ B₂₂) := by
      rw [← hAblk, ← hBblk]
      ext (i | i) (j | j) <;> rfl
    have hdetAB' : (A' ⊙ B').det =
        A₁₁ default default * B₁₁ default default * SAB.det := by
      rw [hhad, det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique, hadamard_apply]
    -- the key identity
    have hkey : SAB = SA ⊙ B₂₂ + (A₂₁ * A₁₁⁻¹ * A₁₂) ⊙ SB := by
      ext i j
      simp only [hSAB, hSA, hSB, Matrix.sub_apply, hadamard_apply, Matrix.add_apply, mul_inv_mul_apply, mul_inv]
      ring
    -- the correction term is positive semidefinite
    have hP : ((A₂₁ * A₁₁⁻¹ * A₁₂) ⊙ SB).PosSemidef := by
      have hrank : A₂₁ * A₁₁⁻¹ * A₁₂ = (A₁₁ default default)⁻¹ • (A₂₁ * A₂₁ᴴ) := by
        ext i j
        have : A₁₂ = A₂₁ᴴ := by rw [hA21, conjTranspose_conjTranspose]
        simp only [mul_inv_mul_apply, Matrix.smul_apply, mul_apply, Fintype.sum_unique, this,
          conjTranspose_apply, star_trivial, smul_eq_mul, inv_unique_apply]
        ring
      rw [hrank]
      exact ((posSemidef_self_mul_conjTranspose A₂₁).smul (inv_nonneg.mpr hα.le)).hadamard hSBpsd
    -- induction hypothesis on the Schur complement of `A` and the lower block of `B`
    have hcardU : Fintype.card {i : n // ¬ i = i₀} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]; rfl
    have hih := ih hcardU hSApsd hB22psd
    -- the product of the diagonal of `B`
    have hprod : ∏ i, B i i = B₁₁ default default * ∏ j, B₂₂ j j := by
      rw [← Fintype.prod_equiv e (fun i => B' i i) (fun i => B i i) (fun _ => rfl),
        Fintype.prod_sum_type, Fintype.prod_unique]
      rfl
    -- assemble
    have hmono : (SA ⊙ B₂₂).det ≤ SAB.det := by
      rw [hkey]; exact det_le_det_add (hSApsd.hadamard hB22psd) hP
    have hαβ : 0 ≤ A₁₁ default default * B₁₁ default default := (mul_pos hα hβ).le
    calc A.det * ∏ i, B i i
        = A₁₁ default default * B₁₁ default default * (SA.det * ∏ j, B₂₂ j j) := by
          rw [← hdetA, hdetA', hprod]; ring
      _ ≤ A₁₁ default default * B₁₁ default default * (SA ⊙ B₂₂).det :=
          mul_le_mul_of_nonneg_left hih hαβ
      _ ≤ A₁₁ default default * B₁₁ default default * SAB.det :=
          mul_le_mul_of_nonneg_left hmono hαβ
      _ = (A ⊙ B).det := by rw [← hdetAB, hdetAB']

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det :=
  oppenheim_aux (Fintype.card n) rfl hA hB

end Submission
