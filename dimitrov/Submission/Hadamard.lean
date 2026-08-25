import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Hadamard's determinant inequality

For a matrix `M` over `𝕜 = ℝ` or `ℂ`, `‖det M‖² ≤ ∏ᵢ ∑ⱼ ‖M i j‖²` (the determinant is bounded
by the product of the Euclidean norms of the rows).

The proof goes through the positive semidefinite form (Fischer/Hadamard):
`re (det G) ≤ ∏ᵢ re (G i i)` for `G` positive semidefinite, proved by induction on the size via
Schur complements, using that the determinant is monotone under adding a positive semidefinite
matrix (`det_re_le_det_re_add`). Then `‖det M‖² = det (M Mᴴ)` and `(M Mᴴ) i i = ∑ⱼ ‖M i j‖²`.

None of this is in Mathlib at the pinned revision (Mathlib has the Hadamard *product*, not the
inequality).
-/

open scoped MatrixOrder Matrix ComplexOrder
open Matrix

namespace Submission

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Monotonicity of the determinant under adding a positive semidefinite matrix -/

section DetMono

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every eigenvalue of `1 + Z` is at least `1` when `Z` is positive semidefinite. -/
lemma one_le_eigenvalues_one_add {Z : Matrix n n 𝕜} (hZ : Z.PosSemidef) (j : n) :
    1 ≤ (isHermitian_one.add hZ.1).eigenvalues j := by
  set H : (1 + Z).IsHermitian := isHermitian_one.add hZ.1
  set v : n → 𝕜 := ⇑(H.eigenvectorBasis j) with hv_def
  have hv : (1 + Z) *ᵥ v = H.eigenvalues j • v := H.mulVec_eigenvectorBasis j
  have hvv : star v ⬝ᵥ v = 1 := by
    have h := orthonormal_iff_ite.mp (H.eigenvectorBasis).orthonormal j j
    rw [if_pos rfl, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm]
    simpa [hv_def] using h
  have h1 : star v ⬝ᵥ ((1 + Z) *ᵥ v) = ((H.eigenvalues j : ℝ) : 𝕜) := by
    rw [hv, dotProduct_smul, hvv, RCLike.real_smul_eq_coe_mul, mul_one]
  have h2 : star v ⬝ᵥ ((1 + Z) *ᵥ v) = 1 + star v ⬝ᵥ (Z *ᵥ v) := by
    rw [add_mulVec, one_mulVec, dotProduct_add, hvv]
  have h3 : 0 ≤ star v ⬝ᵥ (Z *ᵥ v) := hZ.dotProduct_mulVec_nonneg v
  have h3' := (RCLike.nonneg_iff.mp h3).1
  have := congrArg RCLike.re (h1.symm.trans h2)
  simp only [RCLike.ofReal_re, map_add, RCLike.one_re] at this
  linarith

/-- `det (1 + Z)` is a real number `≥ 1` for `Z` positive semidefinite. -/
lemma exists_one_le_det_one_add {Z : Matrix n n 𝕜} (hZ : Z.PosSemidef) :
    ∃ r : ℝ, 1 ≤ r ∧ (1 + Z).det = (r : 𝕜) := by
  have H : (1 + Z).IsHermitian := isHermitian_one.add hZ.1
  refine ⟨∏ i, H.eigenvalues i, ?_, ?_⟩
  · calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, H.eigenvalues i :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => one_le_eigenvalues_one_add hZ i)
  · rw [H.det_eq_prod_eigenvalues, RCLike.ofReal_prod]

/-- The determinant of a positive semidefinite matrix is a nonnegative real number. -/
lemma posSemidef_exists_det_eq_ofReal {X : Matrix n n 𝕜} (hX : X.PosSemidef) :
    ∃ a : ℝ, 0 ≤ a ∧ X.det = (a : 𝕜) := by
  refine ⟨∏ i, hX.1.eigenvalues i, Finset.prod_nonneg (fun i _ => hX.eigenvalues_nonneg i), ?_⟩
  rw [hX.1.det_eq_prod_eigenvalues, RCLike.ofReal_prod]

/-- The determinant is monotone under adding a positive semidefinite matrix. -/
lemma det_re_le_det_re_add {X Y : Matrix n n 𝕜} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    RCLike.re X.det ≤ RCLike.re (X + Y).det := by
  obtain ⟨a, ha, hXa⟩ := posSemidef_exists_det_eq_ofReal hX
  by_cases hdet : X.det = 0
  · rw [hdet, map_zero]
    obtain ⟨b, hb, hb'⟩ := posSemidef_exists_det_eq_ofReal (hX.add hY)
    rw [hb']; simpa using hb
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
    obtain ⟨r, hr, hrdet⟩ := exists_one_le_det_one_add hZps
    obtain ⟨s, hs, hsdet⟩ := posSemidef_exists_det_eq_ofReal hRps
    have hX' : X.det = ((s * s : ℝ) : 𝕜) := by rw [hXdet, hsdet]; push_cast; ring
    have hXY' : (X + Y).det = ((s * r * s : ℝ) : 𝕜) := by
      rw [hXY, det_mul, det_mul, hrdet, hsdet]; push_cast; ring
    rw [hX', hXY', RCLike.ofReal_re, RCLike.ofReal_re]
    nlinarith [mul_nonneg hs hs]

end DetMono

/-! ### One-by-one blocks -/

section Unique

variable {m : Type*} [Fintype m] [DecidableEq m] [Unique m]

lemma inv_unique_apply (M : Matrix m m 𝕜) (i j : m) : M⁻¹ i j = (M i j)⁻¹ := by
  rw [inv_subsingleton]
  obtain rfl := Subsingleton.elim i j
  simp [Ring.inverse_eq_inv]

lemma mul_inv_mul_apply {p : Type*} (X : Matrix p m 𝕜) (M : Matrix m m 𝕜) (Y : Matrix m p 𝕜)
    (i j : p) :
    (X * M⁻¹ * Y) i j = X i default * (M default default)⁻¹ * Y default j := by
  simp [mul_apply, inv_unique_apply]

omit [Fintype m] in
lemma posDef_of_unique {M : Matrix m m 𝕜} (h : 0 < M default default) : M.PosDef := by
  have hM : M = diagonal (fun _ => M default default) := by
    ext i j
    obtain rfl := Subsingleton.elim i j
    obtain rfl := Subsingleton.elim i default
    simp
  rw [hM]
  exact posDef_diagonal_iff.mpr (fun _ => h)

end Unique

/-! ### Hadamard's inequality for positive semidefinite matrices -/

theorem posSemidef_det_re_le_prod_diag_aux (k : ℕ) :
    ∀ {n : Type u} [Fintype n] [DecidableEq n], Fintype.card n = k →
      ∀ {G : Matrix n n 𝕜}, G.PosSemidef →
        RCLike.re G.det ≤ ∏ i, RCLike.re (G i i) := by
  induction k with
  | zero =>
    intro n _ _ hcard G _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard
    simp [det_isEmpty]
  | succ k ih =>
    intro n _ _ hcard G hG
    have hdiag : ∀ i, 0 ≤ RCLike.re (G i i) := fun i =>
      (RCLike.nonneg_iff.mp hG.diag_nonneg).1
    by_cases hGdet : G.det = 0
    · rw [hGdet, map_zero]; exact Finset.prod_nonneg (fun i _ => hdiag i)
    have hGpd : G.PosDef := hG.posDef_iff_det_ne_zero.mpr hGdet
    obtain ⟨i₀⟩ : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    set e := Equiv.sumCompl (fun i : n => i = i₀) with he
    set G' := G.submatrix e e with hG'def
    have hG' : G'.PosSemidef := hG.submatrix e
    have hdetG : G'.det = G.det := det_submatrix_equiv_self e G
    set G₁₁ := G'.toBlocks₁₁ with hG₁₁
    set G₁₂ := G'.toBlocks₁₂ with hG₁₂
    set G₂₁ := G'.toBlocks₂₁ with hG₂₁
    set G₂₂ := G'.toBlocks₂₂ with hG₂₂
    have hGblk : fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ = G' := fromBlocks_toBlocks G'
    have hG21 : G₂₁ = G₁₂ᴴ := by
      ext i j
      simp only [hG₂₁, hG₁₂, toBlocks₂₁, toBlocks₁₂, of_apply, conjTranspose_apply]
      exact (hG'.1.apply _ _).symm
    have hα : 0 < G₁₁ default default := hGpd.diag_pos
    have hαre : 0 < RCLike.re (G₁₁ default default) := (RCLike.pos_iff.mp hα).1
    have hαim : RCLike.im (G₁₁ default default) = 0 := (RCLike.pos_iff.mp hα).2
    have hG11pd : G₁₁.PosDef := posDef_of_unique hα
    haveI : Invertible G₁₁ :=
      invertibleOfIsUnitDet _ (by rw [det_unique]; exact isUnit_iff_ne_zero.mpr hα.ne')
    set S := G₂₂ - G₂₁ * G₁₁⁻¹ * G₁₂ with hS
    have hSpsd : S.PosSemidef := by
      have hblk : (fromBlocks G₁₁ G₁₂ G₁₂ᴴ G₂₂).PosSemidef := by
        rw [← hG21, hGblk]; exact hG'
      have := (PosDef.fromBlocks₁₁ G₁₂ G₂₂ hG11pd).mp hblk
      rwa [← hG21] at this
    have hG22psd : G₂₂.PosSemidef := hG'.submatrix Sum.inr
    have hdetG' : G'.det = G₁₁ default default * S.det := by
      rw [← hGblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique]
    -- the correction term is positive semidefinite
    have hP : (G₂₁ * G₁₁⁻¹ * G₁₂).PosSemidef := by
      have hrank : G₂₁ * G₁₁⁻¹ * G₁₂ = (G₁₁ default default)⁻¹ • (G₂₁ * G₂₁ᴴ) := by
        ext i j
        have : G₁₂ = G₂₁ᴴ := by rw [hG21, conjTranspose_conjTranspose]
        simp only [mul_inv_mul_apply, Matrix.smul_apply, mul_apply, Fintype.sum_unique, this,
          conjTranspose_apply, smul_eq_mul, inv_unique_apply]
        ring
      rw [hrank]
      exact (posSemidef_self_mul_conjTranspose G₂₁).smul (inv_nonneg.mpr hα.le)
    have hmono : RCLike.re S.det ≤ RCLike.re G₂₂.det := by
      have := det_re_le_det_re_add hSpsd hP
      rwa [hS, sub_add_cancel] at this
    have hcardU : Fintype.card {i : n // ¬ i = i₀} = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]; rfl
    have hih := ih hcardU hG22psd
    have hprod : ∏ i, RCLike.re (G i i) =
        RCLike.re (G₁₁ default default) * ∏ j, RCLike.re (G₂₂ j j) := by
      rw [← Fintype.prod_equiv e (fun i => RCLike.re (G' i i)) (fun i => RCLike.re (G i i))
        (fun _ => rfl), Fintype.prod_sum_type, Fintype.prod_unique]
      rfl
    obtain ⟨s, hs, hsdet⟩ := posSemidef_exists_det_eq_ofReal hSpsd
    have hre : RCLike.re G.det = RCLike.re (G₁₁ default default) * RCLike.re S.det := by
      rw [← hdetG, hdetG', hsdet, mul_comm, RCLike.re_ofReal_mul, RCLike.ofReal_re, mul_comm]
    rw [hre, hprod]
    calc RCLike.re (G₁₁ default default) * RCLike.re S.det
        ≤ RCLike.re (G₁₁ default default) * RCLike.re G₂₂.det :=
          mul_le_mul_of_nonneg_left hmono hαre.le
      _ ≤ RCLike.re (G₁₁ default default) * ∏ j, RCLike.re (G₂₂ j j) :=
          mul_le_mul_of_nonneg_left hih hαre.le

/-- **Hadamard's inequality, positive semidefinite form**: `re (det G) ≤ ∏ re (G i i)`. -/
theorem posSemidef_det_re_le_prod_diag {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n 𝕜} (hG : G.PosSemidef) :
    RCLike.re G.det ≤ ∏ i, RCLike.re (G i i) :=
  posSemidef_det_re_le_prod_diag_aux (Fintype.card n) rfl hG

/-- **Hadamard's inequality**: the squared modulus of the determinant is at most the product of
the squared Euclidean norms of the rows. -/
theorem norm_det_sq_le_prod_sum_norm_sq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕜) :
    ‖M.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hG : (M * Mᴴ).PosSemidef := posSemidef_self_mul_conjTranspose M
  have h := posSemidef_det_re_le_prod_diag hG
  have hdet : RCLike.re (M * Mᴴ).det = ‖M.det‖ ^ 2 := by
    rw [det_mul, det_conjTranspose, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  have hdiag : ∀ i, RCLike.re ((M * Mᴴ) i i) = ∑ j, ‖M i j‖ ^ 2 := by
    intro i
    simp only [mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.mul_conj, map_sum,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hdet] at h
  simpa [hdiag] using h

end Submission
