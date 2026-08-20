import Mathlib
import Submission.Helpers

open Matrix Finset
open scoped MatrixOrder Matrix

namespace Submission

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise description of a real positive semidefinite matrix coming from the spectral
theorem: `B i j = ∑ k, d k * (U i k * U j k)` with nonnegative `d`. -/
private lemma psd_entry_decomp {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    ∃ (d : n → ℝ) (U : Matrix n n ℝ), (∀ k, 0 ≤ d k) ∧
      ∀ i j, B i j = ∑ k, d k * (U i k * U j k) := by
  have hH : B.IsHermitian := hB.1
  refine ⟨hH.eigenvalues, hH.eigenvectorUnitary, fun k =>
    (hH.posSemidef_iff_eigenvalues_nonneg.mp hB) k, ?_⟩
  intro i j
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  conv_lhs => rw [hspec]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [Matrix.star_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    star_trivial, Unitary.coe_star]
  ring

/-- Schur product theorem over `ℝ`: the Hadamard (entrywise) product of positive semidefinite
matrices is positive semidefinite. -/
private lemma schur_product {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef := by
  obtain ⟨d, U, hd, hentry⟩ := psd_entry_decomp hB
  have hAsymm : ∀ i j, A j i = A i j := fun i j => by
    conv_lhs => rw [← hA.1]
    simp [conjTranspose_apply, star_trivial]
  have hBsymm : ∀ i j, B j i = B i j := fun i j => by
    conv_lhs => rw [← hB.1]
    simp [conjTranspose_apply, star_trivial]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, hadamard_apply, star_trivial]
    rw [hAsymm, hBsymm]
  · intro x
    have hsx : star x = x := by ext i; simp
    rw [hsx]
    have key : x ⬝ᵥ ((A ⊙ B) *ᵥ x) =
        ∑ k, d k * ((fun i => x i * U i k) ⬝ᵥ (A *ᵥ fun i => x i * U i k)) := by
      simp only [dotProduct, mulVec, hadamard_apply]
      calc ∑ i, x i * ∑ j, A i j * B i j * x j
          = ∑ i, ∑ j, ∑ k, d k * ((x i * U i k) * (A i j * (x j * U j k))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hentry i j, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = ∑ i, ∑ k, ∑ j, d k * ((x i * U i k) * (A i j * (x j * U j k))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ j, d k * ((x i * U i k) * (A i j * (x j * U j k))) :=
            Finset.sum_comm
        _ = ∑ k, d k * ((fun i => x i * U i k) ⬝ᵥ (A *ᵥ fun i => x i * U i k)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [dotProduct, mulVec, Finset.mul_sum]
    rw [key]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hd k) ?_
    have := hA.dotProduct_mulVec_nonneg (fun i => x i * U i k)
    simpa [star_trivial] using this

/-- Entrywise powers of a positive semidefinite real matrix are positive semidefinite. -/
private lemma hadamard_pow_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∀ k : ℕ, (Matrix.of fun i j => (A i j) ^ k).PosSemidef := by
  intro k
  induction k with
  | zero =>
    have hones : (Matrix.of fun i j : n => ((A i j) ^ 0 : ℝ)) =
        vecMulVec (fun _ => 1) (star fun _ => (1 : ℝ)) := by
      ext i j
      simp [vecMulVec_apply]
    rw [hones]
    exact posSemidef_vecMulVec_self_star _
  | succ k ih =>
    have hstep : (Matrix.of fun i j : n => ((A i j) ^ (k + 1) : ℝ)) =
        A ⊙ (Matrix.of fun i j => (A i j) ^ k) := by
      ext i j
      simp [hadamard_apply]
      ring
    rw [hstep]
    exact schur_product hA ih

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  have hAsymm : ∀ i j, A j i = A i j := fun i j => by
    conv_lhs => rw [← hA.1]
    simp [conjTranspose_apply, star_trivial]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, map_apply, star_trivial]
    rw [hAsymm]
  · intro x
    have hsx : star x = x := by ext i; simp
    rw [hsx]
    set f : ℕ → ℝ := fun N =>
      ∑ i, x i * ∑ j, (∑ k ∈ Finset.range N, (A i j) ^ k / k.factorial) * x j with hf
    have hf_nonneg : ∀ N, 0 ≤ f N := by
      intro N
      have hswap : f N = ∑ k ∈ Finset.range N,
          (1 / (k.factorial : ℝ)) *
            (x ⬝ᵥ ((Matrix.of fun i j => (A i j) ^ k) *ᵥ x)) := by
        simp only [hf]
        calc ∑ i, x i * ∑ j, (∑ k ∈ Finset.range N, (A i j) ^ k / k.factorial) * x j
            = ∑ i, ∑ j, ∑ k ∈ Finset.range N,
                (1 / (k.factorial : ℝ)) * (x i * ((A i j) ^ k * x j)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              field_simp
          _ = ∑ i, ∑ k ∈ Finset.range N, ∑ j,
                (1 / (k.factorial : ℝ)) * (x i * ((A i j) ^ k * x j)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact Finset.sum_comm
          _ = ∑ k ∈ Finset.range N, ∑ i, ∑ j,
                (1 / (k.factorial : ℝ)) * (x i * ((A i j) ^ k * x j)) :=
              Finset.sum_comm
          _ = ∑ k ∈ Finset.range N, (1 / (k.factorial : ℝ)) *
                (x ⬝ᵥ ((Matrix.of fun i j => (A i j) ^ k) *ᵥ x)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
      rw [hswap]
      refine Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) ?_
      have := (hadamard_pow_posSemidef hA k).dotProduct_mulVec_nonneg x
      simpa [star_trivial] using this
    have hlim : Filter.Tendsto f Filter.atTop
        (nhds (x ⬝ᵥ ((A.map Real.exp) *ᵥ x))) := by
      have hterm : ∀ i j : n, Filter.Tendsto
          (fun N => ∑ k ∈ Finset.range N, (A i j) ^ k / k.factorial)
          Filter.atTop (nhds (Real.exp (A i j))) := by
        intro i j
        have h := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
        rw [Real.exp_eq_exp_ℝ]
        exact h
      have hmain : Filter.Tendsto (fun N => ∑ i, x i * ∑ j,
          (∑ k ∈ Finset.range N, (A i j) ^ k / k.factorial) * x j)
          Filter.atTop (nhds (∑ i, x i * ∑ j, Real.exp (A i j) * x j)) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        refine Filter.Tendsto.const_mul _ ?_
        refine tendsto_finsetSum _ fun j _ => ?_
        exact (hterm i j).mul_const _
      have heq : (x ⬝ᵥ ((A.map Real.exp) *ᵥ x)) =
          ∑ i, x i * ∑ j, Real.exp (A i j) * x j := by
        simp [dotProduct, mulVec, map_apply]
      rw [heq]
      exact hmain
    exact ge_of_tendsto' hlim hf_nonneg

end Submission
