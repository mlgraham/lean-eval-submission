import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The squaring lemma (Dimitrov, Lemma 2.3)

* If a finite multiset `M` of nonzero elements of a field is stable under squaring
  (`M.map (·^2) = M`), then every element of `M` is a root of unity: squaring is a surjective
  self-map of the finite set of elements, hence a permutation of finite order `k`, and
  `β^(2^k) = β`.
* If `P` is irreducible and `P * R = Q²` with `R` monic of the same degree as `P`, then `R = P`.
* Consequently, if the polynomial with roots `xᵢ⁴` equals the one with roots `xᵢ²`, all the
  (nonzero) `xᵢ` are roots of unity.

No Galois theory is used (Dimitrov's proof iterates a Galois automorphism; here the permutation
of the finite root set does the same job).
-/

open Polynomial

namespace Submission

section Squaring

variable {F : Type*} [Field F]

/-- **Squaring lemma.** A finite multiset of nonzero elements stable under squaring consists of
roots of unity. -/
theorem isOfFinOrder_of_multiset_map_sq_eq {M : Multiset F}
    (hM : M.map (fun z => z ^ 2) = M) {β : F} (hβ : β ∈ M) (h0 : β ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ β ^ k = 1 := by
  classical
  set S := M.toFinset with hS
  -- squaring maps `S` to itself
  have hmaps : ∀ z ∈ S, z ^ 2 ∈ S := by
    intro z hz
    rw [hS, Multiset.mem_toFinset] at hz ⊢
    rw [← hM]
    exact Multiset.mem_map_of_mem _ hz
  set f : S → S := fun z => ⟨z.1 ^ 2, hmaps z.1 z.2⟩ with hf
  -- and surjectively
  have hsurj : Function.Surjective f := by
    intro ⟨γ, hγ⟩
    rw [hS, Multiset.mem_toFinset, ← hM, Multiset.mem_map] at hγ
    obtain ⟨z, hz, hzγ⟩ := hγ
    exact ⟨⟨z, by rw [hS, Multiset.mem_toFinset]; exact hz⟩, Subtype.ext hzγ⟩
  have hbij : Function.Bijective f := Finite.surjective_iff_bijective.mp hsurj
  set π : Equiv.Perm S := Equiv.ofBijective f hbij with hπ
  obtain ⟨k, hk, hπk⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite π)
  -- `π ^ k` raises to the power `2 ^ k`
  have hpow : ∀ (j : ℕ) (z : S), ((π ^ j) z).1 = z.1 ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ j ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hπ, Equiv.ofBijective_apply, hf]
      simp only
      rw [← pow_mul, pow_succ, mul_comm]
  have hβS : β ∈ S := by rw [hS, Multiset.mem_toFinset]; exact hβ
  have h1 := hpow k ⟨β, hβS⟩
  rw [hπk, Equiv.Perm.one_apply] at h1
  -- `β ^ (2 ^ k) = β` with `β ≠ 0`
  refine ⟨2 ^ k - 1, ?_, ?_⟩
  · have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · have h2 : β ^ (2 ^ k - 1) * β = β := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), ← h1]
    exact mul_right_cancel₀ h0 (by rw [h2, one_mul])

/-- If `P` is irreducible, `R` is monic of the same degree, and `P * R` is a square, then
`R = P`. -/
theorem eq_of_irreducible_of_mul_eq_sq {P R Q : F[X]} (hP : Irreducible P) (hPm : P.Monic)
    (hRm : R.Monic) (hdeg : R.natDegree = P.natDegree) (h : P * R = Q ^ 2) : R = P := by
  have hprime : Prime P := hP.prime
  have hPQ : P ∣ Q := hprime.dvd_of_dvd_pow (h ▸ dvd_mul_right P R)
  obtain ⟨T, hT⟩ := hPQ
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hR : R = P * T ^ 2 := by
    have : P * R = P * (P * T ^ 2) := by rw [h, hT]; ring
    exact mul_left_cancel₀ hP0 this
  have hdvd : P ∣ R := ⟨T ^ 2, hR⟩
  exact eq_of_monic_of_dvd_of_natDegree_le hPm hRm hdvd hdeg.le

/-- If the polynomial with roots `xᵢ⁴` equals the polynomial with roots `xᵢ²`, every nonzero
`xᵢ` is a root of unity. -/
theorem isOfFinOrder_of_prod_X_sub_C_pow_four_eq_two {σ : Type*} [Fintype σ] (x : σ → F)
    (h : ∏ i, (X - C (x i ^ 4)) = ∏ i, (X - C (x i ^ 2))) (i : σ) (hi : x i ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ x i ^ k = 1 := by
  classical
  set M : Multiset F := Finset.univ.val.map fun i => x i ^ 2 with hMdef
  have hmm : ∀ m, ∏ i, (X - C (x i ^ m)) =
      ((Finset.univ.val.map fun i => x i ^ m).map fun a => X - C a).prod := by
    intro m
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hroots := congrArg Polynomial.roots h
  rw [hmm 4, hmm 2, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hroots
  have hM : M.map (fun z => z ^ 2) = M := by
    rw [hMdef, Multiset.map_map, ← hroots]
    congr 1
    funext j
    simp only [Function.comp]
    ring
  have hβ : x i ^ 2 ∈ M := Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  obtain ⟨k, hk, hk'⟩ := isOfFinOrder_of_multiset_map_sq_eq hM hβ (pow_ne_zero 2 hi)
  exact ⟨2 * k, by omega, by rw [pow_mul, hk']⟩

end Squaring

end Submission
