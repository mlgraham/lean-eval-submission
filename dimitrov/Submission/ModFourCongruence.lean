import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Submission.SymmetricIntegrality

/-!
# The Arnold–Smyth congruence `P₄ ≡ P₂ (mod 4)`

For `x : σ → S` whose elementary symmetric functions are integers, the elementary symmetric
functions of the fourth powers `x⁴` and of the squares `x²` are integers that agree modulo `4`
(Dimitrov, Lemma 2.1, after Arnold and Smyth). Two ingredients:

* **Power sums.** Newton's identities give, for integers `e₁, …, e₄`,
  `s₂ = e₁² − 2e₂` and `s₄ = e₁⁴ − 4e₁²e₂ + 2e₂² + 4e₁e₃ − 4e₄`, so `s₄ ≡ s₂ (mod 4)` because
  `e₁⁴ ≡ e₁²` and `2e₂² ≡ −2e₂ (mod 4)` for integers.
* **Symmetric powers.** `eₖ(x⁴) = s₄(y)` and `eₖ(x²) = s₂(y)` where `y` runs over the products
  `∏ᵢ∈ₜ xᵢ` for `k`-subsets `t`; the elementary symmetric functions of `y` are symmetric in `x`,
  hence integers.
-/

open MvPolynomial Finset

namespace Submission

section PowerSums

variable {τ S : Type*} [Fintype τ] [CommRing S]

/-- Integer arithmetic: `e₁⁴ − e₁² ≡ 0 (mod 4)`. -/
lemma four_dvd_pow_four_sub_sq (e : ℤ) : (4 : ℤ) ∣ e ^ 4 - e ^ 2 := by
  rcases Int.even_or_odd' e with ⟨a, rfl | rfl⟩
  · exact ⟨4 * a ^ 4 - a ^ 2, by ring⟩
  · exact ⟨(2 * a + 1) ^ 2 * (a ^ 2 + a), by ring⟩

/-- Integer arithmetic: `2e₂² + 2e₂ ≡ 0 (mod 4)`. -/
lemma four_dvd_two_mul_sq_add_two_mul (e : ℤ) : (4 : ℤ) ∣ 2 * e ^ 2 + 2 * e := by
  rcases Int.even_or_odd' e with ⟨b, rfl | rfl⟩
  · exact ⟨2 * b ^ 2 + b, by ring⟩
  · exact ⟨2 * b ^ 2 + 3 * b + 1, by ring⟩

/-- Newton's identities, unfolded for `k ≤ 4`, evaluated at `y`. -/
lemma aeval_psum_four_two (y : τ → S) :
    aeval y (psum τ ℤ 2) = aeval y (esymm τ ℤ 1) ^ 2 - 2 * aeval y (esymm τ ℤ 2) ∧
    aeval y (psum τ ℤ 4) = aeval y (esymm τ ℤ 1) ^ 4
      - 4 * aeval y (esymm τ ℤ 1) ^ 2 * aeval y (esymm τ ℤ 2)
      + 2 * aeval y (esymm τ ℤ 2) ^ 2
      + 4 * aeval y (esymm τ ℤ 1) * aeval y (esymm τ ℤ 3)
      - 4 * aeval y (esymm τ ℤ 4) := by
  classical
  have h1 : (∑ i, y i) = aeval y (esymm τ ℤ 1) := by
    rw [esymm_one]; simp
  have h2 := congrArg (aeval y) (psum_eq_mul_esymm_sub_sum τ ℤ 2 (by norm_num))
  have h3 := congrArg (aeval y) (psum_eq_mul_esymm_sub_sum τ ℤ 3 (by norm_num))
  have h4 := congrArg (aeval y) (psum_eq_mul_esymm_sub_sum τ ℤ 4 (by norm_num))
  have s2 : ({a ∈ antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} : Finset (ℕ × ℕ)) = {(1, 1)} := by decide
  have s3 : ({a ∈ antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} : Finset (ℕ × ℕ)) =
      {(1, 2), (2, 1)} := by decide
  have s4 : ({a ∈ antidiagonal 4 | a.1 ∈ Set.Ioo 0 4} : Finset (ℕ × ℕ)) =
      {(1, 3), (2, 2), (3, 1)} := by decide
  rw [s2] at h2
  rw [s3] at h3
  rw [s4] at h4
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert, Finset.mem_singleton,
    Finset.mem_insert, Prod.mk.injEq] at h2 h3 h4
  simp only [Nat.cast_ofNat, Nat.cast_one, sub_zero] at h2 h3 h4
  norm_num at h2 h3 h4
  constructor
  · rw [h2, h1]; ring
  · rw [h4, h3, h2, h1]; ring

/-- **Power-sum congruence.** If the elementary symmetric functions of `y` are integers, then
`s₄(y)` and `s₂(y)` are integers congruent modulo `4`. -/
theorem exists_int_psum_four_two (y : τ → S)
    (hy : ∀ k, aeval y (esymm τ ℤ k) ∈ Set.range (algebraMap ℤ S)) :
    ∃ A B : ℤ, (A : S) = aeval y (psum τ ℤ 4) ∧ (B : S) = aeval y (psum τ ℤ 2) ∧
      (4 : ℤ) ∣ A - B := by
  obtain ⟨e1, he1⟩ := hy 1
  obtain ⟨e2, he2⟩ := hy 2
  obtain ⟨e3, he3⟩ := hy 3
  obtain ⟨e4, he4⟩ := hy 4
  obtain ⟨hs2, hs4⟩ := aeval_psum_four_two y
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at he1 he2 he3 he4
  refine ⟨e1 ^ 4 - 4 * e1 ^ 2 * e2 + 2 * e2 ^ 2 + 4 * e1 * e3 - 4 * e4, e1 ^ 2 - 2 * e2, ?_, ?_, ?_⟩
  · rw [hs4, ← he1, ← he2, ← he3, ← he4]; push_cast; ring
  · rw [hs2, ← he1, ← he2]; push_cast; ring
  · have h := dvd_add (four_dvd_pow_four_sub_sq e1) (four_dvd_two_mul_sq_add_two_mul e2)
    have h' := dvd_sub h (dvd_mul_right (4 : ℤ) (e1 ^ 2 * e2 - e1 * e3 + e4))
    have heq : e1 ^ 4 - 4 * e1 ^ 2 * e2 + 2 * e2 ^ 2 + 4 * e1 * e3 - 4 * e4 - (e1 ^ 2 - 2 * e2) =
        e1 ^ 4 - e1 ^ 2 + (2 * e2 ^ 2 + 2 * e2) - 4 * (e1 ^ 2 * e2 - e1 * e3 + e4) := by ring
    rw [heq]; exact h'

end PowerSums

section SymmetricPowers

variable {σ S : Type*} [Fintype σ] [CommRing S]

/-- The `k`-subsets of `σ`. -/
abbrev KSubsets (σ : Type*) (k : ℕ) := {s : Finset σ // s.card = k}

/-- The permutation of `k`-subsets induced by a permutation of `σ`. -/
def kSubsetsPerm (k : ℕ) (e : Equiv.Perm σ) : Equiv.Perm (KSubsets σ k) :=
  Equiv.subtypeEquiv e.finsetCongr (fun s => by simp)

/-- The product monomial `∏ᵢ∈ₜ Xᵢ` attached to a `k`-subset `t`. -/
noncomputable def subsetProd (k : ℕ) (t : KSubsets σ k) : MvPolynomial σ ℤ := ∏ i ∈ t.1, X i

lemma rename_subsetProd (k : ℕ) (e : Equiv.Perm σ) (t : KSubsets σ k) :
    rename e (subsetProd k t) = subsetProd k (kSubsetsPerm k e t) := by
  simp only [subsetProd, map_prod, rename_X, kSubsetsPerm, Equiv.subtypeEquiv_apply,
    Equiv.finsetCongr_apply]
  rw [Finset.prod_map]
  rfl

/-- A symmetric polynomial in the subset products is symmetric in `σ`. -/
lemma isSymmetric_aeval_subsetProd (k : ℕ) {p : MvPolynomial (KSubsets σ k) ℤ}
    (hp : p.IsSymmetric) : (aeval (subsetProd k) p).IsSymmetric := by
  intro e
  rw [← AlgHom.comp_apply, comp_aeval]
  simp only [rename_subsetProd]
  have : (fun t => subsetProd k (kSubsetsPerm k e t)) = subsetProd k ∘ (kSubsetsPerm k e) := rfl
  rw [this, ← aeval_rename, hp]

/-- `eₖ(xᵐ) = sₘ(y)` for `y` the subset products of `x`. -/
lemma aeval_esymm_pow_eq_aeval_psum (x : σ → S) (k m : ℕ) :
    aeval (fun i => x i ^ m) (esymm σ ℤ k) =
      aeval (fun t : KSubsets σ k => ∏ i ∈ t.1, x i) (psum (KSubsets σ k) ℤ m) := by
  rw [esymm_eq_sum_subtype, psum]
  simp only [map_sum, map_prod, map_pow, aeval_X, Finset.prod_pow]

/-- **Arnold–Smyth congruence, symmetric-function form.** If the elementary symmetric functions
of `x` are integers, then `eₖ(x⁴)` and `eₖ(x²)` are integers congruent modulo `4`. -/
theorem exists_int_esymm_pow_four_two (x : σ → S)
    (hx : ∀ k, aeval x (esymm σ ℤ k) ∈ Set.range (algebraMap ℤ S)) (k : ℕ) :
    ∃ A B : ℤ, (A : S) = aeval (fun i => x i ^ 4) (esymm σ ℤ k) ∧
      (B : S) = aeval (fun i => x i ^ 2) (esymm σ ℤ k) ∧ (4 : ℤ) ∣ A - B := by
  classical
  set y : KSubsets σ k → S := fun t => ∏ i ∈ t.1, x i with hy_def
  have hy : ∀ j, aeval y (esymm (KSubsets σ k) ℤ j) ∈ Set.range (algebraMap ℤ S) := by
    intro j
    have h := aeval_mem_range_of_isSymmetric x hx
      (isSymmetric_aeval_subsetProd k (esymm_isSymmetric (KSubsets σ k) ℤ j))
    rw [← AlgHom.comp_apply, comp_aeval] at h
    have hfun : (fun t => aeval x (subsetProd k t)) = y := by
      funext t
      simp [hy_def, subsetProd, map_prod, aeval_X]
    rw [hfun] at h
    exact h
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_int_psum_four_two y hy
  exact ⟨A, B, by rw [hA, aeval_esymm_pow_eq_aeval_psum], by rw [hB, aeval_esymm_pow_eq_aeval_psum],
    hAB⟩

end SymmetricPowers

section Polynomials

open Polynomial

variable {σ S : Type*} [Fintype σ] [CommRing S] [Nontrivial S] [CharZero S]

/-- Coefficients of `∏ᵢ (X − C (x i ^ m))` are `(−1)^(n−j) · e_{n−j}(xᵐ)`. -/
lemma coeff_prod_X_sub_C_pow (x : σ → S) (m j : ℕ) (hj : j ≤ Fintype.card σ) :
    (∏ i, (Polynomial.X - Polynomial.C (x i ^ m))).coeff j =
      (-1) ^ (Fintype.card σ - j) * aeval (fun i => x i ^ m) (esymm σ ℤ (Fintype.card σ - j)) := by
  classical
  have hcard : Multiset.card (Finset.univ.val.map fun i => x i ^ m) = Fintype.card σ := by simp
  have hmm : Multiset.map (fun i => Polynomial.X - Polynomial.C (x i ^ m)) Finset.univ.val =
      (Finset.univ.val.map fun i => x i ^ m).map (fun t => Polynomial.X - Polynomial.C t) := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, hmm, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; omega),
    hcard, ← aeval_esymm_eq_multiset_esymm (σ := σ) (R := ℤ)]

/-- **Arnold–Smyth congruence, polynomial form.** If the elementary symmetric functions of `x`
are integers, then the integer polynomials `P₂`, `P₄` with roots `x²`, `x⁴` satisfy
`P₄ ≡ P₂ (mod 4)` coefficientwise. -/
theorem exists_int_polys_pow_four_two_congr (x : σ → S)
    (hx : ∀ k, aeval x (esymm σ ℤ k) ∈ Set.range (algebraMap ℤ S)) :
    ∃ P₂ P₄ : ℤ[X],
      P₂.map (Int.castRingHom S) = ∏ i, (Polynomial.X - Polynomial.C (x i ^ 2)) ∧
      P₄.map (Int.castRingHom S) = ∏ i, (Polynomial.X - Polynomial.C (x i ^ 4)) ∧
      ∀ j, (4 : ℤ) ∣ P₄.coeff j - P₂.coeff j := by
  classical
  obtain ⟨P₂, hP₂⟩ := exists_map_eq_prod_X_sub_C_pow x hx 2
  obtain ⟨P₄, hP₄⟩ := exists_map_eq_prod_X_sub_C_pow x hx 4
  refine ⟨P₂, P₄, hP₂, hP₄, fun j => ?_⟩
  set n := Fintype.card σ with hn
  have hc₂ := congrArg (fun q => Polynomial.coeff q j) hP₂
  have hc₄ := congrArg (fun q => Polynomial.coeff q j) hP₄
  simp only [Polynomial.coeff_map, algebraMap_int_eq, Int.coe_castRingHom] at hc₂ hc₄
  by_cases hj : j ≤ n
  · obtain ⟨A, B, hA, hB, hAB⟩ := exists_int_esymm_pow_four_two x hx (n - j)
    rw [coeff_prod_X_sub_C_pow x 4 j hj, ← hA] at hc₄
    rw [coeff_prod_X_sub_C_pow x 2 j hj, ← hB] at hc₂
    have h₄ : P₄.coeff j = (-1) ^ (n - j) * A := by
      apply Int.cast_injective (α := S); push_cast; exact hc₄
    have h₂ : P₂.coeff j = (-1) ^ (n - j) * B := by
      apply Int.cast_injective (α := S); push_cast; exact hc₂
    rw [h₄, h₂, ← mul_sub]
    exact Dvd.dvd.mul_left hAB _
  · have hdeg : ∀ m, (∏ i, (Polynomial.X - Polynomial.C (x i ^ m))).coeff j = 0 := by
      intro m
      have hcard : Multiset.card (Finset.univ.val.map fun i => x i ^ m) = n := by simp [hn]
      have hmm : Multiset.map (fun i => Polynomial.X - Polynomial.C (x i ^ m)) Finset.univ.val =
          (Finset.univ.val.map fun i => x i ^ m).map (fun t => Polynomial.X - Polynomial.C t) := by
        rw [Multiset.map_map]; rfl
      rw [Finset.prod_eq_multiset_prod, hmm, Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
      omega
    rw [hdeg] at hc₂ hc₄
    have h₄ : P₄.coeff j = 0 := by exact_mod_cast hc₄
    have h₂ : P₂.coeff j = 0 := by exact_mod_cast hc₂
    rw [h₄, h₂, sub_zero]
    exact dvd_zero _

end Polynomials

end Submission
