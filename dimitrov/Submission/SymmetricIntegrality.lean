import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Symmetric functions of the roots of a polynomial over the base ring

If `x : σ → S` (say the roots of a polynomial in a splitting field `S` of an `R`-polynomial) has
all its elementary symmetric functions in the image of `R`, then every *symmetric* polynomial
expression in `x` lies in the image of `R` (fundamental theorem of symmetric polynomials).

Consequences used for Dimitrov's proof of Schinzel–Zassenhaus:
* if `P.map (algebraMap R S) = ∏ᵢ (X − C (x i))` then the elementary symmetric functions of `x`
  lie in `R`;
* hence for every `m` the polynomial `∏ᵢ (X − C (x i ^ m))` is the image of a polynomial over `R`
  (the polynomial "`P_m`" whose roots are the `m`-th powers of the roots of `P`).
-/

open MvPolynomial Polynomial

namespace Submission

variable {σ R S : Type*} [Fintype σ] [CommRing R] [CommRing S] [Algebra R S]

/-- If the elementary symmetric functions of `x` lie in (the image of) `R`, so does every
symmetric polynomial expression in `x`. -/
theorem aeval_mem_range_of_isSymmetric (x : σ → S)
    (hx : ∀ k, aeval x (esymm σ R k) ∈ Set.range (algebraMap R S))
    {p : MvPolynomial σ R} (hp : p.IsSymmetric) :
    aeval x p ∈ Set.range (algebraMap R S) := by
  classical
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective (σ := σ) R (n := Fintype.card σ) le_rfl ⟨p, hp⟩
  have hpq : p = aeval (fun i : Fin (Fintype.card σ) => esymm σ R (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  choose y hy using fun i : Fin (Fintype.card σ) => hx (i + 1)
  rw [hpq, ← AlgHom.comp_apply, comp_aeval]
  have hfun : (fun i : Fin (Fintype.card σ) => aeval x (esymm σ R (i + 1))) =
      fun i => algebraMap R S (y i) := by
    funext i; exact (hy i).symm
  rw [hfun]
  refine ⟨aeval y q, ?_⟩
  rw [map_aeval]
  simp [aeval_eq_eval₂Hom]

/-- Substituting `Xᵢ ↦ Xᵢ ^ m` preserves symmetry. -/
theorem IsSymmetric.aeval_X_pow {p : MvPolynomial σ R} (hp : p.IsSymmetric) (m : ℕ) :
    (aeval (fun i => X i ^ m : σ → MvPolynomial σ R) p).IsSymmetric := by
  intro e
  rw [← AlgHom.comp_apply, comp_aeval]
  simp only [map_pow, rename_X]
  have : (fun i : σ => (X (e i) : MvPolynomial σ R) ^ m) =
      (fun i => X i ^ m) ∘ e := rfl
  rw [this, ← aeval_rename, hp e]

/-- The elementary symmetric functions of the `m`-th powers of `x` are symmetric in `x`. -/
theorem aeval_esymm_pow_mem_range (x : σ → S)
    (hx : ∀ k, aeval x (esymm σ R k) ∈ Set.range (algebraMap R S)) (m k : ℕ) :
    aeval (fun i => x i ^ m) (esymm σ R k) ∈ Set.range (algebraMap R S) := by
  have h := aeval_mem_range_of_isSymmetric x hx (IsSymmetric.aeval_X_pow (esymm_isSymmetric σ R k) m)
  rw [← AlgHom.comp_apply, comp_aeval] at h
  simpa [MvPolynomial.aeval_X] using h

/-- If `P` maps to `∏ᵢ (X − C (x i))`, the elementary symmetric functions of `x` lie in `R`. -/
theorem aeval_esymm_mem_range_of_map_eq_prod (x : σ → S) (P : R[X])
    (hP : P.map (algebraMap R S) = ∏ i, (Polynomial.X - Polynomial.C (x i))) (k : ℕ) :
    aeval x (esymm σ R k) ∈ Set.range (algebraMap R S) := by
  classical
  set n := Fintype.card σ with hn
  have hcard : Multiset.card (Finset.univ.val.map x) = n := by simp [hn]
  by_cases hk : k ≤ n
  · have hcoeff := congrArg (fun q => Polynomial.coeff q (n - k)) hP
    simp only [Polynomial.coeff_map] at hcoeff
    have hmm : Multiset.map (fun i => Polynomial.X - Polynomial.C (x i)) Finset.univ.val =
        (Finset.univ.val.map x).map (fun t => Polynomial.X - Polynomial.C t) := by
      rw [Multiset.map_map]; rfl
    rw [Finset.prod_eq_multiset_prod, hmm,
      Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; omega), hcard,
      show n - (n - k) = k by omega, ← aeval_esymm_eq_multiset_esymm (σ := σ) (R := R)] at hcoeff
    refine ⟨(-1) ^ k * P.coeff (n - k), ?_⟩
    rw [map_mul, map_pow, map_neg, map_one, hcoeff, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul]
    simp
  · refine ⟨0, ?_⟩
    rw [map_zero, aeval_esymm_eq_multiset_esymm, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]
    simp

/-- **Integrality of `P_m`.** If the elementary symmetric functions of `x` lie in `R`, then
`∏ᵢ (X − C (x i ^ m))` is the image of a polynomial over `R`. -/
theorem exists_map_eq_prod_X_sub_C_pow [Nontrivial S] (x : σ → S)
    (hx : ∀ k, aeval x (esymm σ R k) ∈ Set.range (algebraMap R S)) (m : ℕ) :
    ∃ Q : R[X], Q.map (algebraMap R S) = ∏ i, (Polynomial.X - Polynomial.C (x i ^ m)) := by
  classical
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro j
  set n := Fintype.card σ with hn
  have hcard : Multiset.card (Finset.univ.val.map fun i => x i ^ m) = n := by simp [hn]
  have hmm : Multiset.map (fun i => Polynomial.X - Polynomial.C (x i ^ m)) Finset.univ.val =
      (Finset.univ.val.map fun i => x i ^ m).map (fun t => Polynomial.X - Polynomial.C t) := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, hmm]
  by_cases hj : j ≤ n
  · rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; omega), hcard,
      ← aeval_esymm_eq_multiset_esymm (σ := σ) (R := R)]
    obtain ⟨r, hr⟩ := aeval_esymm_pow_mem_range x hx m (n - j)
    exact ⟨(-1) ^ (n - j) * r, by rw [map_mul, map_pow, map_neg, map_one, hr]⟩
  · refine ⟨0, ?_⟩
    rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
    omega

end Submission
