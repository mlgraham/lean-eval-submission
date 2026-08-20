import Mathlib
import Submission.Helpers

open Polynomial Module

namespace Submission

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  haveI hnz : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI hnzq : NeZero ((Monoid.exponent G : ℕ) : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  haveI hcyc : IsCyclotomicExtension {Monoid.exponent G} ℚ
      (CyclotomicField (Monoid.exponent G) ℚ) :=
    CyclotomicField.isCyclotomicExtension (Monoid.exponent G) ℚ
  have halg : Algebra.IsAlgebraic ℚ (CyclotomicField (Monoid.exponent G) ℚ) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  let φa : CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨φa.toRingHom, ?_⟩
  intro V _ _ _ ρ g
  have hζ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta (Monoid.exponent G) ℚ
        (CyclotomicField (Monoid.exponent G) ℚ)) (Monoid.exponent G) :=
    IsCyclotomicExtension.zeta_spec _ ℚ _
  have hinj : Function.Injective φa.toRingHom := φa.toRingHom.injective
  have hζC : IsPrimitiveRoot
      (φa.toRingHom (IsCyclotomicExtension.zeta (Monoid.exponent G) ℚ _))
      (Monoid.exponent G) := hζ.map_of_injective hinj
  set f : Module.End ℂ V := ρ g with hfdef
  have hfn : f ^ (Monoid.exponent G) = 1 := by
    rw [hfdef, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  let b := Module.finBasis ℂ V
  set A := LinearMap.toMatrix b b f with hAdef
  have htr : LinearMap.trace ℂ V f = A.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  have hsum : A.trace = A.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly A
  have hroot_mem : ∀ μ ∈ A.charpoly.roots, μ ∈ φa.toRingHom.range := by
    intro μ hμ
    have hisroot : IsRoot A.charpoly μ := (Polynomial.mem_roots'.mp hμ).2
    have hchar : A.charpoly = f.charpoly := f.charpoly_toMatrix b
    have hev : f.HasEigenvalue μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← hchar]
      exact hisroot
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hpow := hv.pow_apply (Monoid.exponent G)
    rw [hfn] at hpow
    have hv1 : v = μ ^ (Monoid.exponent G) • v := by simpa using hpow
    have hμn : μ ^ (Monoid.exponent G) = 1 := by
      by_contra hne
      have h0 : (μ ^ (Monoid.exponent G) - 1) • v = 0 := by
        rw [sub_smul, one_smul, ← hv1, sub_self]
      rcases smul_eq_zero.mp h0 with h | h
      · exact hne (sub_eq_zero.mp h)
      · exact hv.2 h
    obtain ⟨i, _, hipow⟩ := hζC.eq_pow_of_pow_eq_one hμn
    exact ⟨(IsCyclotomicExtension.zeta (Monoid.exponent G) ℚ _) ^ i, by rw [map_pow, hipow]⟩
  rw [htr, hsum]
  exact multiset_sum_mem _ hroot_mem

end Submission
