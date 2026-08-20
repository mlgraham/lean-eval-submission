import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod
import Submission.Helpers

open scoped Real
open Set Real

namespace Submission

/-- Uniqueness for the second-order linear ODE `u'' = -lam * u` on `[0, π]`, proved by
passing to the first-order system `(u, u')' = L (u, u')` in `ℝ × ℝ` and applying Grönwall's
trajectory estimate with the (globally Lipschitz) continuous linear vector field `L`. -/
private lemma ode2_unique (lam : ℝ) (u v u' v' : ℝ → ℝ)
    (hu : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt u' (-(lam * u t)) t)
    (hv : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt v (v' t) t)
    (hv' : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt v' (-(lam * v t)) t)
    (h0 : u 0 = v 0) (h0' : u' 0 = v' 0) :
    ∀ t ∈ Icc (0:ℝ) π, u t = v t := by
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((-lam) • ContinuousLinearMap.fst ℝ ℝ ℝ) with hLdef
  have hLapp : ∀ p : ℝ × ℝ, L p = (p.2, -(lam * p.1)) := by
    intro p
    simp [hLdef, neg_mul]
  have hlip : ∀ t : ℝ, LipschitzWith ‖L‖₊ (fun p : ℝ × ℝ => L p) := fun _ => L.lipschitz
  have hF : ∀ t ∈ Ico (0:ℝ) π, HasDerivWithinAt (fun t => (u t, u' t))
      (L (u t, u' t)) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => (u t, u' t)) (u' t, -(lam * u t)) t :=
      (hu t (Ico_subset_Icc_self ht)).prodMk (hu' t (Ico_subset_Icc_self ht))
    rw [hLapp]
    exact h1.hasDerivWithinAt
  have hG : ∀ t ∈ Ico (0:ℝ) π, HasDerivWithinAt (fun t => (v t, v' t))
      (L (v t, v' t)) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => (v t, v' t)) (v' t, -(lam * v t)) t :=
      (hv t (Ico_subset_Icc_self ht)).prodMk (hv' t (Ico_subset_Icc_self ht))
    rw [hLapp]
    exact h1.hasDerivWithinAt
  have hcontF : ContinuousOn (fun t => (u t, u' t)) (Icc 0 π) := fun t ht =>
    (((hu t ht).prodMk (hu' t ht)).continuousAt).continuousWithinAt
  have hcontG : ContinuousOn (fun t => (v t, v' t)) (Icc 0 π) := fun t ht =>
    (((hv t ht).prodMk (hv' t ht)).continuousAt).continuousWithinAt
  have hinit : dist ((fun t => (u t, u' t)) 0) ((fun t => (v t, v' t)) 0) ≤ 0 := by
    simp [h0, h0']
  have hkey := dist_le_of_trajectories_ODE (v := fun _ p => L p)
    hlip hcontF hF hcontG hG hinit
  intro t ht
  have h2 := hkey t ht
  rw [zero_mul] at h2
  have h3 : (u t, u' t) = (v t, v' t) :=
    dist_eq_zero.mp (le_antisymm h2 dist_nonneg)
  exact congrArg Prod.fst h3

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · rintro ⟨y, J, _hJopen, hJsub, hy, hy', h0, hπ, x₀, hx₀, hyx₀⟩
    have hyI : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt y (deriv y t) t :=
      fun t ht => hy t (hJsub ht)
    have hyI' : ∀ t ∈ Icc (0:ℝ) π, HasDerivAt (deriv y) (-(lam * y t)) t :=
      fun t ht => hy' t (hJsub ht)
    have hπmem : π ∈ Icc (0:ℝ) π := right_mem_Icc.mpr pi_pos.le
    have hzero_case : deriv y 0 ≠ 0 := by
      intro hz
      have hzero := ode2_unique lam y (fun _ => 0) (deriv y) (fun _ => 0)
        hyI hyI'
        (fun t _ => hasDerivAt_const t (0:ℝ))
        (fun t _ => by simpa using hasDerivAt_const t (0:ℝ))
        (by simpa using h0) (by simpa using hz)
      exact hyx₀ (by simpa using hzero x₀ (Ioo_subset_Icc_self hx₀))
    rcases lt_trichotomy lam 0 with hneg | hz | hpos
    · -- lam < 0 : compare with the sinh solution, which cannot vanish at π
      exfalso
      have hs0 : 0 < Real.sqrt (-lam) := Real.sqrt_pos.mpr (by linarith)
      set s := Real.sqrt (-lam) with hsdef
      have hsne : s ≠ 0 := ne_of_gt hs0
      have hs2 : s ^ 2 = -lam := Real.sq_sqrt (by linarith)
      set d0 := deriv y 0 with hd0
      have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => s * t) s t := fun t => by
        simpa using (hasDerivAt_id t).const_mul s
      have hc : ∀ t : ℝ, HasDerivAt (fun t => (d0 / s) * Real.sinh (s * t))
          ((d0 / s) * (s * Real.cosh (s * t))) t := by
        intro t
        have h3 : HasDerivAt (fun t => (d0 / s) * Real.sinh (s * t))
            ((d0 / s) * (Real.cosh (s * t) * s)) t :=
          ((Real.hasDerivAt_sinh (s * t)).comp t (hlin t)).const_mul (d0 / s)
        rw [show (d0 / s) * (s * Real.cosh (s * t)) =
          (d0 / s) * (Real.cosh (s * t) * s) from by ring]
        exact h3
      have hc' : ∀ t : ℝ, HasDerivAt (fun t => (d0 / s) * (s * Real.cosh (s * t)))
          (-(lam * ((d0 / s) * Real.sinh (s * t)))) t := by
        intro t
        have h3 : HasDerivAt (fun t => ((d0 / s) * s) * Real.cosh (s * t))
            (((d0 / s) * s) * (Real.sinh (s * t) * s)) t :=
          ((Real.hasDerivAt_cosh (s * t)).comp t (hlin t)).const_mul ((d0 / s) * s)
        have hfun : (fun t => ((d0 / s) * s) * Real.cosh (s * t)) =
            fun t => (d0 / s) * (s * Real.cosh (s * t)) := by
          funext r; ring
        rw [← hfun]
        have hval : -(lam * ((d0 / s) * Real.sinh (s * t))) =
            ((d0 / s) * s) * (Real.sinh (s * t) * s) := by
          have h5 : ((d0 / s) * s) * (Real.sinh (s * t) * s) =
              s ^ 2 * ((d0 / s) * Real.sinh (s * t)) := by ring
          rw [h5, hs2]
          ring
        rw [hval]
        exact h3
      have huniq := ode2_unique lam y (fun t => (d0 / s) * Real.sinh (s * t))
        (deriv y) (fun t => (d0 / s) * (s * Real.cosh (s * t)))
        hyI hyI' (fun t _ => hc t) (fun t _ => hc' t)
        (by simpa using h0)
        (by
          show deriv y 0 = (d0 / s) * (s * Real.cosh (s * 0))
          rw [mul_zero, Real.cosh_zero, mul_one, div_mul_cancel₀ _ hsne, hd0])
      have hcπ : (d0 / s) * Real.sinh (s * π) = 0 := by
        rw [← huniq π hπmem]
        exact hπ
      have hsinh : 0 < Real.sinh (s * π) :=
        Real.sinh_pos_iff.mpr (by positivity)
      have hd00 : d0 = 0 := by
        rcases mul_eq_zero.mp hcπ with h | h
        · exact (div_eq_zero_iff.mp h).resolve_right hsne
        · exact absurd h (ne_of_gt hsinh)
      exact hzero_case hd00
    · -- lam = 0 : compare with the linear solution
      exfalso
      set d0 := deriv y 0 with hd0
      have hc : ∀ t : ℝ, HasDerivAt (fun t => d0 * t) d0 t := by
        intro t
        simpa using (hasDerivAt_id t).const_mul d0
      have hc' : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => d0) (-(lam * (d0 * t))) t := by
        intro t
        rw [hz]
        simpa using hasDerivAt_const t d0
      have huniq := ode2_unique lam y (fun t => d0 * t) (deriv y) (fun _ => d0)
        hyI hyI' (fun t _ => hc t) (fun t _ => hc' t)
        (by simpa using h0) rfl
      have hcπ : d0 * π = 0 := by
        rw [← huniq π hπmem]
        exact hπ
      have hd00 : d0 = 0 := by
        rcases mul_eq_zero.mp hcπ with h | h
        · exact h
        · exact absurd h pi_ne_zero
      exact hzero_case hd00
    · -- lam > 0 : the sine solution forces sin (√lam · π) = 0
      have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hpos
      set s := Real.sqrt lam with hsdef
      have hsne : s ≠ 0 := ne_of_gt hs0
      have hs2 : s ^ 2 = lam := Real.sq_sqrt hpos.le
      set d0 := deriv y 0 with hd0
      have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => s * t) s t := fun t => by
        simpa using (hasDerivAt_id t).const_mul s
      have hc : ∀ t : ℝ, HasDerivAt (fun t => (d0 / s) * Real.sin (s * t))
          ((d0 / s) * (s * Real.cos (s * t))) t := by
        intro t
        have h3 : HasDerivAt (fun t => (d0 / s) * Real.sin (s * t))
            ((d0 / s) * (Real.cos (s * t) * s)) t :=
          ((Real.hasDerivAt_sin (s * t)).comp t (hlin t)).const_mul (d0 / s)
        rw [show (d0 / s) * (s * Real.cos (s * t)) =
          (d0 / s) * (Real.cos (s * t) * s) from by ring]
        exact h3
      have hc' : ∀ t : ℝ, HasDerivAt (fun t => (d0 / s) * (s * Real.cos (s * t)))
          (-(lam * ((d0 / s) * Real.sin (s * t)))) t := by
        intro t
        have h3 : HasDerivAt (fun t => ((d0 / s) * s) * Real.cos (s * t))
            (((d0 / s) * s) * (-Real.sin (s * t) * s)) t :=
          ((Real.hasDerivAt_cos (s * t)).comp t (hlin t)).const_mul ((d0 / s) * s)
        have hfun : (fun t => ((d0 / s) * s) * Real.cos (s * t)) =
            fun t => (d0 / s) * (s * Real.cos (s * t)) := by
          funext r; ring
        rw [← hfun]
        have hval : -(lam * ((d0 / s) * Real.sin (s * t))) =
            ((d0 / s) * s) * (-Real.sin (s * t) * s) := by
          have h5 : ((d0 / s) * s) * (-Real.sin (s * t) * s) =
              -(s ^ 2 * ((d0 / s) * Real.sin (s * t))) := by ring
          rw [h5, hs2]
        rw [hval]
        exact h3
      have huniq := ode2_unique lam y (fun t => (d0 / s) * Real.sin (s * t))
        (deriv y) (fun t => (d0 / s) * (s * Real.cos (s * t)))
        hyI hyI' (fun t _ => hc t) (fun t _ => hc' t)
        (by simpa using h0)
        (by
          show deriv y 0 = (d0 / s) * (s * Real.cos (s * 0))
          rw [mul_zero, Real.cos_zero, mul_one, div_mul_cancel₀ _ hsne, hd0])
      have hcπ : (d0 / s) * Real.sin (s * π) = 0 := by
        rw [← huniq π hπmem]
        exact hπ
      have hsin : Real.sin (s * π) = 0 := by
        rcases mul_eq_zero.mp hcπ with h | h
        · exact absurd ((div_eq_zero_iff.mp h).resolve_right hsne) hzero_case
        · exact h
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
      have hks : (k : ℝ) = s := mul_right_cancel₀ pi_ne_zero hk
      have hkpos : 0 < k := by
        have : (0:ℝ) < (k:ℝ) := hks ▸ hs0
        exact_mod_cast this
      refine ⟨k.toNat, by omega, ?_⟩
      have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        have h6 : ((k.toNat : ℤ) : ℝ) = (k : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hkpos.le)
        exact_mod_cast h6
      rw [hcast, hks, hs2]
  · rintro ⟨n, hn, rfl⟩
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := fun x => by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hdy : ∀ x : ℝ, HasDerivAt (fun x => Real.sin (n * x))
        ((n : ℝ) * Real.cos (n * x)) x := by
      intro x
      have h2 : HasDerivAt (fun x => Real.sin ((n : ℝ) * x))
          (Real.cos ((n : ℝ) * x) * n) x :=
        (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x (hlin x)
      rw [show (n : ℝ) * Real.cos (n * x) = Real.cos ((n : ℝ) * x) * n from by ring]
      exact h2
    have hderiv_eq : deriv (fun x => Real.sin (n * x)) = fun x => (n : ℝ) * Real.cos (n * x) :=
      funext fun x => (hdy x).deriv
    refine ⟨fun x => Real.sin (n * x), univ, isOpen_univ, subset_univ _, ?_, ?_, ?_, ?_,
      ⟨π / (2 * n), ⟨?_, ?_⟩, ?_⟩⟩
    · intro x _
      rw [hderiv_eq]
      exact hdy x
    · intro x _
      rw [hderiv_eq]
      have h3 : HasDerivAt (fun x => (n : ℝ) * Real.cos ((n : ℝ) * x))
          ((n : ℝ) * (-Real.sin ((n : ℝ) * x) * n)) x :=
        ((Real.hasDerivAt_cos ((n : ℝ) * x)).comp x (hlin x)).const_mul (n : ℝ)
      rw [show -((n : ℝ) ^ 2 * Real.sin (n * x)) =
        (n : ℝ) * (-Real.sin ((n : ℝ) * x) * n) from by ring]
      exact h3
    · simp
    · simpa using Real.sin_nat_mul_pi n
    · positivity
    · rw [div_lt_iff₀ (by positivity)]
      have h7 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      nlinarith [pi_pos]
    · have harg : (n : ℝ) * (π / (2 * n)) = π / 2 := by
        field_simp
      show Real.sin ((n : ℝ) * (π / (2 * n))) ≠ 0
      rw [harg, Real.sin_pi_div_two]
      exact one_ne_zero

end Submission
