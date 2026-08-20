import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.IntermediateValue
import Submission.Helpers

open Set

namespace Submission

/-- If `z` vanishes at both ends of `[α, β]` while `y` never vanishes there, the Wronskian
`y z' - z y'` must vanish somewhere inside: apply Rolle to `z / y`. -/
private lemma no_wronskian_zero_contradiction
    (y z : ℝ → ℝ) (α β : ℝ) (hαβ : α < β)
    (hy_cont : ContinuousOn y (Icc α β)) (hz_cont : ContinuousOn z (Icc α β))
    (hy_diff : ∀ x ∈ Ioo α β, HasDerivAt y (deriv y x) x)
    (hz_diff : ∀ x ∈ Ioo α β, HasDerivAt z (deriv z x) x)
    (hzα : z α = 0) (hzβ : z β = 0)
    (hyne : ∀ x ∈ Icc α β, y x ≠ 0)
    (hWne : ∀ x ∈ Ioo α β, y x * deriv z x - z x * deriv y x ≠ 0) : False := by
  have hdiv : ∀ x ∈ Ioo α β, HasDerivAt (fun t => z t / y t)
      ((deriv z x * y x - z x * deriv y x) / y x ^ 2) x := fun x hx =>
    (hz_diff x hx).div (hy_diff x hx) (hyne x (Ioo_subset_Icc_self hx))
  have hfc : ContinuousOn (fun t => z t / y t) (Icc α β) := hz_cont.div hy_cont hyne
  have hI : (fun t => z t / y t) α = (fun t => z t / y t) β := by simp [hzα, hzβ]
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hαβ hfc hI hdiv
  have hyc : y c ≠ 0 := hyne c (Ioo_subset_Icc_self hc)
  have hnum : deriv z c * y c - z c * deriv y c = 0 :=
    (div_eq_zero_iff.mp hc0).resolve_right (pow_ne_zero 2 hyc)
  exact hWne c hc (by linarith)

/-- A solution of `W' = -p W` that is nonzero at one point of a preconnected open set is
nonzero everywhere on it. Forward propagation of a zero is Grönwall's zero lemma; backward
propagation is the same lemma after the time reflection `t ↦ x₀ + x - t`. -/
private lemma wronskian_ne_zero_of_ne_zero_at
    (J : Set ℝ) (hJ_conn : IsPreconnected J)
    (p W : ℝ → ℝ) (hp : ContinuousOn p J)
    (hWd : ∀ x ∈ J, HasDerivAt W (-p x * W x) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ J) (hW₀ : W x₀ ≠ 0) :
    ∀ x ∈ J, W x ≠ 0 := by
  intro x hx hWx
  apply hW₀
  have hord : OrdConnected J := hJ_conn.ordConnected
  rcases le_total x x₀ with hle | hle
  · have hIcc : Icc x x₀ ⊆ J := hord.out hx hx₀
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hp.mono hIcc)
    have hcont : ContinuousOn W (Icc x x₀) := fun t ht =>
      (hWd t (hIcc ht)).continuousAt.continuousWithinAt
    have hbound : ∀ t ∈ Ico x x₀, ‖-p t * W t‖ ≤ K * ‖W t‖ := by
      intro t ht
      calc ‖-p t * W t‖ = ‖p t‖ * ‖W t‖ := by rw [norm_mul, norm_neg]
        _ ≤ K * ‖W t‖ :=
          mul_le_mul_of_nonneg_right (hK t (Ico_subset_Icc_self ht)) (norm_nonneg _)
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont
      (fun t ht => (hWd t (hIcc (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      hWx hbound x₀ (right_mem_Icc.mpr hle)
  · have hIcc : Icc x₀ x ⊆ J := hord.out hx₀ hx
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hp.mono hIcc)
    have hmem : ∀ t ∈ Icc x₀ x, x₀ + x - t ∈ Icc x₀ x := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hFd : ∀ t ∈ Icc x₀ x,
        HasDerivAt (fun s => W (x₀ + x - s)) (p (x₀ + x - t) * W (x₀ + x - t)) t := by
      intro t ht
      have h1 : HasDerivAt (fun s : ℝ => x₀ + x - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (x₀ + x)
      have h2 : HasDerivAt (fun s => W (x₀ + x - s))
          (-p (x₀ + x - t) * W (x₀ + x - t) * -1) t :=
        (hWd (x₀ + x - t) (hIcc (hmem t ht))).comp t h1
      have heq : p (x₀ + x - t) * W (x₀ + x - t) =
          -p (x₀ + x - t) * W (x₀ + x - t) * -1 := by ring
      rw [heq]
      exact h2
    have hcont : ContinuousOn (fun s => W (x₀ + x - s)) (Icc x₀ x) := fun t ht =>
      (hFd t ht).continuousAt.continuousWithinAt
    have h0 : (fun s => W (x₀ + x - s)) x₀ = 0 := by simpa using hWx
    have hbound : ∀ t ∈ Ico x₀ x,
        ‖p (x₀ + x - t) * W (x₀ + x - t)‖ ≤ K * ‖(fun s => W (x₀ + x - s)) t‖ := by
      intro t ht
      calc ‖p (x₀ + x - t) * W (x₀ + x - t)‖ = ‖p (x₀ + x - t)‖ * ‖W (x₀ + x - t)‖ :=
            norm_mul _ _
        _ ≤ K * ‖W (x₀ + x - t)‖ :=
          mul_le_mul_of_nonneg_right (hK _ (hmem t (Ico_subset_Icc_self ht))) (norm_nonneg _)
    have hfin := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont
      (fun t ht => (hFd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      h0 hbound x (right_mem_Icc.mpr hle)
    simpa using hfin

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  have hWd : ∀ x ∈ J, HasDerivAt (fun t => y₁ t * deriv y₂ t - y₂ t * deriv y₁ t)
      (-p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)) x := by
    intro x hx
    have h : HasDerivAt (fun t => y₁ t * deriv y₂ t - y₂ t * deriv y₁ t)
        (deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))
          - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x :=
      ((hy₁ x hx).mul (hy₂' x hx)).sub ((hy₂ x hx).mul (hy₁' x hx))
    have heq : -p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) =
        deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))
          - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) := by ring
    rw [heq]
    exact h
  obtain ⟨x₀, hx₀, hW₀⟩ := hW
  have hWne : ∀ x ∈ J, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0 :=
    wronskian_ne_zero_of_ne_zero_at J hJ_conn p _ hp hWd x₀ hx₀ hW₀
  have hy₁cont : ContinuousOn y₁ (Icc a b) := fun t ht =>
    (hy₁ t (hJ_sub ht)).continuousAt.continuousWithinAt
  have hy₂cont : ContinuousOn y₂ (Icc a b) := fun t ht =>
    (hy₂ t (hJ_sub ht)).continuousAt.continuousWithinAt
  have hamem : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hbmem : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hy₂a : y₂ a ≠ 0 := by
    intro h0
    exact hWne a (hJ_sub hamem) (by rw [hza, h0]; ring)
  have hy₂b : y₂ b ≠ 0 := by
    intro h0
    exact hWne b (hJ_sub hbmem) (by rw [hzb, h0]; ring)
  have hex : ∃ c ∈ Ioo a b, y₂ c = 0 := by
    by_contra hno
    push_neg at hno
    have hy₂ne : ∀ x ∈ Icc a b, y₂ x ≠ 0 := by
      intro t ht
      obtain h1 | h1 := eq_or_lt_of_le ht.1
      · exact h1 ▸ hy₂a
      obtain h2 | h2 := eq_or_lt_of_le ht.2
      · exact h2 ▸ hy₂b
      exact hno t ⟨h1, h2⟩
    exact no_wronskian_zero_contradiction y₂ y₁ a b hab hy₂cont hy₁cont
      (fun x hx => hy₂ x (hJ_sub (Ioo_subset_Icc_self hx)))
      (fun x hx => hy₁ x (hJ_sub (Ioo_subset_Icc_self hx)))
      hza hzb hy₂ne
      (fun x hx h0 => hWne x (hJ_sub (Ioo_subset_Icc_self hx)) (by linarith))
  obtain ⟨c, hc, hc0⟩ := hex
  refine ⟨c, ⟨hc, hc0⟩, ?_⟩
  rintro d ⟨hd, hd0⟩
  by_contra hdc
  have pair_contra : ∀ u v : ℝ, u ∈ Ioo a b → v ∈ Ioo a b → u < v →
      y₂ u = 0 → y₂ v = 0 → False := by
    intro u v hu hv huv hu0 hv0
    have hIccJ : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1.le hv.2.le
    have hIooab : ∀ x ∈ Icc u v, x ∈ Ioo a b := fun x hx =>
      ⟨lt_of_lt_of_le hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩
    exact no_wronskian_zero_contradiction y₁ y₂ u v huv
      (hy₁cont.mono hIccJ) (hy₂cont.mono hIccJ)
      (fun x hx => hy₁ x (hJ_sub (hIccJ (Ioo_subset_Icc_self hx))))
      (fun x hx => hy₂ x (hJ_sub (hIccJ (Ioo_subset_Icc_self hx))))
      hu0 hv0
      (fun x hx => hne x (hIooab x hx))
      (fun x hx => hWne x (hJ_sub (hIccJ (Ioo_subset_Icc_self hx))))
  rcases lt_or_gt_of_ne hdc with hlt | hgt
  · exact pair_contra d c hd hc hlt hd0 hc0
  · exact pair_contra c d hc hd hgt hc0 hd0

end Submission
