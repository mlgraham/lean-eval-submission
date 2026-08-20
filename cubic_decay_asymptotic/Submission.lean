import Mathlib
import Submission.Helpers

open Filter Topology Set

namespace Submission

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  set c : ℝ → ℝ := fun t => (Real.sqrt (1 + 2 * t))⁻¹ with hcdef
  have hupos : ∀ t : ℝ, 0 ≤ t → (0:ℝ) < 1 + 2 * t := by intro t ht; linarith
  have hsqrtpos : ∀ t : ℝ, 0 ≤ t → 0 < Real.sqrt (1 + 2 * t) := fun t ht =>
    Real.sqrt_pos.mpr (hupos t ht)
  have hc0 : c 0 = 1 := by simp [hcdef]
  have hcle : ∀ t : ℝ, 0 ≤ t → |c t| ≤ 1 := by
    intro t ht
    have h1 : (1:ℝ) ≤ Real.sqrt (1 + 2 * t) :=
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (1 + 2 * t) := Real.sqrt_le_sqrt (by linarith)
    rw [hcdef, abs_of_pos (inv_pos.mpr (hsqrtpos t ht))]
    exact inv_le_one_of_one_le₀ h1
  have hc_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt c (-(c t) ^ 3) t := by
    intro t ht
    have hu := hupos t ht
    have hs := hsqrtpos t ht
    have h1 : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2:ℝ)).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + 2 * s))
        (1 / (2 * Real.sqrt (1 + 2 * t)) * 2) t :=
      (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp t h1
    have h3 := h2.inv (ne_of_gt hs)
    have heq : -(c t) ^ 3 =
        -(1 / (2 * Real.sqrt (1 + 2 * t)) * 2) / Real.sqrt (1 + 2 * t) ^ 2 := by
      rw [hcdef]
      field_simp
    rw [heq]
    exact h3
  -- y agrees with the explicit solution on [0, ∞)
  have hyc : ∀ t : ℝ, 0 ≤ t → y t = c t := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | htpos
    · rw [← h0, hy0, hc0]
    have hy_contOn : ContinuousOn y (Icc 0 t) := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0]
        exact hy_cont.mono Icc_subset_Ici_self
      · exact ((hy_diff s h0).continuousAt).continuousWithinAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hy_contOn
    set R : ℝ := max M 1 with hRdef
    have hR1 : (1:ℝ) ≤ R := le_max_right _ _
    have hR0 : (0:ℝ) ≤ R := le_trans zero_le_one hR1
    have hyR : ∀ s ∈ Icc (0:ℝ) t, y s ∈ Metric.closedBall (0:ℝ) R := by
      intro s hs
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact le_trans (hM s hs) (le_max_left _ _)
    have hcR : ∀ s ∈ Icc (0:ℝ) t, c s ∈ Metric.closedBall (0:ℝ) R := by
      intro s hs
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact le_trans (hcle s hs.1) hR1
    set K : NNReal := ⟨3 * R ^ 2, by positivity⟩ with hKdef
    have hlip : LipschitzOnWith K (fun x : ℝ => -x ^ 3) (Metric.closedBall (0:ℝ) R) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro a ha b hb
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ha hb
      rw [Real.dist_eq, Real.dist_eq]
      have hfac : -a ^ 3 - -b ^ 3 = -((a - b) * (a ^ 2 + a * b + b ^ 2)) := by ring
      rw [hfac, abs_neg, abs_mul]
      have hKcoe : (K : ℝ) = 3 * R ^ 2 := rfl
      rw [hKcoe, mul_comm (3 * R ^ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h1 := abs_le.mp ha
      have h2 := abs_le.mp hb
      have habs : |a ^ 2 + a * b + b ^ 2| ≤ 3 * R ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
      exact habs
    have hbound : ∀ δ : ℝ, 0 < δ → δ ≤ t →
        dist (y t) (c t) ≤ dist (y δ) (c δ) * Real.exp (K * (t - δ)) := by
      intro δ hδ0 hδt
      have hIccsub : Icc δ t ⊆ Icc 0 t := Icc_subset_Icc hδ0.le le_rfl
      have hIcosub : Ico δ t ⊆ Icc 0 t := fun s hs => ⟨le_trans hδ0.le hs.1, hs.2.le⟩
      have h := dist_le_of_trajectories_ODE_of_mem
        (v := fun _ x => -x ^ 3) (s := fun _ => Metric.closedBall (0:ℝ) R) (K := K)
        (f := y) (g := c) (a := δ) (b := t)
        (fun _ _ => hlip)
        (hy_contOn.mono hIccsub)
        (fun s hs => (hy_diff s (lt_of_lt_of_le hδ0 hs.1)).hasDerivWithinAt)
        (fun s hs => hyR s (hIcosub hs))
        (fun s hs => ((hc_deriv s (le_trans hδ0.le hs.1)).continuousAt).continuousWithinAt)
        (fun s hs => (hc_deriv s (le_trans hδ0.le hs.1)).hasDerivWithinAt)
        (fun s hs => hcR s (hIcosub hs))
        (le_refl (dist (y δ) (c δ)))
      exact h t (right_mem_Icc.mpr hδt)
    have h1 : Tendsto y (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have h := hy_cont
      rw [ContinuousWithinAt, hy0] at h
      exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 : Tendsto c (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have h := (hc_deriv 0 le_rfl).continuousAt
      rw [ContinuousAt, hc0] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hdist0 : Tendsto (fun δ => dist (y δ) (c δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := h1.dist h2
      simpa using this
    have hexp : Tendsto (fun δ : ℝ => Real.exp (K * (t - δ))) (𝓝[>] (0:ℝ))
        (𝓝 (Real.exp (K * t))) := by
      have hcont : Continuous fun δ : ℝ => Real.exp (K * (t - δ)) := by
        continuity
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    have hεlim : Tendsto (fun δ => dist (y δ) (c δ) * Real.exp (K * (t - δ)))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using hdist0.mul hexp
    have hfinal : dist (y t) (c t) ≤ 0 := by
      refine ge_of_tendsto hεlim ?_
      have hIoc : Ioc (0:ℝ) t ∈ 𝓝[>] (0:ℝ) := Ioc_mem_nhdsGT htpos
      filter_upwards [hIoc] with δ hδ
      exact hbound δ hδ.1 hδ.2
    exact dist_eq_zero.mp (le_antisymm hfinal dist_nonneg)
  -- the limit computation
  have hyx : (fun t : ℝ => y t * Real.sqrt t) =ᶠ[atTop]
      fun t : ℝ => Real.sqrt (t / (1 + 2 * t)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [hyc t ht, hcdef, Real.sqrt_div ht, div_eq_inv_mul]
  have hlim2 : Tendsto (fun t : ℝ => t / (1 + 2 * t)) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ + 2) atTop (𝓝 (0 + 2)) :=
      tendsto_inv_atTop_zero.add tendsto_const_nhds
    have h2 : Tendsto (fun t : ℝ => (t⁻¹ + 2)⁻¹) atTop (𝓝 ((0 + 2 : ℝ))⁻¹) :=
      h1.inv₀ (by norm_num)
    have h3 : Tendsto (fun t : ℝ => (t⁻¹ + 2)⁻¹) atTop (𝓝 (1 / 2)) := by
      convert h2 using 2
      norm_num
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [eq_comm]
    field_simp
  have hlim3 : Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) atTop
      (𝓝 (Real.sqrt (1 / 2))) :=
    (Real.continuous_sqrt.tendsto _).comp hlim2
  have hval : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [one_div, one_div, Real.sqrt_inv]
  rw [← hval]
  exact Filter.Tendsto.congr' hyx.symm hlim3

end Submission
