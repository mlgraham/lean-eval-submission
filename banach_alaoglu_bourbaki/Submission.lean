import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open Set Topology
open scoped Pointwise

namespace Submission

section TypeSynonym

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Type synonym: `E` retopologized by the seminorm `p`. -/
private def Ep (_p : Seminorm ℝ E) : Type _ := E

private instance (p : Seminorm ℝ E) : AddCommGroup (Ep p) :=
  inferInstanceAs (AddCommGroup E)

private instance (p : Seminorm ℝ E) : SeminormedAddCommGroup (Ep p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (p.toAddGroupSeminorm)

private instance (p : Seminorm ℝ E) : Module ℝ (Ep p) := inferInstanceAs (Module ℝ E)

private lemma Ep_norm (p : Seminorm ℝ E) (x : Ep p) : ‖x‖ = p x := rfl

private instance (p : Seminorm ℝ E) : NormedSpace ℝ (Ep p) where
  norm_smul_le c x := by
    rw [Ep_norm, Ep_norm]
    rw [show ((c • x : Ep p) : E) = c • (x : E) from rfl] -- may be unnecessary
    exact le_of_eq (map_smul_eq_mul p c x)

end TypeSynonym

theorem banach_alaoglu_bourbaki (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (U : Set E) (_hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (weakStarPolar E U) := by
  classical
  -- E is a topological additive group: negation is `(-1) • ·`.
  haveI : ContinuousNeg E := ⟨by
    have h : Continuous fun x : E => (-1 : ℝ) • x := continuous_const_smul _
    simpa [neg_one_smul] using h⟩
  haveI : IsTopologicalAddGroup E := ⟨⟩
  -- pick an open absolutely convex V ⊆ U
  obtain ⟨V, ⟨hV0, hVopen, hVbal, hVconv⟩, hVU⟩ :=
    (nhds_hasBasis_absConvex_open ℝ E).mem_iff.mp _hU
  have hVnhds : V ∈ 𝓝 (0 : E) := hVopen.mem_nhds hV0
  have hVabs : Absorbent ℝ V := absorbent_nhds_zero hVnhds
  set p : Seminorm ℝ E := gaugeSeminorm hVbal hVconv hVabs with hpdef
  have hball : p.ball 0 1 = V := gaugeSeminorm_ball_one hVopen
  have hmem_of_lt_one : ∀ x : E, p x < 1 → x ∈ V := by
    intro x hx
    rw [← hball]
    simpa [Seminorm.mem_ball_zero] using hx
  -- gauge is small near zero
  have hp_tendsto : Filter.Tendsto p (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmul : (ε / 2) • V ∈ 𝓝 (0 : E) := by
      exact (set_smul_mem_nhds_zero_iff (by positivity : (ε / 2 : ℝ) ≠ 0)).mpr hVnhds
    filter_upwards [hsmul] with x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hpv : p v < 1 := gaugeSeminorm_lt_one_of_isOpen hVopen hv
    have : p ((ε / 2) • v) = (ε / 2) * p v := by
      rw [map_smul_eq_mul p]
      congr 1
      exact Real.norm_of_nonneg (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg p _), this]
    nlinarith [apply_nonneg p v]
  -- polar members are dominated by the gauge
  have hdom : ∀ φ : WeakDual ℝ E, φ ∈ weakStarPolar E U → ∀ x : E, ‖φ x‖ ≤ p x := by
    intro φ hφ x
    by_contra hlt
    push_neg at hlt
    set s : ℝ := (p x + ‖φ x‖) / 2 with hs
    have hs0 : 0 < s := by
      have := apply_nonneg p x
      have := norm_nonneg (φ x)
      nlinarith
    have hps : p x < s := by simp only [hs]; nlinarith
    have hsφ : s < ‖φ x‖ := by simp only [hs]; nlinarith
    have hmem : s⁻¹ • x ∈ V := by
      apply hmem_of_lt_one
      rw [show p (s⁻¹ • x) = |s⁻¹| * p x from map_smul_eq_mul p s⁻¹ x, abs_of_pos (by positivity)]
      rw [inv_mul_lt_iff₀ hs0, mul_one]
      exact hps
    have hle := hφ _ (hVU hmem)
    rw [map_smul, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le] at hle
    rw [inv_mul_le_iff₀ hs0, mul_one] at hle
    exact absurd hle (not_le.mpr hsφ)
  -- the compact source: polar of the unit ball in the seminormed synonym
  have hK : IsCompact (WeakDual.polar ℝ (Metric.closedBall (0 : Ep p) 1)) :=
    WeakDual.isCompact_polar ℝ (Metric.closedBall_mem_nhds _ one_pos)
  -- transport map: a p-continuous functional is E-continuous
  have hEcont : ∀ ψ : WeakDual ℝ (Ep p), Continuous fun x : E => ψ x := by
    intro ψ
    let ψ' : (Ep p) →L[ℝ] ℝ := ψ
    have hbound : ∀ x : E, ‖ψ x‖ ≤ ‖ψ'‖ * p x := fun x => by
      let x' : Ep p := x
      have h := ψ'.le_opNorm x'
      have hx : ‖x'‖ = p x := rfl
      rw [hx] at h
      exact h
    have hat0 : Filter.Tendsto (fun x : E => ψ x) (𝓝 0) (𝓝 0) := by
      apply squeeze_zero_norm hbound
      simpa using hp_tendsto.const_mul ‖ψ'‖
    let f : E →+ ℝ :=
      { toFun := fun x : E => ψ x
        map_zero' := map_zero ψ
        map_add' := fun a b => map_add ψ a b }
    have h0 : f 0 = 0 := map_zero ψ
    have hf : Continuous f := continuous_of_continuousAt_zero f (by
      unfold ContinuousAt
      rw [h0]
      exact hat0)
    exact hf
  let T : WeakDual ℝ (Ep p) → WeakDual ℝ E := fun ψ =>
    { toLinearMap := (ψ.toLinearMap : E →ₗ[ℝ] ℝ), cont := hEcont ψ }
  have hTcont : Continuous T := by
    apply WeakBilin.continuous_of_continuous_eval
    intro y
    exact WeakBilin.eval_continuous _ y
  -- weakStarPolar E U sits inside the image of the compact polar
  have hsub : weakStarPolar E U ⊆ T '' WeakDual.polar ℝ (Metric.closedBall (0 : Ep p) 1) := by
    intro φ hφ
    have hb := hdom φ hφ
    refine ⟨LinearMap.mkContinuous (φ.toLinearMap : Ep p →ₗ[ℝ] ℝ) 1 (fun x => ?_), ?_, ?_⟩
    · rw [Ep_norm, one_mul]
      exact hb x
    · intro x hx
      have hx1 : p x ≤ 1 := by
        simpa [Ep_norm] using mem_closedBall_zero_iff.mp hx
      exact le_trans (hb x) hx1
    · exact ContinuousLinearMap.ext fun x => rfl
  -- the polar is weak-* closed
  have hclosed : IsClosed (weakStarPolar E U) := by
    have heq : weakStarPolar E U = ⋂ x ∈ U, {φ : WeakDual ℝ E | ‖φ x‖ ≤ 1} := by
      ext φ
      simp [weakStarPolar]
    rw [heq]
    refine isClosed_biInter fun x hx => ?_
    have hcont : Continuous fun φ : WeakDual ℝ E => ‖φ x‖ :=
      (WeakBilin.eval_continuous _ x).norm
    exact isClosed_le hcont continuous_const
  exact (hK.image hTcont).of_isClosed_subset hclosed hsub

end Submission
