import Mathlib
import Submission.Helpers

namespace Submission

/-- Comparison principle for the 1-D Dirichlet problem: with `w := u - v`, the hypothesis
`-u'' ≤ -v''` on `(0,1)` says `w'' ≥ 0`, so `w` is convex on `[0,1]` and hence bounded by
its endpoint values, both `≤ 0`. -/
theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  have hwd : ∀ x ∈ J, HasDerivAt (fun y => u y - v y) (deriv u x - deriv v x) x :=
    fun x hx => (hu x hx).sub (hv x hx)
  have hwderiv : ∀ x ∈ J, deriv (fun y => u y - v y) x = deriv u x - deriv v x :=
    fun x hx => (hwd x hx).deriv
  have hwd2 : ∀ x ∈ J,
      HasDerivAt (deriv (fun y => u y - v y)) (deriv (deriv u) x - deriv (deriv v) x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => deriv u y - deriv v y)
        (deriv (deriv u) x - deriv (deriv v) x) x := (hu' x hx).sub (hv' x hx)
    exact h1.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hJ_open.mem_nhds hx) fun y hy => hwderiv y hy)
  have hcont : ContinuousOn (fun y => u y - v y) (Set.Icc (0 : ℝ) 1) := fun x hx =>
    ((hwd x (hJ_sub hx)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun y => u y - v y) (interior (Set.Icc (0 : ℝ) 1)) :=
    fun x hx => ((hwd x (hJ_sub (interior_subset hx))).differentiableAt).differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv (fun y => u y - v y))
      (interior (Set.Icc (0 : ℝ) 1)) :=
    fun x hx => ((hwd2 x (hJ_sub (interior_subset hx))).differentiableAt).differentiableWithinAt
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun y => u y - v y) := by
    refine convexOn_of_deriv2_nonneg (convex_Icc 0 1) hcont hdiff hdiff2 ?_
    intro x hx
    rw [interior_Icc] at hx
    have h2 : deriv (deriv (fun y => u y - v y)) x = deriv (deriv u) x - deriv (deriv v) x :=
      (hwd2 x (hJ_sub (Set.Ioo_subset_Icc_self hx))).deriv
    have h3 := hineq x hx
    show 0 ≤ deriv^[2] (fun y => u y - v y) x
    have hit : deriv^[2] (fun y => u y - v y) x = deriv (deriv (fun y => u y - v y)) x := rfl
    rw [hit, h2]
    linarith
  intro x hx
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hseg : x ∈ segment ℝ (0 : ℝ) 1 := by
    rwa [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  have hle := hconv.le_on_segment h01 h11 hseg
  have hmax : max (u 0 - v 0) (u 1 - v 1) ≤ 0 :=
    max_le (sub_nonpos.mpr hu0) (sub_nonpos.mpr hu1)
  have : u x - v x ≤ 0 := le_trans hle hmax
  linarith

end Submission
