import Mathlib
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.LeanEval
open _root_.LeanEval.ConvexGeometry
open _root_.LeanEval.ConvexGeometry.LinearProgram
namespace LeanEval
namespace ConvexGeometry

open Matrix Set

section Helpers

variable {m n : ℕ}

/-- The objective as a continuous linear functional. -/
noncomputable def objectiveCLM (lp : LinearProgram m n) : (Fin m → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => lp.c ⬝ᵥ y
      map_add' := fun y z => dotProduct_add _ _ _
      map_smul' := fun r y => by simp [dotProduct_smul] }

@[simp] lemma objectiveCLM_apply (lp : LinearProgram m n) (y : Fin m → ℝ) :
    objectiveCLM lp y = lp.objective y := rfl

lemma objective_eq (lp : LinearProgram m n) : lp.objective = fun y => lp.c ⬝ᵥ y := rfl

lemma convex_feasible (lp : LinearProgram m n) : Convex ℝ lp.feasible := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · intro i
    have h1 := hx1 i
    have h2 := hy1 i
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc a * (lp.A *ᵥ x) i + b * (lp.A *ᵥ y) i ≤ a * lp.b i + b * lp.b i := by gcongr
      _ = lp.b i := by rw [← add_mul, hab, one_mul]
  · intro i
    have h1 := hx2 i
    have h2 := hy2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    positivity

lemma isClosed_feasible (lp : LinearProgram m n) : IsClosed lp.feasible := by
  have hcont : Continuous fun x : Fin m → ℝ => lp.A *ᵥ x :=
    (Matrix.mulVecLin lp.A).continuous_of_finiteDimensional
  exact (isClosed_le hcont continuous_const).inter (isClosed_le continuous_const continuous_id)

lemma concaveOn_objective (lp : LinearProgram m n) : ConcaveOn ℝ lp.feasible lp.objective := by
  refine ⟨(convex_feasible lp), ?_⟩
  intro x _ y _ a b _ _ _
  simp only [objective_eq, dotProduct_add, dotProduct_smul, smul_eq_mul, le_refl]

end Helpers

/-- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) := by
  have hmax : IsMaxOn lp.objective lp.feasible x :=
    IsMaxOn.of_isLocalMaxOn_of_concaveOn _hx _hlocal (concaveOn_objective lp)
  refine ⟨hmax, fun hc => ?_⟩
  refine ⟨subset_closure _hx, fun hint => ?_⟩
  -- an interior point can be moved in direction `c` while staying feasible
  rcases Metric.isOpen_iff.1 isOpen_interior x hint with ⟨ε, hε, hball⟩
  have hcc : 0 < lp.c ⬝ᵥ lp.c := by
    have h := dotProduct_self_star_pos_iff.2 hc
    simpa using h
  have hcn : 0 < ‖lp.c‖ := norm_pos_iff.2 hc
  set t : ℝ := ε / (2 * ‖lp.c‖) with ht
  have htpos : 0 < t := by positivity
  have hy : x + t • lp.c ∈ lp.feasible := by
    apply interior_subset
    apply hball
    have hnorm : ‖t • lp.c‖ = ε / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
      field_simp
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
    linarith
  have := hmax hy
  simp only [objective_eq, Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  nlinarith

/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible := by
  have hcpt : IsCompact lp.feasible := Metric.isCompact_of_isClosed_isBounded (isClosed_feasible lp) _hbdd
  obtain ⟨x₀, hx₀, hmax₀⟩ := hcpt.exists_isMaxOn _hfeas (objectiveCLM lp).continuous.continuousOn
  -- the maximal face
  set F : Set (Fin m → ℝ) := {y ∈ lp.feasible | ∀ z ∈ lp.feasible, (objectiveCLM lp) z ≤ (objectiveCLM lp) y}
    with hF
  have hexp : IsExposed ℝ lp.feasible F := fun _ => ⟨(objectiveCLM lp), rfl⟩
  have hFne : F.Nonempty := ⟨x₀, hx₀, fun z hz => hmax₀ hz⟩
  have hFcpt : IsCompact F := hexp.isCompact hcpt
  obtain ⟨e, he⟩ := hFcpt.extremePoints_nonempty hFne
  refine ⟨e, he.1.1, fun z hz => he.1.2 z hz, ?_⟩
  exact hexp.isExtreme.extremePoints_subset_extremePoints he

end ConvexGeometry
end LeanEval

end Submission
