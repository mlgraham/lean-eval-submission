import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.KoszulFormula
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

namespace Submission

theorem koszul_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (X Y Z : Π x : M, TangentSpace I x)
    (_hX : CMDiff ∞ (T% X)) (_hY : CMDiff ∞ (T% Y)) (_hZ : CMDiff ∞ (T% Z))
    (x : M) :
    2 * inner ℝ (cov Y x (X x)) (Z x) =
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x (X x)
      + mvfderiv I (fun y : M => inner ℝ (X y) (Z y)) x (Y x)
      - mvfderiv I (fun y : M => inner ℝ (X y) (Y y)) x (Z x)
      - inner ℝ (X x) (mlieBracket I Y Z x)
      - inner ℝ (Y x) (mlieBracket I X Z x)
      + inner ℝ (Z x) (mlieBracket I X Y x) := by
  have hX' : MDiffAt (T% X) x := _hX.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) x := _hY.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := _hZ.mdifferentiableAt (by simp)
  have hYZ : cov Z x (Y x) - cov Y x (Z x) = mlieBracket I Y Z x :=
    cov.torsion_eq_zero_iff.mp _htor hY' hZ'
  have hXZ : cov Z x (X x) - cov X x (Z x) = mlieBracket I X Z x :=
    cov.torsion_eq_zero_iff.mp _htor hX' hZ'
  have hXY : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    cov.torsion_eq_zero_iff.mp _htor hX' hY'
  rw [_hmet Y Z _hY _hZ x (X x), _hmet X Z _hX _hZ x (Y x), _hmet X Y _hX _hY x (Z x),
    ← hYZ, ← hXZ, ← hXY]
  simp only [inner_sub_right]
  rw [real_inner_comm (Z x) (cov Y x (X x)), real_inner_comm (Z x) (cov X x (Y x)),
    real_inner_comm (cov X x (Z x)) (Y x)]
  ring

end Submission
