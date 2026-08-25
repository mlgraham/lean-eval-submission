import ChallengeDeps
import Submission.Helpers
import Submission.Newton

open LeanEval.LinearAlgebra.TraceNewton
open Matrix Polynomial
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Submission

theorem trace_cayley_hamilton_newton {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * charpolyDescendingCoeff A k +
        ∑ j ∈ Finset.Icc 1 k,
          trace (A ^ j) * charpolyDescendingCoeff A (k - j) = 0 := by
  have hc : ∀ m, charpolyDescendingCoeff A m = cdesc A m := fun m => rfl
  simp only [hc]
  exact newton_trace_identity A hk

end Submission
