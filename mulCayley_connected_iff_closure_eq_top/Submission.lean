import Mathlib
import Submission.Helpers

open SimpleGraph

namespace Submission

/-- Left translation by `a` is a homomorphism of the Cayley graph: adjacency is defined by
right factors, which left translation preserves. -/
private def leftMulHom {G : Type*} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun x := a * x
  map_rel' := by
    intro u v h
    rw [SimpleGraph.mulCayley_adj] at h ⊢
    obtain ⟨hne, h⟩ := h
    refine ⟨by simpa using hne, ?_⟩
    simpa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  have adj_mem : ∀ {x y : G}, (mulCayley S).Adj x y →
      x ∈ Subgroup.closure S → y ∈ Subgroup.closure S := by
    intro x y hadj hx
    rw [SimpleGraph.mulCayley_adj] at hadj
    obtain ⟨-, h | h⟩ := hadj
    · have h1 : x * (x⁻¹ * y) ∈ Subgroup.closure S :=
        mul_mem hx (Subgroup.subset_closure h)
      simpa [mul_inv_cancel_left] using h1
    · have h1 : x * (y⁻¹ * x)⁻¹ ∈ Subgroup.closure S :=
        mul_mem hx (inv_mem (Subgroup.subset_closure h))
      simpa [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h1
  constructor
  · intro hconn
    rw [Subgroup.eq_top_iff']
    intro g
    obtain ⟨w⟩ := hconn.preconnected 1 g
    have main : ∀ {a b : G}, (mulCayley S).Walk a b →
        a ∈ Subgroup.closure S → b ∈ Subgroup.closure S := by
      intro a b w
      induction w with
      | nil => exact id
      | cons h p ih => exact fun ha => ih (adj_mem h ha)
    exact main w (one_mem _)
  · intro htop
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨1, fun g => ?_⟩
    have hg : g ∈ Subgroup.closure S := htop ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      by_cases h1 : x = 1
      · subst h1; exact Reachable.refl _
      · refine SimpleGraph.Adj.reachable ?_
        rw [SimpleGraph.mulCayley_adj]
        exact ⟨fun h => h1 h.symm, Or.inl (by simpa using hx)⟩
    | one => exact Reachable.refl _
    | mul x y hx hy ihx ihy =>
      have h2 : (mulCayley S).Reachable (x * 1) (x * y) := ihy.map (leftMulHom S x)
      have h3 : (mulCayley S).Reachable x (x * y) := by simpa using h2
      exact ihx.trans h3
    | inv x hx ihx =>
      have h2 : (mulCayley S).Reachable (x⁻¹ * 1) (x⁻¹ * x) := ihx.map (leftMulHom S x⁻¹)
      have h3 : (mulCayley S).Reachable x⁻¹ 1 := by simpa using h2
      exact h3.symm

end Submission
