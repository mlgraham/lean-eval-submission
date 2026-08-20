import Mathlib
import Submission.Helpers

open SimpleGraph Finset

namespace Submission

/-- Finset form of the finite Ramsey theorem, by double induction on `r` and `s`:
there is an `n` such that any finset `A` of at least `n` vertices (in any graph, on any
vertex type) contains an `r`-clique of `G` or an `s`-clique of `Gᶜ`. The pivot-vertex
pigeonhole argument stays inside the one vertex type, so no induced-subgraph transfer
is needed. -/
theorem ramsey_aux :
    ∀ r s : ℕ, ∃ n : ℕ, ∀ (V : Type) (G : SimpleGraph V) (A : Finset V), n ≤ A.card →
      (∃ t ⊆ A, G.IsNClique r t) ∨ (∃ t ⊆ A, Gᶜ.IsNClique s t) := by
  intro r
  induction r with
  | zero =>
    intro s
    exact ⟨0, fun V G A _ => Or.inl ⟨∅, empty_subset _, by simp⟩⟩
  | succ r ihr =>
    intro s
    induction s with
    | zero =>
      exact ⟨0, fun V G A _ => Or.inr ⟨∅, empty_subset _, by simp⟩⟩
    | succ s ihs =>
      obtain ⟨m₁, hm₁⟩ := ihr (s + 1)
      obtain ⟨m₂, hm₂⟩ := ihs
      refine ⟨m₁ + m₂ + 1, ?_⟩
      intro V G A hA
      classical
      have hAne : A.Nonempty := card_pos.mp (by omega)
      obtain ⟨v, hv⟩ := hAne
      have hBcard : m₁ + m₂ ≤ (A.erase v).card := by
        have := card_erase_of_mem hv
        omega
      have hNM := card_filter_add_card_filter_not (s := A.erase v) (fun u => G.Adj v u)
      set N := (A.erase v).filter (fun u => G.Adj v u) with hNdef
      set M := (A.erase v).filter (fun u => ¬ G.Adj v u) with hMdef
      have hsubN : N ⊆ A := (filter_subset _ _).trans (erase_subset _ _)
      have hsubM : M ⊆ A := (filter_subset _ _).trans (erase_subset _ _)
      rcases le_or_gt m₁ N.card with hle | hlt
      · rcases hm₁ V G N hle with ⟨t, htN, ht⟩ | ⟨t, htN, ht⟩
        · refine Or.inl ⟨insert v t, insert_subset hv (htN.trans hsubN), ht.insert ?_⟩
          intro b hb
          exact (mem_filter.mp (htN hb)).2
        · exact Or.inr ⟨t, htN.trans hsubN, ht⟩
      · have hM2 : m₂ ≤ M.card := by omega
        rcases hm₂ V G M hM2 with ⟨t, htM, ht⟩ | ⟨t, htM, ht⟩
        · exact Or.inl ⟨t, htM.trans hsubM, ht⟩
        · refine Or.inr ⟨insert v t, insert_subset hv (htM.trans hsubM), ht.insert ?_⟩
          intro b hb
          have hb' := mem_filter.mp (htM hb)
          exact (G.compl_adj v b).mpr ⟨(ne_of_mem_erase hb'.1).symm, hb'.2⟩

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s _ _
  obtain ⟨n, hn⟩ := ramsey_aux r s
  refine ⟨n, fun G => ?_⟩
  rcases hn (Fin n) G univ (by simp) with ⟨t, _, ht⟩ | ⟨t, _, ht⟩
  · exact Or.inl fun h => h t ht
  · exact Or.inr fun h => h t ht

end Submission
