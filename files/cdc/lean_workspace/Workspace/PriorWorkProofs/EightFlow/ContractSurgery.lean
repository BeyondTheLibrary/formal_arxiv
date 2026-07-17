import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.PriorWorkProofs.Tutte.Basic

open Set
open scoped Graph
open Workspace.PriorWorkProofs.Tutte

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*} [DecidableEq α] {G : Graph α β}

/-- **GOAL 1.** Reachability pushes forward through contraction: a walk in `G − e'` maps to a
walk in `(G / e₁) − e'` under the merge map. The contracted edge `e₁` collapses its two ends to
a single vertex, so any step of the original walk that used `e₁` becomes a no-op. -/
theorem reachable_deleteEdges_contract {e₁ e' : β} {x y : α} (hxy : G.IsLink e₁ x y) {u v : α}
    (h : (G.deleteEdges {e'}).Reachable u v) :
    ((contract G e₁ x y).deleteEdges {e'}).Reachable (mergeMap x y u) (mergeMap x y v) := by
  -- `mergeMap x y` sends both ends of `e₁` to `x`.
  have hmerge : ∀ z : α, z = x ∨ z = y → mergeMap x y z = x := by
    rintro z (hz | hz)
    · rw [hz]; unfold mergeMap; split_ifs <;> rfl
    · rw [hz]; exact mergeMap_self x y
  induction h with
  | refl => exact Graph.Reachable.rfl
  | @tail p q hup hpq ih =>
    obtain ⟨e'', hf⟩ := hpq
    rw [Graph.deleteEdges_isLink] at hf
    obtain ⟨hLpq, hne'⟩ := hf
    by_cases hee : e'' = e₁
    · -- The step uses the contracted edge, so its two images coincide: no progress.
      subst hee
      have hpq_eq : mergeMap x y p = mergeMap x y q := by
        rcases hLpq.eq_and_eq_or_eq_and_eq hxy with ⟨hp, hq⟩ | ⟨hp, hq⟩
        · rw [hmerge p (Or.inl hp), hmerge q (Or.inr hq)]
        · rw [hmerge p (Or.inr hp), hmerge q (Or.inl hq)]
      rw [← hpq_eq]; exact ih
    · -- The step survives contraction as a genuine edge of `(G / e₁) − e'`.
      have hcontract : (contract G e₁ x y).IsLink e'' (mergeMap x y p) (mergeMap x y q) := by
        rw [contract_isLink]
        exact ⟨hee, p, q, hLpq, rfl, rfl⟩
      have hdel : ((contract G e₁ x y).deleteEdges {e'}).IsLink e''
          (mergeMap x y p) (mergeMap x y q) := by
        rw [Graph.deleteEdges_isLink]
        exact ⟨hcontract, hne'⟩
      exact ih.tail ⟨e'', hdel⟩

/-- **GOAL 2.** Contracting a (non-loop) edge preserves bridgelessness. -/
theorem contract_bridgeless {e₁ : β} {x y : α} (hbr : G.Bridgeless) (hxy : G.IsLink e₁ x y) :
    (contract G e₁ x y).Bridgeless := by
  apply Graph.bridgeless_of_forall_reachable
  intro e' _he' a b hab
  rw [contract_isLink] at hab
  obtain ⟨_hne, a', b', hLab, ha, hb⟩ := hab
  -- `e'` is a genuine edge of `G`, and `G` is bridgeless, so its ends stay connected in `G − e'`.
  have hnb : ¬ G.IsBridge e' := hbr.not_isBridge e'
  rw [Graph.isBridge_def] at hnb
  push_neg at hnb
  have hreach : (G.deleteEdges {e'}).Reachable a' b' := hnb a' b' hLab
  -- Push that walk through the contraction.
  have key := reachable_deleteEdges_contract hxy hreach
  rw [ha, hb] at key
  exact key

/-- **GOAL 3.** Contracting an existing edge strictly drops the edge count. -/
theorem edgeSet_contract_ncard_lt {e₁ : β} {x y : α} (hE : E(G).Finite) (he₁ : e₁ ∈ E(G)) :
    (E(contract G e₁ x y)).ncard < E(G).ncard := by
  rw [edgeSet_contract]
  exact Set.ncard_diff_singleton_lt_of_mem he₁ hE

end Workspace.PriorWorkProofs.EightFlow
