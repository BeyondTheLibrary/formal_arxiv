import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.Tutte.PartI
import Workspace.PriorWorkProofs.Tutte.Rerouting

/-!
# Assembly of Tutte's group-flow theorem

This file assembles the two proved halves — `exists_flow_iff_zmod` (Part I) and
`zk_iff_int_k_flow` (Rerouting) — into Tutte's group-flow theorem and its `Γ`/`8`
corollary, matching byte-for-byte the signatures of the `axiom`s
`tutte_group_flow` and `tutte_gamma_flow_iff_integer_eight_flow` in
`Workspace/PriorWork.lean`.
-/

open Graph
open scoped Graph
open Workspace.Types.Gamma Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.Tutte

/-- **Tutte's group-flow theorem** (assembled). For a finite abelian group `A` of
order `k`, a graph has a nowhere-zero `A`-flow iff it has a nowhere-zero integer
`k`-flow. -/
theorem tutte_group_flow_proved {α β : Type*} {A : Type*} [AddCommGroup A] [Finite A] {k : ℕ}
    (hA : Nat.card A = k) (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (O : Orientation G) :
    (∃ f : β → A, G.IsFlow O f ∧ G.IsNowhereZero f) ↔
      (∃ φ : β → ℤ, G.IsIntegerKFlow O φ (k : ℤ)) := by
  haveI := Classical.decEq α
  haveI : Nonempty A := ⟨0⟩
  have hk : 1 ≤ k := by
    have : 0 < Nat.card A := Nat.card_pos
    omega
  haveI : NeZero k := ⟨by omega⟩
  exact (exists_flow_iff_zmod hE O hA).trans (zk_iff_int_k_flow hk hV hE O)

/-- **Tutte's group-flow theorem, the `Γ = 𝔽₂³` / `8`-flow corollary** (assembled).
A graph has a nowhere-zero `Γ`-flow iff it has a nowhere-zero integer `8`-flow. -/
theorem tutte_gamma_flow_iff_integer_eight_flow_proved {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (O : Orientation G) :
    (∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f) ↔
      (∃ φ : β → ℤ, G.IsIntegerKFlow O φ 8) := by
  have hcard : Nat.card Gamma = 8 := by
    rw [Nat.card_eq_fintype_card, Gamma.card_eq]
  have h := tutte_group_flow_proved hcard G hV hE O
  simpa using h

end Workspace.PriorWorkProofs.Tutte
