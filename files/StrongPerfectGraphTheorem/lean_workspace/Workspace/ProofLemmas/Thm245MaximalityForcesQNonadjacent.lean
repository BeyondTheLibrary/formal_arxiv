import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false

namespace Workspace.Types.Thm245MaximalityForcesQNonadjacent

open Workspace.Types.Core.SPGT

theorem thm245MaximalityForcesQNonadjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Set V) (p : List V) (p₁ z q : V)
    (hX : AnticonnectedSet G X)
    (hXY : Disjoint X Y) (hcomp : Complete G X Y)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (hp₁ : p₁ ∈ p)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hzX : z ∉ X) (hzcomp : VertexComplete G z (X ∪ Y))
    (hmax : ∀ S : Set V, X ⊆ S →
      AnticonnectedSet G S →
      Disjoint S Y → Complete G S Y →
      (∀ w ∈ p, w ∉ S ∪ Y) →
      (∀ w ∈ p, (VertexComplete G w S ↔ w = p₁)) →
      z ∉ S → VertexComplete G z (S ∪ Y) →
      S = X)
    (hzp : ∀ w ∈ p, ¬ G.Adj z w)
    (hzq : G.Adj z q)
    (hqX : q ∉ X) (hqnotcomp : ¬ VertexComplete G q X)
    (hqY : VertexComplete G q Y) :
    ¬ G.Adj q p₁ := by
  intro hqp₁
  have hqnotp : q ∉ p := by
    intro hqp
    exact hzp q hqp hzq
  have hqnotY : q ∉ Y := by
    intro hqYmem
    exact G.irrefl (hqY q hqYmem)
  have hSanti : AnticonnectedSet G (X ∪ {q}) := by
    have hex : ∃ x ∈ X, ¬ G.Adj q x := by
      by_contra hnone
      apply hqnotcomp
      intro x hx
      by_contra hqx
      exact hnone ⟨x, hx, hqx⟩
    obtain ⟨x, hx, hqx⟩ := hex
    exact Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
      (G := Gᶜ) hX ⟨x, hx, ⟨by rintro rfl; exact hqX hx, hqx⟩⟩
  have hSY : Disjoint (X ∪ {q}) Y := by
    rw [Set.disjoint_left]
    intro v hvS hvY
    rcases hvS with hvX | hvq
    · exact Set.disjoint_left.mp hXY hvX hvY
    · exact hqnotY (Set.mem_singleton_iff.mp hvq ▸ hvY)
  have hScomp : Complete G (X ∪ {q}) Y := by
    intro v hvS y hy
    rcases hvS with hvX | hvq
    · exact hcomp v hvX y hy
    · exact Set.mem_singleton_iff.mp hvq ▸ hqY y hy
  have hpSY : ∀ w ∈ p, w ∉ (X ∪ {q}) ∪ Y := by
    intro w hw hmem
    rcases hmem with hwS | hwY
    · rcases hwS with hwX | hwq
      · exact hpXY w hw (Or.inl hwX)
      · exact hqnotp (Set.mem_singleton_iff.mp hwq ▸ hw)
    · exact hpXY w hw (Or.inr hwY)
  have hSuniq : ∀ w ∈ p, (VertexComplete G w (X ∪ {q}) ↔ w = p₁) := by
    intro w hw
    constructor
    · intro hwS
      exact (hXuniq w hw).mp (fun x hx => hwS x (Or.inl hx))
    · rintro rfl
      intro v hvS
      rcases hvS with hvX | hvq
      · exact (hXuniq w hw).mpr rfl v hvX
      · exact Set.mem_singleton_iff.mp hvq ▸ hqp₁.symm
  have hzS : z ∉ X ∪ {q} := by
    intro hzmem
    rcases hzmem with hzmem | hzqeq
    · exact hzX hzmem
    · exact G.irrefl (Set.mem_singleton_iff.mp hzqeq ▸ hzq)
  have hzScomp : VertexComplete G z ((X ∪ {q}) ∪ Y) := by
    intro v hv
    rcases hv with hvS | hvY
    · rcases hvS with hvX | hvq
      · exact hzcomp v (Or.inl hvX)
      · exact Set.mem_singleton_iff.mp hvq ▸ hzq
    · exact hzcomp v (Or.inr hvY)
  have heq : X ∪ {q} = X :=
    hmax (X ∪ {q}) Set.subset_union_left hSanti hSY hScomp hpSY hSuniq hzS hzScomp
  have hqmem : q ∈ X ∪ {q} := Or.inr rfl
  rw [heq] at hqmem
  exact hqX hqmem

end Workspace.Types.Thm245MaximalityForcesQNonadjacent
