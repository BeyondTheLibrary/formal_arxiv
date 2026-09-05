import Workspace.ProofLemmas.Thm175Claim3Size
import Workspace.ProofLemmas.Thm175Claim3Structure
import Workspace.ProofLemmas.Thm175Symmetry

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim3Main

open Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "There is an antipath `x₁-⋯-x_s-y₁-⋯-y_t` such that
`s,t > 1` and `X = {x₁,…,x_s}`, and `Y = {y₁,…,y_t}`."
This assembles the size argument, the two non-cut arguments, and the unique
cross-pair. Its list conclusion avoids an import cycle with `Thm175Claims`. -/
theorem blocks (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁))
    (hsfirst : ∀ w ∈ (swapCounterexample G z c hfirst).core.p,
      (VertexComplete G w (swapCounterexample G z c hfirst).X ↔
        w = (swapCounterexample G z c hfirst).core.p₁))
    (hc : ∀ a ∈ c.X, ∀ b ∈ c.X, a ≠ b →
      AnticonnectedSet G (c.X \ {a}) → AnticonnectedSet G (c.X \ {b}) →
      Disjoint c.X c.Y ∧
        ((∀ v ∈ c.X, ((∃ y ∈ c.Y, ¬ G.Adj v y) ↔ v = a)) ∨
         (∀ v ∈ c.X, ((∃ y ∈ c.Y, ¬ G.Adj v y) ↔ v = b))))
    (hsc : ∀ a ∈ c.Y, ∀ b ∈ c.Y, a ≠ b →
      AnticonnectedSet G (c.Y \ {a}) → AnticonnectedSet G (c.Y \ {b}) →
      Disjoint c.Y c.X ∧
        ((∀ v ∈ c.Y, ((∃ y ∈ c.X, ¬ G.Adj v y) ↔ v = a)) ∨
         (∀ v ∈ c.Y, ((∃ y ∈ c.X, ¬ G.Adj v y) ↔ v = b)))) :
    ∃ p q : List V, ∃ a b : V,
      1 < p.length ∧ 1 < q.length ∧ p.head? = some a ∧ q.getLast? = some b ∧
      IsAntipathFrom G (p ++ q) a b ∧
      (∀ v, v ∈ p ↔ v ∈ c.X) ∧ (∀ v, v ∈ q ↔ v ∈ c.Y) := by
  have hX := Thm175Claim3Size.not_subsingleton G hG z c hfirst
  have hY : ¬ c.Y.Subsingleton :=
    Thm175Claim3Size.not_subsingleton G hG z (swapCounterexample G z c hfirst) hsfirst
  obtain ⟨p, a, x, hp, hpl, hpX, hd, hx⟩ :=
    Thm175Claim3Structure.one_block G c.X c.Y c.hXa hX hc
  obtain ⟨q, b, y, hq, hql, hqY, _, hy⟩ :=
    Thm175Claim3Structure.one_block G c.Y c.X c.hYa hY hsc
  refine ⟨p, q.reverse, a, b, hpl, ?_, hp.2.1, ?_, ?_, hpX, ?_⟩
  · simpa using hql
  · simpa using hq.2.1
  · exact Thm175Claim3Structure.join_blocks G c.X c.Y p q a x b y hp hq hpX hqY hd hx hy
  · intro v
    simpa using hqY v

end Workspace.ProofLemmas.Thm175Claim3Main
