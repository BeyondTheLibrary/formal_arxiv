import Mathlib
import Workspace.Types.Core

/-!
# 7.5: `W = (Nc₁ \ {r₁}) ∪ (Nc₂ \ {r₂})` is anticonnected

PAPER (proof of 7.5, printed p. 38): *"Let `W = (Nc₁ \ {r₁}) ∪ (Nc₂ \ {r₂})`.  Then `W ⊆ X₁` by
(3), and since there are no edges between `Nc₁` and `Nc₂`, it follows that `W` has exactly two
components, both cliques.  In particular, `W` is anticonnected."*

The step "in particular, `W` is anticonnected" needs only the anticompleteness: in the complement
the two parts are *complete* to each other, so any two vertices of `W` are joined by a path of
length at most two in `Ḡ|W`.  (The cliqueness of the two parts is what the paper uses separately,
for the last hypothesis of 4.6.)
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75AnticonnectedUnion

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- A union of two nonempty mutually anticomplete sets is anticonnected. -/
theorem thm75AnticonnectedUnion {V : Type*} (G : SimpleGraph V) (P Q : Set V)
    (hPQ : Anticomplete G P Q) (hPne : P.Nonempty) (hQne : Q.Nonempty) :
    AnticonnectedSet G (P ∪ Q) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hPne
  obtain ⟨q₀, hq₀⟩ := hQne
  have hq₀mem : q₀ ∈ P ∪ Q := Or.inr hq₀
  have hp₀mem : p₀ ∈ P ∪ Q := Or.inl hp₀
  -- an element of `P` is joined to `q₀` in `Ḡ|(P ∪ Q)`
  have hPreach : ∀ a : ↥(P ∪ Q), (a : V) ∈ P →
      (Gᶜ.induce (P ∪ Q)).Reachable a ⟨q₀, hq₀mem⟩ := by
    intro a ha
    by_cases hEq : (a : V) = q₀
    · exact (Subtype.ext hEq : a = ⟨q₀, hq₀mem⟩) ▸ SimpleGraph.Reachable.refl a
    · exact SimpleGraph.Adj.reachable (by
        refine ⟨hEq, ?_⟩
        exact hPQ (a : V) ha q₀ hq₀)
  -- an element of `Q` is joined to `p₀`, hence to `q₀`
  have hQreach : ∀ a : ↥(P ∪ Q), (a : V) ∈ Q →
      (Gᶜ.induce (P ∪ Q)).Reachable a ⟨q₀, hq₀mem⟩ := by
    intro a ha
    have h1 : (Gᶜ.induce (P ∪ Q)).Reachable a ⟨p₀, hp₀mem⟩ := by
      by_cases hEq : (a : V) = p₀
      · exact (Subtype.ext hEq : a = ⟨p₀, hp₀mem⟩) ▸ SimpleGraph.Reachable.refl a
      · exact SimpleGraph.Adj.reachable (by
          refine ⟨hEq, ?_⟩
          intro hadj
          exact hPQ p₀ hp₀ (a : V) ha hadj.symm)
    exact h1.trans (hPreach ⟨p₀, hp₀mem⟩ hp₀)
  intro a b
  have ha := a.2
  have hb := b.2
  have hareach : (Gᶜ.induce (P ∪ Q)).Reachable a ⟨q₀, hq₀mem⟩ := by
    rcases ha with h | h
    · exact hPreach a h
    · exact hQreach a h
  have hbreach : (Gᶜ.induce (P ∪ Q)).Reachable b ⟨q₀, hq₀mem⟩ := by
    rcases hb with h | h
    · exact hPreach b h
    · exact hQreach b h
  exact hareach.trans hbreach.symm

end Workspace.ProofLemmas.Thm75AnticonnectedUnion
