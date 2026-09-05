import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm82RungFamily
import Workspace.ProofLemmas.StripSystemBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.StripSystems.SPGT

/-- Two prescribed rungs on distinct edges incident with one vertex extend to one
edge-indexed symmetric family of rungs. -/
theorem TwoPrescribedSymmetricRungFamily
    {V U : Type*} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N)
    (u v w : U) (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w)
    (P Q : List V) (hP : IsUVRung G J S N u v P) (hQ : IsUVRung G J S N u w Q) :
    ∃ R : U → U → List V,
      (∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b)) ∧
      (∀ a b : U, J.Adj a b → R b a = (R a b).reverse) ∧
      R u v = P ∧ R u w = Q := by
  classical
  obtain ⟨Rs, hRs, -⟩ := Workspace.ProofLemmas.StripSystemBasics.exists_special_rungs hSN
  obtain ⟨f, hfinj⟩ : ∃ f : U → ℕ, Function.Injective f :=
    ⟨fun a => ((Fintype.equivFin U a : Fin (Fintype.card U)) : ℕ),
      fun a b h => (Fintype.equivFin U).injective (Fin.ext h)⟩
  refine ⟨fun a b =>
      if a = u ∧ b = v then P
      else if a = v ∧ b = u then P.reverse
      else if a = u ∧ b = w then Q
      else if a = w ∧ b = u then Q.reverse
      else if f a < f b then Rs a b else (Rs b a).reverse, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 h3 h4 _
    · obtain ⟨rfl, rfl⟩ := h1
      exact hP
    · obtain ⟨rfl, rfl⟩ := h2
      exact Workspace.ProofLemmas.Thm82RungFamily.rung_reverse hSN hP
    · obtain ⟨rfl, rfl⟩ := h3
      exact hQ
    · obtain ⟨rfl, rfl⟩ := h4
      exact Workspace.ProofLemmas.Thm82RungFamily.rung_reverse hSN hQ
    · exact hRs a b hab
    · exact Workspace.ProofLemmas.Thm82RungFamily.rung_reverse hSN (hRs b a hab.symm)
  · intro a b hab
    have hne : a ≠ b := hab.ne
    have hfab : f a ≠ f b := fun h => hne (hfinj h)
    dsimp only
    split_ifs <;> simp_all <;> omega
  · dsimp only
    rw [if_pos ⟨rfl, rfl⟩]
  · dsimp only
    simp [huv.ne, hvw.symm]

end Workspace.ProofLemmas
