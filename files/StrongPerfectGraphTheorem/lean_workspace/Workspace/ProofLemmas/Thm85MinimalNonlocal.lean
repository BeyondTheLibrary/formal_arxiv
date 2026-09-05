import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems

/-!
# 8.5, the reduction to a minimal `F`

PAPER (printed p. 42, second sentence of the proof of 8.5): *"Let `X` be the set of attachments
of `F` in `V(S,N)`, and suppose for a contradiction that `X` is not local.  **We may assume that
`F` is minimal (connected) with this property.**"*

Since `V(G)` is finite, a connected set whose attachment set is not local contains a *minimal*
such set: choose one of least cardinality.  Minimality is used twice in the printed proof — in
(2) (*"The minimality of `F` implies that there is a path `P` with `V(P) = F` …"*) and after (3)
(*"from the minimality of `F` it follows that `F` is the vertex set of a path"*).

The minimal set is automatically nonempty: the attachment set of `∅` is `∅`, which is local
(`∅ ⊆ N_v` for any vertex `v` of `J`, and `J` — being 3-connected — has a vertex).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85MinimalNonlocal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- **"We may assume that `F` is minimal (connected) with this property."**  (Proof of 8.5,
printed p. 42.) -/
theorem thm85MinimalNonlocal {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (F : Set V) (hFconn : ConnectedSet G F)
    (hFnotlocal :
      ¬ LocalForStripSystem J S N (attachments G F (stripSystemVertices J S))) :
    ∃ F₀ : Set V, F₀ ⊆ F ∧ F₀.Nonempty ∧ ConnectedSet G F₀ ∧
      ¬ LocalForStripSystem J S N (attachments G F₀ (stripSystemVertices J S)) ∧
      ∀ F₁ : Set V, F₁ ⊆ F₀ → ConnectedSet G F₁ →
        ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) →
        F₁ = F₀ := by
  classical
  set 𝒮 : Set (Set V) :=
    {F' : Set V | F' ⊆ F ∧ ConnectedSet G F' ∧
      ¬ LocalForStripSystem J S N (attachments G F' (stripSystemVertices J S))} with h𝒮
  have hne : 𝒮.Nonempty := ⟨F, subset_rfl, hFconn, hFnotlocal⟩
  obtain ⟨F₀, hF₀, hmin⟩ := Set.exists_min_image 𝒮 Set.ncard (Set.toFinite _) hne
  refine ⟨F₀, hF₀.1, ?_, hF₀.2.1, hF₀.2.2, ?_⟩
  · rcases Set.eq_empty_or_nonempty F₀ with h | h
    · exfalso
      apply hF₀.2.2
      have hcard : 3 < Fintype.card U := hJ.1
      have hU : Nonempty U := Fintype.card_pos_iff.mp (by omega)
      refine Or.inl ⟨Classical.arbitrary U, ?_⟩
      intro x hx
      simp only [h, attachments, IsAttachment, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        false_and, exists_false, and_false] at hx
    · exact h
  · intro F₁ h1 h2 h3
    exact Set.eq_of_subset_of_ncard_le h1 (hmin F₁ ⟨h1.trans hF₀.1, h2, h3⟩) (Set.toFinite _)

end Workspace.ProofLemmas.Thm85MinimalNonlocal
