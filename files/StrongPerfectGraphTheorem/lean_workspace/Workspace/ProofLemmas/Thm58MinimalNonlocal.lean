import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The minimal connected set in the proof of 5.8

This is the finite-set reduction in the first sentence of the proof of 5.8 after its statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58MinimalNonlocal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: *"We may assume `F` is minimal such that its set of attachments is not local."* -/
theorem thm58MinimalNonlocal
    (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (F : Set V) (hFconn : ConnectedSet G F)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K}) :
    ∃ F₀ : Set V, F₀ ⊆ F ∧ F₀.Nonempty ∧ ConnectedSet G F₀ ∧
      ¬ LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ attachments G F₀ K} ∧
      ∀ F₁ : Set V, F₁ ⊆ F₀ → ConnectedSet G F₁ →
        ¬ LocalForLineGraph H
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
            (↑(φ ⟨e, he⟩) : V) ∈ attachments G F₁ K} →
        F₁ = F₀ := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdegree : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard := fun u =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hrange : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdegree
  set families : Set (Set V) :=
    {F' : Set V | F' ⊆ F ∧ ConnectedSet G F' ∧
      ¬ LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ attachments G F' K}} with hfamilies
  have hnonempty : families.Nonempty := ⟨F, subset_rfl, hFconn, hnotlocal⟩
  obtain ⟨F₀, hF₀, hmin⟩ :=
    Set.exists_min_image families Set.ncard (Set.toFinite _) hnonempty
  refine ⟨F₀, hF₀.1, ?_, hF₀.2.1, hF₀.2.2, ?_⟩
  · rcases Set.eq_empty_or_nonempty F₀ with hempty | hne
    · exfalso
      apply hF₀.2.2
      have hcard : 3 < m := by simpa using hJ.1
      let u : Fin m := ⟨0, by omega⟩
      refine Or.inl ⟨ι u, hrange ⟨u, rfl⟩, ?_⟩
      · intro e he
        simp only [hempty, attachments, IsAttachment, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, false_and, exists_false, and_false] at he
    · exact hne
  · intro F₁ hsub hconn hbad
    exact Set.eq_of_subset_of_ncard_le hsub
      (hmin F₁ ⟨hsub.trans hF₀.1, hconn, hbad⟩) (Set.toFinite _)

end Workspace.ProofLemmas.Thm58MinimalNonlocal
