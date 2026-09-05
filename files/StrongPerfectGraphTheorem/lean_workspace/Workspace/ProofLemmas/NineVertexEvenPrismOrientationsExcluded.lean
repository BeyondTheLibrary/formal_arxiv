import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.BergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile
import Workspace.ProofLemmas.SpanningNineVertexEvenPrismHasInducedDegreeBounds

set_option autoImplicit false

namespace Workspace.ProofLemmas.NineVertexEvenPrismOrientationsExcluded

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

theorem nineVertexEvenPrismOrientationsExcluded
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsLongPrism G s t R₁ R₂ R₃ ∧ IsOddPrism G s t R₁ R₂ R₃) :
    ¬ ((∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G a b P₁ P₂ P₃ ∧
          {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ P₃} = Set.univ) ∧
      Fintype.card V = 9) ∧
    ¬ ((∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism Gᶜ a b P₁ P₂ P₃ ∧
          {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ P₃} = Set.univ) ∧
      Fintype.card V = 9) := by
  classical
  constructor
  · rintro ⟨⟨a, b, P₁, P₂, P₃, heven, hcover⟩, hcard⟩
    rcases
        Workspace.ProofLemmas.BergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile.bergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile G hG hcard hprism with
      ⟨W, hWcard, hdegreeThree, hdegreeTwo⟩
    have hbounds :=
      Workspace.ProofLemmas.SpanningNineVertexEvenPrismHasInducedDegreeBounds G hcard
        ⟨a, b, P₁, P₂, P₃, heven, hcover⟩ W hWcard
    omega
  · rintro ⟨⟨a, b, P₁, P₂, P₃, heven, hcover⟩, hcard⟩
    rcases
        Workspace.ProofLemmas.BergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile.bergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile G hG hcard hprism with
      ⟨W, hWcard, hdegreeThree, hdegreeTwo⟩
    have hbounds :=
      Workspace.ProofLemmas.SpanningNineVertexEvenPrismHasInducedDegreeBounds Gᶜ hcard
        ⟨a, b, P₁, P₂, P₃, heven, hcover⟩ W hWcard
    rw [compl_compl] at hbounds
    have hdegreeTwoNonempty :
        {w : W |
          letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
          (G.induce W).degree w = 2}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h] at hdegreeTwo
      norm_num at hdegreeTwo
    rcases hdegreeTwoNonempty with ⟨w, hw⟩
    letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
    have hw' : (G.induce W).degree w = 2 := by
      simpa only [Set.mem_setOf_eq] using hw
    have hlower : 4 ≤ (G.induce W).degree w := hbounds.2 w
    omega

end Workspace.ProofLemmas.NineVertexEvenPrismOrientationsExcluded
