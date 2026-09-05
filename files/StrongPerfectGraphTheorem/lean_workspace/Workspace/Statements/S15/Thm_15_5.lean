import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm155HoleCases

set_option autoImplicit false

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_15_5 (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (hC : IsHoleList G C)
    (X : Set V) (hXC : ∀ x ∈ X, x ∉ C) (hXanti : AnticonnectedSet G X)
    (P : List V) (u v : V) (hP : IsPathFrom G P u v)
    (hPC : ∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k)
    (hPlen : 1 < pathLength P)
    (hu : VertexComplete G u X) (hv : VertexComplete G v X)
    (hint : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w X) :
    Even (pathLength P) := by
  -- *"The claim is trivial if `C` has length 4, so we assume it has length ≥ 6."*
  -- `G ∈ F₆ ⊆ F₃` is Berge, so `holeLength C` is even; a hole has length `≥ 4`;
  -- hence the length is `4` or at least `6`.
  have hBerge : Berge G := hG.1.1.1
  have heven : Even (holeLength C) := hBerge.1 C hC
  have hge4 : 4 ≤ holeLength C := hC.1
  rcases Nat.lt_or_ge (holeLength C) 6 with hlt | hge
  · have h4 : holeLength C = 4 := by
      obtain ⟨m, hm⟩ := heven
      omega
    exact Workspace.ProofLemmas.Thm155HoleCases.even_of_holeLength_four G C hC h4 P hP.1 hPC hPlen
  · exact Workspace.ProofLemmas.Thm155HoleCases.even_of_holeLength_ge_six G hG C hC hge X hXC
      hXanti P u v hP hPC hPlen hu hv hint


end SPGT

end Workspace.Statements.S15
