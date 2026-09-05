import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.AppearanceVertexTypeTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84GluedTransport

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem glued_transport {U Wt : Type*} [Finite Wt]
    (G : SimpleGraph V) (J : SimpleGraph U) (K : Set V) (Hs : SimpleGraph Wt)
    (hsub : IsSubdivision J Hs) (hbip : Hs.IsBipartite)
    (hiso : Nonempty (Hs.lineGraph ≃g G.induce K)) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision J H ∧ Nonempty (H.lineGraph ≃g G.induce K) := by
  classical
  letI : Fintype Wt := Fintype.ofFinite Wt
  obtain ⟨H, ⟨ψ⟩⟩ := Workspace.ProofLemmas.IsoTransport.exists_iso_fin Hs
  obtain ⟨φ⟩ := hiso
  exact ⟨Fintype.card Wt, H,
    Thm75Claim2Transport.isBipartiteSubdivision_map ψ ⟨hsub, hbip⟩,
    ⟨(Thm75Claim2Transport.lineGraphIso ψ).symm.trans φ⟩⟩

end Workspace.ProofLemmas.Thm84GluedTransport
