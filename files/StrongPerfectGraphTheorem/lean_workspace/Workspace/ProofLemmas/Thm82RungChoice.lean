import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm82RungFamily
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph

/-!
# The first sentence of the printed proof of 8.2

PAPER (printed p. 40, opening of the proof of 8.2): *"For each edge `ij` of `J` choose an
`ij`-rung `R_ij`, arbitrarily for every edge of `J` different from `uv`, and such that `R_uv`
has length `≥ 1`; and let this choice of rungs form `L(H)`."*

Two things are being used here, both of them supplied by the paper itself rather than by 8.2:

* every edge of `J` **has** a rung — this is the third axiom of a `J`-strip system (*"For each
  `uv ∈ E(J)`, every vertex of `S_{uv}` is in a `uv`-rung"*) together with `S_{uv} ≠ ∅`, and it
  lets one choose `R_ij` "arbitrarily" away from `uv` while pinning `R_uv` to the prescribed
  rung of length `≥ 1`;
* the construction announced immediately after the proof of 8.1 (printed p. 39): *"For each
  edge `uv` of `J`, choose a `uv`-rung `R_{uv}`.  It follows from 8.1 and the final axiom above
  that the subgraph of `G` induced on the union of the vertex sets of these rungs is a line
  graph of a bipartite subdivision `H` of `J`.  For brevity we say that this choice of rungs
  forms `L(H)`."*  That is exactly `StripSystems.FormsLineGraph`.

So the content of this module is: *any* prescribed rung on one edge extends to a full choice of
rungs, and every choice of rungs forms an `L(H)`.

The first half is `ProofLemmas.Thm82RungFamily.exists_symmetric_rung_family` (proved); the
second half is `ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph` (cited).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm82RungChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- **"For each edge `ij` of `J` choose an `ij`-rung `R_ij`, … and let this choice of rungs form
`L(H)`."**

Given a prescribed `uv`-rung `R₀` (in the proof of 8.2, one of length `≥ 1`), there is a choice
of rungs `R` whose value at the edge `uv` is `R₀` and which forms `L(H)` for some bipartite
subdivision `H` of `J`. -/
theorem thm82RungChoice {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (u v : U) (huv : J.Adj u v) (R₀ : List V) (hR₀ : IsUVRung G J S N u v R₀) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V),
      FormsLineGraph G J S N R H ∧ R u v = R₀ := by
  -- *"For each edge `ij` of `J` choose an `ij`-rung `R_ij`, arbitrarily for every edge of `J`
  -- different from `uv`"*, pinning the value at `uv` to the prescribed rung `R₀`.  The family is
  -- edge-indexed: reversing the edge reverses the rung.
  obtain ⟨R, hR, hRrev, hRuv⟩ :=
    Thm82RungFamily.exists_symmetric_rung_family hSN huv hR₀
  -- *"and let this choice of rungs form `L(H)`"* — the construction announced after the proof
  -- of 8.1.
  obtain ⟨n, H, hforms⟩ :=
    Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph G hG J hJ S N hSN R hR
      hRrev
  exact ⟨n, H, R, hforms, hRuv⟩

end Workspace.ProofLemmas.Thm82RungChoice
