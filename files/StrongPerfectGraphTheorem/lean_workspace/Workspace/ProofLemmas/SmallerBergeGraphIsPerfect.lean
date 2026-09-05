import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge

/-!
# Minimality: every smaller Berge graph is perfect

Item P6 of the proof of 1.5.  `MinimumImperfect G` says that `G` is a counterexample
to *"perfect iff Berge"* on as few vertices as possible, the minimality being
expressed over `SimpleGraph (Fin n)`.  Unpacking it into the form the proof actually
uses takes two steps, and both are recorded here.

* `isPerfect_of_berge_of_card_lt` quantifies over an **arbitrary** finite vertex type
  `W`, because §5.2 applies it to `H`, a graph on a subtype of `V ⊕ Unit`.  This is
  exactly the transport that the `Fin n` form of `MinimumImperfect` demands, and it
  is why the proof needs `IsoTransport.exists_iso_fin`, `not_perfect_iff_berge_iso`,
  `berge_iso` and `isPerfect_iso`.
* `isPerfect_induce_of_ne_univ` is the special case for a *proper* induced subgraph
  of `G` itself; it additionally uses that `G` is Berge (P1, from
  `IsoTransport.minimumImperfect_berge` with the `thm_E5_perfect_implies_berge`
  axiom), `HoleBasics.berge_induce`, and `Fintype.card ↥X < Fintype.card V` for a
  proper subset `X`.

Used at §5.2 (for `H`) and at §6 (for `G|C` and `G|D`).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SmallerBergeGraphIsPerfect

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

/-- **(i)** If `G` is minimum imperfect, then every Berge graph on strictly fewer
vertices — on any finite vertex type whatsoever — is perfect. -/
theorem isPerfect_of_berge_of_card_lt {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : MinimumImperfect G) {W : Type*} [Fintype W] (K : SimpleGraph W)
    (hK : Berge K) (hcard : Fintype.card W < Fintype.card V) :
    IsPerfect K := by
  by_contra hnp
  -- `K` would be a counterexample to 1.2 on fewer vertices than `G`
  have hctr : ¬ (IsPerfect K ↔ Berge K) := fun hiff => hnp (hiff.mpr hK)
  obtain ⟨H, ⟨e⟩⟩ := IsoTransport.exists_iso_fin K
  have hH : ¬ (IsPerfect H ↔ Berge H) := (IsoTransport.not_perfect_iff_berge_iso e).mp hctr
  exact absurd (hG.2 (Fintype.card W) H hH) (by omega)

/-- **(ii)** If `G` is minimum imperfect, then every *proper* induced subgraph of `G`
is perfect. -/
theorem isPerfect_induce_of_ne_univ {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : MinimumImperfect G) {X : Set V} (hX : X ≠ Set.univ) :
    IsPerfect (G.induce X) := by
  classical
  -- P1: `G` is Berge, hence so is every induced subgraph
  have hBG : Berge G :=
    IsoTransport.minimumImperfect_berge hG
      (fun hp => Workspace.MainTheorem.SPGT.thm_E5_perfect_implies_berge G hp)
  have hBX : Berge (G.induce X) := HoleBasics.berge_induce hBG X
  -- `X` is a proper subset, so `|X| < |V|`
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ X := by
    by_contra h
    push Not at h
    exact hX (Set.eq_univ_of_forall h)
  have hcard : Fintype.card ↥X < Fintype.card V := Fintype.card_subtype_lt (p := (· ∈ X)) hv
  exact isPerfect_of_berge_of_card_lt hG _ hBX hcard

end Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
