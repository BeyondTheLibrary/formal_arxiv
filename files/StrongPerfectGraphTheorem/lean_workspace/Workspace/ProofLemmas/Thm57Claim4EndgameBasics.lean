import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim4Basics

/-!
# 5.7 (4), last paragraph: two bookkeeping lemmas

The endgame of claim (4) needs two facts that carry no mathematics of their own.

* A connected set `U` has an edge from any proper nonempty "closed" subset to the rest — this
  is what produces the paper's edge *"`sv` of `H` such that `s ∈ V(S)` and
  `v ∈ V(H) \ (V(S) ∪ {a₃, b₃})`"*.
* A track that starts in a set `S` and stays inside a set `B` on which `S` is closed under
  taking neighbours lies entirely inside `S`.  This is the routine way the paper's *"since `S`
  is maximal"* is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm57Claim4EndgameBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Basics

variable {W : Type*}

/-- If `S ⊆ U`, `U` is connected, and some vertex of `U` is outside `S`, then some edge of the
graph leaves `S` inside `U`. -/
theorem exists_crossing_edge (G : SimpleGraph W) (U S : Set W)
    (hU : ConnectedSet G U) (hSU : S ⊆ U) {u w : W} (hu : u ∈ S) (hw : w ∈ U) (hwS : w ∉ S) :
    ∃ p ∈ S, ∃ q ∈ U, q ∉ S ∧ G.Adj p q := by
  by_contra hcon
  push_neg at hcon
  have hclose : ∀ p, p ∈ S → ∀ q, q ∈ U → G.Adj p q → q ∈ S := by
    intro p hp q hq hadj
    by_contra hqS
    exact hcon p hp q hq hqS hadj
  have key : ∀ (a b : U), (G.induce U).Walk a b → (a : W) ∈ S → (b : W) ∈ S := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hs => ih (hclose _ hs _ (by exact Subtype.coe_prop _) h)
  obtain ⟨p⟩ := hU ⟨u, hSU hu⟩ ⟨w, hw⟩
  exact hwS (key _ _ p hu)

/-- A track starting inside `S` and staying inside `B` never leaves `S`, when `S` is closed
under `B`-neighbours. -/
theorem mem_of_track {G : SimpleGraph W} {S B : Set W}
    (hclose : ∀ p, p ∈ S → ∀ q, q ∈ B → G.Adj p q → q ∈ S)
    {R : List W} {p q : W} (hR : IsTrackFrom G R p q)
    (hRB : ∀ z ∈ R, z ∈ B) (hp : p ∈ S) : ∀ z ∈ R, z ∈ S := by
  have hne : 0 < R.length := List.length_pos_of_ne_nil hR.1.1
  have h0 : R[0]'hne = p := getElem_zero_of_head? hR.2.1 hne
  have key : ∀ n, ∀ hn : n < R.length, R[n]'hn ∈ S := by
    intro n
    induction n with
    | zero => intro hn; rw [h0]; exact hp
    | succ n ih =>
      intro hn
      exact hclose _ (ih (by omega)) _ (hRB _ (List.getElem_mem hn)) (hR.1.2.2 n hn)
  intro z hz
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hz
  exact key n hn

end Workspace.ProofLemmas.Thm57Claim4EndgameBasics
