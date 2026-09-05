import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# 7.5 claim (2): a minimal `F` is disjoint from `L(H)`

PAPER (proof of 7.5, claim (2), printed p. 36):

*"From the minimality of `F` it also follows that `F` is disjoint from `L(H)`; for any vertex of
`F` in `L(H)` would be in `S` or `T`, since it is not in `X₁`, and then we could make `F` shorter
by omitting this vertex."*

`hmin` is the paper's *"minimality of `F`"* read contrapositively: it is the induction hypothesis
of claim (2) on `|F|`, specialised to proper subsets of `F` with the SAME appearance, and it is
supplied by the caller (`Workspace.ProofLemmas.Thm75Claim2Generalised`) from the `by_cases` that
opens the inductive step.

The conclusion is exactly the hypothesis `hFK : F ⊆ Kᶜ` that 5.8 needs, and it is also what makes
the paper's next sentence — *"Consequently `F ∩ X = ∅`"* — a one-liner at the call site (a vertex
of `F ∩ X` would lie in `X \ K = X₀`, which `hFdisj` forbids).

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2FAvoidsLineGraph

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- If `F` is inclusion-minimal among connected sets attached to two anticomplete sides, then
`F` misses the first side.  Starting at a hypothetical vertex of the first side and following
an induced path in `F` to a neighbour of the second side, deleting the first vertex of that
path gives a smaller admissible connected set. -/
private theorem minimal_connected_avoids_left {V : Type*} (G : SimpleGraph V)
    (A B F Z : Set V) (hFconn : ConnectedSet G F) (hanti : Anticomplete G A B)
    (hFZ : ∀ x ∈ F, x ∉ Z)
    (hB : ∃ b ∈ B, ∃ f ∈ F, G.Adj b f)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
      (∀ x ∈ F', x ∉ Z) → (∃ a ∈ A, ∃ f ∈ F', G.Adj a f) →
      (∃ b ∈ B, ∃ f ∈ F', G.Adj b f) → False) :
    ∀ x ∈ F, x ∉ A := by
  classical
  intro x hxF hxA
  obtain ⟨b, hbB, f, hfF, hbf⟩ := hB
  have hxf : x ≠ f := by
    intro h
    subst f
    exact hanti x hxA b hbB hbf.symm
  obtain ⟨p, hp, hpF⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
      hFconn hxF hfF
  have hpos : 0 < p.length := Workspace.ProofLemmas.PathBasics.path_length_pos hp.1
  have hzero : p[0]'hpos = x :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = f :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hlen₂ : 2 ≤ p.length := by
    by_contra hnot
    apply hxf
    rw [← hzero, ← hlast]
    exact hp.1.2.1.getElem_inj_iff.mpr (by omega)
  have htailPath : IsPathList G p.tail := by
    rw [← List.drop_one]
    exact Workspace.ProofLemmas.PathBasics.isPathList_drop hp.1 (by omega)
  let F' : Set V := {z : V | z ∈ p.tail}
  have hF'sub : F' ⊆ F := by
    intro z hz
    exact hpF z (List.mem_of_mem_tail hz)
  have hcons : x :: p.tail = p := List.cons_head?_tail hp.2.1
  have hxTail : x ∉ p.tail := by
    have hnd := hp.1.2.1
    rw [← hcons, List.nodup_cons] at hnd
    exact hnd.1
  have hF'ne : F' ≠ F := by
    intro heq
    have hxF' : x ∈ F' := by rw [heq]; exact hxF
    exact hxTail hxF'
  have hF'conn : ConnectedSet G F' :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htailPath
  have hp₁Tail : p[1]'(by omega) ∈ p.tail := by
    have htpos : 0 < p.tail.length := by simp; omega
    have heq : p.tail[0]'htpos = p[1]'(by omega) := by simp
    rw [← heq]
    exact List.getElem_mem _
  have hxp₁ : G.Adj x (p[1]'(by omega)) := by
    have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hp.1
      (show 0 + 1 < p.length by omega)
    rw [hzero] at hadj
    exact hadj
  have hfTail : f ∈ p.tail := by
    have hfp : f ∈ p := by rw [← hlast]; exact List.getElem_mem _
    rw [← hcons] at hfp
    simp only [List.mem_cons] at hfp
    exact hfp.resolve_left hxf.symm
  exact hmin F' hF'sub hF'ne hF'conn
    (fun z hz => hFZ z (hF'sub hz))
    ⟨x, hxA, p[1]'(by omega), hp₁Tail, hxp₁⟩
    ⟨b, hbB, f, hfTail, hbf⟩

/-- **A minimal `F` is disjoint from `V(L(H)) = K`** (printed p. 36). -/
theorem thm75Claim2FAvoidsLineGraph {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (Y X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (F : Set V) (hFconn : ConnectedSet G F) (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f) (hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f)
    (hSTanti : Anticomplete G S T)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
      (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
      (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False) :
    ∀ x ∈ F, x ∉ K := by
  have hnoS : ∀ x ∈ F, x ∉ S :=
    minimal_connected_avoids_left G S T F (X₀ ∪ X₁ ∪ Y) hFconn hSTanti hFdisj hTF hmin
  have hTSanti : Anticomplete G T S := by
    intro t ht s hs hts
    exact hSTanti s hs t ht hts.symm
  have hnoT : ∀ x ∈ F, x ∉ T :=
    minimal_connected_avoids_left G T S F (X₀ ∪ X₁ ∪ Y) hFconn hTSanti hFdisj hSF
      (fun F' hsub hne hconn hdisj hTF' hSF' => hmin F' hsub hne hconn hdisj hSF' hTF')
  intro x hxF hxK
  have hxX₁ : x ∉ X₁ := fun hx => hFdisj x hxF (Or.inl (Or.inr hx))
  by_cases hxR : x ∈ Rset
  · exact hnoS x hxF (by rw [hS]; exact ⟨hxR, hxX₁⟩)
  · exact hnoT x hxF (by rw [hT]; exact ⟨⟨hxK, hxR⟩, hxX₁⟩)

end Workspace.ProofLemmas.Thm75Claim2FAvoidsLineGraph
