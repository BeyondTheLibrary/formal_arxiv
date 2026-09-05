import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.CyclicThreeConnectedAttachments

/-!
# A track through a component, joining two of its attachments

5.3's closing paragraph: *"If say `a₁, b₁` are attachments, **choose a track `P` between `a₁, b₁`
with interior in `F`**"*.

`F` is a component of `H \ V(J)` and `u₁, u₂` are two of its attachments — vertices of `V(J)`
each with a neighbour in `F`.  Walking inside `F` from one neighbour to the other and hanging
`u₁`, `u₂` on the two ends gives the track.  Its interior is exactly the walk's vertex list, so
it lies in `F`; and since `F` is disjoint from `V(J)`, the interior avoids `V(J)` — which is what
makes the six tracks of the resulting `K₄`-subdivision meet only at their ends.

The track has length at least `2`: the interior is non-empty, since `F` is non-empty and the two
attachments lie outside it.  That is what stops the constructed subdivision from degenerating in
the *opposite-side* case, where the four-cycle on the branch vertices would need the deleted edge
`a₁b₁`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.TrackThroughComponent

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-- **A track between two attachments of a connected set, with interior inside it.** -/
theorem exists_track_through_connected {H : SimpleGraph W} {F : Set W}
    (hF : ConnectedSet H F) {u₁ u₂ f₁ f₂ : W}
    (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (hu₁ : u₁ ∉ F) (hu₂ : u₂ ∉ F) (hne : u₁ ≠ u₂)
    (ha₁ : H.Adj u₁ f₁) (ha₂ : H.Adj u₂ f₂) :
    ∃ P : List W, IsTrackFrom H P u₁ u₂ ∧ 2 ≤ trackLength P ∧
      (∀ w ∈ trackInterior P, w ∈ F) := by
  classical
  obtain ⟨p⟩ := hF ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩
  -- a *path* of `H.induce F` from `f₁` to `f₂`
  obtain ⟨q, hqpath⟩ := p.toPath
  set L : List W := q.support.map Subtype.val with hLdef
  have hLmem : ∀ w ∈ L, w ∈ F := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hw
    exact x.2
  have hLnd : L.Nodup := hqpath.support_nodup.map Subtype.val_injective
  have hLne : L ≠ [] := by
    rw [hLdef]
    cases hcase : q.support with
    | nil => exact absurd hcase q.support_ne_nil
    | cons x t => simp
  have hLhead : L.head? = some f₁ := by
    rw [hLdef, List.head?_map, List.head?_eq_some_head q.support_ne_nil,
      SimpleGraph.Walk.head_support]
    rfl
  have hLlast : L.getLast? = some f₂ := by
    rw [hLdef, List.getLast?_map, List.getLast?_eq_some_getLast q.support_ne_nil,
      SimpleGraph.Walk.getLast_support]
    rfl
  have hLchain : List.IsChain H.Adj L := by
    rw [hLdef, List.isChain_map]
    exact q.isChain_adj_support
  -- assemble `u₁ :: L ++ [u₂]`
  have hheadapp : (L ++ [u₂]).head? = some f₁ := by rw [List.head?_append, hLhead]; rfl
  have hlastapp : (L ++ [u₂]).getLast? = some u₂ := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
  have hu₁L : u₁ ∉ L := fun h => hu₁ (hLmem u₁ h)
  have hu₂L : u₂ ∉ L := fun h => hu₂ (hLmem u₂ h)
  refine ⟨u₁ :: (L ++ [u₂]), ⟨⟨by simp, ?_, ?_⟩, rfl, ?_⟩, ?_, ?_⟩
  · -- `Nodup`
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hLnd, List.nodup_singleton _, ?_⟩⟩
    · intro hcon
      rcases List.mem_append.mp hcon with h | h
      · exact hu₁L h
      · exact hne (List.mem_singleton.mp h)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      rintro rfl
      exact hu₂L (hy ▸ hx)
  · -- adjacency along the list
    refine List.isChain_iff_getElem.mp (List.isChain_cons.mpr ⟨?_, ?_⟩)
    · intro y hy
      rw [Option.mem_def, hheadapp] at hy
      rw [← Option.some_injective _ hy]
      exact ha₁
    · refine List.isChain_append.mpr ⟨hLchain, List.isChain_singleton _, ?_⟩
      intro x hx y hy
      rw [Option.mem_def, hLlast] at hx
      rw [Option.mem_def, List.head?_singleton] at hy
      rw [← Option.some_injective _ hx, ← Option.some_injective _ hy]
      exact ha₂.symm
  · -- last vertex
    rw [List.getLast?_cons_of_ne_nil (by simp), hlastapp]
  · -- length
    have : 1 ≤ L.length := List.length_pos_iff.mpr hLne
    simp only [trackLength, List.length_cons, List.length_append]
    omega
  · -- interior
    intro w hw
    have hw' : w ∈ (L ++ [u₂]).dropLast := hw
    rw [List.dropLast_concat] at hw'
    exact hLmem w hw'

/-- **5.3, closing paragraph: the track supplied by a vertex outside `V(J)`.**

Given a vertex `v` outside `S` (`= V(J)`), the component `F` of `H \ S` containing it has, by
cyclic 3-connectivity, at least two attachments in `S`; a track through `F` between two of them
has its interior inside `F`, hence disjoint from `S`.

This packages `CyclicThreeConnectedAttachments.two_attachments_of_component` together with
`exists_track_through_connected`, and is the exact input the two constructions of 5.3's closing
paragraph need: two distinct vertices of `V(J)` joined by a track of length `≥ 2` meeting `V(J)`
only in its ends. -/
theorem exists_two_attachments_track [Fintype W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) (S : Set W) (hS : 2 ≤ S.ncard) {v : W} (hv : v ∉ S) :
    ∃ (u₁ u₂ : W) (P : List W), u₁ ∈ S ∧ u₂ ∈ S ∧ u₁ ≠ u₂ ∧
      IsTrackFrom H P u₁ u₂ ∧ 2 ≤ trackLength P ∧ (∀ w ∈ trackInterior P, w ∉ S) := by
  classical
  obtain ⟨F, hF, hvF⟩ := ComponentsOfSetBasics.exists_isComponent_mem H Sᶜ hv
  have hFS : ∀ w ∈ F, w ∉ S := fun w hw => hF.1 hw
  have hcard : 2 ≤ {w ∈ S | ∃ f ∈ F, H.Adj f w}.ncard :=
    CyclicThreeConnectedAttachments.two_attachments_of_component hc3 S F hF ⟨v, hvF⟩ hS
  obtain ⟨u₁, hu₁Att, u₂, hu₂Att, hne⟩ :=
    (Set.one_lt_ncard (s := {w ∈ S | ∃ f ∈ F, H.Adj f w}) (Set.toFinite _)).mp (by omega)
  obtain ⟨hu₁S, f₁, hf₁F, hadj₁⟩ := hu₁Att
  obtain ⟨hu₂S, f₂, hf₂F, hadj₂⟩ := hu₂Att
  obtain ⟨P, hP, hPlen, hPint⟩ :=
    exists_track_through_connected hF.2.1 hf₁F hf₂F (fun h => hFS u₁ h hu₁S)
      (fun h => hFS u₂ h hu₂S) hne hadj₁.symm hadj₂.symm
  exact ⟨u₁, u₂, P, hu₁S, hu₂S, hne, hP, hPlen, fun w hw => hFS w (hPint w hw)⟩

end Workspace.ProofLemmas.TrackThroughComponent
