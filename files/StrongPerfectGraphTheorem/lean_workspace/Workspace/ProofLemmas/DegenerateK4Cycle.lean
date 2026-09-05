import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum

/-!
# The four short tracks of a degenerate `K₄`-subdivision

`Workspace.ProofLemmas.DegenerateK4Tracks` extracts, from a degenerate `K₄`-subdivision, the two
*diagonal* tracks that 5.3 calls `P` and `Q`.  It deliberately never proves that the four tracks
along the degenerate four-cycle have length one, because the extraction does not need it.

**Step 2 of 5.3 does need it.**  The paper's *"There is therefore a cycle of `H'` with vertex set
`{r₁, r_t, p_m, q_n}`.  Since `H` is bipartite and `p_mq_n` is an edge, it follows that `t = 2`"*
works by knowing exactly which four of the six tracks of the second subdivision `H'` are single
edges: that is what pins `t = 2`, `r₁ = p_{m-1}`, `r₂ = q_{n-1}`.  This module supplies it.

The engine is `adj_branch_forces_short_track`: **an edge of the subdivision joining two
branch-vertices is a whole track**.  Both of its ends lie in `Set.range ι`, and the interior of
every track misses `Set.range ι`, so neither end is an internal vertex of the track carrying that
edge — and `SubdivisionCounting.track_edge_len_two` then says that track has exactly two
vertices.  Injectivity of `ι` identifies it as the track between the two given branch-vertices.

This is the one place in §5 where the *edge-set* clause of `IsSubdivision`
(`D.edgeSet = ⋃ trackEdges (T u v)`) is genuinely used; everything else in the section goes
through the six local clauses of `Workspace.ProofLemmas.SubdivisionDatum.IsK4Datum`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.DegenerateK4Cycle

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.SubdivisionDatum

variable {X : Type*}

/-- **An edge between two branch-vertices of a subdivision of `K₄` is a whole track.**

If `ι p` and `ι q` are adjacent in `D`, then the track `T p q` joining them has exactly two
vertices, i.e. length `1`. -/
theorem adj_branch_forces_short_track {D : SimpleGraph X}
    {ι : Fin 4 → X} {T : Fin 4 → Fin 4 → List X}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
      IsTrackFrom D (T u v) (ι u) (ι v))
    (hrev : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v → T v u = (T u v).reverse)
    (hnew : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
      ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : D.edgeSet =
      ⋃ (u : Fin 4) (v : Fin 4) (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v), trackEdges (T u v))
    {p q : Fin 4} (hadj : D.Adj (ι p) (ι q)) :
    (T p q).length = 2 := by
  have hmem : s(ι p, ι q) ∈ D.edgeSet := hadj
  rw [hedges] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨u, v, huv, i, hi, heq⟩ := hmem
  -- both ends of the edge are branch-vertices, so neither is internal to its track
  have hrng : (T u v)[i]'(by omega) ∈ Set.range ι ∧ (T u v)[i + 1]'hi ∈ Set.range ι := by
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨p, h1⟩, ⟨q, h2⟩⟩
    · exact ⟨⟨q, h2⟩, ⟨p, h1⟩⟩
  have hlen2 : (T u v).length = 2 :=
    track_edge_len_two (T u v) i hi (fun hc => hnew u v huv _ hc hrng.1)
      (fun hc => hnew u v huv _ hc hrng.2)
  have hieq : i = 0 := by omega
  have hA : (T u v)[i]'(by omega) = ι u :=
    (getElem_eq_of_index_eq (T u v) hieq (by omega) (by omega)).trans
      (track_head (htrack u v huv) (by omega))
  have hB : (T u v)[i + 1]'hi = ι v :=
    (getElem_eq_of_index_eq (T u v) (show i + 1 = 1 from by omega) hi (by omega)).trans
      (track_last (htrack u v huv) hlen2)
  have heq2 : s(ι p, ι q) = s(ι u, ι v) := by rw [heq, hA, hB]
  rcases Sym2.eq_iff.mp heq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rfl, rfl⟩ : p = u ∧ q = v := ⟨hι h1, hι h2⟩
    exact hlen2
  · obtain ⟨rfl, rfl⟩ : p = v ∧ q = u := ⟨hι h1, hι h2⟩
    rw [hrev q p huv, List.length_reverse]
    exact hlen2

/-- **The same fact, phrased for an `IsK4Datum` rather than a full `IsSubdivision`.**

`adj_branch_forces_short_track` reads the edge off the `edgeSet = ⋃ trackEdges` clause; when one
has built the subdivision oneself the edge is already known to lie on a *named* track, and only
this "rest" of the argument is needed.  This is the form that turns *"there is a cycle of `H'`
with vertex set `{r₁, r_t, p_m, q_n}`"* into statements about the six tracks one constructed —
without needing uniqueness of the subdivision structure.

Note the `u ≠ v` phrasing, so it consumes a `SubdivisionDatum.IsK4Datum` directly. -/
theorem short_track_of_mem_trackEdges {D : SimpleGraph X}
    {ι : Fin 4 → X} {T : Fin 4 → Fin 4 → List X}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : Fin 4, u ≠ v → IsTrackFrom D (T u v) (ι u) (ι v))
    (hrev : ∀ u v : Fin 4, u ≠ v → T v u = (T u v).reverse)
    (hnew : ∀ u v : Fin 4, u ≠ v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    {p q u v : Fin 4} (huv : u ≠ v) (hmem : s(ι p, ι q) ∈ trackEdges (T u v)) :
    (T p q).length = 2 := by
  obtain ⟨i, hi, heq⟩ := hmem
  have hrng : (T u v)[i]'(by omega) ∈ Set.range ι ∧ (T u v)[i + 1]'hi ∈ Set.range ι := by
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨p, h1⟩, ⟨q, h2⟩⟩
    · exact ⟨⟨q, h2⟩, ⟨p, h1⟩⟩
  have hlen2 : (T u v).length = 2 :=
    track_edge_len_two (T u v) i hi (fun hc => hnew u v huv _ hc hrng.1)
      (fun hc => hnew u v huv _ hc hrng.2)
  have hieq : i = 0 := by omega
  have hA : (T u v)[i]'(by omega) = ι u :=
    (getElem_eq_of_index_eq (T u v) hieq (by omega) (by omega)).trans
      (track_head (htrack u v huv) (by omega))
  have hB : (T u v)[i + 1]'hi = ι v :=
    (getElem_eq_of_index_eq (T u v) (show i + 1 = 1 from by omega) hi (by omega)).trans
      (track_last (htrack u v huv) hlen2)
  have heq2 : s(ι p, ι q) = s(ι u, ι v) := by rw [heq, hA, hB]
  rcases Sym2.eq_iff.mp heq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rfl, rfl⟩ : p = u ∧ q = v := ⟨hι h1, hι h2⟩
    exact hlen2
  · obtain ⟨rfl, rfl⟩ : p = v ∧ q = u := ⟨hι h1, hι h2⟩
    rw [hrev q p huv, List.length_reverse]
    exact hlen2

/-- **The degenerate four-cycle, labelled.**

A degenerate `K₄`-subdivision `D` carries four pairwise distinct branch indices `α, β, γ, δ`
whose four *consecutive* tracks each have exactly two vertices.  The two remaining ("diagonal")
tracks `T α γ` and `T β δ` are the `P` and `Q` of
`Workspace.ProofLemmas.DegenerateK4Tracks.exists_two_tracks_of_degenerate`. -/
theorem exists_degenerate_cycle_tracks [Finite X] {D : SimpleGraph X}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) D)
    (hdegen : DegenerateK4Appearance D) :
    ∃ (ι : Fin 4 → X) (T : Fin 4 → Fin 4 → List X) (α β γ δ : Fin 4),
      IsK4Datum D ι T ∧
      α ≠ β ∧ α ≠ γ ∧ α ≠ δ ∧ β ≠ γ ∧ β ≠ δ ∧ γ ≠ δ ∧
      (T α β).length = 2 ∧ (T β γ).length = 2 ∧
      (T γ δ).length = 2 ∧ (T δ α).length = 2 := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  obtain ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hbr⟩ := hdegen
  have dab : a ≠ b := by rintro rfl; simp at hnd
  have dac : a ≠ c := by rintro rfl; simp at hnd
  have dad : a ≠ d := by rintro rfl; simp at hnd
  have dbc : b ≠ c := by rintro rfl; simp at hnd
  have dbd : b ≠ d := by rintro rfl; simp at hnd
  have dcd : c ≠ d := by rintro rfl; simp at hnd
  -- the four cycle vertices are exactly the four branch-vertices
  have hdeg4 : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    three_le_degree_of_three_connected (⊤ : SimpleGraph (Fin 4)) k4_three_connected
  have hA : Set.range ι ⊆ branchVertices D :=
    range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg4
  have hcard1 : (Set.range ι).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hι, Set.ncard_univ]
    simp
  have hcard2 : ({a, b, c, d} : Set X).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [dab, dac, dad]),
      Set.ncard_insert_of_notMem (by simp [dbc, dbd]),
      Set.ncard_insert_of_notMem (by simp [dcd]), Set.ncard_singleton]
  have hrange : Set.range ι = ({a, b, c, d} : Set X) :=
    Set.eq_of_subset_of_ncard_le (hA.trans hbr) (by omega) (Set.toFinite _)
  obtain ⟨α, hα⟩ : a ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨β, hβ⟩ : b ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨γ, hγ⟩ : c ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨δ, hδ⟩ : d ∈ Set.range ι := by rw [hrange]; simp
  have iαβ : α ≠ β := fun h => dab (by rw [← hα, ← hβ, h])
  have iαγ : α ≠ γ := fun h => dac (by rw [← hα, ← hγ, h])
  have iαδ : α ≠ δ := fun h => dad (by rw [← hα, ← hδ, h])
  have iβγ : β ≠ γ := fun h => dbc (by rw [← hβ, ← hγ, h])
  have iβδ : β ≠ δ := fun h => dbd (by rw [← hβ, ← hδ, h])
  have iγδ : γ ≠ δ := fun h => dcd (by rw [← hγ, ← hδ, h])
  have htop : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv; rw [SimpleGraph.top_adj]; exact huv
  have hshort : ∀ p q : Fin 4, D.Adj (ι p) (ι q) → (T p q).length = 2 := fun p q hpq =>
    adj_branch_forces_short_track hι htrack hrev hnew hedges hpq
  refine ⟨ι, T, α, β, γ, δ, ⟨hι, fun u v huv => htrack u v (htop u v huv),
    fun u v huv => hlen u v (htop u v huv), fun u v huv => hrev u v (htop u v huv),
    fun u v u' v' huv huv' hs => hdisjint u v u' v' (htop u v huv) (htop u' v' huv') hs,
    fun u v huv => hnew u v (htop u v huv)⟩,
    iαβ, iαγ, iαδ, iβγ, iβδ, iγδ, ?_, ?_, ?_, ?_⟩
  · exact hshort α β (by rw [hα, hβ]; exact hab)
  · exact hshort β γ (by rw [hβ, hγ]; exact hbc)
  · exact hshort γ δ (by rw [hγ, hδ]; exact hcd)
  · exact hshort δ α (by rw [hδ, hα]; exact hda)

end Workspace.ProofLemmas.DegenerateK4Cycle
