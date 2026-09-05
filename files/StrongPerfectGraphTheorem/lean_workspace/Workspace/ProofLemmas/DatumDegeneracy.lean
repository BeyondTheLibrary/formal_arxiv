import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.SubdivisionDatumRealize
import Workspace.ProofLemmas.DegenerateK4Cycle

/-!
# Reading degeneracy off a datum one has built oneself

`SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum` hides both of its ends,
so a caller who has just been told *"the subgraph you built is degenerate"* cannot say which of
**its own** six tracks the degenerate four-cycle runs along.  Both remaining holes of 5.3 need
exactly that:

* the cross-track branch of Step 2 — *"There is therefore a cycle of `H'` with vertex set
  `{r₁, r_t, p_m, q_n}`"*, which is only usable once the four short tracks are identified among
  the six tracks of `H'` that were just constructed;
* the closing paragraph — *"the union of `P` and `J \ {a₁b₁, a₂b₂}` satisfies the theorem"*,
  whose nondegeneracy obligation is discharged by exhibiting two tracks that are too long.

The bridge is that `SubdivisionDatumRealize.dsubgraph` is a **named** subgraph with a public
adjacency (`dsubgraph_adj`, an `Iff.rfl`), so the four cycle edges can be pushed back onto the
given `T`.  The only missing link is that the four given branch-vertices really are
branch-vertices of the realized subgraph; that is `dbranch_mem_branchVertices`, proved by
running `SubdivisionCounting.range_subset_branchVertices` on `S.spanningCoe` (where the vertex
type is still `W`) and then transporting the neighbour count along `Subtype.val`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.DatumDegeneracy

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.SubdivisionDatumRealize

variable {W : Type*}

/-! ### The branch-vertices of the realized subgraph -/

/-- Every branch-vertex of a datum is a vertex of the subgraph the datum spans. -/
theorem mem_dverts {D : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum D ι T) (u : Fin 4) : ι u ∈ (dsubgraph D ι T hd).verts := by
  obtain ⟨v, hv⟩ : ∃ v : Fin 4, u ≠ v := by
    fin_cases u
    exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
  have hhead : (T u v).head? = some (ι u) := (hd.2.1 u v hv).2.1
  refine ⟨u, v, hv, List.mem_of_mem_head? ?_⟩
  rw [Option.mem_def, hhead]

/-- The branch-vertex `ι u`, read inside the subgraph the datum spans. -/
def dbranch {D : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum D ι T) (u : Fin 4) : ↥(dsubgraph D ι T hd).verts :=
  ⟨ι u, mem_dverts hd u⟩

@[simp] theorem dbranch_val {D : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum D ι T) (u : Fin 4) : ((dbranch hd u : ↥(dsubgraph D ι T hd).verts) : W) = ι u :=
  rfl

theorem dbranch_injective {D : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum D ι T) : Function.Injective (dbranch hd) := by
  intro x y hxy
  exact hd.1 (congrArg Subtype.val hxy)

/-- The four branch-vertices of a datum really are branch-vertices (degree `≥ 3`) of the
subgraph the datum spans. -/
theorem dbranch_mem_branchVertices [Finite W] {D : SimpleGraph W} {ι : Fin 4 → W}
    {T : Fin 4 → Fin 4 → List W} (hd : IsK4Datum D ι T) (u : Fin 4) :
    dbranch hd u ∈ branchVertices (dsubgraph D ι T hd).coe := by
  classical
  set S := dsubgraph D ι T hd with hS
  have hι := hd.1
  have htrack := hd.2.1
  have hlen := hd.2.2.1
  have hdisjint := hd.2.2.2.2.1
  have hnew := hd.2.2.2.2.2
  have htop' : ∀ x y : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj x y → x ≠ y := by
    intro x y h; rwa [SimpleGraph.top_adj] at h
  -- the six tracks are tracks of the *spanning* coercion, whose vertex type is still `W`
  have hspan : ∀ x y : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj x y →
      IsTrackFrom S.spanningCoe (T x y) (ι x) (ι y) := by
    intro x y hxy
    have hxy' := htop' x y hxy
    obtain ⟨⟨hne, hnd, hadj⟩, hh, hl⟩ := htrack x y hxy'
    refine ⟨⟨hne, hnd, ?_⟩, hh, hl⟩
    intro i hi
    show S.Adj _ _
    exact ⟨x, y, hxy', ⟨i, hi, rfl⟩⟩
  have hdeg4 : ∀ x : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet x).ncard :=
    three_le_degree_of_three_connected (⊤ : SimpleGraph (Fin 4)) k4_three_connected
  have hsub : Set.range ι ⊆ branchVertices S.spanningCoe :=
    range_subset_branchVertices hι hspan (fun x y h => hlen x y (htop' x y h))
      (fun x y x' y' h h' hs => hdisjint x y x' y' (htop' x y h) (htop' x' y' h') hs)
      (fun x y h => hnew x y (htop' x y h)) hdeg4
  have hcount : 3 ≤ (S.spanningCoe.neighborSet (ι u)).ncard := hsub ⟨u, rfl⟩
  -- transport the neighbour count along `Subtype.val`
  have himg : (Subtype.val : ↥S.verts → W) '' (S.coe.neighborSet (dbranch hd u))
      = S.spanningCoe.neighborSet (ι u) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hy' : S.Adj (ι u) y := hy
      exact ⟨⟨y, S.edge_vert hy'.symm⟩, hy', rfl⟩
  show 3 ≤ (S.coe.neighborSet (dbranch hd u)).ncard
  rw [← Set.ncard_image_of_injective (S.coe.neighborSet (dbranch hd u)) Subtype.val_injective,
    himg]
  exact hcount

/-! ### The degenerate four-cycle, read back onto the given tracks -/

/-- **The degenerate four-cycle of a datum-built subgraph, in terms of the given tracks.**

If the subgraph a datum spans has a degenerate appearance, then four of the six given tracks —
those joining the consecutive pairs of a four-cycle on the index set `Fin 4` — have exactly two
vertices. -/
theorem exists_degenerate_cycle_of_datum [Finite W] {D : SimpleGraph W} {ι : Fin 4 → W}
    {T : Fin 4 → Fin 4 → List W} (hd : IsK4Datum D ι T)
    (hdegen : DegenerateK4Appearance (dsubgraph D ι T hd).coe) :
    ∃ α β γ δ : Fin 4,
      α ≠ β ∧ α ≠ γ ∧ α ≠ δ ∧ β ≠ γ ∧ β ≠ δ ∧ γ ≠ δ ∧
      (T α β).length = 2 ∧ (T β γ).length = 2 ∧
      (T γ δ).length = 2 ∧ (T δ α).length = 2 := by
  classical
  set S := dsubgraph D ι T hd with hS
  obtain ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hbr⟩ := hdegen
  have dab : a ≠ b := by rintro rfl; simp at hnd
  have dac : a ≠ c := by rintro rfl; simp at hnd
  have dad : a ≠ d := by rintro rfl; simp at hnd
  have dbc : b ≠ c := by rintro rfl; simp at hnd
  have dbd : b ≠ d := by rintro rfl; simp at hnd
  have dcd : c ≠ d := by rintro rfl; simp at hnd
  -- the four branch-vertices exhaust the four cycle vertices
  have hA : Set.range (dbranch hd) ⊆ ({a, b, c, d} : Set ↥S.verts) :=
    fun _ ⟨u, hu⟩ => hbr (hu ▸ dbranch_mem_branchVertices hd u)
  have hcard1 : (Set.range (dbranch hd)).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (dbranch_injective hd), Set.ncard_univ]
    simp
  have hcard2 : ({a, b, c, d} : Set ↥S.verts).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [dab, dac, dad]),
      Set.ncard_insert_of_notMem (by simp [dbc, dbd]),
      Set.ncard_insert_of_notMem (by simp [dcd]), Set.ncard_singleton]
  have hrange : Set.range (dbranch hd) = ({a, b, c, d} : Set ↥S.verts) :=
    Set.eq_of_subset_of_ncard_le hA (by omega) (Set.toFinite _)
  obtain ⟨α, hα⟩ : a ∈ Set.range (dbranch hd) := by rw [hrange]; simp
  obtain ⟨β, hβ⟩ : b ∈ Set.range (dbranch hd) := by rw [hrange]; simp
  obtain ⟨γ, hγ⟩ : c ∈ Set.range (dbranch hd) := by rw [hrange]; simp
  obtain ⟨δ, hδ⟩ : d ∈ Set.range (dbranch hd) := by rw [hrange]; simp
  have iαβ : α ≠ β := fun h => dab (by rw [← hα, ← hβ, h])
  have iαγ : α ≠ γ := fun h => dac (by rw [← hα, ← hγ, h])
  have iαδ : α ≠ δ := fun h => dad (by rw [← hα, ← hδ, h])
  have iβγ : β ≠ γ := fun h => dbc (by rw [← hβ, ← hγ, h])
  have iβδ : β ≠ δ := fun h => dbd (by rw [← hβ, ← hδ, h])
  have iγδ : γ ≠ δ := fun h => dcd (by rw [← hγ, ← hδ, h])
  -- an edge of the realized subgraph between two branch-vertices lies on some given track,
  -- and hence is a whole track
  have hshort : ∀ x y : Fin 4, S.coe.Adj (dbranch hd x) (dbranch hd y) → (T x y).length = 2 := by
    intro x y hxy
    have hxy' : S.Adj (ι x) (ι y) := hxy
    obtain ⟨p, q, hpq, hmem⟩ := (dsubgraph_adj hd (ι x) (ι y)).mp hxy'
    exact DegenerateK4Cycle.short_track_of_mem_trackEdges hd.1 hd.2.1 hd.2.2.2.1
      hd.2.2.2.2.2 hpq hmem
  refine ⟨α, β, γ, δ, iαβ, iαγ, iαδ, iβγ, iβδ, iγδ, ?_, ?_, ?_, ?_⟩
  · exact hshort α β (by rw [hα, hβ]; exact hab)
  · exact hshort β γ (by rw [hβ, hγ]; exact hbc)
  · exact hshort γ δ (by rw [hγ, hδ]; exact hcd)
  · exact hshort δ α (by rw [hδ, hα]; exact hda)

/-! ### Two long tracks make the appearance nondegenerate -/

/-- **The combinatorial core.**  For four distinct indices of `Fin 4`, the two pairs that are
*not* consecutive on the cycle `α-β-γ-δ-α` are `{α,γ}` and `{β,δ}`, which are disjoint.  Since
`{0,1}` and `{0,2}` share the index `0`, they cannot both be non-consecutive: at least one of
them is a consecutive pair of the cycle. -/
theorem zero_one_or_zero_two_consecutive_aux :
    ∀ α β γ δ : Fin 4,
      α = β ∨ α = γ ∨ α = δ ∨ β = γ ∨ β = δ ∨ γ = δ ∨
      ((α = 0 ∧ β = 1) ∨ (α = 1 ∧ β = 0) ∨ (β = 0 ∧ γ = 1) ∨ (β = 1 ∧ γ = 0) ∨
       (γ = 0 ∧ δ = 1) ∨ (γ = 1 ∧ δ = 0) ∨ (δ = 0 ∧ α = 1) ∨ (δ = 1 ∧ α = 0)) ∨
      ((α = 0 ∧ β = 2) ∨ (α = 2 ∧ β = 0) ∨ (β = 0 ∧ γ = 2) ∨ (β = 2 ∧ γ = 0) ∨
       (γ = 0 ∧ δ = 2) ∨ (γ = 2 ∧ δ = 0) ∨ (δ = 0 ∧ α = 2) ∨ (δ = 2 ∧ α = 0)) := by
  intro α β γ δ
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;> simp

theorem zero_one_or_zero_two_consecutive (α β γ δ : Fin 4)
    (h1 : α ≠ β) (h2 : α ≠ γ) (h3 : α ≠ δ) (h4 : β ≠ γ) (h5 : β ≠ δ) (h6 : γ ≠ δ) :
    ((α = 0 ∧ β = 1) ∨ (α = 1 ∧ β = 0) ∨ (β = 0 ∧ γ = 1) ∨ (β = 1 ∧ γ = 0) ∨
     (γ = 0 ∧ δ = 1) ∨ (γ = 1 ∧ δ = 0) ∨ (δ = 0 ∧ α = 1) ∨ (δ = 1 ∧ α = 0)) ∨
    ((α = 0 ∧ β = 2) ∨ (α = 2 ∧ β = 0) ∨ (β = 0 ∧ γ = 2) ∨ (β = 2 ∧ γ = 0) ∨
     (γ = 0 ∧ δ = 2) ∨ (γ = 2 ∧ δ = 0) ∨ (δ = 0 ∧ α = 2) ∨ (δ = 2 ∧ α = 0)) := by
  rcases zero_one_or_zero_two_consecutive_aux α β γ δ with
    h | h | h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · exact absurd h h5
  · exact absurd h h6
  · exact Or.inl h
  · exact Or.inr h

/-- **A datum with two long tracks spans a nondegenerate appearance.**

A degenerate four-cycle forces the four tracks on its consecutive index pairs to have exactly
two vertices, and one of `{0,1}`, `{0,2}` is always such a pair. -/
theorem nondegenerate_of_two_long [Finite W] {D : SimpleGraph W} {ι : Fin 4 → W}
    {T : Fin 4 → Fin 4 → List W} (hd : IsK4Datum D ι T)
    (h01 : 3 ≤ (T 0 1).length) (h02 : 3 ≤ (T 0 2).length) :
    ¬ DegenerateK4Appearance (dsubgraph D ι T hd).coe := by
  intro hdegen
  obtain ⟨α, β, γ, δ, i1, i2, i3, i4, i5, i6, s1, s2, s3, s4⟩ :=
    exists_degenerate_cycle_of_datum hd hdegen
  have hrevlen : ∀ x y : Fin 4, x ≠ y → (T y x).length = (T x y).length := by
    intro x y hxy
    rw [hd.2.2.2.1 x y hxy, List.length_reverse]
  have key01 : (T 0 1).length ≠ 2 := by omega
  have key02 : (T 0 2).length ≠ 2 := by omega
  have key10 : (T 1 0).length ≠ 2 := by rw [hrevlen 0 1 (by decide)]; omega
  have key20 : (T 2 0).length ≠ 2 := by rw [hrevlen 0 2 (by decide)]; omega
  rcases zero_one_or_zero_two_consecutive α β γ δ i1 i2 i3 i4 i5 i6 with hc | hc <;>
    rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
      ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    subst e1 <;> subst e2 <;>
    first
      | exact key01 s1 | exact key01 s2 | exact key01 s3 | exact key01 s4
      | exact key10 s1 | exact key10 s2 | exact key10 s3 | exact key10 s4
      | exact key02 s1 | exact key02 s2 | exact key02 s3 | exact key02 s4
      | exact key20 s1 | exact key20 s2 | exact key20 s3 | exact key20 s4

end Workspace.ProofLemmas.DatumDegeneracy
