import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# Realizing a `K₄`-subdivision datum as an honest subgraph

This is step **(B)** of the chain that supplies the first sentence of the proof of 5.3.
`Workspace.ProofLemmas.SubdivisionDatum` isolated the six *local* clauses of
`IsSubdivision (⊤ : SimpleGraph (Fin 4)) _` as `HasK4Datum`, precisely because those are the
clauses that survive transport and composition.  Here we go back: a datum in `H` is realized by
an honest `S : H.Subgraph` with `IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe`.

The subgraph is the obvious one — the union of the six tracks:

```
S.verts = {w | ∃ u v, u ≠ v ∧ w ∈ T u v}      S.Adj x y = ∃ u v, u ≠ v ∧ s(x,y) ∈ E(T u v)
```

and the two *exactness* clauses (`cover`, `edgeSet = ⋃ trackEdges`) then hold essentially by
construction.  The work is all in the other direction: every one of the six local clauses is a
statement about lists in the **subtype** `↥S.verts`, and has to be transported down to the
corresponding statement about lists in `W`.

The device that makes that painless is `List.attachWith`: for `u ≠ v` we set
`P u v := (T u v).attachWith (· ∈ S.verts) _`, whose only relevant property is
`(P u v).map Subtype.val = T u v` (`List.attachWith_map_subtype_val`).  Every clause is then
proved by pushing it along `Subtype.val` and using injectivity — and, crucially, all index
transfer is done through **`getElem?`**, which carries no proof term, so no rewrite ever hits
the "motive is not type correct" wall that `getElem` rewrites do.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SubdivisionDatumRealize

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.SubdivisionDatum

variable {W : Type*}

/-- Some index of `Fin 4` other than `u`. -/
private def other (u : Fin 4) : Fin 4 := if u = 0 then 1 else 0

private theorem other_ne (u : Fin 4) : u ≠ other u := by
  unfold other
  split_ifs with h
  · subst h; decide
  · exact h

/-- The vertex set of the subgraph a datum spans. -/
private def dverts (T : Fin 4 → Fin 4 → List W) : Set W :=
  {w | ∃ u v : Fin 4, u ≠ v ∧ w ∈ T u v}

/-- The adjacency of the subgraph a datum spans. -/
private def dadj (T : Fin 4 → Fin 4 → List W) (x y : W) : Prop :=
  ∃ u v : Fin 4, u ≠ v ∧ s(x, y) ∈ trackEdges (T u v)

/-- The subgraph of `H` spanned by the six tracks of a datum.

Public, so that a caller who built the datum can recognise the subgraph it gets back: see
`dsubgraph_adj` and `dsubgraph_verts`.  Without that, a caller holding
`DegenerateK4Appearance S.coe` has no way to relate the degenerate four-cycle to the `ι`, `T`
it constructed. -/
def dsubgraph (H : SimpleGraph W) (ι : Fin 4 → W) (T : Fin 4 → Fin 4 → List W)
    (hd : IsK4Datum H ι T) : H.Subgraph where
  verts := dverts T
  Adj := dadj T
  adj_sub := by
    rintro x y ⟨u, v, huv, i, hi, heq⟩
    have hadj := (hd.2.1 u v huv).1.2.2 i hi
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hadj
    · rw [h1, h2]; exact hadj.symm
  edge_vert := by
    rintro x y ⟨u, v, huv, i, hi, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨u, v, huv, by rw [h1]; exact List.getElem_mem _⟩
    · exact ⟨u, v, huv, by rw [h1]; exact List.getElem_mem _⟩
  symm := by
    rintro x y ⟨u, v, huv, he⟩
    exact ⟨u, v, huv, by rwa [Sym2.eq_swap]⟩

/-- The six tracks, read inside the subtype `↥S.verts`. -/
private def dtracks (H : SimpleGraph W) (ι : Fin 4 → W) (T : Fin 4 → Fin 4 → List W)
    (hd : IsK4Datum H ι T) (u v : Fin 4) : List ↥(dsubgraph H ι T hd).verts :=
  if huv : u ≠ v then
    (T u v).attachWith (· ∈ (dsubgraph H ι T hd).verts) (fun _w hw => ⟨u, v, huv, hw⟩)
  else []

/-- **(B), named form.**  The subgraph a datum spans really is a subdivision of `K₄`.

This is the whole content of `exists_subgraph_isSubdivision_of_hasK4Datum` below, stated about
the *named* subgraph `dsubgraph H ι T hd` so that the caller keeps hold of `ι` and `T`. -/
theorem isSubdivision_dsubgraph {H : SimpleGraph W} {ι : Fin 4 → W}
    {T : Fin 4 → Fin 4 → List W} (hd : IsK4Datum H ι T) :
    IsSubdivision (⊤ : SimpleGraph (Fin 4)) (dsubgraph H ι T hd).coe := by
  classical
  have hι := hd.1
  have htrack := hd.2.1
  have hlen := hd.2.2.1
  have hrev := hd.2.2.2.1
  have hdisjint := hd.2.2.2.2.1
  have hnew := hd.2.2.2.2.2
  have hlen2 : ∀ u v : Fin 4, u ≠ v → 2 ≤ (T u v).length := by
    intro u v huv
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  -- the subgraph and its tracks
  set S := dsubgraph H ι T hd with hS
  set P := dtracks H ι T hd with hP
  -- the single property of `attachWith` we use
  have hmapP : ∀ u v : Fin 4, u ≠ v → (P u v).map Subtype.val = T u v := by
    intro u v huv
    rw [hP]
    unfold dtracks
    rw [dif_pos huv]
    exact List.attachWith_map_subtype_val _
  have hlenP : ∀ u v : Fin 4, u ≠ v → (P u v).length = (T u v).length := by
    intro u v huv
    rw [← hmapP u v huv, List.length_map]
  -- index transfer, through `getElem?` so that no proof term is ever rewritten
  have hgetP : ∀ (u v : Fin 4), u ≠ v → ∀ (i : ℕ) (hi : i < (P u v).length)
      (hi' : i < (T u v).length), (((P u v)[i]'hi : ↥S.verts) : W) = (T u v)[i]'hi' := by
    intro u v huv i hi hi'
    have h2 : ((P u v)[i]?).map Subtype.val = (T u v)[i]? := by
      rw [← List.getElem?_map, hmapP u v huv]
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at h2
    simpa using h2
  -- membership and interior transfer
  have hmemP : ∀ (u v : Fin 4), u ≠ v → ∀ z : ↥S.verts, z ∈ P u v ↔ (z : W) ∈ T u v := by
    intro u v huv z
    constructor
    · intro hz
      rw [← hmapP u v huv]
      exact List.mem_map_of_mem hz
    · intro hz
      rw [← hmapP u v huv] at hz
      obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hz
      exact (Subtype.ext hyz : y = z) ▸ hy
  have hintP : ∀ (u v : Fin 4), u ≠ v → ∀ z : ↥S.verts,
      z ∈ trackInterior (P u v) ↔ (z : W) ∈ trackInterior (T u v) := by
    intro u v huv z
    have hkey : trackInterior (T u v) = (trackInterior (P u v)).map Subtype.val := by
      rw [← hmapP u v huv, trackInterior_map]
    constructor
    · intro hz
      rw [hkey]
      exact List.mem_map_of_mem hz
    · intro hz
      rw [hkey] at hz
      obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hz
      exact (Subtype.ext hyz : y = z) ▸ hy
  -- edges of a track transfer
  have hedgeP : ∀ (u v : Fin 4), u ≠ v → ∀ a b : ↥S.verts,
      (s(a, b) ∈ trackEdges (P u v) ↔ s((a : W), (b : W)) ∈ trackEdges (T u v)) := by
    intro u v huv a b
    constructor
    · rintro ⟨i, hi, heq⟩
      have hi' : i + 1 < (T u v).length := by rw [← hlenP u v huv]; exact hi
      refine ⟨i, hi', ?_⟩
      have := congrArg (Sym2.map (Subtype.val : ↥S.verts → W)) heq
      simpa [Sym2.map_mk, hgetP u v huv i (by omega) (by omega),
        hgetP u v huv (i + 1) hi hi'] using this
    · rintro ⟨i, hi, heq⟩
      have hi' : i + 1 < (P u v).length := by rw [hlenP u v huv]; exact hi
      refine ⟨i, hi', ?_⟩
      apply Sym2.map.injective (Subtype.val_injective : Function.Injective
        (Subtype.val : ↥S.verts → W))
      simpa [Sym2.map_mk, hgetP u v huv i (by omega) (by omega),
        hgetP u v huv (i + 1) hi' hi] using heq
  -- the branch-vertex embedding
  have hιmem : ∀ u : Fin 4, ι u ∈ S.verts := by
    intro u
    refine ⟨u, other u, other_ne u, ?_⟩
    have h0 : (T u (other u))[0]'(by have := hlen2 u (other u) (other_ne u); omega) = ι u :=
      track_head (htrack u (other u) (other_ne u)) (by have := hlen2 u (other u) (other_ne u); omega)
    exact h0 ▸ List.getElem_mem _
  have htop : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv; rw [SimpleGraph.top_adj]; exact huv
  have htop' : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v → u ≠ v := by
    intro u v huv; rwa [SimpleGraph.top_adj] at huv
  refine ⟨fun u => (⟨ι u, hιmem u⟩ : ↥S.verts), P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity of the embedding
    intro x y hxy
    exact hι (congrArg Subtype.val hxy)
  · -- each `P u v` is a track of `S.coe` from `ι u` to `ι v`
    intro u v huv'
    have huv := htop' u v huv'
    have hL : 2 ≤ (P u v).length := by rw [hlenP u v huv]; exact hlen2 u v huv
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro hc
      rw [hc] at hL
      simp at hL
    · have := (htrack u v huv).1.2.1
      rw [← hmapP u v huv] at this
      exact List.Nodup.of_map _ this
    · intro i hi
      have hi' : i + 1 < (T u v).length := by rw [← hlenP u v huv]; exact hi
      refine ⟨u, v, huv, i, hi', ?_⟩
      rw [Sym2.eq_iff]
      exact Or.inl ⟨hgetP u v huv i (by omega) (by omega), hgetP u v huv (i + 1) hi hi'⟩
    · have h2 : ((P u v).head?).map Subtype.val = (T u v).head? := by
        rw [← List.head?_map, hmapP u v huv]
      rw [(htrack u v huv).2.1] at h2
      cases hcase : (P u v).head? with
      | none => rw [hcase] at h2; simp at h2
      | some z =>
          rw [hcase] at h2
          simp only [Option.map_some] at h2
          exact congrArg some (Subtype.ext (Option.some_injective _ h2))
    · have h2 : ((P u v).getLast?).map Subtype.val = (T u v).getLast? := by
        rw [← List.getLast?_map, hmapP u v huv]
      rw [(htrack u v huv).2.2] at h2
      cases hcase : (P u v).getLast? with
      | none => rw [hcase] at h2; simp at h2
      | some z =>
          rw [hcase] at h2
          simp only [Option.map_some] at h2
          exact congrArg some (Subtype.ext (Option.some_injective _ h2))
  · -- positive length
    intro u v huv'
    have huv := htop' u v huv'
    have := hlen u v huv
    simp only [trackLength] at *
    rw [hlenP u v huv]
    omega
  · -- reversal
    intro u v huv'
    have huv := htop' u v huv'
    apply List.map_injective_iff.mpr (Subtype.val_injective : Function.Injective
      (Subtype.val : ↥S.verts → W))
    rw [hmapP v u (Ne.symm huv), List.map_reverse, hmapP u v huv, hrev u v huv]
  · -- interiors miss the other tracks
    intro u v u' v' huv' huv'' hs w hw hmem
    have huv := htop' u v huv'
    have hu'v' := htop' u' v' huv''
    exact hdisjint u v u' v' huv hu'v' hs (w : W) ((hintP u v huv w).mp hw)
      ((hmemP u' v' hu'v' w).mp hmem)
  · -- interiors are new vertices
    intro u v huv' w hw hrng
    have huv := htop' u v huv'
    obtain ⟨k, hk⟩ := hrng
    exact hnew u v huv (w : W) ((hintP u v huv w).mp hw) ⟨k, congrArg Subtype.val hk⟩
  · -- cover
    intro w
    obtain ⟨u, v, huv, hw⟩ := w.2
    by_cases hint : (w : W) ∈ trackInterior (T u v)
    · exact Or.inr ⟨u, v, htop u v huv, (hintP u v huv w).mpr hint⟩
    · refine Or.inl ?_
      rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior hw hint
          (by have := hlen2 u v huv; omega) with hend | hend
      · refine ⟨u, Subtype.ext ?_⟩
        show (w : W) = ι u
        rw [hend]
        exact track_head (htrack u v huv) (by have := hlen2 u v huv; omega)
      · refine ⟨v, Subtype.ext ?_⟩
        show (w : W) = ι v
        rw [hend]
        exact Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack u v huv)
          (by have := hlen2 u v huv; omega)
  · -- edge set
    ext e
    induction e using Sym2.ind with
    | _ a b =>
        simp only [SimpleGraph.mem_edgeSet, Set.mem_iUnion]
        constructor
        · rintro ⟨u, v, huv, he⟩
          exact ⟨u, v, htop u v huv, (hedgeP u v huv a b).mpr he⟩
        · rintro ⟨u, v, huv', he⟩
          have huv := htop' u v huv'
          exact ⟨u, v, huv, (hedgeP u v huv a b).mp he⟩

/-- **(B)** A `K₄`-subdivision datum in `H` is realized by a subgraph of `H` which is a
subdivision of `K₄`. -/
theorem exists_subgraph_isSubdivision_of_hasK4Datum {H : SimpleGraph W} (h : HasK4Datum H) :
    ∃ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe := by
  obtain ⟨ι, T, hd⟩ := h
  exact ⟨dsubgraph H ι T hd, isSubdivision_dsubgraph hd⟩

/-- The adjacency of the subgraph a datum spans, by construction. -/
theorem dsubgraph_adj {H : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum H ι T) (x y : W) :
    (dsubgraph H ι T hd).Adj x y ↔ ∃ u v : Fin 4, u ≠ v ∧ s(x, y) ∈ trackEdges (T u v) :=
  Iff.rfl

/-- The vertex set of the subgraph a datum spans, by construction. -/
theorem dsubgraph_verts {H : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
    (hd : IsK4Datum H ι T) :
    (dsubgraph H ι T hd).verts = {w : W | ∃ u v : Fin 4, u ≠ v ∧ w ∈ T u v} :=
  rfl

end Workspace.ProofLemmas.SubdivisionDatumRealize
