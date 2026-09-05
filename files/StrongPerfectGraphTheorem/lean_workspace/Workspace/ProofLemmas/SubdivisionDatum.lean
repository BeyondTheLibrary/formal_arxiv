import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# `K₄`-subdivision data: the part of `IsSubdivision` that survives composition

The first sentence of the proof of 5.3 needs a `K₄`-subdivision *inside* `H`, obtained by
applying Dirac's theorem (`Workspace.PriorWork.DiracK4Subdivision`) to the 3-connected graph
`J` that `H` subdivides and then pushing the result up through `IsSubdivision J H`.  `H` itself
does **not** satisfy Dirac's hypothesis — the internal vertices of its tracks have degree `2`.

`Types.Tracks.SPGT.IsSubdivision J K` has eight clauses.  Six of them are *local* — they talk
only about the embedding `ι` and the tracks `T u v` — while the last two,

* `∀ w, (∃ u, w = ι u) ∨ ∃ u v, J.Adj u v ∧ w ∈ trackInterior (T u v)`  (the cover clause), and
* `K.edgeSet = ⋃ u v (_ : J.Adj u v), trackEdges (T u v)`  (the edge-set clause),

are *exactness* clauses: they pin the data down to an ambient graph that is **exactly** the
subdivision and nothing more.  Those are precisely the two clauses that break when one composes
a subdivision with a subdivision, or transports a subdivision into a larger host graph.

So this module introduces the six-clause remainder as `IsK4Datum` / `HasK4Datum`, and proves

* `hasK4Datum_of_isSubdivision` — every `K₄`-subdivision *is* a datum (forget two clauses);
* `hasK4Datum_of_injHom` — a datum transports along any injective graph homomorphism;
* `hasK4Datum_of_subgraph_subdivision` — **(A)** a subgraph of `H` which is a `K₄`-subdivision
  gives a datum in `H` itself.

The converse direction — turning a datum back into an honest `S : H.Subgraph` with
`IsSubdivision K₄ S.coe` — is **(B)**, and lives in `Workspace.ProofLemmas.SubdivisionDatumRealize`.
The composition **(C)** lives in `Workspace.ProofLemmas.SubdivisionCompose`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SubdivisionDatum

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

/-! ### Pushing a track along an injective homomorphism -/

/-- A track maps to a track along any injective graph homomorphism.
(`SubdivisionCounting.isTrackFrom_map` is the special case of an isomorphism; here the map need
not be surjective and need not reflect adjacency, which is what a *subgraph* inclusion gives.) -/
theorem isTrackFrom_of_injHom {X W : Type*} {D : SimpleGraph X} {H : SimpleGraph W}
    (f : X → W) (hinj : Function.Injective f)
    (hf : ∀ x y : X, D.Adj x y → H.Adj (f x) (f y))
    {q : List X} {a b : X} (h : IsTrackFrom D q a b) :
    IsTrackFrom H (q.map f) (f a) (f b) := by
  obtain ⟨⟨hne, hnd, hadj⟩, hh, hl⟩ := h
  have hne' : q.map f ≠ [] := by
    cases q with
    | nil => exact absurd rfl hne
    | cons x t => exact List.cons_ne_nil _ _
  refine ⟨⟨hne', hnd.map hinj, ?_⟩, ?_, ?_⟩
  · intro i hi
    have hi' : i + 1 < q.length := by simpa using hi
    simp only [List.getElem_map]
    exact hf _ _ (hadj i hi')
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, hl]; rfl

/-! ### The datum -/

/-- **A `K₄`-subdivision datum in `D`**: the six *local* clauses of
`IsSubdivision (⊤ : SimpleGraph (Fin 4)) D`, with the two exactness clauses (cover, edge-set)
dropped.  Informally: four distinct branch-vertices `ι 0, …, ι 3` of `D`, joined pairwise by
six tracks of `D` that meet only at their ends. -/
def IsK4Datum {X : Type*} (D : SimpleGraph X) (ι : Fin 4 → X)
    (T : Fin 4 → Fin 4 → List X) : Prop :=
  Function.Injective ι ∧
  (∀ u v : Fin 4, u ≠ v → IsTrackFrom D (T u v) (ι u) (ι v)) ∧
  (∀ u v : Fin 4, u ≠ v → 1 ≤ trackLength (T u v)) ∧
  (∀ u v : Fin 4, u ≠ v → T v u = (T u v).reverse) ∧
  (∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' → s(u, v) ≠ s(u', v') →
    ∀ w ∈ trackInterior (T u v), w ∉ T u' v') ∧
  (∀ u v : Fin 4, u ≠ v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)

/-- `D` carries a `K₄`-subdivision datum. -/
def HasK4Datum {X : Type*} (D : SimpleGraph X) : Prop :=
  ∃ (ι : Fin 4 → X) (T : Fin 4 → Fin 4 → List X), IsK4Datum D ι T

/-- A `K₄`-subdivision is in particular a `K₄`-subdivision datum: forget the two exactness
clauses. -/
theorem hasK4Datum_of_isSubdivision {X : Type*} {D : SimpleGraph X}
    (h : IsSubdivision (⊤ : SimpleGraph (Fin 4)) D) : HasK4Datum D := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, -, -⟩ := h
  have top : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv; rw [SimpleGraph.top_adj]; exact huv
  exact ⟨ι, T, hι, fun u v h => htrack u v (top u v h),
    fun u v h => hlen u v (top u v h), fun u v h => hrev u v (top u v h),
    fun u v u' v' h h' hs => hdisjint u v u' v' (top u v h) (top u' v' h') hs,
    fun u v h => hnew u v (top u v h)⟩

/-- **A datum transports along an injective graph homomorphism.**

This is what makes the datum the right intermediate object: none of its six clauses mentions
the ambient graph beyond "these consecutive vertices are adjacent", so all six survive being
moved into a larger host graph.  Neither exactness clause would. -/
theorem hasK4Datum_of_injHom {X W : Type*} {D : SimpleGraph X} {H : SimpleGraph W}
    (f : X → W) (hinj : Function.Injective f)
    (hf : ∀ x y : X, D.Adj x y → H.Adj (f x) (f y))
    (h : HasK4Datum D) : HasK4Datum H := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew⟩ := h
  refine ⟨fun u => f (ι u), fun u v => (T u v).map f, hinj.comp hι, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact isTrackFrom_of_injHom f hinj hf (htrack u v huv)
  · intro u v huv
    have := hlen u v huv
    simp only [trackLength, List.length_map] at *
    omega
  · intro u v huv
    show (T v u).map f = ((T u v).map f).reverse
    rw [hrev u v huv, List.map_reverse]
  · intro u v u' v' huv huv' hs w hw hmem
    rw [trackInterior_map] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
    obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hmem
    exact hdisjint u v u' v' huv huv' hs w₀ hw₀ (by rw [← hinj hzw]; exact hz)
  · intro u v huv w hw hrng
    rw [trackInterior_map] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
    obtain ⟨k, hk⟩ := hrng
    exact hnew u v huv w₀ hw₀ ⟨k, hinj hk⟩

/-- **(A)** A subgraph of `H` which is a subdivision of `K₄` yields a `K₄`-subdivision datum in
`H` itself.  This is the form in which Dirac's theorem — whose conclusion is
`∃ S : J.Subgraph, IsSubdivision K₄ S.coe` — enters the composition. -/
theorem hasK4Datum_of_subgraph_subdivision {W : Type*} {H : SimpleGraph W} (S : H.Subgraph)
    (h : IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe) : HasK4Datum H :=
  hasK4Datum_of_injHom Subtype.val Subtype.val_injective (fun _ _ hxy => S.adj_sub hxy)
    (hasK4Datum_of_isSubdivision h)

end Workspace.ProofLemmas.SubdivisionDatum
