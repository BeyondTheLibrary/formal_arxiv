import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm101ThetaOfPrismAux

/-!
# A prism is the line graph of a theta graph — in full generality

This is the general form of `Workspace.ProofLemmas.NinePrismLineGraph`, and the first of the
five modules that decompose `Workspace.ProofLemmas.Thm101CaseOneK4AppearanceWitness`.

## What it discharges

Half of the printed sentence 10.1.1 (printed p. 56):

> *"… and (therefore) `G` has an induced subgraph which is the line graph of a bipartite
> subdivision of `K₄`."*

Before the `f`-branch is attached, the prism `K` alone is already the line graph of a
**theta graph** `Θ`: two branch-vertices `x, y` joined by three internally disjoint tracks
`Q 0, Q 1, Q 2`, the track `Q i` having `pathLength (R i) + 1` edges — one edge for each of
the `pathLength (R i) + 1 = |R i|` vertices of the rung `R i`.  Counting vertices,

  `|V(Θ)| = 2 + Σᵢ (|Q i| - 2) = pathLength (R 0) + pathLength (R 1) + pathLength (R 2) + 2`,

which is the index type below.  (For the nine-vertex even prism all three `pathLength (R i)`
are `2`, giving `Fin 8` — exactly `NinePrismLineGraph.theta`.)

## Which `decide` this generalises

`NinePrismLineGraph` fixes `pathLength (R i) = 2` and therefore gets to check the whole
correspondence by kernel evaluation.  This module replaces **three** of its `decide`s:

* `NinePrismLineGraph.psi_mem` (`by revert p; decide`) — "each of the nine listed pairs really
  is an edge of `theta`" — becomes the `IsTrackFrom` clause of `IsThetaDatum` plus the
  edge-set clause `Θ.edgeSet = ⋃ i, trackEdges (Q i)`.
* `NinePrismLineGraph.psiE_inj` (`by decide`) and the cardinality `decide` inside
  `psiE_bij` — "the nine edges are pairwise distinct and exhaust `E(theta)`" — become the
  pairwise-disjointness clause (`i ≠ j → no internal vertex of `Q i` lies on `Q j`) together
  with the covering clause of `IsThetaDatum`.
* the `decide` closing `NinePrismLineGraph.prismIsoLine.map_rel_iff'` — "two of the nine edges
  of `theta` share an end exactly when the corresponding prism vertices are adjacent" — is
  the conclusion here: the isomorphism `φ : Θ.lineGraph ≃g G.induce K` together with the
  explicit index correspondence *"the `k`-th edge of `Q i` is the vertex `(R i)[k]`"*.

Nothing below is specific to §10; it is stated in prism generality so that other sections may
cite it.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.ThetaData

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT

/-- **The theta graph, as a datum.**

`IsThetaDatum Θ x y Q` says that the graph `Θ` consists of exactly two distinguished vertices
`x ≠ y` joined by three tracks `Q 0, Q 1, Q 2`, each with at least one edge, that are disjoint
except at their common ends `x, y`, and that between them use up every vertex and every edge
of `Θ`.

This is the intrinsic (`decide`-free) description of `NinePrismLineGraph.theta`. -/
def IsThetaDatum {m : ℕ} (Θ : SimpleGraph (Fin m)) (x y : Fin m)
    (Q : Fin 3 → List (Fin m)) : Prop :=
  x ≠ y ∧
  (∀ i : Fin 3, IsTrackFrom Θ (Q i) x y) ∧
  (∀ i : Fin 3, 2 ≤ (Q i).length) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ v ∈ trackInterior (Q i), v ∉ Q j) ∧
  (∀ i : Fin 3, ∀ v ∈ trackInterior (Q i), v ≠ x ∧ v ≠ y) ∧
  (∀ v : Fin m, v = x ∨ v = y ∨ ∃ i : Fin 3, v ∈ trackInterior (Q i)) ∧
  Θ.edgeSet = ⋃ i : Fin 3, trackEdges (Q i)

/-- **A theta graph presenting a prism as its line graph.**

On top of `IsThetaDatum`, this records the two facts that tie `Θ` to the prism `R`:

* the track `Q i` has exactly `|R i|` edges (i.e. `pathLength (R i) + 1`);
* the *index correspondence*: the `k`-th edge of `Q i` is carried by `φ` to the `k`-th vertex
  of the rung `R i`.

The correspondence is what makes `Θ` usable downstream — it is how one recognises which vertex
of `Θ` sits between two prescribed consecutive rung-vertices (`u u'` and `w w'` in 10.1). -/
def IsPrismTheta {V : Type*} (G : SimpleGraph V) (R : Fin 3 → List V) (K : Set V)
    {m : ℕ} (Θ : SimpleGraph (Fin m)) (x y : Fin m) (Q : Fin 3 → List (Fin m))
    (φ : Θ.lineGraph ≃g G.induce K) : Prop :=
  IsThetaDatum Θ x y Q ∧
  (∀ i : Fin 3, (Q i).length = (R i).length + 1) ∧
  (∀ (i : Fin 3) (k : ℕ) (hk : k + 1 < (Q i).length),
    ∃ he : s((Q i)[k]'(by omega), (Q i)[k + 1]'hk) ∈ Θ.edgeSet,
      (R i)[k]? = some (↑(φ ⟨_, he⟩) : V))

end Workspace.ProofLemmas.ThetaData

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.ThetaData
open Workspace.ProofLemmas.Thm101ThetaOfPrismAux

/-- **Every prism is the line graph of a theta graph.**

Given a prism formed by the three rungs `R 0, R 1, R 2` of `G`, with vertex set
`K = V(R 0) ∪ V(R 1) ∪ V(R 2)`, there is a theta graph `Θ` on
`pathLength (R 0) + pathLength (R 1) + pathLength (R 2) + 2` vertices with
`Θ.lineGraph ≃g G.induce K`, presented as an `IsPrismTheta` datum (so the branch-vertices
`x, y`, the three tracks `Q i`, and the index correspondence
*"`k`-th edge of `Q i` ↔ `(R i)[k]`"* all come with it).

This is the general form of `NinePrismLineGraph.prismIsoLine`, and it generalises three of
that module's `decide`s: `psi_mem`, `psiE_inj` (with the card-`decide` in `psiE_bij`), and the
`decide` closing `prismIsoLine.map_rel_iff'`.  See the module docstring for the exact
correspondence between those `decide`s and the clauses of `IsThetaDatum` / `IsPrismTheta`. -/
theorem Thm101ThetaOfPrism {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) :
    ∃ (Θ : SimpleGraph (Fin (pathLength (R 0) + pathLength (R 1) + pathLength (R 2) + 2)))
      (x y : Fin (pathLength (R 0) + pathLength (R 1) + pathLength (R 2) + 2))
      (Q : Fin 3 → List (Fin (pathLength (R 0) + pathLength (R 1) + pathLength (R 2) + 2)))
      (φ : Θ.lineGraph ≃g G.induce K),
      IsPrismTheta G R K Θ x y Q φ := by
  let psi : H (rungSize R) ≃g theta (rungSize R) :=
    SimpleGraph.Iso.map (finEquiv (rungSize R)) (H (rungSize R))
  let phi : (theta (rungSize R)).lineGraph ≃g G.induce K :=
    psi.lineGraph.symm.trans (rawPrismIso G a b R K hprism hK)
  have htheta : IsThetaDatum (theta (rungSize R)) (fx (rungSize R))
      (fy (rungSize R)) (fq (rungSize R)) := by
    simpa [IsThetaDatum, IsRawThetaDatum] using fin_isTheta (rungSize R)
  refine ⟨theta (rungSize R), fx (rungSize R), fy (rungSize R),
    fq (rungSize R), phi, htheta, ?_, ?_⟩
  · intro i
    have hqfin : (fq (rungSize R) i).length = rungSize R i + 2 := by
      simp [fq, q_length]
    have hsize := rungSize_add_one hprism i
    calc
      (fq (rungSize R) i).length = rungSize R i + 2 := hqfin
      _ = (rungSize R i + 1) + 1 := by omega
      _ = (R i).length + 1 := congrArg (fun z => z + 1) hsize
  · intro i k hk
    have hkedge : k < rungSize R i + 1 := by
      have hlen : (fq (rungSize R) i).length = rungSize R i + 2 := by
        simp [fq, q_length]
      have hk' : k + 1 < rungSize R i + 2 := by
        rw [← hlen]
        exact hk
      omega
    let p : EdgeIndex (rungSize R) := ⟨i, ⟨k, hkedge⟩⟩
    let eraw : (H (rungSize R)).edgeSet := indexedEdge (rungSize R) p
    let efin : (theta (rungSize R)).edgeSet := psi.lineGraph eraw
    have heval :
        (efin : Sym2 (Fin (rungSize R 0 + rungSize R 1 + rungSize R 2 + 2))) =
          s((fq (rungSize R) i)[k]'(by simpa using Nat.lt_trans (Nat.lt_succ_self k) hk),
            (fq (rungSize R) i)[k + 1]'hk) := by
      change Sym2.map (finEquiv (rungSize R)) (edgeAt (rungSize R) p) = _
      simp [edgeAt, p, fq, List.getElem_map]
    have he :
        s((fq (rungSize R) i)[k]'(by simpa using Nat.lt_trans (Nat.lt_succ_self k) hk),
          (fq (rungSize R) i)[k + 1]'hk) ∈ (theta (rungSize R)).edgeSet := by
      rw [← heval]
      exact efin.2
    refine ⟨he, ?_⟩
    have hefin :
        (⟨s((fq (rungSize R) i)[k]'(by simpa using Nat.lt_trans (Nat.lt_succ_self k) hk),
            (fq (rungSize R) i)[k + 1]'hk), he⟩ : (theta (rungSize R)).edgeSet) =
          efin := Subtype.ext heval.symm
    have happ :
        phi ⟨s((fq (rungSize R) i)[k]'(by simpa using Nat.lt_trans (Nat.lt_succ_self k) hk),
            (fq (rungSize R) i)[k + 1]'hk), he⟩ = phi efin := congrArg phi hefin
    have happval :
        (↑(phi ⟨s((fq (rungSize R) i)[k]'(by
              simpa using Nat.lt_trans (Nat.lt_succ_self k) hk),
            (fq (rungSize R) i)[k + 1]'hk), he⟩) : V) = (↑(phi efin) : V) :=
      congrArg Subtype.val happ
    have hkR : k < (R i).length := by
      rw [← rungSize_add_one hprism i]
      exact hkedge
    have hbase : (R i)[k]? = some (↑(phi efin) : V) := by
      rw [List.getElem?_eq_getElem hkR]
      congr 1
      simp [phi, efin, eraw, p, psi, rawPrismIso_indexedEdge, rungInK, rungVertex]
    exact hbase.trans (congrArg some happval.symm)

end Workspace.ProofLemmas
