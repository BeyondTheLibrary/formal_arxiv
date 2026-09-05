import Workspace.ProofLemmas.DiracK4SubdivisionInduction
import Workspace.ProofLemmas.SubdivisionDatumRealize

/-!
# Dirac's theorem: minimum degree `≥ 3` forces a `K₄`-subdivision

**NL statement.**  *Every finite simple graph in which every vertex has degree at least `3`
contains, as a subgraph, a subdivision of `K₄`.*

**Citation.**  G. A. Dirac, *A property of 4-chromatic graphs and some remarks on critical
graphs*, J. London Math. Soc. **27** (1952) 85–92.  Classical, and standard textbook material
(Diestel, *Graph Theory*, Prop. 1.7.2 / Lemma 3.5.1 territory).

The printed proof of **5.3** (`paper/proofs/5_3.md`, published page 19) opens with

> *"There is a subgraph of `H` which is a subdivision of `K₄`, and we may assume that it does
> not satisfy the theorem."*

The proof below supplies that folklore result.  It uses the standard finite reduction: choose a
distinguished vertex, delete it when its degree is at most one, suppress it when its degree is two,
delete an incident edge when its degree is at least four, and stop with a `K₄` when its three
neighbours form a triangle.  A one-edge "boost" records the single parallel edge needed by the
usual multigraph presentation while keeping every intermediate object a simple graph.

**Vocabulary.**  `IsSubdivision` is the project's own notion, from
`Workspace.Types.Tracks` (printed pp. 19–20): `IsSubdivision J K` says `K` is obtained from `J`
by replacing each edge by a track, the tracks being disjoint except for their ends, with `K`
having no other vertices and no other edges.  `K₄` is `(⊤ : SimpleGraph (Fin 4))`.  "Contains
as a subgraph" is `∃ S : J.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe` — the
subgraph `S` is *exactly* the subdivision, since `IsSubdivision` pins down both `S.verts` and
`S.coe.edgeSet`.  Degree is written `(J.neighborSet u).ncard`, matching `branchVertices` in
`Workspace.Types.Tracks` (it avoids carrying a `DecidableRel J.Adj` instance).

**For callers.**  `Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected`
says every vertex of a 3-connected graph has degree `≥ 3`, so a caller holding
`IsKConnected J 3` supplies `hdeg` directly from it; the same hypothesis also gives
`3 < Fintype.card U`, which supplies the `Nonempty U` instance.
-/

set_option autoImplicit false

namespace Workspace.PriorWork.DiracK4Subdivision

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-- **Dirac (1952)** — *every finite simple graph of minimum degree at least `3` contains, as a
subgraph, a subdivision of `K₄`*.

`Nonempty U` is not decoration: without it the statement is **false**, since for `U` empty the
degree hypothesis is vacuous while no subgraph can carry an injection `Fin 4 → S.verts`.  The
classical statement quantifies over graphs with at least one vertex (minimum degree of the null
graph is not `≥ 3`, it is undefined), and any nonempty graph of minimum degree `≥ 3` has at
least `4` vertices. -/
theorem exists_k4_subdivision_subgraph_of_min_degree_three
    {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (J : SimpleGraph U)
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard) :
    ∃ S : J.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe := by
  classical
  let root : U := Classical.choice (inferInstance : Nonempty U)
  have hcard : 2 ≤ Fintype.card U := by
    have hrootDegree := hdeg root
    have hlt :=
      Workspace.ProofLemmas.DiracInductionBasics.ncard_neighborSet_lt_card J root
    omega
  have hcondition :
      Workspace.ProofLemmas.DiracK4SubdivisionInduction.DegreeCondition J root none := by
    intro x _
    exact hdeg x
  exact
    Workspace.ProofLemmas.SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum
      (Workspace.ProofLemmas.DiracK4SubdivisionInduction.hasK4Datum_of_degreeCondition
        J root none hcard hcondition)

end Workspace.PriorWork.DiracK4Subdivision
