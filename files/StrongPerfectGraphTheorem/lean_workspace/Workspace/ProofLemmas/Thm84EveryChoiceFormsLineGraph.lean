import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Statements.S08.Thm_8_1
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84GluedSubdivision
import Workspace.ProofLemmas.Thm84GluedBipartite
import Workspace.ProofLemmas.Thm84GluedLineGraphIso
import Workspace.ProofLemmas.Thm84GluedTransport

/-!
# Every choice of rungs forms a line graph

PAPER (printed p. 39, the prose immediately following the proof of 8.1): *"For each edge `uv` of
`J`, choose a `uv`-rung `R_uv`.  It follows from 8.1 and the final axiom above that the subgraph
of `G` induced on the union of the vertex sets of these rungs is a line graph of a bipartite
subdivision `H` of `J`.  For brevity we say that this choice of rungs forms `L(H)`."*

`Workspace.Types.StripSystems.FormsLineGraph` transcribes only the *"for brevity we say"* half:
it is the **property** that a given family `R` of rungs, together with a given graph `H`, realises
the union of the rung vertex sets as `L(H)`.  The mathematical content of the printed sentence —
that **every** choice of rungs has this property, for a suitable `H` — is the theorem below.

The paper uses it as a fact about arbitrary choices of rungs throughout §8:

* 8.4 (printed p. 41): *"Let us say that a choice of rungs `R_ij` forming a line graph `L(H)` is
  saturated if `X` saturates `L(H)` … If every choice of rungs is saturated, then `X` saturates
  the strip system as required, so we may therefore assume that there is some choice of rungs
  …"* — the quantification "every choice of rungs" only makes sense because each one does form
  some `L(H)`.
* 8.5 (printed p. 43): *"Make a choice of rungs `R_ij` `(ij ∈ E(J))` such that `x ∈ V(R_uv)` and
  `x' ∈ V(R_{u'v})`, forming `L(H)`."*, and (5) *"Every choice of rungs is broad."*
* 8.6 (printed p. 46): *"For every choice of rungs, forming `L(H)` say, every member of `Y'` is
  major with respect to `L(H)` … Since this holds for every choice of rungs, it follows that `X`
  saturates the strip system."*

As everywhere in this project, "there is a graph `H`" is rendered by
`∃ (n : ℕ) (H : SimpleGraph (Fin n))`, matching `Appearances.Appears` and
`StripSystems.NondegenerateStripSystem`.  The hypotheses are the standing ones of §8 (`G` Berge,
`J` 3-connected, `(S,N)` a `J`-strip system) plus the choice of rungs `R` itself; `hR` is exactly
the paper's *"for each edge `uv` of `J`, choose a `uv`-rung `R_uv`"*, and it is also the first
conjunct of the conclusion's `FormsLineGraph`.

**Why `hRsymm` is needed.**  The paper's choice of rungs is indexed by the **edges** `uv ∈ E(J)`,
so `R_uv` and `R_vu` denote the same rung; the Lean encoding `R : U → U → List V` indexes by
ordered pairs, and `IsUVRung G J S N u v (R u v)` for all adjacent ordered pairs does *not* force
the two to agree.  Without that clause the statement is false: a strip `S_uv` may contain two
distinct rungs `R₁ ≠ R₂` (this is exactly what 8.1 is about), and taking `R u v = R₁`,
`R v u = R₂` puts the vertices of *both* into the union
`⋃ (a b) (_ : J.Adj a b), V(R a b)` that `FormsLineGraph` uses.  With `p` the `u`-end of the rung
at another edge `uw` and `q` the `u`-end of the rung at `ux` (both exist since `deg_J u ≥ 3`), the
axiom "*`N_u ∩ S_uv` is complete to `N_u ∩ S_uw`*" makes the `u`-ends of `R₁` and of `R₂` both
adjacent to `p` and to `q`, and `p,q` adjacent — a diamond or a `K₄` on those four vertices.  In
the line graph of a **bipartite** `H` every triangle is a star `δ_H(z)`, so two triangles sharing
an edge force all four vertices into one `δ_H(z)`, i.e. two internally disjoint `ι u`–`ι v`
branches in `H`, contradicting `IsBipartiteSubdivision J H`.  So no `H` can work for an
asymmetric `R`.  Restricting to edge-indexed families is the paper's own reading and loses
nothing downstream: 8.4/8.5/8.6 construct their choices of rungs themselves.

**DEFECT FOUND AND REPAIRED (2026-08-28).**  This module previously carried the clause in the
form `hRsymm : ∀ u v, J.Adj u v → R u v = R v u`.  That equation is **false for every rung of
positive length**, hence made the theorem inapplicable exactly where §8 needs it (8.2 asks for a
choice of rungs in which `R_uv` has length `≥ 1`).  Reason: a `uv`-rung is a *directed* object in
this encoding.  `IsUVRung G J S N u v L` pins `head L` as the unique vertex of `L` lying in
`N_u`, while `IsUVRung G J S N v u L` pins `getLast L` as the unique vertex of `L` lying in
`N_u`; on one and the same list `L` those two force `head L = getLast L`, and `L.Nodup` then
collapses `L` to a single vertex.  Machine-checked, sorry-free, at
`lean_workspace/ProofAttempts/Thm82RungChoice/Thm82RungChoice_scratch.lean`
(`forced_pathLength_zero`): `hR` together with `R a b = R b a` proves
`pathLength (R u v) = 0` for **every** edge of `J`.  This is forced rather than stylistic,
because the first conjunct of `FormsLineGraph` *is* `hR`, quantified over both orientations of
every edge.

The repair is the faithful reading of *"for each **edge** `uv` … choose a `uv`-rung"*: reversing
the orientation reverses the list, i.e.

```lean
hRsymm : ∀ u v, J.Adj u v → R v u = (R u v).reverse
```

The union `⋃ (a b) (_ : J.Adj a b), V(R a b)` is unchanged (a list and its reverse have the same
members), so `FormsLineGraph`'s `K` is exactly the paper's *"union of the vertex sets of these
rungs"*, one rung per edge — while the degeneracy above disappears, since
`IsUVRung … v u (R u v).reverse` is precisely `Thm82RungFamily.rung_reverse` applied to
`IsUVRung … u v (R u v)`.  `Thm82RungFamily.exists_symmetric_rung_family` produces families
satisfying exactly this clause.  Recorded in `AMBIGUITIES.md`.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **"For each edge `uv` of `J`, choose a `uv`-rung `R_uv`.  It follows from 8.1 and the final
axiom above that the subgraph of `G` induced on the union of the vertex sets of these rungs is a
line graph of a bipartite subdivision `H` of `J`."**

Every choice of rungs forms a line graph: given a `J`-strip system `(S,N)` in a Berge graph `G`
with `J` 3-connected, and any family `R` assigning to each **edge** `uv` of `J` a `uv`-rung
`R u v` — edge-indexed, i.e. reversing the orientation reverses the list, `R v u = (R u v).reverse`
— there is a (bipartite subdivision) graph `H` with `FormsLineGraph G J S N R H`. -/
theorem everyChoiceFormsLineGraph {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), FormsLineGraph G J S N R H := by
  classical
  let K : Set V := ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}

  -- The last strip-system axiom provides one reference family.  Theorem 8.1
  -- transfers its cycle-parity equation to the arbitrary family `R`.
  obtain ⟨R₀, hR₀, hcycle₀⟩ :=
    Workspace.ProofLemmas.StripSystemBasics.exists_special_rungs hSN
  have hlength_modEq (u v : U) (huv : J.Adj u v) :
      pathLength (R u v) ≡ pathLength (R₀ u v) [MOD 2] := by
    have hp := Workspace.Statements.S08.SPGT.thm_8_1
      G hG J hJ S N hSN u v huv (R u v) (R₀ u v) (hR u v huv) (hR₀ u v huv)
    rw [Nat.even_iff, Nat.even_iff] at hp
    show pathLength (R u v) % 2 = pathLength (R₀ u v) % 2
    omega
  have hcycle (c : List U) (hlen : 3 ≤ c.length) (hnd : c.Nodup)
      (hadj : ∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) :
      ((c.zip (c.rotate 1)).map (fun p => pathLength (R p.1 p.2))).sum
        ≡ c.length [MOD 2] := by
    apply (Nat.ModEq.listSum_map (l := c.zip (c.rotate 1))
      (f := fun p => pathLength (R p.1 p.2))
      (g := fun p => pathLength (R₀ p.1 p.2)) ?_).trans
    · exact hcycle₀ c hlen hnd hadj
    · intro p hp
      exact hlength_modEq p.1 p.2 (hadj p hp)

  -- What remains is the explicit realization theorem: glue a track of
  -- length `pathLength (R u v) + 1` along every edge of `J`; `hcycle`
  -- makes the glued subdivision bipartite, and the strip axioms identify
  -- its line graph with `G.induce K`.
  have hrealize : ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision J H ∧ Nonempty (H.lineGraph ≃g G.induce K) := by
    obtain ⟨Hs, T, ρ, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges,
      hlength, _horiented, hdict⟩ :=
      Workspace.ProofLemmas.Thm84GluedSubdivision.exists_glued_subdivision
        G hG J hJ S N hSN R hR hRsymm
    have hsub : IsSubdivision J Hs :=
      ⟨Sum.inl, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩
    have hTlen : ∀ u v : U, J.Adj u v →
        trackLength (T u v) = pathLength (R u v) + 1 := by
      intro u v huv
      obtain ⟨s, t, hp, -, -⟩ :=
        Workspace.ProofLemmas.StripSystemBasics.rung_isPath (hR u v huv)
      have hRpos : 0 < (R u v).length := List.length_pos_of_ne_nil hp.1.1
      have hlen' := hlength u v huv
      unfold trackLength pathLength
      omega
    have hbip : Hs.IsBipartite :=
      Workspace.ProofLemmas.Thm84GluedBipartite.glued_isBipartite
        G hG J hJ S N hSN R hR hRsymm Hs Sum.inl T hι htrack hlen hrev hdisj
          hnew hcover hedges hTlen hcycle
    have hdata : Workspace.ProofLemmas.Thm84GluedLineGraphIso.GluedData
        J Hs R Sum.inl T ρ :=
      ⟨hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges, hlength, hdict⟩
    have hiso : Nonempty (Hs.lineGraph ≃g G.induce K) := by
      simpa [K] using
        (Workspace.ProofLemmas.Thm84GluedLineGraphIso.glued_lineGraph_iso
          G hG J hJ S N hSN R hR hRsymm Hs Sum.inl T ρ hdata)
    exact Workspace.ProofLemmas.Thm84GluedTransport.glued_transport
      G J K Hs hsub hbip hiso
  obtain ⟨n, H, hsub, hline⟩ := hrealize
  exact ⟨n, H, hR, hsub, by simpa [K] using hline⟩

end Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
