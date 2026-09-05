import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# 5.3, assembled from its three printed steps

The printed proof of **5.3** (`paper/proofs/5_3.md`, published page 19) falls into exactly three
pieces, separated by the two places where the authors change gear.  This module proves 5.3 from
those three pieces, taking each as a `def`-wrapped hypothesis, so that the node closes with a
single `exact` as the pieces land.  (Same pattern as `Workspace.ProofLemmas.OddWheelAssembly`.)

**Step 1 — `HasK4SubdivisionSubgraph`.**  The opening sentence:

> *"There is a subgraph of `H` which is a subdivision of `K₄` …"*

Asserted with no proof and no citation; it is Dirac's theorem applied to the 3-connected graph
that `H` subdivides.  Its chain is
`PriorWork.DiracK4Subdivision` → `SubdivisionDatum.hasK4Datum_of_subgraph_subdivision` (A) →
`hasK4Datum_of_isSubdivision_comp` (C, in flight) →
`SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum` (B).

**Step 2 — `TwoTracksYieldK33`.**  Everything from *"Suppose every track in `H` between
`{p₁,…,p_m}` and `{q₁,…,q_n}` uses one of the edges …"* down to *"Hence there is a subgraph `J`
of `H` isomorphic to `K₃,₃`."*  Its two outcomes are the paper's two: either the no-cross-track
case, where cyclic 3-connectivity forces `H` itself to be a subdivision of `K₄`, or the
cross-track case, which ends with a `K₃,₃` subgraph.

**Step 3 — `K33SubgraphYieldsTheorem`.**  The closing paragraph, from *"It is helpful now to
change the notation"* to the end: given a `K₃,₃` subgraph, either some component `F` of
`H \ V(J)` has two attachments — and then `P ∪ (J \ {a₁b₁, a₂b₂})` resp.
`P ∪ (J \ {a₁b₁, a₂b₃})` is a nondegenerate `K₄`-subdivision — or there is no such `F`, and
bipartiteness gives `H = J = K₃,₃`.

**What this module actually proves** is the glue the paper leaves implicit: that *"we may assume
it does not satisfy the theorem"* turns the goal's third disjunct into *"every `K₄`-subdivision
subgraph of `H` is degenerate"*, and that this is exactly the hypothesis under which
`DegenerateK4Tracks.exists_two_tracks_of_degenerate_subgraph` produces the paper's `P` and `Q`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm53Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {W : Type*}

/-- **Step 1 of 5.3** — the printed opening sentence *"There is a subgraph of `H` which is a
subdivision of `K₄`"*. -/
def HasK4SubdivisionSubgraph (H : SimpleGraph W) : Prop :=
  ∃ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe

/-- **Step 2 of 5.3** — from the two disjoint odd tracks with the four cross edges, either `H`
is itself a subdivision of `K₄` (the no-cross-track case) or `H` has a `K₃,₃` subgraph.

The two length guards are existential binders so that the `getElem`s below elaborate; this is
the convention `Workspace.Statements.S05.Thm_5_3`'s own header prescribes. -/
def TwoTracksYieldK33 (H : SimpleGraph W) : Prop :=
  H.IsBipartite → CyclicallyThreeConnected H →
  (∀ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe →
    DegenerateK4Appearance S.coe) →
  ∀ (P Q : List W) (_hP : 3 ≤ P.length) (_hQ : 3 ≤ Q.length),
    IsTrackList H P → IsTrackList H Q → (∀ x ∈ P, x ∉ Q) →
    Odd P.length → Odd Q.length →
    H.Adj P[0] Q[0] → H.Adj P[0] Q[Q.length - 1] →
    H.Adj P[P.length - 1] Q[0] → H.Adj P[P.length - 1] Q[Q.length - 1] →
    IsSubdivision (⊤ : SimpleGraph (Fin 4)) H ∨
      ∃ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3))

/-- **Step 3 of 5.3** — the closing paragraph: a `K₃,₃` subgraph of a bipartite, cyclically
3-connected `H` already gives the theorem. -/
def K33SubgraphYieldsTheorem (H : SimpleGraph W) : Prop :=
  H.IsBipartite → CyclicallyThreeConnected H →
  ∀ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe

/-- **5.3**, assembled from its three printed steps.

`Workspace.Statements.S05.SPGT.thm_5_3` is `thm_5_3_of_steps H hbip hc3 h₁ h₂ h₃` once the three
steps are available; the signature of the conclusion is byte-identical to the frozen one. -/
theorem thm_5_3_of_steps [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (hbip : H.IsBipartite) (hc3 : CyclicallyThreeConnected H)
    (hstart : HasK4SubdivisionSubgraph H)
    (hstep2 : TwoTracksYieldK33 H)
    (hstep3 : K33SubgraphYieldsTheorem H) :
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
    IsSubdivision (⊤ : SimpleGraph (Fin 4)) H ∨
    (∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe) := by
  by_contra hcon
  have hnoK33 : ¬ Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) :=
    fun h => hcon (Or.inl h)
  have hnosub : ¬ IsSubdivision (⊤ : SimpleGraph (Fin 4)) H :=
    fun h => hcon (Or.inr (Or.inl h))
  have hnoC : ¬ ∃ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe :=
    fun h => hcon (Or.inr (Or.inr h))
  -- *"and we may assume that it does not satisfy the theorem"*: the failure of the third
  -- disjunct says exactly that every `K₄`-subdivision subgraph of `H` is degenerate.
  have hdegall : ∀ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe →
      DegenerateK4Appearance S.coe := by
    intro S hS
    by_contra hnd
    exact hnoC ⟨S, hS, ClassLemmas.nondegenerateAppearance_K4_iff.mpr hnd⟩
  -- *"Hence there are tracks `P` and `Q` …"*
  obtain ⟨S, hS⟩ := hstart
  obtain ⟨P, Q, hP, hQ, htP, htQ, hdisj, hoP, hoQ, e1, e2, e3, e4⟩ :=
    DegenerateK4Tracks.exists_two_tracks_of_degenerate_subgraph hbip S hS (hdegall S hS)
  rcases hstep2 hbip hc3 hdegall P Q hP hQ htP htQ hdisj hoP hoQ e1 e2 e3 e4 with
    hsubd | ⟨J, hJ⟩
  · exact hnosub hsubd
  · rcases hstep3 hbip hc3 J hJ with h1 | h2
    · exact hnoK33 h1
    · exact hnoC h2

end Workspace.ProofLemmas.Thm53Assembly
