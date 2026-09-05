import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.RungReplacementAddTrack
import Workspace.ProofLemmas.RungReplacementDelete
import Workspace.ProofLemmas.RungReplacementResidual
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.RungReplacementLabels
import Workspace.ProofLemmas.RungReplacementTransport
import Workspace.ProofLemmas.RungReplacementSurgeryGaps
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.PathBasics

/-!
# The labelled rung-replacement construction

PAPER (proof of 7.5, claim (2), printed p. 37):

> *"So if in `L(H)` we replace `Rb₁b₂` by `R′` we obtain another appearance of `J` in `G`, say
> `L(H′)`, where `H′` is obtained from `H` by replacing the branch `Bb₁b₂` by some new branch
> `B′` joining the same two vertices.  For each `v ∈ V(J)` let `N′v` be the clique in `L(H′)`
> formed by the edges in `δ_H′(v)`.  So `N′v = Nv` for all vertices `v` of `J` except for `b₁`
> and `b₂`.  Let `R′` be between `r′₁` and `r′₂`, where `r′ᵢ ∈ N′_{bᵢ}`."*

The paper prints no proof of this sentence; it is used four times inside 5.8's case analysis,
and again in 7.5, 8.4 and 8.5.  This module fixes **one** interface for all of those uses.

## Why the interface looks the way it does

Write `Qset` for the vertex set of the old rung `R`, and `K₀ = K \ Qset` for the part of the
old appearance that survives.  The construction deletes the old branch `q` — its edges and its
internal vertices — restricts the old isomorphism `φ` to `K₀`, and then adds a new track whose
rung is `R′`.  Two design decisions matter, and both are forced by 5.8's case analysis:

* **The replacement path must be disjoint from the *retained* appearance, not from all of `K`.**
  In case 1 of 5.8.2 the replacement reuses a terminal segment of the old rung, so vertices of
  `R′` may lie in `K`.  What is needed is only `hdisj`: a vertex of `R′` that lies in `K` lies
  on the old rung.
* **The attachment condition is an "if and only if", imposed on every vertex of `R′` but only
  against `K₀`.**  Cases 2 and 4 of 5.8.2 permit the extra edges `p₁r₁` and `p₂r₂`; since `r₁`
  and `r₂` lie on the old rung, those edges are simply not constrained by `hboundary`.  The
  reverse direction of the "if and only if" is the statement that the two ends of `R′` really
  are complete to the two clique remainders, which is what makes the new graph a line graph of
  a subdivision at all.

`hpar` is load-bearing: `IsAppearance` demands that `H′` be a **bipartite** subdivision of `J`,
and replacing one track shifts the length of every cycle of `H` through that track by
`trackLength B′ − trackLength Bb₁b₂`.  So `H′` is bipartite exactly when `R′` and `R` have the
same parity.  Every caller must supply it; the paper supplies it in cases 2, 3 and 4 of 5.8.2
directly, and in case 1 it has to be derived from `Berge G`.

## What the output records

`RungReplacementResult` deliberately returns **labelled** data rather than the bare existence of
a new appearance.  A caller has to know which vertex of `G` each new clique gained and lost —
*"`N′cᵢ = (Ncᵢ \ {rᵢ}) ∪ {r′ᵢ}`"* — and an isomorphism produced by an unlabelled existential
statement does not determine that.  The fields therefore include:

* the new branch `q'` with its ends `ι b₁, ι b₂` and its length `pathLength R′ + 1`;
* its rung, which is exactly `R′`;
* the two changed endpoint cliques, and the fact that every other clique is unchanged;
* survival of every other branch, with its ends, its length and its rung unchanged.

That last group is what lets a caller say *"`Bc₁c₂` is still a branch of `H′`"* when the
replaced branch is a different one.

## How the construction is meant to go

The route that avoids rebuilding an appearance from scratch is: **delete the old branch,
restrict `φ`, add the labelled new track, restore bipartiteness.**  Concretely, with
`W₀ = {w : W // w ∉ trackInterior q}` and `H₀.Adj x y := H.Adj x.val y.val ∧
s(x.val, y.val) ∉ trackEdges q`:

1. *Delete the branch.*  An edge of `H` outside `trackEdges q` has both ends outside
   `trackInterior q`, because an internal vertex of a branch has degree two and both of its
   edges are branch edges.  So `φ` restricts to `φ₀ : H₀.lineGraph ≃g G.induce (K \ V(R))`,
   and `¬ H₀.Adj b₁ b₂` (a retained edge joining the two ends would be a second branch between
   them), with `NSet G H₀ (K \ V(R)) φ₀ bᵢ = NSet G H K φ bᵢ \ {rᵢ}`.
2. *Add the new track.*  Apply
   `Workspace.ProofLemmas.RungReplacementAddTrack.addTrackLabelled` to `H₀`, `φ₀` and `R'`.
   Its hypotheses `h₁`, `h₂`, `hno` are exactly the two directions of `hboundary`, and its two
   edge-label equations are what make the fields `hrung'`, `hleft`, `hright` and `hother`
   computable rather than merely existential.
3. *Recover the subdivision.*  Reuse the old presentation of `H` as a subdivision of `J`,
   replacing the two orientations of the selected edge by the new track.  Coverage holds
   because every deleted vertex was internal to precisely that track.
4. *Recover bipartiteness.*  Restrict an old two-colouring to `W₀` and colour the new internal
   vertices alternately from the colour of `b₁`; `hpar` together with the length dictionary
   `Workspace.ProofLemmas.RungReplacementRungLength.rung_length_eq_trackLength` makes the
   colour constraint at `b₂` hold.
5. *Transport to `Fin m`* with `IsoTransport.exists_iso_fin`, carrying the labelled data.

**Status: statement only.**  The construction itself is the remaining gap; see the note on
`rungReplacement`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementLabelled

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.RungReplacementDelete
open Workspace.ProofLemmas.RungReplacementResidual
open Workspace.ProofLemmas.RungReplacementBranchFacts
open Workspace.ProofLemmas.RungReplacementLabels
open Workspace.ProofLemmas.RungReplacementAddTrack
open Workspace.ProofLemmas.RungReplacementSurgeryGaps

/-- The set of vertices of `G` representing the edges of the track `q`, i.e. the *rung* of `q`
in the appearance `φ`.  This is the `Set`-valued form of
`Workspace.ProofLemmas.TrackToRungPath.trackRung`, and it is how the paper's `V(Ruv)` is
written in the frozen statements of §7. -/
def rungSet {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (q : List W) : Set V :=
  {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)}

/-- **The labelled output of replacing the rung of one branch.**

`H'` is the new subdivision, `K'` the new vertex set, `φ'` the new appearance isomorphism, and
`ι` relabels the old vertices inside `H'`.  `q'` is the new branch, which joins the same two
vertices `ι b₁, ι b₂` as the old one and whose rung is exactly `R'`.

Every field is an equation of **sets of vertices of `G`**, not an abstract isomorphism: that is
what a caller needs in order to read off *"`N′cᵢ = (Ncᵢ \ {rᵢ}) ∪ {r′ᵢ}`"* and *"`N′v = Nv` for
all other `v`"*. -/
structure RungReplacementResult {V U W : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (q : List W) (b₁ b₂ : W) (R R' : List V) (r₁ r₂ r₁' r₂' : V) where
  /-- The number of vertices of the new subdivision. -/
  m : ℕ
  /-- The new subdivision `H'` of `J`. -/
  H' : SimpleGraph (Fin m)
  /-- The vertex set of the new appearance. -/
  K' : Set V
  /-- The new appearance isomorphism. -/
  φ' : H'.lineGraph ≃g G.induce K'
  /-- PAPER: *"we obtain another appearance of `J` in `G`, say `L(H′)`"*. -/
  happ : IsAppearance G J H' K'
  /-- The relabelling of the old vertices of `H` inside `H'`. -/
  ι : W → Fin m
  /-- `ι` is injective on the branch-vertices, which are exactly the vertices of `J`. -/
  ιinj : Set.InjOn ι (branchVertices H)
  /-- PAPER: *"the branch `Bb₁b₂` … replaced by some new branch `B′` joining the same two
  vertices"*. -/
  q' : List (Fin m)
  hq' : IsBranch H' q'
  hq'from : IsTrackFrom H' q' (ι b₁) (ι b₂)
  /-- The new branch has one more edge than the replacement rung has vertices minus one. -/
  hq'len : trackLength q' = pathLength R' + 1
  /-- The new appearance is the old one with the old rung swapped out for the new one. -/
  hK' : K' = (K \ {x : V | x ∈ R}) ∪ {x : V | x ∈ R'}
  /-- The rung of the new branch is the replacement path. -/
  hrung' : rungSet G H' K' φ' q' = {x : V | x ∈ R'}
  /-- PAPER: *"`N′b₁ = (Nb₁ \ {r₁}) ∪ {r′₁}`"*. -/
  hleft : NSet G H' K' φ' (ι b₁) = (NSet G H K φ b₁ \ {r₁}) ∪ {r₁'}
  /-- PAPER: *"`N′b₂ = (Nb₂ \ {r₂}) ∪ {r′₂}`"*. -/
  hright : NSet G H' K' φ' (ι b₂) = (NSet G H K φ b₂ \ {r₂}) ∪ {r₂'}
  /-- PAPER: *"`N′v = Nv` for all vertices `v` of `J` except for `b₁` and `b₂`"*.

  The hypothesis `c ∉ trackInterior q` is not in the paper's sentence, and is not needed for
  the vertices the paper is talking about: the paper quantifies over the vertices of `J`, which
  are the branch-vertices of `H`, and no branch-vertex is internal to a branch (that is part of
  `Workspace.Types.Tracks.IsBranch`).  It is however *necessary*, and was missing from the
  first version of this interface: an internal vertex `c` of the replaced branch has
  `N_c ⊆ V(R)`, and the two vertices of `V(R)` in question are usually deleted, so no vertex of
  `H'` whatever can carry the clique `N_c`.  See `lean_workspace/REPORT.md`. -/
  hother : ∀ c : W, c ∉ trackInterior q → c ≠ b₁ → c ≠ b₂ →
    NSet G H' K' φ' (ι c) = NSet G H K φ c
  /-- Every other branch of `H` survives, with the same ends and the same rung. -/
  hbranches : ∀ (p : List W) (u v : W), IsBranch H p → IsTrackFrom H p u v →
    trackEdges p ≠ trackEdges q →
    IsBranch H' (p.map ι) ∧ IsTrackFrom H' (p.map ι) (ι u) (ι v) ∧
      rungSet G H' K' φ' (p.map ι) = rungSet G H K φ p

/-- **The rung-replacement construction.**

Hypotheses, in the order in which the construction uses them.  `q` is the branch `Bb₁b₂` of the
subdivision `H`, `R` is its rung (`hRset`), and `rᵢ` is the unique vertex of `R` lying in the
clique `N_{bᵢ}`.  The replacement path `R'` runs from `r₁'` to `r₂'` and satisfies:

* `hdisj` — it meets the old appearance only inside the old rung;
* `hboundary` — a vertex of `R'` is adjacent to a **retained** vertex of `K` exactly when it is
  `r₁'` and that vertex lies in `N_{b₁} \ {r₁}`, or it is `r₂'` and that vertex lies in
  `N_{b₂} \ {r₂}`;
* `hpar` — it has the same parity as `R`, which is what keeps `H'` bipartite.

**Remaining gaps.**  The construction is the one described in the module docstring: delete the
old branch, restrict `φ` to `K \ V(R)`, add a labelled new track of length `pathLength R' + 1`,
and restore bipartiteness from `hpar`.  Everything about the *labels* — the clique dictionary,
the rung of the new branch, and the transport to `Fin m` — is proved below.  What is used
without proof is the purely structural half, isolated as the four statements of
`Workspace.ProofLemmas.RungReplacementSurgeryGaps`: after the surgery the graph is again a
subdivision of `J`, it is again bipartite, the new track is a branch, and every other branch
survives with its ends. -/
theorem rungReplacement {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (q : List W) (b₁ b₂ : W) (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (R : List V) (hR : IsPathList G R) (hRset : {x : V | x ∈ R} = rungSet G H K φ q)
    (r₁ r₂ : V)
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂})
    (R' : List V) (r₁' r₂' : V) (hR' : IsPathFrom G R' r₁' r₂')
    (hdisj : ∀ x ∈ R', x ∈ K → x ∈ R)
    (hboundary : ∀ x ∈ R', ∀ y ∈ K, y ∉ R →
      (G.Adj x y ↔
        (x = r₁' ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = r₂' ∧ y ∈ NSet G H K φ b₂ \ {r₂})))
    (hpar : Even (pathLength R') ↔ Even (pathLength R)) :
    Nonempty (RungReplacementResult G J H K φ q b₁ b₂ R R' r₁ r₂ r₁' r₂') := by
  classical
  obtain ⟨hbsub, -⟩ := happ
  have hsub : IsSubdivision J H := hbsub.1
  have hbip : H.IsBipartite := hbsub.2
  -- Every clique of the appearance lies in `K`.
  have hNK : ∀ c : W, NSet G H K φ c ⊆ K := by
    rintro c x ⟨e, he, -, rfl⟩
    exact (φ ⟨e, he⟩).2
  have hr₁mem : r₁ ∈ NSet G H K φ b₁ ∩ {x : V | x ∈ R} := by rw [hr₁]; rfl
  have hr₂mem : r₂ ∈ NSet G H K φ b₂ ∩ {x : V | x ∈ R} := by rw [hr₂]; rfl
  -- The old rung is nonempty, so the old branch has an edge.
  have hq2 : 2 ≤ q.length := by
    have hmem : r₁ ∈ rungSet G H K φ q := hRset ▸ hr₁mem.2
    obtain ⟨e, he, ⟨i, hi, -⟩, -⟩ := hmem
    omega
  have hb₁int : b₁ ∉ trackInterior q := fun h => hq.2.1 b₁ h hb₁
  have hb₂int : b₂ ∉ trackInterior q := fun h => hq.2.1 b₂ h hb₂
  have hrung : rungOf G H K φ q = {x : V | x ∈ R} := hRset.symm
  have hclosed := edges_off_branch_avoid_interior hJ hsub hq hq2
  obtain ⟨φ₀, hlab⟩ := exists_resIso G H K φ q hclosed
  -- ## The two residual endpoint cliques
  have hA₁ : NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀ ⟨b₁, hb₁int⟩
      = NSet G H K φ b₁ \ {r₁} :=
    nset_resGraph G H K φ q hclosed φ₀ hlab b₁ hb₁int r₁ (by rw [hrung]; exact hr₁)
  have hA₂ : NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀ ⟨b₂, hb₂int⟩
      = NSet G H K φ b₂ \ {r₂} :=
    nset_resGraph G H K φ q hclosed φ₀ hlab b₂ hb₂int r₂ (by rw [hrung]; exact hr₂)
  -- ## The hypotheses of the labelled add-track step
  have hb₁₂ : b₁ ≠ b₂ := by
    intro hcon
    have h0 : q[0]'(by omega) = b₁ :=
      Workspace.ProofLemmas.SubdivisionCounting.track_head hqf (by omega)
    have hL : q[q.length - 1]'(by omega) = b₂ := by
      have h' := hqf.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
      exact Option.some_injective _ h'
    have := hqf.1.2.1.getElem_inj_iff.mp
      (show q[0]'(by omega) = q[q.length - 1]'(by omega) by rw [h0, hL, hcon])
    omega
  have hne0 : (⟨b₁, hb₁int⟩ : resVerts q) ≠ ⟨b₂, hb₂int⟩ :=
    fun h => hb₁₂ (congrArg Subtype.val h)
  have hnadj := not_resGraph_adj_ends hJ hsub hq hqf hq2 hb₁int hb₂int
  have hR'ends := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR'
  have hnotR : ∀ (c : W) (r : V), NSet G H K φ c ∩ {x : V | x ∈ R} = {r} →
      ∀ y ∈ NSet G H K φ c \ {r}, y ∉ R := by
    intro c r hcr y hy hyR
    exact hy.2 (show y ∈ ({r} : Set V) by rw [← hcr]; exact ⟨hy.1, hyR⟩)
  have h₁ : ∀ (e : Sym2 (resVerts q)) (he : e ∈ (resGraph H q).edgeSet),
      (⟨b₁, hb₁int⟩ : resVerts q) ∈ e → G.Adj r₁' (↑(φ₀ ⟨e, he⟩) : V) := by
    intro e he hb
    have hy : (↑(φ₀ ⟨e, he⟩) : V) ∈ NSet G H K φ b₁ \ {r₁} := by
      rw [← hA₁]; exact ⟨e, he, ⟨he, hb⟩, rfl⟩
    exact (hboundary r₁' hR'ends.1 _ (hNK b₁ hy.1) (hnotR b₁ r₁ hr₁ _ hy)).mpr (Or.inl ⟨rfl, hy⟩)
  have h₂ : ∀ (e : Sym2 (resVerts q)) (he : e ∈ (resGraph H q).edgeSet),
      (⟨b₂, hb₂int⟩ : resVerts q) ∈ e → G.Adj r₂' (↑(φ₀ ⟨e, he⟩) : V) := by
    intro e he hb
    have hy : (↑(φ₀ ⟨e, he⟩) : V) ∈ NSet G H K φ b₂ \ {r₂} := by
      rw [← hA₂]; exact ⟨e, he, ⟨he, hb⟩, rfl⟩
    exact (hboundary r₂' hR'ends.2 _ (hNK b₂ hy.1) (hnotR b₂ r₂ hr₂ _ hy)).mpr (Or.inr ⟨rfl, hy⟩)
  have hPK : ∀ x ∈ R', x ∉ K \ rungOf G H K φ q := by
    intro x hx hcon
    exact hcon.2 (by rw [hrung]; exact hdisj x hx hcon.1)
  have hno : ∀ x ∈ R', ∀ y ∈ K \ rungOf G H K φ q, G.Adj x y →
      (x = r₁' ∧ ∃ (e : Sym2 (resVerts q)) (he : e ∈ (resGraph H q).edgeSet),
        (⟨b₁, hb₁int⟩ : resVerts q) ∈ e ∧ y = (↑(φ₀ ⟨e, he⟩) : V)) ∨
      (x = r₂' ∧ ∃ (e : Sym2 (resVerts q)) (he : e ∈ (resGraph H q).edgeSet),
        (⟨b₂, hb₂int⟩ : resVerts q) ∈ e ∧ y = (↑(φ₀ ⟨e, he⟩) : V)) := by
    intro x hx y hy hadj
    have hyR : y ∉ R := by
      intro hcon
      exact hy.2 (by rw [hrung]; exact hcon)
    rcases (hboundary x hx y hy.1 hyR).mp hadj with ⟨hx1, hy1⟩ | ⟨hx2, hy2⟩
    · refine Or.inl ⟨hx1, ?_⟩
      obtain ⟨e, he, ⟨-, hb⟩, hyeq⟩ : y ∈ NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀
          ⟨b₁, hb₁int⟩ := by rw [hA₁]; exact hy1
      exact ⟨e, he, hb, hyeq⟩
    · refine Or.inr ⟨hx2, ?_⟩
      obtain ⟨e, he, ⟨-, hb⟩, hyeq⟩ : y ∈ NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀
          ⟨b₂, hb₂int⟩ := by rw [hA₂]; exact hy2
      exact ⟨e, he, hb, hyeq⟩
  -- ## Add the new track
  obtain ⟨D, q'Z, psi, hext, hqlen, hold, hnew⟩ :=
    addTrackLabelled G (resGraph H q) (K \ rungOf G H K φ q) φ₀ R' r₁' r₂' hR' hPK
      ⟨b₁, hb₁int⟩ ⟨b₂, hb₂int⟩ hne0 hnadj h₁ h₂ hno
  -- ## Lengths and parity
  have hR'pos : 0 < R'.length := List.length_pos_of_ne_nil hR'.1.1
  have hRpos : 0 < R.length := List.length_pos_of_ne_nil hR.1
  have hRlen : R.length = trackLength q :=
    rung_length_eq_trackLength φ q hq.1 (by simp only [trackLength]; omega) R hR hrung.symm
  have hparZ : Even (trackLength q'Z) ↔ Even (trackLength q) := by
    have h1 : trackLength q'Z = R'.length := by simp only [trackLength, hqlen]; omega
    rw [h1, ← hRlen]
    have e1 := hpar
    simp only [pathLength, Nat.even_iff] at e1 ⊢
    omega
  -- ## Transport to `Fin m`
  haveI : Fintype (resVerts q ⊕ Fin (R'.length - 1)) := Fintype.ofFinite _
  obtain ⟨Hfin, ⟨χ⟩⟩ := Workspace.ProofLemmas.IsoTransport.exists_iso_fin D
  have hsubD : IsSubdivision J D :=
    subdivision_of_replacement hJ hsub hq hqf hq2 hb₁int hb₂int hext
  have hbipD : D.IsBipartite :=
    bipartite_of_replacement hJ hsub hbip hq hqf hq2 hb₁int hb₂int hext hparZ
  have hembb₁ : resEmb q b₁ hb₁int b₁ = ⟨b₁, hb₁int⟩ := resEmb_of_notMem q b₁ hb₁int hb₁int
  have hembb₂ : resEmb q b₁ hb₁int b₂ = ⟨b₂, hb₂int⟩ := resEmb_of_notMem q b₁ hb₁int hb₂int
  have hR'0 : R'[0]'hR'pos = r₁' :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR'.2.1 hR'pos
  have hR'last : R'[R'.length - 1]'(by omega) = r₂' :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR'.2.2 hR'pos
  have hmapback : ∀ l : List (resVerts q ⊕ Fin (R'.length - 1)),
      (l.map ⇑χ).map ⇑χ.symm = l := by
    intro l
    rw [List.map_map]
    simp
  -- the transported rung dictionary
  have hrungTrans : ∀ l : List (resVerts q ⊕ Fin (R'.length - 1)),
      rungSet G Hfin ((K \ rungOf G H K φ q) ∪ {x : V | x ∈ R'})
          ((Thm75Claim2Transport.lineGraphIso χ).symm.trans psi) (l.map ⇑χ)
        = rungSet G D ((K \ rungOf G H K φ q) ∪ {x : V | x ∈ R'}) psi l := by
    intro l
    have := Thm75Claim2Transport.rungSet_map χ psi (l.map ⇑χ)
    rw [hmapback l] at this
    exact this.symm
  refine ⟨{
    m := Fintype.card (resVerts q ⊕ Fin (R'.length - 1))
    H' := Hfin
    K' := (K \ rungOf G H K φ q) ∪ {x : V | x ∈ R'}
    φ' := (Thm75Claim2Transport.lineGraphIso χ).symm.trans psi
    happ := ⟨⟨Workspace.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso χ hsubD,
      SimpleGraph.Colorable.of_hom χ.symm.toHom hbipD⟩,
      ⟨(Thm75Claim2Transport.lineGraphIso χ).symm.trans psi⟩⟩
    ι := fun w => χ (Sum.inl (resEmb q b₁ hb₁int w))
    ιinj := ?_
    q' := q'Z.map ⇑χ
    hq' := ?_
    hq'from := ?_
    hq'len := ?_
    hK' := by rw [hrung]
    hrung' := ?_
    hleft := ?_
    hright := ?_
    hother := ?_
    hbranches := ?_ }⟩
  · -- `ι` is injective on branch-vertices
    intro c hc c' hc' hcc
    have h1 : c ∉ trackInterior q := fun h => hq.2.1 c h hc
    have h2 : c' ∉ trackInterior q := fun h => hq.2.1 c' h hc'
    have := (EquivLike.injective χ) hcc
    rw [resEmb_of_notMem q b₁ hb₁int h1, resEmb_of_notMem q b₁ hb₁int h2] at this
    exact congrArg Subtype.val (Sum.inl_injective this)
  · exact Thm75Claim2Transport.isBranch_map χ (isBranch_new hJ hsub hq hqf hq2 hb₁int hb₂int hext)
  · have := Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map χ hext.track
    rw [hembb₁, hembb₂]
    exact this
  · simp only [trackLength, List.length_map, hqlen, pathLength]
    omega
  · rw [hrungTrans q'Z]
    exact rung_new hext hqlen hnew
  · rw [hembb₁, RungReplacementTransport.nset_map χ psi (Sum.inl (⟨b₁, hb₁int⟩ : resVerts q)),
      nset_left hext hqlen hR'pos hold hnew, hA₁, hR'0]
  · rw [hembb₂, RungReplacementTransport.nset_map χ psi (Sum.inl (⟨b₂, hb₂int⟩ : resVerts q)),
      nset_right hext hqlen hR'pos hold hnew, hA₂, hR'last]
  · intro c hcint hc₁ hc₂
    have hcq : c ∉ q := by
      intro hcon
      rcases mem_track_cases hqf hq2 hcon with h | h | h
      · exact hc₁ h
      · exact hc₂ h
      · exact hcint h
    rw [resEmb_of_notMem q b₁ hb₁int hcint,
      RungReplacementTransport.nset_map χ psi (Sum.inl (⟨c, hcint⟩ : resVerts q)),
      nset_other hext hold ⟨c, hcint⟩ (fun h => hc₁ (congrArg Subtype.val h))
        (fun h => hc₂ (congrArg Subtype.val h))]
    exact nset_resGraph_of_notMem G H K φ q hclosed φ₀ hlab c hcq hcint
  · intro p u v hp hpf hpne
    have hp2 := two_le_length_of_isBranch hJ hsub hp
    have hpin := other_branch_avoids_interior hJ hsub hq hq2 hp hp2 hpne
    obtain ⟨hbr, htr⟩ :=
      branch_survives hJ hsub hq hqf hq2 hb₁int hb₂int hext hp hp2 hpf hpne
    have hmapeq : p.map (fun w => χ (Sum.inl (resEmb q b₁ hb₁int w)))
        = (p.map (fun w => Sum.inl (resEmb q b₁ hb₁int w))).map ⇑χ := by
      rw [List.map_map]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hmapeq]; exact Thm75Claim2Transport.isBranch_map χ hbr
    · rw [hmapeq]; exact Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map χ htr
    · have hpE : ∀ (i : ℕ) (hi : i + 1 < p.length),
          s(p[i]'(by omega), p[i + 1]'hi) ∈ H.edgeSet := fun i hi => hp.1.2.2 i hi
      have hpq : ∀ (i : ℕ) (hi : i + 1 < p.length),
          s(p[i]'(by omega), p[i + 1]'hi) ∉ trackEdges q := fun i hi =>
        trackEdges_disjoint_of_ne hJ hsub hq hq2 hp hp2 hpne _ ⟨i, hi, rfl⟩
      have hlift : ∀ (i : ℕ) (hi : i + 1 < (p.map (resEmb q b₁ hb₁int)).length),
          s((p.map (resEmb q b₁ hb₁int))[i]'(by omega),
            (p.map (resEmb q b₁ hb₁int))[i + 1]'hi) ∈ (resGraph H q).edgeSet := by
        intro i hi
        have hi' : i + 1 < p.length := by simpa using hi
        simp only [List.getElem_map]
        rw [resEmb_of_notMem q b₁ hb₁int (hpin _ (List.getElem_mem _)),
          resEmb_of_notMem q b₁ hb₁int (hpin _ (List.getElem_mem _))]
        exact ⟨hpE i hi', hpq i hi'⟩
      have hmapeq2 : p.map (fun w => (Sum.inl (resEmb q b₁ hb₁int w) :
            resVerts q ⊕ Fin (R'.length - 1)))
          = (p.map (resEmb q b₁ hb₁int)).map
            (Sum.inl : resVerts q → resVerts q ⊕ Fin (R'.length - 1)) := by
        rw [List.map_map]; rfl
      rw [hmapeq, hrungTrans, hmapeq2]
      exact Eq.trans (rung_old hext hold (p.map (resEmb q b₁ hb₁int)) hlift)
        (rung_resGraph G H K φ q b₁ hb₁int φ₀ hlab p hpin hpE hpq)

end Workspace.ProofLemmas.RungReplacementLabelled
