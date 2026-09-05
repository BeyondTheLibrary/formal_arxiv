import Workspace.ProofLemmas.Thm58StarStarGapTracks
import Workspace.ProofLemmas.Thm58StarStarGapBranchConn
import Workspace.ProofLemmas.Thm58StarStarGapOffBranchTransport
import Workspace.Statements.S05.Thm_5_6

/-!
# 5.6 applied off the branch, for 5.8 (4)

Claim (4) of 5.8 runs the argument of claim (3) inside the graph obtained from `H` by deleting
the branch `R_{v₁v₂}`.  Two facts about that graph are used and not proved in the paper: it is
connected (so the first track exists), and it satisfies the hypotheses of 5.6 (so the second
track exists).  Both are isolated here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapOffBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism
open Thm58StarStarGapOffBranchConn Thm58StarStarGapOffBranchTransport

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- PAPER, proof of 5.8 (4), printed p. 27, the implicit premise of *"There is a path `S₁`
from `A₁` to `A₂` with no vertex in `N_{v₁} ∪ N_{v₂} ∪ V(R_{v₁v₂})` except for its ends"*: the
graph obtained from `H` by deleting the branch `R_{v₁v₂}` — its two ends `v₁, v₂` and its
internal vertices — is connected.  Proved in `Thm58StarStarGapBranchConn`. -/
theorem branch_complement_connected {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) :
    ConnectedSet H ({x : W | x ∈ q}ᶜ) :=
  Thm58StarStarGapBranchConn.branch_complement_connected hc3 hq hq2

/-- The far end of an edge at an end of the branch that is not an edge of the branch lies off
the branch. -/
theorem far_end_off_branch {H : SimpleGraph W} {q : List W} {c₁ c₂ : W}
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hchord : ∀ f ∈ H.edgeSet, c₁ ∈ f → c₂ ∈ f → f ∈ trackEdges q)
    {c : W} (hc : c = c₁ ∨ c = c₂) {e : Sym2 W} (he : e ∈ H.edgeSet) (hce : c ∈ e)
    (hE : e ∉ trackEdges q) : ∃ a, e = s(c, a) ∧ H.Adj c a ∧ a ∉ q := by
  classical
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hce
  have hadj : H.Adj c a := he
  refine ⟨a, rfl, hadj, ?_⟩
  intro haq
  by_cases hint : a ∈ trackInterior q
  · obtain ⟨j, hj, hja⟩ := SubdivisionCounting.mem_trackInterior_iff q a |>.mp hint
    have hsub : incidentEdges H (q[j + 1]'(by omega)) ⊆ trackEdges q :=
      Thm57Claim2Structure.incidentEdges_internal_subset hq (by omega) (by omega)
    rw [hja] at hsub
    exact hE (hsub ⟨he, Sym2.mem_mk_right _ _⟩)
  · have hends := SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 haq hint
    have hne : a ≠ c := hadj.ne'
    refine hE (hchord _ he ?_ ?_)
    · rcases hc with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · rcases hends with rfl | rfl
        · exact Sym2.mem_mk_right _ _
        · exact absurd rfl hne
    · rcases hc with rfl | rfl
      · rcases hends with rfl | rfl
        · exact absurd rfl hne
        · exact Sym2.mem_mk_right _ _
      · exact Sym2.mem_mk_left _ _

/-- GAP — PAPER, proof of 5.8 (4), printed p. 27: *"Then we can apply 5.6 to the graph obtained
from `H` by deleting the edges and internal vertices of the branch between `v₁` and `v₂`.  We
deduce (possibly after exchanging `v₁` and `v₂`) that there is a path `S₂` of `L(H)` with first
vertex in `A₁`, second vertex in `B₁`, last vertex in `A₂`, and otherwise disjoint from
`N_{v₁} ∪ N_{v₂} ∪ V(R_{v₁v₂})`."*

The graph the paper applies 5.6 to is `H` with the edges and the internal vertices of the
branch `q` removed; `A₁, B₁` partition the edges at `v₁` that survive, and likewise `A₂, B₂` at
`v₂`.  A track of that graph is a track of `H` no edge of which lies on `q`, which is the form
the conclusion takes here.  The two alternatives are the paper's *"possibly after exchanging
`v₁` and `v₂`"*. -/
theorem five_six_off_branch {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H)
    {c₁ c₂ : W} {q : List W} (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂)
    (hq2 : 2 ≤ q.length)
    (hchord : ∀ f ∈ H.edgeSet, c₁ ∈ f → c₂ ∈ f → f ∈ trackEdges q)
    (A₁ B₁ A₂ B₂ : Set (Sym2 W))
    (hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁ \ trackEdges q) (hdisj₁ : Disjoint A₁ B₁)
    (hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂ \ trackEdges q) (hdisj₂ : Disjoint A₂ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB : B₁.Nonempty ∨ B₂.Nonempty)
    (hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e) :
    (∃ (t : List W) (_ht : 3 ≤ t.length), IsTrackList H t ∧
        (∀ e ∈ trackEdges t, e ∉ trackEdges q) ∧
        s(t[0], t[1]) ∈ A₁ ∧ s(t[1], t[2]) ∈ B₁ ∧
        t.getLast? = some c₂ ∧ s(t[t.length - 2], t[t.length - 1]) ∈ A₂) ∨
    (∃ (t : List W) (_ht : 3 ≤ t.length), IsTrackList H t ∧
        (∀ e ∈ trackEdges t, e ∉ trackEdges q) ∧
        s(t[0], t[1]) ∈ A₂ ∧ s(t[1], t[2]) ∈ B₂ ∧
        t.getLast? = some c₁ ∧ s(t[t.length - 2], t[t.length - 1]) ∈ A₁) := by
  classical
  -- The graph 5.6 is applied to: `H` with the edges of the branch `q` deleted, restricted to
  -- the vertices that are not internal vertices of `q`.
  set S : Set W := {x : W | x ∉ trackInterior q} with hSdef
  haveI : Fintype ↥S := Fintype.ofFinite _
  haveI : DecidableEq ↥S := fun a b => Classical.dec _
  have hnd : q.Nodup := hq.1.2.1
  have hc₁S : c₁ ∈ S := head_notMem_trackInterior hnd hfrom.2.1
  have hc₂S : c₂ ∈ S := getLast_notMem_trackInterior hnd hfrom.2.2
  have hc₁q : c₁ ∈ q := List.mem_of_head? hfrom.2.1
  have hc₂q : c₂ ∈ q := List.mem_of_getLast? hfrom.2.2
  have hne12 : c₁ ≠ c₂ := ends_ne hnd hq2 hfrom
  -- the far end of every edge of the four parts lies off the branch
  have hfar : ∀ c : W, (c = c₁ ∨ c = c₂) → ∀ e ∈ incidentEdges H c \ trackEdges q,
      ∃ a, e = s(c, a) ∧ H.Adj c a ∧ a ∉ q := fun c hc e he =>
    far_end_off_branch hq hfrom hq2 hchord hc he.1.1 he.1.2 he.2
  -- hence every such edge survives in the deleted graph
  have hlift : ∀ c : W, (c = c₁ ∨ c = c₂) → ∀ e ∈ incidentEdges H c \ trackEdges q,
      ∃ e' : Sym2 ↥S, Sym2.map Subtype.val e' = e := by
    intro c hc e he
    obtain ⟨a, rfl, hadj, haq⟩ := hfar c hc e he
    have hcS : c ∈ S := by rcases hc with rfl | rfl <;> assumption
    have haS : a ∈ S := fun hcon => haq (SubdivisionCompose.mem_of_mem_trackInterior hcon)
    exact ⟨s(⟨c, hcS⟩, ⟨a, haS⟩), by simp⟩
  -- no edge of the branch survives between two vertices of `H \ {c, a}` off the branch
  have hedgeY : ∀ c a : W, (c = c₁ ∨ c = c₂) →
      ∀ x ∈ (({c, a} : Set W)ᶜ) \ {x : W | x ∈ trackInterior q},
      ∀ y ∈ (({c, a} : Set W)ᶜ) \ {x : W | x ∈ trackInterior q},
      s(x, y) ∉ trackEdges q := by
    intro c a hc x hx y hy hmem
    rcases trackEdge_endpoint hfrom hmem with ⟨z, hz, hze⟩ | heq
    · rcases Sym2.mem_iff.mp hze with h | h
      · exact hx.2 (h ▸ hz)
      · exact hy.2 (h ▸ hz)
    · have hcmem : c ∈ s(x, y) := by
        rw [heq]
        rcases hc with rfl | rfl
        · exact Sym2.mem_mk_left _ _
        · exact Sym2.mem_mk_right _ _
      rcases Sym2.mem_iff.mp hcmem with h | h
      · exact hx.1 (Or.inl h.symm)
      · exact hy.1 (Or.inl h.symm)
  -- PAPER: the premise *"for every edge `uv ∈ A₁ ∪ A₂`, `H \ {u, v}` is connected"* of 5.6,
  -- read in the deleted graph
  have hpairconn : ∀ (c a : W) (u v : ↥S), (c = c₁ ∨ c = c₂) → a ∉ q → H.Adj c a →
      (((u : W) = c ∧ (v : W) = a) ∨ ((u : W) = a ∧ (v : W) = c)) →
      ConnectedSet (del H (trackEdges q) S) (({u, v} : Set ↥S)ᶜ) := by
    intro c a u v hc haq hadj huv
    have hmemuv : ∀ x : W, (x = (u : W) ∨ x = (v : W)) ↔ (x = c ∨ x = a) := by
      rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    have hY : ConnectedSet H ((({c, a} : Set W)ᶜ) \ {x : W | x ∈ trackInterior q}) := by
      rcases hc with rfl | rfl
      · exact interior_edge_complement_connected hc3 hq hfrom hq2 (Or.inl rfl) (Or.inr rfl)
          hne12 haq hadj
      · exact interior_edge_complement_connected hc3 hq hfrom hq2 (Or.inr rfl) (Or.inl rfl)
          (Ne.symm hne12) haq hadj
    refine connectedSet_del ?_ (hedgeY c a hc) hY
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx2, ?_⟩
      rintro (h | h)
      · exact hx1 ((hmemuv x).mp (Or.inl (congrArg Subtype.val h)))
      · exact hx1 ((hmemuv x).mp (Or.inr (congrArg Subtype.val h)))
    · rintro ⟨hxS, hxT⟩
      refine ⟨?_, hxS⟩
      intro hcon
      rcases (hmemuv x).mpr hcon with h | h
      · exact hxT (Or.inl (Subtype.ext h))
      · exact hxT (Or.inr (Subtype.ext h))
  -- the premises of 5.6, one by one
  have hnadj' : ¬ (del H (trackEdges q) S).Adj ⟨c₁, hc₁S⟩ ⟨c₂, hc₂S⟩ := by
    intro hadj
    rw [del_adj] at hadj
    exact hadj.2 (hchord _ hadj.1 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _))
  have hconn' : ConnectedSet (del H (trackEdges q) S)
      (({⟨c₁, hc₁S⟩, ⟨c₂, hc₂S⟩} : Set ↥S)ᶜ) := by
    refine connectedSet_del ?_ ?_ (branch_complement_connected hc3 hq hq2)
    · intro x
      constructor
      · intro hx
        have hxS : x ∈ S := fun hcon => hx (SubdivisionCompose.mem_of_mem_trackInterior hcon)
        refine ⟨hxS, ?_⟩
        rintro (h | h)
        · exact hx (by rw [show x = c₁ from congrArg Subtype.val h]; exact hc₁q)
        · exact hx (by rw [show x = c₂ from congrArg Subtype.val h]; exact hc₂q)
      · rintro ⟨hxS, hxT⟩ hxq
        rcases (mem_iff_interior_or_end hfrom).mp hxq with h | h | h
        · exact hxS h
        · exact hxT (Or.inl (Subtype.ext h))
        · exact hxT (Or.inr (Subtype.ext h))
    · intro x hx y _ hmem
      exact hx (BranchClassification.mem_of_mem_trackEdges hmem).1
  have hpartS₁ : Sym2.map Subtype.val ⁻¹' A₁ ∪ Sym2.map Subtype.val ⁻¹' B₁
      = incidentEdges (del H (trackEdges q) S) ⟨c₁, hc₁S⟩ := by
    rw [incidentEdges_del hc₁S, ← hpart₁, Set.preimage_union]
  have hpartS₂ : Sym2.map Subtype.val ⁻¹' A₂ ∪ Sym2.map Subtype.val ⁻¹' B₂
      = incidentEdges (del H (trackEdges q) S) ⟨c₂, hc₂S⟩ := by
    rw [incidentEdges_del hc₂S, ← hpart₂, Set.preimage_union]
  have hdisjS₁ : Disjoint (Sym2.map Subtype.val ⁻¹' A₁ : Set (Sym2 ↥S))
      (Sym2.map Subtype.val ⁻¹' B₁) := by
    rw [Set.disjoint_left]
    exact fun e he he' => Set.disjoint_left.mp hdisj₁ he he'
  have hdisjS₂ : Disjoint (Sym2.map Subtype.val ⁻¹' A₂ : Set (Sym2 ↥S))
      (Sym2.map Subtype.val ⁻¹' B₂) := by
    rw [Set.disjoint_left]
    exact fun e he he' => Set.disjoint_left.mp hdisj₂ he he'
  have hne : ∀ (c : W) (C D : Set (Sym2 W)), (c = c₁ ∨ c = c₂) →
      C ∪ D = incidentEdges H c \ trackEdges q → C.Nonempty →
      (Sym2.map Subtype.val ⁻¹' C : Set (Sym2 ↥S)).Nonempty := by
    intro c C D hc hpart hC
    obtain ⟨e, he⟩ := hC
    obtain ⟨e', he'⟩ := hlift c hc e (hpart ▸ Set.mem_union_left D he)
    exact ⟨e', by rw [Set.mem_preimage, he']; exact he⟩
  have hAS₁ := hne c₁ A₁ B₁ (Or.inl rfl) hpart₁ hA₁
  have hAS₂ := hne c₂ A₂ B₂ (Or.inr rfl) hpart₂ hA₂
  have hBS : (Sym2.map Subtype.val ⁻¹' B₁ : Set (Sym2 ↥S)).Nonempty ∨
      (Sym2.map Subtype.val ⁻¹' B₂ : Set (Sym2 ↥S)).Nonempty := by
    rcases hB with h | h
    · exact Or.inl (hne c₁ B₁ A₁ (Or.inl rfl) (by rw [Set.union_comm]; exact hpart₁) h)
    · exact Or.inr (hne c₂ B₂ A₂ (Or.inr rfl) (by rw [Set.union_comm]; exact hpart₂) h)
  have hAconnS : ∀ e ∈ (Sym2.map Subtype.val ⁻¹' A₁ ∪ Sym2.map Subtype.val ⁻¹' A₂ :
        Set (Sym2 ↥S)),
      ∀ u v : ↥S, e = s(u, v) →
        ConnectedSet (del H (trackEdges q) S) (({u, v} : Set ↥S)ᶜ) := by
    intro e he u v huv
    subst huv
    have hmapeq : Sym2.map Subtype.val s(u, v) = s((u : W), (v : W)) := by simp
    rcases he with he | he
    · rw [Set.mem_preimage, hmapeq] at he
      obtain ⟨a, hea, hadj, haq⟩ :=
        hfar c₁ (Or.inl rfl) _ (hpart₁ ▸ Set.mem_union_left B₁ he)
      refine hpairconn c₁ a u v (Or.inl rfl) haq hadj ?_
      rcases Sym2.eq_iff.mp hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    · rw [Set.mem_preimage, hmapeq] at he
      obtain ⟨a, hea, hadj, haq⟩ :=
        hfar c₂ (Or.inr rfl) _ (hpart₂ ▸ Set.mem_union_left B₂ he)
      refine hpairconn c₂ a u v (Or.inr rfl) haq hadj ?_
      rcases Sym2.eq_iff.mp hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  have hnocoverS : ¬ ∃ w : ↥S, ∀ e ∈ (Sym2.map Subtype.val ⁻¹' A₁ ∪
      Sym2.map Subtype.val ⁻¹' A₂ : Set (Sym2 ↥S)), w ∈ e := by
    rintro ⟨w, hw⟩
    refine hnocover ⟨(w : W), ?_⟩
    intro e he
    have key : ∀ (c : W) (C D : Set (Sym2 W)), (c = c₁ ∨ c = c₂) →
        C ∪ D = incidentEdges H c \ trackEdges q → e ∈ C →
        (∀ e' : Sym2 ↥S, e' ∈ (Sym2.map Subtype.val ⁻¹' C : Set (Sym2 ↥S)) → w ∈ e') →
        (w : W) ∈ e := by
      intro c C D hc hpart heC hcov
      obtain ⟨e', he'⟩ := hlift c hc e (hpart ▸ Set.mem_union_left D heC)
      have hwe' : w ∈ e' := hcov e' (by rw [Set.mem_preimage, he']; exact heC)
      rw [← he']
      exact Sym2.mem_map.mpr ⟨w, hwe', rfl⟩
    rcases he with he | he
    · exact key c₁ A₁ B₁ (Or.inl rfl) hpart₁ he (fun e' h => hw e' (Or.inl h))
    · exact key c₂ A₂ B₂ (Or.inr rfl) hpart₂ he (fun e' h => hw e' (Or.inr h))
  -- 5.6, applied to the deleted graph
  rcases Workspace.Statements.S05.SPGT.thm_5_6 (del H (trackEdges q) S)
      ⟨c₁, hc₁S⟩ ⟨c₂, hc₂S⟩ hnadj' hconn' _ _ _ _ hpartS₁ hdisjS₁ hpartS₂ hdisjS₂
      hAS₁ hAS₂ hBS hAconnS hnocoverS with
    ⟨t, ht3, htrack, htA, htB, htlast, htA'⟩ | ⟨t, ht3, htrack, htA, htB, htlast, htA'⟩
  · refine Or.inl ⟨t.map Subtype.val, by rw [List.length_map]; exact ht3,
      isTrackList_map htrack, trackEdges_map_notMem htrack, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem_map, List.getElem_map]; exact htA
    · rw [List.getElem_map, List.getElem_map]; exact htB
    · rw [List.getLast?_map, htlast]; rfl
    · simp only [List.length_map]
      rw [List.getElem_map, List.getElem_map]; exact htA'
  · refine Or.inr ⟨t.map Subtype.val, by rw [List.length_map]; exact ht3,
      isTrackList_map htrack, trackEdges_map_notMem htrack, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem_map, List.getElem_map]; exact htA
    · rw [List.getElem_map, List.getElem_map]; exact htB
    · rw [List.getLast?_map, htlast]; rfl
    · simp only [List.length_map]
      rw [List.getElem_map, List.getElem_map]; exact htA'


/-! ## The two parts of the edges at a star vertex, off the branch -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
  {φ : H.lineGraph ≃g G.induce K}

/-- PAPER, proof of 5.8 (4), printed p. 27: *"Let `A₁` be the set of vertices in
`N_{v₁} \ {r₁}` adjacent to `p₁`"*. -/
def adjPartOff (G : SimpleGraph V) {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (p : V) (c : Fin n) (E : Set (Sym2 (Fin n))) :
    Set (Sym2 (Fin n)) :=
  {e | ∃ he : e ∈ H.edgeSet, c ∈ e ∧ e ∉ E ∧ G.Adj p (φ ⟨e, he⟩ : V)}

/-- PAPER, proof of 5.8 (4), printed p. 27: *"and `B₁ = N_{v₁} \ (A₁ ∪ r₁)`"*. -/
def nonAdjPartOff (G : SimpleGraph V) {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (p : V) (c : Fin n) (E : Set (Sym2 (Fin n))) :
    Set (Sym2 (Fin n)) :=
  {e | ∃ he : e ∈ H.edgeSet, c ∈ e ∧ e ∉ E ∧ ¬ G.Adj p (φ ⟨e, he⟩ : V)}

theorem partOff_union (p : V) (c : Fin n) (E : Set (Sym2 (Fin n))) :
    adjPartOff G φ p c E ∪ nonAdjPartOff G φ p c E = incidentEdges H c \ E := by
  classical
  ext e
  constructor
  · rintro (⟨he, hce, hE, -⟩ | ⟨he, hce, hE, -⟩) <;> exact ⟨⟨he, hce⟩, hE⟩
  · rintro ⟨⟨he, hce⟩, hE⟩
    by_cases hadj : G.Adj p (φ ⟨e, he⟩ : V)
    · exact Or.inl ⟨he, hce, hE, hadj⟩
    · exact Or.inr ⟨he, hce, hE, hadj⟩

theorem partOff_disjoint (p : V) (c : Fin n) (E : Set (Sym2 (Fin n))) :
    Disjoint (adjPartOff G φ p c E) (nonAdjPartOff G φ p c E) := by
  rw [Set.disjoint_left]
  rintro e ⟨he, -, -, hadj⟩ ⟨he', -, -, hnadj⟩
  exact hnadj hadj

theorem mem_incident_of_adjPartOff {p : V} {c : Fin n} {E : Set (Sym2 (Fin n))}
    {e : Sym2 (Fin n)} (he : e ∈ adjPartOff G φ p c E) : c ∈ e := he.choose_spec.1

theorem mem_incident_of_nonAdjPartOff {p : V} {c : Fin n} {E : Set (Sym2 (Fin n))}
    {e : Sym2 (Fin n)} (he : e ∈ nonAdjPartOff G φ p c E) : c ∈ e := he.choose_spec.1

/-- A vertex of the star of `c` off the rung, adjacent to `p`, comes from an edge of
`adjPartOff`. -/
theorem exists_adjPartOff_edge {N : Fin n → Set V} {q : List (Fin n)} {R : List V} {r : V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    {c : Fin n} (hi : N c ∩ {x : V | x ∈ R} = {r})
    {p x : V} (hx : x ∈ N c \ {r}) (hadj : G.Adj p x) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ adjPartOff G φ p c (trackEdges q) ∧ x = (φ ⟨e, he⟩ : V) := by
  have hxN := hx.1
  rw [hstar c] at hxN
  obtain ⟨e, he, hce, rfl⟩ := hxN
  refine ⟨e, he, ⟨he, hce.2, ?_, hadj⟩, rfl⟩
  intro hEq
  have hmem : (φ ⟨e, he⟩ : V) ∈ N c ∩ {y : V | y ∈ R} := by
    refine ⟨hx.1, ?_⟩
    rw [hRset]
    exact ⟨e, he, hEq, rfl⟩
  rw [hi] at hmem
  exact hx.2 hmem

/-- A vertex of the star of `c` off the rung, not adjacent to `p`, comes from an edge of
`nonAdjPartOff`. -/
theorem exists_nonAdjPartOff_edge {N : Fin n → Set V} {q : List (Fin n)} {R : List V} {r : V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    {c : Fin n} (hi : N c ∩ {x : V | x ∈ R} = {r})
    {p x : V} (hx : x ∈ N c \ {r}) (hadj : ¬ G.Adj p x) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ nonAdjPartOff G φ p c (trackEdges q) ∧ x = (φ ⟨e, he⟩ : V) := by
  have hxN := hx.1
  rw [hstar c] at hxN
  obtain ⟨e, he, hce, rfl⟩ := hxN
  refine ⟨e, he, ⟨he, hce.2, ?_, hadj⟩, rfl⟩
  intro hEq
  have hmem : (φ ⟨e, he⟩ : V) ∈ N c ∩ {y : V | y ∈ R} := by
    refine ⟨hx.1, ?_⟩
    rw [hRset]
    exact ⟨e, he, hEq, rfl⟩
  rw [hi] at hmem
  exact hx.2 hmem

theorem edge_of_adjPartOff {p : V} {c : Fin n} {E : Set (Sym2 (Fin n))}
    {e : Sym2 (Fin n)} (he : e ∈ adjPartOff G φ p c E) : e ∈ H.edgeSet := he.choose

theorem notMem_of_adjPartOff {p : V} {c : Fin n} {E : Set (Sym2 (Fin n))}
    {e : Sym2 (Fin n)} (he : e ∈ adjPartOff G φ p c E) : e ∉ E := he.choose_spec.2.1

theorem notMem_of_nonAdjPartOff {p : V} {c : Fin n} {E : Set (Sym2 (Fin n))}
    {e : Sym2 (Fin n)} (he : e ∈ nonAdjPartOff G φ p c E) : e ∉ E := he.choose_spec.2.1

end Workspace.ProofLemmas.Thm58StarStarGapOffBranch
