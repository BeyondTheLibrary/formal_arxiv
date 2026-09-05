import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.NoCrossTrackBranch

/-!
# 5.5 — reduction to the two structural facts about a subdivision

For subgraphs `C,D` with `C \sqcup D = H`, put `S = V(C) \cap V(D)`.  The vertices in
`V(C) \ V(D)` and `V(D) \ V(C)` are nonempty and no edge joins the two sets.  Thus each of
these two sets is closed under adjacency in `H-S`.

The proof below packages the elementary subgraph bookkeeping.  Its two hypotheses are the
two facts about a subdivision that carry the graph theory in the paper's sentence

> *"Then one of `C,D` is contained in a branch of `H`."*

They will be supplied by `Thm55Structure`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm55Reduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Every end of an edge of a subgraph belongs to its vertex set. -/
theorem edge_ends_mem_subgraph {H : SimpleGraph W} (C : H.Subgraph) {e : Sym2 W}
    (he : e ∈ C.edgeSet) : ∀ w ∈ e, w ∈ C.verts := by
  induction e using Sym2.ind with
  | _ u v =>
      intro w hw
      have hadj : C.Adj u v := he
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hadj.fst_mem
      · exact hadj.snd_mem

/-- Every edge of a subgraph is an edge of its host graph. -/
theorem edge_mem_host {H : SimpleGraph W} (C : H.Subgraph) {e : Sym2 W}
    (he : e ∈ C.edgeSet) : e ∈ H.edgeSet := by
  induction e using Sym2.ind with
  | _ u v => exact C.adj_sub he

/-- The part belonging only to `C` is closed under adjacency after deleting the overlap. -/
theorem left_closed {H : SimpleGraph W} (C D : H.Subgraph) (hunion : C ⊔ D = ⊤) :
    ∀ c ∈ C.verts \ D.verts, ∀ w ∈ (C.verts ∩ D.verts)ᶜ,
      H.Adj c w → w ∈ C.verts \ D.verts := by
  intro c hc w hw hadj
  have htop : (⊤ : H.Subgraph).Adj c w := hadj
  rw [← hunion, SimpleGraph.Subgraph.sup_adj] at htop
  rcases htop with hC | hD
  · refine ⟨hC.snd_mem, ?_⟩
    intro hwD
    exact hw ⟨hC.snd_mem, hwD⟩
  · exact absurd hD.fst_mem hc.2

/-- The part belonging only to `D` is closed under adjacency after deleting the overlap. -/
theorem right_closed {H : SimpleGraph W} (C D : H.Subgraph) (hunion : C ⊔ D = ⊤) :
    ∀ d ∈ D.verts \ C.verts, ∀ w ∈ (C.verts ∩ D.verts)ᶜ,
      H.Adj d w → w ∈ D.verts \ C.verts := by
  intro d hd w hw hadj
  have htop : (⊤ : H.Subgraph).Adj d w := hadj
  rw [← hunion, SimpleGraph.Subgraph.sup_adj] at htop
  rcases htop with hC | hD
  · exact absurd hC.fst_mem hd.2
  · refine ⟨hD.snd_mem, ?_⟩
    intro hwC
    exact hw ⟨hwC, hD.snd_mem⟩

/-- The vertices of either subgraph are its exclusive vertices together with the overlap. -/
theorem verts_eq_sdiff_union_inter {H : SimpleGraph W} (C D : H.Subgraph)
    (hunion : C ⊔ D = ⊤) :
    C.verts = (C.verts \ D.verts) ∪ (C.verts ∩ D.verts) ∧
    D.verts = (D.verts \ C.verts) ∪ (C.verts ∩ D.verts) := by
  constructor <;> ext w
  · constructor
    · intro hw
      by_cases hD : w ∈ D.verts
      · exact Or.inr ⟨hw, hD⟩
      · exact Or.inl ⟨hw, hD⟩
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  · constructor
    · intro hw
      by_cases hC : w ∈ C.verts
      · exact Or.inr ⟨hC, hw⟩
      · exact Or.inl ⟨hw, hC⟩
    · rintro (⟨hw, -⟩ | ⟨-, hw⟩) <;> exact hw

/-- The non-spanning assumptions make both exclusive sides nonempty. -/
theorem exclusive_nonempty {H : SimpleGraph W} (C D : H.Subgraph)
    (hunion : C ⊔ D = ⊤) (hCne : C.verts ≠ Set.univ) (hDne : D.verts ≠ Set.univ) :
    (C.verts \ D.verts).Nonempty ∧ (D.verts \ C.verts).Nonempty := by
  have hall : C.verts ∪ D.verts = Set.univ := by
    rw [← SimpleGraph.Subgraph.verts_sup, hunion, SimpleGraph.Subgraph.verts_top]
  constructor
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ D.verts := by
      simpa [Set.eq_univ_iff_forall] using hDne
    have hwU : w ∈ C.verts ∪ D.verts := by rw [hall]; exact Set.mem_univ w
    rcases hwU with hwC | hwD
    · exact ⟨w, hwC, hw⟩
    · exact absurd hwD hw
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ C.verts := by
      simpa [Set.eq_univ_iff_forall] using hCne
    have hwU : w ∈ C.verts ∪ D.verts := by rw [hall]; exact Set.mem_univ w
    rcases hwU with hwC | hwD
    · exact absurd hwC hw
    · exact ⟨w, hwD, hw⟩

/-- The complete reduction of 5.5 once its two subdivision facts are available. -/
theorem reduce
    (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H) (C D : H.Subgraph)
    (hunion : C ⊔ D = ⊤) (hcap : (C ⊓ D).verts.ncard ≤ 2)
    (hCne : C.verts ≠ Set.univ) (hDne : D.verts ≠ Set.univ)
    (branch_reach : ∀ {x y : W}, x ∈ branchVertices H → y ∈ branchVertices H →
      x ∈ (C.verts ∩ D.verts)ᶜ → y ∈ (C.verts ∩ D.verts)ᶜ →
      RchIn H (C.verts ∩ D.verts)ᶜ x y)
    (branchless_side : ∀ E : Set W, E.Nonempty → E ⊆ (C.verts ∩ D.verts)ᶜ →
      (∀ e ∈ E, ∀ w ∈ (C.verts ∩ D.verts)ᶜ, H.Adj e w → w ∈ E) →
      (∀ e ∈ E, e ∉ branchVertices H) →
      ∃ q : List W, IsBranch H q ∧
        E ∪ (C.verts ∩ D.verts) ⊆ {v : W | v ∈ q} ∧
        {e ∈ H.edgeSet | ∀ w ∈ e, w ∈ E ∪ (C.verts ∩ D.verts)} ⊆ trackEdges q) :
    (∃ q : List W, IsBranch H q ∧ C.verts ⊆ {v : W | v ∈ q} ∧
      C.edgeSet ⊆ trackEdges q) ∨
    (∃ q : List W, IsBranch H q ∧ D.verts ⊆ {v : W | v ∈ q} ∧
      D.edgeSet ⊆ trackEdges q) := by
  let S : Set W := C.verts ∩ D.verts
  let L : Set W := C.verts \ D.verts
  let R : Set W := D.verts \ C.verts
  have hcard : S.ncard ≤ 2 := by simpa [S] using hcap
  have hne : L.Nonempty ∧ R.Nonempty := by
    simpa [L, R] using exclusive_nonempty C D hunion hCne hDne
  have hLS : L ⊆ Sᶜ := by
    rintro w ⟨hwC, hwD⟩ ⟨-, h⟩
    exact hwD h
  have hRS : R ⊆ Sᶜ := by
    rintro w ⟨hwD, hwC⟩ ⟨h, -⟩
    exact hwC h
  have hLcl : ∀ e ∈ L, ∀ w ∈ Sᶜ, H.Adj e w → w ∈ L := by
    simpa [L, S] using left_closed C D hunion
  have hRcl : ∀ e ∈ R, ∀ w ∈ Sᶜ, H.Adj e w → w ∈ R := by
    simpa [R, S, Set.inter_comm] using right_closed C D hunion
  have hchoice : (∀ e ∈ L, e ∉ branchVertices H) ∨
      (∀ e ∈ R, e ∉ branchVertices H) := by
    by_cases hLb : ∃ e ∈ L, e ∈ branchVertices H
    · right
      obtain ⟨b, hbL, hbb⟩ := hLb
      intro r hrR hrb
      have hbS : b ∈ Sᶜ := hLS hbL
      have hrS : r ∈ Sᶜ := hRS hrR
      have hreach : RchIn H Sᶜ b r := branch_reach hbb hrb hbS hrS
      have hrL : r ∈ L := rchIn_closed hLcl hbL hreach
      exact hrR.2 hrL.1
    · left
      intro e he heb
      exact hLb ⟨e, he, heb⟩
  have hverts := verts_eq_sdiff_union_inter C D hunion
  rcases hchoice with hLnb | hRnb
  · left
    obtain ⟨q, hq, hqV, hqE⟩ :=
      branchless_side L hne.1 hLS hLcl hLnb
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hverts.1]
      simpa [L, S] using hqV
    · intro e he
      apply hqE
      refine ⟨edge_mem_host C he, ?_⟩
      intro w hw
      have hwC := edge_ends_mem_subgraph C he w hw
      rw [hverts.1] at hwC
      simpa [L, S] using hwC
  · right
    obtain ⟨q, hq, hqV, hqE⟩ :=
      branchless_side R hne.2 hRS hRcl hRnb
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hverts.2]
      simpa [R, S] using hqV
    · intro e he
      apply hqE
      refine ⟨edge_mem_host D he, ?_⟩
      intro w hw
      have hwD := edge_ends_mem_subgraph D he w hw
      rw [hverts.2] at hwD
      simpa [R, S] using hwD

end Workspace.ProofLemmas.Thm55Reduction
