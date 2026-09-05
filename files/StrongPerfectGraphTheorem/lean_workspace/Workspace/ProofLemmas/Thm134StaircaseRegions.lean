import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.Thm134RegionAux
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.ProofLemmas.StrongStaircaseVertexClassification
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7
import Workspace.Statements.S04.Thm_4_5
import Workspace.Statements.S12.Thm_12_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The three printed sub-claims of the region analysis of 13.4

Carved out of §13's printed proof of 13.4 (`paper/proofs/13_4.md`, printed
pp. 84–85), which after fixing the strongly maximal staircase
`K = (S = (A, C, B), a₀-R₀-b₀)`, the classes `A₀` (left-stars), `B₀`
(right-stars), `N` (the `A ∪ B`-complete vertices) and
`H = G \ (V(S) ∪ A₀ ∪ B₀ ∪ N)` argues:

**(1)** *"Let `F` be a component of `H`, and let `X` be the set of attachments
of `F` in `V(S) ∪ A₀ ∪ B₀`.  Then either `X ∩ V(S) = ∅`, or `X ⊆ V(S)` and `X`
meets both `A ∪ C` and `B ∪ C`."*  — `componentAttachmentDichotomy`.

The printed argument: *"We may assume that `X` meets `V(S)`, and therefore from
the symmetry we may assume that `X` meets `A ∪ C`.  Since no vertex in `F` is
`A`- or `B`-complete, and therefore no vertex in `F` is major or a left- or
right-star, it follows from 12.3 that `X` is disjoint from `B₀`.  If `X` meets
`B ∪ C` then similarly `X` is disjoint from `A₀`, and so `X ⊆ V(S)` and the
claim holds.  We assume therefore that `X ⊆ A ∪ A₀`.  Now if `v ∈ V(G) \ F` has
a neighbour in `F`, then `v ∉ V(H)`, and so `v ∈ V(S) ∪ A₀ ∪ B₀ ∪ N`, and
therefore `v ∈ X ∪ N ⊆ A ∪ A₀ ∪ N`.  Hence
`(V(G) \ (A ∪ A₀ ∪ N), A ∪ A₀ ∪ N)` is a skew partition of `G`, since `F` is a
component of `V(G) \ (A ∪ A₀ ∪ N)` and `b₀` is in a different component, and
`A, A₀ ∪ N` are both nonempty and complete to each other.  Now by 2.6,
`(B ∪ C, A)` is balanced, since `a₀` is complete to `A` and anticomplete to
`B ∪ C`; and therefore from 2.7, `(F, A)` is balanced (since `B ∪ C` is
connected and all vertices in `A` have neighbours in it).  Hence from 4.5, `G`
admits a balanced skew partition, a contradiction.  This proves (1)."*

**(2)** *"Then `M` is nonempty, since by (1) the component of `H` containing the
interior of `R₀` has no attachments in `V(S)`."* —
`interiorBanisterComponentHasNoStripAttachment`.

**(3)** the corresponding fact for the other side used in the proof of claim (2)
of 13.4 (*"the only edges between `V(S) ∪ D` and `A₀ ∪ B₀ ∪ M` are the edges
from `A` to `A₀` and those from `B` to `B₀`"*): a component of `H` with no
attachment in `V(S)` does attach to both `A₀` and `B₀` —
`middleComponentAttachesToBothStars`.

All three are stated with the *same* hypothesis block as
`Workspace.ProofLemmas.StrongStaircaseComponentStructure`, so that they can be
applied there verbatim.
-/

namespace Workspace.ProofLemmas.Thm134StaircaseRegions

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions.SPGT

/-- The last paragraph of the printed proof of 13.4(1): if every vertex outside
`F` with a neighbour in `F` lies in `A ∪ A₀ ∪ N`, then
`(V(G) \ (A ∪ A₀ ∪ N), A ∪ A₀ ∪ N)` is a skew partition of `G`, and 2.6, 2.7 and
4.5 make it balanced — *"a contradiction"*.

Stated one-sidedly with the strip written `(A, C, B)`; the mirror case
`X ⊆ B ∪ B₀` is obtained by applying it to the reversed staircase. -/
private theorem noOneSidedComponent {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hskew : ¬ AdmitsBalancedSkewPartition H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hNVS : ∀ v ∈ A ∪ B ∪ C, ¬ VertexComplete H v (A ∪ B))
    (F : Set V) (hFne : F.Nonempty)
    (hFVS : ∀ f ∈ F, f ∉ A ∪ B ∪ C)
    (hFls : ∀ f ∈ F, ¬ IsLeftStar H A C B f)
    (hFrs : ∀ f ∈ F, ¬ IsRightStar H A C B f)
    (hFN : ∀ f ∈ F, ¬ VertexComplete H f (A ∪ B))
    (hout : ∀ v : V, v ∉ F → (∃ f ∈ F, H.Adj v f) →
      v ∈ A ∨ IsLeftStar H A C B v ∨ VertexComplete H v (A ∪ B)) :
    False := by
  have hsc : StepConnected H A C B := hstairs.1.1.1
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstairs.1.1.2.1
  have hls : IsLeftStar H A C B a₀ := hban.2.2.1
  have hrs : IsRightStar H A C B b₀ := hban.2.2.2.1
  obtain ⟨⟨hAB, hAC, hBC⟩, ⟨hAne, hBne⟩, -, -, -⟩ := hsc
  obtain ⟨aw, haw⟩ := hAne
  -- the four sets of 4.5
  have hXAdisj : Disjoint ({v : V | IsLeftStar H A C B v} ∪
      {v : V | VertexComplete H v (A ∪ B)}) A := by
    refine Set.disjoint_left.mpr ?_
    rintro v (hv | hv) hvA
    · exact hv.1 (Or.inl (Or.inl hvA))
    · exact H.irrefl (hv v (Or.inl hvA))
  have hXFdisj : Disjoint ({v : V | IsLeftStar H A C B v} ∪
      {v : V | VertexComplete H v (A ∪ B)}) F := by
    refine Set.disjoint_left.mpr ?_
    rintro v (hv | hv) hvF
    · exact hFls v hvF hv
    · exact hFN v hvF hv
  have hAFdisj : Disjoint A F :=
    Set.disjoint_left.mpr fun v hv hvF => hFVS v hvF (Or.inl (Or.inl hv))
  have hb₀R : b₀ ∈ (({v : V | IsLeftStar H A C B v} ∪
      {v : V | VertexComplete H v (A ∪ B)}) ∪ A ∪ F)ᶜ := by
    rintro (((hv | hv) | hv) | hv)
    · exact hrs.2.2 aw (Or.inl haw) (hv.2.1 aw haw)
    · exact hrs.2.2 aw (Or.inl haw) (hv aw (Or.inl haw))
    · exact hrs.1 (Or.inl (Or.inl hv))
    · exact hFrs b₀ hv hrs
  -- `(B ∪ C, A)` is balanced, by 2.6 applied to `a₀`
  have hdBCA : Disjoint (B ∪ C) A := by
    refine Set.disjoint_left.mpr ?_
    rintro v (hv | hv) hvA
    · exact (Set.disjoint_left.mp hAB hvA) hv
    · exact (Set.disjoint_left.mp hAC hvA) hv
  have ha₀not : a₀ ∉ (B ∪ C) ∪ A := by
    rintro ((hv | hv) | hv)
    · exact hls.1 (Or.inl (Or.inr hv))
    · exact hls.1 (Or.inr hv)
    · exact hls.1 (Or.inl (Or.inl hv))
  have hbal1 := Workspace.Statements.S02.SPGT.thm_2_6 H hBerge (B ∪ C) A hdBCA a₀
    ha₀not hls.2.1 hls.2.2
  -- and therefore so is `(F, A)`, by 2.7
  have hFsub : F ⊆ ((B ∪ C) ∪ A)ᶜ := by
    intro f hf hc
    rcases hc with (h | h) | h
    · exact hFVS f hf (Or.inl (Or.inr h))
    · exact hFVS f hf (Or.inr h)
    · exact hFVS f hf (Or.inl (Or.inl h))
  have hFanti : Anticomplete H (B ∪ C) F := by
    intro w hw f hf hadj
    have hwVS : w ∈ A ∪ B ∪ C := by
      rcases hw with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hwF : w ∉ F := fun h => hFVS w h hwVS
    rcases hout w hwF ⟨f, hf, hadj⟩ with h | h | h
    · rcases hw with hb | hc
      · exact (Set.disjoint_left.mp hAB h) hb
      · exact (Set.disjoint_left.mp hAC h) hc
    · exact h.1 hwVS
    · exact hNVS w hwVS h
  have hbal2 := (Workspace.Statements.S02.SPGT.thm_2_7 H hBerge (B ∪ C) A hbal1 F hFsub).1
    (Thm134RegionAux.stripFarSideConnected hstairs.1.1.1)
    (Thm134RegionAux.stripVertexHasFarNeighbour hstairs.1.1.1) hFanti
  -- 4.5 with `X = A₀ ∪ N`, `Y = A`, `L = F`, `R` the rest
  refine hskew (Workspace.Statements.S04.SPGT.thm_4_5 H hBerge
    ({v : V | IsLeftStar H A C B v} ∪ {v : V | VertexComplete H v (A ∪ B)}) A F
    (({v : V | IsLeftStar H A C B v} ∪ {v : V | VertexComplete H v (A ∪ B)}) ∪ A ∪ F)ᶜ
    (Set.union_compl_self _) hXAdisj hXFdisj ?_ hAFdisj ?_ ?_
    ⟨a₀, Or.inl hls⟩ ⟨aw, haw⟩ hFne ⟨b₀, hb₀R⟩ ?_ ?_ (Or.inr (Or.inr hbal2)))
  · exact Set.disjoint_left.mpr fun v hv hv' => hv' (Or.inl (Or.inl hv))
  · exact Set.disjoint_left.mpr fun v hv hv' => hv' (Or.inl (Or.inr hv))
  · exact Set.disjoint_left.mpr fun v hv hv' => hv' (Or.inr hv)
  · -- no edges between `F` and the rest
    intro f hf r hr hadj
    have hrF : r ∉ F := fun h => hr (Or.inr h)
    rcases hout r hrF ⟨f, hf, hadj.symm⟩ with h | h | h
    · exact hr (Or.inl (Or.inr h))
    · exact hr (Or.inl (Or.inl (Or.inl h)))
    · exact hr (Or.inl (Or.inl (Or.inr h)))
  · -- `A₀ ∪ N` is complete to `A`
    rintro x (hx | hx) y hy
    · exact hx.2.1 y hy
    · exact hx y (Or.inl hy)

/-- The mirror of `noOneSidedComponent`, i.e. the printed *"from the symmetry"*:
the same argument run on the reversed staircase `(S' = (B, C, A), b₀-R₀ʳ-a₀)`,
which rules out a component of `H` all of whose outside neighbours lie in
`B ∪ B₀ ∪ N`. -/
private theorem noOneSidedComponent' {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hskew : ¬ AdmitsBalancedSkewPartition H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hNVS : ∀ v ∈ A ∪ B ∪ C, ¬ VertexComplete H v (A ∪ B))
    (F : Set V) (hFne : F.Nonempty)
    (hFVS : ∀ f ∈ F, f ∉ A ∪ B ∪ C)
    (hFls : ∀ f ∈ F, ¬ IsLeftStar H A C B f)
    (hFrs : ∀ f ∈ F, ¬ IsRightStar H A C B f)
    (hFN : ∀ f ∈ F, ¬ VertexComplete H f (A ∪ B))
    (hout : ∀ v : V, v ∉ F → (∃ f ∈ F, H.Adj v f) →
      v ∈ B ∨ IsRightStar H A C B v ∨ VertexComplete H v (A ∪ B)) :
    False := by
  refine noOneSidedComponent H hBerge hskew B C A b₀ a₀ R₀.reverse
    (StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hstairs) ?_ F hFne ?_ ?_ ?_ ?_ ?_
  · intro v hv hc
    rw [Set.union_comm B A] at hv hc
    exact hNVS v hv hc
  · intro f hf hc
    rw [Set.union_comm B A] at hc
    exact hFVS f hf hc
  · exact fun f hf hc => hFrs f hf (StaircaseLeftRightSymmetry.isRightStar_swap.mpr hc)
  · exact fun f hf hc => hFls f hf (StaircaseLeftRightSymmetry.isLeftStar_swap.mpr hc)
  · intro f hf hc
    rw [Set.union_comm B A] at hc
    exact hFN f hf hc
  · intro v hvF hadj
    rcases hout v hvF hadj with hv | hv | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl (StaircaseLeftRightSymmetry.isRightStar_swap.mp hv))
    · refine Or.inr (Or.inr ?_)
      rw [Set.union_comm B A]
      exact hv

/-- The 12.3 step of the printed proof of 13.4(1): *"Since no vertex in `F` is
`A`- or `B`-complete, and therefore no vertex in `F` is major or a left- or
right-star, it follows from 12.3 that `X` is disjoint from `B₀`."*

One-sided form: if `F` has an attachment in `B ∪ C`, then no left-star has a
neighbour in `F` — for otherwise `F` together with that left-star satisfies the
hypotheses of 12.3, whose two conclusions are both refuted. -/
private theorem starDisjoint {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hK4 : ¬ Appears H (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism H s t R₁ R₂ R₃)
    (h1breaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker H A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hmax : MaximalStaircase H A C B a₀ R₀ b₀) (hAne : A.Nonempty)
    (F : Set V)
    (hFVS : ∀ f ∈ F, f ∉ A ∪ B ∪ C)
    (hFconn : ConnectedSet H F)
    (hFls : ∀ f ∈ F, ¬ IsLeftStar H A C B f)
    (hFrs : ∀ f ∈ F, ¬ IsRightStar H A C B f)
    (hFmaj : ∀ f ∈ F, ¬ MajorForStaircase H A C B a₀ R₀ b₀ f)
    (hatt : (attachments H F (B ∪ C)).Nonempty)
    (w : V) (hw : IsLeftStar H A C B w) (hwF : ∃ f ∈ F, H.Adj w f) :
    False := by
  obtain ⟨aw, haw⟩ := hAne
  obtain ⟨x, hxBC, f₀, hf₀, hadj₀⟩ := hatt
  have hF'VS : ∀ f ∈ F ∪ ({w} : Set V), f ∉ A ∪ B ∪ C := by
    rintro f (hf | rfl)
    · exact hFVS f hf
    · exact hw.1
  have hF'conn : ConnectedSet H (F ∪ ({w} : Set V)) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hFconn hwF
  have hF'att : (attachments H (F ∪ ({w} : Set V)) (B ∪ C)).Nonempty :=
    ⟨x, hxBC, f₀, Or.inl hf₀, hadj₀⟩
  rcases Workspace.Statements.S12.SPGT.thm_12_3 H hBerge hK4 heven h1breaker A C B a₀ b₀ R₀
      hmax (F ∪ ({w} : Set V)) (fun f hf => hF'VS f hf) hF'conn ⟨w, Or.inr rfl, hw⟩ hF'att with
    ⟨v, hvF', hvmaj⟩ | ⟨u, v, R, hR, hban⟩
  · -- a major vertex: impossible inside `F`, and a left-star is not major
    rcases hvF' with hv | rfl
    · exact hFmaj v hv hvmaj
    · obtain ⟨y, hyB, hadjy⟩ := hvmaj.2.2.1
      exact hw.2.2 y (Or.inl hyB) hadjy
  · -- a banister: its two ends are stars, so both are `w`, which is impossible
    have huR : u ∈ R := PathBasics.head_mem hban.1.2.1
    have hvR : v ∈ R := PathBasics.getLast_mem hban.1.2.2
    have huw : u = w := by
      rcases hR u huR with h | h
      · exact absurd hban.2.2.1 (hFls u h)
      · exact h
    have hvw : v = w := by
      rcases hR v hvR with h | h
      · exact absurd hban.2.2.2.1 (hFrs v h)
      · exact h
    have hlsw : IsLeftStar H A C B w := by rw [← huw]; exact hban.2.2.1
    have hrsw : IsRightStar H A C B w := by rw [← hvw]; exact hban.2.2.2.1
    exact hrsw.2.2 aw (Or.inl haw) (hlsw.2.1 aw haw)

/-- **13.4(1)** (printed p. 84). -/
theorem componentAttachmentDichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hK4 : ¬ Appears H (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism H s t R₁ R₂ R₃)
    (h1breaker : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker H A' C' B' F Q)
    (h3breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' x : V),
      IsThreeBreaker H A' C' B' a₀' R₀' b₀' x)
    (hskew : ¬ AdmitsBalancedSkewPartition H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hodd : Odd (pathLength R₀)) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    ∀ F : Set V, F.Nonempty → IsComponent H H₀ F →
      (attachments H F (VS ∪ A₀ ∪ B₀) ∩ VS).Nonempty →
      attachments H F (VS ∪ A₀ ∪ B₀) ⊆ VS ∧
        (attachments H F (VS ∪ A₀ ∪ B₀) ∩ (A ∪ C)).Nonempty ∧
        (attachments H F (VS ∪ A₀ ∪ B₀) ∩ (B ∪ C)).Nonempty := by
  intro VS A₀ B₀ N H₀ F hFne hFcomp hmeet
  have hsc : StepConnected H A C B := hstairs.1.1.1
  have hAne : A.Nonempty := hsc.2.1.1
  have hBne : B.Nonempty := hsc.2.1.2
  -- the classification paragraph printed just before (1)
  obtain ⟨-, ⟨-, -, hNVSd⟩, -, -, -, hH₀, -⟩ :=
    StrongStaircaseVertexClassification.strongStaircaseVertexClassification
      H hBerge hK4 heven h1breaker h3breaker A C B a₀ b₀ R₀ hstairs
  have hFH₀ : ∀ f ∈ F, f ∈ H₀ := fun f hf => hFcomp.1 hf
  have hFVS : ∀ f ∈ F, f ∉ A ∪ B ∪ C :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inl (Or.inl hc)))
  have hFls : ∀ f ∈ F, ¬ IsLeftStar H A C B f :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inl (Or.inr hc)))
  have hFrs : ∀ f ∈ F, ¬ IsRightStar H A C B f :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inr hc))
  have hFN : ∀ f ∈ F, ¬ VertexComplete H f (A ∪ B) :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inr hc)
  have hFmaj : ∀ f ∈ F, ¬ MajorForStaircase H A C B a₀ R₀ b₀ f :=
    fun f hf => (hH₀ f (hFH₀ f hf)).2.2.2.2
  have hFconn : ConnectedSet H F := hFcomp.2.1
  have hNVSall : ∀ v ∈ A ∪ B ∪ C, ¬ VertexComplete H v (A ∪ B) :=
    fun v hv hc => (Set.disjoint_left.mp hNVSd hc) hv
  -- *"if `v ∈ V(G) \ F` has a neighbour in `F`, then `v ∉ V(H)`"*
  have hout0 : ∀ v : V, v ∉ F → (∃ f ∈ F, H.Adj v f) →
      v ∈ A ∪ B ∪ C ∨ IsLeftStar H A C B v ∨ IsRightStar H A C B v ∨
        VertexComplete H v (A ∪ B) := by
    intro v hvF hadj
    by_cases h1 : v ∈ A ∪ B ∪ C
    · exact Or.inl h1
    by_cases h2 : IsLeftStar H A C B v
    · exact Or.inr (Or.inl h2)
    by_cases h3 : IsRightStar H A C B v
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : VertexComplete H v (A ∪ B)
    · exact Or.inr (Or.inr (Or.inr h4))
    exfalso
    obtain ⟨f, hf, hvf⟩ := hadj
    refine Thm134RegionAux.component_no_outside_neighbour hFcomp
      (show v ∈ H₀ from ⟨trivial, ?_⟩) hvF f hf hvf
    rintro (((h | h) | h) | h)
    exacts [h1 h, h2 h, h3 h, h4 h]
  -- 12.3, in the two orientations
  have step2 : (attachments H F (B ∪ C)).Nonempty →
      ∀ w : V, IsLeftStar H A C B w → (∃ f ∈ F, H.Adj w f) → False := by
    intro hatt w hw hwF
    exact starDisjoint H hBerge hK4 heven h1breaker A C B a₀ b₀ R₀ hstairs.1 hAne F
      hFVS hFconn hFls hFrs hFmaj hatt w hw hwF
  have step1 : (attachments H F (A ∪ C)).Nonempty →
      ∀ w : V, IsRightStar H A C B w → (∃ f ∈ F, H.Adj w f) → False := by
    intro hatt w hw hwF
    refine starDisjoint H hBerge hK4 heven h1breaker B C A b₀ a₀ R₀.reverse
      (StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hstairs.1) hBne F ?_ hFconn ?_ ?_ ?_
      hatt w (StaircaseLeftRightSymmetry.isRightStar_swap.mp hw) hwF
    · intro f hf hc
      rw [Set.union_comm B A] at hc
      exact hFVS f hf hc
    · exact fun f hf hc => hFrs f hf (StaircaseLeftRightSymmetry.isRightStar_swap.mpr hc)
    · exact fun f hf hc => hFls f hf (StaircaseLeftRightSymmetry.isLeftStar_swap.mpr hc)
    · exact fun f hf hc =>
        hFmaj f hf (StaircaseLeftRightSymmetry.majorForStaircase_swap.mpr hc)
  -- *"We assume therefore that `X ⊆ A ∪ A₀`"* — refuted by the last paragraph
  have hAC : (attachments H F (A ∪ C)).Nonempty → (attachments H F (B ∪ C)).Nonempty := by
    intro hattAC
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    have hemp : ∀ v : V, v ∈ B ∪ C → (∃ f ∈ F, H.Adj v f) → False := by
      intro v hv ha
      have hx : v ∈ attachments H F (B ∪ C) := ⟨hv, ha⟩
      rw [hno] at hx
      exact hx
    refine noOneSidedComponent H hBerge hskew A C B a₀ b₀ R₀ hstairs hNVSall F hFne hFVS
      hFls hFrs hFN ?_
    intro v hvF hadj
    rcases hout0 v hvF hadj with hv | hv | hv | hv
    · rcases hv with (hv | hv) | hv
      · exact Or.inl hv
      · exact (hemp v (Or.inl hv) hadj).elim
      · exact (hemp v (Or.inr hv) hadj).elim
    · exact Or.inr (Or.inl hv)
    · exact (step1 hattAC v hv hadj).elim
    · exact Or.inr (Or.inr hv)
  have hBC : (attachments H F (B ∪ C)).Nonempty → (attachments H F (A ∪ C)).Nonempty := by
    intro hattBC
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    have hemp : ∀ v : V, v ∈ A ∪ C → (∃ f ∈ F, H.Adj v f) → False := by
      intro v hv ha
      have hx : v ∈ attachments H F (A ∪ C) := ⟨hv, ha⟩
      rw [hno] at hx
      exact hx
    refine noOneSidedComponent' H hBerge hskew A C B a₀ b₀ R₀ hstairs hNVSall F hFne hFVS
      hFls hFrs hFN ?_
    intro v hvF hadj
    rcases hout0 v hvF hadj with hv | hv | hv | hv
    · rcases hv with (hv | hv) | hv
      · exact (hemp v (Or.inl hv) hadj).elim
      · exact Or.inl hv
      · exact (hemp v (Or.inr hv) hadj).elim
    · exact (step2 hattBC v hv hadj).elim
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  -- *"We may assume that `X` meets `V(S)`"*
  obtain ⟨x, ⟨-, hxF⟩, hxVS⟩ := hmeet
  have hboth : (attachments H F (A ∪ C)).Nonempty ∧ (attachments H F (B ∪ C)).Nonempty := by
    rcases hxVS with (hx | hx) | hx
    · have h1 : (attachments H F (A ∪ C)).Nonempty := ⟨x, Or.inl hx, hxF⟩
      exact ⟨h1, hAC h1⟩
    · have h2 : (attachments H F (B ∪ C)).Nonempty := ⟨x, Or.inl hx, hxF⟩
      exact ⟨hBC h2, h2⟩
    · exact ⟨⟨x, Or.inr hx, hxF⟩, ⟨x, Or.inr hx, hxF⟩⟩
  obtain ⟨hAC', hBC'⟩ := hboth
  refine ⟨?_, ?_, ?_⟩
  · -- *"and so `X ⊆ V(S)`"*
    rintro v ⟨hvK, hvadj⟩
    rcases hvK with (hvVS | hvA₀) | hvB₀
    · exact hvVS
    · exact (step2 hBC' v hvA₀ hvadj).elim
    · exact (step1 hAC' v hvB₀ hvadj).elim
  · obtain ⟨y, hyAC, hyadj⟩ := hAC'
    have hyVS : y ∈ A ∪ B ∪ C := by
      rcases hyAC with h | h
      exacts [Or.inl (Or.inl h), Or.inr h]
    exact ⟨y, ⟨Or.inl (Or.inl hyVS), hyadj⟩, hyAC⟩
  · obtain ⟨y, hyBC, hyadj⟩ := hBC'
    have hyVS : y ∈ A ∪ B ∪ C := by
      rcases hyBC with h | h
      exacts [Or.inl (Or.inr h), Or.inr h]
    exact ⟨y, ⟨Or.inl (Or.inl hyVS), hyadj⟩, hyBC⟩

/-- **13.4, the sentence after (1)** (printed p. 84): *"`M` is nonempty, since by
(1) the component of `H` containing the interior of `R₀` has no attachments in
`V(S)`."* -/
theorem interiorBanisterComponentHasNoStripAttachment
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hK4 : ¬ Appears H (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism H s t R₁ R₂ R₃)
    (h1breaker : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker H A' C' B' F Q)
    (h3breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' x : V),
      IsThreeBreaker H A' C' B' a₀' R₀' b₀' x)
    (hskew : ¬ AdmitsBalancedSkewPartition H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hodd : Odd (pathLength R₀)) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    ∀ F : Set V, IsComponent H H₀ F → ({v : V | v ∈ interior R₀} ∩ F).Nonempty →
      attachments H F VS = ∅ := by
  intro VS A₀ B₀ N H₀ F hFcomp hmeetInt
  obtain ⟨z, hzint, hzF⟩ := hmeetInt
  have hFne : F.Nonempty := ⟨z, hzF⟩
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstairs.1.1.2.1
  have hpath : IsPathFrom H R₀ a₀ b₀ := hban.1
  have hlen3 : 3 ≤ pathLength R₀ := hstairs.1.1.2.2
  have hlen : 4 ≤ R₀.length := by
    have h := PathBasics.length_eq_pathLength_add_one hpath.1
    omega
  -- *"the interior of `R₀`"* lies in `H`
  obtain ⟨-, -, -, -, -, -, hintsub⟩ :=
    StrongStaircaseVertexClassification.strongStaircaseVertexClassification
      H hBerge hK4 heven h1breaker h3breaker A C B a₀ b₀ R₀ hstairs
  have hintconn : ConnectedSet H {v : V | v ∈ interior R₀} :=
    MinimalConnectedIsPath.connectedSet_interior hpath
  have heq : F ∪ {v : V | v ∈ interior R₀} = F :=
    hFcomp.2.2 (F ∪ {v : V | v ∈ interior R₀}) Set.subset_union_left
      (Set.union_subset hFcomp.1 hintsub)
      (ConnectedSetUnionAttach.connectedSet_union hFcomp.2.1 hintconn
        (Or.inl ⟨z, hzF, hzint⟩))
  have hsub : {v : V | v ∈ interior R₀} ⊆ F := by
    intro v hv
    have hmem : v ∈ F ∪ {u : V | u ∈ interior R₀} := Or.inr hv
    rwa [heq] at hmem
  -- `R₀[1]` is an interior vertex of the banister, and `a₀` is adjacent to it
  have h1int : (R₀[1]'(by omega)) ∈ interior R₀ :=
    PathBasics.getElem_mem_interior hpath.1 (by omega) (by omega) (by omega)
  have h0 : (R₀[0]'(by omega)) = a₀ := PathBasics.getElem_zero_of_head? hpath.2.1 (by omega)
  have hadj : H.Adj a₀ (R₀[1]'(by omega)) := by
    have h := PathBasics.path_adj_succ hpath.1 (i := 0) (by omega)
    rwa [h0] at h
  -- so if `F` had an attachment in `V(S)`, (1) would put the left-star `a₀` in `V(S)`
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hxVS, hxadj⟩
  obtain ⟨hXsub, -, -⟩ := componentAttachmentDichotomy H hBerge hK4 heven h1breaker h3breaker
    hskew A C B a₀ b₀ R₀ hstairs hodd F hFne hFcomp ⟨x, ⟨Or.inl (Or.inl hxVS), hxadj⟩, hxVS⟩
  have ha₀X : a₀ ∈ attachments H F (VS ∪ A₀ ∪ B₀) :=
    ⟨Or.inl (Or.inr hban.2.2.1), (R₀[1]'(by omega)), hsub h1int, hadj⟩
  exact hban.2.2.1.1 (hXsub ha₀X)

/-- **13.4, in the proof of claim (2)** (printed p. 85): *"the only edges between
`V(S) ∪ D` and `A₀ ∪ B₀ ∪ M` are the edges from `A` to `A₀` and those from `B`
to `B₀`"* — a component of `H` with no attachment in `V(S)` attaches to both
`A₀` and `B₀`. -/
theorem middleComponentAttachesToBothStars
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hK4 : ¬ Appears H (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism H s t R₁ R₂ R₃)
    (h1breaker : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker H A' C' B' F Q)
    (h3breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' x : V),
      IsThreeBreaker H A' C' B' a₀' R₀' b₀' x)
    (hskew : ¬ AdmitsBalancedSkewPartition H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hodd : Odd (pathLength R₀)) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → attachments H F VS = ∅ →
      (attachments H F A₀).Nonempty ∧ (attachments H F B₀).Nonempty := by
  intro VS A₀ B₀ N H₀ F hFne hFcomp hnoatt
  obtain ⟨-, ⟨-, -, hNVSd⟩, -, -, -, -, -⟩ :=
    StrongStaircaseVertexClassification.strongStaircaseVertexClassification
      H hBerge hK4 heven h1breaker h3breaker A C B a₀ b₀ R₀ hstairs
  have hFH₀ : ∀ f ∈ F, f ∈ H₀ := fun f hf => hFcomp.1 hf
  have hFVS : ∀ f ∈ F, f ∉ A ∪ B ∪ C :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inl (Or.inl hc)))
  have hFls : ∀ f ∈ F, ¬ IsLeftStar H A C B f :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inl (Or.inr hc)))
  have hFrs : ∀ f ∈ F, ¬ IsRightStar H A C B f :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inl (Or.inr hc))
  have hFN : ∀ f ∈ F, ¬ VertexComplete H f (A ∪ B) :=
    fun f hf hc => (hFH₀ f hf).2 (Or.inr hc)
  have hNVSall : ∀ v ∈ A ∪ B ∪ C, ¬ VertexComplete H v (A ∪ B) :=
    fun v hv hc => (Set.disjoint_left.mp hNVSd hc) hv
  have hout0 : ∀ v : V, v ∉ F → (∃ f ∈ F, H.Adj v f) →
      v ∈ A ∪ B ∪ C ∨ IsLeftStar H A C B v ∨ IsRightStar H A C B v ∨
        VertexComplete H v (A ∪ B) := by
    intro v hvF hadj
    by_cases h1 : v ∈ A ∪ B ∪ C
    · exact Or.inl h1
    by_cases h2 : IsLeftStar H A C B v
    · exact Or.inr (Or.inl h2)
    by_cases h3 : IsRightStar H A C B v
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : VertexComplete H v (A ∪ B)
    · exact Or.inr (Or.inr (Or.inr h4))
    exfalso
    obtain ⟨f, hf, hvf⟩ := hadj
    refine Thm134RegionAux.component_no_outside_neighbour hFcomp
      (show v ∈ H₀ from ⟨trivial, ?_⟩) hvF f hf hvf
    rintro (((h | h) | h) | h)
    exacts [h1 h, h2 h, h3 h, h4 h]
  have hnoVS : ∀ v : V, v ∈ A ∪ B ∪ C → (∃ f ∈ F, H.Adj v f) → False := by
    intro v hv ha
    have hx : v ∈ attachments H F VS := ⟨hv, ha⟩
    rw [hnoatt] at hx
    exact hx
  constructor
  · -- no attachment in `A₀` would leave every outside neighbour in `B ∪ B₀ ∪ N`
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    have hnoA₀ : ∀ v : V, IsLeftStar H A C B v → (∃ f ∈ F, H.Adj v f) → False := by
      intro v hv ha
      have hx : v ∈ attachments H F A₀ := ⟨hv, ha⟩
      rw [hno] at hx
      exact hx
    refine noOneSidedComponent' H hBerge hskew A C B a₀ b₀ R₀ hstairs hNVSall F hFne hFVS
      hFls hFrs hFN ?_
    intro v hvF hadj
    rcases hout0 v hvF hadj with hv | hv | hv | hv
    · exact (hnoVS v hv hadj).elim
    · exact (hnoA₀ v hv hadj).elim
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · -- and symmetrically for `B₀`
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    have hnoB₀ : ∀ v : V, IsRightStar H A C B v → (∃ f ∈ F, H.Adj v f) → False := by
      intro v hv ha
      have hx : v ∈ attachments H F B₀ := ⟨hv, ha⟩
      rw [hno] at hx
      exact hx
    refine noOneSidedComponent H hBerge hskew A C B a₀ b₀ R₀ hstairs hNVSall F hFne hFVS
      hFls hFrs hFN ?_
    intro v hvF hadj
    rcases hout0 v hvF hadj with hv | hv | hv | hv
    · exact (hnoVS v hv hadj).elim
    · exact Or.inr (Or.inl hv)
    · exact (hnoB₀ v hv hadj).elim
    · exact Or.inr (Or.inr hv)

end Workspace.ProofLemmas.Thm134StaircaseRegions
