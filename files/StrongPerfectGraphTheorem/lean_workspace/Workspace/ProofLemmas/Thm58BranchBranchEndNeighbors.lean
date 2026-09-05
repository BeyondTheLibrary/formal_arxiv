import Workspace.ProofLemmas.Thm58BranchBranchSingleton
import Workspace.ProofLemmas.Thm58BranchBranchLinks
import Workspace.ProofLemmas.Thm57Claim1Konig
import Workspace.Statements.S02.Thm_2_4

/-!
# The neighbors of either end in 5.8 (7)

A unique neighbor at a branch end is excluded by claim (6). An internal unique
neighbor and two nonadjacent neighbors are excluded by the two triangle links
and 2.4. The remaining neighbors form a clique inside a branch path, so there
are exactly two, and they are adjacent.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- After excluding interior attachments, the first attachment set is exactly the
neighborhood of the first end. -/
theorem first_attachment_iff
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (e : H.edgeSet) :
    e.1 ∈ edgeAttachments φ (F \ {p₂}) ↔ G.Adj p₁ (↑(φ e) : V) := by
  constructor
  · rintro ⟨_, hyK, x, hx, hyx⟩
    rcases adjacent_vertex_is_end h hq₁ hq₂ hX₁ hX₂ hx.1 hyK hyx.symm with hxp | hxp
    · exact hxp ▸ hyx.symm
    · exact (hx.2 hxp).elim
  · intro hpy
    have hpF : p₁ ∈ F := by
      rw [← h.2.2.2.2.2.2.2.1]
      exact PathBasics.head_mem h.2.2.2.2.2.2.1.2.1
    exact ⟨e.2, (φ e).2, p₁, ⟨hpF, ends_ne h⟩, hpy.symm⟩

/-- This is the contradiction from 2.4 used in both last sentences of claim (7). -/
theorem no_link_with_two_nonneighbors (hG : Berge G) {r a b c : V}
    (hlink : VertexCanBeLinkedOntoTriangle G r a b c)
    (ha : ¬ G.Adj r a) (hb : ¬ G.Adj r b) : False := by
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG r a b c hlink with h | h | h
  · exact ha h.1
  · exact ha h.1
  · exact hb h.1

/-- Claim (6) deals with an end-edge neighbor, and the first triangle link deals
with an internal neighbor. Thus the first end cannot have a unique neighbor. -/
theorem not_unique_neighbor
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hstar : ∀ c ∈ branchVertices H,
      edgeAttachments φ (F \ {p₂}) ⊆ incidentEdges H c →
      Thm58Setup.Outcome G n H K φ N P p₁ p₂)
    {r : V} (hrK : r ∈ K) (hpr : G.Adj p₁ r)
    (hunique : ∀ y ∈ K, G.Adj p₁ y → y = r) : False := by
  let e := φ.symm ⟨r, hrK⟩
  have her : (↑(φ e) : V) = r := congrArg Subtype.val (φ.apply_symm_apply ⟨r, hrK⟩)
  by_cases hend : ∃ c ∈ branchVertices H, c ∈ e.1
  · obtain ⟨c, hc, hce⟩ := hend
    have hinc : edgeAttachments φ (F \ {p₂}) ⊆ incidentEdges H c := by
      rintro d ⟨hd, hdatt⟩
      have hpd := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ ⟨d, hd⟩).mp ⟨hd, hdatt⟩
      have hde : d = e.1 := congrArg (fun e : H.edgeSet => e.1)
        (φ.injective (Subtype.ext ((hunique _ (φ ⟨d, hd⟩).2 hpd).trans her.symm)))
      exact ⟨hd, hde.symm ▸ hce⟩
    exact not_outcome_of_unique_neighbor h hunique (hstar c hc hinc)
  · have hint : ∀ c ∈ branchVertices H, c ∉ (φ.symm ⟨r, hrK⟩).1 := by
      intro c hc hce
      exact hend ⟨c, hc, hce⟩
    obtain ⟨a, b, c, hlink, ha, hb⟩ :=
      singleton_interior_link_gap h hq₁ hq₂ hX₁ hX₂ hrK hpr hunique hint
    exact no_link_with_two_nonneighbors h.1 hlink ha hb

/-- The second triangle link and 2.4 force the endpoint's neighbors to be pairwise adjacent. -/
theorem neighbors_adjacent
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    (hpa : G.Adj p₁ a) (hpb : G.Adj p₁ b) (hab : a ≠ b) : G.Adj a b := by
  by_contra hbad
  obtain ⟨x, y, z, hlink, hx, hy⟩ :=
    nonadjacent_neighbors_link_gap h hq₁ hq₂ hX₁ hX₂ haK hbK hpa hpb hab hbad
  exact no_link_with_two_nonneighbors h.1 hlink hx hy

/-- Pairwise adjacent neighbors inside one branch form a pair as soon as there
are two distinct neighbors. The common-edge endpoint form of König's argument
avoids introducing indices for the rung. -/
theorem pair_of_adjacent_neighbors
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hclique : ∀ a ∈ K, ∀ b ∈ K, G.Adj p₁ a → G.Adj p₁ b → a ≠ b → G.Adj a b)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    (hpa : G.Adj p₁ a) (hpb : G.Adj p₁ b) (hab : a ≠ b) :
    TwoAdjacentNeighbors G K p₁ := by
  let A := edgeAttachments φ (F \ {p₂})
  let e := φ.symm ⟨a, haK⟩
  let f := φ.symm ⟨b, hbK⟩
  have hea : (↑(φ e) : V) = a := congrArg Subtype.val (φ.apply_symm_apply ⟨a, haK⟩)
  have hfb : (↑(φ f) : V) = b := congrArg Subtype.val (φ.apply_symm_apply ⟨b, hbK⟩)
  have heA : e.1 ∈ A := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ e).mpr (hea.symm ▸ hpa)
  have hfA : f.1 ∈ A := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ f).mpr (hfb.symm ▸ hpb)
  have hAE : A ⊆ H.edgeSet := by rintro d ⟨hd, _⟩; exact hd
  have hmeet : ∀ d ∈ A, ∀ g ∈ A, ¬ DisjointEdges d g := by
    intro d hd g hg
    by_cases hdg : d = g
    · subst g
      induction d using Sym2.ind with
      | _ u v => exact fun hn => hn u ⟨by simp, by simp⟩
    · have hpd := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ ⟨d, hAE hd⟩).mp hd
      have hpg := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ ⟨g, hAE hg⟩).mp hg
      have hne : (↑(φ ⟨d, hAE hd⟩) : V) ≠ (↑(φ ⟨g, hAE hg⟩) : V) := by
        intro hv
        exact hdg (congrArg Subtype.val (φ.injective (Subtype.ext hv)))
      have hadj : H.lineGraph.Adj ⟨d, hAE hd⟩ ⟨g, hAE hg⟩ :=
        φ.map_rel_iff.mp (hclique _ (φ ⟨d, hAE hd⟩).2 _ (φ ⟨g, hAE hg⟩).2 hpd hpg hne)
      obtain ⟨_, c, hcd, hcg⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
      exact fun hn => hn c ⟨hcd, hcg⟩
  obtain ⟨c, hc⟩ := Thm57Claim1Konig.exists_common_vertex h.2.2.1.2 A hAE ⟨e.1, heA⟩ hmeet
  have hef : e.1 ≠ f.1 := by
    intro hef
    exact hab (hea.symm.trans ((congrArg (fun d : H.edgeSet => (↑(φ d) : V))
      (Subtype.ext hef)).trans hfb))
  have hint := internal_of_two_edges hq₁.1.2.1 (hX₁ heA) (hX₁ hfA) hef (hc _ heA) (hc _ hfA)
  have hstar : incidentEdges H c = {e.1, f.1} := by
    have hsub : ({e.1, f.1} : Set (Sym2 (Fin n))) ⊆ incidentEdges H c := by
      rintro d (rfl | rfl)
      · exact ⟨e.2, hc _ heA⟩
      · exact ⟨f.2, hc _ hfA⟩
    apply (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
    rw [Thm84RungEndDictionary.incidentEdges_ncard, Set.ncard_pair hef]
    have hn := hq₁.2.1 c hint
    change ¬ 3 ≤ (H.neighborSet c).ncard at hn
    omega
  refine ⟨a, b, haK, hbK, hclique a haK b hbK hpa hpb hab, ?_⟩
  intro y hyK
  constructor
  · intro hpy
    let d := φ.symm ⟨y, hyK⟩
    have hdy : (↑(φ d) : V) = y := congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyK⟩)
    have hdA : d.1 ∈ A := (first_attachment_iff h hq₁ hq₂ hX₁ hX₂ d).mpr (hdy.symm ▸ hpy)
    have hdstar : d.1 ∈ incidentEdges H c := ⟨d.2, hc _ hdA⟩
    rw [hstar] at hdstar
    rcases hdstar with hde | hdf
    · exact Or.inl (hdy.symm.trans ((congrArg (fun t : H.edgeSet => (↑(φ t) : V))
        (Subtype.ext hde)).trans hea))
    · exact Or.inr (hdy.symm.trans ((congrArg (fun t : H.edgeSet => (↑(φ t) : V))
        (Subtype.ext (show d.1 = f.1 from hdf))).trans hfb))
  · rintro (rfl | rfl)
    · exact hpa
    · exact hpb

/-- Applying the two contradictions leaves exactly two adjacent neighbors. -/
theorem first_end_pair
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hstar : ∀ c ∈ branchVertices H,
      edgeAttachments φ (F \ {p₂}) ⊆ incidentEdges H c →
      Thm58Setup.Outcome G n H K φ N P p₁ p₂) :
    TwoAdjacentNeighbors G K p₁ := by
  obtain ⟨a, haK, hpa⟩ := first_end_has_neighbor h hq₂ hX₂
  have hex : ∃ b ∈ K, G.Adj p₁ b ∧ b ≠ a := by
    by_contra hnone
    apply not_unique_neighbor h hq₁ hq₂ hX₁ hX₂ hstar haK hpa
    intro b hbK hpb
    by_contra hne
    exact hnone ⟨b, hbK, hpb, hne⟩
  obtain ⟨b, hbK, hpb, hba⟩ := hex
  apply pair_of_adjacent_neighbors h hq₁ hq₂ hX₁ hX₂ ?_ haK hbK hpa hpb hba.symm
  intro x hx y hy hpx hpy hxy
  exact neighbors_adjacent h hq₁ hq₂ hX₁ hX₂ hx hy hpx hpy hxy

/-- Claims (5) and (7), with claim (6) supplied in both endpoint orders. Only
`Ready` is reversed: no symmetry of the asymmetric `Outcome` is used. -/
theorem branchBranch
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (q₁ q₂ : List (Fin n)) (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hstar₁ : ∀ c ∈ branchVertices H,
      edgeAttachments φ (F \ {p₂}) ⊆ incidentEdges H c →
      Thm58Setup.Outcome G n H K φ N P p₁ p₂)
    (hstar₂ : ∀ c ∈ branchVertices H,
      edgeAttachments φ (F \ {p₁}) ⊆ incidentEdges H c →
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  have hpair₁ := first_end_pair h hq₁ hq₂ hX₁ hX₂ hstar₁
  have hpair₂ := first_end_pair (ready_reverse h) hq₂ hq₁ hX₂ hX₁ hstar₂
  exact outcome_of_two_pairs h hq₁ hq₂ hX₁ hX₂ hpair₁ hpair₂

end Workspace.ProofLemmas.Thm58BranchBranch
