import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.AppearanceVertexTypeTransport
import Workspace.ProofLemmas.Thm75Claim2Generalised

/-!
# 7.5, claim (2)

PAPER (proof of 7.5, printed pp. 36–37):

*"(2) If `F ⊆ V(G)` is connected and some vertex of `S` has a neighbour in `F`, and so does some
vertex of `T`, and `F ∩ (X₀ ∪ X₁ ∪ Y) = ∅`, then the theorem holds."*

with

```
X₁ = X ∩ (Nc₁ ∪ Nc₂)
X₂ = X ∩ (V(L(H)) \ (Nc₁ ∪ Nc₂))
X₀ = X \ V(L(H))
S  = V(Rc₁c₂) \ X₁
T  = (V(L(H)) \ V(Rc₁c₂)) \ X₁
```

The printed proof is an induction on `|F|` — *"even for different choices of `L(H)`"* — that
reduces `G|F` to a path, applies **5.8** to the (non-local, major-free) set of attachments of
`F`, and then, in the 5.8.2 branch, replaces the rung `Rb₁b₂` by the new rung `R'` and re-applies
the inductive hypothesis to the resulting appearance `L(H')`, using **7.1** and **7.4** to show
that `Y` stays a maximal anticonnected set of dominant vertices, and **2.2** / **2.8** to handle
the case `bᵢ = cᵢ`.  Its conclusion, *"the theorem holds"*, is literally the disjunction that 7.5
asserts, so that is what is stated here.

`V(L(H))` is `K`, and `V(Rc₁c₂)` is the set `Rset` of vertices of `G` corresponding to the edges
of the branch `B = Bc₁c₂`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- **7.5, claim (2)**: *"If `F ⊆ V(G)` is connected and some vertex of `S` has a neighbour in
`F`, and so does some vertex of `T`, and `F ∩ (X₀ ∪ X₁ ∪ Y) = ∅`, then the theorem holds."* -/
theorem thm75Claim2 {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y)
    (X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (F : Set V) (hFconn : ConnectedSet G F)
    (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f)
    (hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f) :
    (∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
        ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
          IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
      AdmitsBalancedSkewPartition G := by
  classical
  let H' : SimpleGraph (Fin (Fintype.card W)) :=
    SimpleGraph.map (Fintype.equivFin W).toEmbedding H
  let ψ : H ≃g H' := SimpleGraph.Iso.map (Fintype.equivFin W) H
  let φ' : H'.lineGraph ≃g G.induce K :=
    (Thm75Claim2Transport.lineGraphIso ψ).symm.trans φ
  let B' : List (Fin (Fintype.card W)) := B.map ψ
  have happ' : IsAppearance G J H' K :=
    Thm75Claim2Transport.isAppearance_map ψ happ φ
  have hbranch' : IsBranch H' B' := by
    exact Thm75Claim2Transport.isBranch_map ψ hbranch
  have hfrom' : IsTrackFrom H' B' (ψ c₁) (ψ c₂) := by
    exact Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map ψ hfrom
  have hodd' : Odd (trackLength B') := by
    simpa [B', trackLength] using hodd
  have hlen' : 3 ≤ trackLength B' := by
    simpa [B', trackLength] using hlen
  have hN (c : W) : NSet G H' K φ' (ψ c) = NSet G H K φ c := by
    ext x
    constructor
    · rintro ⟨e', he', hec', hx⟩
      have he : Sym2.map ψ.symm e' ∈ H.edgeSet :=
        Thm75Claim2Transport.map_mem_edgeSet ψ.symm e' he'
      have hec : Sym2.map ψ.symm e' ∈ incidentEdges H c := by
        refine (Thm75Claim2Transport.mem_incidentEdges_map ψ c
          (Sym2.map ψ.symm e')).mp ?_
        rw [Thm75Claim2Transport.sym2_map_symm' ψ]
        exact hec'
      refine ⟨Sym2.map ψ.symm e', he, hec, ?_⟩
      have hb := Thm75Claim2Transport.phi_bridge ψ φ (Sym2.map ψ.symm e') he
      rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
          Thm75Claim2Transport.map_mem_edgeSet ψ (Sym2.map ψ.symm e') he⟩ : H'.edgeSet) =
          ⟨e', he'⟩ from Subtype.ext (Thm75Claim2Transport.sym2_map_symm' ψ e')] at hb
      exact hx.trans hb
    · rintro ⟨e, he, hec, hx⟩
      refine ⟨Sym2.map ψ e, Thm75Claim2Transport.map_mem_edgeSet ψ e he, ?_, ?_⟩
      · exact (Thm75Claim2Transport.mem_incidentEdges_map ψ c e).mpr hec
      · exact hx.trans (Thm75Claim2Transport.phi_bridge ψ φ e he).symm
  have hYdom' : ∀ y ∈ Y,
      IsDominantFor G (NSet G H' K φ' (ψ c₁)) (NSet G H' K φ' (ψ c₂)) y := by
    intro y hy
    simpa only [hN c₁, hN c₂] using hYdom y hy
  have hYmax' : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H' K φ' (ψ c₁))
        (NSet G H' K φ' (ψ c₂)) y) → Y' = Y := by
    intro Y' hsub hanti hdom
    apply hYmax Y' hsub hanti
    intro y hy
    simpa only [hN c₁, hN c₂] using hdom y hy
  have hmapback : B'.map ψ.symm = B := by
    simp [B', List.map_map]
  have hRset' : Rset = {x : V | ∃ (e : Sym2 (Fin (Fintype.card W))) (he : e ∈ H'.edgeSet),
      e ∈ trackEdges B' ∧ x = (↑(φ' ⟨e, he⟩) : V)} := by
    rw [hRset]
    rw [← Thm75Claim2Transport.rungSet_map ψ φ B']
    rw [hmapback]
  have hX₁' : X₁ = X ∩
      (NSet G H' K φ' (ψ c₁) ∪ NSet G H' K φ' (ψ c₂)) := by
    rw [hN c₁, hN c₂]
    exact hX₁
  have hFcard : F.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_card F
  exact Workspace.ProofLemmas.Thm75Claim2Generalised.thm75Claim2Generalised
    G hG J hJ (Fintype.card V) (Fintype.card W) H' K φ' happ' B' (ψ c₁) (ψ c₂)
      hbranch' hfrom' hodd' hlen' Y hYne hYanti hYdom' hYmax' X X₀ X₁ Rset S T F hX
      hRset' hX₀ hX₁' hS hT hFcard hFconn hFdisj hSF hTF

end Workspace.ProofLemmas.Thm75Claim2
