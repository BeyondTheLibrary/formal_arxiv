import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.AppearanceVertexTypeTransport

/-!
# Moving the knot appearance dictionary onto `Fin n`

`Workspace.ProofLemmas.Thm93Infrastructure.KnotAppearanceData` asks for a subdivision on
`Fin n`, while the subdivision built for 9.3 lives on a sum type.  This file re-indexes it,
using the transport lemmas of `AppearanceVertexTypeTransport`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93KnotTransportW

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

/-- The whole appearance package, re-indexed from an arbitrary finite vertex type onto
`Fin (Fintype.card W)`. -/
theorem transportW {V W : Type*} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (P₁ P₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (c₁ c₂ c₃ c₄ : W) (N : W → Set V)
    (hsub : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (hdeg : DegenerateK4Appearance H)
    (hN : ∀ c : W, N c = {v : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(φ ⟨e, he⟩) : V)})
    (hnd : [c₁, c₂, c₃, c₄].Nodup)
    (h12 : H.Adj c₁ c₂) (h23 : H.Adj c₂ c₃) (h34 : H.Adj c₃ c₄) (h41 : H.Adj c₄ c₁)
    (hbv : branchVertices H = ({c₁, c₂, c₃, c₄} : Set W))
    (hx₁ : ∃ he : s(c₁, c₂) ∈ H.edgeSet, (↑(φ ⟨s(c₁, c₂), he⟩) : V) = x₁)
    (hy₂ : ∃ he : s(c₂, c₃) ∈ H.edgeSet, (↑(φ ⟨s(c₂, c₃), he⟩) : V) = y₂)
    (hy₁ : ∃ he : s(c₃, c₄) ∈ H.edgeSet, (↑(φ ⟨s(c₃, c₄), he⟩) : V) = y₁)
    (hx₂ : ∃ he : s(c₄, c₁) ∈ H.edgeSet, (↑(φ ⟨s(c₄, c₁), he⟩) : V) = x₂)
    (hN₁ : N c₁ = ({x₁, x₂, a₁} : Set V)) (hN₂ : N c₂ = ({x₁, y₂, a₂} : Set V))
    (hN₃ : N c₃ = ({y₁, y₂, b₁} : Set V)) (hN₄ : N c₄ = ({y₁, x₂, b₂} : Set V))
    (hB₁ : ∃ q : List W, IsBranch H q ∧ IsTrackFrom H q c₁ c₃ ∧
      {v : V | v ∈ P₁} = {v : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ v = (↑(φ ⟨e, he⟩) : V)})
    (hB₂ : ∃ q : List W, IsBranch H q ∧ IsTrackFrom H q c₂ c₄ ∧
      {v : V | v ∈ P₂} = {v : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ v = (↑(φ ⟨e, he⟩) : V)}) :
    KnotAppearanceData G P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K := by
  classical
  set ψ : H ≃g SimpleGraph.map (Fintype.equivFin W).toEmbedding H :=
    SimpleGraph.Iso.map (Fintype.equivFin W) H with hψ
  set H' := SimpleGraph.map (Fintype.equivFin W).toEmbedding H with hH'
  set φ' := (Thm75Claim2Transport.lineGraphIso ψ).symm.trans φ with hφ'
  have hedge : ∀ (e : Sym2 W) (he : e ∈ H.edgeSet),
      (↑(φ' ⟨Sym2.map ψ e, Thm75Claim2Transport.map_mem_edgeSet ψ e he⟩) : V)
        = (↑(φ ⟨e, he⟩) : V) := Thm75Claim2Transport.phi_bridge ψ φ
  have hcross : ∀ (u v : W) (huv : H.Adj u v) (z : V),
      (∃ he : s(u, v) ∈ H.edgeSet, (↑(φ ⟨s(u, v), he⟩) : V) = z) →
      ∃ he : s(ψ u, ψ v) ∈ H'.edgeSet, (↑(φ' ⟨s(ψ u, ψ v), he⟩) : V) = z := by
    intro u v huv z hz
    obtain ⟨he0, hval⟩ := hz
    have hmem : s(ψ u, ψ v) ∈ H'.edgeSet := ψ.map_adj_iff.mpr huv
    refine ⟨hmem, ?_⟩
    have hsub2 : (⟨s(ψ u, ψ v), hmem⟩ : H'.edgeSet)
        = ⟨Sym2.map ψ s(u, v), Thm75Claim2Transport.map_mem_edgeSet ψ _ he0⟩ :=
      Subtype.ext (Sym2.map_pair_eq ..).symm
    rw [hsub2, hedge s(u, v) he0, hval]
  refine ⟨Fintype.card W, H', φ',
    ⟨Thm75Claim2Transport.isBipartiteSubdivision_map ψ hsub, ⟨φ'⟩⟩,
    Workspace.ProofLemmas.SubdivisionCounting.degenerateK4Appearance_of_iso ψ hdeg,
    ψ c₁, ψ c₂, ψ c₃, ψ c₄, fun c => N (ψ.symm c), ?_, ?_,
    ψ.map_adj_iff.mpr h12, ψ.map_adj_iff.mpr h23, ψ.map_adj_iff.mpr h34,
    ψ.map_adj_iff.mpr h41, ?_,
    hcross c₁ c₂ h12 x₁ hx₁, hcross c₂ c₃ h23 y₂ hy₂, hcross c₃ c₄ h34 y₁ hy₁,
    hcross c₄ c₁ h41 x₂ hx₂,
    by simpa using hN₁, by simpa using hN₂, by simpa using hN₃, by simpa using hN₄, ?_, ?_⟩
  · -- the transported `N`
    intro c
    show N (ψ.symm c) = _
    rw [hN (ψ.symm c)]
    ext v
    constructor
    · rintro ⟨e, he, hec, rfl⟩
      refine ⟨Sym2.map ψ e, Thm75Claim2Transport.map_mem_edgeSet ψ e he, ?_, ?_⟩
      · have h := (Thm75Claim2Transport.mem_incidentEdges_map ψ (ψ.symm c) e).mpr hec
        rwa [RelIso.apply_symm_apply] at h
      · exact (hedge e he).symm
    · rintro ⟨e', he', hec', rfl⟩
      refine ⟨Sym2.map ψ.symm e', Thm75Claim2Transport.map_mem_edgeSet ψ.symm e' he', ?_, ?_⟩
      · refine (Thm75Claim2Transport.mem_incidentEdges_map ψ (ψ.symm c) _).mp ?_
        rw [Thm75Claim2Transport.sym2_map_symm' ψ, RelIso.apply_symm_apply]
        exact hec'
      · have hb := hedge (Sym2.map ψ.symm e')
          (Thm75Claim2Transport.map_mem_edgeSet ψ.symm e' he')
        rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
            Thm75Claim2Transport.map_mem_edgeSet ψ (Sym2.map ψ.symm e')
              (Thm75Claim2Transport.map_mem_edgeSet ψ.symm e' he')⟩ : H'.edgeSet)
            = ⟨e', he'⟩ from Subtype.ext (Thm75Claim2Transport.sym2_map_symm' ψ e')] at hb
        exact hb
  · -- nodup
    have := hnd.map (EquivLike.injective ψ)
    simpa using this
  · -- branch-vertices
    rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ, hbv]
    simp [Set.image_insert_eq]
  · obtain ⟨q, hq, ht, hset⟩ := hB₁
    refine ⟨q.map ψ, Thm75Claim2Transport.isBranch_map ψ hq,
      Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map ψ ht, ?_⟩
    rw [hset, ← Thm75Claim2Transport.rungSet_map ψ φ (q.map ψ)]
    simp [List.map_map]
  · obtain ⟨q, hq, ht, hset⟩ := hB₂
    refine ⟨q.map ψ, Thm75Claim2Transport.isBranch_map ψ hq,
      Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map ψ ht, ?_⟩
    rw [hset, ← Thm75Claim2Transport.rungSet_map ψ φ (q.map ψ)]
    simp [List.map_map]

end Workspace.ProofLemmas.Thm93KnotTransportW
