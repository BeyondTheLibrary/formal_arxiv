import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SixVertexBipartiteK4SubdivisionDegenerate
import Workspace.Statements.S06.Thm_6_1
import Workspace.Statements.S07.Thm_7_5
import Workspace.Statements.S08.Thm_8_3
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.Types.StripSystems.SPGT

/-- The common neighbours of an anticonnected set of major vertices saturate every
line-graph appearance formed by a choice of rungs in the strip system. -/
theorem MajorAnticomponentSaturatesLineGraphChoice
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (hS : IsJStripSystem G J S N)
    (n₀ : ℕ) (H₀ : SimpleGraph (Fin n₀)) (R₀ : U → U → List V)
    (hR₀ : FormsLineGraph G J S N R₀ H₀)
    (hNoBalancedSkew : ¬ AdmitsBalancedSkewPartition G)
    (hNoOvershadowed :
      (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∨
        Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) →
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
          IsAppearance G J H K ∧ IsOvershadowedAppearance G H K φ)
    (hDegenerate : DegenerateAppearance J H₀ →
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
        IsJEnlargement J J' ∧ Appears Gᶜ J')
    (YPrime : Set V) (hYPrime : AnticonnectedSet G YPrime)
    (X : Set V) (hX : X = {x : V | VertexComplete G x YPrime})
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (hR : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce
      (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (hMajor : ∀ y ∈ YPrime,
      MajorForLineGraph G H
        (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) φ y) :
    SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ X} := by
  classical
  let K : Set V :=
    ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}
  change H.lineGraph ≃g G.induce K at φ
  change ∀ y ∈ YPrime, MajorForLineGraph G H K φ y at hMajor
  change SaturatesLineGraph H
    {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}
  by_contra hnotsat
  have hnotsatVC : ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        VertexComplete G (↑(φ ⟨e, he⟩) : V) YPrime} := by
    simpa [hX] using hnotsat
  obtain ⟨Jf, ⟨eJ⟩⟩ := IsoTransport.exists_iso_fin J
  have hJf : IsKConnected Jf 3 :=
    SubdivisionCounting.isKConnected_of_iso eJ hJ
  have hsubf : IsBipartiteSubdivision Jf H :=
    ⟨Thm85Five8Transported.isSubdivision_of_iso eJ hR.2.1.1, hR.2.1.2⟩
  have hshape_transport :
      (Nonempty (Jf ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
        Nonempty (Jf ≃g (⊤ : SimpleGraph (Fin 4)))) →
      (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∨
        Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) := by
    intro hshape
    rcases hshape with h33 | h4
    · exact Or.inr ⟨eJ.trans h33.some⟩
    · exact Or.inl ⟨eJ.trans h4.some⟩
  have hdeg_transport (hdeg : DegenerateAppearance Jf H) :
      DegenerateAppearance J H := by
    rcases hdeg with ⟨h4, hcycle⟩ | ⟨hnot4, h33, hH33⟩
    · exact Or.inl ⟨⟨eJ.trans h4.some⟩, hcycle⟩
    · exact Or.inr ⟨(fun h4 => hnot4 ⟨eJ.symm.trans h4.some⟩),
        ⟨eJ.trans h33.some⟩, hH33⟩
  have happ_transport {q : ℕ} {A : SimpleGraph (Fin q)} {L : Set V}
      (happ : IsAppearance G Jf A L) : IsAppearance G J A L :=
    ⟨⟨Thm85Five8Transported.isSubdivision_of_iso eJ.symm happ.1.1,
        happ.1.2⟩, happ.2⟩
  have happ_compl_transport {q : ℕ} {A : SimpleGraph (Fin q)} {L : Set V}
      (happ : IsAppearance Gᶜ Jf A L) : IsAppearance Gᶜ J A L :=
    ⟨⟨Thm85Five8Transported.isSubdivision_of_iso eJ.symm happ.1.1,
        happ.1.2⟩, happ.2⟩
  have henl_transport {m' : ℕ} {J' : SimpleGraph (Fin m')}
      (henl : IsJEnlargement Jf J') : IsJEnlargement J J' := by
    rcases henl with ⟨hconn, T, hproper, q, D, hsub, hiso⟩
    exact ⟨hconn, T, hproper, q, D,
      Thm85Five8Transported.isSubdivision_of_iso eJ.symm hsub, hiso⟩
  have hdeg_old
      (hshape : Nonempty (Jf ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
        Nonempty (Jf ≃g (⊤ : SimpleGraph (Fin 4))))
      (hdeg : DegenerateAppearance Jf H) : DegenerateAppearance J H₀ := by
    have hshapeJ := hshape_transport hshape
    have hdegJ := hdeg_transport hdeg
    by_contra hnd₀
    have hndStrip : NondegenerateStripSystem G J S N :=
      ⟨n₀, H₀, R₀, hR₀, hnd₀⟩
    have hnoover : ¬ ∃ (q : ℕ) (A : SimpleGraph (Fin q)) (L : Set V)
        (ψ : A.lineGraph ≃g G.induce L),
          IsAppearance G J A L ∧ IsOvershadowedAppearance G A L ψ :=
      hNoOvershadowed hshapeJ
    have hndH := Workspace.Statements.S08.SPGT.thm_8_3
      G hG J hJ S N hS hndStrip hnoover n H R hR
    exact hndH hdegJ
  have hcases := Workspace.Statements.S06.SPGT.thm_6_1
    G hG (Fintype.card U) Jf hJf n H K hsubf φ YPrime hYPrime hMajor hnotsatVC
  rcases hcases with h₁ | h₂ | h₃ | h₄ | h₅
  · rcases h₁ with ⟨hshape, q, A, L, ψ, happ, hover⟩
    exact hNoOvershadowed (hshape_transport hshape)
      ⟨q, A, L, ψ, happ_transport happ, hover⟩
  · rcases h₂ with ⟨hshape, hdeg, q, A, L, ψ, happ, hover⟩
    obtain ⟨hJ33, hnoenl⟩ := hDegenerate (hdeg_old hshape hdeg)
    rcases Workspace.Statements.S07.SPGT.thm_7_5 Gᶜ
        (HoleBasics.berge_compl.mpr hG) J hJ A L ψ
        (happ_compl_transport happ) hover with henl | hbsp
    · rcases henl with ⟨m', J', hJ', q', A', L', happ', hnd'⟩
      exact hnoenl ⟨m', J', hJ', q', A', L', happ'⟩
    · exact hNoBalancedSkew
        (ClassLemmas.admitsBalancedSkewPartition_compl.mp hbsp)
  · rcases h₃ with ⟨hJf33, hdeg, m', J', henl, happ⟩
    obtain ⟨hJ33, hnoenl⟩ := hDegenerate
      (hdeg_old (Or.inl hJf33) hdeg)
    exact hnoenl ⟨m', J', henl_transport henl, happ⟩
  · rcases h₄ with ⟨hJf4, hcard⟩
    have hdeg : DegenerateAppearance Jf H :=
      SixVertexBipartiteK4SubdivisionDegenerate Jf H hJf4 hsubf hcard
    obtain ⟨hJ33, hnoenl⟩ := hDegenerate
      (hdeg_old (Or.inr hJf4) hdeg)
    obtain ⟨e4⟩ := hJf4
    obtain ⟨e33⟩ := hJ33
    have hcard' : Fintype.card (Fin 4) = Fintype.card (Fin 3 ⊕ Fin 3) :=
      Fintype.card_congr (e4.symm.trans (eJ.symm.trans e33)).toEquiv
    simp at hcard'
  · rcases h₅ with ⟨hJf4, hdeg, hrest⟩
    obtain ⟨hJ33, hnoenl⟩ := hDegenerate
      (hdeg_old (Or.inr hJf4) hdeg)
    obtain ⟨e4⟩ := hJf4
    obtain ⟨e33⟩ := hJ33
    have hcard' : Fintype.card (Fin 4) = Fintype.card (Fin 3 ⊕ Fin 3) :=
      Fintype.card_congr (e4.symm.trans (eJ.symm.trans e33)).toEquiv
    simp at hcard'

end Workspace.ProofLemmas
