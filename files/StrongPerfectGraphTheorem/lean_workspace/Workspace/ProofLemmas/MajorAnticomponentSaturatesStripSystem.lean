import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemMaximal
import Workspace.Statements.S06.Thm_6_1
import Workspace.Statements.S07.Thm_7_5
import Workspace.Statements.S08.Thm_8_3
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily
import Workspace.ProofLemmas.SixVertexBipartiteK4SubdivisionDegenerate
import Workspace.ProofLemmas.MajorAnticomponentSaturatesLineGraphChoice

set_option autoImplicit false

namespace Workspace.ProofLemmas.MajorAnticomponentSaturatesStripSystem

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.StripSystemMaximal (Enlarges)

/-- **8.6, claim (1)** (printed pp. 45--46).

For the natural system, `hS₀K₀`, `hR₀`, and `hR₀K₀` record respectively that its vertex set is
the displayed appearance, that its old track rungs form that appearance, and that their union is
exactly `K₀`. -/
theorem majorAnticomponentSaturatesStripSystem
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n₀ : ℕ) (H₀ : SimpleGraph (Fin n₀)) (K₀ : Set V)
    (hH₀ : IsAppearance G J H₀ K₀)
    (S₀ : U → U → Set V) (N₀ : U → Set V)
    (hS₀ : IsJStripSystem G J S₀ N₀)
    (hS₀K₀ : stripSystemVertices J S₀ = K₀)
    (R₀ : U → U → List V)
    (hR₀ : FormsLineGraph G J S₀ N₀ R₀ H₀)
    (hR₀K₀ : ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₀ u v} = K₀)
    (S : U → U → Set V) (N : U → Set V)
    (hS : IsJStripSystem G J S N)
    (hEnlarges : Enlarges J S₀ N₀ S N)
    (hMaximal : MaximalStripSystem G J S N)
    (hOldRungs : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R₀ u v))
    (hNoBalancedSkew : ¬ AdmitsBalancedSkewPartition G)
    (hNoNondegenerateEnlargement : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement J J' ∧ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
        IsAppearance G J' H K ∧ NondegenerateAppearance J' H)
    (hDegenerate : DegenerateAppearance J H₀ →
      Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
        IsJEnlargement J J' ∧ Appears Gᶜ J')
    (hNoOvershadowed :
      (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∨
        Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) →
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
          IsAppearance G J H K ∧ IsOvershadowedAppearance G H K φ)
    (Y : Set V)
    (hY : Y = {y : V | MajorForStripSystem G J S N y})
    (hYne : Y.Nonempty)
    (YPrime : Set V) (hYPrime : IsAnticomponent G Y YPrime)
    (X : Set V) (hX : X = {x : V | VertexComplete G x YPrime}) :
    SaturatesStripSystem J S N (X ∩ stripSystemVertices J S) := by
  classical
  have hFormsOld : FormsLineGraph G J S N R₀ H₀ := by
    refine ⟨hOldRungs, ?_⟩
    rw [hR₀K₀]
    exact hH₀
  have hDegenerate' : DegenerateAppearance J H₀ →
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
        IsJEnlargement J J' ∧ Appears Gᶜ J' := by
    intro h
    exact ⟨(hDegenerate h).2.1, (hDegenerate h).2.2⟩
  have hYPrimeAnti : AnticonnectedSet G YPrime := hYPrime.2.1
  have hLineSat
      (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
      (hForms : FormsLineGraph G J S N R H)
      (φ : H.lineGraph ≃g G.induce
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
      (ι : U → Fin n) (E : U → U → Sym2 (Fin n))
      (hιInj : Function.Injective ι)
      (hRange : Set.range ι = branchVertices H)
      (hEdges : ∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet)
      (hIncident : ∀ u : U,
        incidentEdges H (ι u) = {e : Sym2 (Fin n) | ∃ v : U, J.Adj u v ∧ e = E u v})
      (hEInj : ∀ u v v' : U,
        J.Adj u v → J.Adj u v' → E u v = E u v' → v = v')
      (hEnd : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
        IsPathFrom G (R u v) s t → (↑(φ ⟨E u v, he⟩) : V) = s) :
      SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ X} := by
    have hKSub :
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) ⊆
          stripSystemVertices J S := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      simp only [stripSystemVertices, Set.mem_iUnion]
      rcases hz with ⟨a, b, hab, hzR⟩
      rcases hForms.1 a b hab with ⟨_, s, t, hPath, hStrip, hNu, hNv⟩
      exact ⟨a, b, hab, hStrip z hzR⟩
    have hMajor : ∀ y ∈ YPrime,
        MajorForLineGraph G H
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) φ y := by
      intro y hy
      have hyStrip : MajorForStripSystem G J S N y := by
        change y ∈ {z : V | MajorForStripSystem G J S N z}
        rw [← hY]
        exact hYPrime.1 hy
      refine ⟨fun hyK => hyStrip.1 (hKSub hyK), ?_⟩
      intro b hb e he f hf
      rw [← hRange] at hb
      rcases hb with ⟨u, rfl⟩
      have heIndex := he.1
      have hfIndex := hf.1
      rw [hIncident u] at heIndex hfIndex
      rcases heIndex with ⟨v, huv, rfl⟩
      rcases hfIndex with ⟨w, huw, rfl⟩
      rcases hForms.1 u v huv with ⟨_, s, t, hPath, hStrip, hNu, hNv⟩
      rcases hForms.1 u w huw with ⟨_, s', t', hPath', hStrip', hNu', hNv'⟩
      have hsMem : s ∈ R u v := List.mem_of_mem_head? hPath.2.1
      have hs'Mem : s' ∈ R u w := List.mem_of_mem_head? hPath'.2.1
      have hys : ¬ G.Adj y s := by
        intro hAdj
        apply he.2
        refine ⟨hEdges u v huv, ?_⟩
        rw [hEnd u v huv (hEdges u v huv) s t hPath]
        exact hAdj
      have hys' : ¬ G.Adj y s' := by
        intro hAdj
        apply hf.2
        refine ⟨hEdges u w huw, ?_⟩
        rw [hEnd u w huw (hEdges u w huw) s' t' hPath']
        exact hAdj
      have hvBad : v ∈ {z : U | J.Adj u z ∧
          ¬ stripSystemNuv S N u z ⊆ G.neighborSet y ∩ stripSystemVertices J S} := by
        refine ⟨huv, Set.not_subset.mpr ⟨s, ?_, ?_⟩⟩
        · exact ⟨(hNu s hsMem).2 rfl, hStrip s hsMem⟩
        · rintro ⟨hsNeighbor, -⟩
          exact hys hsNeighbor
      have hwBad : w ∈ {z : U | J.Adj u z ∧
          ¬ stripSystemNuv S N u z ⊆ G.neighborSet y ∩ stripSystemVertices J S} := by
        refine ⟨huw, Set.not_subset.mpr ⟨s', ?_, ?_⟩⟩
        · exact ⟨(hNu' s' hs'Mem).2 rfl, hStrip' s' hs'Mem⟩
        · rintro ⟨hs'Neighbor, -⟩
          exact hys' hs'Neighbor
      have hvw : v = w := hyStrip.2 u hvBad hwBad
      subst w
      rfl
    exact Workspace.ProofLemmas.MajorAnticomponentSaturatesLineGraphChoice
      G hG J hJ S N hS n₀ H₀ R₀ hFormsOld hNoBalancedSkew hNoOvershadowed
      hDegenerate' YPrime hYPrimeAnti X hX n H R hForms φ hMajor
  intro u v hv w hw
  rcases hv with ⟨huv, hv⟩
  rcases hw with ⟨huw, hw⟩
  by_contra hvw
  obtain ⟨x, hxNuv, hx⟩ := Set.not_subset.mp hv
  obtain ⟨x', hx'Nuw, hx'⟩ := Set.not_subset.mp hw
  have hxK : x ∈ stripSystemVertices J S := by
    simp only [stripSystemVertices, Set.mem_iUnion]
    exact ⟨u, v, huv, hxNuv.2⟩
  have hx'K : x' ∈ stripSystemVertices J S := by
    simp only [stripSystemVertices, Set.mem_iUnion]
    exact ⟨u, w, huw, hx'Nuw.2⟩
  have hxNotX : x ∉ X := fun hxX => hx ⟨hxX, hxK⟩
  have hx'NotX : x' ∉ X := fun hx'X => hx' ⟨hx'X, hx'K⟩
  obtain ⟨P, hP, hxP⟩ := hS.2.2.2.1 u v huv x hxNuv.2
  obtain ⟨Q, hQ, hx'Q⟩ := hS.2.2.2.1 u w huw x' hx'Nuw.2
  rcases hP with ⟨_, s, t, hPathP, hPStrip, hPNu, hPNv⟩
  rcases hQ with ⟨_, s', t', hPathQ, hQStrip, hQNu, hQNv⟩
  have hxs : x = s := (hPNu x hxP).1 hxNuv.1
  have hx's' : x' = s' := (hQNu x' hx'Q).1 hx'Nuw.1
  subst s
  subst s'
  obtain ⟨R, hR, hRsymm, hRuv, hRuw⟩ :=
    Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily
      G J S N hS u v w huv huw hvw P Q
      ⟨huv, x, t, hPathP, hPStrip, hPNu, hPNv⟩
      ⟨huw, x', t', hPathQ, hQStrip, hQNu, hQNv⟩
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hS R hR hRsymm
  obtain ⟨φ, ι, E, hιInj, hRange, hEdges, hIncident, hEInj, hEnd⟩ :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.rungEndDictionary
      G J hJ S N hS H R hForms
  have hSat := hLineSat n H R hForms φ ι E hιInj hRange hEdges hIncident hEInj hEnd
  have hPathRuv : IsPathFrom G (R u v) x t := by
    rw [hRuv]
    exact hPathP
  have hPathRuw : IsPathFrom G (R u w) x' t' := by
    rw [hRuw]
    exact hPathQ
  have hBranch : ι u ∈ branchVertices H := by
    rw [← hRange]
    exact ⟨u, rfl⟩
  have heMissing : E u v ∈ incidentEdges H (ι u) \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
    constructor
    · rw [hIncident u]
      exact ⟨v, huv, rfl⟩
    · rintro ⟨he, heX⟩
      rw [hEnd u v huv he x t hPathRuv] at heX
      exact hxNotX heX
  have hfMissing : E u w ∈ incidentEdges H (ι u) \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
    constructor
    · rw [hIncident u]
      exact ⟨w, huw, rfl⟩
    · rintro ⟨he, heX⟩
      rw [hEnd u w huw he x' t' hPathRuw] at heX
      exact hx'NotX heX
  have hEq : E u v = E u w := hSat (ι u) hBranch heMissing hfMissing
  exact hvw (hEInj u v w huv huw hEq)

end Workspace.ProofLemmas.MajorAnticomponentSaturatesStripSystem
