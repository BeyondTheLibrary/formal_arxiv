import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.NoMajorVerticesCleanPath
import Workspace.ProofLemmas.NoMajorVerticesDegenerate
import Workspace.ProofLemmas.NoMajorVerticesSetChoice
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.StripSystemCrossAdjacency
import Workspace.Statements.S04.Thm_4_2

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoMajorVerticesOutsideMaximalStripSystem

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools.SPGT

theorem noMajorVerticesOutsideMaximalStripSystem
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (hstrip : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (hnoSkew : ¬ AdmitsBalancedSkewPartition G)
    (hlocal : ∀ F : Set V,
      IsComponent G
        ((stripSystemVertices J S ∪
          {y : V | MajorForStripSystem G J S N y})ᶜ) F →
      LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)))
    (hsaturates :
      {y : V | MajorForStripSystem G J S N y}.Nonempty →
      ∀ Y' : Set V,
        IsAnticomponent G {y : V | MajorForStripSystem G J S N y} Y' →
        SaturatesStripSystem J S N
          ({x : V | VertexComplete G x Y'} ∩ stripSystemVertices J S))
    (n : ℕ) (H₀ : SimpleGraph (Fin n))
    (hdeg : DegenerateAppearance J H₀ →
      Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
        IsJEnlargement J J' ∧ Appears Gᶜ J')
    (R : U → U → List V)
    (hOldRungs : FormsLineGraph G J S N R H₀) :
    {y : V | MajorForStripSystem G J S N y} = ∅ := by
  classical
  let Y : Set V := {y : V | MajorForStripSystem G J S N y}
  change Y = ∅
  by_contra hYempty
  have hYne : Y.Nonempty := Set.nonempty_iff_ne_empty.mpr hYempty
  obtain ⟨y₀, hy₀Y⟩ := hYne
  obtain ⟨Y', hY'comp, hy₀Y'⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Gᶜ Y hy₀Y
  have hsat := hsaturates (by simpa [Y] using (⟨y₀, hy₀Y⟩ : Y.Nonempty)) Y'
    (by simpa [Y] using hY'comp)
  let X : Set V := {x : V | VertexComplete G x Y'}
  let VSN : Set V := stripSystemVertices J S
  have hsatX : SaturatesStripSystem J S N (X ∩ VSN) := by
    simpa [X, VSN] using hsat

  -- Choose the paper's edge `b₁b₂`, and the two unions of all but one end class.
  obtain ⟨b₁, b₂, hb₁b₂, hselected⟩ :=
    Workspace.ProofLemmas.NoMajorVerticesSetChoice.exists_selected_edge
      (S := S) hJ X
  obtain ⟨e₁, hb₁e₁, hgood₁, he₁⟩ :=
    Workspace.ProofLemmas.NoMajorVerticesSetChoice.exists_exceptional_end
      hstrip (X ∩ VSN) hsatX hb₁b₂
  obtain ⟨e₂, hb₂e₂, hgood₂, he₂⟩ :=
    Workspace.ProofLemmas.NoMajorVerticesSetChoice.exists_exceptional_end
      hstrip (X ∩ VSN) hsatX hb₁b₂.symm
  let X₁ : Set V := N b₁ \ stripSystemNuv S N b₁ e₁
  let X₂ : Set V := (N b₂ \ stripSystemNuv S N b₂ e₂) \ X₁
  have hX₁good : X₁ ⊆ X ∩ VSN := by simpa [X₁] using hgood₁
  have hX₂good : X₂ ⊆ X ∩ VSN := fun z hz => hgood₂ hz.1
  have hX₁N : X₁ ⊆ N b₁ := fun _ hz => hz.1
  have hX₂N : X₂ ⊆ N b₂ := fun _ hz => hz.1.1
  have hX₁ne : X₁.Nonempty := by
    simpa [X₁] using
      (Workspace.ProofLemmas.NoMajorVerticesSetChoice.end_set_nonempty hJ hstrip hb₁e₁)

  -- The selected strip has a vertex outside `X₁ ∪ X₂`.
  have hcentralMiss : (S b₁ b₂ \ (X₁ ∪ X₂)).Nonempty := by
    by_cases hcentralX : S b₁ b₂ ⊆ X
    · have hVSNX : VSN ⊆ X := by simpa [VSN] using hselected hcentralX
      have hall₁ : ∀ w : U, J.Adj b₁ w → stripSystemNuv S N b₁ w ⊆ X ∩ VSN := by
        intro w hbw z hz
        exact ⟨hVSNX (Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hbw hz.2),
          Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hbw hz.2⟩
      have hall₂ : ∀ w : U, J.Adj b₂ w → stripSystemNuv S N b₂ w ⊆ X ∩ VSN := by
        intro w hbw z hz
        exact ⟨hVSNX (Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hbw hz.2),
          Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hbw hz.2⟩
      have heq₁ : e₁ = b₂ := he₁ hall₁
      have heq₂ : e₂ = b₁ := he₂ hall₂
      obtain ⟨z, hzS⟩ := Workspace.ProofLemmas.StripSystemBasics.strip_nonempty hstrip hb₁b₂
      refine ⟨z, hzS, ?_⟩
      rintro (hz₁ | hz₂)
      · exact hz₁.2 (by simpa [heq₁] using ⟨hz₁.1, hzS⟩)
      · have hzN₂ : z ∈ N b₂ := hz₂.1.1
        have hzSrev : z ∈ S b₂ b₁ := by
          rw [← Workspace.ProofLemmas.StripSystemBasics.strip_symm hstrip hb₁b₂]
          exact hzS
        exact hz₂.1.2 (by simpa [heq₂] using ⟨hzN₂, hzSrev⟩)
    · obtain ⟨z, hzS, hzX⟩ := Set.not_subset.mp hcentralX
      refine ⟨z, hzS, ?_⟩
      rintro (hz₁ | hz₂)
      · exact hzX (hX₁good hz₁).1
      · exact hzX (hX₂good hz₂).1

  let X₀ : Set V := X \ VSN
  let B : Set V := Y' ∪ X₀ ∪ X₁ ∪ X₂
  let D : Set V := Bᶜ
  have hY'subY : Y' ⊆ Y := hY'comp.1
  have hY'disjVSN : Disjoint Y' VSN := by
    rw [Set.disjoint_left]
    intro z hzY' hzS
    exact (hY'subY hzY').1 hzS
  have hYsubB : Y ⊆ B := by
    intro z hzY
    by_cases hzY' : z ∈ Y'
    · exact Or.inl (Or.inl (Or.inl hzY'))
    · have hzX : z ∈ X :=
        Workspace.ProofLemmas.LooseSkewPartition.vertexComplete_of_notMem_anticomponent
          hY'comp hzY hzY'
      exact Or.inl (Or.inl (Or.inr ⟨hzX, hzY.1⟩))
  have hBminusComplete : ∀ z ∈ B \ Y', VertexComplete G z Y' := by
    intro z hz
    rcases hz.1 with ((hzY' | hzX₀) | hzX₁) | hzX₂
    · exact (hz.2 hzY').elim
    · exact hzX₀.1
    · exact (hX₁good hzX₁).1
    · exact (hX₂good hzX₂).1
  have hY'anti : Anticomplete Gᶜ Y' (B \ Y') := by
    intro y hy z hz hadj
    exact hadj.2 ((hBminusComplete z hz y hy).symm)
  have hBsplit : B = Y' ∪ (B \ Y') := by
    ext z
    constructor
    · intro hzB
      by_cases hzY' : z ∈ Y'
      · exact Or.inl hzY'
      · exact Or.inr ⟨hzB, hzY'⟩
    · rintro (hzY' | hzB)
      · exact Or.inl (Or.inl (Or.inl hzY'))
      · exact hzB.1
  have hY'compB : IsAnticomponent G B Y' := by
    exact Workspace.Statements.S04.SPGT.Helpers42.isComponent_of_split
      (G := Gᶜ) (A := B) (S := Y') (C := Y') (T := B \ Y')
      (Workspace.Statements.S04.SPGT.Helpers42.isComponent_self hY'comp.2.1)
      ⟨y₀, hy₀Y'⟩ hBsplit hY'anti
  have hBnotanti : ¬ AnticonnectedSet G B := by
    intro hBanti
    have heq : B = Y' := hY'compB.2.2 B hY'compB.1 subset_rfl hBanti
    obtain ⟨z, hzX₁⟩ := hX₁ne
    have hzB : z ∈ B := Or.inl (Or.inr hzX₁)
    have hzY' : z ∈ Y' := by rw [← heq]; exact hzB
    exact (Set.disjoint_left.mp hY'disjVSN hzY') (hX₁good hzX₁).2

  -- If `D` were disconnected, the paper's skew partition would be loose unless every
  -- `X`-vertex of the strip system lay in `X₁ ∪ X₂`.
  have hDconn : ConnectedSet G D := by
    by_contra hDnot
    have hskew : IsSkewPartition G D B := by
      refine ⟨?_, ?_, hDnot, hBnotanti⟩
      · simpa [D] using Set.compl_union_self B
      · simpa [D] using (disjoint_compl_left : Disjoint Bᶜ B)
    have hcoverX : X ∩ VSN ⊆ X₁ ∪ X₂ := by
      intro z hz
      by_contra hz12
      have hzD : z ∈ D := by
        simp only [D, Set.mem_compl_iff]
        intro hzB
        rcases hzB with ((hzY' | hzX₀) | hzX₁) | hzX₂
        · exact (Set.disjoint_left.mp hY'disjVSN hzY') hz.2
        · exact hzX₀.2 hz.2
        · exact hz12 (Or.inl hzX₁)
        · exact hz12 (Or.inr hzX₂)
      have hloose : IsLooseSkewPartition G D B :=
        ⟨hskew, Or.inr ⟨z, hzD, Y', hY'compB, hz.1⟩⟩
      exact hnoSkew (Workspace.Statements.S04.SPGT.thm_4_2 G hG ⟨D, B, hloose⟩)
    have hinside :
        (X ∩ VSN) ∩
            (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) ⊆
          N b₁ ∪ N b₂ := by
      intro z hz
      rcases hcoverX ⟨hz.1.1, hz.1.2⟩ with hz₁ | hz₂
      · exact Or.inl (hX₁N hz₁)
      · exact Or.inr (hX₂N hz₂)
    obtain ⟨hK₄, hdegH₀⟩ :=
      Workspace.ProofLemmas.NoMajorVerticesDegenerate.saturation_inside_two_ends_forces_degenerate
        G J hJ S N hstrip (X ∩ VSN) hsatX b₁ b₂ hb₁b₂ n H₀ R hOldRungs hinside
    obtain ⟨-, hK₃₃, -⟩ := hdeg hdegH₀
    have hcard4 : Fintype.card U = 4 := by
      obtain ⟨e⟩ := hK₄
      simpa using Fintype.card_congr e.toEquiv
    have hcard6 : Fintype.card U = 6 := by
      obtain ⟨e⟩ := hK₃₃
      simpa using Fintype.card_congr e.toEquiv
    omega

  -- A vertex in the selected strip and a vertex in a different strip, both outside the two
  -- retained end sets, cannot form a local pair.
  have hnotLocalPair : ∀ a ∈ S b₁ b₂, ∀ b ∈ VSN, b ∉ S b₁ b₂ →
      a ∉ X₁ ∪ X₂ → b ∉ X₁ ∪ X₂ →
      ¬ LocalForStripSystem J S N ({a, b} : Set V) := by
    intro a haS b hbVS hbS ha12 hb12
    rintro (⟨w, hw⟩ | ⟨c, d, hcd, hcdsub⟩)
    · have haN : a ∈ N w := hw (by simp)
      have hbN : b ∈ N w := hw (by simp)
      have hwends : w = b₁ ∨ w = b₂ := by
        by_contra h
        push Not at h
        have : a ∈ S b₁ b₂ ∩ N w := ⟨haS, haN⟩
        rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty
          hstrip hb₁b₂ h.1 h.2] at this
        exact this
      rcases hwends with hwb₁ | hwb₂
      · have haN₁ : a ∈ N b₁ := by simpa [hwb₁] using haN
        have hbN₁ : b ∈ N b₁ := by simpa [hwb₁] using hbN
        have haE : a ∈ stripSystemNuv S N b₁ e₁ := by
          refine ⟨haN₁, ?_⟩
          by_contra hnot
          exact ha12 (Or.inl ⟨haN₁, fun haNuv => hnot haNuv.2⟩)
        have haC : a ∈ stripSystemNuv S N b₁ b₂ := ⟨haN₁, haS⟩
        have heq : e₁ = b₂ :=
          Workspace.ProofLemmas.StripSystemBasics.Nuv_eq_of_mem hstrip hb₁e₁ hb₁b₂ haE haC
        have hbE : b ∈ stripSystemNuv S N b₁ e₁ := by
          refine ⟨hbN₁, ?_⟩
          by_contra hnot
          exact hb12 (Or.inl ⟨hbN₁, fun hbNuv => hnot hbNuv.2⟩)
        exact hbS (by simpa [heq] using hbE.2)
      · have haN₂ : a ∈ N b₂ := by simpa [hwb₂] using haN
        have hbN₂ : b ∈ N b₂ := by simpa [hwb₂] using hbN
        have haE : a ∈ stripSystemNuv S N b₂ e₂ := by
          refine ⟨haN₂, ?_⟩
          by_contra hnot
          have haFirst : a ∈ N b₂ \ stripSystemNuv S N b₂ e₂ :=
            ⟨haN₂, fun haNuv => hnot haNuv.2⟩
          exact ha12 (Or.inr ⟨haFirst, fun h => ha12 (Or.inl h)⟩)
        have haC : a ∈ stripSystemNuv S N b₂ b₁ := by
          refine ⟨haN₂, ?_⟩
          rw [← Workspace.ProofLemmas.StripSystemBasics.strip_symm hstrip hb₁b₂]
          exact haS
        have heq : e₂ = b₁ :=
          Workspace.ProofLemmas.StripSystemBasics.Nuv_eq_of_mem
            hstrip hb₂e₂ hb₁b₂.symm haE haC
        have hbE : b ∈ stripSystemNuv S N b₂ e₂ := by
          refine ⟨hbN₂, ?_⟩
          by_contra hnot
          have hbFirst : b ∈ N b₂ \ stripSystemNuv S N b₂ e₂ :=
            ⟨hbN₂, fun hbNuv => hnot hbNuv.2⟩
          exact hb12 (Or.inr ⟨hbFirst, fun h => hb12 (Or.inl h)⟩)
        exact hbS (by
          have hmem : b ∈ S b₂ b₁ := by simpa [heq] using hbE.2
          rw [Workspace.ProofLemmas.StripSystemBasics.strip_symm hstrip hb₁b₂]
          exact hmem)
    · have haCD : a ∈ S c d := hcdsub (by simp)
      have hbCD : b ∈ S c d := hcdsub (by simp)
      have heq := Workspace.ProofLemmas.StripSystemBasics.strip_eq_of_mem_strips
        hstrip hcd hb₁b₂ haCD haS
      apply hbS
      rw [← heq]
      exact hbCD

  obtain ⟨u, huS, hu12⟩ := hcentralMiss
  obtain ⟨c, d, hcd, hc₁, hc₂, hd₁, hd₂⟩ :=
    Workspace.ProofLemmas.NoMajorVerticesSetChoice.exists_edge_avoiding_edge hJ hb₁b₂
  obtain ⟨v, hvS⟩ := Workspace.ProofLemmas.StripSystemBasics.strip_nonempty hstrip hcd
  have hedgeNe : s(c, d) ≠ s(b₁, b₂) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hc₁ h
    · exact hc₂ h
  have hvCentral : v ∉ S b₁ b₂ := by
    intro hv
    exact hedgeNe (Workspace.ProofLemmas.StripSystemBasics.edge_eq_of_mem_strips
      hstrip hcd hb₁b₂ hvS hv)
  have hvVSN : v ∈ VSN :=
    Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hcd hvS
  have hvN₁ : v ∉ N b₁ := by
    intro hvN
    have : v ∈ S c d ∩ N b₁ := ⟨hvS, hvN⟩
    rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty hstrip hcd
      (Ne.symm hc₁) (Ne.symm hd₁)] at this
    exact this
  have hvN₂ : v ∉ N b₂ := by
    intro hvN
    have : v ∈ S c d ∩ N b₂ := ⟨hvS, hvN⟩
    rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty hstrip hcd
      (Ne.symm hc₂) (Ne.symm hd₂)] at this
    exact this
  have hv12 : v ∉ X₁ ∪ X₂ := by
    rintro (h | h)
    · exact hvN₁ (hX₁N h)
    · exact hvN₂ (hX₂N h)
  have huD : u ∈ D := by
    simp only [D, Set.mem_compl_iff]
    rintro (((huY' | huX₀) | huX₁) | huX₂)
    · exact (Set.disjoint_left.mp hY'disjVSN huY')
        (Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hb₁b₂ huS)
    · exact huX₀.2
        (Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hb₁b₂ huS)
    · exact hu12 (Or.inl huX₁)
    · exact hu12 (Or.inr huX₂)
  have hvD : v ∈ D := by
    simp only [D, Set.mem_compl_iff]
    rintro (((hvY' | hvX₀) | hvX₁) | hvX₂)
    · exact (Set.disjoint_left.mp hY'disjVSN hvY') hvVSN
    · exact hvX₀.2 hvVSN
    · exact hv12 (Or.inl hvX₁)
    · exact hv12 (Or.inr hvX₂)

  obtain ⟨P, a, b, hP, haS, hbS, hPD, hPclean⟩ :=
    Workspace.ProofLemmas.NoMajorVerticesCleanPath.exists_clean_path
      (A := S b₁ b₂) (B := VSN \ S b₁ b₂)
      hDconn huD huS hvD ⟨hvVSN, hvCentral⟩
      (Set.disjoint_sdiff_right : Disjoint (S b₁ b₂) (VSN \ S b₁ b₂))
  have ha12 : a ∉ X₁ ∪ X₂ := by
    intro h
    apply hPD a (Workspace.ProofLemmas.PathBasics.head_mem hP.2.1)
    rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hb12 : b ∉ X₁ ∪ X₂ := by
    intro h
    apply hPD b (Workspace.ProofLemmas.PathBasics.getLast_mem hP.2.2)
    rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hpairNotLocal := hnotLocalPair a haS b hbS.1 hbS.2 ha12 hb12
  have hab : a ≠ b := fun h => hbS.2 (h ▸ haS)
  have habNonadj : ¬ G.Adj a b := by
    intro hadj
    have hEdges : s(b₁, b₂) ≠ s(c, d) := hedgeNe.symm
    obtain ⟨c', d', hc'd', hbStrip⟩ :=
      Workspace.ProofLemmas.StripSystemBasics.mem_stripSystemVertices_iff.mp hbS.1
    have hne' : s(b₁, b₂) ≠ s(c', d') := by
      intro heq
      have hset : S b₁ b₂ = S c' d' := by
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Workspace.ProofLemmas.StripSystemBasics.strip_symm hstrip hb₁b₂
      apply hbS.2
      rw [hset]
      exact hbStrip
    obtain ⟨w, -, -, haN, hbN⟩ :=
      (Workspace.ProofLemmas.StripSystemCrossAdjacency.adj_iff_of_ne_edges
        hstrip hb₁b₂ hc'd' hne' haS hbStrip).mp hadj
    exact hpairNotLocal (Or.inl ⟨w, by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact haN
      · exact hbN⟩)
  have hP3 : 3 ≤ P.length :=
    Workspace.ProofLemmas.MinimalConnectedIsPath.three_le_length_of_not_adj hP hab habNonadj
  let F : Set V := {z : V | z ∈ Workspace.Types.Core.SPGT.interior P}
  have hFconn : ConnectedSet G F := by
    simpa [F] using Workspace.ProofLemmas.MinimalConnectedIsPath.connectedSet_interior hP
  have hFsub : F ⊆ (VSN ∪ Y)ᶜ := by
    intro z hz
    have hzClean := hPclean z hz
    have hzD := hPD z (Workspace.ProofLemmas.PathBasics.interior_subset hz)
    change z ∉ VSN ∪ Y
    rintro (hzVS | hzY)
    · exact (hzClean.1 (by
        by_cases hzC : z ∈ S b₁ b₂
        · exact hzC
        · exact (hzClean.2 ⟨hzVS, hzC⟩).elim))
    · exact hzD (hYsubB hzY)
  have hfmem : P[1]'(by omega) ∈ F := by
    change P[1]'(by omega) ∈ Workspace.Types.Core.SPGT.interior P
    rw [Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP]
    refine ⟨List.getElem_mem _, ?_, ?_⟩
    · rw [← Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 (by omega)]
      exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
    · rw [← Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
      exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
  obtain ⟨C, hC, hfC⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G (VSN ∪ Y)ᶜ
      (hFsub hfmem)
  have hFC : F ⊆ C :=
    Workspace.Statements.S04.SPGT.Helpers42.subset_component hFconn hFsub hC hfmem hfC
  have haAtt : a ∈ attachments G C VSN := by
    refine ⟨Workspace.ProofLemmas.StripSystemBasics.strip_subset_vertices hb₁b₂ haS,
      P[1]'(by omega), hFC hfmem, ?_⟩
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 (show 0 + 1 < P.length by omega)
    rwa [Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 (by omega)] at h
  have hbInt : P[P.length - 2]'(by omega) ∈ F := by
    change P[P.length - 2]'(by omega) ∈ Workspace.Types.Core.SPGT.interior P
    rw [Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP]
    refine ⟨List.getElem_mem _, ?_, ?_⟩
    · rw [← Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 (by omega)]
      exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
    · rw [← Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
      exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
  have hbAtt : b ∈ attachments G C VSN := by
    refine ⟨hbS.1, P[P.length - 2]'(by omega), hFC hbInt, ?_⟩
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1
      (show (P.length - 2) + 1 < P.length by omega)
    have hidx : P.length - 2 + 1 = P.length - 1 := by omega
    have h' : G.Adj (P[P.length - 2]'(by omega)) (P[P.length - 1]'(by omega)) := by
      simpa only [hidx] using h
    rw [Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)] at h'
    exact h'.symm
  have hlocalC := hlocal C (by simpa [Y, VSN] using hC)
  exact hpairNotLocal (by
    rcases hlocalC with ⟨w, hw⟩ | ⟨c', d', hcd', hsub⟩
    · exact Or.inl ⟨w, fun z hz => by
        rcases hz with rfl | hz
        · exact hw haAtt
        · exact hw (hz ▸ hbAtt)⟩
    · exact Or.inr ⟨c', d', hcd', fun z hz => by
        rcases hz with rfl | hz
        · exact hsub haAtt
        · exact hsub (hz ▸ hbAtt)⟩)

end Workspace.ProofLemmas.NoMajorVerticesOutsideMaximalStripSystem
