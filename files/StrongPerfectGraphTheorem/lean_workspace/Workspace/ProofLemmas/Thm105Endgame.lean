import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Statements.S04.Thm_4_2
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm105Claim1
import Workspace.ProofLemmas.Thm105Separation
import Workspace.ProofLemmas.Thm105Setup

/-!
# Endgame of the proof of 10.5

Claim (1) separates the interior of the selected first rung from the other
two rungs after deleting the future cutset.  The resulting skew partition is
loose: one of the other two vertices of the first triangle is `Y`-complete.
The conclusion then follows from 4.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm105Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.ProofLemmas.Thm105Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The last two paragraphs of the proof of 10.5, after the first rung has
been selected with both ends `Y`-complete. -/
theorem endgame (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (Y : Set V)
    (hprism : IsEvenPrism G a b (R 0) (R 1) (R 2))
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G a b y)
    (hYmax : ∀ Z : Set V, Y ⊆ Z → AnticonnectedSet G Z →
      (∀ z ∈ Z, MajorForPrism G a b z) → Z = Y)
    (hmin : ∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
      GoodChoice G a' b' R' Y' →
        triangleCompleteCount G a b Y ≤ triangleCompleteCount G a' b' Y')
    (hsat : SaturatesPrism a b {x : V | VertexComplete G x Y})
    (ha₀complete : VertexComplete G (a 0) Y)
    (hb₀complete : VertexComplete G (b 0) Y) :
    AdmitsBalancedSkewPartition G := by
  classical
  let K : Set V := {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2}
  let X : Set V := {x : V | VertexComplete G x Y}
  let X₀ : Set V := X \ K
  let X₁ : Set V := {a 0, b 0}
  let Z : Set V := (X₀ ∪ X₁) ∪ Y
  let S : Set V := {x : V | x ∈ SPGT.interior (R 0)}
  let T : Set V := {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2}
  have hform := hprism.1
  have hpath : ∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i) := fun i ↦
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform i
  have hRmemK : ∀ i : Fin 3, ∀ x ∈ R i, x ∈ K := by
    intro i x hx
    change x ∈ {z : V | z ∈ R 0} ∪ {z : V | z ∈ R 1} ∪ {z : V | z ∈ R 2}
    fin_cases i
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hYK : ∀ y ∈ Y, y ∉ K := by
    intro y hy
    exact Workspace.ProofLemmas.Thm105Setup.major_not_mem_evenPrism
      G a b R hprism y (hYmajor y hy)
  have hSsubK : S ⊆ K := by
    intro x hx
    exact hRmemK 0 x (Workspace.ProofLemmas.PathBasics.interior_subset hx)
  have hTsubK : T ⊆ K := by
    rintro x (hx | hx)
    · exact hRmemK 1 x hx
    · exact hRmemK 2 x hx
  have hSZ : ∀ x ∈ S, x ∉ Z := by
    intro x hxS
    have hxR := Workspace.ProofLemmas.PathBasics.interior_subset hxS
    have hxends := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom (hpath 0)).1 hxS
    rintro ((hxX₀ | hxX₁) | hxY)
    · exact hxX₀.2 (hSsubK hxS)
    · rcases hxX₁ with h | h
      · exact hxends.2.1 h
      · exact hxends.2.2 h
    · exact hYK x hxY (hSsubK hxS)
  have hTZ : ∀ x ∈ T, x ∉ Z := by
    intro x hxT
    rintro ((hxX₀ | hxX₁) | hxY)
    · exact hxX₀.2 (hTsubK hxT)
    · have hxR₀ : x ∈ R 0 := by
        rcases hxX₁ with h | h
        · exact h ▸ Workspace.ProofLemmas.PathBasics.head_mem (hpath 0).2.1
        · exact h ▸ Workspace.ProofLemmas.PathBasics.getLast_mem (hpath 0).2.2
      rcases hxT with hxR₁ | hxR₂
      · exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
          (i := 1) (j := 0) (by decide) x hxR₁ hxR₀
      · exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
          (i := 2) (j := 0) (by decide) x hxR₂ hxR₀
    · exact hYK x hxY (hTsubK hxT)
  have hKZ : K \ Z = S ∪ T := by
    ext x
    constructor
    · rintro ⟨hxK, hxZ⟩
      change x ∈ ({z : V | z ∈ R 0} ∪ {z : V | z ∈ R 1}) ∪
        {z : V | z ∈ R 2} at hxK
      rcases hxK with (hxR₀ | hxR₁) | hxR₂
      · have hxa : x ≠ a 0 := fun h ↦ hxZ (Or.inl (Or.inr (Or.inl h)))
        have hxb : x ≠ b 0 := fun h ↦ hxZ (Or.inl (Or.inr (Or.inr h)))
        exact Or.inl ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom
          (hpath 0)).2 ⟨hxR₀, hxa, hxb⟩)
      · exact Or.inr (Or.inl hxR₁)
      · exact Or.inr (Or.inr hxR₂)
    · rintro (hxS | hxT)
      · exact ⟨hSsubK hxS, hSZ x hxS⟩
      · exact ⟨hTsubK hxT, hTZ x hxT⟩
  have hSTdisj : Disjoint S T := by
    refine Set.disjoint_left.2 ?_
    intro x hxS hxT
    have hxR₀ := Workspace.ProofLemmas.PathBasics.interior_subset hxS
    rcases hxT with hxR₁ | hxR₂
    · exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
        (i := 0) (j := 1) (by decide) x hxR₀ hxR₁
    · exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
        (i := 0) (j := 2) (by decide) x hxR₀ hxR₂
  have hSTanti : Anticomplete G S T := by
    intro x hxS y hyT hxy
    have hx := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom (hpath 0)).1 hxS
    rcases hyT with hyR₁ | hyR₂
    · rcases (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform
          (i := 0) (j := 1) (by decide) x hx.1 y hyR₁).mp hxy with h | h
      · exact hx.2.1 h.1
      · exact hx.2.2 h.1
    · rcases (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform
          (i := 0) (j := 2) (by decide) x hx.1 y hyR₂).mp hxy with h | h
      · exact hx.2.1 h.1
      · exact hx.2.2 h.1
  have hno : ∀ C : Set V, IsComponent G (K ∪ Z)ᶜ C →
      (∃ s ∈ S, ∃ c ∈ C, G.Adj s c) →
      (∃ t ∈ T, ∃ c ∈ C, G.Adj t c) → False := by
    intro C hC hleft hright
    exact Workspace.ProofLemmas.Thm105Claim1.no_component_attaches_both
      G hG hK4 a b R Y K hprism rfl hYne hYanti hYmajor hYmax hmin
      ha₀complete hb₀complete C hC hleft hright
  obtain ⟨L, M, hLM, hLMdisj, hLManti, hSL, hTM⟩ :=
    Workspace.ProofLemmas.Thm105Separation.separate G K Z S T hKZ hSZ hTZ
      hSTdisj hSTanti hno
  have hlen₀ : 2 ≤ pathLength (R 0) := by
    have hlist := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hform 0
    have hpos : 1 ≤ pathLength (R 0) := by simp only [pathLength]; omega
    obtain ⟨m, hm⟩ := hprism.2.1
    omega
  have hlenList₀ : 3 ≤ (R 0).length := by simp only [pathLength] at hlen₀; omega
  have hSne : S.Nonempty := by
    let s := (R 0)[1]'(by omega)
    exact ⟨s, Workspace.ProofLemmas.PathBasics.getElem_mem_interior (hpath 0).1
      (k := 1) (by omega) (by omega) (by omega)⟩
  have hTne : T.Nonempty := by
    exact ⟨a 1, Or.inl (Workspace.ProofLemmas.PathBasics.head_mem (hpath 1).2.1)⟩
  have hLne : L.Nonempty := hSne.mono hSL
  have hMne : M.Nonempty := hTne.mono hTM
  have hPcomplete : ∀ x ∈ X₀ ∪ X₁, VertexComplete G x Y := by
    intro x hx
    rcases hx with hx₀ | hx₁
    · exact hx₀.1
    · change x ∈ ({a 0, b 0} : Set V) at hx₁
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx₁
      rcases hx₁ with rfl | rfl
      · exact ha₀complete
      · exact hb₀complete
  have hPYdisj : Disjoint (X₀ ∪ X₁) Y := by
    refine Set.disjoint_left.2 ?_
    intro x hxP hxY
    exact G.irrefl (hPcomplete x hxP x hxY)
  have hPYanti : Anticomplete Gᶜ (X₀ ∪ X₁) Y := by
    intro x hxP y hyY hxy
    exact ((SimpleGraph.compl_adj G x y).mp hxy).2 (hPcomplete x hxP y hyY)
  have hPne : (X₀ ∪ X₁).Nonempty := ⟨a 0, Or.inr (Or.inl rfl)⟩
  have hskew : IsSkewPartition G (L ∪ M) Z := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hLM]
      exact Set.compl_union_self Z
    · rw [hLM]
      exact disjoint_compl_left
    · exact Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
        rfl hLne hMne hLMdisj hLManti
    · exact Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
        rfl hPne hYne hPYdisj hPYanti
  have hYcomponent : IsAnticomponent G Z Y := by
    refine ⟨Set.subset_union_right, hYanti, ?_⟩
    intro D hYD hDZ hDanti
    obtain ⟨y, hyY⟩ := hYne
    have hDsub : D ⊆ Y ∪ (X₀ ∪ X₁) := by
      intro x hxD
      rcases hDZ hxD with hxP | hxY
      · exact Or.inr hxP
      · exact Or.inl hxY
    have hYPanti : Anticomplete Gᶜ Y (X₀ ∪ X₁) := by
      intro u hu v hv huv
      exact hPYanti v hv u hu huv.symm
    have hDY : D ⊆ Y :=
      Workspace.ProofLemmas.StripSystemNeighbourhood.connectedSet_subset_of_anticomplete
        hYPanti hDanti hDsub (hYD hyY) hyY
    exact Set.Subset.antisymm hDY hYD
  have hotherComplete :
      (a 1 ∈ X ∧ a 1 ∈ T) ∨ (a 2 ∈ X ∧ a 2 ∈ T) := by
    by_contra hnone
    push Not at hnone
    have ha₁not : a 1 ∉ X := fun h ↦ hnone.1 h
      (Or.inl (Workspace.ProofLemmas.PathBasics.head_mem (hpath 1).2.1))
    have ha₂not : a 2 ∉ X := fun h ↦ hnone.2 h
      (Or.inr (Workspace.ProofLemmas.PathBasics.head_mem (hpath 2).2.1))
    have hsub : ({a 0, a 1, a 2} : Set V) ∩ X ⊆ {a 0} := by
      rintro x ⟨hx, hxX⟩
      rcases hx with h | h | h
      · exact h
      · exact False.elim (ha₁not (h ▸ hxX))
      · exact False.elim (ha₂not (h ▸ hxX))
    have hle : (({a 0, a 1, a 2} : Set V) ∩ X).ncard ≤ 1 := by
      calc
        _ ≤ ({a 0} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    exact (by omega : ¬ (2 ≤ (({a 0, a 1, a 2} : Set V) ∩ X).ncard)) hsat.1
  obtain ⟨x, hxX, hxT⟩ : ∃ x : V, x ∈ X ∧ x ∈ T := by
    rcases hotherComplete with h | h
    · exact ⟨a 1, h⟩
    · exact ⟨a 2, h⟩
  have hxM : x ∈ M := hTM hxT
  have hloose : IsLooseSkewPartition G (L ∪ M) Z :=
    ⟨hskew, Or.inr ⟨x, Or.inr hxM, Y, hYcomponent, hxX⟩⟩
  exact Workspace.Statements.S04.SPGT.thm_4_2 G hG ⟨L ∪ M, Z, hloose⟩

end Workspace.ProofLemmas.Thm105Endgame
