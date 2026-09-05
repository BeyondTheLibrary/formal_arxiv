import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.ProofLemmas.StrongStaircaseVertexClassification
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm134StaircaseRegions

set_option autoImplicit false

/-!
# The region structure of the proof of 13.4

PAPER (§13, printed pp. 84–85): claim (1) of the proof of 13.4, and the sentence
that follows it — *"Let `M` be the union of all components of `H` with no
attachment in `V(S)`.  Then `M` is nonempty, since by (1) the component of `H`
containing the interior of `R₀` has no attachments in `V(S)`.  Let `D` be the
union of all the components of `H` that have an attachment in `V(S)`.  Hence
`V(G)` is partitioned into `A, B, C, D, A₀, B₀, N, M`, where possibly `C, D` or
`N` may be empty."*

The three genuinely non-bookkeeping steps — claim (1) itself, the fact that the
component carrying `R₀*` has no attachment in `V(S)`, and the fact (used in the
proof of claim (2)) that a component with no attachment in `V(S)` does attach to
both `A₀` and `B₀` — are `Workspace.ProofLemmas.Thm134StaircaseRegions`.  What is
proved here is the paper's *"Hence `V(G)` is partitioned into
`A, B, C, D, A₀, B₀, N, M`"*: the eight classes are pairwise disjoint and cover
`V(G)`.

The disjointnesses among `A, B, C, A₀, B₀, N` come from
`Workspace.ProofLemmas.StrongStaircaseVertexClassification`; `D` and `M` are
subsets of `H = H₀`, which by construction misses `V(S) ∪ A₀ ∪ B₀ ∪ N`; and `D`
and `M` are disjoint from each other because two components of `H₀` sharing a
vertex are equal, while one of them has an attachment in `V(S)` and the other
does not.  The covering uses that every vertex of `H₀` lies in a component of
`H₀` (`ComponentsOfSetBasics.exists_isComponent_mem`).
-/

namespace Workspace.ProofLemmas.StrongStaircaseComponentStructure

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions.SPGT

theorem strongStaircaseComponentStructure
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
    let M : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      attachments H F VS = ∅}
    let D : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      (attachments H F VS).Nonempty}
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F →
      (attachments H F (VS ∪ A₀ ∪ B₀) ∩ VS).Nonempty →
      attachments H F (VS ∪ A₀ ∪ B₀) ⊆ VS ∧
        (attachments H F (VS ∪ A₀ ∪ B₀) ∩ (A ∪ C)).Nonempty ∧
        (attachments H F (VS ∪ A₀ ∪ B₀) ∩ (B ∪ C)).Nonempty) ∧
    Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧ Disjoint A A₀ ∧ Disjoint A B₀ ∧
      Disjoint A N ∧ Disjoint A M ∧ Disjoint B C ∧ Disjoint B D ∧ Disjoint B A₀ ∧
      Disjoint B B₀ ∧ Disjoint B N ∧ Disjoint B M ∧ Disjoint C D ∧ Disjoint C A₀ ∧
      Disjoint C B₀ ∧ Disjoint C N ∧ Disjoint C M ∧ Disjoint D A₀ ∧ Disjoint D B₀ ∧
      Disjoint D N ∧ Disjoint D M ∧ Disjoint A₀ B₀ ∧ Disjoint A₀ N ∧ Disjoint A₀ M ∧
      Disjoint B₀ N ∧ Disjoint B₀ M ∧ Disjoint N M ∧
      A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M = Set.univ ∧
    ({v : V | v ∈ interior R₀}).Nonempty ∧ {v : V | v ∈ interior R₀} ⊆ M ∧ M.Nonempty ∧
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
      (attachments H F A₀).Nonempty ∧ (attachments H F B₀).Nonempty) ∧
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ D →
      attachments H F (A₀ ∪ B₀) = ∅ ∧
        (attachments H F (A ∪ C)).Nonempty ∧ (attachments H F (B ∪ C)).Nonempty) := by
  intro VS A₀ B₀ N H₀ M D
  -- the three printed sub-claims
  have hclaim1 := Thm134StaircaseRegions.componentAttachmentDichotomy H hBerge hK4 heven
    h1breaker h3breaker hskew A C B a₀ b₀ R₀ hstairs hodd
  have hInt := Thm134StaircaseRegions.interiorBanisterComponentHasNoStripAttachment H hBerge
    hK4 heven h1breaker h3breaker hskew A C B a₀ b₀ R₀ hstairs hodd
  have hStars := Thm134StaircaseRegions.middleComponentAttachesToBothStars H hBerge hK4
    heven h1breaker h3breaker hskew A C B a₀ b₀ R₀ hstairs hodd
  -- the classification of the previous paragraph
  have hcl := StrongStaircaseVertexClassification.strongStaircaseVertexClassification H
    hBerge hK4 heven h1breaker h3breaker A C B a₀ b₀ R₀ hstairs
  have hA₀B₀ : Disjoint A₀ B₀ := hcl.1.1
  have hA₀N : Disjoint A₀ N := hcl.1.2.1
  have hB₀N : Disjoint B₀ N := hcl.1.2.2
  have hA₀VS : Disjoint A₀ VS := hcl.2.1.1
  have hB₀VS : Disjoint B₀ VS := hcl.2.1.2.1
  have hNVS : Disjoint N VS := hcl.2.1.2.2
  have hclInt : {v : V | v ∈ interior R₀} ⊆ H₀ := hcl.2.2.2.2.2.2
  -- the staircase data
  have hsc : StepConnected H A C B := hstairs.1.1.1
  have hpath : IsPathFrom H R₀ a₀ b₀ := hstairs.1.1.2.1.1
  have hAB : Disjoint A B := hsc.1.1
  have hAC : Disjoint A C := hsc.1.2.1
  have hBC : Disjoint B C := hsc.1.2.2
  ---------------------------------------------------------------------------
  -- `H₀`, `M` and `D`
  ---------------------------------------------------------------------------
  have hH₀sub : ∀ v : V, v ∈ H₀ → v ∉ VS ∧ v ∉ A₀ ∧ v ∉ B₀ ∧ v ∉ N := by
    intro v hv
    exact ⟨fun h => hv.2 (Or.inl (Or.inl (Or.inl h))),
      fun h => hv.2 (Or.inl (Or.inl (Or.inr h))),
      fun h => hv.2 (Or.inl (Or.inr h)), fun h => hv.2 (Or.inr h)⟩
  have hMH₀ : ∀ v : V, v ∈ M → v ∈ H₀ := by
    intro v hv
    obtain ⟨F, hF, hvF, -⟩ :=
      (hv : ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧ attachments H F VS = ∅)
    exact hF.1 hvF
  have hDH₀ : ∀ v : V, v ∈ D → v ∈ H₀ := by
    intro v hv
    obtain ⟨F, hF, hvF, -⟩ :=
      (hv : ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧ (attachments H F VS).Nonempty)
    exact hF.1 hvF
  have hcompUnique : ∀ F F' : Set V, IsComponent H H₀ F → IsComponent H H₀ F' →
      ∀ v : V, v ∈ F → v ∈ F' → F = F' := by
    intro F F' hF hF' v hv hv'
    by_contra hne
    exact (Set.disjoint_left.mp
      (ComponentsOfSetBasics.disjoint_of_isComponent H hF hF' hne) hv) hv'
  have hMcomp : ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
      attachments H F VS = ∅ := by
    intro F hFne hF hFM
    obtain ⟨v, hv⟩ := hFne
    obtain ⟨F', hF', hvF', hatt⟩ :=
      (hFM hv : ∃ F' : Set V, IsComponent H H₀ F' ∧ v ∈ F' ∧ attachments H F' VS = ∅)
    rw [hcompUnique F F' hF hF' v hv hvF']
    exact hatt
  have hDcomp : ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ D →
      (attachments H F VS).Nonempty := by
    intro F hFne hF hFD
    obtain ⟨v, hv⟩ := hFne
    obtain ⟨F', hF', hvF', hatt⟩ :=
      (hFD hv : ∃ F' : Set V, IsComponent H H₀ F' ∧ v ∈ F' ∧ (attachments H F' VS).Nonempty)
    rw [hcompUnique F F' hF hF' v hv hvF']
    exact hatt
  ---------------------------------------------------------------------------
  -- membership helpers
  ---------------------------------------------------------------------------
  have hinA : ∀ v : V, v ∈ A → v ∈ VS := fun v h => Or.inl (Or.inl h)
  have hinB : ∀ v : V, v ∈ B → v ∈ VS := fun v h => Or.inl (Or.inr h)
  have hinC : ∀ v : V, v ∈ C → v ∈ VS := fun v h => Or.inr h
  have hA₀nVS : ∀ v : V, v ∈ A₀ → v ∉ VS := fun v h => Set.disjoint_left.mp hA₀VS h
  have hB₀nVS : ∀ v : V, v ∈ B₀ → v ∉ VS := fun v h => Set.disjoint_left.mp hB₀VS h
  have hNnVS : ∀ v : V, v ∈ N → v ∉ VS := fun v h => Set.disjoint_left.mp hNVS h
  ---------------------------------------------------------------------------
  -- the eight classes cover `V(G)`
  ---------------------------------------------------------------------------
  have huniv : A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    simp only [Set.mem_union]
    by_cases h1 : v ∈ A
    · tauto
    by_cases h2 : v ∈ B
    · tauto
    by_cases h3 : v ∈ C
    · tauto
    by_cases h4 : v ∈ A₀
    · tauto
    by_cases h5 : v ∈ B₀
    · tauto
    by_cases h6 : v ∈ N
    · tauto
    have hvVS : v ∉ VS := by
      rintro ((h | h) | h)
      · exact h1 h
      · exact h2 h
      · exact h3 h
    have hvH₀ : v ∈ H₀ := by
      refine ⟨trivial, ?_⟩
      rintro (((h | h) | h) | h)
      · exact hvVS h
      · exact h4 h
      · exact h5 h
      · exact h6 h
    obtain ⟨F, hF, hvF⟩ := ComponentsOfSetBasics.exists_isComponent_mem H H₀ hvH₀
    by_cases hatt : (attachments H F VS).Nonempty
    · have hvD : v ∈ D := ⟨F, hF, hvF, hatt⟩
      tauto
    · rw [Set.not_nonempty_iff_eq_empty] at hatt
      have hvM : v ∈ M := ⟨F, hF, hvF, hatt⟩
      tauto
  ---------------------------------------------------------------------------
  -- the interior of the banister
  ---------------------------------------------------------------------------
  have hlen3 : 3 ≤ R₀.length := by
    have h3 : 3 ≤ pathLength R₀ := hstairs.1.1.2.2
    have hl := PathBasics.length_eq_pathLength_add_one hpath.1
    omega
  have hposi : 0 < (interior R₀).length := by
    have hIL := PathBasics.interior_length R₀
    omega
  have hintNe : ({v : V | v ∈ interior R₀}).Nonempty :=
    ⟨(interior R₀)[0]'hposi, List.getElem_mem hposi⟩
  have hintM : {v : V | v ∈ interior R₀} ⊆ M := by
    intro v hv
    obtain ⟨F, hF, hvF⟩ := ComponentsOfSetBasics.exists_isComponent_mem H H₀ (hclInt hv)
    exact ⟨F, hF, hvF, hInt F hF ⟨v, hv, hvF⟩⟩
  have hMne : M.Nonempty := by
    obtain ⟨w, hw⟩ := hintNe
    exact ⟨w, hintM hw⟩
  ---------------------------------------------------------------------------
  -- the two component clauses
  ---------------------------------------------------------------------------
  have hdpart : ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
      (attachments H F A₀).Nonempty ∧ (attachments H F B₀).Nonempty :=
    fun F hFne hF hFM => hStars F hFne hF (hMcomp F hFne hF hFM)
  have hepart : ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ D →
      attachments H F (A₀ ∪ B₀) = ∅ ∧
        (attachments H F (A ∪ C)).Nonempty ∧ (attachments H F (B ∪ C)).Nonempty := by
    intro F hFne hF hFD
    obtain ⟨w, hwVS, hwn⟩ := hDcomp F hFne hF hFD
    have hmeet : (attachments H F (VS ∪ A₀ ∪ B₀) ∩ VS).Nonempty :=
      ⟨w, ⟨Or.inl (Or.inl hwVS), hwn⟩, hwVS⟩
    obtain ⟨hsub, hac, hbc⟩ := hclaim1 F hFne hF hmeet
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxin : x ∈ VS ∪ A₀ ∪ B₀ := by
        rcases hx.1 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      have hxVS : x ∈ VS := hsub ⟨hxin, hx.2⟩
      rcases hx.1 with h | h
      · exact hA₀nVS x h hxVS
      · exact hB₀nVS x h hxVS
    · obtain ⟨x, hx1, hx2⟩ := hac
      exact ⟨x, hx2, hx1.2⟩
    · obtain ⟨x, hx1, hx2⟩ := hbc
      exact ⟨x, hx2, hx1.2⟩
  ---------------------------------------------------------------------------
  -- assembling
  ---------------------------------------------------------------------------
  refine ⟨hclaim1, hAB, hAC, ?_, ?_, ?_, ?_, ?_, hBC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hA₀B₀, hA₀N, ?_, hB₀N, ?_, ?_, huniv, hintNe, hintM, hMne,
    hdpart, hepart⟩
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv')).1 (hinA v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hA₀nVS v hv' (hinA v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hB₀nVS v hv' (hinA v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hNnVS v hv' (hinA v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).1 (hinA v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv')).1 (hinB v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hA₀nVS v hv' (hinB v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hB₀nVS v hv' (hinB v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hNnVS v hv' (hinB v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).1 (hinB v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv')).1 (hinC v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hA₀nVS v hv' (hinC v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hB₀nVS v hv' (hinC v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => hNnVS v hv' (hinC v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).1 (hinC v hv)
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv)).2.1 hv'
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv)).2.2.1 hv'
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hDH₀ v hv)).2.2.2 hv'
  · -- `D` and `M` are disjoint
    refine Set.disjoint_left.mpr ?_
    intro v hvD hvM
    obtain ⟨F, hF, hvF, hatt⟩ :=
      (hvD : ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧ (attachments H F VS).Nonempty)
    obtain ⟨F', hF', hvF', hatt'⟩ :=
      (hvM : ∃ F' : Set V, IsComponent H H₀ F' ∧ v ∈ F' ∧ attachments H F' VS = ∅)
    rw [hcompUnique F F' hF hF' v hvF hvF'] at hatt
    obtain ⟨x, hx⟩ := hatt
    rw [hatt'] at hx
    exact hx
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).2.1 hv
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).2.2.1 hv
  · exact Set.disjoint_left.mpr fun v hv hv' => (hH₀sub v (hMH₀ v hv')).2.2.2 hv

end Workspace.ProofLemmas.StrongStaircaseComponentStructure
