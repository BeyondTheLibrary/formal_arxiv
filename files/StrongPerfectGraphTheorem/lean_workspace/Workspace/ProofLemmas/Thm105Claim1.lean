import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Statements.S10.Thm_10_3
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm105Replacement
import Workspace.ProofLemmas.Thm105Setup

/-!
# Claim (1) in the proof of 10.5

The component form used here is enough for the separation step.  A component
outside the prism and the future cutset cannot attach both to the interior of
the first rung and to either of the other two rungs.  Otherwise 10.3 supplies
the path used by the rung-replacement contradiction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm105Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm105Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim (1), restricted to a component outside `K ∪ Z`, which is the form
needed to build the two sides of the skew partition. -/
theorem no_component_attaches_both (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (Y K : Set V)
    (hprism : IsEvenPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2})
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G a b y)
    (hYmax : ∀ Z : Set V, Y ⊆ Z → AnticonnectedSet G Z →
      (∀ z ∈ Z, MajorForPrism G a b z) → Z = Y)
    (hmin : ∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
      GoodChoice G a' b' R' Y' →
        triangleCompleteCount G a b Y ≤ triangleCompleteCount G a' b' Y')
    (ha₀complete : VertexComplete G (a 0) Y)
    (hb₀complete : VertexComplete G (b 0) Y)
    (C : Set V)
    (hC : IsComponent G
      (K ∪ ((({x : V | VertexComplete G x Y} \ K) ∪ {a 0, b 0}) ∪ Y))ᶜ C)
    (hleft : ∃ s ∈ SPGT.interior (R 0), ∃ c ∈ C, G.Adj s c)
    (hright : ∃ t ∈ ({x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2}),
      ∃ c ∈ C, G.Adj t c) : False := by
  classical
  have hform := hprism.1
  have hpath : ∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i) := fun i ↦
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform i
  have hRmemK : ∀ i : Fin 3, ∀ x ∈ R i, x ∈ K := by
    intro i x hx
    rw [hK]
    fin_cases i
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hCK : C ⊆ Kᶜ := by
    intro x hx hxK
    exact hC.1 hx (Or.inl hxK)
  have hCZ : ∀ x ∈ C,
      x ∉ (({z : V | VertexComplete G z Y} \ K) ∪ {a 0, b 0}) ∪ Y := by
    intro x hx hxZ
    exact hC.1 hx (Or.inr hxZ)
  have hCmajor : ∀ x ∈ C, ¬ MajorForPrism G a b x := by
    intro x hx hxmajor
    have hxnotcomplete : ¬ VertexComplete G x Y := by
      intro hxcomplete
      exact hCZ x hx (Or.inl (Or.inl ⟨hxcomplete, hCK hx⟩))
    have hanti : AnticonnectedSet G (Y ∪ {x}) :=
      Workspace.ProofLemmas.KiteTailBasics.anticonnectedSet_union_singleton hYanti hxnotcomplete
    have hmajor : ∀ z ∈ Y ∪ {x}, MajorForPrism G a b z := by
      intro z hz
      rcases hz with hzY | hzX
      · exact hYmajor z hzY
      · have hzx : z = x := by simpa using hzX
        simpa [hzx] using hxmajor
    have heq := hYmax (Y ∪ {x}) Set.subset_union_left hanti hmajor
    have hxY : x ∈ Y := by
      rw [← heq]
      exact Or.inr rfl
    exact hCZ x hx (Or.inr hxY)
  obtain ⟨x₁, hx₁int, c₁, hc₁C, hx₁c₁⟩ := hleft
  obtain ⟨x₂, hx₂right, c₂, hc₂C, hx₂c₂⟩ := hright
  have hx₁R₀ : x₁ ∈ R 0 := Workspace.ProofLemmas.PathBasics.interior_subset hx₁int
  have hx₁att : IsAttachment G C K x₁ :=
    ⟨hRmemK 0 x₁ hx₁R₀, c₁, hc₁C, hx₁c₁⟩
  have hx₂data : (∃ i : Fin 3, i ≠ 0 ∧ x₂ ∈ R i) := by
    rcases hx₂right with hx | hx
    · exact ⟨1, by decide, hx⟩
    · exact ⟨2, by decide, hx⟩
  obtain ⟨i, hi0, hx₂Ri⟩ := hx₂data
  have hx₂K : x₂ ∈ K := hRmemK i x₂ hx₂Ri
  have hx₂notR₀ : x₂ ∉ R 0 := by
    intro hx₂R₀
    exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform hi0
      x₂ hx₂Ri hx₂R₀
  have hx₂att : IsAttachment G C K x₂ :=
    ⟨hx₂K, c₂, hc₂C, hx₂c₂⟩
  obtain ⟨f, f₁, fₙ, hf, hfC, hcase⟩ :=
    Workspace.Statements.S10.SPGT.thm_10_3 G hG hK4 a b R K C hform hK hCK hC.2.1
      hCmajor x₁ x₂ hx₁att hx₁int hx₂att hx₂notR₀
  have hfK : ∀ x ∈ f, x ∉ K := fun x hx ↦ hCK (hfC x hx)
  have hf₁C : f₁ ∈ C := hfC f₁ (Workspace.ProofLemmas.PathBasics.head_mem hf.2.1)
  have hf₁not : ¬ VertexComplete G f₁ Y := by
    intro hcomplete
    exact hCZ f₁ hf₁C (Or.inl (Or.inl ⟨hcomplete, hCK hf₁C⟩))
  rcases hcase with hcaseA | hcaseB
  · exact Workspace.ProofLemmas.Thm105Replacement.replacement_contradiction_left
      G hG a b R Y K hprism hK hYne hYanti hYmajor hmin ha₀complete
      f f₁ fₙ hf hfK hf₁not hcaseA.1 hcaseA.2.1 hcaseA.2.2.1 hcaseA.2.2.2
  · let Rrev : Fin 3 → List V := fun i ↦ (R i).reverse
    have hswapForm : FormPrism G b a (Rrev 0) (Rrev 1) (Rrev 2) :=
      Workspace.ProofLemmas.PrismSymmetry.formPrism_swap hform
    have hswapPrism : IsEvenPrism G b a (Rrev 0) (Rrev 1) (Rrev 2) := by
      refine ⟨hswapForm, ?_, ?_, ?_⟩
      · simpa [Rrev, pathLength] using hprism.2.1
      · simpa [Rrev, pathLength] using hprism.2.2.1
      · simpa [Rrev, pathLength] using hprism.2.2.2
    have hKrev : K = {x : V | x ∈ Rrev 0} ∪ {x : V | x ∈ Rrev 1} ∪
        {x : V | x ∈ Rrev 2} := by
      simpa [Rrev] using hK
    have hYmajorSwap : ∀ y ∈ Y, MajorForPrism G b a y := by
      intro y hy
      exact (Workspace.ProofLemmas.PrismSymmetry.majorForPrism_swap).2 (hYmajor y hy)
    have hminSwap : ∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
        GoodChoice G a' b' R' Y' →
          triangleCompleteCount G b a Y ≤ triangleCompleteCount G a' b' Y' := by
      intro a' b' R' Y' hgood
      rw [triangleCompleteCount_swap G a b Y]
      exact hmin a' b' R' Y' hgood
    have hySwap : ∃ y ∈ Rrev 0, y ≠ b 0 ∧ G.Adj fₙ y := by
      obtain ⟨y, hyR, hyb, hfy⟩ := hcaseB.2.2.1
      exact ⟨y, by simpa [Rrev] using hyR, hyb, hfy⟩
    have hotherSwap : ∀ x ∈ f, ∀ k ∈ K, k ≠ b 0 → G.Adj x k →
        (x = f₁ ∧ (k = b 1 ∨ k = b 2)) ∨ (x = fₙ ∧ k ∈ Rrev 0) := by
      intro x hx k hk hkb hxk
      rcases hcaseB.2.2.2 x hx k hk hkb hxk with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by simpa [Rrev] using h.2⟩
    exact Workspace.ProofLemmas.Thm105Replacement.replacement_contradiction_left
      G hG b a Rrev Y K hswapPrism hKrev hYne hYanti hYmajorSwap hminSwap hb₀complete
      f f₁ fₙ hf hfK hf₁not hcaseB.1 hcaseB.2.1 hySwap hotherSwap

end Workspace.ProofLemmas.Thm105Claim1
