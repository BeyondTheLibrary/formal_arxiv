import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Classes
import Workspace.ProofLemmas.NoPathMeetsThreeCatchNeighborSets
import Workspace.ProofLemmas.Thm244Trichotomy
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.Types.MinimalCatchHasUniqueTriangleNeighbors

open Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Classes.SPGT

theorem minimalCatchHasUniqueTriangleNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF7 G) (A F : Set V)
    (a₁ a₂ a₃ : V)
    (hA : IsTriangle G A) (hAeq : A = {a₁, a₂, a₃})
    (hadist : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hcatch : Catches G F A)
    (hatMostOne : ∀ f ∈ F, ¬ 2 ≤ (G.neighborSet f ∩ A).ncard)
    (hmin : ∀ S : Set V, S ⊆ F → Catches G S A → F.ncard ≤ S.ncard) :
    ∃ b₁ b₂ b₃ : V,
      b₁ ∈ F ∧ b₂ ∈ F ∧ b₃ ∈ F ∧
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧
      (∀ f ∈ F,
        (G.Adj a₁ f ↔ f = b₁) ∧
        (G.Adj a₂ f ↔ f = b₂) ∧
        (G.Adj a₃ f ↔ f = b₃)) ∧
      (∀ S : Set V, S ⊆ F →
        (Catches G S A ↔ ConnectedSet G S ∧ b₁ ∈ S ∧ b₂ ∈ S ∧ b₃ ∈ S)) ∧
      (∀ S : Set V, S ⊆ F → ConnectedSet G S →
        b₁ ∈ S → b₂ ∈ S → b₃ ∈ S → S = F) ∧
      ¬ ∃ P : List V,
        IsPathList G P ∧
        (∀ x ∈ P, x ∈ F) ∧
        b₁ ∈ P ∧ b₂ ∈ P ∧ b₃ ∈ P := by
  classical
  let a : Fin 3 → V := ![a₁, a₂, a₃]
  let N : Fin 3 → Set V := fun i => {w | G.Adj (a i) w}
  have haA : ∀ i : Fin 3, a i ∈ A := by
    intro i
    fin_cases i <;> simp [a, hAeq]
  have hainj : Function.Injective a := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [a, hadist.1, hadist.2.1, hadist.2.2,
        Ne.symm hadist.1, Ne.symm hadist.2.1, Ne.symm hadist.2.2]
  have hmeet : ∀ i : Fin 3, ∃ f ∈ F, f ∈ N i := by
    intro i
    obtain ⟨f, hfF, hfadj⟩ := hcatch.2.2.2 (a i) (haA i)
    exact ⟨f, hfF, hfadj⟩
  have hsep : ∀ w ∈ F, ∀ i j : Fin 3, i ≠ j → ¬ (w ∈ N i ∧ w ∈ N j) := by
    intro w hwF i j hij hwij
    apply hatMostOne w hwF
    have haij : a i ≠ a j := fun h => hij (hainj h)
    have hsub : ({a i, a j} : Set V) ⊆ G.neighborSet w ∩ A := by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact ⟨hwij.1.symm, haA i⟩
      · exact ⟨hwij.2.symm, haA j⟩
    calc
      2 = ({a i, a j} : Set V).ncard := by simp [haij]
      _ ≤ (G.neighborSet w ∩ A).ncard := Set.ncard_le_ncard hsub
  have hminN : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ f ∈ S, f ∈ N i) → F.ncard ≤ S.ncard := by
    intro S hSF hSconn hSmeet
    apply hmin S hSF
    refine ⟨hA, hSconn, hcatch.2.2.1.mono hSF Set.Subset.rfl, ?_⟩
    intro x hxA
    rw [hAeq] at hxA
    rcases hxA with (rfl | rfl | rfl)
    · simpa [N, a] using hSmeet (0 : Fin 3)
    · simpa [N, a] using hSmeet (1 : Fin 3)
    · simpa [N, a] using hSmeet (2 : Fin 3)
  have hforbid :=
    Workspace.Types.NoPathMeetsThreeCatchNeighborSets.noPathMeetsThreeCatchNeighborSets
      G hG A F a₁ a₂ a₃ hA hAeq hadist hcatch hatMostOne
  have huniqueData : ∃ v : Fin 3 → V,
      (∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i) ∧
      (∀ i j : Fin 3, i ≠ j → v i ≠ v j) ∧
      (∀ i : Fin 3, ∀ w ∈ F, w ∈ N i → w = v i) := by
    rcases Workspace.Types.Thm244Trichotomy.minimalConnectedThreeTerminal
        G F N hcatch.2.1 hmeet hsep hminN with hspider | hlegs | hthrough
    · obtain ⟨v, u, P, hshape⟩ := hspider
      have hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i := by
        intro i
        refine ⟨hshape.2.2.2.2.1 i (v i) ?_, hshape.1 i⟩
        exact (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem
          (hshape.2.2.2.1 i)).1
      refine ⟨v, hv, ?_, hshape.2.1⟩
      intro i j hij
      exact fun hvij => hsep (v i) (hv i).1 i j hij ⟨(hv i).2, hvij ▸ (hv j).2⟩
    · obtain ⟨v, u, P, hshape⟩ := hlegs
      have hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i := by
        intro i
        refine ⟨hshape.2.2.2.1 i (v i) ?_, hshape.1 i⟩
        exact (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem
          (hshape.2.2.1 i)).1
      refine ⟨v, hv, ?_, hshape.2.1⟩
      intro i j hij
      exact fun hvij => hsep (v i) (hv i).1 i j hij ⟨(hv i).2, hvij ▸ (hv j).2⟩
    · obtain ⟨i, j, k, P, x, y, hshape⟩ := hthrough
      rcases hshape with ⟨hij, hik, hjk, hP, hPF, hxN, hyN,
        huniqI, huniqJ, z, hzP, hzN⟩
      exfalso
      apply hforbid
      have hends := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP
      have hPmeet : ∀ r : Fin 3, ∃ w ∈ P, w ∈ F ∧ w ∈ N r := by
        intro r
        have hr : r = i ∨ r = j ∨ r = k := by
          have hall : ({i, j, k} : Set (Fin 3)) = Set.univ := by
            apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
            simp [hij, hik, hjk]
          have hrmem : r ∈ ({i, j, k} : Set (Fin 3)) := by
            rw [hall]
            trivial
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hrmem
        rcases hr with rfl | rfl | rfl
        · exact ⟨x, hends.1, hPF x hends.1, hxN⟩
        · exact ⟨y, hends.2, hPF y hends.2, hyN⟩
        · exact ⟨z, hzP, hPF z hzP, hzN⟩
      refine ⟨P, hP.1, hPF, ?_, ?_, ?_⟩
      · simpa [N, a] using hPmeet (0 : Fin 3)
      · simpa [N, a] using hPmeet (1 : Fin 3)
      · simpa [N, a] using hPmeet (2 : Fin 3)
  obtain ⟨v, hv, hpair, hunique⟩ := huniqueData
  have hadj : ∀ i : Fin 3, ∀ w ∈ F, (G.Adj (a i) w ↔ w = v i) := by
    intro i w hwF
    constructor
    · exact hunique i w hwF
    · rintro rfl
      exact (hv i).2
  have hcatchIff : ∀ S : Set V, S ⊆ F →
      (Catches G S A ↔ ConnectedSet G S ∧ ∀ i : Fin 3, v i ∈ S) := by
    intro S hSF
    constructor
    · intro hS
      refine ⟨hS.2.1, ?_⟩
      intro i
      obtain ⟨w, hwS, hwadj⟩ := hS.2.2.2 (a i) (haA i)
      have hwv := (hadj i w (hSF hwS)).mp hwadj
      simpa [hwv] using hwS
    · rintro ⟨hSconn, hvS⟩
      refine ⟨hA, hSconn, hcatch.2.2.1.mono hSF Set.Subset.rfl, ?_⟩
      intro x hxA
      rw [hAeq] at hxA
      rcases hxA with (rfl | rfl | rfl)
      · exact ⟨v 0, hvS 0, by simpa [a] using (hv 0).2⟩
      · exact ⟨v 1, hvS 1, by simpa [a] using (hv 1).2⟩
      · exact ⟨v 2, hvS 2, by simpa [a] using (hv 2).2⟩
  refine ⟨v 0, v 1, v 2, (hv 0).1, (hv 1).1, (hv 2).1,
    hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide), ?_, ?_, ?_, ?_⟩
  · intro w hwF
    exact ⟨by simpa [a] using hadj 0 w hwF,
      by simpa [a] using hadj 1 w hwF,
      by simpa [a] using hadj 2 w hwF⟩
  · intro S hSF
    rw [hcatchIff S hSF]
    constructor
    · rintro ⟨hconn, hvS⟩
      exact ⟨hconn, hvS 0, hvS 1, hvS 2⟩
    · rintro ⟨hconn, hv0, hv1, hv2⟩
      refine ⟨hconn, ?_⟩
      intro i
      fin_cases i <;> assumption
  · intro S hSF hSconn hv0 hv1 hv2
    apply Set.eq_of_subset_of_ncard_le hSF
    apply hmin S hSF
    apply (hcatchIff S hSF).2
    refine ⟨hSconn, ?_⟩
    intro i
    fin_cases i <;> assumption
  · rintro ⟨P, hP, hPF, hv0P, hv1P, hv2P⟩
    apply hforbid
    refine ⟨P, hP, hPF, ?_, ?_, ?_⟩
    · exact ⟨v 0, hv0P, (hv 0).1, by simpa [N, a] using (hv 0).2⟩
    · exact ⟨v 1, hv1P, (hv 1).1, by simpa [N, a] using (hv 1).2⟩
    · exact ⟨v 2, hv2P, (hv 2).1, by simpa [N, a] using (hv 2).2⟩

end Workspace.Types.MinimalCatchHasUniqueTriangleNeighbors
