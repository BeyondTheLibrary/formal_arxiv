import Workspace.ProofLemmas.Thm61OddTriads

/-! The nine edge classes of the short odd configuration in 6.1(7). -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm61OddEdgeClasses
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61OddTriads Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-- Paper, 6.1(7): "there is a `J`-enlargement that appears in the complement
of `G`." The setup forces the three edge classes to be the three disjoint
matchings of the labelled `K₃,₃`. This is the attachment data for that construction. -/
theorem edge_classes
    {V : Type*} {n : ℕ} (G : SimpleGraph V) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V)
    (a c : Fin 3 → Fin n) (ha : Function.Injective a) (hc : Function.Injective c)
    (hcross : ∀ i j, H.Adj (a i) (c j))
    (hta : ∀ i, Triad G H K φ Y (a i)) (htc : ∀ j, Triad G H K φ Y (c j))
    (hd1 : Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₁))
    (hd2 : Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₂))
    (hd12 : Disjoint (extraEdges G H K φ Y y₁) (extraEdges G H K φ Y y₂))
    (hs1 : SaturatesLineGraph H (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁))
    (hs2 : SaturatesLineGraph H (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂))
    (h00 : s(a 0, c 0) ∈ extraEdges G H K φ Y y₁)
    (h01 : s(a 0, c 1) ∈ extraEdges G H K φ Y y₂)
    (h10 : s(a 1, c 0) ∈ completeEdges G H K φ Y)
    (h21 : s(a 2, c 1) ∈ completeEdges G H K φ Y) :
    ∀ i j : Fin 3, s(a i, c j) ∈
      if j = i then extraEdges G H K φ Y y₁
      else if j = i + 1 then extraEdges G H K φ Y y₂
      else completeEdges G H K φ Y := by
  have incA : ∀ i j, s(a i, c j) ∈ incidentEdges H (a i) :=
    fun i j => ⟨hcross i j, by simp⟩
  have incC : ∀ i j, s(a i, c j) ∈ incidentEdges H (c j) :=
    fun i j => ⟨hcross i j, by simp⟩
  have ne : ∀ i j k l : Fin 3, (i ≠ k ∨ j ≠ l) → s(a i, c j) ≠ s(a k, c l) := by
    intro i j k l h hE
    rcases Sym2.eq_iff.mp hE with ⟨hA, hC⟩ | ⟨hAC, _⟩
    · exact h.elim (fun h => h (ha hA)) (fun h => h (hc hC))
    · exact (hcross i l).ne hAC
  have notX : ∀ (v : Fin n) (ht : Triad G H K φ Y v) (e f : Sym2 (Fin n)),
      e ∈ incidentEdges H v → f ∈ incidentEdges H v →
      e ∈ completeEdges G H K φ Y → f ≠ e → f ∉ completeEdges G H K φ Y := by
    intro v ht e f he hf hX hne hfX
    exact hne (ht.2 ⟨hf, hfX⟩ ⟨he, hX⟩)
  have h02 := other_incident_is_complete φ Y y₁ y₂ (hta 0).1
    (incA 0 0) h00 (incA 0 1) h01 (incA 0 2)
    (ne 0 2 0 0 (by decide)) (ne 0 2 0 1 (by decide)) hd1 hd2 hd12 hs1 hs2
  have h20 := opposite_extra_class φ Y y₁ y₂ hd12 hs2 (htc 0).1
    (incC 0 0) (incC 2 0) h00
    (notX _ (htc 0) _ _ (incC 1 0) (incC 2 0) h10 (ne 2 0 1 0 (by decide)))
    (ne 2 0 0 0 (by decide))
  have h11 := opposite_extra_class φ Y y₂ y₁ hd12.symm hs1 (htc 1).1
    (incC 0 1) (incC 1 1) h01
    (notX _ (htc 1) _ _ (incC 2 1) (incC 1 1) h21 (ne 1 1 2 1 (by decide)))
    (ne 1 1 0 1 (by decide))
  have h12 := opposite_extra_class φ Y y₁ y₂ hd12 hs2 (hta 1).1
    (incA 1 1) (incA 1 2) h11
    (notX _ (hta 1) _ _ (incA 1 0) (incA 1 2) h10 (ne 1 2 1 0 (by decide)))
    (ne 1 2 1 1 (by decide))
  have h22 := opposite_extra_class φ Y y₂ y₁ hd12.symm hs1 (hta 2).1
    (incA 2 0) (incA 2 2) h20
    (notX _ (hta 2) _ _ (incA 2 1) (incA 2 2) h21 (ne 2 2 2 1 (by decide)))
    (ne 2 2 2 0 (by decide))
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceAdd, Fin.reduceEq, ite_true, ite_false] <;>
    assumption

end Workspace.ProofLemmas.Thm61OddEdgeClasses
