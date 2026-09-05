import Workspace.ProofLemmas.Thm61Claim12RookExtension
import Workspace.ProofLemmas.Thm61Claim12Common

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Workspace.ProofLemmas.Thm61Claim12Short

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance
open Workspace.ProofLemmas.L33SelfComplementary

/-- The nine-edge dictionary and the attachments of `Q` needed for the sentence
"if `B` has length 1 then the second outcome of the theorem holds" in claim (12). -/
theorem short_complement
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K Y : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Q : List V) (y₁ y₂ : V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q)) (hYout : ∀ x ∈ Y, x ∉ K)
    {b b₁ b₂ b₃ u v : Fin n} (hnd : [b, b₁, v, b₂, b₃, u].Nodup)
    (h00 : s(b, b₁) ∈ extraEdges G H K φ Y y₁)
    (h01 : s(b, b₂) ∈ extraEdges G H K φ Y y₂)
    (h02 : s(b, b₃) ∈ completeEdges G H K φ Y)
    (h10 : s(v, b₁) ∈ extraEdges G H K φ Y y₂)
    (h11 : s(v, b₂) ∈ extraEdges G H K φ Y y₁)
    (h12 : s(v, b₃) ∈ completeEdges G H K φ Y)
    (h20 : s(u, b₁) ∈ completeEdges G H K φ Y)
    (h21 : s(u, b₂) ∈ completeEdges G H K φ Y)
    (h22 : s(u, b₃) ∈ H.edgeSet) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
        (φ' : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (completeBipartiteGraph (Fin 3) (Fin 3)) H' K' ∧
        IsOvershadowedAppearance Gᶜ H' K' φ' := by
  classical
  have hn := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  let A : Fin 3 → Fin n := ![b, v, u]
  let B : Fin 3 → Fin n := ![b₁, b₂, b₃]
  have hA : Function.Injective A := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [A] at hij ⊢ <;> omega
  have hB : Function.Injective B := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [B] at hij ⊢ <;> omega
  have hAB : ∀ i j, A i ≠ B j := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp [A, B] <;> omega
  have hE : ∀ i : Fin 3 × Fin 3, s(A i.1, B i.2) ∈ H.edgeSet := by
    rintro ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> dsimp [A, B]
    · exact h00.1.1
    · exact h01.1.1
    · exact h02.1
    · exact h10.1.1
    · exact h11.1.1
    · exact h12.1
    · exact h20.1
    · exact h21.1
    · exact h22
  let edge : Fin 3 × Fin 3 → H.edgeSet := fun i => ⟨s(A i.1, B i.2), hE i⟩
  have hinj : Function.Injective edge := by
    intro i j hij
    have hh : s(A i.1, B i.2) = s(A j.1, B j.2) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.mp hh with ⟨ha, hb⟩ | ⟨ha, _⟩
    · exact Prod.ext (hA ha) (hB hb)
    · exact False.elim (hAB _ _ ha)
  let w : Fin 3 × Fin 3 → V := fun i => (φ (edge i)).val
  have hwinj : Function.Injective w := by
    intro i j hij
    apply hinj
    apply φ.injective
    exact Subtype.ext hij
  have hrel : ∀ i j, G.Adj (w i) (w j) ↔ rook33.Adj i j := by
    intro i j
    change (G.induce K).Adj (φ (edge i)) (φ (edge j)) ↔ _
    rw [φ.map_rel_iff, SimpleGraph.lineGraph_adj_iff_exists, rook33_adj_iff]
    constructor
    · rintro ⟨hne, x, hxi, hxj⟩
      refine ⟨fun h => hne (congrArg edge h), ?_⟩
      change x ∈ s(A i.1, B i.2) at hxi
      change x ∈ s(A j.1, B j.2) at hxj
      rcases Sym2.mem_iff.mp hxi with ha | hb <;> rcases Sym2.mem_iff.mp hxj with hc | hd
      · exact Or.inl (hA (ha.symm.trans hc))
      · exact False.elim (hAB _ _ (ha.symm.trans hd))
      · exact False.elim (hAB _ _ (hc.symm.trans hb))
      · exact Or.inr (hB (hb.symm.trans hd))
    · rintro ⟨hne, hi | hj⟩
      · exact ⟨fun h => hne (hinj h), A i.1, by simp [edge], by simp [edge, hi]⟩
      · exact ⟨fun h => hne (hinj h), B i.2, by simp [edge], by simp [edge, hj]⟩
  have hQout : ∀ x ∈ Q, x ∉ Set.range w := by
    rintro x hx ⟨i, hi⟩
    exact hYout x ((hQY x).mp hx) (hi ▸ (φ (edge i)).property)
  apply Thm61Claim12RookExtension.rook_path_replacement G w hwinj hrel Q y₁ y₂ hQ hy hQeven hQout
  intro x hx i hi
  have hxY := (hQY x).mp hx
  have hxK := hYout x hxY
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simpa [w, edge, A, B] using
      compl_adj_image_of_extraEdges_iff G H K Y φ h00.1.1 h00 hxY hxK
  · simpa [w, edge, A, B] using
      compl_adj_image_of_extraEdges_iff G H K Y φ h01.1.1 h01 hxY hxK
  · simpa [w, edge, A, B] using
      not_compl_adj_image_of_completeEdges G H K Y φ h02.1 h02 hxY
  · simpa [w, edge, A, B] using
      compl_adj_image_of_extraEdges_iff G H K Y φ h10.1.1 h10 hxY hxK
  · simpa [w, edge, A, B] using
      compl_adj_image_of_extraEdges_iff G H K Y φ h11.1.1 h11 hxY hxK
  · simpa [w, edge, A, B] using
      not_compl_adj_image_of_completeEdges G H K Y φ h12.1 h12 hxY
  · simpa [w, edge, A, B] using
      not_compl_adj_image_of_completeEdges G H K Y φ h20.1 h20 hxY
  · simpa [w, edge, A, B] using
      not_compl_adj_image_of_completeEdges G H K Y φ h21.1 h21 hxY
  · exact False.elim (hi rfl)

end Workspace.ProofLemmas.Thm61Claim12Short
