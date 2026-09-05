import Workspace.ProofLemmas.Thm57Setup
import Workspace.Statements.S05.Thm_5_5

/-! # Extending the two-centre cover in 5.7

The paper takes `V(C) = V(A) ∪ {c₁,c₂}` and
`V(D) = (V(H) \\ V(A)) ∪ {c₁,c₂}`. Theorem 5.5 then gives `V(C) = V(H)`,
since neither side can be contained in a branch and `V(D)` is proper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameSeparation

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The separator in the paper extends the cover of the edges meeting `A` to all of `X`. -/
theorem extend_cover (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet) (hnoB : ¬ SomeBranchMeetsAll H X)
    (A : Set W) (hlarge : 3 ≤ A.ncard)
    (hnoA : ¬ ∃ q : List W, IsBranch H q ∧ A ⊆ {v | v ∈ q})
    (hboundary : ∀ u ∈ A, ∀ v ∉ A, H.Adj u v → s(u, v) ∈ X)
    (c₁ c₂ : W)
    (hlocal : ∀ e ∈ X, (∃ v ∈ A, v ∈ e) → c₁ ∈ e ∨ c₂ ∈ e) :
    (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
      X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂ := by
  classical
  let P : Set W := {c₁, c₂}
  let CV : Set W := A ∪ P
  let DV : Set W := Aᶜ ∪ P
  let C : H.Subgraph := (⊤ : H.Subgraph).induce CV
  let D : H.Subgraph := (⊤ : H.Subgraph).induce DV
  have hcross : ∀ u ∈ A, ∀ v ∉ A, H.Adj u v → u ∈ P ∨ v ∈ P := by
    intro u hu v hv huv
    rcases hlocal s(u, v) (hboundary u hu v hv huv) ⟨u, hu, by simp⟩ with h | h
    · rcases Sym2.mem_iff.mp h with h | h
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr (Or.inl h.symm)
    · rcases Sym2.mem_iff.mp h with h | h
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr (Or.inr h.symm)
  have hunion : C ⊔ D = ⊤ := by
    apply le_antisymm le_top
    constructor
    · intro w _
      by_cases hw : w ∈ A
      · exact Or.inl (Or.inl hw)
      · exact Or.inr (Or.inl hw)
    · intro u v huv
      by_cases hu : u ∈ A
      · by_cases hv : v ∈ A
        · exact Or.inl ⟨Or.inl hu, Or.inl hv, huv⟩
        · rcases hcross u hu v hv huv with huP | hvP
          · exact Or.inr ⟨Or.inr huP, Or.inl hv, huv⟩
          · exact Or.inl ⟨Or.inl hu, Or.inr hvP, huv⟩
      · by_cases hv : v ∈ A
        · rcases hcross v hv u hu huv.symm with hvP | huP
          · exact Or.inr ⟨Or.inl hu, Or.inr hvP, huv⟩
          · exact Or.inl ⟨Or.inr huP, Or.inl hv, huv⟩
        · exact Or.inr ⟨Or.inl hu, Or.inl hv, huv⟩
  have hPcard : P.ncard ≤ 2 := by
    calc
      P.ncard ≤ ({c₂} : Set W).ncard + 1 := Set.ncard_insert_le c₁ {c₂}
      _ = 2 := by simp
  have hcap : (C ⊓ D).verts.ncard ≤ 2 := by
    apply le_trans (Set.ncard_le_ncard (t := P) ?_ (Set.toFinite _)) hPcard
    intro w hw
    change (w ∈ A ∨ w ∈ P) ∧ (w ∉ A ∨ w ∈ P) at hw
    rcases hw.1 with hwA | hwP
    · exact hw.2.resolve_left (not_not.mpr hwA)
    · exact hwP
  have hDne : D.verts ≠ Set.univ := by
    intro hD
    have hAP : A ⊆ P := by
      intro w hw
      have hwD : w ∈ D.verts := hD.symm ▸ Set.mem_univ w
      change w ∉ A ∨ w ∈ P at hwD
      exact hwD.resolve_left (not_not.mpr hw)
    have := Set.ncard_le_ncard hAP (Set.toFinite _)
    omega
  have hXD : ∀ e ∈ X, ∃ w ∈ D.verts, w ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      by_cases hu : u ∈ A
      · rcases hlocal s(u, v) he ⟨u, hu, by simp⟩ with hc | hc
        · exact ⟨c₁, Or.inr (Or.inl rfl), hc⟩
        · exact ⟨c₂, Or.inr (Or.inr rfl), hc⟩
      · exact ⟨u, Or.inl hu, by simp⟩
  have hCfull : C.verts = Set.univ := by
    by_contra hCne
    rcases _root_.Workspace.Statements.S05.SPGT.thm_5_5
      H hc3 C D hunion hcap hCne hDne with ⟨q, hq, hCV, _⟩ | ⟨q, hq, hDV, _⟩
    · exact hnoA ⟨q, hq, fun _ hw => hCV (Or.inl hw)⟩
    · apply hnoB
      refine ⟨q, hq, ?_⟩
      intro e he
      obtain ⟨w, hw, hwe⟩ := hXD e he
      exact ⟨w, hDV hw, hwe⟩
  have hglobal : ∀ e ∈ X, c₁ ∈ e ∨ c₂ ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huC : u ∈ C.verts := hCfull.symm ▸ Set.mem_univ u
      change u ∈ A ∨ u ∈ P at huC
      rcases huC with huA | huP
      · exact hlocal _ he ⟨u, huA, by simp⟩
      · rcases huP with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
  constructor
  · rintro ⟨q, hq, hc₁, hc₂⟩
    apply hnoB
    refine ⟨q, hq, ?_⟩
    intro e he
    rcases hglobal e he with h | h
    · exact ⟨c₁, hc₁, h⟩
    · exact ⟨c₂, hc₂, h⟩
  · intro e he
    rcases hglobal e he with h | h
    · exact Or.inl ⟨hXE he, h⟩
    · exact Or.inr ⟨hXE he, h⟩

end Workspace.ProofLemmas.Thm57EndgameSeparation
