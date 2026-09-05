import Workspace.ProofLemmas.Thm192Claim5Last
import Workspace.Statements.S13.Thm_13_6

/-! The parity argument for the last neighbour in claim (5) of 19.2 (printed p. 119). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim5Cut

open Workspace.Types.Core.SPGT Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup
open Workspace.ProofLemmas.Thm192Claim4Rim

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "Since `i > 1`, `x₀-x₂-pᵢ-⋯-pₙ-x₁` is an odd path of length ≥ 5."
Applying 13.6 first with `Y ∪ {z}` and then with `Y` gives a complete edge of `C`,
contrary to claim (4). -/
theorem cut_contradiction {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2) {Y : Set V}
    (hHyp : Hyp192 G z A₀ x Y) (hcex : ¬ Concl192 G z A₀ x Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ interior P, w ∈ wheelSystemA G z A₀ x 1) (hPlen : 3 ≤ P.length)
    (h02 : G.Adj (x 0) (x 2)) {i : ℕ} (hi : 2 ≤ i) (hil : i + 2 < P.length)
    (hmax : ∀ (j : ℕ) (hj : j < P.length), i ≤ j → (G.Adj (x 2) (P[j]'hj) ↔ j = i)) :
    False := by
  classical
  have hBerge := hG.1.1.1.1
  have hrim := rim hBerge hws hP hPint hPlen
  have hzP : z ∉ P := (List.nodup_cons.mp hrim.1.2.1).1
  have hzx : ∀ j ≤ 2, G.Adj z (x j) := hws.2.2.2.2.2.2
  have h0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hx01 : x 0 ≠ x 1 := by
    intro he
    have := hws.2.1 0 (by omega) 1 (by omega) he
    omega
  have h2P : x 2 ∉ P := by
    intro h2
    have h20 : x 2 ≠ x 0 := h02.ne.symm
    have h21 : x 2 ≠ x 1 := by
      intro he
      have := hws.2.1 2 (by omega) 1 (by omega) he
      omega
    have h2int := (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨h2, h20, h21⟩
    exact wheelSystemA_no_z _ (hPint _ h2int) (hzx 2 (by omega))
  have hS : IsPathFrom G (P.drop i) (P[i]'(by omega)) (x 1) := by
    refine ⟨PathBasics.isPathList_drop hP.1 (by omega), ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem (by omega)]
    · rw [List.getLast?_drop, if_neg (by omega)]; exact hP.2.2
  have hSmem : ∀ a ∈ P.drop i, a ∈ P ∧ a ≠ x 0 ∧ ¬ G.Adj (x 0) a := by
    intro a ha
    obtain ⟨j, hj, he⟩ := List.mem_drop_iff_getElem.mp ha
    have hji : i + j < P.length := by omega
    have hidx : P[i + j]'hji = a := he
    refine ⟨List.mem_of_mem_drop ha, ?_, ?_⟩
    · intro heq
      have ee : P[i + j]'hji = P[0]'(by omega) := hidx.trans (heq.trans h0.symm)
      have := hP.1.2.1.getElem_inj_iff.mp ee
      omega
    · rw [← hidx, ← h0]
      exact PathBasics.path_not_adj_of_gap hP.1 (by omega) hji (by omega) (by omega)
  have hSA : ∀ a ∈ P.drop i, a ≠ x 1 → a ∈ wheelSystemA G z A₀ x 1 := by
    intro a ha ha1
    exact hPint a ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨(hSmem a ha).1, (hSmem a ha).2.1, ha1⟩)
  have h2S : IsPathFrom G (x 2 :: P.drop i) (x 2) (x 1) := by
    refine PathAttach.isPathFrom_cons hS ((hmax i (by omega) le_rfl).mpr rfl)
      (fun hm => h2P (List.mem_of_mem_drop hm)) ?_
    intro a ha hne hadj
    obtain ⟨j, hj, he⟩ := List.mem_drop_iff_getElem.mp ha
    have hji : i + j < P.length := by omega
    have hidx : P[i + j]'hji = a := he
    have heq := (hmax (i + j) hji (by omega)).mp (hidx ▸ hadj)
    have helem : P[i + j]'hji = P[i]'(by omega) := hP.1.2.1.getElem_inj_iff.mpr heq
    exact hne (hidx.symm.trans helem)
  have hT : IsPathFrom G (x 0 :: x 2 :: P.drop i) (x 0) (x 1) := by
    refine PathAttach.isPathFrom_cons h2S h02 ?_ ?_
    · intro ha
      rcases List.mem_cons.mp ha with he | he
      · exact h02.ne he
      · exact (hSmem _ he).2.1 rfl
    · intro a ha hne
      rcases List.mem_cons.mp ha with he | he
      · exact (hne he).elim
      · exact (hSmem a he).2.2
  have hC : IsHoleList G (z :: x 2 :: P.drop i) :=
    Thm192Infra.holeFromCut hP hPint
      (fun a ha => wheelSystemA_no_z a ha) (hzx 0 (by omega)) (hzx 1 (by omega))
      (hzx 2 (by omega)) hzP h2P (by omega) (by omega) hmax
  have hEven := hBerge.1 _ hC
  have hTlen : 6 ≤ (x 0 :: x 2 :: P.drop i).length := by
    obtain ⟨k, hk⟩ := hEven
    simp only [holeLength, List.length_cons, List.length_drop] at hk ⊢
    omega
  have hTodd : Odd (pathLength (x 0 :: x 2 :: P.drop i)) := by
    obtain ⟨k, hk⟩ := hEven
    refine ⟨k - 1, ?_⟩
    simp only [holeLength, List.length_cons, List.length_drop] at hk
    simp only [pathLength, List.length_cons, List.length_drop]
    omega
  have hTout : ∀ a ∈ x 0 :: x 2 :: P.drop i, a ∉ Y ∧ a ≠ z := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with he | he | he
    · rw [he]
      exact ⟨fun ha => (hHyp.1 _ ha).2.1 rfl, (hzx 0 (by omega)).ne.symm⟩
    · rw [he]
      exact ⟨fun ha => (hHyp.1 _ ha).2.2.2 rfl, (hzx 2 (by omega)).ne.symm⟩
    · refine ⟨?_, fun heq => hzP (heq ▸ (hSmem a he).1)⟩
      by_cases ha1 : a = x 1
      · rw [ha1]; exact fun ha => (hHyp.1 _ ha).2.2.1 rfl
      · exact hub_outside hHyp (hSA a he ha1)
  have h0c : VertexComplete G (x 0) (Y ∪ {z}) := by
    rintro a (ha | rfl)
    · exact hHyp.2.2.1 a ha
    · exact (hzx 0 (by omega)).symm
  have h1c : VertexComplete G (x 1) (Y ∪ {z}) := by
    rintro a (ha | rfl)
    · exact hHyp.2.2.2.1 a ha
    · exact (hzx 1 (by omega)).symm
  have hzY : VertexComplete G z Y := by
    by_contra hn
    obtain ⟨w, hw, hnw⟩ : ∃ w ∈ Y, ¬ G.Adj z w := by
      simpa only [VertexComplete, not_forall, exists_prop] using hn
    have hanti : AnticonnectedSet G (Y ∪ {z}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hHyp.2.1
        ⟨w, hw, ⟨fun he => (hHyp.1 w hw).1 he.symm, hnw⟩⟩
    have honly : ∀ a ∈ x 0 :: x 2 :: P.drop i,
        VertexComplete G a (Y ∪ {z}) → a = x 0 ∨ a = x 1 := by
      intro a ha hc
      simp only [List.mem_cons] at ha
      rcases ha with he | he | he
      · exact Or.inl he
      · exfalso
        apply hHyp.2.2.2.2.1
        rw [← he]
        exact fun b hb => hc b (Or.inl hb)
      · by_cases ha1 : a = x 1
        · exact Or.inr ha1
        · exact (wheelSystemA_no_z a (hSA a he ha1) (hc z (Or.inr rfl)).symm).elim
    have hXP : Y ∪ {z} ⊆ {a : V | a ∈ x 0 :: x 2 :: P.drop i}ᶜ := by
      intro a ha hm
      rcases ha with ha | ha
      · exact (hTout a hm).1 ha
      · exact (hTout a hm).2 ha
    rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 _ _ _ hT hTodd
        _ hXP hanti h0c h1c with ⟨u, hu, v, hv, he⟩ | ⟨h3, _⟩
    · rcases honly u hu he.2.1 with hu | hu <;>
        rcases honly v hv he.2.2 with hv | hv
      · rw [hu, hv] at he; exact G.irrefl he.1
      · exact x0_not_adj_x1 hws (by rw [hu, hv] at he; exact he.1)
      · exact x0_not_adj_x1 hws (by rw [hu, hv] at he; exact he.1.symm)
      · rw [hu, hv] at he; exact G.irrefl he.1
    · simp only [pathLength] at h3
      omega
  have hXP : Y ⊆ {a : V | a ∈ x 0 :: x 2 :: P.drop i}ᶜ :=
    fun a ha hm => (hTout a hm).1 ha
  rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 _ _ _ hT hTodd
      _ hXP hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1 with ⟨u, hu, v, hv, he⟩ | ⟨h3, _⟩
  · have hmem : ∀ a ∈ x 0 :: x 2 :: P.drop i, VertexComplete G a Y → a ∈ P := by
      intro a ha hc
      simp only [List.mem_cons] at ha
      rcases ha with he | he | he
      · rw [he]; exact PathBasics.head_mem hP.2.1
      · rw [he] at hc; exact (hHyp.2.2.2.2.1 hc).elim
      · exact (hSmem a he).1
    exact hcex (wheel_of_complete_edge hBerge hws hHyp hzY hP hPint hPlen
      (hmem u hu he.2.1) (hmem v hv he.2.2) he)
  · simp only [pathLength] at h3
    omega

end Workspace.ProofLemmas.Thm192Claim5Cut
