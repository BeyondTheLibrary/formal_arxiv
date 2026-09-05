import Workspace.ProofLemmas.Thm61OddK33

/-! The complete six-vertex configuration in 6.1(7). -/
set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61OddLabelled

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers Workspace.ProofLemmas.Thm61OddTriads
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- Paper, 6.1(7): "By (3) applied to `f₂` and `b₁` we deduce that `b₁`
is adjacent to `x₂`, and, similarly, `x₁` is adjacent to `b₂`."
The resulting bipartition has three triads on each side. -/
theorem labelled_configuration
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    (htriad : Triad G H K φ Y b)
    (htriad₃ : Triad G H K φ Y b₃)
    (hB₁ : trackLength B₁ = 1) (hB₂ : trackLength B₂ = 1)
    (hB₃ : trackLength B₃ = 1)
    (x₁ x₂ : Fin n) (hf₁eq : f₁ = s(b₁, x₁)) (hf₂eq : f₂ = s(b₂, x₂))
    (hx₁x₂ : x₁ ≠ x₂) (hb₁x₁ : H.Adj b₁ x₁) (hb₂x₂ : H.Adj b₂ x₂)
    (hx₁b₃ : H.Adj x₁ b₃) (hx₂b₃ : H.Adj x₂ b₃) :
    let a : Fin 3 → Fin n := ![b, x₁, x₂]
    let c : Fin 3 → Fin n := ![b₁, b₂, b₃]
    Function.Injective a ∧ Function.Injective c ∧
    (∀ i j, H.Adj (a i) (c j)) ∧
    (∀ i, Triad G H K φ Y (a i)) ∧ (∀ i, Triad G H K φ Y (c i)) := by
  classical
  dsimp only
  have hbc' := hbc
  rcases hbc' with ⟨hbV, _, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, _, _,
    hBr₁, he₁B₁, hfrom₁, hBr₂, he₂B₂, hfrom₂, hBr₃, he₃B₃, hfrom₃⟩
  obtain ⟨_, _, _, _, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
    hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have short_adj : ∀ {B : List (Fin n)} {u v : Fin n},
      IsTrackFrom H B u v → trackLength B = 1 → H.Adj u v := by
    intro B u v hfrom hlen
    have he : s(u, v) ∈ trackEdges B := by
      rw [trackEdges_eq_singleton_of_length_one hfrom hlen]
      exact Set.mem_singleton _
    obtain ⟨i, hi, he⟩ := he
    have heE : s(u, v) ∈ H.edgeSet := by rw [he]; exact hfrom.1.2.2 i hi
    exact heE
  have hb₁ := short_adj hfrom₁ hB₁
  have hb₂ := short_adj hfrom₂ hB₂
  have hb₃ := short_adj hfrom₃ hB₃
  have hn12 : ¬ H.Adj b₁ b₂ := fun h => no_triangle_of_bipartite hsub.2 hb₁ h hb₂
  have hn13 : ¬ H.Adj b₁ b₃ := fun h => no_triangle_of_bipartite hsub.2 hb₁ h hb₃
  have hn23 : ¬ H.Adj b₂ b₃ := fun h => no_triangle_of_bipartite hsub.2 hb₂ h hb₃
  have triadAt (u v : Fin n) := triad_of_nonadjacent_triad G hG H hsub.2 K φ Y hYmajor hmin
    y₁ y₂ Q hQ hQY hy hQodd (u := u) (v := v)
  have ht₁ := triadAt b₁ b₃ hb₁V htriad₃ hb₁b₃ hn13
  have ht₂ := triadAt b₂ b₃ hb₂V htriad₃ hb₂b₃ hn23
  have hx₁b : x₁ ≠ b := by
    intro h
    have heq : f₁ = e₁ := by
      rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁] at he₁B₁
      rw [Set.mem_singleton_iff.mp he₁B₁, hf₁eq, h, Sym2.eq_swap]
    exact he₁X₁.2 (heq ▸ hf.1.1)
  have hx₂b : x₂ ≠ b := by
    intro h
    have heq : f₂ = e₂ := by
      rw [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂] at he₂B₂
      rw [Set.mem_singleton_iff.mp he₂B₂, hf₂eq, h, Sym2.eq_swap]
    exact he₂X₂.2 (heq ▸ hf.2.1.1)
  have hx₁b₂ : x₁ ≠ b₂ := fun h => hn12 (by rwa [← h])
  have hx₂b₁ : x₂ ≠ b₁ := fun h => hn12 (by rw [← h]; exact hb₂x₂.symm)
  have cross (u a c : Fin n) := adjacent_to_complete_end G hG H K φ Y hYmajor hmin
    y₁ y₂ Q hQ hQY hy hQodd (u := u) (a := a) (c := c)
  have h12 := (cross b₁ b₂ x₂ ht₁ hb₁b₂ hx₂b₁.symm hn12 (by simpa [hf₂eq] using hf.2.1.1)).1
  have h21 := (cross b₂ b₁ x₁ ht₂ hb₁b₂.symm hx₁b₂.symm (fun h => hn12 h.symm)
    (by simpa [hf₁eq] using hf.1.1)).1
  have hcross : ∀ i j : Fin 3, H.Adj (![b, x₁, x₂] i) (![b₁, b₂, b₃] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons] <;>
      first | assumption | exact hb₁x₁.symm | exact hb₂x₂.symm | exact h12.symm | exact h21.symm
  have ha : Function.Injective (![b, x₁, x₂] : Fin 3 → Fin n) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hx₁b h).elim | exact (hx₂b h).elim | exact (hx₁x₂ h).elim | exact (hx₁b h.symm).elim | exact (hx₂b h.symm).elim | exact (hx₁x₂ h.symm).elim
  have hc : Function.Injective (![b₁, b₂, b₃] : Fin 3 → Fin n) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hb₁b₂ h).elim | exact (hb₁b₃ h).elim | exact (hb₂b₃ h).elim | exact (hb₁b₂ h.symm).elim | exact (hb₁b₃ h.symm).elim | exact (hb₂b₃ h.symm).elim
  have branch : ∀ i : Fin 3, (![b, x₁, x₂] i) ∈ branchVertices H := by
    intro i
    have hsubN : ({b₁, b₂, b₃} : Set (Fin n)) ⊆ H.neighborSet (![b, x₁, x₂] i) := by
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact hcross i 0
      · exact hcross i 1
      · exact hcross i 2
    have hcard : ({b₁, b₂, b₃} : Set (Fin n)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨b₁, b₂, b₃, hb₁b₂, hb₁b₃, hb₂b₃, rfl⟩
    change 3 ≤ (H.neighborSet _).ncard
    rw [← hcard]
    exact Set.ncard_le_ncard hsubN
  refine ⟨ha, hc, hcross, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact htriad
    · exact triadAt x₁ b (branch 1) htriad hx₁b
        (fun h => no_triangle_of_bipartite hsub.2 h hb₃ hx₁b₃)
    · exact triadAt x₂ b (branch 2) htriad hx₂b
        (fun h => no_triangle_of_bipartite hsub.2 h hb₃ hx₂b₃)
  · intro i
    fin_cases i
    · exact ht₁
    · exact ht₂
    · exact htriad₃

end Workspace.ProofLemmas.Thm61OddLabelled
