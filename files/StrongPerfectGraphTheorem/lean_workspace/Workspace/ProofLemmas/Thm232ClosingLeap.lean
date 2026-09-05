import Workspace.ProofLemmas.Thm132Claim5Long
import Workspace.Statements.S13.Thm_13_6

/-! Exclude the leap in the closing paragraph of 23.2 by 13.6. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingLeap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “A leap would imply there are two vertices in
`Y`, joined by an odd path of length ≥ 5 with interior in `F ∪ A₀`. Hence its
ends are `{x₀,x₁}`-complete, and its internal vertices are not, contrary to 13.6.” -/
theorem leap_absurd {G : SimpleGraph V} (hG : InF5 G)
    {D : List V} (hD : IsHoleList G D) (hD6 : 6 ≤ D.length)
    {u v : V} {X Y B : Set V} (hX : AnticonnectedSet G X)
    (hDY : ∀ w ∈ D, w ∉ Y)
    (hDB : ∀ w ∈ D, w ≠ u → w ≠ v → w ∈ B)
    (hYX : ∀ a ∈ Y, VertexComplete G a X)
    (hYout : ∀ a ∈ Y, a ∉ X) (hBout : ∀ a ∈ B, a ∉ X)
    (hBnc : ∀ a ∈ B, ¬ VertexComplete G a X)
    {a b : V} (ha : a ∈ Y) (hb : b ∈ Y)
    (hleap : IsLeapForHole G D u v a b) : False := by
  obtain ⟨_, i, hhead, hlast, hL⟩ := hleap
  let P := D.rotate i
  have hP : IsPathFrom (G.deleteEdges {s(u,v)}) P v u :=
    PathGlue.isPathFrom_hole_deleteEdges hD hhead hlast
  have hPlen : P.length = D.length := List.length_rotate _ _
  have hPY : ∀ w ∈ P, w ∉ Y := fun w hw => hDY w (List.mem_rotate.mp hw)
  have hIB : ∀ w ∈ SPGT.interior P, w ∈ B := by
    intro w hw
    obtain ⟨hwP, hwv, hwu⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
    exact hDB w (List.mem_rotate.mp hwP) hwu hwv
  have huD : u ∈ D := List.mem_rotate.mp (PathBasics.getLast_mem hlast)
  have hvD : v ∈ D := List.mem_rotate.mp (PathBasics.head_mem hhead)
  let K := a :: (SPGT.interior P ++ [b])
  obtain ⟨hKdel, hKlen⟩ := Thm132Claim5Long.leap_path hP
    (by change 5 ≤ P.length - 1; omega) hPY ha hb hL
  have hKavoid : ∀ w ∈ K, w ≠ u ∧ w ≠ v := by
    intro w hw
    simp only [K, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with he | hw | he
    · subst w
      exact ⟨fun he => hDY u huD (he ▸ ha), fun he => hDY v hvD (he ▸ ha)⟩
    · have hh := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
      exact ⟨hh.2.2, hh.2.1⟩
    · subst w
      exact ⟨fun he => hDY u huD (he ▸ hb), fun he => hDY v hvD (he ▸ hb)⟩
  have hadj : ∀ w ∈ K, ∀ t : V,
      (G.deleteEdges {s(u,v)}).Adj w t ↔ G.Adj w t := by
    intro w hw t
    simp [SimpleGraph.deleteEdges_adj, Sym2.eq_iff, (hKavoid w hw).1, (hKavoid w hw).2]
  have hK : IsPathFrom G K a b := by
    refine ⟨⟨hKdel.1.1, hKdel.1.2.1, ?_⟩, hKdel.2.1, hKdel.2.2⟩
    intro j k hj hk
    rw [← hadj _ (List.getElem_mem hj) _]
    exact hKdel.1.2.2 j k hj hk
  have hK5 : 5 ≤ pathLength K := by
    change pathLength K = pathLength P at hKlen
    rw [hKlen]
    change 5 ≤ P.length - 1
    omega
  have hKodd : Odd (pathLength K) := by
    have heven := hG.1.1.1 D hD
    change Even D.length at heven
    rw [Nat.even_iff] at heven
    rw [hKlen, PathBasics.pathLength_eq, hPlen, Nat.odd_iff]
    omega
  have hKout : ∀ w ∈ K, w ∉ X := by
    intro w hw
    simp only [K, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with he | hw | he
    · exact he ▸ hYout a ha
    · exact hBout w (hIB w hw)
    · exact he ▸ hYout b hb
  have hcomplete : ∀ w ∈ K, VertexComplete G w X → w = a ∨ w = b := by
    intro w hw hc
    simp only [K, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with he | hw | he
    · exact Or.inl he
    · exact (hBnc w (hIB w hw) hc).elim
    · exact Or.inr he
  have hnab : ¬ G.Adj a b := by
    have hn : 3 ≤ K.length := by change 5 ≤ K.length - 1 at hK5; omega
    have hh := PathBasics.path_ends_not_adj hK.1 hn
    rwa [PathBasics.getElem_zero_of_head? hK.2.1 (by omega),
      PathBasics.getElem_last_of_getLast? hK.2.2 (by omega)] at hh
  rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG K a b hK hKodd X
      (fun w hwX hwK => hKout w hwK hwX) hX (hYX a ha) (hYX b hb) with
      ⟨c, hc, d, hd, he⟩ | hthree
  · rcases hcomplete c hc he.2.1 with rfl | rfl <;>
      rcases hcomplete d hd he.2.2 with rfl | rfl
    · exact G.irrefl he.1
    · exact hnab he.1
    · exact hnab he.1.symm
    · exact G.irrefl he.1
  · omega

end Workspace.ProofLemmas.Thm232ClosingLeap
