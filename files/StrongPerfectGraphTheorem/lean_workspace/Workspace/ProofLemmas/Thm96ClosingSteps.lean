import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm96StriationTools
import Workspace.Statements.S04.Thm_4_1
import Workspace.Statements.S04.Thm_4_2

/-!
# Separation steps in the closing paragraph of 9.6

The closing paragraph uses two short separation arguments.  An outside component with no
attachment is a component of the whole graph.  If an antistrip has a middle vertex, that
vertex together with the chosen strip is the anticonnected side of a skew partition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm96ClosingSteps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm96StriationTools

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem component_add_adjacent {G : SimpleGraph V} {X F : Set V}
    (hF : IsComponent G X F) {x y : V} (hx : x ∈ F) (hy : y ∈ X)
    (hxy : G.Adj x y) : y ∈ F := by
  have hcon : ConnectedSet G (F ∪ {y}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨x, hx, hxy.symm⟩
  have heq := hF.2.2 (F ∪ {y}) Set.subset_union_left
    (Set.union_subset hF.1 (Set.singleton_subset_iff.mpr hy)) hcon
  have hy' : y ∈ F ∪ {y} := Or.inr rfl
  rwa [heq] at hy'

private theorem eq_of_reachable_isolated {W : Type*} {H : SimpleGraph W} {a b : W}
    (hiso : ∀ z, ¬ H.Adj a z) (h : H.Reachable a b) : a = b := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

private theorem singleton_component_of_isolated {H : SimpleGraph V} {X : Set V} {z : V}
    (hzX : z ∈ X) (hiso : ∀ x ∈ X, ¬ H.Adj z x) :
    IsComponent H X ({z} : Set V) := by
  refine ⟨Set.singleton_subset_iff.mpr hzX, ?_, ?_⟩
  · intro a b
    have hab : a = b := Subtype.ext (by simpa using a.2.trans b.2.symm)
    rw [hab]
  · intro D hzD hDX hDcon
    apply Set.Subset.antisymm
    · intro y hyD
      have hr := hDcon ⟨z, hzD rfl⟩ ⟨y, hyD⟩
      have heq : (⟨z, hzD rfl⟩ : ↥D) = ⟨y, hyD⟩ :=
        eq_of_reachable_isolated
          (H := H.induce D)
          (fun q h => hiso q.1 (hDX q.2) h) hr
      simpa using (congrArg Subtype.val heq).symm
    · exact hzD

/-- PAPER (9.6, closing paragraph): an outside component with no attachment is separated
from the whole striation and from every other outside component, so the graph is disconnected. -/
theorem not_connected_of_unattached_component
    (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M F : Set V) (hL : IsStriation G S T)
    (hpart : M = (striationVertices S T)ᶜ)
    (hF : IsComponent G M F) (hFne : F.Nonempty)
    (hatt : attachments G F (striationVertices S T) = ∅) :
    ¬ ConnectedSet G (Set.univ : Set V) := by
  have hFanti : Anticomplete G F Fᶜ := by
    intro x hx y hy hadj
    by_cases hyM : y ∈ M
    · exact hy (component_add_adjacent hF hx hyM hadj)
    · have hyL : y ∈ striationVertices S T := by
        by_contra hyL
        exact hyM (by rw [hpart]; exact hyL)
      have hyatt : y ∈ attachments G F (striationVertices S T) :=
        ⟨hyL, x, hx, hadj.symm⟩
      rw [hatt] at hyatt
      exact hyatt
  have hFcne : Fᶜ.Nonempty := by
    have hm : 0 < m := by have := hL.2.2.2.2.2.2.2.1; omega
    let i : Fin m := ⟨0, hm⟩
    obtain ⟨x, hx⟩ := left_nonempty (hL.1 i)
    refine ⟨x, ?_⟩
    intro hxF
    exact (hpart ▸ hF.1 hxF)
      (Or.inl (Set.mem_iUnion.mpr ⟨i, left_subset_stripVertices _ hx⟩))
  exact _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
    (by rw [Set.union_compl_self]) hFne hFcne disjoint_compl_right hFanti

/-- PAPER (9.6, closing paragraph): if `z` is a middle vertex of an antistrip, then
`V(S i) ∪ {z}` is the anticonnected side of a skew partition.  Its singleton
anticomponent `{z}` lets theorem 4.1 balance the partition. -/
theorem balancedSkewPartition_of_middle_vertex
    (G : SimpleGraph V) (hG : Berge G) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M : Set V) (hL : IsStriation G S T)
    (hpart : M = (striationVertices S T)ᶜ)
    (hManti : ∀ f ∈ M, ∀ u ∈ (⋃ j : Fin n, stripVertices (T j)), ¬ G.Adj f u)
    (F : Set V) (hF : IsComponent G M F) (hFne : F.Nonempty)
    (i : Fin m)
    (hatt : attachments G F (striationVertices S T) ⊆ stripVertices (S i))
    (j : Fin n) (z : V) (hz : z ∈ middlePart (T j)) :
    AdmitsBalancedSkewPartition G := by
  let B : Set V := stripVertices (S i) ∪ {z}
  let A : Set V := Bᶜ
  have hzT : z ∈ stripVertices (T j) := middle_subset_stripVertices _ hz
  have hzL : z ∈ striationVertices S T :=
    Or.inr (Set.mem_iUnion.mpr ⟨j, hzT⟩)
  have hcomplete : ∀ v ∈ stripVertices (S i), G.Adj z v :=
    middle_vertex_complete_strip hG hL i j hz
  have hFsubA : F ⊆ A := by
    intro x hxF
    show x ∈ Bᶜ
    intro hxB
    rcases hxB with hxS | hxz
    · exact (hpart ▸ hF.1 hxF)
        (Or.inl (Set.mem_iUnion.mpr ⟨i, hxS⟩))
    · exact (hpart ▸ hF.1 hxF) (show x ∈ striationVertices S T by
        rw [show x = z from hxz]; exact hzL)
  have hrestne : (A \ F).Nonempty := by
    have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    obtain ⟨k, hki⟩ : ∃ k : Fin m, k ≠ i := by
      by_cases hi : i = ⟨0, h0⟩
      · exact ⟨⟨1, h1⟩, by rw [hi]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, h0⟩, Ne.symm hi⟩
    obtain ⟨w, hw⟩ := left_nonempty (hL.1 k)
    have hwSk : w ∈ stripVertices (S k) := left_subset_stripVertices _ hw
    refine ⟨w, ?_, ?_⟩
    · show w ∈ Bᶜ
      rintro (hwSi | hwz)
      · exact Set.disjoint_left.mp (hL.2.2.1 k i hki) hwSk hwSi
      · exact Set.disjoint_left.mp (hL.2.2.2.2.1 k j) hwSk
          (by rw [show w = z from hwz]; exact hzT)
    · intro hwF
      exact (hpart ▸ hF.1 hwF)
        (Or.inl (Set.mem_iUnion.mpr ⟨k, hwSk⟩))
  have hFanti : Anticomplete G F (A \ F) := by
    intro x hxF y hy hadj
    by_cases hyL : y ∈ striationVertices S T
    · rcases hyL with hyS | hyT
      · have hyatt : y ∈ attachments G F (striationVertices S T) :=
          ⟨Or.inl hyS, x, hxF, hadj.symm⟩
        exact hy.1 (Or.inl (hatt hyatt))
      · exact hManti x (hF.1 hxF) y hyT hadj
    · have hyM : y ∈ M := by rw [hpart]; exact hyL
      exact hy.2 (component_add_adjacent hF hxF hyM hadj)
  have hAeq : A = F ∪ (A \ F) := by
    ext x
    constructor
    · intro hxA
      by_cases hxF : x ∈ F
      · exact Or.inl hxF
      · exact Or.inr ⟨hxA, hxF⟩
    · rintro (hxF | hx)
      · exact hFsubA hxF
      · exact hx.1
  have hAncon : ¬ ConnectedSet G A :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      hAeq hFne hrestne Set.disjoint_sdiff_right hFanti
  have hSine : (stripVertices (S i)).Nonempty :=
    ⟨(left_nonempty (hL.1 i)).choose,
      left_subset_stripVertices _ (left_nonempty (hL.1 i)).choose_spec⟩
  have hznotS : z ∉ stripVertices (S i) :=
    fun hzS => Set.disjoint_left.mp (hL.2.2.2.2.1 i j) hzS hzT
  have hantiC : Anticomplete Gᶜ (stripVertices (S i)) ({z} : Set V) := by
    intro x hx y hy hadj
    have hyz : y = z := hy
    subst y
    exact ((SimpleGraph.compl_adj G x z).mp hadj).2 (hcomplete x hx).symm
  have hBnacon : ¬ AnticonnectedSet G B :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      rfl hSine ⟨z, rfl⟩ (Set.disjoint_singleton_right.mpr hznotS) hantiC
  have hskew : IsSkewPartition G A B :=
    ⟨Set.compl_union_self B, disjoint_compl_left, hAncon, hBnacon⟩
  have hzcomp : IsAnticomponent G B ({z} : Set V) :=
    singleton_component_of_isolated (H := Gᶜ) (X := B) (Or.inr rfl) (by
      intro x hx hadj
      rcases hx with hxS | hxz
      · exact ((SimpleGraph.compl_adj G z x).mp hadj).2 (hcomplete x hxS)
      · subst x
        exact hadj.ne rfl)
  exact _root_.Workspace.Statements.S04.SPGT.thm_4_1 G hG A B hskew
    (Or.inr ⟨{z}, hzcomp, z, rfl⟩)

end Workspace.ProofLemmas.Thm96ClosingSteps
