import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85EndgameNotions

/-!
# Proof of claim (5) in theorem 8.5

The key point is the redundancy supplied by a traversal.  After forbidding one edge of `J`,
there are still two disjoint edges, one at each end of the traversal.  Their selected rungs
meet the attachment set.  Thus changing one selected rung preserves broadness.  A finite
induction changes all rungs one at a time.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Claim5Proof

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

private theorem exists_mem_ne_pair {α : Type*} {t : Set α} (ht : 3 ≤ t.ncard) (a b : α) :
    ∃ x ∈ t, x ≠ a ∧ x ≠ b := by
  by_contra h
  push_neg at h
  have hsub : t ⊆ ({a, b} : Set α) := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (h x hx hxa)
  have hcard : t.ncard ≤ ({a, b} : Set α).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hp : ({a, b} : Set α).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le a ({b} : Set α)
  omega

private theorem other_eq_of_edge_eq {α : Type*} {a b c : α} (hab : a ≠ b)
    (h : s(a, b) = s(a, c)) : b = c := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.2
  · exact (hab h.2.symm).elim

/-- At the two ends of an edge in a 3-connected graph, one can select disjoint incident
edges while avoiding one prescribed edge. -/
theorem exists_disjoint_edges_at_ends_avoiding {U : Type*} [Fintype U]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) {i j : U} (hij : J.Adj i j)
    (e : Sym2 U) :
    ∃ w w' : U, J.Adj i w ∧ J.Adj j w' ∧ [i, w, j, w'].Nodup ∧
      s(i, w) ≠ e ∧ s(j, w') ≠ e := by
  classical
  obtain ⟨w, w', hiw, hjw', hnd⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_disjoint_edges_at_ends hJ hij
  have hdistinct : i ≠ w ∧ i ≠ j ∧ i ≠ w' ∧ w ≠ j ∧ w ≠ w' ∧ j ≠ w' := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  by_cases hleft : s(i, w) = e
  · have hdegi : 3 ≤ (J.neighborSet i).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ i
    obtain ⟨z, hiz, hzj, hzw⟩ := exists_mem_ne_pair hdegi j w
    have hdegj : 3 ≤ (J.neighborSet j).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ j
    obtain ⟨z', hjz', hz'i, hz'z⟩ := exists_mem_ne_pair hdegj i z
    have hnewnd : [i, z, j, z'].Nodup := by
      simp [hiz.ne, hij.ne, hz'i.symm, hzj, hz'z.symm, hjz'.ne]
    refine ⟨z, z', hiz, hjz', hnewnd, ?_, ?_⟩
    · intro heq
      have hzw' : z = w := other_eq_of_edge_eq hiz.ne (heq.trans hleft.symm)
      exact hzw hzw'
    · intro heq
      have hedge : s(j, z') = s(i, w) := heq.trans hleft.symm
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hij.ne h.1.symm
      · exact hdistinct.2.2.2.1 h.1.symm
  · by_cases hright : s(j, w') = e
    · have hdegj : 3 ≤ (J.neighborSet j).ncard :=
        SubdivisionCounting.three_le_degree_of_three_connected J hJ j
      obtain ⟨z', hjz', hz'i, hz'w'⟩ := exists_mem_ne_pair hdegj i w'
      have hdegi : 3 ≤ (J.neighborSet i).ncard :=
        SubdivisionCounting.three_le_degree_of_three_connected J hJ i
      obtain ⟨z, hiz, hzj, hzz'⟩ := exists_mem_ne_pair hdegi j z'
      have hnewnd : [i, z, j, z'].Nodup := by
        simp [hiz.ne, hij.ne, hz'i.symm, hzj, hzz', hjz'.ne]
      refine ⟨z, z', hiz, hjz', hnewnd, ?_, ?_⟩
      · intro heq
        have hedge : s(i, z) = s(j, w') := heq.trans hright.symm
        rcases Sym2.eq_iff.mp hedge with h | h
        · exact hij.ne h.1
        · exact hdistinct.2.2.1 h.1
      · intro heq
        have hzw' : z' = w' := other_eq_of_edge_eq hjz'.ne (heq.trans hright.symm)
        exact hz'w' hzw'
    · exact ⟨w, w', hiw, hjw', hnd, hleft, hright⟩

/-- A traversal supplies two disjoint selected rungs meeting the attachment set, and the two
edges can be chosen to avoid any one prescribed edge. -/
theorem traversal_has_disjoint_meeting_rungs_avoiding
    {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (R : U → U → List V) (hR : RungChoice G J S N R) (i j : U)
    (hij : IsTraversal G J N F f₁ fn R i j) (e : Sym2 U) :
    ∃ w w' : U, J.Adj i w ∧ J.Adj j w' ∧ [i, w, j, w'].Nodup ∧
      s(i, w) ≠ e ∧ s(j, w') ≠ e ∧
      (∃ x ∈ attachments G F (stripSystemVertices J S), x ∈ R i w) ∧
      ∃ x ∈ attachments G F (stripSystemVertices J S), x ∈ R j w' := by
  classical
  obtain ⟨w, w', hiw, hjw', hnd, hiwe, hjw'e⟩ :=
    exists_disjoint_edges_at_ends_avoiding J hJ hij.1 e
  have hdistinct : i ≠ w ∧ i ≠ j ∧ i ≠ w' ∧ w ≠ j ∧ w ≠ w' ∧ j ≠ w' := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨r, hrR, hrNi, hrEdge⟩ := hij.2.1 w hdistinct.2.2.2.1 hiw
  obtain ⟨r', hr'R, hr'Nj, hr'Edge⟩ := hij.2.2.1 w' hdistinct.2.2.1.symm hjw'
  have hrV : r ∈ stripSystemVertices J S := by
    obtain ⟨-, -, -, -, hsub, -, -⟩ := hR.1 i w hiw
    exact StripSystemBasics.strip_subset_vertices hiw (hsub r hrR)
  have hr'V : r' ∈ stripSystemVertices J S := by
    obtain ⟨-, -, -, -, hsub, -, -⟩ := hR.1 j w' hjw'
    exact StripSystemBasics.strip_subset_vertices hjw' (hsub r' hr'R)
  refine ⟨w, w', hiw, hjw', hnd, hiwe, hjw'e, ⟨r, ?_, hrR⟩, r', ?_, hr'R⟩
  · exact ⟨hrV, f₁, hf₁, hrEdge.2.2.1⟩
  · exact ⟨hr'V, fn, hfn, hr'Edge.2.2.1⟩

/-- Replacing the rung on at most one unoriented edge preserves broadness. -/
theorem broad_of_single_edge_change
    {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (R R' : U → U → List V) (hR' : RungChoice G J S N R')
    (e : Sym2 U)
    (hsame : ∀ u v : U, J.Adj u v → s(u, v) ≠ e → R' u v = R u v)
    (hBroad : BroadChoice G J S N
      (attachments G F (stripSystemVertices J S)) R)
    (hclaim4 : ∀ Q : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Q →
      HasUniqueTraversal G J N F f₁ fn Q) :
    BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R' := by
  obtain ⟨i, j, hij, -⟩ := hclaim4 R hBroad
  obtain ⟨w, w', hiw, hjw', hnd, hiwe, hjw'e, hmeet, hmeet'⟩ :=
    traversal_has_disjoint_meeting_rungs_avoiding
      G J hJ S N hSN F f₁ fn hf₁ hfn R hBroad.1 i j hij e
  refine ⟨hR', i, w, j, w', hiw, hjw', hnd, ?_, ?_⟩
  · obtain ⟨x, hx, hxR⟩ := hmeet
    exact ⟨x, hx, by rwa [hsame i w hiw hiwe]⟩
  · obtain ⟨x, hx, hxR⟩ := hmeet'
    exact ⟨x, hx, by rwa [hsame j w' hjw' hjw'e]⟩

/-- PAPER (proof of 8.5, claim (5), printed pp. 43–44):

*"Consequently, if we take another choice of rungs, differing from this one on only one edge,
then it too is broad. It follows that every choice is broad."* -/
theorem every_choice_broad {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hBroadExists : ∃ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R) :
    ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R := by
  classical
  obtain ⟨R₀, hR₀Broad⟩ := hBroadExists
  intro R₁ hR₁
  let mix : Finset (Sym2 U) → U → U → List V := fun A u v =>
    if s(u, v) ∈ A then R₁ u v else R₀ u v
  have hmixChoice : ∀ A : Finset (Sym2 U), RungChoice G J S N (mix A) := by
    intro A
    constructor
    · intro u v huv
      by_cases hmem : s(u, v) ∈ A
      · simpa [mix, hmem] using hR₁.1 u v huv
      · simpa [mix, hmem] using hR₀Broad.1.1 u v huv
    · intro u v huv
      have hswap : s(v, u) = s(u, v) := Sym2.eq_swap
      by_cases hmem : s(u, v) ∈ A
      · simp only [mix, hmem, if_true]
        rw [hswap, if_pos hmem]
        exact hR₁.2 u v huv
      · simp only [mix, hmem, if_false]
        rw [hswap, if_neg hmem]
        exact hR₀Broad.1.2 u v huv
  have hmixBroad : ∀ A : Finset (Sym2 U),
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) (mix A) := by
    intro A
    induction A using Finset.induction with
    | empty =>
        obtain ⟨-, i, j, h, k, hij, hhk, hnd, hmeet, hmeet'⟩ := hR₀Broad
        refine ⟨hmixChoice ∅, i, j, h, k, hij, hhk, hnd, ?_, ?_⟩
        · simpa [mix] using hmeet
        · simpa [mix] using hmeet'
    | @insert e A he ih =>
        apply broad_of_single_edge_change G J hJ S N hSN F f₁ fn hf₁ hfn
          (mix A) (mix (insert e A)) (hmixChoice (insert e A)) e
        · intro u v huv hne
          simp [mix, hne]
        · exact ih
        · exact hclaim4
  obtain ⟨-, i, j, h, k, hij, hhk, hnd, hmeet, hmeet'⟩ := hmixBroad J.edgeFinset
  refine ⟨hR₁, i, j, h, k, hij, hhk, hnd, ?_, ?_⟩
  · have hedge : s(i, j) ∈ J.edgeFinset := by simpa using hij
    simpa [mix, hedge] using hmeet
  · have hedge : s(h, k) ∈ J.edgeFinset := by simpa using hhk
    simpa [mix, hedge] using hmeet'

end Workspace.ProofLemmas.Thm85Claim5Proof
