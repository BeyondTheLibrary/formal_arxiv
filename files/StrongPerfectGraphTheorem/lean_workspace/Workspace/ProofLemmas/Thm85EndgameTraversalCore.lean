import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm85EndgameNotions

/-!
# 8.5, claim (4): the three bullets, once the outcome of 5.8 is in strip language

The three outcomes 5.8.2.b, 5.8.2.c, 5.8.2.d that survive in claim (4) all say the same thing
about the edges leaving `F`, once the branch of `H` has been identified with an edge `ij` of
`J` (`Thm85EndgameBranchEdge.branch_edge_data`) and once the vertices of the chosen rung `R_ij`
have been set aside:

* the end `p₁` of the path is adjacent to every `N_i`-end of a chosen rung at `i` other than
  the one on `R_ij`,
* the end `p₂` is adjacent to every `N_j`-end of a chosen rung at `j` other than the one on
  `R_ij`,
* and every other edge from the path to the union of the chosen rungs runs from `p₁` to such
  an `N_i`-end or from `p₂` to such an `N_j`-end.

This module turns that data into the three printed bullets of (4).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameTraversalCore

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-- A rung meets `N_u` in exactly one vertex. -/
theorem rung_N_unique {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V}
    {N : U → Set V} {u v : U} {Q : List V} (hQ : IsUVRung G J S N u v Q)
    {x y : V} (hx : x ∈ Q) (hxN : x ∈ N u) (hy : y ∈ Q) (hyN : y ∈ N u) : x = y := by
  obtain ⟨s, -, -, -, huniq⟩ := StripSystemBasics.exists_rung_head hQ
  rw [huniq x hx hxN, huniq y hy hyN]

/-- **The three bullets of (4).** -/
theorem traversal_of_unified
    {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
    (hSN : IsJStripSystem G J S N)
    {R : U → U → List V} (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {F : Set V} {Q : List V} {p₁ p₂ : V} (hQF : F = {x : V | x ∈ Q})
    (hp₁ : p₁ ∈ F) (hp₂ : p₂ ∈ F)
    {Nc1 Nc2 : Set V} {i j : U} (hij : J.Adj i j)
    (hNc1 : Nc1 ⊆ N i) (hNc2 : Nc2 ⊆ N j)
    (hhead1 : ∀ w : U, J.Adj i w → ∃ r : V, r ∈ R i w ∧ r ∈ N i ∧ r ∈ Nc1)
    (hU1 : ∀ x ∈ Nc1, x ∉ R i j → G.Adj p₁ x)
    (hU3 : ∀ x ∈ Q, ∀ y ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}),
      y ∉ R i j → G.Adj x y → (x = p₁ ∧ y ∈ Nc1) ∨ (x = p₂ ∧ y ∈ Nc2))
    (hhead2 : ∀ w : U, J.Adj j w → ∃ r : V, r ∈ R j w ∧ r ∈ N j ∧ r ∈ Nc2)
    (hU2 : ∀ x ∈ Nc2, x ∉ R i j → G.Adj p₂ x) :
    IsTraversal G J N F p₁ p₂ R i j := by
  classical
  -- a vertex of a rung at an edge different from `ij` is not on `R_ij`
  have hnotij : ∀ (a b : U), J.Adj a b → s(a, b) ≠ s(i, j) → ∀ z : V, z ∈ R a b → z ∉ R i j := by
    intro a b hab hne z hz hzij
    exact hne (StripSystemBasics.edge_eq_of_mem_strips hSN hab hij
      (StripSystemBasics.rung_subset_strip (hR a b hab) z hz)
      (StripSystemBasics.rung_subset_strip (hR i j hij) z hzij))
  have hmemK : ∀ (a b : U), J.Adj a b → ∀ z : V, z ∈ R a b →
      z ∈ (⋃ (c : U) (d : U) (_ : J.Adj c d), {y : V | y ∈ R c d}) := by
    intro a b hab z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a, b, hab, hz⟩
  refine ⟨hij, ?_, ?_, ?_⟩
  · -- first bullet
    intro w hwj hiw
    obtain ⟨r, hrR, hrN, hrNc⟩ := hhead1 w hiw
    have hne : s(i, w) ≠ s(i, j) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hwj h2
      · exact hij.ne h1
    have hrnot : r ∉ R i j := hnotij i w hiw hne r hrR
    refine ⟨r, hrR, hrN, hrR, hp₁, (hU1 r hrNc hrnot).symm, ?_⟩
    intro a haR f hfF hadj
    have hfQ : f ∈ Q := by rw [hQF] at hfF; exact hfF
    have hanot : a ∉ R i j := hnotij i w hiw hne a haR
    rcases hU3 f hfQ a (hmemK i w hiw a haR) hanot hadj.symm with ⟨hfp, haNc⟩ | ⟨hfp, haNc⟩
    · refine ⟨?_, hfp⟩
      exact rung_N_unique (hR i w hiw) haR (hNc1 haNc) hrR hrN
    · exfalso
      have h1 : a ∈ S i w ∩ N j :=
        ⟨StripSystemBasics.rung_subset_strip (hR i w hiw) a haR, hNc2 haNc⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hiw hij.ne.symm
        (fun h => hwj h.symm)] at h1
      exact h1
  · -- second bullet
    intro w hwi hjw
    obtain ⟨r, hrR, hrN, hrNc⟩ := hhead2 w hjw
    have hne : s(j, w) ≠ s(i, j) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hij.ne h1.symm
      · exact hwi h2
    have hrnot : r ∉ R i j := hnotij j w hjw hne r hrR
    refine ⟨r, hrR, hrN, hrR, hp₂, (hU2 r hrNc hrnot).symm, ?_⟩
    intro a haR f hfF hadj
    have hfQ : f ∈ Q := by rw [hQF] at hfF; exact hfF
    have hanot : a ∉ R i j := hnotij j w hjw hne a haR
    rcases hU3 f hfQ a (hmemK j w hjw a haR) hanot hadj.symm with ⟨hfp, haNc⟩ | ⟨hfp, haNc⟩
    · exfalso
      have h1 : a ∈ S j w ∩ N i :=
        ⟨StripSystemBasics.rung_subset_strip (hR j w hjw) a haR, hNc1 haNc⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hjw hij.ne
        (fun h => hwi h.symm)] at h1
      exact h1
    · refine ⟨?_, hfp⟩
      exact rung_N_unique (hR j w hjw) haR (hNc2 haNc) hrR hrN
  · -- third bullet
    intro u v huv hnd a haR f hfF hadj
    have hfQ : f ∈ Q := by rw [hQF] at hfF; exact hfF
    have hne : s(u, v) ≠ s(i, j) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp at hnd
    have hanot : a ∉ R i j := hnotij u v huv hne a haR
    have hiuv : i ≠ u ∧ i ≠ v ∧ j ≠ u ∧ j ≠ v := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or] at hnd
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> tauto
    rcases hU3 f hfQ a (hmemK u v huv a haR) hanot hadj.symm with ⟨-, haNc⟩ | ⟨-, haNc⟩
    · have h1 : a ∈ S u v ∩ N i :=
        ⟨StripSystemBasics.rung_subset_strip (hR u v huv) a haR, hNc1 haNc⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hiuv.1 hiuv.2.1] at h1
      exact h1
    · have h1 : a ∈ S u v ∩ N j :=
        ⟨StripSystemBasics.rung_subset_strip (hR u v huv) a haR, hNc2 haNc⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hiuv.2.2.1 hiuv.2.2.2] at h1
      exact h1

end Workspace.ProofLemmas.Thm85EndgameTraversalCore
