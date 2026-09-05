import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S07.Thm_7_2

/-!
# 10.4, first step: there is no major vertex in `F`

PAPER (proof of 10.4, printed p. 61): *"If there is a major vertex `v ∈ F`, then since it has
no neighbours in `R₃`, it is adjacent to `a₁` and `b₂`, and since `v-a₁-a₃-R₃-b₃-b₂-v` is a
hole, it follows that the prism is even, contrary to the hypothesis.  So there is no major
vertex in `F`."*

The hole is assembled with `PathGlue.glue_hole` from the three-vertex path `b₂-v-a₁` and the
path `R₃`, and its length is `pathLength R₃ + 4`; `Berge` then forces `pathLength R₃` even,
and 7.2 transfers that parity to `R₁` and `R₂`, so the prism is even.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm104NoMajor

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's first sentence in the proof of 10.4: under the hypotheses of 10.4 no vertex of
`F` is major with respect to the prism. -/
theorem thm104_no_major (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ)
    (hFmaj : IsEvenPrism G a b (R 0) (R 1) (R 2) → ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (hR₃ : ∀ v ∈ attachments G F K, v ∉ R 2) :
    ∀ v ∈ F, ¬ MajorForPrism G a b v := by
  intro v hv hmaj
  obtain ⟨htA, htB, hab, hP0, hP1, hP2, h01, h02, h12⟩ := id hprism
  -- endpoints belong to their paths
  have ha0mem : a 0 ∈ R 0 := List.mem_of_mem_head? hP0.2.1
  have hb0mem : b 0 ∈ R 0 := List.mem_of_mem_getLast? hP0.2.2
  have ha1mem : a 1 ∈ R 1 := List.mem_of_mem_head? hP1.2.1
  have hb1mem : b 1 ∈ R 1 := List.mem_of_mem_getLast? hP1.2.2
  have ha2mem : a 2 ∈ R 2 := List.mem_of_mem_head? hP2.2.1
  have hb2mem : b 2 ∈ R 2 := List.mem_of_mem_getLast? hP2.2.2
  -- `v` is outside the prism
  have hvK : v ∉ K := hFK hv
  -- `v` has no neighbour in `R₃`
  have hvR2 : ∀ x ∈ R 2, ¬ G.Adj v x := by
    intro x hx hadj
    refine hR₃ x ?_ hx
    exact ⟨by rw [hK]; exact Or.inr hx, v, hv, hadj.symm⟩
  -- so `v` is adjacent to both remaining vertices of each triangle
  have key : ∀ c : Fin 3 → V,
      2 ≤ (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet v).ncard →
      ¬ G.Adj v (c 2) → G.Adj v (c 0) ∧ G.Adj v (c 1) := by
    intro c hc hc2
    constructor
    · by_contra h
      have hsub : ({c 0, c 1, c 2} : Set V) ∩ G.neighborSet v ⊆ ({c 1} : Set V) := by
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1
        rw [SimpleGraph.mem_neighborSet] at hx2
        rcases hx1 with rfl | rfl | rfl
        · exact absurd hx2 h
        · rfl
        · exact absurd hx2 hc2
      have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton] at hle
      omega
    · by_contra h
      have hsub : ({c 0, c 1, c 2} : Set V) ∩ G.neighborSet v ⊆ ({c 0} : Set V) := by
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1
        rw [SimpleGraph.mem_neighborSet] at hx2
        rcases hx1 with rfl | rfl | rfl
        · rfl
        · exact absurd hx2 h
        · exact absurd hx2 hc2
      have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton] at hle
      omega
  obtain ⟨hva0, hva1⟩ := key a hmaj.1 (hvR2 (a 2) ha2mem)
  obtain ⟨hvb0, hvb1⟩ := key b hmaj.2 (hvR2 (b 2) hb2mem)
  -- basic disequalities
  have ha0b0 : a 0 ≠ b 0 := hab 0 0
  have ha0b1 : a 0 ≠ b 1 := hab 0 1
  have ha1b1 : a 1 ≠ b 1 := hab 1 1
  have ha0a2 : a 0 ≠ a 2 := (htA 0 2 (by decide)).ne
  have hb1b2 : b 1 ≠ b 2 := (htB 1 2 (by decide)).ne
  have ha1b0 : a 1 ≠ b 0 := hab 1 0
  have ha2b1 : a 2 ≠ b 1 := hab 2 1
  have ha2b2 : a 2 ≠ b 2 := hab 2 2
  -- `a₁` and `b₂` are not on `R₃`
  have ha0R2 : a 0 ∉ R 2 := by
    intro hmem
    have := (h12 (a 1) ha1mem (a 0) hmem).mp (htA 1 0 (by decide))
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact ha0a2 h
    · exact ha1b1 h
  have hb1R2 : b 1 ∉ R 2 := by
    intro hmem
    have := (h02 (b 0) hb0mem (b 1) hmem).mp (htB 0 1 (by decide))
    rcases this with ⟨h, _⟩ | ⟨_, h⟩
    · exact ha0b0 h.symm
    · exact hb1b2 h
  have hvR2' : v ∉ R 2 := fun hmem => hvK (by rw [hK]; exact Or.inr hmem)
  -- `b₂` is not adjacent to `a₁`
  have hnb1a0 : ¬ G.Adj (b 1) (a 0) := by
    intro hadj
    rcases (h01 (a 0) ha0mem (b 1) hb1mem).mp hadj.symm with ⟨_, h⟩ | ⟨h, _⟩
    · exact ha1b1 h.symm
    · exact ha0b0 h
  -- the three-vertex path `b₂-v-a₁`
  have hpair : IsPathFrom G [v, a 0] v (a 0) :=
    ⟨PathBasics.isPathList_pair hva0, rfl, rfl⟩
  have hPpath : IsPathFrom G [b 1, v, a 0] (b 1) (a 0) := by
    refine PathAttach.isPathFrom_cons hpair hvb1.symm ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      push_neg
      refine ⟨?_, ?_⟩
      · intro h; exact hvK (by rw [hK]; exact Or.inl (Or.inr (h ▸ hb1mem)))
      · exact fun h => ha0b1 h.symm
    · intro x hx hxv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd rfl hxv
      · exact hnb1a0
  -- glue it to `R₃`
  have hhole : IsHoleList G ([b 1, v, a 0] ++ R 2) := by
    refine PathGlue.glue_hole hPpath hP2 ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hb1R2
      · exact hvR2'
      · exact ha0R2
    · intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · constructor
        · intro hadj
          rcases (h12 (b 1) hb1mem y hy).mp hadj with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h.symm ha1b1
          · exact Or.inr ⟨rfl, h⟩
        · rintro (⟨h, _⟩ | ⟨_, rfl⟩)
          · exact absurd h.symm ha0b1
          · exact (h12 (b 1) hb1mem (b 2) hb2mem).mpr (Or.inr ⟨rfl, rfl⟩)
      · constructor
        · intro hadj; exact absurd hadj (hvR2 y hy)
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact absurd (h ▸ ha0mem) (fun hm => hvK (by rw [hK]; exact Or.inl (Or.inl hm)))
          · exact absurd (h ▸ hb1mem) (fun hm => hvK (by rw [hK]; exact Or.inl (Or.inr hm)))
      · constructor
        · intro hadj
          rcases (h02 (a 0) ha0mem y hy).mp hadj with ⟨_, h⟩ | ⟨h, _⟩
          · exact Or.inl ⟨rfl, h⟩
          · exact absurd h ha0b0
        · rintro (⟨_, rfl⟩ | ⟨h, _⟩)
          · exact (h02 (a 0) ha0mem (a 2) ha2mem).mpr (Or.inl ⟨rfl, rfl⟩)
          · exact absurd h ha0b1
    · have : 0 < (R 2).length := PathBasics.path_length_pos hP2.1
      simp only [List.length_cons, List.length_nil]
      omega
  -- the hole has length `pathLength R₃ + 4`, so `R₃` is even
  have hlen2 : 0 < (R 2).length := PathBasics.path_length_pos hP2.1
  have heven2 : Even (pathLength (R 2)) := by
    have := hG.1 _ hhole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at this
    have hpl : (R 2).length = pathLength (R 2) + 1 :=
      PathBasics.length_eq_pathLength_add_one hP2.1
    rw [hpl] at this
    rcases this with ⟨k, hk⟩
    exact ⟨k - 2, by omega⟩
  -- 7.2 transfers the parity to the other two paths
  have h72 := Workspace.Statements.S07.SPGT.thm_7_2 G hG a b (R 0) (R 1) (R 2) hprism
  have heven0 : Even (pathLength (R 0)) := h72.2.mpr heven2
  have heven1 : Even (pathLength (R 1)) := h72.1.mp heven0
  exact hFmaj ⟨hprism, heven0, heven1, heven2⟩ v hv hmaj

end Workspace.ProofLemmas.Thm104NoMajor
