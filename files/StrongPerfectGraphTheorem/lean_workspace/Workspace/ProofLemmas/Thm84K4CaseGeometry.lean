import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S02.Thm_2_4

/-!
# The hole and triangle arguments in the short-branch case of 8.4

The two holes in the last paragraph have the same form: a path in the changed strip,
a path in a second strip, and three further vertices. The second path may be a singleton.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm84K4CaseGeometry

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.RousselRubio.SPGT

/-- For a one-edge branch, no third vertex can have two incident edges in the union
of its end-stars. Two such edges would make a triangle in the bipartite graph. -/
theorem outside_stars_subsingleton {W : Type*} {H : SimpleGraph W}
    (hbip : H.IsBipartite) {s t v : W} (hst : H.Adj s t)
    (hvs : v ≠ s) (hvt : v ≠ t) {X : Set (Sym2 W)}
    (hX : X \ {s(s, t)} = (incidentEdges H s ∪ incidentEdges H t) \ {s(s, t)}) :
    (incidentEdges H v ∩ X).Subsingleton := by
  intro e he f hf
  have classify : ∀ e ∈ incidentEdges H v ∩ X, e = s(v, s) ∨ e = s(v, t) := by
    intro e he
    have hne : e ≠ s(s, t) := by
      intro h
      have hv := he.1.2
      rw [h, Sym2.mem_iff] at hv
      exact hv.elim hvs hvt
    have hh : e ∈ X \ {s(s, t)} := ⟨he.2, hne⟩
    rw [hX] at hh
    rcases hh.1 with hs | ht
    · exact Or.inl ((Sym2.mem_and_mem_iff hvs).mp ⟨he.1.2, hs.2⟩)
    · exact Or.inr ((Sym2.mem_and_mem_iff hvt).mp ⟨he.1.2, ht.2⟩)
  rcases classify e he with rfl | rfl <;> rcases classify f hf with rfl | rfl
  · rfl
  · exact (Thm84RungEndDictionary.no_triangle_of_bipartite hbip
      (show H.Adj v s from he.1.1) hst (show H.Adj v t from hf.1.1)).elim
  · exact (Thm84RungEndDictionary.no_triangle_of_bipartite hbip
      (show H.Adj v s from hf.1.1) hst (show H.Adj v t from he.1.1)).elim
  · rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- PAPER (8.4, printed p. 42): "but then `y` can be linked onto the triangle
`T'_1` via `R'_{1,2}` and `R_{1,4}`, contrary to 2.4."

The three paths already have only their triangle edges between them. Attaching `t`
to the first path gives a linkage, since `t` has no edges to the other two paths. -/
theorem no_neighbor_of_triangle_link
    (hG : Berge G) {P Q C : List V} {a b c t y : V}
    (hP : IsPathList G P) (hQ : IsPathList G Q) (hC : IsPathList G C)
    (ha : P.getLast? = some a) (hb : Q.head? = some b) (hc : C.head? = some c)
    (hdPQ : ∀ x ∈ P, x ∉ Q) (hdPC : ∀ x ∈ P, x ∉ C)
    (hdQC : ∀ x ∈ Q, x ∉ C)
    (hPQ : ∀ x ∈ P, ∀ z ∈ Q, G.Adj x z ↔ x = a ∧ z = b)
    (hPC : ∀ x ∈ P, ∀ z ∈ C, G.Adj x z ↔ x = a ∧ z = c)
    (hQC : ∀ x ∈ Q, ∀ z ∈ C, G.Adj x z ↔ x = b ∧ z = c)
    (htQ : t ∉ Q) (htC : t ∉ C)
    (htantiQ : ∀ x ∈ Q, ¬ G.Adj t x) (htantiC : ∀ x ∈ C, ¬ G.Adj t x)
    (hyt : G.Adj y t) (hyQ : ∃ x ∈ Q, G.Adj y x)
    (hyC : ∃ x ∈ C, G.Adj y x)
    (hya : ¬ G.Adj y a) (hybc : ¬ (G.Adj y b ∧ G.Adj y c)) :
    ∀ x ∈ P, ¬ G.Adj t x := by
  intro x hx htx
  have hconn := ConnectedSetUnionAttach.connectedSet_union_singleton
    (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hP) ⟨x, hx, htx⟩
  obtain ⟨L, hL, hsub⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hconn
    (show t ∈ {x | x ∈ P} ∪ {t} from Or.inr rfl)
    (show a ∈ {x | x ∈ P} ∪ {t} from Or.inl (PathBasics.getLast_mem ha))
  have haP := PathBasics.getLast_mem ha
  have hbQ := PathBasics.head_mem hb
  have hcC := PathBasics.head_mem hc
  have hlink : VertexCanBeLinkedOntoTriangle G y a b c := by
    refine ⟨L, Q, C, ⟨hL.1, hQ, hC⟩, ?_,
      ⟨Or.inr hL.2.2, Or.inl hb, Or.inl hc⟩, ?_,
      ⟨⟨t, PathBasics.head_mem hL.2.1, hyt⟩, hyQ, hyC⟩⟩
    · refine ⟨?_, ?_, hdQC⟩
      · intro z hz
        rcases hsub z hz with hzP | rfl
        · exact hdPQ z hzP
        · exact htQ
      · intro z hz
        rcases hsub z hz with hzP | rfl
        · exact hdPC z hzP
        · exact htC
    · refine ⟨?_, ?_, hQC⟩
      · intro z hz w hw
        constructor
        · intro hzw
          rcases hsub z hz with hzP | rfl
          · exact (hPQ z hzP w hw).mp hzw
          · exact (htantiQ w hw hzw).elim
        · rintro ⟨hz, hwz⟩
          rw [hz, hwz]
          exact (hPQ a haP b hbQ).mpr ⟨rfl, rfl⟩
      · intro z hz w hw
        constructor
        · intro hzw
          rcases hsub z hz with hzP | rfl
          · exact (hPC z hzP w hw).mp hzw
          · exact (htantiC w hw hzw).elim
        · rintro ⟨hz, hwz⟩
          rw [hz, hwz]
          exact (hPC a haP c hcC).mpr ⟨rfl, rfl⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG y a b c hlink with h | h | h
  · exact hya h.1
  · exact hya h.1
  · exact hybc h

/-- PAPER (8.4, printed p. 42): "If `r_{2,1}` has no neighbour in `R'_{1,2}`,
then ... is an odd hole, a contradiction."

Both displayed holes have the form `y-t-z-P-Q-y`. Their common parity condition is
that the lengths of `P` and `Q` have even sum. -/
theorem short_case_hole_absurd
    (hG : Berge G) {P Q : List V} {p₀ p₁ q₀ q₁ y t z : V}
    (hP : IsPathFrom G P p₀ p₁) (hQ : IsPathFrom G Q q₀ q₁)
    (hdPQ : ∀ x ∈ P, x ∉ Q)
    (hPQ : ∀ x ∈ P, ∀ w ∈ Q, G.Adj x w ↔ x = p₁ ∧ w = q₀)
    (hyP : ∀ x ∈ P, ¬ G.Adj y x)
    (hyQ : ∀ x ∈ Q, G.Adj y x ↔ x = q₁)
    (htP : ∀ x ∈ P, ¬ G.Adj t x)
    (htQ : ∀ x ∈ Q, ¬ G.Adj t x)
    (hzP : ∀ x ∈ P, G.Adj z x ↔ x = p₀)
    (hzQ : ∀ x ∈ Q, ¬ G.Adj z x)
    (hyout : y ∉ P ∧ y ∉ Q) (htout : t ∉ P ∧ t ∉ Q)
    (hzout : z ∉ P ∧ z ∉ Q)
    (hyt : G.Adj y t) (htz : G.Adj t z) (hyz : ¬ G.Adj y z)
    (hpar : Even (pathLength P + pathLength Q)) : False := by
  have hp₀ := PathBasics.head_mem hP.2.1
  have hp₁ := PathBasics.getLast_mem hP.2.2
  have hzp : G.Adj z p₀ := (hzP p₀ hp₀).mpr rfl
  have hzpath : IsPathFrom G (z :: P) z p₁ :=
    PathAttach.isPathFrom_cons hP hzp hzout.1
      (fun x hx hne hadj => hne ((hzP x hx).mp hadj))
  have htpath : IsPathFrom G (t :: z :: P) t p₁ := by
    apply PathAttach.isPathFrom_cons hzpath htz
    · simpa only [List.mem_cons, not_or] using And.intro htz.ne htout.1
    · intro x hx hne
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hne rfl).elim
      · exact htP x hx
  have hyne : y ≠ z := by
    intro h
    exact hyP p₀ hp₀ (h.symm ▸ hzp)
  have hypath : IsPathFrom G (y :: t :: z :: P) y p₁ := by
    apply PathAttach.isPathFrom_cons htpath hyt
    · simp only [List.mem_cons, not_or]
      exact ⟨hyt.ne, hyne, hyout.1⟩
    · intro x hx hne
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hne rfl).elim
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hyz
      · exact hyP x hx
  have hole : IsHoleList G ((y :: t :: z :: P) ++ Q) := by
    apply PathGlue.glue_hole hypath hQ
    · intro x hx hxQ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hyout.2 hxQ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact htout.2 hxQ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hzout.2 hxQ
      · exact hdPQ x hx hxQ
    · intro x hx w hw
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hyQ w hw]
        constructor
        · intro h; exact Or.inr ⟨rfl, h⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact (hyout.1 (h.symm ▸ hp₁)).elim
          · exact h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact iff_of_false (htQ w hw) (by
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact htout.1 (h.symm ▸ hp₁)
          · exact hyt.ne h.symm)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact iff_of_false (hzQ w hw) (by
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact hzout.1 (h.symm ▸ hp₁)
          · exact hyne h.symm)
      · rw [hPQ x hx w hw]
        constructor
        · exact Or.inl
        · rintro (h | ⟨h, -⟩)
          · exact h
          · exact (hyout.1 (h ▸ hx)).elim
    · have hplen := PathBasics.path_length_pos hP.1
      have hqlen := PathBasics.path_length_pos hQ.1
      simp only [List.length_cons]
      omega
  have hev := hG.1 _ hole
  have hplen := PathBasics.path_length_pos hP.1
  have hqlen := PathBasics.path_length_pos hQ.1
  simp only [holeLength, List.length_append, List.length_cons, Nat.even_iff] at hev
  simp only [pathLength, Nat.even_iff] at hpar
  omega

end Workspace.ProofLemmas.Thm84K4CaseGeometry
