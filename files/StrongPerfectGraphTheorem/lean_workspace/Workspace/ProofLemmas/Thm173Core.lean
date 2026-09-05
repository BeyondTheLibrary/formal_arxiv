import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Classes
import Workspace.Statements.S17.Thm_17_2
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S02.Thm_2_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm114Aux
import Workspace.ProofLemmas.ComponentsOfSetBasics

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The asymmetric strip lemma 17.3

The connected case is an application of 17.2.  In the other case the paper
splits `F \ {b}` into its component containing `a` and all remaining
components.  The three lemmas below match the three sentences in that part of
the proof.
-/

namespace Workspace.ProofLemmas.Thm173Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_eq_index {W : Type*} (l : List W) {i j : ℕ}
    (h : i = j) (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst j
  rfl

/-- The data carried by the component split in the proof of 17.3.  The two
blocks cover `F`, meet only at the cut vertex `b`, and their parts away from
`b` have no edge between them. -/
structure CutSplit (G : SimpleGraph V) (F : Set V) (a b : V)
    (F₁ F₂ : Set V) : Prop where
  cover : F = F₁ ∪ F₂
  inter : F₁ ∩ F₂ = {b}
  a_mem : a ∈ F₁
  b_mem_left : b ∈ F₁
  b_mem_right : b ∈ F₂
  a_notMem_right : a ∉ F₂
  left_subset : F₁ ⊆ F
  right_subset : F₂ ⊆ F
  left_connected : ConnectedSet G F₁
  right_connected : ConnectedSet G F₂
  left_without_a_connected : ConnectedSet G (F₁ \ {a})
  left_without_b_connected : ConnectedSet G (F₁ \ {b})
  separated : Anticomplete G (F₁ \ {b}) (F₂ \ {b})

/-- PAPER (proof of 17.3, printed p. 104):

> *"Assume `F \ {b}` is not [connected], and let `F₁'` be the component of
> `F \ {b}` that contains `a`, and `F₂'` the union of all the other
> components. For `i = 1,2` let `Fᵢ = Fᵢ' ∪ {b}`. Then
> `F₁ \ {a}`, `F₁ \ {b}` are both connected."*

The conclusion also records the cover and the separation of the two families
of components, which are part of this construction. -/
theorem componentSplit (G : SimpleGraph V) (F : Set V) (a b : V)
    (hF : ConnectedSet G F) (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b)
    (hFa : ConnectedSet G (F \ {a})) (hnotFb : ¬ ConnectedSet G (F \ {b})) :
    ∃ F₁ F₂ : Set V, CutSplit G F a b F₁ F₂ := by
  classical
  let A : Set V := F \ {b}
  have haA : a ∈ A := ⟨ha, by simpa using hab⟩
  have hbA : b ∉ A := by simp [A]
  obtain ⟨C, hC, haC⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G A haA

  have component_no_edge : ∀ {Q : Set V}, IsComponent G A Q →
      ∀ x ∈ Q, ∀ y ∈ A, y ∉ Q → ¬ G.Adj x y := by
    intro Q hQ x hxQ y hyA hyQ hxy
    have hconn : ConnectedSet G (Q ∪ {y}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
        hQ.2.1 ⟨x, hxQ, hxy.symm⟩
    have heq : Q ∪ {y} = Q := hQ.2.2 (Q ∪ {y}) Set.subset_union_left
      (Set.union_subset hQ.1 (Set.singleton_subset_iff.mpr hyA)) hconn
    exact hyQ (by rw [← heq]; simp)

  have component_attaches_b : ∀ (Q : Set V), IsComponent G A Q → Q.Nonempty →
      ∃ q ∈ Q, G.Adj b q := by
    intro Q hQ hQne
    obtain ⟨q, hqQ⟩ := hQne
    have hQF : Q ⊆ F := fun x hx => (hQ.1 hx).1
    have hbQ : b ∉ Q := fun h => hbA (hQ.1 h)
    obtain ⟨x, hxF, hxQ, y, hyQ, hxy⟩ :=
      Workspace.ProofLemmas.Thm114Aux.exists_cross_edge hF hQF hqQ hb hbQ
    have hxb : x = b := by
      by_contra hxne
      have hxA : x ∈ A := ⟨hxF, by simpa using hxne⟩
      exact component_no_edge hQ y hyQ x hxA hxQ hxy.symm
    exact ⟨y, hyQ, by simpa [hxb] using hxy⟩

  let F₁ : Set V := C ∪ {b}
  let F₂ : Set V := (A \ C) ∪ {b}
  have hbC : b ∉ C := fun h => hbA (hC.1 h)
  have hCne : C.Nonempty := ⟨a, haC⟩
  have hF₁conn : ConnectedSet G F₁ :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
      hC.2.1 (component_attaches_b C hC hCne)

  have hF₂conn : ConnectedSet G F₂ := by
    let bb : ↑F₂ := ⟨b, Or.inr (by simp)⟩
    have key : ∀ u : ↑F₂, (G.induce F₂).Reachable u bb := by
      intro u
      rcases u.2 with huAC | hub
      · obtain ⟨Q, hQ, huQ⟩ :=
          Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G A huAC.1
        have hQC : Q ≠ C := by
          intro heq
          subst Q
          exact huAC.2 huQ
        have hdisj := Workspace.ProofLemmas.ComponentsOfSetBasics.disjoint_of_isComponent
          G hQ hC hQC
        have hQF₂ : Q ⊆ F₂ := by
          intro q hqQ
          exact Or.inl ⟨hQ.1 hqQ, fun hqC => Set.disjoint_left.mp hdisj hqQ hqC⟩
        obtain ⟨q, hqQ, hbq⟩ := component_attaches_b Q hQ ⟨u, huQ⟩
        have huq : (G.induce F₂).Reachable u ⟨q, hQF₂ hqQ⟩ := by
          obtain ⟨w⟩ := hQ.2.1 ⟨u, huQ⟩ ⟨q, hqQ⟩
          exact ⟨SimpleGraph.Walk.map
            (⟨fun z => ⟨z.1, hQF₂ z.2⟩, fun {_ _} hadj => hadj⟩ :
              (G.induce Q) →g (G.induce F₂)) w⟩
        have hqb : (G.induce F₂).Adj ⟨q, hQF₂ hqQ⟩ bb := hbq.symm
        exact huq.trans hqb.reachable
      · have hub' : (u : V) = b := by simpa using hub
        have : u = bb := Subtype.ext hub'
        rw [this]
    intro u v
    exact (key u).trans (key v).symm

  have hF₁aConn : ConnectedSet G (F₁ \ {a}) := by
    have heq : F₁ \ {a} = (C \ {a}) ∪ {b} := by
      ext x
      simp only [F₁, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxC | hxb, hxa⟩
        · exact Or.inl ⟨hxC, hxa⟩
        · exact Or.inr hxb
      · rintro (⟨hxC, hxa⟩ | hxb)
        · exact ⟨Or.inl hxC, hxa⟩
        · exact ⟨Or.inr hxb, by simpa [hxb] using hab.symm⟩
    rw [heq]
    let B : Set V := C \ {a}
    let D : Set V := B ∪ {b}
    have hbFa : b ∈ F \ {a} := ⟨hb, by simpa using hab.symm⟩
    have componentB_attaches_b : ∀ (Q : Set V), IsComponent G B Q → Q.Nonempty →
        ∃ q ∈ Q, G.Adj b q := by
      intro Q hQ hQne
      obtain ⟨q, hqQ⟩ := hQne
      have hQFa : Q ⊆ F \ {a} := by
        intro z hzQ
        have hzB := hQ.1 hzQ
        exact ⟨(hC.1 hzB.1).1, hzB.2⟩
      have hbQ : b ∉ Q := fun h => hbC (hQ.1 h).1
      obtain ⟨x, hxFa, hxQ, y, hyQ, hxy⟩ :=
        Workspace.ProofLemmas.Thm114Aux.exists_cross_edge hFa hQFa hqQ hbFa hbQ
      have hxb : x = b := by
        by_contra hxne
        have hxA : x ∈ A := ⟨hxFa.1, by simpa using hxne⟩
        have hyC : y ∈ C := (hQ.1 hyQ).1
        have hxC : x ∈ C := by
          by_contra hxc
          exact component_no_edge hC y hyC x hxA hxc hxy.symm
        have hxB : x ∈ B := ⟨hxC, hxFa.2⟩
        have hconn : ConnectedSet G (Q ∪ {x}) :=
          Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
            hQ.2.1 ⟨y, hyQ, hxy⟩
        have heq : Q ∪ {x} = Q := hQ.2.2 (Q ∪ {x}) Set.subset_union_left
          (Set.union_subset hQ.1 (Set.singleton_subset_iff.mpr hxB)) hconn
        exact hxQ (by rw [← heq]; simp)
      exact ⟨y, hyQ, by simpa [hxb] using hxy⟩
    have hDconn : ConnectedSet G D := by
      let bb : ↑D := ⟨b, Or.inr (by simp)⟩
      have key : ∀ u : ↑D, (G.induce D).Reachable u bb := by
        intro u
        rcases u.2 with huB | hub
        · obtain ⟨Q, hQ, huQ⟩ :=
            Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G B huB
          have hQD : Q ⊆ D := fun q hq => Or.inl (hQ.1 hq)
          obtain ⟨q, hqQ, hbq⟩ := componentB_attaches_b Q hQ ⟨u, huQ⟩
          have huq : (G.induce D).Reachable u ⟨q, hQD hqQ⟩ := by
            obtain ⟨w⟩ := hQ.2.1 ⟨u, huQ⟩ ⟨q, hqQ⟩
            exact ⟨SimpleGraph.Walk.map
              (⟨fun z => ⟨z.1, hQD z.2⟩, fun {_ _} hadj => hadj⟩ :
                (G.induce Q) →g (G.induce D)) w⟩
          have hqb : (G.induce D).Adj ⟨q, hQD hqQ⟩ bb := hbq.symm
          exact huq.trans hqb.reachable
        · have hub' : (u : V) = b := by simpa using hub
          have : u = bb := Subtype.ext hub'
          rw [this]
      intro u v
      exact (key u).trans (key v).symm
    exact hDconn

  refine ⟨F₁, F₂, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF₁conn, hF₂conn, hF₁aConn, ?_, ?_⟩
  · ext x
    constructor
    · intro hxF
      by_cases hxb : x = b
      · exact Or.inl (Or.inr hxb)
      · have hxA : x ∈ A := ⟨hxF, hxb⟩
        by_cases hxC : x ∈ C
        · exact Or.inl (Or.inl hxC)
        · exact Or.inr (Or.inl ⟨hxA, hxC⟩)
    · rintro (hx₁ | hx₂)
      · rcases hx₁ with hxC | hxb
        · exact (hC.1 hxC).1
        · rw [hxb]
          exact hb
      · rcases hx₂ with hxAC | hxb
        · exact hxAC.1.1
        · rw [hxb]
          exact hb
  · ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      rcases hx₁ with hxC | hxb
      · rcases hx₂ with hxAC | hxb
        · exact False.elim (hxAC.2 hxC)
        · simpa using hxb
      · simpa using hxb
    · intro hxb
      have hxb' : x = b := by simpa using hxb
      exact ⟨Or.inr hxb', Or.inr hxb'⟩
  · exact Or.inl haC
  · exact Or.inr rfl
  · exact Or.inr rfl
  · rintro (haAC | heq)
    · exact haAC.2 haC
    · exact hab heq
  · rintro x (hxC | rfl)
    · exact (hC.1 hxC).1
    · exact hb
  · rintro x (hxAC | rfl)
    · exact hxAC.1.1
    · exact hb
  · have heq : F₁ \ {b} = C := by
      ext x
      simp only [F₁, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxC | hxb, hxne⟩
        · exact hxC
        · exact False.elim (hxne hxb)
      · intro hxC
        exact ⟨Or.inl hxC, fun h => hbC (h ▸ hxC)⟩
    rw [heq]
    exact hC.2.1
  · intro x hx₁ y hx₂ hadj
    have hxC : x ∈ C := by
      rcases hx₁.1 with h | h
      · exact h
      · exact False.elim (hx₁.2 h)
    have hyAC : y ∈ A \ C := by
      rcases hx₂.1 with h | h
      · exact h
      · exact False.elim (hx₂.2 h)
    exact component_no_edge hC x hxC y hyAC.1 hyAC.2 hadj

/-- Remove the endpoint `v` from a path from an outside vertex `u` into a
connected set.  The remaining path ends at `u`, stays in `A \ {v}` apart from
`u`, and has a neighbour of `v`. -/
private theorem attachedPathWithoutEndpoint (G : SimpleGraph V) (A : Set V)
    (u v : V) (hA : ConnectedSet G A) (hvA : v ∈ A) (huA : u ∉ A)
    (huv : u ≠ v) (hu : ∃ x ∈ A, G.Adj u x) :
    ∃ p : List V, IsPathList G p ∧ p.head? = some u ∧
      (∀ x ∈ p, x ∈ A \ {v} ∨ x = u) ∧ ∃ x ∈ p, G.Adj v x := by
  obtain ⟨q, hq, hqmem, -⟩ :=
    Workspace.ProofLemmas.SkewPartitionFromSeparator.exists_path_of_connected_attach
      hA (Or.inr hu) (Or.inl hvA)
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    rcases (show q.length = 1 ∨ 2 ≤ q.length by omega) with h | h
    · exfalso
      obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp h
      have hzu : z = u := by simpa using hq.2.1
      have hzv : z = v := by simpa using hq.2.2
      exact huv (hzu.symm.trans hzv)
    · exact h
  have hlast : q.getLast hq.1.1 = v := by
    simpa [List.getLast?_eq_some_getLast hq.1.1] using hq.2.2
  let p := q.dropLast
  have hp : IsPathList G p := by
    change IsPathList G q.dropLast
    rw [List.dropLast_eq_take]
    exact Workspace.ProofLemmas.PathBasics.isPathList_take hq.1 (by omega)
  have hphead : p.head? = some u := by
    change q.dropLast.head? = some u
    rw [List.head?_dropLast, if_pos (by omega), hq.2.1]
  have hpmem : ∀ x ∈ p, x ∈ A \ {v} ∨ x = u := by
    intro x hx
    have hxq : x ∈ q ∧ x ≠ q.getLast hq.1.1 :=
      (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hq.1.2.1 hq.1.1).mp hx
    rcases hqmem x hxq.1 with hxA | hxu | hxv
    · exact Or.inl ⟨hxA, by simpa [hlast] using hxq.2⟩
    · exact Or.inr hxu
    · exact False.elim (hxq.2 (by simpa [hlast, hxv]))
  let x := q[q.length - 2]'(by omega)
  have hxq : x ∈ q := List.getElem_mem _
  have hxne : x ≠ q.getLast hq.1.1 := by
    intro he
    have hlastElem : q[q.length - 1]'(by omega) = v :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 (by omega)
    have hxeq : x = q[q.length - 1]'(by omega) := by simpa [hlastElem, hlast] using he
    exact (by
      have := hq.1.2.1.getElem_inj_iff.mp hxeq
      omega)
  have hxp : x ∈ p :=
    (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hq.1.2.1 hq.1.1).mpr ⟨hxq, hxne⟩
  have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hq.1
    (i := q.length - 2) (by omega)
  have hlastElem : q[q.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 (by omega)
  have hidx : q.length - 2 + 1 = q.length - 1 := by omega
  have helem : q[q.length - 2 + 1]'(by omega) = q[q.length - 1]'(by omega) := by
    exact getElem_eq_index q hidx (by omega) (by omega)
  rw [helem, hlastElem] at hadj
  exact ⟨p, hp, hphead, hpmem, x, hxp, hadj.symm⟩

/-- Two distinct vertices of the first triangle have adjacent partners in a
reflection. -/
private theorem reflectionPair {G : SimpleGraph V}
    {a₁ a₂ a₃ b₁ b₂ b₃ u v : V}
    (h : IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃)
    (hu : u ∈ ({a₁, a₂, a₃} : Set V))
    (hv : v ∈ ({a₁, a₂, a₃} : Set V)) (huv : u ≠ v) :
    ∃ bu ∈ ({b₁, b₂, b₃} : Set V), ∃ bv ∈ ({b₁, b₂, b₃} : Set V),
      G.Adj u bu ∧ G.Adj v bv ∧ G.Adj bu bv := by
  obtain ⟨-, hB, -, hiff⟩ := h
  have hbne : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ := by
    have hcard := hB.1
    have hpair : ∀ a b : V, ({a, b} : Set V).ncard ≤ 2 := by
      intro a b
      have hh := Set.ncard_insert_le a ({b} : Set V)
      simpa using hh
    refine ⟨?_, ?_, ?_⟩ <;> intro he
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
        ext t
        simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₂ b₃; omega)
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
        ext t
        simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₂ b₃; omega)
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₁, b₃} : Set V) := by
        ext t
        simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₁ b₃; omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact ⟨b₁, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.1⟩
  · exact ⟨b₁, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.1⟩
  · exact ⟨b₂, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hbne.1.symm⟩
  · exact absurd rfl huv
  · exact ⟨b₂, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.2⟩
  · exact ⟨b₃, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hbne.2.1.symm⟩
  · exact ⟨b₃, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.2.symm⟩
  · exact absurd rfl huv

/-- PAPER (proof of 17.3, printed p. 104):

> *"If `y` has a neighbour in `F₂` then `b` can be linked onto the triangle
> `{y,a₀,b₀}`, a contradiction to 2.4."*

Here `y` has no neighbour in `F₁`, as supplied by the first outcome of
17.2 applied to `F₁`. -/
theorem outsideNeighborContradictsLink
    (G : SimpleGraph V) (hG : InF7 G) (F Y F₁ F₂ : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hsplit : CutSplit G F a b F₁ F₂)
    (y : V) (hyY : y ∈ Y) (hyF₁ : VertexAnticomplete G y F₁)
    (hyF₂ : ∃ f ∈ F₂, G.Adj y f) : False := by
  classical
  have haa₀ : G.Adj a a₀ := (hpath.2.2 0 1 (by simp) (by simp)).2 (by simp)
  have ha₀b₀ : G.Adj a₀ b₀ := (hpath.2.2 1 2 (by simp) (by simp)).2 (by simp)
  have hb₀b : G.Adj b₀ b := (hpath.2.2 2 3 (by simp) (by simp)).2 (by simp)
  have hna₀b : ¬ G.Adj a₀ b := by
    intro hadj
    have := (hpath.2.2 1 3 (by simp) (by simp)).1 hadj
    simp at this
  have hyF : y ∉ F := fun hy => Set.disjoint_left.mp hFY hy hyY
  have hyF₂out : y ∉ F₂ := fun hy => hyF (hsplit.right_subset hy)
  have ha₀F₁out : a₀ ∉ F₁ := fun hx => ha₀ (Or.inl (hsplit.left_subset hx))
  have hyb : ¬ G.Adj y b := hyF₁ b hsplit.b_mem_left
  have hyne_b : y ≠ b := fun he => hyF (he ▸ hb)
  have ha₀ne_b : a₀ ≠ b := fun he => ha₀ (Or.inl (he.symm ▸ hb))
  obtain ⟨pY, hpY, hpYhead, hpYmem, hbPY⟩ :=
    attachedPathWithoutEndpoint G F₂ y b hsplit.right_connected hsplit.b_mem_right
      hyF₂out hyne_b hyF₂
  obtain ⟨pA, hpA, hpAhead, hpAmem, hbPA⟩ :=
    attachedPathWithoutEndpoint G F₁ a₀ b hsplit.left_connected hsplit.b_mem_left
      ha₀F₁out ha₀ne_b ⟨a, hsplit.a_mem, haa₀.symm⟩
  have hYAdisj : ∀ x ∈ pY, x ∉ pA := by
    intro x hxY hxA
    rcases hpYmem x hxY with hx₂ | rfl <;> rcases hpAmem x hxA with hx₁ | heq
    · have hxI : x ∈ F₁ ∩ F₂ := ⟨hx₁.1, hx₂.1⟩
      rw [hsplit.inter] at hxI
      exact hx₂.2 (by simpa using hxI)
    · exact ha₀ (Or.inl (heq ▸ hsplit.right_subset hx₂.1))
    · exact hyF (hsplit.left_subset hx₁.1)
    · exact ha₀ (Or.inr (heq ▸ hyY))
  have hYBdisj : ∀ x ∈ pY, x ∉ [b₀] := by
    intro x hxY hxB
    have hxb₀ : x = b₀ := by simpa using hxB
    rcases hpYmem x hxY with hx₂ | hxy
    · exact hb₀ (Or.inl (hxb₀ ▸ hsplit.right_subset hx₂.1))
    · exact hb₀ (Or.inr (hxb₀ ▸ hxy ▸ hyY))
  have hABdisj : ∀ x ∈ pA, x ∉ [b₀] := by
    intro x hxA hxB
    have hxb₀ : x = b₀ := by simpa using hxB
    rcases hpAmem x hxA with hx₁ | hxa₀
    · exact hb₀ (Or.inl (hxb₀ ▸ hsplit.left_subset hx₁.1))
    · exact ha₀b₀.ne (hxa₀.symm.trans hxb₀)
  have hYA : ∀ x ∈ pY, ∀ z ∈ pA,
      (G.Adj x z ↔ x = y ∧ z = a₀) := by
    intro x hxY z hzA
    constructor
    · intro hadj
      rcases hpYmem x hxY with hx₂ | hxy <;> rcases hpAmem z hzA with hz₁ | hza₀
      · exact False.elim (hsplit.separated z hz₁ x hx₂ hadj.symm)
      · have hm : x ∈ {f ∈ F | G.Adj a₀ f} :=
          ⟨hsplit.right_subset hx₂.1, hza₀ ▸ hadj.symm⟩
        rw [ha₀F] at hm
        have hxa : x = a := by simpa using hm
        exact False.elim (hsplit.a_notMem_right (hxa ▸ hx₂.1))
      · exact False.elim (hyF₁ z hz₁.1 (hxy ▸ hadj))
      · exact ⟨hxy, hza₀⟩
    · rintro ⟨hxy, hza₀⟩
      rw [hxy, hza₀]
      exact (ha₀Y y hyY).symm
  have hYB : ∀ x ∈ pY, ∀ z ∈ [b₀],
      (G.Adj x z ↔ x = y ∧ z = b₀) := by
    intro x hxY z hzB
    have hzb₀ : z = b₀ := by simpa using hzB
    constructor
    · intro hadj
      rcases hpYmem x hxY with hx₂ | hxy
      · have hm : x ∈ {f ∈ F | G.Adj b₀ f} :=
          ⟨hsplit.right_subset hx₂.1, hzb₀ ▸ hadj.symm⟩
        rw [hb₀F] at hm
        have hxb : x = b := by simpa using hm
        exact False.elim (hx₂.2 (by simpa [hxb]))
      · exact ⟨hxy, hzb₀⟩
    · rintro ⟨hxy, hzb₀⟩
      rw [hxy, hzb₀]
      exact (hb₀Y y hyY).symm
  have hAB : ∀ x ∈ pA, ∀ z ∈ [b₀],
      (G.Adj x z ↔ x = a₀ ∧ z = b₀) := by
    intro x hxA z hzB
    have hzb₀ : z = b₀ := by simpa using hzB
    constructor
    · intro hadj
      rcases hpAmem x hxA with hx₁ | hxa₀
      · have hm : x ∈ {f ∈ F | G.Adj b₀ f} :=
          ⟨hsplit.left_subset hx₁.1, hzb₀ ▸ hadj.symm⟩
        rw [hb₀F] at hm
        have hxb : x = b := by simpa using hm
        exact False.elim (hx₁.2 (by simpa [hxb]))
      · exact ⟨hxa₀, hzb₀⟩
    · rintro ⟨rfl, rfl⟩
      exact ha₀b₀
  have hlink : VertexCanBeLinkedOntoTriangle G b y a₀ b₀ := by
    exact ⟨pY, pA, [b₀],
      ⟨⟨hpY, hpA, Workspace.ProofLemmas.PathBasics.isPathList_singleton G b₀⟩,
        ⟨hYAdisj, hYBdisj, hABdisj⟩,
        ⟨Or.inl hpYhead, Or.inl hpAhead, Or.inl rfl⟩,
        ⟨hYA, hYB, hAB⟩,
        ⟨hbPY, hbPA, ⟨b₀, by simp, hb₀b.symm⟩⟩⟩⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG.1.1.1.1 b y a₀ b₀ hlink with
    h | h | h
  · exact hyb h.1.symm
  · exact hyb h.1.symm
  · exact hna₀b h.1.symm

/-- PAPER (proof of 17.3, printed p. 104):

> *"If `y₁` has neighbours in `F₂` then `(F \ {a}) ∪ {y₂}` catches
> the triangle `{a,a₀,y₁}`; ... there is no reflection ... contrary to
> 17.1. So `y₁` has no neighbours in `F₂`."* -/
theorem outsideNeighborContradictsCatch
    (G : SimpleGraph V) (hG : InF7 G) (F Y F₁ F₂ : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hFa : ConnectedSet G (F \ {a}))
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hsplit : CutSplit G F a b F₁ F₂)
    (y₁ y₂ : V) (hy₁Y : y₁ ∈ Y) (hy₂Y : y₂ ∈ Y)
    (hy₁y₂ : ¬ G.Adj y₁ y₂)
    (hy₁F₁ : {f ∈ F₁ | G.Adj y₁ f} = {a})
    (hy₂F₁ : {f ∈ F₁ | G.Adj y₂ f} = {b})
    (hy₁F₂ : ∃ f ∈ F₂, G.Adj y₁ f) : False := by
  classical
  have haa₀ : G.Adj a a₀ := (hpath.2.2 0 1 (by simp) (by simp)).2 (by simp)
  have ha₀b₀ : G.Adj a₀ b₀ := (hpath.2.2 1 2 (by simp) (by simp)).2 (by simp)
  have hb₀b : G.Adj b₀ b := (hpath.2.2 2 3 (by simp) (by simp)).2 (by simp)
  have hnab : ¬ G.Adj a b := by
    intro hadj
    have h := (hpath.2.2 0 3 (by simp) (by simp)).1 hadj
    simp at h
  have hfour : IsPathFrom G [a, a₀, b₀, b] a b := ⟨hpath, by simp, by simp⟩
  have hab : a ≠ b :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hfour (by simp [pathLength])
  have hy₁a : G.Adj y₁ a := by
    have hm : a ∈ {f ∈ F₁ | G.Adj y₁ f} := by rw [hy₁F₁]; simp
    exact hm.2
  have hy₂b : G.Adj y₂ b := by
    have hm : b ∈ {f ∈ F₁ | G.Adj y₂ f} := by rw [hy₂F₁]; simp
    exact hm.2
  have hy₁b : ¬ G.Adj y₁ b := by
    intro hadj
    have hm : b ∈ {f ∈ F₁ | G.Adj y₁ f} := ⟨hsplit.b_mem_left, hadj⟩
    rw [hy₁F₁] at hm
    have hba : b = a := by simpa using hm
    exact hab hba.symm
  have hy₂a : ¬ G.Adj y₂ a := by
    intro hadj
    have hm : a ∈ {f ∈ F₁ | G.Adj y₂ f} := ⟨hsplit.a_mem, hadj⟩
    rw [hy₂F₁] at hm
    exact hab (by simpa using hm)
  have hy₁ne₂ : y₁ ≠ y₂ := by
    intro he
    subst y₂
    exact hy₂a hy₁a
  have hy₁Fout : y₁ ∉ F := fun hy => Set.disjoint_left.mp hFY hy hy₁Y
  have hy₂Fout : y₂ ∉ F := fun hy => Set.disjoint_left.mp hFY hy hy₂Y
  have ha₀Fout : a₀ ∉ F := fun h => ha₀ (Or.inl h)
  have ha₀Yout : a₀ ∉ Y := fun h => ha₀ (Or.inr h)

  obtain ⟨x, hxF, hxne, z, hz, hxz⟩ :=
    Workspace.ProofLemmas.Thm114Aux.exists_cross_edge hF
      (T := F) (S := ({a} : Set V)) (by simp [ha]) (s := a) (t := b)
        (by simp) hb (by simpa using hab.symm)
  have hza : z = a := by simpa using hz
  have hax : G.Adj a x := by simpa [hza] using hxz.symm

  let D : Set V := (F \ {a}) ∪ {y₂}
  let T : Set V := {a, a₀, y₁}
  have ha₀y₁ : G.Adj a₀ y₁ := ha₀Y y₁ hy₁Y
  have hT : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr
      ⟨a, a₀, y₁, haa₀.ne, hy₁a.ne.symm, ha₀y₁.ne, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact haa₀
    · exact hy₁a.symm
    · exact haa₀.symm
    · exact (huv rfl).elim
    · exact ha₀y₁
    · exact hy₁a
    · exact ha₀y₁.symm
    · exact (huv rfl).elim
  have hDconn : ConnectedSet G D := by
    exact Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
      hFa ⟨b, ⟨hb, by simpa using hab.symm⟩, hy₂b⟩
  have hDT : Disjoint D T := by
    apply Set.disjoint_left.mpr
    intro d hdD hdT
    rcases hdD with hdF | hdY₂
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hdT
      rcases hdT with rfl | rfl | rfl
      · exact hdF.2 rfl
      · exact ha₀Fout hdF.1
      · exact hy₁Fout hdF.1
    · have hdy₂ : d = y₂ := by simpa using hdY₂
      subst d
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hdT
      rcases hdT with h | h | h
      · exact hy₂Fout (h.symm ▸ ha)
      · exact ha₀Yout (h.symm ▸ hy₂Y)
      · exact hy₁ne₂ h.symm
  have hcatch : Catches G D T := by
    refine ⟨hT, hDconn, hDT, ?_⟩
    intro t ht
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨x, Or.inl ⟨hxF, hxne⟩, hax⟩
    · exact ⟨y₂, Or.inr (by simp), ha₀Y y₂ hy₂Y⟩
    · obtain ⟨f, hfF₂, hy₁f⟩ := hy₁F₂
      have hfF : f ∈ F := hsplit.right_subset hfF₂
      have hfne : f ≠ a := fun he => hsplit.a_notMem_right (he ▸ hfF₂)
      exact ⟨f, Or.inl ⟨hfF, by simpa using hfne⟩, hy₁f⟩
  have hDcompl : D ⊆ Tᶜ := by
    intro d hdD
    simpa only [Set.mem_compl_iff] using fun hdT => Set.disjoint_left.mp hDT hdD hdT

  have left_of_adj_a : ∀ {d : V}, d ∈ F \ {a} → G.Adj d a → d ∈ F₁ \ {b} := by
    intro d hd hadj
    have hdcover : d ∈ F₁ ∪ F₂ := by simpa [hsplit.cover] using hd.1
    rcases hdcover with hd₁ | hd₂
    · exact ⟨hd₁, fun he => hnab (he ▸ hadj.symm)⟩
    · have hdne : d ≠ b := fun he => hnab (he ▸ hadj.symm)
      exact False.elim (hsplit.separated a ⟨hsplit.a_mem, by simpa [hab]⟩ d
        ⟨hd₂, by simpa using hdne⟩ hadj.symm)
  have right_of_adj_y₁ : ∀ {d : V}, d ∈ F \ {a} → G.Adj d y₁ → d ∈ F₂ \ {b} := by
    intro d hd hadj
    have hdcover : d ∈ F₁ ∪ F₂ := by simpa [hsplit.cover] using hd.1
    rcases hdcover with hd₁ | hd₂
    · have hm : d ∈ {f ∈ F₁ | G.Adj y₁ f} := ⟨hd₁, hadj.symm⟩
      rw [hy₁F₁] at hm
      have hda : d = a := by simpa using hm
      exact False.elim (hd.2 (by simpa [hda]))
    · exact ⟨hd₂, fun he => hy₁b (he ▸ hadj.symm)⟩

  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T hT D hDcompl hcatch with
    href | htwo
  · obtain ⟨c₁, c₂, c₃, d₁, d₂, d₃, hTeq, hDsub, href⟩ := href
    have haT : a ∈ ({c₁, c₂, c₃} : Set V) := by rw [← hTeq]; simp [T]
    have hy₁T : y₁ ∈ ({c₁, c₂, c₃} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨da, hdaB, dy, hdyB, hada, hy₁dy, hdady⟩ :=
      reflectionPair href haT hy₁T hy₁a.ne.symm
    have hdaD : da ∈ D := hDsub hdaB
    have hdyD : dy ∈ D := hDsub hdyB
    have hdaF : da ∈ F \ {a} := by
      rcases hdaD with h | h
      · exact h
      · have he : da = y₂ := by simpa using h
        exact False.elim (hy₂a (he ▸ hada.symm))
    have hdyF : dy ∈ F \ {a} := by
      rcases hdyD with h | h
      · exact h
      · have he : dy = y₂ := by simpa using h
        exact False.elim (hy₁y₂ (he ▸ hy₁dy))
    have hdaLeft : da ∈ F₁ \ {b} := left_of_adj_a hdaF hada.symm
    have hdyRight : dy ∈ F₂ \ {b} := right_of_adj_y₁ hdyF hy₁dy.symm
    exact hsplit.separated da hdaLeft dy hdyRight hdady
  · obtain ⟨d, hdD, hdcard⟩ := htwo
    have hle : (G.neighborSet d ∩ T).ncard ≤ 1 := by
      apply (Set.ncard_le_one (Set.toFinite _)).2
      intro u hu v hv
      have hdu : G.Adj d u := by simpa only [SimpleGraph.mem_neighborSet] using hu.1
      have hdv : G.Adj d v := by simpa only [SimpleGraph.mem_neighborSet] using hv.1
      rcases hdD with hdF | hdY₂
      · have classify : ∀ {w : V}, w ∈ T → G.Adj d w → w = a ∨ w = y₁ := by
          intro w hw hdw
          simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with hwa | hwa₀ | hwy₁
          · exact Or.inl hwa
          · have hm : d ∈ {f ∈ F | G.Adj a₀ f} := ⟨hdF.1, hwa₀ ▸ hdw.symm⟩
            rw [ha₀F] at hm
            have hda : d = a := by simpa using hm
            exact False.elim (hdF.2 (by simpa [hda]))
          · exact Or.inr hwy₁
        rcases classify hu.2 hdu with rfl | rfl <;>
          rcases classify hv.2 hdv with rfl | rfl
        · rfl
        · have hdL := left_of_adj_a hdF hdu
          have hdR := right_of_adj_y₁ hdF hdv
          have hdb : d ∈ ({b} : Set V) := by rw [← hsplit.inter]; exact ⟨hdL.1, hdR.1⟩
          exact False.elim (hdL.2 hdb)
        · have hdL := left_of_adj_a hdF hdv
          have hdR := right_of_adj_y₁ hdF hdu
          have hdb : d ∈ ({b} : Set V) := by rw [← hsplit.inter]; exact ⟨hdL.1, hdR.1⟩
          exact False.elim (hdL.2 hdb)
        · rfl
      · have hdy₂ : d = y₂ := by simpa using hdY₂
        have huT := hu.2
        have hvT := hv.2
        subst d
        simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at huT hvT
        have hu0 : u = a₀ := by
          rcases huT with rfl | rfl | rfl
          · exact False.elim (hy₂a hdu)
          · rfl
          · exact False.elim (hy₁y₂ hdu.symm)
        have hv0 : v = a₀ := by
          rcases hvT with rfl | rfl | rfl
          · exact False.elim (hy₂a hdv)
          · rfl
          · exact False.elim (hy₁y₂ hdv.symm)
        exact hu0.trans hv0.symm
    omega

private theorem unique_neighbor_restrict (G : SimpleGraph V) (F S : Set V)
    (x a : V) (hSF : S ⊆ F) (haS : a ∈ S)
    (h : {f ∈ F | G.Adj x f} = {a}) :
    {f ∈ S | G.Adj x f} = {a} := by
  ext f
  constructor
  · intro hf
    have : f ∈ {z ∈ F | G.Adj x z} := ⟨hSF hf.1, hf.2⟩
    rw [h] at this
    exact this
  · intro hf
    have hfa : f = a := by simpa using hf
    subst f
    have haFull : a ∈ {z ∈ F | G.Adj x z} := by rw [h]; simp
    exact ⟨haS, haFull.2⟩

/-- The disconnected branch of 17.3, assembled from the three printed
sentences isolated above and 17.2 on the block `F₁`. -/
theorem disconnectedCase
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hFa : ConnectedSet G (F \ {a})) (hnotFb : ¬ ConnectedSet G (F \ {b})) :
    ∃ y ∈ Y, VertexAnticomplete G y (F \ {a}) := by
  classical
  have hfour : IsPathFrom G [a, a₀, b₀, b] a b := ⟨hpath, by simp, by simp⟩
  have hab : a ≠ b :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hfour (by simp [pathLength])
  obtain ⟨F₁, F₂, hs⟩ := componentSplit G F a b hF ha hb hab hFa hnotFb
  have hF₁Y : Disjoint F₁ Y := Set.disjoint_of_subset_left hs.left_subset hFY
  have ha₀out : a₀ ∉ F₁ ∪ Y := by
    rintro (h | h)
    · exact ha₀ (Or.inl (hs.left_subset h))
    · exact ha₀ (Or.inr h)
  have hb₀out : b₀ ∉ F₁ ∪ Y := by
    rintro (h | h)
    · exact hb₀ (Or.inl (hs.left_subset h))
    · exact hb₀ (Or.inr h)
  have ha₀F₁ : {f ∈ F₁ | G.Adj a₀ f} = {a} :=
    unique_neighbor_restrict G F F₁ a₀ a hs.left_subset hs.a_mem ha₀F
  have hb₀F₁ : {f ∈ F₁ | G.Adj b₀ f} = {b} :=
    unique_neighbor_restrict G F F₁ b₀ b hs.left_subset hs.b_mem_left hb₀F
  have h172 := _root_.Workspace.Statements.S17.SPGT.thm_17_2 G hG F₁ Y
    hF₁Y hs.left_connected hY a₀ b₀ a b ha₀out hb₀out hs.a_mem
    hs.b_mem_left hpath ha₀Y hb₀Y haY hbY ha₀F₁ hb₀F₁
    hs.left_without_a_connected hs.left_without_b_connected
  rcases h172 with ⟨y, hyY, hyF₁⟩ | ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁y₂, hy₁F₁, hy₂F₁⟩
  · refine ⟨y, hyY, ?_⟩
    intro f hf hadj
    have hfF : f ∈ F := hf.1
    rw [hs.cover] at hfF
    rcases hfF with hf₁ | hf₂
    · exact hyF₁ f hf₁ hadj
    · exact outsideNeighborContradictsLink G hG F Y F₁ F₂ hFY hF
        a₀ b₀ a b ha₀ hb₀ ha hb hpath ha₀Y hb₀Y ha₀F hb₀F hs y hyY hyF₁
        ⟨f, hf₂, hadj⟩
  · refine ⟨y₁, hy₁Y, ?_⟩
    intro f hf hadj
    have hfF : f ∈ F := hf.1
    rw [hs.cover] at hfF
    rcases hfF with hf₁ | hf₂
    · have hm : f ∈ {z ∈ F₁ | G.Adj y₁ z} := ⟨hf₁, hadj⟩
      rw [hy₁F₁] at hm
      exact hf.2 (by simpa using hm)
    · exact outsideNeighborContradictsCatch G hG F Y F₁ F₂ hFY hF
        a₀ b₀ a b ha₀ hb₀ ha hb hFa hpath ha₀Y hb₀Y ha₀F hb₀F hs
        y₁ y₂ hy₁Y hy₂Y hy₁y₂ hy₁F₁ hy₂F₁ ⟨f, hf₂, hadj⟩

/-- The full conclusion of 17.3. -/
theorem main
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hFa : ConnectedSet G (F \ {a})) :
    ∃ y ∈ Y, VertexAnticomplete G y (F \ {a}) := by
  classical
  by_cases hFb : ConnectedSet G (F \ {b})
  · have h172 := _root_.Workspace.Statements.S17.SPGT.thm_17_2 G hG F Y hFY hF hY
      a₀ b₀ a b ha₀ hb₀ ha hb hpath ha₀Y hb₀Y haY hbY ha₀F hb₀F hFa hFb
    rcases h172 with ⟨y, hyY, hyF⟩ | ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁y₂, hy₁F, hy₂F⟩
    · exact ⟨y, hyY, fun f hf => hyF f hf.1⟩
    · refine ⟨y₁, hy₁Y, ?_⟩
      intro f hf hadj
      have hm : f ∈ {z ∈ F | G.Adj y₁ z} := ⟨hf.1, hadj⟩
      rw [hy₁F] at hm
      exact hf.2 (by simpa using hm)
  · exact disconnectedCase G hG F Y hFY hF hY a₀ b₀ a b ha₀ hb₀ ha hb hpath
      ha₀Y hb₀Y haY hbY ha₀F hb₀F hFa hFb

end Workspace.ProofLemmas.Thm173Core
