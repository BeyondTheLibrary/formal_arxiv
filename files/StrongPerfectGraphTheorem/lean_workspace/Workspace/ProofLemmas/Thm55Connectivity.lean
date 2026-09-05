import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# 5.5 — small edge cuts in a 3-connected graph

These elementary lemmas supply the connectivity needed when one or two deleted vertices of a
subdivision lie inside subdividing tracks.  Such a vertex blocks one original edge.  The
paper uses this inside its sentence

> *"Then one of `C,D` is contained in a branch of `H`."*

A 3-connected graph stays connected after deleting two edges.  After deleting one vertex it
also stays connected after deleting one edge.  We prove only these two small forms.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm55Connectivity

open Workspace.Types.Tracks.SPGT

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A 3-connected graph is connected. -/
theorem connected_of_three_connected {J : SimpleGraph U} (hJ : IsKConnected J 3) :
    J.Connected := by
  have hpos : 0 < Fintype.card U := by
    have h := hJ.1
    omega
  letI : Nonempty U := Fintype.card_pos_iff.mp hpos
  refine ⟨?_⟩
  intro u v
  have hconn := hJ.2 (∅ : Set U) (by simp)
  obtain ⟨p⟩ := hconn.preconnected ⟨u, by simp⟩ ⟨v, by simp⟩
  exact ⟨p.map (⟨fun z => (z : U), fun {_ _} h => h⟩ : J.induce (∅ : Set U)ᶜ →g J)⟩

/-- The ends of an edge of a 3-connected graph have an alternative route avoiding that edge. -/
theorem reachable_delete_edge {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {a b : U} (hab : J.Adj a b) :
    (J.deleteEdges {s(a, b)}).Reachable a b := by
  have hdeg := Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  have hnsub : ¬ J.neighborSet a ⊆ ({b} : Set U) := by
    intro hsub
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton b)
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨z, hza, hzb⟩ := Set.not_subset.mp hnsub
  have hzb' : z ≠ b := by simpa using hzb
  have hza' : z ≠ a := hza.ne'
  have hconn := hJ.2 ({a} : Set U) (by simp)
  let z' : ↥(({a} : Set U)ᶜ) := ⟨z, by simp [hza']⟩
  let b' : ↥(({a} : Set U)ᶜ) := ⟨b, by simp [hab.ne']⟩
  obtain ⟨p⟩ := hconn.preconnected z' b'
  let f : J.induce ({a} : Set U)ᶜ →g J.deleteEdges {s(a, b)} :=
    { toFun := fun x => (x : U)
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hxy, ?_⟩
        intro heq
        have ha : a ∈ s((x : U), (y : U)) := by rw [heq]; simp
        rcases Sym2.mem_iff.mp ha with ha | ha
        · exact x.2 (by simpa [ha])
        · exact y.2 (by simpa [ha]) }
  have hfirst : (J.deleteEdges {s(a, b)}).Adj a z := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hza, ?_⟩
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨h, -⟩
    · exact hzb' h
    · exact absurd h hab.ne
  exact ⟨SimpleGraph.Walk.cons hfirst (p.map f)⟩

/-- Deleting one edge from a 3-connected graph leaves it connected. -/
theorem connected_delete_edge {J : SimpleGraph U} (hJ : IsKConnected J 3) (a b : U) :
    (J.deleteEdges {s(a, b)}).Connected := by
  have hconn := connected_of_three_connected hJ
  apply hconn.connected_delete_edge_of_not_isBridge
  intro hb
  have hchar := SimpleGraph.isBridge_iff.mp hb
  exact hchar.2 (reachable_delete_edge hJ hchar.1)

/-- After deleting one vertex from a 3-connected graph, deleting one more edge still leaves a
connected graph. -/
theorem connected_induce_compl_singleton_delete_edge {J : SimpleGraph U}
    (hJ : IsKConnected J 3) (r : U) (a b : ↑(({r} : Set U)ᶜ)) :
    ((J.induce ({r} : Set U)ᶜ).deleteEdges {s(a, b)}).Connected := by
  have hconn : (J.induce ({r} : Set U)ᶜ).Connected := hJ.2 {r} (by simp)
  apply hconn.connected_delete_edge_of_not_isBridge
  intro hbri
  have hchar := SimpleGraph.isBridge_iff.mp hbri
  have habJ : J.Adj (a : U) (b : U) := hchar.1
  have hdeg :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ (a : U)
  have hnsub : ¬ J.neighborSet (a : U) ⊆ ({(b : U), r} : Set U) := by
    intro hsub
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hp : ({(b : U), r} : Set U).ncard ≤ 2 := by
      calc
        ({(b : U), r} : Set U).ncard ≤ ({r} : Set U).ncard + 1 :=
          Set.ncard_insert_le (b : U) {r}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨z, hza, hzout⟩ := Set.not_subset.mp hnsub
  have hzb : z ≠ (b : U) := fun h => hzout (Or.inl h)
  have hzr : z ≠ r := fun h => hzout (Or.inr h)
  have hza' : z ≠ (a : U) := hza.ne'
  let X : Set U := ({(a : U), r} : Set U)ᶜ
  have hXcard : ({(a : U), r} : Set U).ncard < 3 := by
    have hp : ({(a : U), r} : Set U).ncard ≤ 2 := by
      calc
        ({(a : U), r} : Set U).ncard ≤ ({r} : Set U).ncard + 1 :=
          Set.ncard_insert_le (a : U) {r}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hconn' := hJ.2 ({(a : U), r} : Set U) hXcard
  let z' : ↑X := ⟨z, by simp [X, hza', hzr]⟩
  let b' : ↑X := ⟨(b : U), by
    simp only [X, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨habJ.ne', fun hbr => b.2 (by simp [hbr])⟩⟩
  obtain ⟨p⟩ := hconn'.preconnected z' b'
  let K := (J.induce ({r} : Set U)ᶜ).deleteEdges {s(a, b)}
  let f : J.induce X →g K :=
    { toFun := fun x => ⟨(x : U), by
        simpa using fun h => x.2 (Or.inr h)⟩
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hxy, ?_⟩
        intro heq
        have ha : (a : U) ∈ s((x : U), (y : U)) := by
          have heq' : s((x : U), (y : U)) = s((a : U), (b : U)) := by
            simpa using congrArg (Sym2.map (fun z : ↑(({r} : Set U)ᶜ) => (z : U))) heq
          rw [heq']
          simp
        rcases Sym2.mem_iff.mp ha with ha | ha
        · exact x.2 (by simp [X, ha])
        · exact y.2 (by simp [X, ha]) }
  let az : ↑(({r} : Set U)ᶜ) := ⟨z, by simp [hzr]⟩
  have hfirst : K.Adj a az := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hza, ?_⟩
    intro heq
    have heq' : s((a : U), z) = s((a : U), (b : U)) := by
      simpa using congrArg (Sym2.map (fun z : ↑(({r} : Set U)ᶜ) => (z : U))) heq
    rcases Sym2.eq_iff.mp heq' with ⟨-, h⟩ | ⟨h, -⟩
    · exact hzb h
    · exact absurd h habJ.ne
  exact hchar.2 ⟨SimpleGraph.Walk.cons hfirst (p.map f)⟩

/-- If two distinct edges `ab` and `cd` are present, the ends `c,d` have a route avoiding
both edges. -/
theorem reachable_delete_two_edges {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {a b c d : U} (hab : J.Adj a b) (hcd : J.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) :
    ((J.deleteEdges {s(a, b)}).deleteEdges {s(c, d)}).Reachable c d := by
  obtain ⟨t, hte, htc, htd⟩ : ∃ t : U, t ∈ s(a, b) ∧ t ≠ c ∧ t ≠ d := by
    by_cases hac : a = c
    · refine ⟨b, by simp, ?_, ?_⟩
      · exact fun hbc => hab.ne (hac.trans hbc.symm)
      · intro hbd
        apply hne
        apply Sym2.eq_iff.mpr
        exact Or.inl ⟨hac, hbd⟩
    · by_cases had : a = d
      · refine ⟨b, by simp, ?_, ?_⟩
        · intro hbc
          apply hne
          apply Sym2.eq_iff.mpr
          exact Or.inr ⟨had, hbc⟩
        · exact fun hbd => hab.ne (had.trans hbd.symm)
      · exact ⟨a, by simp, hac, had⟩
  have hdeg := Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ c
  have hnsub : ¬ J.neighborSet c ⊆ ({d, t} : Set U) := by
    intro hsub
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hp : ({d, t} : Set U).ncard ≤ 2 := by
      calc
        ({d, t} : Set U).ncard ≤ ({t} : Set U).ncard + 1 := Set.ncard_insert_le d {t}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨z, hzc, hzout⟩ := Set.not_subset.mp hnsub
  have hzd : z ≠ d := by
    intro h
    exact hzout (Or.inl h)
  have hzt : z ≠ t := by
    intro h
    exact hzout (Or.inr h)
  have hzc' : z ≠ c := hzc.ne'
  let X : Set U := ({c, t} : Set U)ᶜ
  have hXcard : ({c, t} : Set U).ncard < 3 := by
    have hp : ({c, t} : Set U).ncard ≤ 2 := by
      calc
        ({c, t} : Set U).ncard ≤ ({t} : Set U).ncard + 1 := Set.ncard_insert_le c {t}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hconn := hJ.2 ({c, t} : Set U) hXcard
  let z' : ↥X := ⟨z, by simp [X, hzc', hzt]⟩
  let d' : ↥X := ⟨d, by simp [X, hcd.ne', Ne.symm htd]⟩
  obtain ⟨p⟩ := hconn.preconnected z' d'
  let K := (J.deleteEdges {s(a, b)}).deleteEdges {s(c, d)}
  let f : J.induce X →g K :=
    { toFun := fun x => (x : U)
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj]
        refine ⟨⟨hxy, ?_⟩, ?_⟩
        · intro heq
          have ht : t ∈ s((x : U), (y : U)) := by rw [heq]; exact hte
          rcases Sym2.mem_iff.mp ht with ht | ht
          · exact x.2 (by simp [X, ht])
          · exact y.2 (by simp [X, ht])
        · intro heq
          have hc : c ∈ s((x : U), (y : U)) := by rw [heq]; simp
          rcases Sym2.mem_iff.mp hc with hc | hc
          · exact x.2 (by simp [X, hc])
          · exact y.2 (by simp [X, hc]) }
  have hfirst : K.Adj c z := by
    rw [SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj]
    refine ⟨⟨hzc, ?_⟩, ?_⟩
    · intro heq
      have ht : t ∈ s(c, z) := by rw [heq]; exact hte
      rcases Sym2.mem_iff.mp ht with ht | ht
      · exact htc ht
      · exact hzt ht.symm
    · intro heq
      rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨h, -⟩
      · exact hzd h
      · exact absurd h hcd.ne
  exact ⟨SimpleGraph.Walk.cons hfirst (p.map f)⟩

/-- Deleting two edges from a 3-connected graph leaves it connected. -/
theorem connected_delete_two_edges {J : SimpleGraph U} (hJ : IsKConnected J 3)
    (a b c d : U) :
    ((J.deleteEdges {s(a, b)}).deleteEdges {s(c, d)}).Connected := by
  have hconn₁ := connected_delete_edge hJ a b
  apply hconn₁.connected_delete_edge_of_not_isBridge
  intro hb
  have hchar := SimpleGraph.isBridge_iff.mp hb
  have hcdJ : J.Adj c d := (SimpleGraph.deleteEdges_adj.mp hchar.1).1
  by_cases habJ : J.Adj a b
  · have hne : s(a, b) ≠ s(c, d) :=
      Ne.symm (SimpleGraph.deleteEdges_adj.mp hchar.1).2
    exact hchar.2 (reachable_delete_two_edges hJ habJ hcdJ hne)
  · have heq : J.deleteEdges {s(a, b)} = J := by
      ext u v
      rw [SimpleGraph.deleteEdges_adj]
      constructor
      · exact And.left
      · intro huv
        refine ⟨huv, ?_⟩
        intro he
        apply habJ
        rw [← SimpleGraph.mem_edgeSet, ← he]
        exact huv
    rw [heq] at hchar
    exact hchar.2 (reachable_delete_edge hJ hcdJ)

end Workspace.ProofLemmas.Thm55Connectivity
