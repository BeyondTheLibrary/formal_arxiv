/-  Proof attempt 1 for statement 20.2 (printed p. 123, proof printed pp. 123-124).

    The printed proof has three paragraphs.  The first two ("Suppose first that
    x₀,…,x_t is a Y-square of height 3" and "Now suppose x₀,…,x_t is a polished
    Y-diamond of height 4 … The proof is completed exactly as in the previous
    paragraph") run the *same* argument with `w = x₃` resp. `w = x₄`; it is
    factored out below as `square_core`.  The third paragraph is a one-line
    appeal to 19.2.                                                            -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S15.Thm_15_7
import Workspace.Statements.S19.Thm_19_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.Thm201HubBasics

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S20

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas

/-- Truncating a wheel system: `x₀,…,x_s` is a wheel system whenever `x₀,…,x_t`
is and `1 ≤ s ≤ t`. -/
private theorem wheelSystem_truncate {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t s : ℕ} (hws : IsWheelSystem G z A₀ x t) (hs : 1 ≤ s) (hst : s ≤ t) :
    IsWheelSystem G z A₀ x s := by
  obtain ⟨-, hinj, hout, hfr, h2, h3, h4⟩ := hws
  exact ⟨hs, fun j hj k hk h => hinj j (by omega) k (by omega) h,
    fun j hj => hout j (by omega), hfr,
    fun i hi hit => h2 i hi (by omega),
    fun i hi hit => h3 i hi (by omega),
    fun j hj => h4 j (by omega)⟩

/-- **The common core of the first two paragraphs of the printed proof.**

`w` is the paper's `x₃` (first paragraph) resp. `x₄` (second paragraph): a vertex
adjacent to `z` and to `x₂`, with no neighbour in `A₁`, and `q ∈ A₂` is adjacent
to `w` and has a neighbour in `A₁`.  The printed argument derives a
contradiction. -/
private theorem square_core {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} (hws : IsWheelSystem G z A₀ x t)
    (ht : 2 ≤ t) {w q : V}
    (hzw : G.Adj z w) (hwq : G.Adj w q) (hwx2 : G.Adj w (x 2))
    (hwA1 : ∀ a ∈ wheelSystemA G z A₀ x 1, ¬ G.Adj w a)
    (hqA2 : q ∈ wheelSystemA G z A₀ x 2)
    (hqb : ∃ b ∈ wheelSystemA G z A₀ x 1, G.Adj q b) :
    False := by
  obtain ⟨h1t, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := hws
  have hX1 : wheelSystemX x 1 = ({x 0, x 1} : Set V) := WheelSystemBasics.wheelSystemX_one x
  -- ###  standing facts about `A₁`
  have hA₀nc1 : ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x 1) := by
    intro v hv; rw [hX1]; exact hA₀nc v hv
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x 1 :=
    WheelSystemBasics.A₀_subset_wheelSystemA hframe hA₀nc1
  have hA₁conn : ConnectedSet G (wheelSystemA G z A₀ x 1) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hznotadj : ∀ v ∈ wheelSystemA G z A₀ x 1, ¬ G.Adj z v :=
    fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv
  have hA₁nc : ∀ v ∈ wheelSystemA G z A₀ x 1, ¬ VertexComplete G v (wheelSystemX x 1) :=
    fun v hv => WheelSystemBasics.wheelSystemA_no_complete hv
  have hzX1 : VertexComplete G z (wheelSystemX x 1) := by
    intro v hv
    rw [WheelSystemBasics.mem_wheelSystemX] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact hzadj j (by omega)
  have hzX2 : VertexComplete G z (wheelSystemX x 2) := by
    intro v hv
    rw [WheelSystemBasics.mem_wheelSystemX] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact hzadj j (by omega)
  have hx2nc : ¬ VertexComplete G (x 2) (wheelSystemX x 1) := hcond3 2 (by omega) ht
  have hznotA₁ : z ∉ wheelSystemA G z A₀ x 1 := fun h => hA₁nc z h hzX1
  have hx0notA₁ : x 0 ∉ wheelSystemA G z A₀ x 1 :=
    fun h => hznotadj _ h (hzadj 0 (by omega))
  have hx1notA₁ : x 1 ∉ wheelSystemA G z A₀ x 1 :=
    fun h => hznotadj _ h (hzadj 1 (by omega))
  have hx2notA₁ : x 2 ∉ wheelSystemA G z A₀ x 1 :=
    fun h => hznotadj _ h (hzadj 2 (by omega))
  have hwnotA₁ : w ∉ wheelSystemA G z A₀ x 1 := fun h => hznotadj _ h hzw
  have hqnotA₁ : q ∉ wheelSystemA G z A₀ x 1 := fun h => hwA1 q h hwq
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA2
  have hqnc2 : ¬ VertexComplete G q (wheelSystemX x 2) :=
    WheelSystemBasics.wheelSystemA_no_complete hqA2
  have hzneq : z ≠ q := fun h => hqnc2 (h ▸ hzX2)
  -- ###  "From the maximality of A₁ it follows that q is X₁-complete"
  have hqX1 : VertexComplete G q (wheelSystemX x 1) := by
    by_contra hcon
    obtain ⟨b, hb, hqbadj⟩ := hqb
    refine hqnotA₁ (WheelSystemBasics.mem_wheelSystemA_of_witness
      (B := wheelSystemA G z A₀ x 1 ∪ {q})
      (fun v hv => Or.inl (hA₀sub hv))
      (ConnectedSetUnionAttach.connectedSet_union_singleton hA₁conn ⟨b, hb, hqbadj⟩)
      ?_ ?_ (Or.inr rfl))
    · intro v hv
      rcases hv with hv | hv
      · exact hznotadj v hv
      · rw [Set.mem_singleton_iff] at hv; subst hv; exact hzq
    · intro v hv
      rcases hv with hv | hv
      · exact hA₁nc v hv
      · rw [Set.mem_singleton_iff] at hv; subst hv; exact hcon
  -- ###  "and therefore nonadjacent to x₂"
  have hqx2 : ¬ G.Adj q (x 2) := by
    intro hadj
    refine hqnc2 ?_
    intro v hv
    rw [WheelSystemBasics.mem_wheelSystemX] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    interval_cases j
    · exact hqX1 (x 0) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    · exact hqX1 (x 1) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    · exact hadj
  have hqnex2 : q ≠ x 2 := fun h => hzq (h ▸ hzadj 2 ht)
  -- ###  "Let Q be a path from q to x₂ with interior in A₁"
  have hx2nb : ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj (x 2) a := by
    obtain ⟨B, hB0, hBc, hbex, hBz, hBnc⟩ := hcond2 2 (by omega) ht
    exact WheelSystemBasics.exists_adj_wheelSystemA_of_witness hB0 hBc hBz hBnc hbex
  obtain ⟨Q, hQ, hQmem⟩ :=
    PathInteriorIn.exists_path_mem_of_interior_in hA₁conn hqnotA₁ hx2notA₁ hqb hx2nb
  have hQint : ∀ y ∈ SPGT.interior Q, y ∈ wheelSystemA G z A₀ x 1 := by
    intro y hy
    obtain ⟨hyQ, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hy
    rcases hQmem y hyQ with h | h | h
    · exact absurd h hy1
    · exact absurd h hy2
    · exact h
  -- "so Q has length ≥ 2"
  have hQlen2 : 2 ≤ pathLength Q := by
    by_contra hcon
    have h01 : pathLength Q = 0 ∨ pathLength Q = 1 := by omega
    rcases h01 with h | h
    · have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
      have hlen1 : Q.length = 1 := by
        have := PathBasics.pathLength_eq Q; omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
      have e1 : a = q := by simpa using hQ.2.1
      have e2 : a = x 2 := by simpa using hQ.2.2
      exact hqnex2 (e1 ▸ e2)
    · exact hqx2 (PathBasics.isPathFrom_ends_adj_of_length_one hQ h)
  -- ###  "Q is even since it can be completed to a hole via x₂-x₃-q"
  have hBerge : Berge G := hG.1.1.1.1
  have hwnotQ : w ∉ Q := by
    intro hmem
    rcases hQmem w hmem with h | h | h
    · exact G.irrefl (h ▸ hwq)
    · exact G.irrefl (h ▸ hwx2)
    · exact hwnotA₁ h
  have hhole1 : IsHoleList G (w :: Q) :=
    PrismBasics.isHoleList_of_path_add_vertex hQ hQlen2 hwq hwx2 hwnotQ
      (fun y hy => hwA1 y (hQint y hy))
  have hQeven : Even (pathLength Q) := by
    have hev := hBerge.1 _ hhole1
    rw [PrismBasics.holeLength_cons w (PathBasics.path_ne_nil hQ.1)] at hev
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  -- ###  "and so q-Q-x₂-z is an odd path"
  have hznotQ : z ∉ Q := by
    intro hmem
    rcases hQmem z hmem with h | h | h
    · exact hzneq h
    · exact (hout 2 ht).2 h.symm
    · exact hznotA₁ h
  have hP' : IsPathFrom G (Q ++ [z]) q z := by
    refine PathAttach.isPathFrom_concat hQ (hzadj 2 ht) hznotQ ?_
    intro y hy hyne
    rcases hQmem y hy with h | h | h
    · subst h; exact hzq
    · exact absurd h hyne
    · exact hznotadj y h
  have hP'len : pathLength (Q ++ [z]) = pathLength Q + 1 := by
    have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
    simp only [pathLength, List.length_append, List.length_singleton]
    omega
  have hP'odd : Odd (pathLength (Q ++ [z])) := by
    rw [hP'len]
    exact Even.add_one hQeven
  -- ###  `X₁` is anticonnected
  have hx0nex1 : x 0 ≠ x 1 := by
    intro h; exact absurd (hinj 0 (by omega) 1 (by omega) h) (by omega)
  have hnadj01 : ¬ G.Adj (x 0) (x 1) := by
    intro h
    refine hcond3 1 le_rfl (by omega) ?_
    intro v hv
    rw [WheelSystemBasics.wheelSystemX_zero, Set.mem_singleton_iff] at hv
    subst hv
    exact h.symm
  have hX1anti : AnticonnectedSet G (wheelSystemX x 1) := by
    have hap : IsAntipathList G [x 0, x 1] := by
      refine PathBasics.isPathList_pair ?_
      rw [SimpleGraph.compl_adj]
      exact ⟨hx0nex1, hnadj01⟩
    have h2 := InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList hap
    have hset : {v : V | v ∈ [x 0, x 1]} = wheelSystemX x 1 := by
      rw [hX1]; ext v; simp
    rwa [hset] at h2
  -- ###  "By 13.6 it has length 3"
  have hXsub : wheelSystemX x 1 ⊆ {v : V | v ∈ Q ++ [z]}ᶜ := by
    intro y hy
    rw [WheelSystemBasics.mem_wheelSystemX] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · rcases hQmem _ h with e | e | e
      · exact G.irrefl (e ▸ hqX1 (x j) (WheelSystemBasics.self_mem_wheelSystemX x hj))
      · exact absurd (hinj j (by omega) 2 ht e) (by omega)
      · exact hznotadj _ e (hzadj j (by omega))
    · rw [List.mem_singleton] at h
      exact (hout j (by omega)).2 h
  have hclass : ∀ y ∈ Q ++ [z], VertexComplete G y (wheelSystemX x 1) → y = q ∨ y = z := by
    intro y hy hyc
    rcases List.mem_append.mp hy with h | h
    · rcases hQmem y h with e | e | e
      · exact Or.inl e
      · exact absurd (e ▸ hyc) hx2nc
      · exact absurd hyc (hA₁nc y e)
    · rw [List.mem_singleton] at h; exact Or.inr h
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 (Q ++ [z]) q z hP' hP'odd
      (wheelSystemX x 1) hXsub hX1anti hqX1 hzX1 with halt1 | halt2
  · -- the `X₁`-complete edge alternative: its ends must be `q` and `z`, which are nonadjacent
    obtain ⟨u, hu, v, hv, hadj, huc, hvc⟩ := halt1
    rcases hclass u hu huc with rfl | rfl <;> rcases hclass v hv hvc with hv' | hv'
    · exact G.irrefl (hv' ▸ hadj)
    · exact hzq (hv' ▸ hadj).symm
    · exact hzq (hv' ▸ hadj)
    · exact G.irrefl (hv' ▸ hadj)
  -- ###  "and there is an antipath with interior in X₁, joining its middle vertices"
  obtain ⟨hlen3, c, d, hint, qa, hqa, hqaodd, hqaint⟩ := halt2
  have hQlen3 : Q.length = 3 := by
    rw [hP'len] at hlen3
    have := PathBasics.pathLength_eq Q
    have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
    omega
  obtain ⟨a0, a1, a2, hQeq0⟩ := PrismBasics.length_eq_three hQlen3
  have ha0 : a0 = q := by rw [hQeq0] at hQ; simpa using hQ.2.1
  have ha2 : a2 = x 2 := by rw [hQeq0] at hQ; simpa using hQ.2.2
  rw [ha0, ha2] at hQeq0
  have hQeq : Q = [q, a1, x 2] := hQeq0
  have hQ' : IsPathFrom G [q, a1, x 2] q (x 2) := by rw [← hQeq]; exact hQ
  have hQadj01 : G.Adj q a1 := by
    have h := PathBasics.path_adj_succ hQ'.1 (i := 0) (by simp)
    simpa using h
  have hQadj12 : G.Adj a1 (x 2) := by
    have h := PathBasics.path_adj_succ hQ'.1 (i := 1) (by simp)
    simpa using h
  have hintQ : SPGT.interior Q = [a1] := by rw [hQeq]; rfl
  have ha1A₁ : a1 ∈ wheelSystemA G z A₀ x 1 := hQint a1 (by rw [hintQ]; simp)
  have hintP' : SPGT.interior (Q ++ [z]) = [a1, x 2] := by rw [hQeq]; rfl
  rw [hintP'] at hint
  obtain ⟨hc, hd⟩ : c = a1 ∧ d = x 2 := by
    injection hint with h1 h2
    injection h2 with h3 h4
    exact ⟨h1.symm, h3.symm⟩
  rw [hc, hd] at hqa
  -- the antipath `qa` runs from `a1` to `x₂`; its length is odd and at least `3`
  have hqalen1 : pathLength qa ≠ 1 := by
    intro h
    have := PathBasics.isPathFrom_ends_adj_of_length_one hqa h
    rw [SimpleGraph.compl_adj] at this
    exact this.2 hQadj12
  have hqaNodup : (SPGT.interior qa).Nodup :=
    ((List.dropLast_sublist qa.tail).trans (List.tail_sublist qa)).nodup
      (PathBasics.path_nodup hqa.1)
  have hIle : (SPGT.interior qa).length ≤ 2 := by
    have h1 : (SPGT.interior qa).toFinset.card = (SPGT.interior qa).length :=
      List.toFinset_card_of_nodup hqaNodup
    have h2 : (SPGT.interior qa).toFinset ⊆ ({x 0, x 1} : Finset V) := by
      intro y hy
      rw [List.mem_toFinset] at hy
      have hy2 := hqaint y hy
      rw [hX1] at hy2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      simpa using hy2
    have h3 := Finset.card_le_card h2
    have h4 : ({x 0, x 1} : Finset V).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  have hIlen : (SPGT.interior qa).length = qa.length - 2 := PathBasics.interior_length qa
  have hqapos : 0 < qa.length := PathBasics.path_length_pos hqa.1
  have hqale : pathLength qa ≤ 3 := by
    have := PathBasics.pathLength_eq qa; omega
  have hqaeq3 : pathLength qa = 3 := by
    obtain ⟨k, hk⟩ := hqaodd
    omega
  have hIlen2 : (SPGT.interior qa).length = 2 := by
    have := PathBasics.pathLength_eq qa; omega
  -- the interior of `qa` is exactly `{x₀, x₁}`
  obtain ⟨e0, e1, he⟩ := PrismBasics.length_eq_two hIlen2
  have he0 : e0 = x 0 ∨ e0 = x 1 := by
    have := hqaint e0 (by rw [he]; simp)
    rw [hX1] at this; simpa using this
  have he1 : e1 = x 0 ∨ e1 = x 1 := by
    have := hqaint e1 (by rw [he]; simp)
    rw [hX1] at this; simpa using this
  have hene : e0 ≠ e1 := by
    rw [he] at hqaNodup; simpa using hqaNodup
  have hx0mem : x 0 ∈ SPGT.interior qa := by
    rcases he0 with h | h
    · rw [he, ← h]; simp
    · rcases he1 with h' | h'
      · rw [he, ← h']; simp
      · exact absurd (h.trans h'.symm) hene
  have hx1mem : x 1 ∈ SPGT.interior qa := by
    rcases he0 with h | h
    · rcases he1 with h' | h'
      · exact absurd (h.trans h'.symm) hene
      · rw [he, ← h']; simp
    · rw [he, ← h]; simp
  -- ###  "This antipath can be completed via r-z-q-x₂ to an antihole of length ≥ 6"
  have hmemqa : ∀ y ∈ qa, y = a1 ∨ y = x 2 ∨ y ∈ wheelSystemX x 1 := by
    intro y hy
    by_cases h1 : y = a1
    · exact Or.inl h1
    by_cases h2 : y = x 2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hqaint y ((PathBasics.mem_interior_iff_of_pathFrom hqa).mpr
      ⟨hy, h1, h2⟩)))
  have hznotqa : z ∉ qa := by
    intro hy
    rcases hmemqa z hy with h | h | h
    · exact hznotA₁ (h ▸ ha1A₁)
    · exact (hout 2 ht).2 h.symm
    · exact G.irrefl (hzX1 z h)
  have hqnotqa : q ∉ qa := by
    intro hy
    rcases hmemqa q hy with h | h | h
    · exact G.irrefl (h ▸ hQadj01)
    · exact hqnex2 h
    · exact G.irrefl (hqX1 q h)
  have hantihole : IsAntiholeList G (q :: z :: qa) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hqa (by omega) ?_ ?_ ?_
      hznotqa hqnotqa ?_ ?_ ?_ ?_
    · rw [SimpleGraph.compl_adj]
      exact ⟨fun h => hznotA₁ (h ▸ ha1A₁), hznotadj a1 ha1A₁⟩
    · rw [SimpleGraph.compl_adj]; exact ⟨hqnex2, hqx2⟩
    · rw [SimpleGraph.compl_adj]; exact ⟨hzneq, hzq⟩
    · rw [SimpleGraph.compl_adj]
      intro h; exact h.2 (hzadj 2 ht)
    · rw [SimpleGraph.compl_adj]
      intro h; exact h.2 hQadj01
    · intro y hy h
      rw [SimpleGraph.compl_adj] at h
      exact h.2 (hzX1 y (hqaint y hy))
    · intro y hy h
      rw [SimpleGraph.compl_adj] at h
      exact h.2 (hqX1 y (hqaint y hy))
  have hDlen : holeLength (q :: z :: qa) = 6 := by
    rw [PrismBasics.holeLength_cons_cons z q (PathBasics.path_ne_nil hqa.1), hqaeq3]
  -- ###  "but let P be a path from x₀ to x₁ with interior in A₀"
  have hx0notA₀ : x 0 ∉ A₀ := (hout 0 (by omega)).1
  have hx1notA₀ : x 1 ∉ A₀ := (hout 1 (by omega)).1
  obtain ⟨P, hP, hPmem⟩ :=
    PathInteriorIn.exists_path_mem_of_interior_in hframe.2.1 hx0notA₀ hx1notA₀ hnb0 hnb1
  have hPint : ∀ y ∈ SPGT.interior P, y ∈ A₀ := by
    intro y hy
    obtain ⟨hyP, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hy
    rcases hPmem y hyP with h | h | h
    · exact absurd h hy1
    · exact absurd h hy2
    · exact h
  have hPlen : 3 ≤ pathLength P := by
    by_contra hcon
    have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
    have hpl := PathBasics.pathLength_eq P
    have h012 : pathLength P = 0 ∨ pathLength P = 1 ∨ pathLength P = 2 := by omega
    rcases h012 with h | h | h
    · have hlen1 : P.length = 1 := by omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
      have e1 : a = x 0 := by simpa using hP.2.1
      have e2 : a = x 1 := by simpa using hP.2.2
      exact hx0nex1 (e1 ▸ e2)
    · exact hnadj01 (PathBasics.isPathFrom_ends_adj_of_length_one hP h)
    · have hlen3 : P.length = 3 := by omega
      obtain ⟨b0, b1, b2, hPeq0⟩ := PrismBasics.length_eq_three hlen3
      have e1 : b0 = x 0 := by rw [hPeq0] at hP; simpa using hP.2.1
      have e2 : b2 = x 1 := by rw [hPeq0] at hP; simpa using hP.2.2
      rw [e1, e2] at hPeq0
      have hPeq : P = [x 0, b1, x 1] := hPeq0
      have hP2 : IsPathFrom G [x 0, b1, x 1] (x 0) (x 1) := by rw [← hPeq]; exact hP
      have hadj0 : G.Adj (x 0) b1 := by
        have h := PathBasics.path_adj_succ hP2.1 (i := 0) (by simp)
        simpa using h
      have hadj1 : G.Adj b1 (x 1) := by
        have h := PathBasics.path_adj_succ hP2.1 (i := 1) (by simp)
        simpa using h
      have hintP : SPGT.interior P = [b1] := by rw [hPeq]; rfl
      have hb1 : b1 ∈ A₀ := hPint b1 (by rw [hintP]; simp)
      refine hA₀nc b1 hb1 ?_
      intro v hv
      rcases hv with hv | hv
      · subst hv; exact hadj0.symm
      · rw [Set.mem_singleton_iff] at hv; subst hv; exact hadj1
  have hznotP : z ∉ P := by
    intro hy
    rcases hPmem z hy with h | h | h
    · exact (hout 0 (by omega)).2 h.symm
    · exact (hout 1 (by omega)).2 h.symm
    · exact hframe.2.2.1 h
  have hholeC : IsHoleList G (z :: P) :=
    PrismBasics.isHoleList_of_path_add_vertex hP (by omega) (hzadj 0 (by omega))
      (hzadj 1 (by omega)) hznotP
      (fun y hy => hframe.2.2.2 y (hPint y hy))
  have hCl : 4 < holeLength (z :: P) := by
    rw [PrismBasics.holeLength_cons z (PathBasics.path_ne_nil hP.1)]; omega
  -- ###  "But this contradicts 15.7"
  have h157 := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hG.1 (z :: P) (q :: z :: qa)
    hholeC hCl hantihole (by rw [hDlen]; omega)
  have hsub3 : ({x 0, x 1, z} : Set V) ⊆
      ({w : V | w ∈ z :: P} ∩ {w : V | w ∈ q :: z :: qa}) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, List.mem_cons]
      rcases hy with rfl | rfl | rfl
      · exact Or.inr (PathBasics.head_mem hP.2.1)
      · exact Or.inr (PathBasics.getLast_mem hP.2.2)
      · exact Or.inl rfl
    · simp only [Set.mem_setOf_eq, List.mem_cons]
      rcases hy with rfl | rfl | rfl
      · exact Or.inr (Or.inr (PathBasics.interior_subset hx0mem))
      · exact Or.inr (Or.inr (PathBasics.interior_subset hx1mem))
      · exact Or.inr (Or.inl rfl)
  have hcard3 : ({x 0, x 1, z} : Set V).ncard = 3 := by
    refine Set.ncard_eq_three.mpr ⟨x 0, x 1, z, hx0nex1, ?_, ?_, rfl⟩
    · exact fun h => (hout 0 (by omega)).2 h
    · exact fun h => (hout 1 (by omega)).2 h
  have := Set.ncard_le_ncard hsub3 (Set.toFinite _)
  omega


/-- **20.2** (printed p. 123).

PAPER: *"Let `G ∈ F₇`, let `(z,A₀)` be a frame, and let
`Y ⊆ V(G) \ (A₀ ∪ {z})` be nonempty and anticonnected.  There is no `Y`-square of
height `3` or polished `Y`-diamond of height `4` in `G`; and if `x₀,…,x₃` is a
`Y`-diamond of height `3`, then `z` is `Y`-complete and `G` contains a wheel
`(C, Y ∪ {x₃})`."*

Encoding notes.

* The conclusion has three parts, formalized as a conjunction in the printed
  order: no `Y`-square of height `3`; no polished `Y`-diamond of height `4`; and
  the implication about `Y`-diamonds of height `3`.
* *"a wheel `(C, Y ∪ {x₃})`"* is `IsWheel G C (Y ∪ {x 3})` — the hub of the
  produced wheel is the *larger* set `Y ∪ {x₃}`, which is the "annoying wastage"
  the paper remarks on immediately after this statement. -/
theorem thm_20_2 (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (Y : Set V) (hYsub : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y) :
    (¬ ∃ x : ℕ → V, IsYSquare G z A₀ x 3 Y) ∧
    (¬ ∃ x : ℕ → V, IsPolishedYDiamond G z A₀ x 4 Y) ∧
    (∀ x : ℕ → V, IsYDiamond G z A₀ x 3 Y →
      VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C (Y ∪ {x 3})) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ###  first paragraph:  `x₀,…,x₃` is a `Y`-square of height `3`
    rintro ⟨x, hws, -, -, -, -, -, -, hadj32, hnoA1, a, haA2, haw, b, hbA1, hab⟩
    have h21 : (3 : ℕ) - 1 = 2 := by norm_num
    have h22 : (3 : ℕ) - 2 = 1 := by norm_num
    rw [h22] at hnoA1
    rw [h21] at haA2
    rw [h22] at hbA1
    rw [h21] at hadj32
    exact square_core hG hframe hws (by omega) (hws.2.2.2.2.2.2 3 (by omega))
      haw.symm hadj32 hnoA1 haA2 ⟨b, hbA1, hab⟩
  · -- ###  second paragraph:  `x₀,…,x₄` is a polished `Y`-diamond of height `4`
    rintro ⟨x, ⟨hws, -, -, -, -, -, -, hx4X2, -⟩, -, -, hnoA1, -,
      a, haA2, haw, hax3, b, hbA1, hab⟩
    have h41 : (4 : ℕ) - 1 = 3 := by norm_num
    have h42 : (4 : ℕ) - 2 = 2 := by norm_num
    have h43 : (4 : ℕ) - 3 = 1 := by norm_num
    rw [h43] at hnoA1
    rw [h42] at haA2
    rw [h43] at hbA1
    rw [h42] at hx4X2
    exact square_core hG hframe hws (by omega) (hws.2.2.2.2.2.2 4 (by omega))
      haw.symm (hx4X2 (x 2) (WheelSystemBasics.self_mem_wheelSystemX x (by omega)))
      hnoA1 haA2 ⟨b, hbA1, hab⟩
  · -- ###  third paragraph:  "from 19.2 with A = A₁, v = x₂ and anticonnected set Y ∪ {x₃}"
    intro x hdia
    obtain ⟨hws, hYne', hYanti', ⟨hzY, hxY⟩, hVC, hnVC, -, hx3X1, hx3A1⟩ := hdia
    have h32 : (3 : ℕ) - 2 = 1 := by norm_num
    rw [h32] at hx3X1
    rw [h32] at hx3A1
    obtain ⟨h1t, hinj, hout, hfr, hcond2, hcond3, hzadj⟩ := id hws
    have hws2 : IsWheelSystem G z A₀ x 2 := wheelSystem_truncate hws (by omega) (by omega)
    have hx3notY : x 3 ∉ Y := hxY 3 le_rfl
    -- `x₃` is `X₁`-complete, and therefore nonadjacent to `x₂`
    have hadj30 : G.Adj (x 3) (x 0) :=
      hx3X1 (x 0) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    have hadj31 : G.Adj (x 3) (x 1) :=
      hx3X1 (x 1) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    have hnadj32 : ¬ G.Adj (x 3) (x 2) := by
      intro h
      refine hcond3 3 (by omega) (by omega) ?_
      intro v hv
      rw [WheelSystemBasics.mem_wheelSystemX] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      interval_cases j
      · exact hadj30
      · exact hadj31
      · exact h
    -- `Y ∪ {x₃}` is anticonnected
    have hanti : AnticonnectedSet G (Y ∪ {x 3}) := by
      obtain ⟨y, hyY, hnadj⟩ : ∃ y ∈ Y, ¬ G.Adj (x 3) y := by
        by_contra hcon
        push_neg at hcon
        exact hnVC (fun y hy => hcon y hy)
      refine ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hYanti' ?_
      refine ⟨y, hyY, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => hx3notY (h ▸ hyY), hnadj⟩
    -- the hypotheses of 19.2
    have hsub : ∀ y ∈ Y ∪ {x 3}, y ≠ z ∧ y ≠ x 0 ∧ y ≠ x 1 ∧ y ≠ x 2 := by
      intro y hy
      rcases hy with hy | hy
      · exact ⟨fun h => hzY (h ▸ hy), fun h => hxY 0 (by omega) (h ▸ hy),
          fun h => hxY 1 (by omega) (h ▸ hy), fun h => hxY 2 (by omega) (h ▸ hy)⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨(hout 3 (by omega)).2, ?_, ?_, ?_⟩
        · intro h; exact absurd (hinj 3 (by omega) 0 (by omega) h) (by omega)
        · intro h; exact absurd (hinj 3 (by omega) 1 (by omega) h) (by omega)
        · intro h; exact absurd (hinj 3 (by omega) 2 (by omega) h) (by omega)
    have hc0 : VertexComplete G (x 0) (Y ∪ {x 3}) := by
      intro y hy
      rcases hy with hy | hy
      · exact hVC 0 (by omega) y hy
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact hadj30.symm
    have hc1 : VertexComplete G (x 1) (Y ∪ {x 3}) := by
      intro y hy
      rcases hy with hy | hy
      · exact hVC 1 (by omega) y hy
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact hadj31.symm
    have hc2 : ¬ VertexComplete G (x 2) (Y ∪ {x 3}) := by
      intro hcon
      exact hnadj32 (hcon (x 3) (Or.inr rfl)).symm
    have hnb : ∀ y ∈ Y ∪ {x 3}, ¬ G.Adj y (x 2) →
        (∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj y a) ∧ G.Adj y z := by
      intro y hy hnadj
      rcases hy with hy | hy
      · exact absurd (hVC 2 (by omega) y hy).symm hnadj
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨hx3A1, (hzadj 3 (by omega)).symm⟩
    obtain ⟨hzc, C, hC, -, -, -, -⟩ :=
      _root_.Workspace.Statements.S19.SPGT.thm_19_2 G hG z A₀ hframe x hws2 (Y ∪ {x 3})
        hsub hanti hc0 hc1 hc2 hnb
    exact ⟨fun y hy => hzc y (Or.inl hy), C, hC⟩


end SPGT

end Workspace.Statements.S20
