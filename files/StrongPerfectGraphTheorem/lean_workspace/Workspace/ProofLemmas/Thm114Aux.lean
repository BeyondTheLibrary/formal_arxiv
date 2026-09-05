/-  Infrastructure for the proof of statement 11.4 (`Workspace.Statements.S11.SPGT.thm_11_4`).

    These lemmas are the bookkeeping the printed proof of 11.4 leaves implicit: the banister
    through `F` that the first sentence of the proof asserts without comment, the avoidance
    conditions a path built through `F` satisfies, and basic facts about rungs and interiors.

    PROVENANCE.  Every declaration in this file is copied verbatim from the `Aux` namespace of
    `Workspace/Statements/S11/Thm_11_5.lean` (lines 149-469), where it was written and proved
    while proving 11.5.  It cannot be imported from there: `Thm_11_5.lean` imports
    `Thm_11_4.lean`, so a dependency in the other direction would be a cycle.  The right
    long-term fix is to lift the `Aux` block of 11.5 into this module and have 11.5 import it;
    that refactor is left to the orchestrator because 11.5 is already promoted.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm114Aux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-! ### Connectivity bookkeeping -/

/-- A connected set has an edge leaving any nonempty proper subset. -/
theorem exists_cross_edge {G : SimpleGraph V} {T S : Set V}
    (hT : ConnectedSet G T) (hST : S ⊆ T) {s t : V} (hs : s ∈ S) (ht : t ∈ T) (hts : t ∉ S) :
    ∃ x, x ∈ T ∧ x ∉ S ∧ ∃ y ∈ S, G.Adj x y := by
  classical
  obtain ⟨p⟩ := hT ⟨s, hST hs⟩ ⟨t, ht⟩
  obtain ⟨d, -, hd1, hd2⟩ :=
    p.exists_boundary_dart {u : ↥T | (u : V) ∈ S} hs hts
  exact ⟨(d.snd : V), d.snd.2, hd2, (d.fst : V), hd1, d.adj.symm⟩

/-- An anticonnected subset of `N` is contained in an anticomponent of `N`. -/
theorem exists_anticomponent_containing [Fintype V] {G : SimpleGraph V} {N Q : Set V}
    (hQN : Q ⊆ N) (hQ : AnticonnectedSet G Q) {q : V} (hq : q ∈ Q) :
    ∃ N₁ : Set V, IsComponent Gᶜ N N₁ ∧ Q ⊆ N₁ ∧ q ∈ N₁ := by
  obtain ⟨N₁, hN₁, hqN₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ N (hQN hq)
  have hconn : ConnectedSet Gᶜ (Q ∪ N₁) :=
    ConnectedSetUnionAttach.connectedSet_union hQ hN₁.2.1 (Or.inl ⟨q, hq, hqN₁⟩)
  have heq : Q ∪ N₁ = N₁ :=
    hN₁.2.2 (Q ∪ N₁) Set.subset_union_right (Set.union_subset hQN hN₁.1) hconn
  exact ⟨N₁, hN₁, fun x hx => heq ▸ Or.inl hx, hqN₁⟩

/-- Every vertex of a rung lies in `V(S) = A ∪ B ∪ C`. -/
theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (by rw [hwa]; exact h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (by rw [hwb]; exact h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((PathBasics.mem_interior_iff_of_pathFrom h.1).mpr ⟨hw, hwa, hwb⟩))

/-- **"Since the strip is step-connected, every vertex in `A` has a nonneighbour in `B`."**
(printed p. 67, in the proof of (7)).  Every vertex of `A` is the `A`-end of a rung of some
step, and the `B`-end of the other rung of that step is a nonneighbour of it. -/
theorem exists_nonneighbour_in_B {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {a : V} (ha : a ∈ A) : ∃ b ∈ B, ¬ G.Adj a b := by
  obtain ⟨⟨hdAB, -, -⟩, -, -, hinstep, -⟩ := hS
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ := hinstep a (Or.inl (Or.inl ha))
  obtain ⟨hr₁, hr₂, -, hcross⟩ := hstep
  have hne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := by
    intro x hx y hy hxy
    exact Set.disjoint_left.mp hdAB hx (hxy ▸ hy)
  rcases hmem with hmem | hmem
  · -- `a` is a vertex of `R₁` lying in `A`, hence `a = a₁`
    refine ⟨b₂, hr₂.2.2.1, ?_⟩
    intro hadj
    rcases (hcross a hmem b₂ (PathBasics.isPathFrom_ends_mem hr₂.1).2).mp hadj with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hne a₂ hr₂.2.1 b₂ hr₂.2.2.1 h2.symm
    · exact hne a ha b₁ hr₁.2.2.1 h1
  · refine ⟨b₁, hr₁.2.2.1, ?_⟩
    intro hadj
    rcases (hcross b₁ (PathBasics.isPathFrom_ends_mem hr₁.1).2 a hmem).mp hadj.symm with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne a₁ hr₁.2.1 b₁ hr₁.2.2.1 h1.symm
    · exact hne a ha b₂ hr₂.2.2.1 h2

/-- Two entries of a list at equal indices agree. -/
theorem getElem_eq_index {alpha : Type*} (l : List alpha) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- A three-element list with the two consecutive edges present and the end pair absent
is a path. -/
theorem isPathList_three {G : SimpleGraph V} {a b c : V}
    (hnd : [a, b, c].Nodup) (h1 : G.Adj a b) (h2 : G.Adj b c) (n1 : ¬ G.Adj a c) :
    IsPathList G [a, b, c] := by
  have key : ∀ i j : ℕ, i < 3 → j < 3 →
      ∀ (hi : i < [a, b, c].length) (hj : j < [a, b, c].length),
        (G.Adj ([a, b, c][i]'hi) ([a, b, c][j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi3 hj3
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

/-- Interior membership, indexed. -/
theorem mem_interior_iff_index {G : SimpleGraph V} {p : List V} {u w : V}
    (hp : IsPathFrom G p u w) {x : V} :
    x ∈ SPGT.interior p ↔ ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ k + 2 ≤ p.length ∧
      (p[k]'hk) = x := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = w := PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  constructor
  · intro hx
    rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hx
    obtain ⟨hxm, hxu, hxw⟩ := hx
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxm
    refine ⟨k, hk, ?_, ?_, hkx⟩
    · by_contra hc
      refine hxu ?_
      rw [← hkx, ← h0]
      exact getElem_eq_index p hk hpos (by omega)
    · by_contra hc
      refine hxw ?_
      rw [← hkx, ← hl]
      exact getElem_eq_index p hk (by omega) (by omega)
  · rintro ⟨k, hk, h1, h2, rfl⟩
    exact PathBasics.getElem_mem_interior hp.1 hk h1 h2

/-- In an induced path `u-P-w` on at least three vertices, `u` is adjacent to exactly one
interior vertex (the first) and `w` to exactly one (the last).  This is the paper's *"`p₁-P-p₂`
with `V(P)` minimal"*: minimality is inducedness. -/
theorem interior_ends {G : SimpleGraph V} {p : List V} {u w a b : V}
    (hp : IsPathFrom G p u w) (h3 : 3 ≤ p.length)
    (hint : IsPathFrom G (SPGT.interior p) a b) :
    G.Adj u a ∧ G.Adj w b ∧ (∀ z ∈ SPGT.interior p, G.Adj u z → z = a) ∧
      (∀ z ∈ SPGT.interior p, G.Adj w z → z = b) := by
  have hpos : 0 < p.length := by omega
  have hstd := PathGlue.isPathFrom_interior hp.1 h3
  have ha : a = p[1]'(by omega) := Option.some_injective _ (hint.2.1.symm.trans hstd.2.1)
  have hb : b = p[p.length - 2]'(by omega) :=
    Option.some_injective _ (hint.2.2.symm.trans hstd.2.2)
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = w := PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha, ← h0]
    exact PathBasics.path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
  · have hadj := PathBasics.path_adj_succ hp.1 (show p.length - 2 + 1 < p.length by omega)
    have he : p[p.length - 2 + 1]'(show p.length - 2 + 1 < p.length by omega)
        = p[p.length - 1]'(by omega) := getElem_eq_index p _ _ (by omega)
    rw [hb, ← hl, ← he]
    exact hadj.symm
  · intro z hz hadj
    rw [mem_interior_iff_index hp] at hz
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := hz
    rw [← h0] at hadj
    rcases (PathBasics.path_adj_iff hp.1 hpos hk).mp hadj with h | h
    · rw [ha]
      exact getElem_eq_index p hk (by omega) (by omega)
    · exact absurd h (by omega)
  · intro z hz hadj
    rw [mem_interior_iff_index hp] at hz
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := hz
    rw [← hl] at hadj
    rcases (PathBasics.path_adj_iff hp.1 (show p.length - 1 < p.length by omega) hk).mp hadj
      with h | h
    · exact absurd h (by omega)
    · rw [hb]
      exact getElem_eq_index p hk (by omega) (by omega)

/-- The routine avoidance bookkeeping for a path built through `F`: its ends lie outside
`V(S)` and differ from the excluded star `z`, and its interior lies in `F`. -/
theorem path_avoid {G : SimpleGraph V} {A C B F : Set V} {x y z : V} {P : List V}
    (hFout : ∀ w ∈ F, w ∉ A ∪ B ∪ C) (hP : IsPathFrom G P x y)
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ F)
    (hxS : x ∉ A ∪ B ∪ C) (hyS : y ∉ A ∪ B ∪ C)
    (hxz : x ≠ z) (hyz : y ≠ z) (hzF : z ∉ F) :
    ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({z} : Set V) := by
  intro w hw hcon
  by_cases hwx : w = x
  · rcases hcon with hc | hc
    · exact hxS (hwx ▸ hc)
    · exact hxz (hwx ▸ (Set.mem_singleton_iff.mp hc))
  by_cases hwy : w = y
  · rcases hcon with hc | hc
    · exact hyS (hwy ▸ hc)
    · exact hyz (hwy ▸ (Set.mem_singleton_iff.mp hc))
  · have hwF : w ∈ F :=
      hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hwx, hwy⟩)
    rcases hcon with hc | hc
    · exact hFout w hwF hc
    · exact hzF ((Set.mem_singleton_iff.mp hc) ▸ hwF)

/-- A path with two distinct ends has at least two vertices. -/
theorem len_ge_two {G : SimpleGraph V} {P : List V} {x y : V}
    (hP : IsPathFrom G P x y) (hxy : x ≠ y) : 2 ≤ P.length := by
  have h0 : 0 < P.length := PathBasics.path_length_pos hP.1
  by_contra hcon
  have hone : P.length = 1 := by omega
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hone
  have h1 : c = x := by simpa using hP.2.1
  have h2 : c = y := by simpa using hP.2.2
  exact hxy (h1.symm.trans h2)

/-- A rung with its `A`-end removed: a path inside `B ∪ C` containing the `B`-end. -/
theorem rung_tail {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (hdAB : Disjoint A B) (h : IsRungOfStrip G A C B a p b) :
    ∃ t : List V, p = a :: t ∧ IsPathList G t ∧ (∀ w ∈ t, w ∈ B ∪ C) ∧ b ∈ t := by
  have hne : a ≠ b := fun hc => Set.disjoint_left.mp hdAB h.2.1 (hc ▸ h.2.2.1)
  have hlen : 2 ≤ p.length := len_ge_two h.1 hne
  obtain ⟨c, t, hct⟩ : ∃ c t, p = c :: t := by
    cases p with
    | nil => simp at hlen
    | cons c t => exact ⟨c, t, rfl⟩
  have hca : c = a := by rw [hct] at h; simpa using h.1.2.1
  subst hca
  refine ⟨t, hct, ?_, ?_, ?_⟩
  · have := PathBasics.isPathList_drop h.1.1 (k := 1) (by omega)
    rwa [hct, List.drop_one, List.tail_cons] at this
  · intro w hw
    have hwp : w ∈ p := by rw [hct]; exact List.mem_cons_of_mem _ hw
    have hnodup : (c :: t).Nodup := by rw [← hct]; exact PathBasics.path_nodup h.1.1
    have hwc : w ≠ c := by
      rintro rfl
      exact (List.nodup_cons.mp hnodup).1 hw
    rcases rung_mem_strip h w hwp with (hA | hB) | hC
    · exact absurd (h.2.2.2.1 w hwp hA) hwc
    · exact Or.inl hB
    · exact Or.inr hC
  · have hbp : b ∈ p := (PathBasics.isPathFrom_ends_mem h.1).2
    rw [hct] at hbp
    rcases List.mem_cons.mp hbp with hb | hb
    · exact absurd hb.symm hne
    · exact hb

/-- **"`B ∪ C` is connected (because every vertex of `B ∪ C` is in a step and the strip is
step-connected)"** — printed p. 66, in the proof of (3).

The component `K` of `B ∪ C` containing a fixed vertex of `B` absorbs all of `B` (any
partition of `B` is crossed by a stepped edge) and then all of `C` (each vertex of `C` lies
on a rung, whose `A`-end-deleted tail is a connected subset of `B ∪ C` meeting `B`). -/
theorem bc_connected [Fintype V] {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) : ConnectedSet G (B ∪ C) := by
  obtain ⟨⟨hdAB, hdAC, hdBC⟩, ⟨hAne, hBne⟩, hrung, -, hpart⟩ := hS
  obtain ⟨bstar, hbstar⟩ := hBne
  obtain ⟨K, hK, hbK⟩ :=
    ComponentsOfSetBasics.exists_isComponent_mem G (B ∪ C) (Or.inl hbstar : bstar ∈ B ∪ C)
  -- absorbing a vertex of `B ∪ C` with a neighbour in `K`
  have absorb : ∀ x ∈ B ∪ C, (∃ y ∈ K, G.Adj x y) → x ∈ K := by
    intro x hx hxy
    have hcon : ConnectedSet G (K ∪ {x}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hK.2.1 hxy
    have := hK.2.2 (K ∪ {x}) Set.subset_union_left
      (Set.union_subset hK.1 (Set.singleton_subset_iff.mpr hx)) hcon
    exact this ▸ (Or.inr rfl : x ∈ K ∪ {x})
  -- absorbing a connected subset of `B ∪ C` meeting `K`
  have absorbSet : ∀ S : Set V, S ⊆ B ∪ C → ConnectedSet G S → (S ∩ K).Nonempty → S ⊆ K := by
    intro S hSsub hScon hmeet
    have hcon : ConnectedSet G (K ∪ S) :=
      ConnectedSetUnionAttach.connectedSet_union hK.2.1 hScon
        (Or.inl (by obtain ⟨z, hzS, hzK⟩ := hmeet; exact ⟨z, hzK, hzS⟩))
    have := hK.2.2 (K ∪ S) Set.subset_union_left (Set.union_subset hK.1 hSsub) hcon
    exact fun z hz => this ▸ (Or.inr hz : z ∈ K ∪ S)
  -- (i) `B ⊆ K`
  have hBK : B ⊆ K := by
    by_contra hcon
    obtain ⟨t, htB, htK⟩ := Set.not_subset.mp hcon
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, h1, h2⟩ :=
      hpart (B ∩ K) (B \ K) (Or.inr (by
          ext x
          simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
          constructor
          · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
          · intro hx; by_cases h : x ∈ K
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr ⟨hx, h⟩))
        (Set.disjoint_left.mpr (fun x hx hx' => hx'.2 hx.2))
        ⟨bstar, hbstar, hbK⟩ ⟨t, htB, htK⟩
    obtain ⟨hr₁, hr₂, -, hcross⟩ := hstep
    have hAB : ∀ x ∈ A, x ∉ B := fun x hx => Set.disjoint_left.mp hdAB hx
    have hb₁ : b₁ ∈ B ∩ K := by
      rcases h1 with h1 | h1
      · exact absurd h1.1 (hAB a₁ hr₁.2.1)
      · exact h1
    have hb₂ : b₂ ∈ B \ K := by
      rcases h2 with h2 | h2
      · exact absurd h2.1 (hAB a₂ hr₂.2.1)
      · exact h2
    refine hb₂.2 (absorb b₂ (Or.inl hb₂.1) ⟨b₁, hb₁.2, ?_⟩)
    exact ((hcross b₁ (PathBasics.isPathFrom_ends_mem hr₁.1).2 b₂
      (PathBasics.isPathFrom_ends_mem hr₂.1).2).mpr (Or.inr ⟨rfl, rfl⟩)).symm
  -- (ii) `C ⊆ K`
  have hCK : C ⊆ K := by
    intro v hv
    obtain ⟨a, p, b, hr, hvp⟩ := hrung v (Or.inr hv)
    obtain ⟨t, hpt, htpath, htBC, hbt⟩ := rung_tail hdAB hr
    have hvt : v ∈ t := by
      rw [hpt] at hvp
      rcases List.mem_cons.mp hvp with h | h
      · exact absurd (h ▸ hr.2.1) (Set.disjoint_right.mp hdAC hv)
      · exact h
    refine absorbSet {w : V | w ∈ t} htBC
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htpath)
      ⟨b, hbt, hBK hr.2.2.1⟩ hvt
  have hKeq : K = B ∪ C := Set.Subset.antisymm hK.1 (Set.union_subset hBK hCK)
  rw [← hKeq]
  exact hK.2.1

/-- A left- or right-star is never in `F`: it has a neighbour in `V(S)`, and `F` has none. -/
theorem star_notMem_F {G : SimpleGraph V} {A C B F : Set V}
    (hFanti : SPGT.Anticomplete G F (A ∪ B ∪ C)) {x y : V} (hy : y ∈ A ∪ B ∪ C)
    (hadj : G.Adj x y) : x ∉ F := fun hx => hFanti x hx y hy hadj

/-- **The banister the paper uses without comment**: a 1-breaker supplies a left-star and a
right-star each with a neighbour in the connected set `F`, and `F` is anticomplete to `V(S)`,
so a path between them with interior in `F` is a banister. -/
theorem banister_through_F {G : SimpleGraph V} {A C B F : Set V} {a₀ b₀ : V}
    (hFout : ∀ v ∈ F, v ∉ A ∪ B ∪ C)
    (hFanti : SPGT.Anticomplete G F (A ∪ B ∪ C)) (hFconn : ConnectedSet G F)
    (hLS : IsLeftStar G A C B a₀) (hRS : IsRightStar G A C B b₀)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (ha₀F : ∃ f ∈ F, G.Adj a₀ f) (hb₀F : ∃ f ∈ F, G.Adj b₀ f) :
    ∃ R₀ : List V, IsBanister G A C B a₀ R₀ b₀ ∧ (∀ w ∈ SPGT.interior R₀, w ∈ F) := by
  obtain ⟨x, hx⟩ := hAne
  obtain ⟨y, hy⟩ := hBne
  have ha₀ : a₀ ∉ F := star_notMem_F hFanti (Or.inl (Or.inl hx)) (hLS.2.1 x hx)
  have hb₀ : b₀ ∉ F := star_notMem_F hFanti (Or.inl (Or.inr hy)) (hRS.2.1 y hy)
  obtain ⟨p, hp, hint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn ha₀ hb₀ ha₀F hb₀F
  refine ⟨p, ⟨hp, ?_, hLS, hRS, ?_⟩, hint⟩
  · intro w hw
    by_cases hwa : w = a₀
    · exact hwa ▸ hLS.1
    by_cases hwb : w = b₀
    · exact hwb ▸ hRS.1
    · exact hFout w
        (hint w ((PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hw, hwa, hwb⟩))
  · intro w hw z hz
    exact hFanti w (hint w hw) z hz
end Workspace.ProofLemmas.Thm114Aux
