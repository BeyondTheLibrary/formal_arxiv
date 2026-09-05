import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.WheelConverse
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_10

/-!
# The first half of claim (1) in the proof of 16.3

PAPER (printed p. 101, inside the proof of 16.3, claim (1)): *"Suppose there is such a vertex
`v`.  Suppose first that there is an odd `Y ∪ {v}`-segment in `C`.  From the maximality of `Y`,
`(C, Y ∪ {v})` is therefore not a wheel, and so there is a unique `Y ∪ {v}`-complete edge in `C`.
By 2.10, either `v` has only two neighbours in `C`, or some vertex of `Y` has only three, in
either case a contradiction.  **So there is no odd `Y ∪ {v}`-segment in `C`.**"*

That last sentence is what this module proves.  The printed *"and so"* compresses a chain the
authors leave implicit; it is recorded in `AMBIGUITIES.md` and reproduced here:

1. `(C, Y ∪ {v})` is not a wheel, so by `WheelConverse.yEdgeCount_le_two_of_not_isWheel` the rim
   carries at most two `Y ∪ {v}`-complete edges.
2. The odd `Y ∪ {v}`-segment `S` has an **even** number of vertices, and four or more vertices
   would already give two *disjoint* `Y ∪ {v}`-complete edges, i.e. a wheel.  So `S` has exactly
   two vertices, and (`SegmentBasics.isSegment_run`) the two cyclic positions flanking it are not
   `Y ∪ {v}`-complete.
3. A second `Y ∪ {v}`-complete edge of `C` would either flank `S` — contradicting 2 — or be
   disjoint from `S`'s edge, giving a wheel.  So there is exactly **one**.
4. One is odd, so the second bullet of 2.3 gives *exactly two* `Y ∪ {v}`-complete **vertices**,
   and they are adjacent — which is what 2.10 consumes.
5. 2.10 produces a hat or a leap inside `Y ∪ {v}`.  A hat has two neighbours on `C`, and each of
   the two vertices of a leap has three; but every vertex of `Y` has at least four (the four ends
   of the two disjoint `Y`-complete edges of the wheel `(C,Y)`).  So the hat is `v` — and then
   `a, b` are its only neighbours on `C`, hence adjacent, contrary to hypothesis — and both
   vertices of a leap are `v`, contrary to their being distinct.

Nothing else in this module corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelNoOddExtSegment

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Small bridges between `CycVert`, `CycEdge` and the list -/

private theorem cycVert_getElem (hn : 0 < C.length) {m : ℕ}
    (h : SegmentBasics.CycVert G Y C m) :
    VertexComplete G (C[m % C.length]'(Nat.mod_lt _ hn)) Y := by
  obtain ⟨u, hu, huY⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu
  rw [Option.some_injective _ hu]
  exact huY

private theorem cycEdge_congr {a b : ℕ} (h : a % C.length = b % C.length) :
    WheelParity.CycEdge G Y C a ↔ WheelParity.CycEdge G Y C b := by
  simp only [WheelParity.CycEdge, h, SegmentBasics.add_mod_congr h 1]

private theorem cycVert_of_cycEdge_left {m : ℕ}
    (h : WheelParity.CycEdge G Y C m) : SegmentBasics.CycVert G Y C m := by
  obtain ⟨u, w, hu, hw, hE⟩ := h
  exact ⟨u, hu, hE.2.1⟩

private theorem cycVert_of_cycEdge_right {m : ℕ}
    (h : WheelParity.CycEdge G Y C m) : SegmentBasics.CycVert G Y C (m + 1) := by
  obtain ⟨u, w, hu, hw, hE⟩ := h
  exact ⟨w, hw, hE.2.2⟩

private theorem hole_adj_cyc (hC : IsHoleList G C) (hn : 0 < C.length) (m : ℕ) :
    G.Adj (C[m % C.length]'(Nat.mod_lt _ hn)) (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  refine (HoleBasics.hole_adj_iff hC (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)).mpr (Or.inl ?_)
  rw [Nat.mod_add_mod]

private theorem cycEdge_of_cycVert (hC : IsHoleList G C) (hn : 0 < C.length) {m : ℕ}
    (h1 : SegmentBasics.CycVert G Y C m) (h2 : SegmentBasics.CycVert G Y C (m + 1)) :
    WheelParity.CycEdge G Y C m :=
  ⟨_, _, List.getElem?_eq_getElem (Nat.mod_lt _ hn),
    List.getElem?_eq_getElem (Nat.mod_lt _ hn),
    ⟨hole_adj_cyc hC hn m, cycVert_getElem hn h1, cycVert_getElem hn h2⟩⟩

private theorem succ_mod_inj' {n p q : ℕ} (hp : p < n) (hq : q < n)
    (h : (p + 1) % n = (q + 1) % n) : p = q := by
  have e1 : (p + 1) % n = if p + 1 = n then 0 else p + 1 := by
    by_cases h' : p + 1 = n
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  have e2 : (q + 1) % n = if q + 1 = n then 0 else q + 1 := by
    by_cases h' : q + 1 = n
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  split_ifs at h <;> omega

private theorem edgeComplete_of_cycEdge' (hn : 0 < C.length) {m : ℕ}
    (h : WheelParity.CycEdge G Y C m) :
    EdgeComplete G Y (C[m % C.length]'(Nat.mod_lt _ hn))
      (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  obtain ⟨u, w, hu, hw, hE⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu hw
  rw [Option.some_injective _ hu, Option.some_injective _ hw]
  exact hE

/-! ### Pigeonhole -/

private theorem three_not_in_two {x y p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p = x ∨ p = y) (hq : q = x ∨ q = y) (hr : r = x ∨ r = y) : False := by
  have hsub : ({p, q, r} : Set V) ⊆ ({x, y} : Set V) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have e1 : p ∉ ({q, r} : Set V) := by simp [hpq, hpr]
  have e2 : q ∉ ({r} : Set V) := by simp [hqr]
  have h3 : ({p, q, r} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem e1 (Set.toFinite _),
      Set.ncard_insert_of_notMem e2 (Set.toFinite _), Set.ncard_singleton]
  have h2 : ({x, y} : Set V).ncard ≤ 2 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    rw [Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

private theorem four_not_in_three {z₁ z₂ z₃ p q r s : V}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hp : p = z₁ ∨ p = z₂ ∨ p = z₃) (hq : q = z₁ ∨ q = z₂ ∨ q = z₃)
    (hr : r = z₁ ∨ r = z₂ ∨ r = z₃) (hs : s = z₁ ∨ s = z₂ ∨ s = z₃) : False := by
  have hsub : ({p, q, r, s} : Set V) ⊆ ({z₁, z₂, z₃} : Set V) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
    · exact hs
  have e1 : p ∉ ({q, r, s} : Set V) := by simp [hpq, hpr, hps]
  have e2 : q ∉ ({r, s} : Set V) := by simp [hqr, hqs]
  have e3 : r ∉ ({s} : Set V) := by simp [hrs]
  have h4 : ({p, q, r, s} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem e1 (Set.toFinite _),
      Set.ncard_insert_of_notMem e2 (Set.toFinite _),
      Set.ncard_insert_of_notMem e3 (Set.toFinite _), Set.ncard_singleton]
  have h3 : ({z₁, z₂, z₃} : Set V).ncard ≤ 3 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    have := Set.ncard_insert_le z₂ ({z₃} : Set V)
    rw [Set.ncard_singleton] at this
    omega
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-! ### A vertex of a leap has only three neighbours on the rim -/

private theorem leap_nbrs_gen {c' u₁ u₂ : V} {i j₁ j₂ j₃ : ℕ}
    (hadj : ∀ (m : ℕ) (hm : m < (C.rotate i).length),
      ((G.deleteEdges {s(u₁, u₂)}).Adj c' ((C.rotate i)[m]'hm) ↔ (m = j₁ ∨ m = j₂ ∨ m = j₃)))
    (h1 : c' ≠ u₁) (h2 : c' ≠ u₂) :
    ∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj c' z → z = z₁ ∨ z = z₂ ∨ z = z₃ := by
  classical
  refine ⟨(C.rotate i).getD j₁ c', (C.rotate i).getD j₂ c', (C.rotate i).getD j₃ c', ?_⟩
  intro z hz hadjz
  obtain ⟨m, hm, hmz⟩ := List.getElem_of_mem (List.mem_rotate.mpr hz)
  have hHadj : (G.deleteEdges {s(u₁, u₂)}).Adj c' ((C.rotate i)[m]'hm) := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨by rw [hmz]; exact hadjz, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact h1 e1
    · exact h2 e1
  rcases (hadj m hm).mp hHadj with rfl | rfl | rfl
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ hm]; exact hmz.symm)
  · exact Or.inr (Or.inl (by rw [List.getD_eq_getElem _ _ hm]; exact hmz.symm))
  · exact Or.inr (Or.inr (by rw [List.getD_eq_getElem _ _ hm]; exact hmz.symm))

private theorem leap_nbrs_pair {u₁ u₂ a' b' : V}
    (hleap : IsLeapForHole G C u₁ u₂ a' b')
    (ha1 : a' ≠ u₁) (ha2 : a' ≠ u₂) (hb1 : b' ≠ u₁) (hb2 : b' ≠ u₂) :
    (∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj a' z → z = z₁ ∨ z = z₂ ∨ z = z₃) ∧
      (∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj b' z → z = z₁ ∨ z = z₂ ∨ z = z₃) ∧ a' ≠ b' := by
  obtain ⟨-, i, -, -, -, -, hne, -, ha_adj, hb_adj⟩ := hleap
  exact ⟨leap_nbrs_gen ha_adj ha1 ha2, leap_nbrs_gen hb_adj hb1 hb2, hne⟩

/-! ### The main statement -/

/-- PAPER (16.3, claim (1), printed p. 101): *"So there is no odd `Y ∪ {v}`-segment in `C`."* -/
theorem no_odd_ext_segment [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hBerge : Berge G) {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    (hYmax : ¬ ∃ (C' : List V) (Y' : Set V), IsOddWheel G C' Y' ∧ Y ⊂ Y')
    {v : V} (hvC : v ∉ C) (hvY : v ∉ Y) (hvnY : ¬ VertexComplete G v Y)
    {a b : V} (haC : a ∈ C) (hbC : b ∈ C) (hab : a ≠ b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hnadj : ¬ G.Adj a b) :
    ¬ ∃ S : List V, IsSegment G C (Y ∪ {v}) S ∧ Odd (pathLength S) := by
  classical
  rintro ⟨S, hS, hSodd⟩
  obtain ⟨⟨hhole, hlen6⟩, ⟨hYne, hYanti, hCY⟩, p, q, r, t, hpC, hqC, hrC, htC, hpq, hrt,
    hpr, hpt, hqr, hqt⟩ := hw
  have hn6 : 6 ≤ C.length := hlen6
  have hn : 0 < C.length := by omega
  -- `W := Y ∪ {v}` is a strictly larger anticonnected hub, disjoint from `C`
  have hWne : (Y ∪ {v} : Set V).Nonempty := ⟨v, Or.inr rfl⟩
  have hCW : ∀ u ∈ C, u ∉ (Y ∪ {v} : Set V) := by
    intro u hu hmem
    rcases hmem with h | h
    · exact hCY u hu h
    · exact hvC (by rw [← Set.mem_singleton_iff.mp h]; exact hu)
  have hWanti : AnticonnectedSet G (Y ∪ {v} : Set V) := by
    obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y₀ ∈ Y, ¬ G.Adj v y₀ := by
      by_contra hcon
      push Not at hcon
      exact hvnY hcon
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hYanti
      ⟨y₀, hy₀Y, ⟨fun h => hvY (by rw [h]; exact hy₀Y), hy₀⟩⟩
  have hYW : Y ⊂ (Y ∪ {v} : Set V) :=
    ⟨Set.subset_union_left, fun hsub => hvY (hsub (Or.inr rfl))⟩
  -- by the maximality of `Y`, `(C, W)` is not a wheel
  have hnotW : ¬ IsWheel G C (Y ∪ {v} : Set V) := fun hWwheel =>
    hYmax ⟨C, Y ∪ {v}, ⟨hWwheel, S, hS, hSodd⟩, hYW⟩
  -- so the odd `W`-segment has exactly two vertices
  have hSpath : IsPathList G S := hS.1.1
  have hSlenpos : 1 ≤ S.length := PathBasics.path_length_pos hSpath
  have hSeven : Even S.length := (SegmentBasics.odd_pathLength_iff_even_length hSlenpos).mp hSodd
  have hSmemC : ∀ w ∈ S, w ∈ C ∧ VertexComplete G w (Y ∪ {v} : Set V) := hS.1.2.2
  have hSlt4 : S.length < 4 := by
    by_contra hcon
    push Not at hcon
    have i0 : (0 : ℕ) < S.length := by omega
    have i1 : (1 : ℕ) < S.length := by omega
    have i2 : (2 : ℕ) < S.length := by omega
    have i3 : (3 : ℕ) < S.length := by omega
    have e01 : G.Adj (S[0]'i0) (S[1]'i1) := PathBasics.path_adj_succ hSpath (by omega)
    have e23 : G.Adj (S[2]'i2) (S[3]'i3) := PathBasics.path_adj_succ hSpath (by omega)
    exact hnotW ⟨⟨hhole, hlen6⟩, ⟨hWne, hWanti, hCW⟩,
      S[0]'i0, S[1]'i1, S[2]'i2, S[3]'i3,
      (hSmemC _ (List.getElem_mem i0)).1, (hSmemC _ (List.getElem_mem i1)).1,
      (hSmemC _ (List.getElem_mem i2)).1, (hSmemC _ (List.getElem_mem i3)).1,
      ⟨e01, (hSmemC _ (List.getElem_mem i0)).2, (hSmemC _ (List.getElem_mem i1)).2⟩,
      ⟨e23, (hSmemC _ (List.getElem_mem i2)).2, (hSmemC _ (List.getElem_mem i3)).2⟩,
      PathBasics.path_ne_of_ne_index hSpath i0 i2 (by omega),
      PathBasics.path_ne_of_ne_index hSpath i0 i3 (by omega),
      PathBasics.path_ne_of_ne_index hSpath i1 i2 (by omega),
      PathBasics.path_ne_of_ne_index hSpath i1 i3 (by omega)⟩
  have hSlen2 : S.length = 2 := by rcases hSeven with ⟨m, hm⟩; omega
  -- the run description of `S`
  obtain ⟨k, -, hall, hnext, hprev, hmem⟩ :=
    SegmentBasics.isSegment_run hhole hS (by omega)
  rw [hSlen2] at hall hnext
  have hck : SegmentBasics.CycVert G (Y ∪ {v} : Set V) C k := hall 0 (by omega)
  have hck1 : SegmentBasics.CycVert G (Y ∪ {v} : Set V) C (k + 1) := hall 1 (by omega)
  have hcek : WheelParity.CycEdge G (Y ∪ {v} : Set V) C k := cycEdge_of_cycVert hhole hn hck hck1
  -- the rim carries at most two `W`-complete edges
  have hcount : WheelParity.cycCount G (Y ∪ {v} : Set V) C C.length ≤ 2 := by
    have h := WheelConverse.yEdgeCount_le_two_of_not_isWheel hhole hlen6 hWne hWanti hCW hnotW
    rw [OptimalWheelChoice.yEdgeCount_def,
      WheelParity.ncard_yEdges_eq_cycCount hhole] at h
    exact h
  have hkmem : k % C.length ∈
      (Finset.range C.length).filter (fun m => WheelParity.CycEdge G (Y ∪ {v} : Set V) C m) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    exact (cycEdge_congr (by simp)).mp hcek
  -- and in fact exactly one, so the count is odd
  have hnoteven : ¬ Even (WheelParity.cycCount G (Y ∪ {v} : Set V) C C.length) := by
    intro heven
    have hpos : 1 ≤ WheelParity.cycCount G (Y ∪ {v} : Set V) C C.length := by
      rw [WheelParity.cycCount]
      exact Finset.card_pos.mpr ⟨_, hkmem⟩
    have h2 : WheelParity.cycCount G (Y ∪ {v} : Set V) C C.length = 2 := by
      rcases heven with ⟨c, hc⟩; omega
    rw [WheelParity.cycCount] at h2
    obtain ⟨m, hmerase⟩ : (((Finset.range C.length).filter
        (fun m => WheelParity.CycEdge G (Y ∪ {v} : Set V) C m)).erase
        (k % C.length)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hkmem, h2]
      omega
    obtain ⟨hmne, hmmem⟩ := Finset.mem_erase.mp hmerase
    obtain ⟨hmrange, hcem⟩ := Finset.mem_filter.mp hmmem
    have hmlt : m < C.length := Finset.mem_range.mp hmrange
    have hmm : m % C.length = m := Nat.mod_eq_of_lt hmlt
    have hcvm : SegmentBasics.CycVert G (Y ∪ {v} : Set V) C m := cycVert_of_cycEdge_left hcem
    have hcvm1 : SegmentBasics.CycVert G (Y ∪ {v} : Set V) C (m + 1) :=
      cycVert_of_cycEdge_right hcem
    -- the second edge cannot flank `S`
    have hcase1 : m ≠ (k + 1) % C.length := by
      intro hcon
      refine hnext ((SegmentBasics.cycVert_congr ?_).mpr hcvm1)
      rw [hcon, SegmentBasics.add_mod_congr
        (show (k + 1) % C.length % C.length = (k + 1) % C.length by simp) 1]
    have hcase2 : (m + 1) % C.length ≠ k % C.length := by
      intro hcon
      refine hprev ((SegmentBasics.cycVert_congr ?_).mpr hcvm)
      have e := SegmentBasics.add_mod_congr hcon (C.length - 1)
      rw [show m + 1 + (C.length - 1) = m + C.length by omega, Nat.add_mod_right] at e
      rw [← e]
    -- so the two edges are disjoint, and `(C, W)` is a wheel after all
    have hd1 : k % C.length ≠ m := fun h => hmne h.symm
    have hd2 : (k + 1) % C.length ≠ m := fun h => hcase1 h.symm
    have hd3 : k % C.length ≠ (m + 1) % C.length := fun h => hcase2 h.symm
    have hd4 : (k + 1) % C.length ≠ (m + 1) % C.length := by
      intro hcon
      exact hd1 (succ_mod_inj' (Nat.mod_lt _ hn) hmlt
        (by rw [Nat.mod_add_mod]; exact hcon))
    refine hnotW ⟨⟨hhole, hlen6⟩, ⟨hWne, hWanti, hCW⟩,
      C[k % C.length]'(Nat.mod_lt _ hn), C[(k + 1) % C.length]'(Nat.mod_lt _ hn),
      C[m % C.length]'(Nat.mod_lt _ hn), C[(m + 1) % C.length]'(Nat.mod_lt _ hn),
      List.getElem_mem _, List.getElem_mem _, List.getElem_mem _, List.getElem_mem _,
      edgeComplete_of_cycEdge' hn ((cycEdge_congr (by simp)).mp hcek),
      edgeComplete_of_cycEdge' hn hcem, ?_, ?_, ?_, ?_⟩
    · exact HoleBasics.hole_ne_of_ne_index hhole _ _ (by rw [hmm]; exact hd1)
    · exact HoleBasics.hole_ne_of_ne_index hhole _ _ hd3
    · exact HoleBasics.hole_ne_of_ne_index hhole _ _ (by rw [hmm]; exact hd2)
    · exact HoleBasics.hole_ne_of_ne_index hhole _ _ hd4
  -- 2.3: an odd number of `W`-complete edges forces exactly two `W`-complete vertices
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge (Y ∪ {v} : Set V)
    hWanti C (Or.inr hhole) hCW).2 hhole
  rw [WheelParity.ncard_yEdges_eq_cycCount hhole] at h23
  obtain ⟨x, y, hset, hxy, hxyadj⟩ := h23.resolve_left hnoteven
  have hmemxy : ∀ w : V, w ∈ C → VertexComplete G w (Y ∪ {v} : Set V) → w = x ∨ w = y := by
    intro w hwC hwY
    have hmw : w ∈ ({x, y} : Set V) := by rw [← hset]; exact ⟨hwC, hwY⟩
    simpa using hmw
  have hxmem : x ∈ ({x, y} : Set V) := by simp
  have hymem : y ∈ ({x, y} : Set V) := by simp
  rw [← hset] at hxmem hymem
  -- 2.10
  have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge (Y ∪ {v} : Set V)
    hWanti C hhole hCW (by omega) x y hxmem.1 hymem.1 hxyadj hxmem.2 hymem.2 hmemxy
  -- every vertex of `Y` has four distinct neighbours on `C`
  have hfour : ∀ z ∈ Y, G.Adj z p ∧ G.Adj z q ∧ G.Adj z r ∧ G.Adj z t := fun z hz =>
    ⟨(hpq.2.1 z hz).symm, (hpq.2.2 z hz).symm, (hrt.2.1 z hz).symm, (hrt.2.2 z hz).symm⟩
  have hpqne : p ≠ q := hpq.1.ne
  have hrtne : r ≠ t := hrt.1.ne
  have hxne : ∀ c' : V, c' ∈ (Y ∪ {v} : Set V) → c' ≠ x ∧ c' ≠ y := by
    intro c' hc'
    exact ⟨fun he => hCW x hxmem.1 (he ▸ hc'), fun he => hCW y hymem.1 (he ▸ hc')⟩
  rcases h210 with ⟨h, hhW, hhat⟩ | ⟨a', ha'W, b', hb'W, hleap⟩
  · -- a hat
    obtain ⟨-, -, -, -, -, -, honly'⟩ := hhat
    have hnb : ∀ z ∈ C, G.Adj h z → z = x ∨ z = y := by
      intro z hzC hadj
      by_contra hcon
      push Not at hcon
      exact honly' z hzC hcon.1 hcon.2 hadj
    have hhv : h = v := by
      rcases hhW with hY | hv'
      · obtain ⟨h1, h2, h3, -⟩ := hfour h hY
        exact absurd (three_not_in_two hpqne hpr hqr (hnb p hpC h1) (hnb q hqC h2)
          (hnb r hrC h3)) (fun hf => hf)
      · exact Set.mem_singleton_iff.mp hv'
    subst hhv
    rcases hnb a haC hva with e1 | e1 <;> rcases hnb b hbC hvb with e2 | e2
    · exact hab (e1.trans e2.symm)
    · exact hnadj (by rw [e1, e2]; exact hxyadj)
    · exact hnadj (by rw [e1, e2]; exact hxyadj.symm)
    · exact hab (e1.trans e2.symm)
  · -- a leap
    have hkill : ∀ c' : V, c' ∈ (Y ∪ {v} : Set V) →
        (∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj c' z → z = z₁ ∨ z = z₂ ∨ z = z₃) → c' = v := by
      rintro c' (hY | hv') ⟨z₁, z₂, z₃, hz⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hfour c' hY
        exact absurd (four_not_in_three hpqne hpr hpt hqr hqt hrtne
          (hz p hpC h1) (hz q hqC h2) (hz r hrC h3) (hz t htC h4)) (fun hf => hf)
      · exact Set.mem_singleton_iff.mp hv'
    obtain ⟨hna, hnb, hne'⟩ :
        (∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj a' z → z = z₁ ∨ z = z₂ ∨ z = z₃) ∧
          (∃ z₁ z₂ z₃ : V, ∀ z ∈ C, G.Adj b' z → z = z₁ ∨ z = z₂ ∨ z = z₃) ∧ a' ≠ b' := by
      rcases hleap with hl | hl
      · exact leap_nbrs_pair hl (hxne a' ha'W).1 (hxne a' ha'W).2
          (hxne b' hb'W).1 (hxne b' hb'W).2
      · exact leap_nbrs_pair hl (hxne a' ha'W).2 (hxne a' ha'W).1
          (hxne b' hb'W).2 (hxne b' hb'W).1
    exact hne' ((hkill a' ha'W hna).trans (hkill b' hb'W hnb).symm)

end Workspace.ProofLemmas.OddWheelNoOddExtSegment
