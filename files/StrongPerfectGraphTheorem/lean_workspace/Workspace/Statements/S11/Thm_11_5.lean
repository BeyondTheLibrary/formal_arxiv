/-  Proof attempt 1 for statement 11.5 (`Workspace.Statements.S11.SPGT.thm_11_5`).

    WORK IN PROGRESS — the infrastructure block below is being built first; the main
    theorem is still `sorry` in this file and this attempt is NOT a claim of success.

    THE PAPER'S PROOF: `paper/proofs/11_5.md` (perfect.pdf, printed pp. 66-68).  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7
import Workspace.Statements.S04.Thm_4_5
import Workspace.Statements.S11.Thm_11_1
import Workspace.Statements.S11.Thm_11_2
import Workspace.Statements.S11.Thm_11_4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S11

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

/-! ## Infrastructure

None of this is in the paper; it is the bookkeeping the printed proof leaves implicit
(the left/right exchange, connectivity of `B ∪ C`, banisters through `F`, …). -/

namespace Aux

open Workspace.ProofLemmas

variable {V : Type*}

/-! ### The left-right exchange -/

/-- A rung read backwards is a rung of the reversed strip. -/
theorem rung_swap {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : IsRungOfStrip G B C A b p.reverse a := by
  obtain ⟨hp, ha, hb, hA, hB, hC⟩ := h
  refine ⟨PathBasics.isPathFrom_reverse hp, hb, ha, ?_, ?_, ?_⟩
  · intro w hw hwB
    exact hB w (List.mem_reverse.mp hw) hwB
  · intro w hw hwA
    exact hA w (List.mem_reverse.mp hw) hwA
  · intro w hw
    exact hC w (PathBasics.mem_interior_reverse.mp hw)

/-- A step read backwards is a step of the reversed strip. -/
theorem step_swap {G : SimpleGraph V} {A C B : Set V} {a₁ b₁ a₂ b₂ : V}
    {R₁ R₂ : List V} (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G B C A b₁ R₁.reverse a₁ b₂ R₂.reverse a₂ := by
  obtain ⟨hr1, hr2, hdisj, hadj⟩ := h
  refine ⟨rung_swap hr1, rung_swap hr2, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_reverse] at hv ⊢
    exact hdisj v hv
  · intro u hu v hv
    simp only [List.mem_reverse] at hu hv
    exact (hadj u hu v hv).trans or_comm

/-- `V(S)` does not see the order of the two ends of the strip. -/
theorem union3_comm (A B C : Set V) : A ∪ B ∪ C = B ∪ A ∪ C := by
  rw [Set.union_comm A B]

/-- A step-connected strip stays step-connected when its two ends are exchanged. -/
theorem stepConnected_swap {G : SimpleGraph V} {A C B : Set V}
    (h : StepConnected G A C B) : StepConnected G B C A := by
  obtain ⟨⟨hAB, hAC, hBC⟩, ⟨hAne, hBne⟩, hrung, hstep, hpart⟩ := h
  refine ⟨⟨hAB.symm, hBC, hAC⟩, ⟨hBne, hAne⟩, ?_, ?_, ?_⟩
  · intro v hv
    rw [union3_comm B A C] at hv
    obtain ⟨a, p, b, hr, hvp⟩ := hrung v hv
    exact ⟨b, p.reverse, a, rung_swap hr, List.mem_reverse.mpr hvp⟩
  · intro v hv
    rw [union3_comm B A C] at hv
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hv'⟩ := hstep v hv
    exact ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs,
      hv'.imp List.mem_reverse.mpr List.mem_reverse.mpr⟩
  · intro X Y hXY hd hX hY
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, h1, h2⟩ := hpart X Y hXY.symm hd hX hY
    exact ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs, h1.symm, h2.symm⟩

/-- Left-stars of `(A, C, B)` are exactly the right-stars of `(B, C, A)`. -/
theorem isLeftStar_swap {G : SimpleGraph V} {A C B : Set V} {v : V} :
    IsLeftStar G A C B v ↔ IsRightStar G B C A v := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C], h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C] at h1, h2, h3⟩

/-- Right-stars of `(A, C, B)` are exactly the left-stars of `(B, C, A)`. -/
theorem isRightStar_swap {G : SimpleGraph V} {A C B : Set V} {v : V} :
    IsRightStar G A C B v ↔ IsLeftStar G B C A v := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C], h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C] at h1, h2, h3⟩

/-- A 1-breaker of `(A, C, B)` becomes a 1-breaker of the exchanged strip `(B, C, A)` once
the two asymmetric bullets of the definition are supplied in their right-star form.  Those
two are exactly what the paper's claim (2) provides, which is why the paper can only say
*"all hypotheses of the theorem are true with 'left' and 'right' exchanged"* after (2). -/
theorem oneBreaker_swap {G : SimpleGraph V} {A C B F Q : Set V}
    (h : IsOneBreaker G A C B F Q)
    (hRS : ∃ w : V, IsRightStar G A C B w ∧ (∃ f ∈ F, G.Adj w f) ∧
      SPGT.VertexComplete G w Q)
    (hnoRS : ∀ q ∈ Q, ¬ IsRightStar G A C B q) : IsOneBreaker G B C A F Q := by
  obtain ⟨hSC, ⟨hFout, hFconn, hFanti, ⟨u, hu, hufF⟩, ⟨w, hw, hwfF⟩⟩,
    ⟨hQout, hQanti⟩, ⟨hA, hB⟩, hQnbr, -, -⟩ := h
  obtain ⟨z, hz, hzf, hzQ⟩ := hRS
  refine ⟨stepConnected_swap hSC,
    ⟨fun v hv => by rw [union3_comm B A C]; exact hFout v hv, hFconn,
      fun x hx => by rw [union3_comm B A C]; exact hFanti x hx,
      ⟨w, isRightStar_swap.mp hw, hwfF⟩, ⟨u, isLeftStar_swap.mp hu, hufF⟩⟩,
    ⟨fun q hq => by rw [union3_comm B A C]; exact hQout q hq, hQanti⟩,
    ⟨hB, hA⟩, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨(hQnbr q hq).1, by
      obtain ⟨x, hx, hadj⟩ := (hQnbr q hq).2
      exact ⟨x, by rw [union3_comm B A C]; exact hx, hadj⟩⟩
  · exact ⟨z, isRightStar_swap.mp hz, hzf, hzQ⟩
  · intro q hq hcon
    exact hnoRS q hq (isRightStar_swap.mpr hcon)

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

end Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas in
/-- The body of the printed proof of 11.5, for a 1-breaker `(S, F, Q)` chosen with
`|F| + |Q|` maximum *"(possibly exchanging "left" and "right")"*, in a graph that admits no
balanced skew partition.  The paper's claims (1)-(9) are the `have`s below, in order. -/
theorem core {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hno : ¬ AdmitsBalancedSkewPartition G)
    {A C B F Q : Set V} (hbr : IsOneBreaker G A C B F Q)
    (hmax : ∀ F' Q' : Set V,
      (IsOneBreaker G A C B F' Q' ∨ IsOneBreaker G B C A F' Q') →
      F'.ncard + Q'.ncard ≤ F.ncard + Q.ncard) : False := by
  classical
  obtain ⟨hSC, ⟨hFout, hFconn, hFanti, ⟨u₀, hu₀LS, hu₀F⟩, ⟨w₀, hw₀RS, hw₀F⟩⟩,
    ⟨hQout, hQanti⟩, ⟨hAnb, hBnb⟩, hQnbr, ⟨z₀, hz₀LS, hz₀F, hz₀Q⟩, hQnoLS⟩ := id hbr
  obtain ⟨⟨hdAB, hdAC, hdBC⟩, ⟨hAne, hBne⟩, hrungcov, hinstep, hpart⟩ := id hSC
  have hFsub : F ⊆ (A ∪ B ∪ C)ᶜ := fun f hf => hFout f hf
  -- PAPER: *"Let `N` be the set of vertices of `G` not in `F` but with a neighbour in `F`."*
  set N : Set V := {x : V | x ∉ F ∧ ∃ f ∈ F, G.Adj x f} with hNdef
  -- PAPER: *"Hence `Q ⊆ N`, and every left- or right-star with a neighbour in `F` is in `N`."*
  have hNnotS : ∀ x ∈ N, x ∉ A ∪ B ∪ C := by
    intro x hx hxS
    obtain ⟨f, hf, hadj⟩ := hx.2
    exact hFanti f hf x hxS hadj.symm
  have hQN : Q ⊆ N := fun q hq => ⟨fun hc => hQout q hq (Or.inr hc), (hQnbr q hq).1⟩
  have hLSN : ∀ x : V, IsLeftStar G A C B x → (∃ f ∈ F, G.Adj x f) → x ∈ N := by
    intro x hx hxF
    obtain ⟨y, hy⟩ := hAne
    exact ⟨Aux.star_notMem_F hFanti (Or.inl (Or.inl hy)) (hx.2.1 y hy), hxF⟩
  have hRSN : ∀ x : V, IsRightStar G A C B x → (∃ f ∈ F, G.Adj x f) → x ∈ N := by
    intro x hx hxF
    obtain ⟨y, hy⟩ := hBne
    exact ⟨Aux.star_notMem_F hFanti (Or.inl (Or.inr hy)) (hx.2.1 y hy), hxF⟩
  -- ==================================================================================
  -- (1) PAPER: *"Every vertex in `N` has a neighbour in `A ∪ B ∪ C`."*
  -- ==================================================================================
  have claim1 : ∀ x ∈ N, ∃ y ∈ A ∪ B ∪ C, G.Adj x y := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    have hxF : x ∉ F := hx.1
    have hxS : x ∉ A ∪ B ∪ C := hNnotS x hx
    have hxQ : x ∉ Q := by
      intro hq
      obtain ⟨y, hy, hadj⟩ := (hQnbr x hq).2
      exact hcon y hy hadj
    -- PAPER: *"Let `F' = F ∪ {v}`. … It follows that the hypotheses of the theorem remain
    -- true, contrary to the maximality of `|F| + |Q|`."*
    have hbr' : IsOneBreaker G A C B (F ∪ {x}) Q := by
      refine ⟨hSC, ⟨?_, ?_, ?_, ⟨u₀, hu₀LS, ?_⟩, ⟨w₀, hw₀RS, ?_⟩⟩, ⟨?_, hQanti⟩,
        ⟨hAnb, hBnb⟩, ?_, ⟨z₀, hz₀LS, ?_, hz₀Q⟩, hQnoLS⟩
      · rintro v (hv | hv)
        · exact hFout v hv
        · exact (Set.mem_singleton_iff.mp hv) ▸ hxS
      · exact ConnectedSetUnionAttach.connectedSet_union_singleton hFconn hx.2
      · rintro v (hv | hv) y hy
        · exact hFanti v hv y hy
        · exact (Set.mem_singleton_iff.mp hv) ▸ hcon y hy
      · obtain ⟨f, hf, ha⟩ := hu₀F; exact ⟨f, Or.inl hf, ha⟩
      · obtain ⟨f, hf, ha⟩ := hw₀F; exact ⟨f, Or.inl hf, ha⟩
      · intro q hq
        rintro (hc | hc | hc)
        · exact hQout q hq (Or.inl hc)
        · exact hQout q hq (Or.inr hc)
        · exact hxQ ((Set.mem_singleton_iff.mp hc) ▸ hq)
      · intro q hq
        obtain ⟨f, hf, ha⟩ := (hQnbr q hq).1
        exact ⟨⟨f, Or.inl hf, ha⟩, (hQnbr q hq).2⟩
      · obtain ⟨f, hf, ha⟩ := hz₀F; exact ⟨f, Or.inl hf, ha⟩
    have hle := hmax (F ∪ {x}) Q (Or.inl hbr')
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hxF F.toFinite] at hle
    omega
  -- ==================================================================================
  -- (2) PAPER: *"There is no left- or right-star in `Q`, and every left- and right-star
  --     with a neighbour in `F` is `Q`-complete."*
  -- ==================================================================================
  -- The first half is 11.4 applied to `Q` itself: its first bullet is exactly the
  -- configuration the paper rules out.
  have hno114 : ¬ ∃ w : V, IsRightStar G A C B w ∧ (∃ f ∈ F, G.Adj w f) ∧
      ∃ q ∈ Q, ¬ G.Adj w q := by
    intro hex
    exact thm_11_4 G hG hK4 hprism A C B hSC F hFsub hFconn hFanti
      ⟨Q, fun q hq => hQout q hq, hQanti, hex, hBnb, ⟨z₀, hz₀LS, hz₀F, hz₀Q⟩,
        fun q hq => (hQnbr q hq).1, fun q hq => (hQnbr q hq).2, hQnoLS⟩
  have claim2a : ∀ q ∈ Q, ¬ IsRightStar G A C B q := by
    intro q hq hRS
    exact hno114 ⟨q, hRS, (hQnbr q hq).1, q, hq, G.irrefl⟩
  have claim2b : ∀ w : V, IsRightStar G A C B w → (∃ f ∈ F, G.Adj w f) →
      SPGT.VertexComplete G w Q := by
    intro w hRS hwF
    by_contra hcon
    simp only [SPGT.VertexComplete, not_forall] at hcon
    obtain ⟨q, hq⟩ := hcon
    obtain ⟨hqQ, hqadj⟩ := by simpa using hq
    exact hno114 ⟨w, hRS, hwF, q, hqQ, hqadj⟩
  -- PAPER: *"… and so all hypotheses of the theorem are true with "left" and "right"
  -- exchanged."*
  have hbrswap : IsOneBreaker G B C A F Q :=
    Aux.oneBreaker_swap hbr ⟨w₀, hw₀RS, hw₀F, claim2b w₀ hw₀RS hw₀F⟩ claim2a
  -- PAPER: *"It follows by the same argument, therefore, that every left-star with a
  -- neighbour in `F` is `Q`-complete."*
  have claim2c : ∀ u : V, IsLeftStar G A C B u → (∃ f ∈ F, G.Adj u f) →
      SPGT.VertexComplete G u Q := by
    intro u hLS huF
    by_contra hcon
    simp only [SPGT.VertexComplete, not_forall] at hcon
    obtain ⟨q, hq⟩ := hcon
    obtain ⟨hqQ, hqadj⟩ := by simpa using hq
    obtain ⟨hSC', ⟨hFout', hFconn', hFanti', -, -⟩, ⟨hQout', -⟩, -,
      hQnbr', ⟨z₁, hz₁LS, hz₁F, hz₁Q⟩, hQnoLS'⟩ := id hbrswap
    exact thm_11_4 G hG hK4 hprism B C A hSC' F (fun f hf => hFout' f hf) hFconn' hFanti'
      ⟨Q, fun q' hq' => hQout' q' hq', hQanti,
        ⟨u, Aux.isLeftStar_swap.mp hLS, huF, q, hqQ, hqadj⟩, hAnb,
        ⟨z₁, hz₁LS, hz₁F, hz₁Q⟩,
        fun q' hq' => (hQnbr' q' hq').1, fun q' hq' => (hQnbr' q' hq').2, hQnoLS'⟩
  -- ==================================================================================
  -- Shared data: the banister through `F`, the anticomponent `N₁ ⊇ Q`, and basic facts.
  -- ==================================================================================
  have hK4nd : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K', happ, -⟩
    exact hK4 ⟨n, H, K', happ⟩
  have hu₀N : u₀ ∈ N := hLSN u₀ hu₀LS hu₀F
  have hw₀N : w₀ ∈ N := hRSN w₀ hw₀RS hw₀F
  have hu₀nw₀ : u₀ ≠ w₀ := by
    obtain ⟨y, hy⟩ := hAne
    intro hc
    exact hw₀RS.2.2 y (Or.inl hy) (hc ▸ hu₀LS.2.1 y hy)
  obtain ⟨R₀, hban, hR₀int⟩ :=
    Aux.banister_through_F hFout hFanti hFconn hu₀LS hw₀RS hAne hBne hu₀F hw₀F
  obtain ⟨aq, haqA, q₀, hq₀Q, -⟩ := id hAnb
  obtain ⟨N₁, hN₁, hQN₁, hq₀N₁⟩ := Aux.exists_anticomponent_containing hQN hQanti hq₀Q
  -- Distinct anticomponents of `N` are complete to each other in `G`.
  have hN₁complete : ∀ x ∈ N, x ∉ N₁ → ∀ y ∈ N₁, G.Adj x y := by
    intro x hxN hxN₁ y hyN₁
    obtain ⟨M, hM, hxM⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ N hxN
    have hMne : M ≠ N₁ := fun hc => hxN₁ (hc ▸ hxM)
    have hanti := ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ hM hN₁ hMne x hxM y hyN₁
    have hxy : x ≠ y := fun hc => hxN₁ (hc ▸ hyN₁)
    by_contra hadj
    exact hanti ((SimpleGraph.compl_adj G x y).mpr ⟨hxy, hadj⟩)
  -- ==================================================================================
  -- (3) PAPER: *"There is a left- or right-star in `N₁`."*
  -- ==================================================================================
  have claim3 : ∃ s ∈ N₁, IsLeftStar G A C B s ∨ IsRightStar G A C B s := by
    by_contra hcon
    push_neg at hcon
    have hnoLS₁ : ∀ s ∈ N₁, ¬ IsLeftStar G A C B s := fun s hs => (hcon s hs).1
    have hu₀N₁ : u₀ ∉ N₁ := fun hc => (hcon u₀ hc).1 hu₀LS
    have hBCsub : B ∪ C ⊆ A ∪ B ∪ C := by
      rintro x (hx | hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
    -- PAPER: *"let `N₂` be the union of all the anticomponents of `N` different from `N₁`"*
    -- and *"`Y = V(G) \ (F ∪ N)`"*.
    set N₂ : Set V := N \ N₁ with hN₂def
    set Yp : Set V := (F ∪ N)ᶜ with hYpdef
    have hSY : A ∪ B ∪ C ⊆ Yp := by
      intro x hx
      simp only [hYpdef, Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨fun hc => hFout x hc hx, fun hc => hNnotS x hc hx⟩
    -- PAPER: *"there are no edges between `F` and `Y`, from definition of `N`"*
    have hFY : SPGT.Anticomplete G F Yp := by
      intro f hf y hy hadj
      simp only [hYpdef, Set.mem_compl_iff, Set.mem_union, not_or] at hy
      exact hy.2 ⟨hy.1, f, hf, hadj.symm⟩
    have hFne : F.Nonempty := by obtain ⟨f, hf, -⟩ := hu₀F; exact ⟨f, hf⟩
    have hN₁ne : N₁.Nonempty := ⟨q₀, hq₀N₁⟩
    have hN₂ne : N₂.Nonempty := ⟨u₀, hu₀N, hu₀N₁⟩
    have hYne : Yp.Nonempty := ⟨aq, hSY (Or.inl (Or.inl haqA))⟩
    -- PAPER: *"every vertex in `N₁` has a neighbour in `B` (since otherwise it would be a
    -- left-star by 11.1 and therefore belong to `N₂`)"*
    have hN₁B : ∀ x ∈ N₁, ∃ b ∈ B, G.Adj x b := by
      intro x hx
      by_contra hcb
      push_neg at hcb
      have hxN : x ∈ N := hN₁.1 hx
      have hxS : x ∉ A ∪ B ∪ C := hNnotS x hxN
      have hxu₀ : x ≠ u₀ := fun hc => hu₀N₁ (hc ▸ hx)
      have hw₀nF : w₀ ∉ F := by
        obtain ⟨y, hy⟩ := hBne
        exact Aux.star_notMem_F hFanti (Or.inl (Or.inr hy)) (hw₀RS.2.1 y hy)
      obtain ⟨P, hP, hPint⟩ :=
        MinimalConnectedIsPath.exists_path_interior_in hFconn hxN.1 hw₀nF hxN.2 hw₀F
      have hu₀nF : u₀ ∉ F := by
        obtain ⟨y, hy⟩ := hAne
        exact Aux.star_notMem_F hFanti (Or.inl (Or.inl hy)) (hu₀LS.2.1 y hy)
      refine hnoLS₁ x hx (thm_11_1 G hG hK4nd A C B hSC u₀ w₀ R₀ hban x hxS ?_ hcb P hP ?_ ?_)
      · obtain ⟨y, hy, hadj⟩ := claim1 x hxN
        rcases hy with (hyA | hyB) | hyC
        · exact ⟨y, Or.inl hyA, hadj⟩
        · exact absurd hadj (hcb y hyB)
        · exact ⟨y, Or.inr hyC, hadj⟩
      · intro w hw
        by_cases hwx : w = x
        · rintro (hc | hc)
          · exact hxS (hwx ▸ hc)
          · exact hxu₀ (hwx ▸ Set.mem_singleton_iff.mp hc)
        by_cases hww : w = w₀
        · rintro (hc | hc)
          · exact hw₀RS.1 (hww ▸ hc)
          · exact hu₀nw₀ ((Set.mem_singleton_iff.mp (hww ▸ hc)).symm)
        · have hwF : w ∈ F :=
            hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hwx, hww⟩)
          rintro (hc | hc)
          · exact hFout w hwF hc
          · exact hu₀nF ((Set.mem_singleton_iff.mp hc) ▸ hwF)
      · intro w hw y hy
        exact hFanti w (hPint w hw) y hy
    -- PAPER: *"Now `(B ∪ C, N₁)` is balanced, by 2.6, since any left-star is complete to
    -- `N₁` and anticomplete to `B ∪ C`."*
    have hdisjBCN₁ : Disjoint (B ∪ C) N₁ := by
      rw [Set.disjoint_left]
      rintro x hx hxN₁
      rcases hx with hxB | hxC
      · exact hNnotS x (hN₁.1 hxN₁) (Or.inl (Or.inr hxB))
      · exact hNnotS x (hN₁.1 hxN₁) (Or.inr hxC)
    have hbalBC : SPGT.Balanced G (B ∪ C) N₁ := by
      refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hG (B ∪ C) N₁ hdisjBCN₁ u₀ ?_ ?_ ?_
      · rintro (hc | hc)
        · exact hu₀LS.1 (hBCsub hc)
        · exact hu₀N₁ hc
      · exact fun y hy => hN₁complete u₀ hu₀N hu₀N₁ y hy
      · exact hu₀LS.2.2
    -- PAPER: *"Since `B ∪ C` is connected …, it follows from 2.7.1 that `(F, N₁)` is
    -- balanced."*
    have hbalF : SPGT.Balanced G F N₁ := by
      refine (_root_.Workspace.Statements.S02.SPGT.thm_2_7 G hG (B ∪ C) N₁ hbalBC F ?_).1
        (Aux.bc_connected hSC) ?_ ?_
      · intro f hf hcon
        rcases hcon with hc | hc
        · exact hFout f hf (hBCsub hc)
        · exact (hN₁.1 hc).1 hf
      · intro b hb
        obtain ⟨y, hy, hadj⟩ := hN₁B b hb
        exact ⟨y, Or.inl hy, hadj⟩
      · intro x hx f hf hadj
        exact hFanti f hf x (hBCsub hx) hadj.symm
    -- PAPER: *"From 4.5, `G` admits a balanced skew partition, a contradiction."*
    refine hno (_root_.Workspace.Statements.S04.SPGT.thm_4_5 G hG N₂ N₁ F Yp
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hN₂ne hN₁ne hFne hYne hFY ?_
      (Or.inr (Or.inr hbalF)))
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true, hN₂def, hYpdef, Set.mem_diff,
        Set.mem_compl_iff, not_or]
      by_cases hxF : x ∈ F
      · exact Or.inl (Or.inr hxF)
      by_cases hxN : x ∈ N
      · by_cases hxN₁ : x ∈ N₁
        · exact Or.inl (Or.inl (Or.inr hxN₁))
        · exact Or.inl (Or.inl (Or.inl ⟨hxN, hxN₁⟩))
      · exact Or.inr ⟨hxF, hxN⟩
    · exact Set.disjoint_left.mpr fun x hx hx' => hx.2 hx'
    · exact Set.disjoint_left.mpr fun x hx hx' => hx.1.1 hx'
    · exact Set.disjoint_left.mpr fun x hx hx' => hx' (Or.inr hx.1)
    · exact Set.disjoint_left.mpr fun x hx hx' => (hN₁.1 hx).1 hx'
    · exact Set.disjoint_left.mpr fun x hx hx' => hx' (Or.inr (hN₁.1 hx))
    · exact Set.disjoint_left.mpr fun x hx hx' => hx' (Or.inl hx)
    · exact fun x hx y hy => hN₁complete x hx.1 hx.2 y hy
  -- ==================================================================================
  -- PAPER: *"From (3), `N₁ ≠ Q`; and hence there is a vertex `v ∈ N \ Q` with a
  --     nonneighbour in `Q`."*
  -- ==================================================================================
  obtain ⟨sstar, hsN₁, hsStar⟩ := claim3
  have hsQ : sstar ∉ Q := by
    intro hq
    rcases hsStar with h | h
    · exact hQnoLS sstar hq h
    · exact claim2a sstar hq h
  obtain ⟨v, hvN₁, hvQ, q', hq'Q, hvq'⟩ :=
    Aux.exists_cross_edge (G := Gᶜ) hN₁.2.1 hQN₁ hq₀Q hsN₁ hsQ
  have hvN : v ∈ N := hN₁.1 hvN₁
  have hvF : v ∉ F := hvN.1
  have hvS : v ∉ A ∪ B ∪ C := hNnotS v hvN
  have hvnbQ : ∃ q ∈ Q, ¬ G.Adj v q :=
    ⟨q', hq'Q, ((SimpleGraph.compl_adj G v q').mp hvq').2⟩
  -- PAPER: *"`v` is not a left-star since all left-stars in `N` are `Q`-complete by (2)"*
  have hvnotLS : ¬ IsLeftStar G A C B v := by
    intro h
    obtain ⟨q, hqQ, hnadj⟩ := hvnbQ
    exact hnadj (claim2c v h hvN.2 q hqQ)
  have hvnotRS : ¬ IsRightStar G A C B v := by
    intro h
    obtain ⟨q, hqQ, hnadj⟩ := hvnbQ
    exact hnadj (claim2b v h hvN.2 q hqQ)
  -- PAPER: *"From the maximality of `|F| + |Q|`, replacing `Q` by `Q ∪ {v}` violates one of
  --     the hypotheses of the theorem."*
  have hQvanti : SPGT.AnticonnectedSet G (Q ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hQanti ⟨q', hq'Q, hvq'⟩
  have hQvcard : (Q ∪ ({v} : Set V)).ncard = Q.ncard + 1 := by
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hvQ Q.toFinite]
  have hQvnbr : ∀ q ∈ Q ∪ ({v} : Set V),
      (∃ f ∈ F, G.Adj q f) ∧ ∃ w ∈ A ∪ B ∪ C, G.Adj q w := by
    intro q hq
    rcases hq with hq | hq
    · exact hQnbr q hq
    · rw [show q = v from hq]
      exact ⟨hvN.2, claim1 v hvN⟩
  -- PAPER: *"so no left-star in `N` is `Q ∪ {v}`-complete.  Since they are all `Q`-complete,
  --     it follows that `v` is nonadjacent to every left-star in `N`."*
  have hvnadjLS : ∀ u : V, IsLeftStar G A C B u → (∃ f ∈ F, G.Adj u f) → ¬ G.Adj u v := by
    intro u hu huF hadj
    have hbr' : IsOneBreaker G A C B F (Q ∪ {v}) := by
      refine ⟨hSC, ⟨hFout, hFconn, hFanti, ⟨u₀, hu₀LS, hu₀F⟩, ⟨w₀, hw₀RS, hw₀F⟩⟩,
        ⟨?_, hQvanti⟩, ⟨?_, ?_⟩, hQvnbr, ⟨u, hu, huF, ?_⟩, ?_⟩
      · intro q hq
        rcases hq with hq | hq
        · exact hQout q hq
        · rw [show q = v from hq]
          intro hcon
          rcases hcon with hc | hc
          · exact hvS hc
          · exact hvF hc
      · obtain ⟨a, ha, q, hq, hnq⟩ := hAnb
        exact ⟨a, ha, q, Or.inl hq, hnq⟩
      · obtain ⟨b, hb, q, hq, hnq⟩ := hBnb
        exact ⟨b, hb, q, Or.inl hq, hnq⟩
      · intro q hq
        rcases hq with hq | hq
        · exact claim2c u hu huF q hq
        · rw [show q = v from hq]
          exact hadj
      · intro q hq
        rcases hq with hq | hq
        · exact hQnoLS q hq
        · rw [show q = v from hq]
          exact hvnotLS
    have hle := hmax F (Q ∪ {v}) (Or.inl hbr')
    rw [hQvcard] at hle
    omega
  -- PAPER: *"Similarly `v` is nonadjacent to every right-star in `N`."*
  have hvnadjRS : ∀ w : V, IsRightStar G A C B w → (∃ f ∈ F, G.Adj w f) → ¬ G.Adj w v := by
    intro w hw hwF hadj
    obtain ⟨hSC', hFblk', ⟨hQout', -⟩, ⟨hAnb', hBnb'⟩, hQnbr', -, -⟩ := id hbrswap
    have hbr' : IsOneBreaker G B C A F (Q ∪ {v}) := by
      refine ⟨hSC', hFblk', ⟨?_, hQvanti⟩, ⟨?_, ?_⟩, ?_,
        ⟨w, Aux.isRightStar_swap.mp hw, hwF, ?_⟩, ?_⟩
      · intro q hq
        rcases hq with hq | hq
        · exact hQout' q hq
        · rw [show q = v from hq]
          intro hcon
          rcases hcon with hc | hc
          · rw [Aux.union3_comm B A C] at hc
            exact hvS hc
          · exact hvF hc
      · obtain ⟨a, ha, q, hq, hnq⟩ := hAnb'
        exact ⟨a, ha, q, Or.inl hq, hnq⟩
      · obtain ⟨b, hb, q, hq, hnq⟩ := hBnb'
        exact ⟨b, hb, q, Or.inl hq, hnq⟩
      · intro q hq
        rcases hq with hq | hq
        · exact hQnbr' q hq
        · rw [show q = v from hq]
          refine ⟨hvN.2, ?_⟩
          obtain ⟨y, hy, hadjy⟩ := claim1 v hvN
          refine ⟨y, ?_, hadjy⟩
          rw [Aux.union3_comm B A C]
          exact hy
      · intro q hq
        rcases hq with hq | hq
        · exact claim2b w hw hwF q hq
        · rw [show q = v from hq]
          exact hadj
      · intro q hq hcon
        rcases hq with hq | hq
        · exact claim2a q hq (Aux.isRightStar_swap.mpr hcon)
        · rw [show q = v from hq] at hcon
          exact hvnotRS (Aux.isRightStar_swap.mpr hcon)
    have hle := hmax F (Q ∪ {v}) (Or.inr hbr')
    rw [hQvcard] at hle
    omega
  have hvnu₀ : ¬ G.Adj u₀ v := hvnadjLS u₀ hu₀LS hu₀F
  have hvnw₀ : ¬ G.Adj w₀ v := hvnadjRS w₀ hw₀RS hw₀F
  -- ==================================================================================
  -- (4) PAPER: *"`v` is complete to `A ∪ B`."*
  -- ==================================================================================
  have hvnew₀ : v ≠ w₀ := fun hc => hvnotRS (hc ▸ hw₀RS)
  have hvneu₀ : v ≠ u₀ := fun hc => hvnotLS (hc ▸ hu₀LS)
  obtain ⟨PA, hPA, hPAint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hvF hu₀N.1 hvN.2 hu₀F
  obtain ⟨PB, hPB, hPBint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hvF hw₀N.1 hvN.2 hw₀F
  have hPAavoid : ∀ w ∈ PA, w ∉ (A ∪ B ∪ C) ∪ ({w₀} : Set V) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      intro hcon
      rcases hcon with hc | hc
      · exact hvS hc
      · exact hvnew₀ (Set.mem_singleton_iff.mp hc)
    by_cases hwu : w = u₀
    · subst hwu
      intro hcon
      rcases hcon with hc | hc
      · exact hu₀LS.1 hc
      · exact hu₀nw₀ (Set.mem_singleton_iff.mp hc)
    · have hwF : w ∈ F :=
        hPAint w ((PathBasics.mem_interior_iff_of_pathFrom hPA).mpr ⟨hw, hwv, hwu⟩)
      intro hcon
      rcases hcon with hc | hc
      · exact hFout w hwF hc
      · exact hw₀N.1 ((Set.mem_singleton_iff.mp hc) ▸ hwF)
  have hPBavoid : ∀ w ∈ PB, w ∉ (A ∪ B ∪ C) ∪ ({u₀} : Set V) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      intro hcon
      rcases hcon with hc | hc
      · exact hvS hc
      · exact hvneu₀ (Set.mem_singleton_iff.mp hc)
    by_cases hww : w = w₀
    · subst hww
      intro hcon
      rcases hcon with hc | hc
      · exact hw₀RS.1 hc
      · exact hu₀nw₀ ((Set.mem_singleton_iff.mp hc).symm)
    · have hwF : w ∈ F :=
        hPBint w ((PathBasics.mem_interior_iff_of_pathFrom hPB).mpr ⟨hw, hwv, hww⟩)
      intro hcon
      rcases hcon with hc | hc
      · exact hFout w hwF hc
      · exact hu₀N.1 ((Set.mem_singleton_iff.mp hc) ▸ hwF)
  have hPQint : SPGT.Anticomplete G
      ({w : V | w ∈ SPGT.interior PA} ∪ {w : V | w ∈ SPGT.interior PB}) (A ∪ B ∪ C) := by
    intro x hx y hy
    rcases hx with hx | hx
    · exact hFanti x (hPAint x hx) y hy
    · exact hFanti x (hPBint x hx) y hy
  -- PAPER: *"By 11.2, `v` is a left-star, a contradiction."*
  have hvB : SPGT.VertexComplete G v B := by
    rcases thm_11_2 G hG hK4 A C B hSC u₀ w₀ R₀ hban v hvS (claim1 v hvN)
        (fun hc => hvnw₀ hc.symm) PA PB hPA hPAavoid hPB hPBavoid hPQint with h | h
    · exact h
    · exact absurd h hvnotLS
  have hSCswap : StepConnected G B C A := Aux.stepConnected_swap hSC
  have hFoutswap : ∀ x ∈ F, x ∉ B ∪ A ∪ C := by
    intro x hx
    rw [Aux.union3_comm B A C]
    exact hFout x hx
  have hFantiswap : SPGT.Anticomplete G F (B ∪ A ∪ C) := by
    intro x hx y hy
    rw [Aux.union3_comm B A C] at hy
    exact hFanti x hx y hy
  obtain ⟨R₀', hban', hR₀'int⟩ :=
    Aux.banister_through_F hFoutswap hFantiswap hFconn (Aux.isRightStar_swap.mp hw₀RS)
      (Aux.isLeftStar_swap.mp hu₀LS) hBne hAne hw₀F hu₀F
  have hvA : SPGT.VertexComplete G v A := by
    have hvSswap : v ∉ B ∪ A ∪ C := by rw [Aux.union3_comm B A C]; exact hvS
    have hvSswap' : ∃ x ∈ B ∪ A ∪ C, G.Adj v x := by
      obtain ⟨y, hy, hadjy⟩ := claim1 v hvN
      exact ⟨y, by rw [Aux.union3_comm B A C]; exact hy, hadjy⟩
    have hPBavoid' : ∀ w ∈ PB, w ∉ (B ∪ A ∪ C) ∪ ({u₀} : Set V) := by
      intro w hw hcon
      refine hPBavoid w hw ?_
      rcases hcon with hc | hc
      · rw [Aux.union3_comm B A C] at hc
        exact Or.inl hc
      · exact Or.inr hc
    have hPAavoid' : ∀ w ∈ PA, w ∉ (B ∪ A ∪ C) ∪ ({w₀} : Set V) := by
      intro w hw hcon
      refine hPAavoid w hw ?_
      rcases hcon with hc | hc
      · rw [Aux.union3_comm B A C] at hc
        exact Or.inl hc
      · exact Or.inr hc
    have hPQint' : SPGT.Anticomplete G
        ({w : V | w ∈ SPGT.interior PB} ∪ {w : V | w ∈ SPGT.interior PA}) (B ∪ A ∪ C) := by
      intro x hx y hy
      rw [Aux.union3_comm B A C] at hy
      rcases hx with hx | hx
      · exact hFanti x (hPBint x hx) y hy
      · exact hFanti x (hPAint x hx) y hy
    rcases thm_11_2 G hG hK4 B C A hSCswap w₀ u₀ R₀' hban' v hvSswap hvSswap'
        (fun hc => hvnu₀ hc.symm) PB PA hPB hPBavoid' hPA hPAavoid' hPQint' with h | h
    · exact h
    · exact absurd (Aux.isLeftStar_swap.mp h) hvnotRS
  have hvAB : ∀ x ∈ A ∪ B, G.Adj v x := by
    rintro x (hx | hx)
    · exact hvA x hx
    · exact hvB x hx
  -- ==================================================================================
  -- PAPER: *"Choose an antipath `v-q₁-⋯-q_k` in `Q`, such that `q_k` has a nonneighbour
  --     in `A ∪ B`, with `k` minimum."*
  -- ==================================================================================
  have hGoodex : ∃ p : List V,
      IsAntipathList G p ∧ p.head? = some v ∧ 2 ≤ p.length ∧
        (∀ z ∈ p, z ≠ v → z ∈ Q) ∧
        (∃ qk : V, p.getLast? = some qk ∧ ∃ x ∈ A ∪ B, ¬ G.Adj qk x) := by
    obtain ⟨a, haA, qa, hqaQ, hnaq⟩ := id hAnb
    obtain ⟨p, hp, hpmem⟩ :=
      InducedPathExtraction.exists_isAntipathFrom_of_anticonnected hQvanti
        (Or.inr rfl : v ∈ Q ∪ ({v} : Set V)) (Or.inl hqaQ : qa ∈ Q ∪ ({v} : Set V))
    have hvq : v ≠ qa := fun hc => hvQ (hc ▸ hqaQ)
    refine ⟨p, hp.1, hp.2.1, Aux.len_ge_two (G := Gᶜ) hp hvq, ?_, qa, hp.2.2, a,
      Or.inl haA, fun hcon => hnaq hcon.symm⟩
    intro z hz hzv
    rcases hpmem z hz with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hzv
  obtain ⟨pq, ⟨hpqpath, hpqhead, hpqlen2, hpqQ, qk, hqklast, xk, hxkAB, hxknadj⟩, hpqmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : List V => IsAntipathList G p ∧ p.head? = some v ∧ 2 ≤ p.length ∧
        (∀ z ∈ p, z ≠ v → z ∈ Q) ∧
        (∃ qk : V, p.getLast? = some qk ∧ ∃ x ∈ A ∪ B, ¬ G.Adj qk x))
      List.length hGoodex
  have hpqpos : 0 < pq.length := by omega
  have hq0 : pq[0]'hpqpos = v := PathBasics.getElem_zero_of_head? hpqhead hpqpos
  have hqkidx : pq[pq.length - 1]'(by omega) = qk :=
    PathBasics.getElem_last_of_getLast? hqklast hpqpos
  have hpqFrom : IsAntipathFrom G pq v qk := ⟨hpqpath, hpqhead, hqklast⟩
  have hvneqk : v ≠ qk := by
    rw [← hq0, ← hqkidx]
    exact PathBasics.path_ne_of_ne_index hpqpath hpqpos (by omega) (by omega)
  have hqkQ : qk ∈ Q :=
    hpqQ qk (PathBasics.isPathFrom_ends_mem hpqFrom).2 (fun hc => hvneqk hc.symm)
  have hqkS : qk ∉ A ∪ B ∪ C := hNnotS qk (hQN hqkQ)
  -- PAPER: *"From the minimality of `k`, `{v, q₁, …, q_{k-1}}` is complete to `A ∪ B`."*
  have hprefABidx : ∀ (j : ℕ) (hj : j < pq.length), j + 1 < pq.length →
      ∀ x ∈ A ∪ B, G.Adj (pq[j]'hj) x := by
    intro j hj hj1 x hx
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hq0]; exact hvAB x hx
    by_contra hnadj
    have hlen : (pq.take (j + 1)).length = j + 1 := by
      rw [List.length_take]; omega
    have hgood : IsAntipathList G (pq.take (j + 1)) ∧ (pq.take (j + 1)).head? = some v ∧
        2 ≤ (pq.take (j + 1)).length ∧
        (∀ z ∈ pq.take (j + 1), z ≠ v → z ∈ Q) ∧
        (∃ qk' : V, (pq.take (j + 1)).getLast? = some qk' ∧
          ∃ y ∈ A ∪ B, ¬ G.Adj qk' y) := by
      refine ⟨PathBasics.isPathList_take hpqpath (by omega), ?_, by omega, ?_,
        pq[j]'hj, ?_, x, hx, hnadj⟩
      · have h := PathBasics.head?_slice pq (i := 0) (j := j) (Nat.zero_le j) hj
        simpa [hq0] using h
      · intro z hz hzv
        exact hpqQ z ((List.take_sublist (j + 1) pq).subset hz) hzv
      · have h := PathBasics.getLast?_slice pq (i := 0) (j := j) (Nat.zero_le j) hj
        simpa using h
    have hle := hpqmin (pq.take (j + 1)) hgood
    omega
  have hprefAB : ∀ z ∈ pq, z ≠ qk → ∀ x ∈ A ∪ B, G.Adj z x := by
    intro z hz hzqk x hx
    obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hz
    subst hjz
    refine hprefABidx j hj ?_ x hx
    by_contra hcon
    refine hzqk ?_
    rw [← hqkidx]
    exact Aux.getElem_eq_index pq hj (by omega) (by omega)
  have hintQ : ∀ z ∈ SPGT.interior pq, z ∈ Q := by
    intro z hz
    rw [PathBasics.mem_interior_iff_of_pathFrom hpqFrom] at hz
    exact hpqQ z hz.1 hz.2.1
  have hintAB : ∀ z ∈ SPGT.interior pq, ∀ x ∈ A ∪ B, G.Adj z x := by
    intro z hz x hx
    rw [PathBasics.mem_interior_iff_of_pathFrom hpqFrom] at hz
    exact hprefAB z hz.1 hz.2.2 x hx
  have hw₀notpq : w₀ ∉ pq := by
    intro hmem
    by_cases hwv : w₀ = v
    · exact hvnew₀ hwv.symm
    · exact claim2a w₀ (hpqQ w₀ hmem hwv) hw₀RS
  have hu₀notpq : u₀ ∉ pq := by
    intro hmem
    by_cases hwv : u₀ = v
    · exact hvneu₀ hwv.symm
    · exact hQnoLS u₀ (hpqQ u₀ hmem hwv) hu₀LS
  have hw₀Q : ∀ q ∈ Q, G.Adj w₀ q := claim2b w₀ hw₀RS hw₀F
  have hu₀Q : ∀ q ∈ Q, G.Adj u₀ q := claim2c u₀ hu₀LS hu₀F
  have hSnotpq : ∀ y ∈ A ∪ B ∪ C, y ∉ pq := by
    intro y hy hmem
    by_cases hyv : y = v
    · exact hvS (hyv ▸ hy)
    · exact hNnotS y (hQN (hpqQ y hmem hyv)) hy
  have hxknotpq : xk ∉ pq := hSnotpq xk (Or.inl hxkAB)
  -- ==================================================================================
  -- (5) PAPER: *"`k` is odd."*   (`pathLength pq = k`, so this is `Even pq.length`.)
  -- ==================================================================================
  have hclose : ∀ st y : V, y ∈ A ∪ B → ¬ G.Adj qk y → st ∉ pq → ¬ G.Adj st v →
      st ≠ v → (∀ q ∈ Q, G.Adj st q) → ¬ G.Adj st y → st ≠ y → Even pq.length := by
    intro st y hyAB hnqk hstpq hstv hstnev hstQ hsty hstney
    have hyqk : y ≠ qk := fun hc => hqkS (Or.inl (hc ▸ hyAB))
    have hhole : IsHoleList Gᶜ (y :: st :: pq) := by
      refine PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hpqFrom
        (by rw [PathBasics.pathLength_eq]; omega)
        ((SimpleGraph.compl_adj G st v).mpr ⟨hstnev, hstv⟩)
        ((SimpleGraph.compl_adj G y qk).mpr ⟨hyqk, fun hc => hnqk hc.symm⟩)
        ((SimpleGraph.compl_adj G st y).mpr ⟨hstney, hsty⟩)
        hstpq (hSnotpq y (Or.inl hyAB)) ?_ ?_ ?_ ?_
      · exact fun hc => ((SimpleGraph.compl_adj G st qk).mp hc).2 (hstQ qk hqkQ)
      · exact fun hc => ((SimpleGraph.compl_adj G y v).mp hc).2 (hvAB y hyAB).symm
      · exact fun z hz hc => ((SimpleGraph.compl_adj G st z).mp hc).2 (hstQ z (hintQ z hz))
      · exact fun z hz hc =>
          ((SimpleGraph.compl_adj G y z).mp hc).2 (hintAB z hz y hyAB).symm
    have hev := hG.2 _ hhole
    simp only [holeLength, List.length_cons] at hev
    rw [Nat.even_iff] at hev ⊢
    omega
  have claim5 : Even pq.length := by
    rcases hxkAB with hxA | hxB
    · exact hclose w₀ xk (Or.inl hxA) hxknadj hw₀notpq hvnw₀ (fun hc => hvnew₀ hc.symm)
        hw₀Q (hw₀RS.2.2 xk (Or.inl hxA))
        (fun hc => hw₀RS.1 (Or.inl (Or.inl (hc ▸ hxA))))
    · exact hclose u₀ xk (Or.inr hxB) hxknadj hu₀notpq hvnu₀ (fun hc => hvneu₀ hc.symm)
        hu₀Q (hu₀LS.2.2 xk (Or.inl hxB))
        (fun hc => hu₀LS.1 (Or.inl (Or.inr (hc ▸ hxB))))
  -- ==================================================================================
  -- (6) PAPER: *"`A₁` is complete to `B₂`, and `A₂` is complete to `B₁`."*
  -- ==================================================================================
  have hcross3 : ∀ (st y z : V), st ∉ pq → y ∉ pq → z ∉ pq →
      (∀ q ∈ Q, G.Adj st q) → G.Adj v y → G.Adj v z → ¬ G.Adj v st → v ≠ st →
      ¬ G.Adj qk y → G.Adj qk z → (∀ w ∈ SPGT.interior pq, G.Adj w y) →
      (∀ w ∈ SPGT.interior pq, G.Adj w z) → y ≠ st → z ≠ st → y ≠ z →
      ∀ x ∈ pq, ∀ w ∈ [y, z, st], (Gᶜ.Adj x w ↔ (x = qk ∧ w = y) ∨ (x = v ∧ w = st)) := by
    intro st y z hstpq hypq hzpq hstQ hvy hvz hvst hvnst hqky hqkz hinty hintz
      hyst hzst hyz x hx w hw
    have hwcase : w = y ∨ w = z ∨ w = st := by simpa using hw
    have hxcase : x = v ∨ x = qk ∨ x ∈ SPGT.interior pq := by
      by_cases h1 : x = v
      · exact Or.inl h1
      by_cases h2 : x = qk
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hpqFrom).mpr ⟨hx, h1, h2⟩))
    have hnotG : ∀ p1 p2 : V, G.Adj p1 p2 → ¬ Gᶜ.Adj p1 p2 :=
      fun p1 p2 h hc => ((SimpleGraph.compl_adj G p1 p2).mp hc).2 h
    rcases hxcase with rfl | rfl | hxint
    · rcases hwcase with rfl | rfl | rfl
      · exact iff_of_false (hnotG _ _ hvy)
          (by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [hvneqk h, hyst h])
      · exact iff_of_false (hnotG _ _ hvz)
          (by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [hvneqk h, hzst h])
      · exact iff_of_true ((SimpleGraph.compl_adj G _ _).mpr ⟨hvnst, hvst⟩) (Or.inr ⟨rfl, rfl⟩)
    · rcases hwcase with rfl | rfl | rfl
      · exact iff_of_true ((SimpleGraph.compl_adj G _ _).mpr
          ⟨fun hc => hypq (hc ▸ (PathBasics.isPathFrom_ends_mem hpqFrom).2), hqky⟩)
          (Or.inl ⟨rfl, rfl⟩)
      · exact iff_of_false (hnotG _ _ hqkz)
          (by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [hyz h.symm, hvneqk h.symm])
      · exact iff_of_false (hnotG _ _ (hstQ _ hqkQ).symm)
          (by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [hyst h.symm, hvneqk h.symm])
    · have hxv : x ≠ v := ((PathBasics.mem_interior_iff_of_pathFrom hpqFrom).mp hxint).2.1
      have hxqk : x ≠ qk := ((PathBasics.mem_interior_iff_of_pathFrom hpqFrom).mp hxint).2.2
      rcases hwcase with rfl | rfl | rfl
      · exact iff_of_false (hnotG _ _ (hinty x hxint))
          (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hxqk h, hxv h])
      · exact iff_of_false (hnotG _ _ (hintz x hxint))
          (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hxqk h, hxv h])
      · exact iff_of_false (hnotG _ _ (hstQ x (hintQ x hxint)).symm)
          (by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [hxqk h, hxv h])
  have claim6a : ∀ a ∈ A, G.Adj qk a → ∀ b ∈ B, ¬ G.Adj qk b → G.Adj a b := by
    intro a haA hqka b hbB hqkb
    by_contra hnab
    have hbw₀ : b ≠ w₀ := fun hc => hw₀RS.1 (Or.inl (Or.inr (hc ▸ hbB)))
    have haw₀ : a ≠ w₀ := fun hc => hw₀RS.1 (Or.inl (Or.inl (hc ▸ haA)))
    have hba : b ≠ a := fun hc => Set.disjoint_left.mp hdAB haA (hc ▸ hbB)
    have hR : IsPathFrom Gᶜ [b, a, w₀] b w₀ := by
      refine ⟨Aux.isPathList_three (by simp [hba, hbw₀, haw₀]) ?_ ?_ ?_, rfl, by simp⟩
      · exact (SimpleGraph.compl_adj G b a).mpr ⟨hba, fun hc => hnab hc.symm⟩
      · exact (SimpleGraph.compl_adj G a w₀).mpr
          ⟨haw₀, fun hc => hw₀RS.2.2 a (Or.inl haA) hc.symm⟩
      · exact fun hc => ((SimpleGraph.compl_adj G b w₀).mp hc).2 (hw₀RS.2.1 b hbB).symm
    have hhole : IsHoleList Gᶜ (pq ++ [b, a, w₀]) := by
      refine PathGlue.glue_hole (G := Gᶜ) hpqFrom hR ?_ ?_ (by simp; omega)
      · intro x hx hcon
        have : x = b ∨ x = a ∨ x = w₀ := by simpa using hcon
        rcases this with rfl | rfl | rfl
        · exact hSnotpq x (Or.inl (Or.inr hbB)) hx
        · exact hSnotpq x (Or.inl (Or.inl haA)) hx
        · exact hw₀notpq hx
      · exact hcross3 w₀ b a hw₀notpq (hSnotpq b (Or.inl (Or.inr hbB)))
          (hSnotpq a (Or.inl (Or.inl haA))) hw₀Q (hvAB b (Or.inr hbB)) (hvAB a (Or.inl haA))
          (fun hc => hvnw₀ hc.symm) hvnew₀ hqkb hqka
          (fun w hw => hintAB w hw b (Or.inr hbB)) (fun w hw => hintAB w hw a (Or.inl haA))
          hbw₀ haw₀ hba
    have hev := hG.2 _ hhole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.even_iff] at claim5
    omega
  have claim6b : ∀ a ∈ A, ¬ G.Adj qk a → ∀ b ∈ B, G.Adj qk b → G.Adj a b := by
    intro a haA hqka b hbB hqkb
    by_contra hnab
    have hbu₀ : b ≠ u₀ := fun hc => hu₀LS.1 (Or.inl (Or.inr (hc ▸ hbB)))
    have hau₀ : a ≠ u₀ := fun hc => hu₀LS.1 (Or.inl (Or.inl (hc ▸ haA)))
    have hab : a ≠ b := fun hc => Set.disjoint_left.mp hdAB haA (hc ▸ hbB)
    have hR : IsPathFrom Gᶜ [a, b, u₀] a u₀ := by
      refine ⟨Aux.isPathList_three (by simp [hab, hbu₀, hau₀]) ?_ ?_ ?_, rfl, by simp⟩
      · exact (SimpleGraph.compl_adj G a b).mpr ⟨hab, hnab⟩
      · exact (SimpleGraph.compl_adj G b u₀).mpr
          ⟨hbu₀, fun hc => hu₀LS.2.2 b (Or.inl hbB) hc.symm⟩
      · exact fun hc => ((SimpleGraph.compl_adj G a u₀).mp hc).2 (hu₀LS.2.1 a haA).symm
    have hhole : IsHoleList Gᶜ (pq ++ [a, b, u₀]) := by
      refine PathGlue.glue_hole (G := Gᶜ) hpqFrom hR ?_ ?_ (by simp; omega)
      · intro x hx hcon
        have : x = a ∨ x = b ∨ x = u₀ := by simpa using hcon
        rcases this with rfl | rfl | rfl
        · exact hSnotpq x (Or.inl (Or.inl haA)) hx
        · exact hSnotpq x (Or.inl (Or.inr hbB)) hx
        · exact hu₀notpq hx
      · exact hcross3 u₀ a b hu₀notpq (hSnotpq a (Or.inl (Or.inl haA)))
          (hSnotpq b (Or.inl (Or.inr hbB))) hu₀Q (hvAB a (Or.inl haA)) (hvAB b (Or.inr hbB))
          (fun hc => hvnu₀ hc.symm) hvneu₀ hqka hqkb
          (fun w hw => hintAB w hw a (Or.inl haA)) (fun w hw => hintAB w hw b (Or.inr hbB))
          hau₀ hbu₀ hab
    have hev := hG.2 _ hhole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.even_iff] at claim5
    omega
  -- ==================================================================================
  -- (7) PAPER: *"`A₁`, `B₁`, `A₂`, `B₂` are all nonempty."*
  -- ==================================================================================
  have hBnonA : ∀ b ∈ B, ∃ a ∈ A, ¬ G.Adj b a := fun b hb =>
    Aux.exists_nonneighbour_in_B hSCswap hb
  have hA₂ne : ∃ a ∈ A, ¬ G.Adj qk a := by
    rcases hxkAB with h | h
    · exact ⟨xk, h, hxknadj⟩
    · obtain ⟨a, haA, hnab⟩ := hBnonA xk h
      exact ⟨a, haA, fun hqka => hnab (claim6a a haA hqka xk h hxknadj).symm⟩
  have hB₂ne : ∃ b ∈ B, ¬ G.Adj qk b := by
    obtain ⟨a, haA, hqka⟩ := hA₂ne
    obtain ⟨b, hbB, hnab⟩ := Aux.exists_nonneighbour_in_B hSC haA
    exact ⟨b, hbB, fun hqkb => hnab (claim6b a haA hqka b hbB hqkb)⟩
  -- PAPER: *"Since `q_k` has a neighbour in `A ∪ B ∪ C` it follows that it has a neighbour
  --     in `B`, by 11.1, and similarly it has a neighbour in `A`."*
  have hqknF : qk ∉ F := fun hc => hQout qk hqkQ (Or.inr hc)
  have hqkFnbr : ∃ f ∈ F, G.Adj qk f := (hQnbr qk hqkQ).1
  have hqkneu₀ : qk ≠ u₀ := fun hc => hQnoLS qk hqkQ (hc ▸ hu₀LS)
  have hqknew₀ : qk ≠ w₀ := fun hc => claim2a qk hqkQ (hc ▸ hw₀RS)
  obtain ⟨PQB, hPQB, hPQBint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hqknF hw₀N.1 hqkFnbr hw₀F
  obtain ⟨PQA, hPQA, hPQAint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hqknF hu₀N.1 hqkFnbr hu₀F
  have hB₁ne : ∃ b ∈ B, G.Adj qk b := by
    by_contra hcon
    have hcon' : SPGT.VertexAnticomplete G qk B := fun b hb hadj => hcon ⟨b, hb, hadj⟩
    refine hQnoLS qk hqkQ (thm_11_1 G hG hK4nd A C B hSC u₀ w₀ R₀ hban qk hqkS ?_ hcon'
      PQB hPQB (Aux.path_avoid hFout hPQB hPQBint hqkS hw₀RS.1 hqkneu₀
        (fun hc => hu₀nw₀ hc.symm) hu₀N.1) ?_)
    · obtain ⟨y, hy, hadjy⟩ := claim1 qk (hQN hqkQ)
      rcases hy with (hyA | hyB) | hyC
      · exact ⟨y, Or.inl hyA, hadjy⟩
      · exact absurd hadjy (hcon' y hyB)
      · exact ⟨y, Or.inr hyC, hadjy⟩
    · exact fun x hx y hy => hFanti x (hPQBint x hx) y hy
  have hA₁ne : ∃ a ∈ A, G.Adj qk a := by
    by_contra hcon
    have hcon' : SPGT.VertexAnticomplete G qk A := fun a ha hadj => hcon ⟨a, ha, hadj⟩
    have hqkSswap : qk ∉ B ∪ A ∪ C := by rw [Aux.union3_comm B A C]; exact hqkS
    have hu₀Sswap : u₀ ∉ B ∪ A ∪ C := by rw [Aux.union3_comm B A C]; exact hu₀LS.1
    have hw₀Sswap : w₀ ∉ B ∪ A ∪ C := by rw [Aux.union3_comm B A C]; exact hw₀RS.1
    refine claim2a qk hqkQ (Aux.isRightStar_swap.mpr
      (thm_11_1 G hG hK4nd B C A hSCswap w₀ u₀ R₀' hban' qk hqkSswap ?_ hcon'
        PQA hPQA (Aux.path_avoid hFoutswap hPQA hPQAint hqkSswap hu₀Sswap hqknew₀ hu₀nw₀
          hw₀N.1) ?_))
    · obtain ⟨y, hy, hadjy⟩ := claim1 qk (hQN hqkQ)
      rcases hy with (hyA | hyB) | hyC
      · exact absurd hadjy (hcon' y hyA)
      · exact ⟨y, Or.inl hyB, hadjy⟩
      · exact ⟨y, Or.inr hyC, hadjy⟩
    · intro x hx y hy
      rw [Aux.union3_comm B A C] at hy
      exact hFanti x (hPQAint x hx) y hy
  -- ==================================================================================
  -- PAPER: *"Now the strip is step-connected, and so there is a step `a₁-R-b₂`,
  --     `a₂-R'-b₁` with `a₁ ∈ A₁` and `a₂ ∈ A₂`."*
  -- ==================================================================================
  have hAsplit : {x : V | x ∈ A ∧ G.Adj qk x} ∪ {x : V | x ∈ A ∧ ¬ G.Adj qk x} = A := by
    ext y
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hy
      by_cases hadj : G.Adj qk y
      · exact Or.inl ⟨hy, hadj⟩
      · exact Or.inr ⟨hy, hadj⟩
  have hAdisj : Disjoint {x : V | x ∈ A ∧ G.Adj qk x} {x : V | x ∈ A ∧ ¬ G.Adj qk x} := by
    rw [Set.disjoint_left]
    rintro y ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  obtain ⟨a₁, RR₁, bb₁, a₂, RR₂, bb₂, hstep, hend₁, hend₂⟩ :=
    hpart {x : V | x ∈ A ∧ G.Adj qk x} {x : V | x ∈ A ∧ ¬ G.Adj qk x} (Or.inl hAsplit) hAdisj
      (by obtain ⟨a, ha, hadj⟩ := hA₁ne; exact ⟨a, ha, hadj⟩)
      (by obtain ⟨a, ha, hadj⟩ := hA₂ne; exact ⟨a, ha, hadj⟩)
  obtain ⟨hr₁, hr₂, hdisj12, hcross12⟩ := hstep
  have ha₁X : a₁ ∈ A ∧ G.Adj qk a₁ := by
    rcases hend₁ with h | h
    · exact h
    · exact absurd h.1 (Set.disjoint_right.mp hdAB hr₁.2.2.1)
  have ha₂Y : a₂ ∈ A ∧ ¬ G.Adj qk a₂ := by
    rcases hend₂ with h | h
    · exact h
    · exact absurd h.1 (Set.disjoint_right.mp hdAB hr₂.2.2.1)
  have ha₁mem : a₁ ∈ RR₁ := (PathBasics.isPathFrom_ends_mem hr₁.1).1
  have hb₁mem : bb₁ ∈ RR₁ := (PathBasics.isPathFrom_ends_mem hr₁.1).2
  have ha₂mem : a₂ ∈ RR₂ := (PathBasics.isPathFrom_ends_mem hr₂.1).1
  have hb₂mem : bb₂ ∈ RR₂ := (PathBasics.isPathFrom_ends_mem hr₂.1).2
  have hABne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := fun x hx y hy hxy =>
    Set.disjoint_left.mp hdAB hx (hxy ▸ hy)
  have hna₁b₂ : ¬ G.Adj a₁ bb₂ := by
    intro hadj
    rcases (hcross12 a₁ ha₁mem bb₂ hb₂mem).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
    · exact hABne a₂ hr₂.2.1 bb₂ hr₂.2.2.1 h.symm
    · exact hABne a₁ ha₁X.1 bb₁ hr₁.2.2.1 h
  have hna₂b₁ : ¬ G.Adj bb₁ a₂ := by
    intro hadj
    rcases (hcross12 bb₁ hb₁mem a₂ ha₂mem).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
    · exact hABne a₁ ha₁X.1 bb₁ hr₁.2.2.1 h.symm
    · exact hABne a₂ ha₂Y.1 bb₂ hr₂.2.2.1 h
  -- PAPER: *"Since `a₁` is not adjacent to `b₁` it follows that `b₁ ∈ B₁` by (6), and
  --     similarly `b₂ ∈ B₂`."*
  have hb₂B₁ : G.Adj qk bb₂ := by
    by_contra hcon
    exact hna₁b₂ (claim6a a₁ ha₁X.1 ha₁X.2 bb₂ hr₂.2.2.1 hcon)
  have hb₁B₂ : ¬ G.Adj qk bb₁ := by
    intro hcon
    exact hna₂b₁ (claim6b a₂ ha₂Y.1 ha₂Y.2 bb₁ hr₁.2.2.1 hcon).symm
  -- PAPER: *"Also by (6), `R` and `R'` both have length 1."*
  have ha₁b₁ : G.Adj a₁ bb₁ := claim6a a₁ ha₁X.1 ha₁X.2 bb₁ hr₁.2.2.1 hb₁B₂
  have ha₂b₂ : G.Adj a₂ bb₂ := claim6b a₂ ha₂Y.1 ha₂Y.2 bb₂ hr₂.2.2.1 hb₂B₁
  -- ==================================================================================
  -- PAPER: *"Since `v-a₁-a₀-b₀-b₁-v` is not an odd hole, it follows that `a₀` is not
  --     adjacent to `b₀`."*  (the printed `b₂` is a typo for `b₁`: `a₁b₂` is an edge of
  --     the rung `a₁-R-b₂`, so `v-a₁-a₀-b₀-b₂-v` has the chord `a₁b₂`.)
  -- ==================================================================================
  have ha₁S : a₁ ∈ A ∪ B ∪ C := Or.inl (Or.inl ha₁X.1)
  have hb₂S : bb₂ ∈ A ∪ B ∪ C := Or.inl (Or.inr hr₂.2.2.1)
  have hu₀w₀nadj : ¬ G.Adj u₀ w₀ := by
    intro hadj
    have hne1 : a₁ ≠ u₀ := fun hc => hu₀LS.1 (hc ▸ ha₁S)
    have hne2 : a₁ ≠ w₀ := fun hc => hw₀RS.1 (hc ▸ ha₁S)
    have hne3 : a₁ ≠ bb₂ := hABne a₁ ha₁X.1 bb₂ hr₂.2.2.1
    have hne4 : bb₂ ≠ u₀ := fun hc => hu₀LS.1 (hc ▸ hb₂S)
    have hne5 : bb₂ ≠ w₀ := fun hc => hw₀RS.1 (hc ▸ hb₂S)
    have hpath : IsPathList G [a₁, u₀, w₀, bb₂] := by
      refine PathGlue.isPathList_four
        (by simp [hne1, hne2, hne3, hu₀nw₀, hne4, hne5, Ne.symm hne4, Ne.symm hne5])
        (hu₀LS.2.1 a₁ ha₁X.1).symm hadj (hw₀RS.2.1 bb₂ hr₂.2.2.1)
        (fun hc => hw₀RS.2.2 a₁ (Or.inl ha₁X.1) hc.symm) hna₁b₂
        (hu₀LS.2.2 bb₂ (Or.inl hr₂.2.2.1))
    have hpf : IsPathFrom G [a₁, u₀, w₀, bb₂] a₁ bb₂ := ⟨hpath, rfl, by simp⟩
    have hvnotmem : v ∉ [a₁, u₀, w₀, bb₂] := by
      intro hmem
      have : v = a₁ ∨ v = u₀ ∨ v = w₀ ∨ v = bb₂ := by simpa using hmem
      rcases this with h | h | h | h
      · exact hvS (h ▸ ha₁S)
      · exact hvneu₀ h
      · exact hvnew₀ h
      · exact hvS (h ▸ hb₂S)
    have hhole : IsHoleList G (v :: [a₁, u₀, w₀, bb₂]) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hpf (by rw [PathBasics.pathLength_eq]; simp)
        (hvAB a₁ (Or.inl ha₁X.1)) (hvAB bb₂ (Or.inr hr₂.2.2.1)) hvnotmem ?_
      intro x hx
      have : x = u₀ ∨ x = w₀ := by simpa [SPGT.interior] using hx
      rcases this with h | h
      · exact fun hc => hvnu₀ (h ▸ hc).symm
      · exact fun hc => hvnw₀ (h ▸ hc).symm
    have hev := hG.1 _ hhole
    simp only [holeLength, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    omega
  -- ==================================================================================
  -- PAPER: *"For every vertex `u ∈ V(G) \ F`, let `F_u` be the set of vertices in `F`
  --     adjacent to `u`."*
  -- (8) PAPER: *"`F_{a₀} ∩ F_{b₀} = ∅`, and every path in `F` between `F_{a₀}` and
  --     `F_{b₀}` meets both `F_v` and `F_{q_k}`."*
  -- ==================================================================================
  have hb₁S : bb₁ ∈ A ∪ B ∪ C := Or.inl (Or.inr hr₁.2.2.1)
  have ha₂S : a₂ ∈ A ∪ B ∪ C := Or.inl (Or.inl ha₂Y.1)
  have hb₂nea₂ : bb₂ ≠ a₂ := (hABne a₂ ha₂Y.1 bb₂ hr₂.2.2.1).symm
  have claim8a : ∀ f ∈ F, G.Adj u₀ f → ¬ G.Adj w₀ f := by
    intro f hfF hu₀f hw₀f
    have hne1 : u₀ ≠ a₁ := fun hc => hu₀LS.1 (hc ▸ ha₁S)
    have hne2 : u₀ ≠ bb₁ := fun hc => hu₀LS.1 (hc ▸ hb₁S)
    have hne3 : a₁ ≠ bb₁ := hABne a₁ ha₁X.1 bb₁ hr₁.2.2.1
    have hne4 : a₁ ≠ w₀ := fun hc => hw₀RS.1 (hc ▸ ha₁S)
    have hne5 : bb₁ ≠ w₀ := fun hc => hw₀RS.1 (hc ▸ hb₁S)
    have hpath : IsPathList G [u₀, a₁, bb₁, w₀] :=
      PathGlue.isPathList_four
        (by simp [hne1, hne2, hu₀nw₀, hne3, hne4, hne5])
        (hu₀LS.2.1 a₁ ha₁X.1) ha₁b₁ (hw₀RS.2.1 bb₁ hr₁.2.2.1).symm
        (hu₀LS.2.2 bb₁ (Or.inl hr₁.2.2.1)) hu₀w₀nadj
        (fun hc => hw₀RS.2.2 a₁ (Or.inl ha₁X.1) hc.symm)
    have hpf : IsPathFrom G [u₀, a₁, bb₁, w₀] u₀ w₀ := ⟨hpath, rfl, by simp⟩
    have hfnotmem : f ∉ [u₀, a₁, bb₁, w₀] := by
      intro hmem
      have hc : f = u₀ ∨ f = a₁ ∨ f = bb₁ ∨ f = w₀ := by simpa using hmem
      rcases hc with h | h | h | h
      · exact hu₀N.1 (h ▸ hfF)
      · exact hFout f hfF (h ▸ ha₁S)
      · exact hFout f hfF (h ▸ hb₁S)
      · exact hw₀N.1 (h ▸ hfF)
    have hhole : IsHoleList G (f :: [u₀, a₁, bb₁, w₀]) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hpf
        (by rw [PathBasics.pathLength_eq]; simp) hu₀f.symm hw₀f.symm hfnotmem ?_
      intro x hx
      have hc : x = a₁ ∨ x = bb₁ := by simpa [SPGT.interior] using hx
      rcases hc with h | h
      · exact fun hadj => hFanti f hfF a₁ ha₁S (h ▸ hadj)
      · exact fun hadj => hFanti f hfF bb₁ hb₁S (h ▸ hadj)
    have hev := hG.1 _ hhole
    simp only [holeLength, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    omega
  obtain ⟨PP, hPP, hPPint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hu₀N.1 hw₀N.1 hu₀F hw₀F
  have hPP3 : 3 ≤ PP.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hPP hu₀nw₀ hu₀w₀nadj
  obtain ⟨f1, fn, hPintFrom⟩ : ∃ a b : V, IsPathFrom G (SPGT.interior PP) a b :=
    ⟨_, _, PathGlue.isPathFrom_interior hPP.1 hPP3⟩
  obtain ⟨hu₀f1, hw₀fn, hu₀uniq, hw₀uniq⟩ := Aux.interior_ends hPP hPP3 hPintFrom
  have hPPmem : ∀ x ∈ PP, x = u₀ ∨ x = w₀ ∨ x ∈ SPGT.interior PP := by
    intro x hx
    by_cases h1 : x = u₀
    · exact Or.inl h1
    by_cases h2 : x = w₀
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hPP).mpr ⟨hx, h1, h2⟩))
  have hPPoutS : ∀ x ∈ PP, x ∉ A ∪ B ∪ C := by
    intro x hx
    rcases hPPmem x hx with h | h | h
    · rw [h]; exact hu₀LS.1
    · rw [h]; exact hw₀RS.1
    · exact hFout x (hPPint x h)
  have hintne : ∀ x ∈ SPGT.interior PP, x ≠ u₀ ∧ x ≠ w₀ := by
    intro x hx
    exact ⟨((PathBasics.mem_interior_iff_of_pathFrom hPP).mp hx).2.1,
      ((PathBasics.mem_interior_iff_of_pathFrom hPP).mp hx).2.2⟩
  have hcross1 : ∀ x ∈ PP, ∀ t ∈ [bb₂, a₂],
      (G.Adj x t ↔ (x = w₀ ∧ t = bb₂) ∨ (x = u₀ ∧ t = a₂)) := by
    intro x hx t ht
    have htc : t = bb₂ ∨ t = a₂ := by simpa using ht
    rcases hPPmem x hx with hxc | hxc | hxint
    · rw [hxc]
      rcases htc with h | h <;> rw [h]
      · exact iff_of_false (hu₀LS.2.2 bb₂ (Or.inl hr₂.2.2.1))
          (by rintro (⟨hc, -⟩ | ⟨-, hc⟩); exacts [hu₀nw₀ hc, hb₂nea₂ hc])
      · exact iff_of_true (hu₀LS.2.1 a₂ ha₂Y.1) (Or.inr ⟨rfl, rfl⟩)
    · rw [hxc]
      rcases htc with h | h <;> rw [h]
      · exact iff_of_true (hw₀RS.2.1 bb₂ hr₂.2.2.1) (Or.inl ⟨rfl, rfl⟩)
      · exact iff_of_false (hw₀RS.2.2 a₂ (Or.inl ha₂Y.1))
          (by rintro (⟨-, hc⟩ | ⟨hc, -⟩); exacts [hb₂nea₂ hc.symm, hu₀nw₀ hc.symm])
    · have hxF : x ∈ F := hPPint x hxint
      have hxn := hintne x hxint
      rcases htc with h | h <;> rw [h]
      · exact iff_of_false (hFanti x hxF bb₂ hb₂S)
          (by rintro (⟨hc, -⟩ | ⟨hc, -⟩); exacts [hxn.2 hc, hxn.1 hc])
      · exact iff_of_false (hFanti x hxF a₂ ha₂S)
          (by rintro (⟨hc, -⟩ | ⟨hc, -⟩); exacts [hxn.2 hc, hxn.1 hc])
  have hPPeven : Even PP.length := by
    have hRpath1 : IsPathFrom G [bb₂, a₂] bb₂ a₂ :=
      ⟨PathBasics.isPathList_pair ha₂b₂.symm, rfl, by simp⟩
    have hhole1 : IsHoleList G (PP ++ [bb₂, a₂]) := by
      refine PathGlue.glue_hole hPP hRpath1 ?_ hcross1
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro x hx hmem
      have hc : x = bb₂ ∨ x = a₂ := by simpa using hmem
      rcases hc with h | h
      · exact hPPoutS x hx (h ▸ hb₂S)
      · exact hPPoutS x hx (h ▸ ha₂S)
    have hev := hG.1 _ hhole1
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev ⊢
    omega
  have claim8v : ∃ z ∈ SPGT.interior PP, G.Adj v z := by
    by_contra hcon
    have hcon' : ∀ z ∈ SPGT.interior PP, ¬ G.Adj v z := fun z hz hadj => hcon ⟨z, hz, hadj⟩
    have hb₂nev : bb₂ ≠ v := fun hc => hvS (hc ▸ hb₂S)
    have hvnea₁ : v ≠ a₁ := fun hc => hvS (hc ▸ ha₁S)
    have hb₂nea₁ : bb₂ ≠ a₁ := (hABne a₁ ha₁X.1 bb₂ hr₂.2.2.1).symm
    have hR : IsPathFrom G [bb₂, v, a₁] bb₂ a₁ := by
      refine ⟨Aux.isPathList_three (by simp [hb₂nev, hvnea₁, hb₂nea₁]) ?_ ?_ ?_, rfl, by simp⟩
      · exact (hvAB bb₂ (Or.inr hr₂.2.2.1)).symm
      · exact hvAB a₁ (Or.inl ha₁X.1)
      · exact fun hc => hna₁b₂ hc.symm
    have hcross2 : ∀ x ∈ PP, ∀ t ∈ [bb₂, v, a₁],
        (G.Adj x t ↔ (x = w₀ ∧ t = bb₂) ∨ (x = u₀ ∧ t = a₁)) := by
      intro x hx t ht
      have htc : t = bb₂ ∨ t = v ∨ t = a₁ := by simpa using ht
      rcases hPPmem x hx with hxc | hxc | hxint
      · rw [hxc]
        rcases htc with h | h | h <;> rw [h]
        · exact iff_of_false (hu₀LS.2.2 bb₂ (Or.inl hr₂.2.2.1))
            (by rintro (⟨hc, -⟩ | ⟨-, hc⟩); exacts [hu₀nw₀ hc, hb₂nea₁ hc])
        · exact iff_of_false hvnu₀
            (by rintro (⟨hc, -⟩ | ⟨-, hc⟩); exacts [hu₀nw₀ hc, hvnea₁ hc])
        · exact iff_of_true (hu₀LS.2.1 a₁ ha₁X.1) (Or.inr ⟨rfl, rfl⟩)
      · rw [hxc]
        rcases htc with h | h | h <;> rw [h]
        · exact iff_of_true (hw₀RS.2.1 bb₂ hr₂.2.2.1) (Or.inl ⟨rfl, rfl⟩)
        · exact iff_of_false hvnw₀
            (by rintro (⟨-, hc⟩ | ⟨hc, -⟩); exacts [hb₂nev hc.symm, hu₀nw₀ hc.symm])
        · exact iff_of_false (fun hc => hw₀RS.2.2 a₁ (Or.inl ha₁X.1) hc)
            (by rintro (⟨-, hc⟩ | ⟨hc, -⟩); exacts [hb₂nea₁ hc.symm, hu₀nw₀ hc.symm])
      · have hxF : x ∈ F := hPPint x hxint
        have hxn := hintne x hxint
        rcases htc with h | h | h <;> rw [h]
        · exact iff_of_false (hFanti x hxF bb₂ hb₂S)
            (by rintro (⟨hc, -⟩ | ⟨hc, -⟩); exacts [hxn.2 hc, hxn.1 hc])
        · exact iff_of_false (fun hadj => hcon' x hxint hadj.symm)
            (by rintro (⟨hc, -⟩ | ⟨hc, -⟩); exacts [hxn.2 hc, hxn.1 hc])
        · exact iff_of_false (hFanti x hxF a₁ ha₁S)
            (by rintro (⟨hc, -⟩ | ⟨hc, -⟩); exacts [hxn.2 hc, hxn.1 hc])
    have hhole : IsHoleList G (PP ++ [bb₂, v, a₁]) := by
      refine PathGlue.glue_hole hPP hR ?_ hcross2
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro x hx hmem
      have hc : x = bb₂ ∨ x = v ∨ x = a₁ := by simpa using hmem
      rcases hc with h | h | h
      · exact hPPoutS x hx (h ▸ hb₂S)
      · exact hvF (h ▸ (hPPint x (by
          rcases hPPmem x hx with h1 | h1 | h1
          · exact absurd (h1 ▸ h : u₀ = v) (Ne.symm hvneu₀)
          · exact absurd (h1 ▸ h : w₀ = v) (Ne.symm hvnew₀)
          · exact h1)))
      · exact hPPoutS x hx (h ▸ ha₁S)
    have hev := hG.1 _ hhole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.even_iff] at hPPeven
    omega
  have hqknotPP : qk ∉ PP := by
    intro hmem
    rcases hPPmem qk hmem with h | h | h
    · exact hqkneu₀ h
    · exact hqknew₀ h
    · exact hqknF (hPPint qk h)
  have claim8q : ∃ z ∈ SPGT.interior PP, G.Adj qk z := by
    by_contra hcon
    have hcon' : ∀ z ∈ SPGT.interior PP, ¬ G.Adj qk z := fun z hz hadj => hcon ⟨z, hz, hadj⟩
    have hhole : IsHoleList G (qk :: PP) :=
      PrismBasics.isHoleList_of_path_add_vertex hPP
        (by rw [PathBasics.pathLength_eq]; omega) (hu₀Q qk hqkQ).symm (hw₀Q qk hqkQ).symm
        hqknotPP hcon'
    have hev := hG.1 _ hhole
    simp only [holeLength, List.length_cons] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.even_iff] at hPPeven
    omega
  -- ==================================================================================
  -- (9) PAPER: *"Every path in `F` between `F_v` and `F_{q_k}` meets both `F_{a₀}` and
  --     `F_{b₀}`."*
  --
  -- `step9` is the printed contradiction: a connected `Fp ⊆ F` meeting `F_v` and exactly
  -- one of `F_{a₀}`, `F_{b₀}` is impossible, by 2.2 in the complement.  The printed proof
  -- puts `q_{k+1} = a₂`; that choice makes the *even* antipath `b₀-v-q₁-⋯-q_{k+1}`
  -- non-induced when `i = k+1` (`b₀` is anticomplete to `A ∋ a₂`, so `b₀a₂` is an edge of
  -- the complement, i.e. a chord).  We therefore take `q_{k+1} = b₂ ∈ B₂` in the branch
  -- whose far star is `b₀` and `q_{k+1} = a₂ ∈ A₂` in the branch whose far star is `a₀`;
  -- everything else is exactly the printed argument.
  -- ==================================================================================
  have hb₂pq : ∀ x ∈ pq, G.Adj bb₂ x := by
    intro x hx
    by_cases hxqk : x = qk
    · rw [hxqk]; exact hb₂B₁.symm
    · exact (hprefAB x hx hxqk bb₂ (Or.inr hr₂.2.2.1)).symm
  have ha₁pq : ∀ x ∈ pq, G.Adj a₁ x := by
    intro x hx
    by_cases hxqk : x = qk
    · rw [hxqk]; exact ha₁X.2.symm
    · exact (hprefAB x hx hxqk a₁ (Or.inl ha₁X.1)).symm
  have step9 : ∀ (Fp : Set V) (sfar snear ee hook comp : V),
      Fp ⊆ F → ConnectedSet G Fp →
      (∃ f ∈ Fp, G.Adj v f) → (∃ f ∈ Fp, G.Adj snear f) → (¬ ∃ f ∈ Fp, G.Adj sfar f) →
      ee ∈ A ∪ B → hook ∈ A ∪ B ∪ C → comp ∈ A ∪ B ∪ C →
      sfar ∉ A ∪ B ∪ C → snear ∉ A ∪ B ∪ C →
      sfar ∉ pq → snear ∉ pq → sfar ∉ F → snear ∉ F →
      ¬ G.Adj sfar v → sfar ≠ v → (∀ q ∈ Q, G.Adj sfar q) → G.Adj sfar ee →
      ¬ G.Adj qk ee →
      ¬ G.Adj snear v → snear ≠ v → (∀ q ∈ Q, G.Adj snear q) →
      ¬ G.Adj hook snear → hook ≠ snear → (∀ x ∈ pq, G.Adj hook x) →
      (∀ x ∈ pq, G.Adj comp x) → G.Adj comp snear →
      False := by
    intro Fp sfar snear ee hook comp hFpF hFpconn hvFp hsnearFp hsfarFp heAB hhookS hcompS
      hsfarS hsnearS hsfarnotpq hsnearnotpq hsfarnF hsnearnF hsfarv hsfarnev hsfarQ hsfaree
      hqkee hsnearv hsnearnev hsnearQ hhooksnear hhooknesnear hhookpq hcomppq hcompsnear
    have heS : ee ∈ A ∪ B ∪ C := Or.inl heAB
    have henotpq : ee ∉ pq := hSnotpq ee heS
    have heqk : ee ≠ qk := fun hc => hqkS (hc ▸ heS)
    have hVSnoFp : ∀ y ∈ A ∪ B ∪ C, ¬ ∃ f ∈ Fp, G.Adj y f := by
      rintro y hy ⟨f, hf, hadj⟩
      exact hFanti f (hFpF hf) y hy hadj.symm
    have hFpnotmemS : ∀ y ∈ A ∪ B ∪ C, y ∉ Fp := fun y hy hc => hFout y (hFpF hc) hy
    have hextFrom : IsAntipathFrom G (pq ++ [ee]) v ee := by
      refine PathAttach.isPathFrom_concat (G := Gᶜ) hpqFrom
        ((SimpleGraph.compl_adj G ee qk).mpr ⟨heqk, fun hc => hqkee hc.symm⟩) henotpq ?_
      intro x hx hxqk hc
      exact ((SimpleGraph.compl_adj G ee x).mp hc).2 (hprefAB x hx hxqk ee heAB).symm
    have hextlen : (pq ++ [ee]).length = pq.length + 1 := by simp
    have hextmem : ∀ x ∈ pq ++ [ee], x = v ∨ x = ee ∨ (x ∈ Q ∧ x ∈ pq) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · by_cases hxv : x = v
        · exact Or.inl hxv
        · exact Or.inr (Or.inr ⟨hpqQ x h hxv, h⟩)
      · exact Or.inr (Or.inl (by simpa using h))
    have hextnotF : ∀ x ∈ pq ++ [ee], x ∉ F := by
      intro x hx
      rcases hextmem x hx with h | h | h
      · rw [h]; exact hvF
      · rw [h]; exact fun hc => hFout ee hc heS
      · exact fun hc => hQout x h.1 (Or.inr hc)
    have hext0 : (pq ++ [ee])[0]'(by omega) = v :=
      PathBasics.getElem_zero_of_head? hextFrom.2.1 (by omega)
    have hextlast : (pq ++ [ee])[(pq ++ [ee]).length - 1]'(by omega) = ee :=
      PathBasics.getElem_last_of_getLast? hextFrom.2.2 (by omega)
    have hwitness : ∃ hj : (pq ++ [ee]).length - 1 < (pq ++ [ee]).length,
        1 ≤ (pq ++ [ee]).length - 1 ∧
        ¬ ∃ f ∈ Fp, G.Adj ((pq ++ [ee])[(pq ++ [ee]).length - 1]'hj) f := by
      refine ⟨by omega, by omega, ?_⟩
      rw [hextlast]
      exact hVSnoFp ee heS
    obtain ⟨i, ⟨hi, hi1, hinbr⟩, himin⟩ :=
      ExtremalChoice.exists_min_nat
        (fun j : ℕ => ∃ hj : j < (pq ++ [ee]).length, 1 ≤ j ∧
          ¬ ∃ f ∈ Fp, G.Adj ((pq ++ [ee])[j]'hj) f)
        id ⟨(pq ++ [ee]).length - 1, hwitness⟩
    have hiub : i ≤ pq.length := by omega
    have himin' : ∀ (j : ℕ), 1 ≤ j → j < i → ∀ (hj : j < (pq ++ [ee]).length),
        ∃ f ∈ Fp, G.Adj ((pq ++ [ee])[j]'hj) f := by
      intro j hj1 hji hj
      by_contra hcon
      have := himin j ⟨hj, hj1, hcon⟩
      simp only [id] at this
      omega
    obtain ⟨pre, hprelen, hpreFrom, hpremem⟩ :
        ∃ pre : List V, pre.length = i + 1 ∧
          IsPathFrom Gᶜ pre v ((pq ++ [ee])[i]'hi) ∧
          (∀ x : V, x ∈ pre ↔ ∃ (k : ℕ) (hk : k < (pq ++ [ee]).length), k ≤ i ∧
            ((pq ++ [ee])[k]'hk) = x) := by
      refine ⟨((pq ++ [ee]).drop 0).take (i - 0 + 1), ?_, ?_, ?_⟩
      · rw [PathBasics.length_slice (pq ++ [ee]) (Nat.zero_le i) hi]; omega
      · have h := PathBasics.isPathFrom_slice (G := Gᶜ) hextFrom.1 (i := 0) (j := i)
          (by omega) hi
        rwa [hext0] at h
      · intro x
        rw [PathBasics.mem_slice_iff (pq ++ [ee]) (Nat.zero_le i) hi]
        constructor
        · rintro ⟨k, hk, -, h2, h3⟩
          exact ⟨k, hk, h2, h3⟩
        · rintro ⟨k, hk, h2, h3⟩
          exact ⟨k, hk, Nat.zero_le k, h2, h3⟩
    have hpresub : ∀ x ∈ pre, x ∈ pq ++ [ee] := by
      intro x hx
      obtain ⟨k, hk, -, hkx⟩ := (hpremem x).mp hx
      rw [← hkx]
      exact List.getElem_mem hk
    have hextidx : ∀ (k : ℕ) (hk : k < (pq ++ [ee]).length), k < pq.length →
        ((pq ++ [ee])[k]'hk) ∈ pq := by
      intro k hk hkpq
      rw [List.getElem_append_left hkpq]
      exact List.getElem_mem hkpq
    have hextiMem : ((pq ++ [ee])[i]'hi) ∈ pq ++ [ee] := List.getElem_mem hi
    have hkeyidx : ∀ x ∈ pre, x ≠ ((pq ++ [ee])[i]'hi) →
        (∃ f ∈ Fp, G.Adj x f) ∧ x ∈ pq := by
      intro x hx hxne
      obtain ⟨k, hk, hki, hkx⟩ := (hpremem x).mp hx
      have hkne : k ≠ i := by
        intro hc
        exact hxne (by rw [← hkx]; exact Aux.getElem_eq_index (pq ++ [ee]) hk hi hc)
      have hklt : k < i := by omega
      have hkpq : k < pq.length := by omega
      refine ⟨?_, by rw [← hkx]; exact hextidx k hk hkpq⟩
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · have hv' : ((pq ++ [ee])[k]'hk) = v := by
          rw [← hext0]
          exact Aux.getElem_eq_index (pq ++ [ee]) hk (by omega) hk0
        rw [← hkx, hv']
        exact hvFp
      · rw [← hkx]
        exact himin' k hk0 hklt hk
    have hFpanti : SPGT.AnticonnectedSet Gᶜ Fp := by
      show SPGT.ConnectedSet (Gᶜ)ᶜ Fp
      rw [compl_compl]
      exact hFpconn
    have hcompC : SPGT.VertexComplete Gᶜ comp Fp := by
      intro x hx
      refine (SimpleGraph.compl_adj G comp x).mpr ⟨?_, ?_⟩
      · intro hceq
        exact hFout x (hFpF hx) (hceq ▸ hcompS)
      · intro hcadj
        exact hFanti x (hFpF hx) comp hcompS hcadj.symm
    have hpn : SPGT.VertexComplete Gᶜ ((pq ++ [ee])[i]'hi) Fp := by
      intro x hx
      refine (SimpleGraph.compl_adj G _ x).mpr ⟨?_, ?_⟩
      · rintro rfl
        exact hextnotF _ hextiMem (hFpF hx)
      · intro hcadj
        exact hinbr ⟨x, hx, hcadj⟩
    rcases Nat.even_or_odd i with hipar | hipar
    · -- PAPER: *"If `i` is even, then `b₀-v-q₁-⋯-q_i` is an odd antipath …"*
      have hsfarnotpre : sfar ∉ pre := by
        intro hc
        rcases hextmem sfar (hpresub sfar hc) with h | h | h
        · exact hsfarnev h
        · exact hsfarS (h ▸ heS)
        · exact hsfarnotpq h.2
      have hcons : IsPathFrom Gᶜ (sfar :: pre) sfar ((pq ++ [ee])[i]'hi) := by
        refine PathAttach.isPathFrom_cons (G := Gᶜ) hpreFrom
          ((SimpleGraph.compl_adj G sfar v).mpr ⟨hsfarnev, hsfarv⟩) hsfarnotpre ?_
        intro x hx hxv hc
        have hGadj : G.Adj sfar x := by
          rcases hextmem x (hpresub x hx) with h | h | h
          · exact absurd h hxv
          · rw [h]; exact hsfaree
          · exact hsfarQ x h.1
        exact ((SimpleGraph.compl_adj G sfar x).mp hc).2 hGadj
      have hconslen : (sfar :: pre).length = i + 2 := by rw [List.length_cons, hprelen]
      have hodd : Odd (pathLength (sfar :: pre)) := by
        rw [PathBasics.pathLength_cons, hprelen, Nat.odd_iff]
        rw [Nat.even_iff] at hipar
        omega
      have hpX : ∀ w ∈ (sfar :: pre), w ∉ Fp := by
        intro w hw
        rcases List.mem_cons.mp hw with h | h
        · rw [h]; exact fun hc => hsfarnF (hFpF hc)
        · exact fun hc => hextnotF w (hpresub w h) (hFpF hc)
      have hp₁ : SPGT.VertexComplete Gᶜ sfar Fp := by
        intro x hx
        refine (SimpleGraph.compl_adj G sfar x).mpr ⟨?_, ?_⟩
        · rintro rfl
          exact hsfarnF (hFpF hx)
        · intro hcadj
          exact hsfarFp ⟨x, hx, hcadj⟩
      have hnoedge : ¬ ∃ u ∈ (sfar :: pre), ∃ w ∈ (sfar :: pre),
          SPGT.EdgeComplete Gᶜ Fp u w := by
        rintro ⟨u, hu, w, hw, hadj, hcu, hcw⟩
        have hkey : ∀ z ∈ (sfar :: pre), SPGT.VertexComplete Gᶜ z Fp →
            z = sfar ∨ z = ((pq ++ [ee])[i]'hi) := by
          intro z hz hzc
          rcases List.mem_cons.mp hz with h | h
          · exact Or.inl h
          · by_cases hze : z = ((pq ++ [ee])[i]'hi)
            · exact Or.inr hze
            · exfalso
              obtain ⟨f, hf, hfadj⟩ := (hkeyidx z h hze).1
              exact absurd hfadj ((SimpleGraph.compl_adj G z f).mp (hzc f hf)).2
        have hendsnadj : ¬ Gᶜ.Adj sfar ((pq ++ [ee])[i]'hi) := by
          have h0 : (sfar :: pre)[0]'(by omega) = sfar :=
            PathBasics.getElem_zero_of_head? hcons.2.1 (by omega)
          have hl : (sfar :: pre)[(sfar :: pre).length - 1]'(by omega)
              = ((pq ++ [ee])[i]'hi) :=
            PathBasics.getElem_last_of_getLast? hcons.2.2 (by omega)
          rw [← h0, ← hl]
          exact PathBasics.path_not_adj_of_gap hcons.1 (by omega) (by omega)
            (by omega) (by omega)
        rcases hkey u hu hcu with h1 | h1 <;> rcases hkey w hw hcw with h2 | h2 <;>
          rw [h1, h2] at hadj
        · exact Gᶜ.irrefl hadj
        · exact hendsnadj hadj
        · exact hendsnadj hadj.symm
        · exact Gᶜ.irrefl hadj
      obtain ⟨z, hzint, hzadj⟩ :=
        _root_.Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ (HoleBasics.berge_compl.mpr hG) Fp
          hFpanti (sfar :: pre) sfar ((pq ++ [ee])[i]'hi) hcons hpX hodd hp₁ hpn hnoedge
          comp hcompC
      rw [PathBasics.mem_interior_iff_of_pathFrom hcons] at hzint
      obtain ⟨hzm, hzh, hze⟩ := hzint
      have hzpre : z ∈ pre := by
        rcases List.mem_cons.mp hzm with h | h
        · exact absurd h hzh
        · exact h
      exact ((SimpleGraph.compl_adj G comp z).mp hzadj).2
        (hcomppq z (hkeyidx z hzpre hze).2)
    · -- PAPER: *"If `i` is odd, then `b₁-a₀-v-q₁-⋯-q_i` is an odd antipath …"*
      have hilt : i < pq.length := by
        rw [Nat.odd_iff] at hipar
        rw [Nat.even_iff] at claim5
        omega
      have hpresubpq : ∀ x ∈ pre, x ∈ pq := by
        intro x hx
        obtain ⟨k, hk, hki, hkx⟩ := (hpremem x).mp hx
        rw [← hkx]
        exact hextidx k hk (by omega)
      have hcons1 : IsPathFrom Gᶜ (snear :: pre) snear ((pq ++ [ee])[i]'hi) := by
        refine PathAttach.isPathFrom_cons (G := Gᶜ) hpreFrom
          ((SimpleGraph.compl_adj G snear v).mpr ⟨hsnearnev, hsnearv⟩)
          (fun hc => hsnearnotpq (hpresubpq snear hc)) ?_
        intro x hx hxv hc
        exact ((SimpleGraph.compl_adj G snear x).mp hc).2
          (hsnearQ x (hpqQ x (hpresubpq x hx) hxv))
      have hhooknotcons : hook ∉ (snear :: pre) := by
        intro hc
        rcases List.mem_cons.mp hc with h | h
        · exact hhooknesnear h
        · exact hSnotpq hook hhookS (hpresubpq hook h)
      have hcons2 : IsPathFrom Gᶜ (hook :: snear :: pre) hook ((pq ++ [ee])[i]'hi) := by
        refine PathAttach.isPathFrom_cons (G := Gᶜ) hcons1
          ((SimpleGraph.compl_adj G hook snear).mpr ⟨hhooknesnear, hhooksnear⟩)
          hhooknotcons ?_
        intro x hx hxs hc
        have hxpre : x ∈ pre := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxs
          · exact h
        exact ((SimpleGraph.compl_adj G hook x).mp hc).2 (hhookpq x (hpresubpq x hxpre))
      have hcons2len : (hook :: snear :: pre).length = i + 3 := by
        rw [List.length_cons, List.length_cons, hprelen]
      have hodd : Odd (pathLength (hook :: snear :: pre)) := by
        rw [PathBasics.pathLength_cons, List.length_cons, hprelen, Nat.odd_iff]
        rw [Nat.odd_iff] at hipar
        omega
      have hpX : ∀ w ∈ (hook :: snear :: pre), w ∉ Fp := by
        intro w hw
        rcases List.mem_cons.mp hw with h | h
        · rw [h]; exact hFpnotmemS hook hhookS
        rcases List.mem_cons.mp h with h' | h'
        · rw [h']; exact fun hc => hsnearnF (hFpF hc)
        · exact fun hc => hextnotF w (hpresub w h') (hFpF hc)
      have hp₁ : SPGT.VertexComplete Gᶜ hook Fp := by
        intro x hx
        refine (SimpleGraph.compl_adj G hook x).mpr ⟨?_, ?_⟩
        · intro hceq
          exact hFout x (hFpF hx) (hceq ▸ hhookS)
        · intro hcadj
          exact hVSnoFp hook hhookS ⟨x, hx, hcadj⟩
      have hnoedge : ¬ ∃ u ∈ (hook :: snear :: pre), ∃ w ∈ (hook :: snear :: pre),
          SPGT.EdgeComplete Gᶜ Fp u w := by
        rintro ⟨u, hu, w, hw, hadj, hcu, hcw⟩
        have hkey : ∀ z ∈ (hook :: snear :: pre), SPGT.VertexComplete Gᶜ z Fp →
            z = hook ∨ z = ((pq ++ [ee])[i]'hi) := by
          intro z hz hzc
          rcases List.mem_cons.mp hz with h | h
          · exact Or.inl h
          rcases List.mem_cons.mp h with h' | h'
          · exfalso
            obtain ⟨f, hf, hfadj⟩ := hsnearFp
            rw [h'] at hzc
            exact absurd hfadj ((SimpleGraph.compl_adj G snear f).mp (hzc f hf)).2
          · by_cases hze : z = ((pq ++ [ee])[i]'hi)
            · exact Or.inr hze
            · exfalso
              obtain ⟨f, hf, hfadj⟩ := (hkeyidx z h' hze).1
              exact absurd hfadj ((SimpleGraph.compl_adj G z f).mp (hzc f hf)).2
        have hendsnadj : ¬ Gᶜ.Adj hook ((pq ++ [ee])[i]'hi) := by
          have h0 : (hook :: snear :: pre)[0]'(by omega) = hook :=
            PathBasics.getElem_zero_of_head? hcons2.2.1 (by omega)
          have hl : (hook :: snear :: pre)[(hook :: snear :: pre).length - 1]'(by omega)
              = ((pq ++ [ee])[i]'hi) :=
            PathBasics.getElem_last_of_getLast? hcons2.2.2 (by omega)
          rw [← h0, ← hl]
          exact PathBasics.path_not_adj_of_gap hcons2.1 (by omega) (by omega)
            (by omega) (by omega)
        rcases hkey u hu hcu with h1 | h1 <;> rcases hkey w hw hcw with h2 | h2 <;>
          rw [h1, h2] at hadj
        · exact Gᶜ.irrefl hadj
        · exact hendsnadj hadj
        · exact hendsnadj hadj.symm
        · exact Gᶜ.irrefl hadj
      obtain ⟨z, hzint, hzadj⟩ :=
        _root_.Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ (HoleBasics.berge_compl.mpr hG) Fp
          hFpanti (hook :: snear :: pre) hook ((pq ++ [ee])[i]'hi) hcons2 hpX hodd hp₁ hpn
          hnoedge comp hcompC
      rw [PathBasics.mem_interior_iff_of_pathFrom hcons2] at hzint
      obtain ⟨hzm, hzh, hze⟩ := hzint
      have hGadj : G.Adj comp z := by
        rcases List.mem_cons.mp hzm with h | h
        · exact absurd h hzh
        rcases List.mem_cons.mp h with h' | h'
        · rw [h']; exact hcompsnear
        · exact hcomppq z (hpresubpq z h')
      exact ((SimpleGraph.compl_adj G comp z).mp hzadj).2 hGadj
  have claim9 : ∀ S : Set V, S ⊆ F → ConnectedSet G S → (∃ f ∈ S, G.Adj v f) →
      (∃ f ∈ S, G.Adj qk f) → (∃ f ∈ S, G.Adj u₀ f) ∧ (∃ f ∈ S, G.Adj w₀ f) := by
    intro S hSF hSconn hSv _hSq
    by_contra hcon
    obtain ⟨f0, hf0S, hf0v⟩ := hSv
    have hFpex : ∃ Fp : Set V, Fp ⊆ F ∧ ConnectedSet G Fp ∧ S ⊆ Fp ∧
        (((∃ f ∈ Fp, G.Adj u₀ f) ∧ ¬ ∃ f ∈ Fp, G.Adj w₀ f) ∨
         ((∃ f ∈ Fp, G.Adj w₀ f) ∧ ¬ ∃ f ∈ Fp, G.Adj u₀ f)) := by
      by_cases hSu : ∃ f ∈ S, G.Adj u₀ f
      · exact ⟨S, hSF, hSconn, subset_rfl, Or.inl ⟨hSu, fun h => hcon ⟨hSu, h⟩⟩⟩
      by_cases hSw : ∃ f ∈ S, G.Adj w₀ f
      · exact ⟨S, hSF, hSconn, subset_rfl, Or.inr ⟨hSw, hSu⟩⟩
      · have hSsubFT : S ⊆ F \ {x : V | x ∈ F ∧ (G.Adj u₀ x ∨ G.Adj w₀ x)} := by
          intro x hx
          refine ⟨hSF hx, ?_⟩
          rintro ⟨-, h | h⟩
          · exact hSu ⟨x, hx, h⟩
          · exact hSw ⟨x, hx, h⟩
        obtain ⟨U, hU, hf0U⟩ :=
          ComponentsOfSetBasics.exists_isComponent_mem G
            (F \ {x : V | x ∈ F ∧ (G.Adj u₀ x ∨ G.Adj w₀ x)}) (hSsubFT hf0S)
        have hSU : S ⊆ U := by
          have hconn : ConnectedSet G (S ∪ U) :=
            ConnectedSetUnionAttach.connectedSet_union hSconn hU.2.1 (Or.inl ⟨f0, hf0S, hf0U⟩)
          have heq : S ∪ U = U :=
            hU.2.2 (S ∪ U) Set.subset_union_right (Set.union_subset hSsubFT hU.1) hconn
          exact fun x hx => heq ▸ (Or.inl hx : x ∈ S ∪ U)
        obtain ⟨t, htF, htadj⟩ := hu₀F
        have htT : t ∈ {x : V | x ∈ F ∧ (G.Adj u₀ x ∨ G.Adj w₀ x)} := ⟨htF, Or.inl htadj⟩
        have htU : t ∉ U := fun hc => (hU.1 hc).2 htT
        obtain ⟨x, hxF, hxU, y, hyU, hxy⟩ :=
          Aux.exists_cross_edge hFconn (fun z hz => (hU.1 hz).1) hf0U htF htU
        have hxconn : ConnectedSet G (U ∪ {x}) :=
          ConnectedSetUnionAttach.connectedSet_union_singleton hU.2.1 ⟨y, hyU, hxy⟩
        have hxT : x ∈ {z : V | z ∈ F ∧ (G.Adj u₀ z ∨ G.Adj w₀ z)} := by
          by_contra hcT
          have heq : U ∪ {x} = U :=
            hU.2.2 (U ∪ {x}) Set.subset_union_left
              (Set.union_subset hU.1 (Set.singleton_subset_iff.mpr ⟨hxF, hcT⟩)) hxconn
          exact hxU (heq ▸ (Or.inr rfl : x ∈ U ∪ {x}))
        have hUnoT : ∀ z ∈ U, ¬ G.Adj u₀ z ∧ ¬ G.Adj w₀ z := by
          intro z hz
          exact ⟨fun hcadj => (hU.1 hz).2 ⟨(hU.1 hz).1, Or.inl hcadj⟩,
            fun hcadj => (hU.1 hz).2 ⟨(hU.1 hz).1, Or.inr hcadj⟩⟩
        refine ⟨U ∪ {x},
          Set.union_subset (fun z hz => (hU.1 hz).1) (Set.singleton_subset_iff.mpr hxF),
          hxconn, fun z hz => Or.inl (hSU hz), ?_⟩
        rcases hxT.2 with h | h
        · refine Or.inl ⟨⟨x, Or.inr rfl, h⟩, ?_⟩
          rintro ⟨f, hf, hadj⟩
          rcases hf with hf | hf
          · exact (hUnoT f hf).2 hadj
          · exact claim8a x hxF h ((Set.mem_singleton_iff.mp hf) ▸ hadj)
        · refine Or.inr ⟨⟨x, Or.inr rfl, h⟩, ?_⟩
          rintro ⟨f, hf, hadj⟩
          rcases hf with hf | hf
          · exact (hUnoT f hf).1 hadj
          · exact claim8a x hxF ((Set.mem_singleton_iff.mp hf) ▸ hadj) h
    obtain ⟨Fp, hFpF, hFpconn, hSFp, hcase⟩ := hFpex
    have hvFp : ∃ f ∈ Fp, G.Adj v f := ⟨f0, hSFp hf0S, hf0v⟩
    rcases hcase with ⟨hnear, hfar⟩ | ⟨hnear, hfar⟩
    · exact step9 Fp w₀ u₀ bb₁ bb₂ a₁ hFpF hFpconn hvFp hnear hfar
        (Or.inr hr₁.2.2.1) hb₂S ha₁S hw₀RS.1 hu₀LS.1 hw₀notpq hu₀notpq hw₀N.1 hu₀N.1
        hvnw₀ (Ne.symm hvnew₀) hw₀Q (hw₀RS.2.1 bb₁ hr₁.2.2.1) hb₁B₂
        hvnu₀ (Ne.symm hvneu₀) hu₀Q
        (fun hc => hu₀LS.2.2 bb₂ (Or.inl hr₂.2.2.1) hc.symm)
        (fun hc => hu₀LS.1 (hc ▸ hb₂S)) hb₂pq ha₁pq (hu₀LS.2.1 a₁ ha₁X.1).symm
    · exact step9 Fp u₀ w₀ a₂ a₁ bb₂ hFpF hFpconn hvFp hnear hfar
        (Or.inl ha₂Y.1) ha₁S hb₂S hu₀LS.1 hw₀RS.1 hu₀notpq hw₀notpq hu₀N.1 hw₀N.1
        hvnu₀ (Ne.symm hvneu₀) hu₀Q (hu₀LS.2.1 a₂ ha₂Y.1) ha₂Y.2
        hvnw₀ (Ne.symm hvnew₀) hw₀Q
        (fun hc => hw₀RS.2.2 a₁ (Or.inl ha₁X.1) hc.symm)
        (fun hc => hw₀RS.1 (hc ▸ ha₁S)) ha₁pq hb₂pq (hw₀RS.2.1 bb₂ hr₂.2.2.1).symm
  -- ==================================================================================
  -- PAPER: *"Let `f₁-f₂-⋯-f_n` be a minimal path in `F` between `F_{a₀}` and `F_{b₀}` …
  --     Then `f₁-⋯-f_n-q_k-a₀-f₁` and `f₁-⋯-f_n-b₀-b₁-v-f₁` are both holes, of different
  --     parity, a contradiction."*
  -- ==================================================================================
  have hVSnotF : ∀ y ∈ A ∪ B ∪ C, y ∉ F := fun y hy hc => hFout y hc hy
  have hintdisj : ∀ (R : List V), (∀ t ∈ R, t ∉ F) → ∀ x ∈ SPGT.interior PP, x ∉ R :=
    fun R hR x hx hc => hR x hc (hPPint x hx)
  have hf1nefn : f1 ≠ fn := by
    intro hc
    exact claim8a f1 (hPPint f1 (PathBasics.isPathFrom_ends_mem hPintFrom).1) hu₀f1
      (hc.symm ▸ hw₀fn)
  have hLpos : 2 ≤ (SPGT.interior PP).length := Aux.len_ge_two hPintFrom hf1nefn
  have hf10 : (SPGT.interior PP)[0]'(by omega) = f1 :=
    PathBasics.getElem_zero_of_head? hPintFrom.2.1 (by omega)
  have hfnl : (SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega) = fn :=
    PathBasics.getElem_last_of_getLast? hPintFrom.2.2 (by omega)
  have hb₂nev : bb₂ ≠ v := fun hc => hvS (hc ▸ hb₂S)
  have hw₀neb₂ : w₀ ≠ bb₂ := fun hc => hw₀RS.1 (hc ▸ hb₂S)
  have hvnea₁ : v ≠ a₁ := fun hc => hvS (hc ▸ ha₁S)
  have ha₁neu₀ : a₁ ≠ u₀ := fun hc => hu₀LS.1 (hc ▸ ha₁S)
  have hmemslice : ∀ (a b c : ℕ) (hab : a ≤ b) (hb : b < (SPGT.interior PP).length)
      (hc : c < (SPGT.interior PP).length), a ≤ c → c ≤ b →
      ((SPGT.interior PP)[c]'hc) ∈ ((SPGT.interior PP).drop a).take (b - a + 1) := by
    intro a b c hab hb hc h1 h2
    rw [PathBasics.mem_slice_iff (SPGT.interior PP) hab hb]
    exact ⟨c, hc, h1, h2, rfl⟩
  have hslice : ∀ (a b : ℕ) (ha : a < (SPGT.interior PP).length)
      (hb : b < (SPGT.interior PP).length), a ≤ b →
      (∃ x ∈ ((SPGT.interior PP).drop a).take (b - a + 1), G.Adj v x) →
      (∃ x ∈ ((SPGT.interior PP).drop a).take (b - a + 1), G.Adj qk x) →
      a = 0 ∧ b = (SPGT.interior PP).length - 1 := by
    intro a b ha hb hab hvx hqx
    have hSl : IsPathList G (((SPGT.interior PP).drop a).take (b - a + 1)) := by
      rcases Nat.lt_or_ge a b with h | h
      · exact PathBasics.isPathList_slice hPintFrom.1 h hb
      · have hab' : b = a := by omega
        subst hab'
        simp only [Nat.sub_self]
        exact PathBasics.isPathList_take (PathBasics.isPathList_drop hPintFrom.1 ha) (by omega)
    have hslmem : ∀ x ∈ ((SPGT.interior PP).drop a).take (b - a + 1),
        ∃ (k : ℕ) (hk : k < (SPGT.interior PP).length), a ≤ k ∧ k ≤ b ∧
          ((SPGT.interior PP)[k]'hk) = x :=
      fun x hx => (PathBasics.mem_slice_iff (SPGT.interior PP) hab hb).mp hx
    have hslsubint : ∀ x ∈ ((SPGT.interior PP).drop a).take (b - a + 1),
        x ∈ SPGT.interior PP := by
      intro x hx
      obtain ⟨k, hk, -, -, hkx⟩ := hslmem x hx
      rw [← hkx]
      exact List.getElem_mem hk
    obtain ⟨hex1, hex2⟩ :=
      claim9 {x : V | x ∈ ((SPGT.interior PP).drop a).take (b - a + 1)}
        (fun x hx => hPPint x (hslsubint x hx))
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hSl) hvx hqx
    obtain ⟨g1, hg1, hg1adj⟩ := hex1
    obtain ⟨g2, hg2, hg2adj⟩ := hex2
    have hg1f1 : g1 = f1 := hu₀uniq g1 (hslsubint g1 hg1) hg1adj
    have hg2fn : g2 = fn := hw₀uniq g2 (hslsubint g2 hg2) hg2adj
    obtain ⟨k1, hk1, hk1a, hk1b, hk1x⟩ := hslmem g1 hg1
    obtain ⟨k2, hk2, hk2a, hk2b, hk2x⟩ := hslmem g2 hg2
    have hk10 : k1 = 0 := by
      have hEq : ((SPGT.interior PP)[k1]'hk1) = ((SPGT.interior PP)[0]'(by omega)) := by
        rw [hk1x, hg1f1, hf10]
      exact (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hPintFrom.1)).mp hEq
    have hk2l : k2 = (SPGT.interior PP).length - 1 := by
      have hEq : ((SPGT.interior PP)[k2]'hk2)
          = ((SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega)) := by
        rw [hk2x, hg2fn, hfnl]
      exact (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hPintFrom.1)).mp hEq
    exact ⟨by omega, by omega⟩
  -- The two closing holes, in the two possible orientations of `P`.
  have hcontraI : G.Adj v f1 → G.Adj qk fn →
      (∀ z ∈ SPGT.interior PP, G.Adj v z → z = f1) →
      (∀ z ∈ SPGT.interior PP, G.Adj qk z → z = fn) → False := by
    intro hvf1 hqkfn huniqv huniqq
    have hR1 : IsPathFrom G [qk, u₀] qk u₀ :=
      ⟨PathBasics.isPathList_pair (hu₀Q qk hqkQ).symm, rfl, by simp⟩
    have hcross1 : ∀ x ∈ SPGT.interior PP, ∀ t ∈ [qk, u₀],
        (G.Adj x t ↔ (x = fn ∧ t = qk) ∨ (x = f1 ∧ t = u₀)) := by
      intro x hx t ht
      have htc : t = qk ∨ t = u₀ := by simpa using ht
      rcases htc with h | h <;> rw [h]
      · constructor
        · intro hadj
          exact Or.inl ⟨huniqq x hx hadj.symm, rfl⟩
        · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · rw [h1]; exact hqkfn.symm
          · exact absurd h2 hqkneu₀
      · constructor
        · intro hadj
          exact Or.inr ⟨hu₀uniq x hx hadj.symm, rfl⟩
        · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact absurd h2.symm hqkneu₀
          · rw [h1]; exact hu₀f1.symm
    have hhole1 : IsHoleList G (SPGT.interior PP ++ [qk, u₀]) := by
      refine PathGlue.glue_hole hPintFrom hR1 (hintdisj [qk, u₀] ?_) hcross1
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro t ht
      have htc : t = qk ∨ t = u₀ := by simpa using ht
      rcases htc with h | h
      · rw [h]; exact hqknF
      · rw [h]; exact hu₀N.1
    have hR2 : IsPathFrom G [w₀, bb₂, v] w₀ v :=
      ⟨Aux.isPathList_three (by simp [hw₀neb₂, hb₂nev, hvnew₀, Ne.symm hvnew₀])
        (hw₀RS.2.1 bb₂ hr₂.2.2.1) (hvAB bb₂ (Or.inr hr₂.2.2.1)).symm hvnw₀, rfl, by simp⟩
    have hcross2 : ∀ x ∈ SPGT.interior PP, ∀ t ∈ [w₀, bb₂, v],
        (G.Adj x t ↔ (x = fn ∧ t = w₀) ∨ (x = f1 ∧ t = v)) := by
      intro x hx t ht
      have htc : t = w₀ ∨ t = bb₂ ∨ t = v := by simpa using ht
      rcases htc with h | h | h <;> rw [h]
      · constructor
        · intro hadj
          exact Or.inl ⟨hw₀uniq x hx hadj.symm, rfl⟩
        · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · rw [h1]; exact hw₀fn.symm
          · exact absurd h2.symm hvnew₀
      · exact iff_of_false (hFanti x (hPPint x hx) bb₂ hb₂S)
          (by rintro (⟨-, h2⟩ | ⟨-, h2⟩); exacts [hw₀neb₂ h2.symm, hb₂nev h2])
      · constructor
        · intro hadj
          exact Or.inr ⟨huniqv x hx hadj.symm, rfl⟩
        · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact absurd h2 hvnew₀
          · rw [h1]; exact hvf1.symm
    have hhole2 : IsHoleList G (SPGT.interior PP ++ [w₀, bb₂, v]) := by
      refine PathGlue.glue_hole hPintFrom hR2 (hintdisj [w₀, bb₂, v] ?_) hcross2
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro t ht
      have htc : t = w₀ ∨ t = bb₂ ∨ t = v := by simpa using ht
      rcases htc with h | h | h
      · rw [h]; exact hw₀N.1
      · rw [h]; exact hVSnotF bb₂ hb₂S
      · rw [h]; exact hvF
    have hev1 := hG.1 _ hhole1
    have hev2 := hG.1 _ hhole2
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev1 hev2
    rw [Nat.even_iff] at hev1 hev2
    omega
  have hcontraII : G.Adj qk f1 → G.Adj v fn →
      (∀ z ∈ SPGT.interior PP, G.Adj qk z → z = f1) →
      (∀ z ∈ SPGT.interior PP, G.Adj v z → z = fn) → False := by
    intro hqkf1 hvfn huniqq huniqv
    have hR1 : IsPathFrom G [w₀, qk] w₀ qk :=
      ⟨PathBasics.isPathList_pair (hw₀Q qk hqkQ), rfl, by simp⟩
    have hcross1 : ∀ x ∈ SPGT.interior PP, ∀ t ∈ [w₀, qk],
        (G.Adj x t ↔ (x = fn ∧ t = w₀) ∨ (x = f1 ∧ t = qk)) := by
      intro x hx t ht
      have htc : t = w₀ ∨ t = qk := by simpa using ht
      rcases htc with h | h <;> rw [h]
      · constructor
        · intro hadj
          exact Or.inl ⟨hw₀uniq x hx hadj.symm, rfl⟩
        · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · rw [h1]; exact hw₀fn.symm
          · exact absurd h2.symm hqknew₀
      · constructor
        · intro hadj
          exact Or.inr ⟨huniqq x hx hadj.symm, rfl⟩
        · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact absurd h2 hqknew₀
          · rw [h1]; exact hqkf1.symm
    have hhole1 : IsHoleList G (SPGT.interior PP ++ [w₀, qk]) := by
      refine PathGlue.glue_hole hPintFrom hR1 (hintdisj [w₀, qk] ?_) hcross1
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro t ht
      have htc : t = w₀ ∨ t = qk := by simpa using ht
      rcases htc with h | h
      · rw [h]; exact hw₀N.1
      · rw [h]; exact hqknF
    have hR2 : IsPathFrom G [v, a₁, u₀] v u₀ :=
      ⟨Aux.isPathList_three (by simp [hvnea₁, ha₁neu₀, hvneu₀, Ne.symm hvneu₀])
        (hvAB a₁ (Or.inl ha₁X.1)) (hu₀LS.2.1 a₁ ha₁X.1).symm (fun hc => hvnu₀ hc.symm),
        rfl, by simp⟩
    have hcross2 : ∀ x ∈ SPGT.interior PP, ∀ t ∈ [v, a₁, u₀],
        (G.Adj x t ↔ (x = fn ∧ t = v) ∨ (x = f1 ∧ t = u₀)) := by
      intro x hx t ht
      have htc : t = v ∨ t = a₁ ∨ t = u₀ := by simpa using ht
      rcases htc with h | h | h <;> rw [h]
      · constructor
        · intro hadj
          exact Or.inl ⟨huniqv x hx hadj.symm, rfl⟩
        · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · rw [h1]; exact hvfn.symm
          · exact absurd h2 hvneu₀
      · exact iff_of_false (hFanti x (hPPint x hx) a₁ ha₁S)
          (by rintro (⟨-, h2⟩ | ⟨-, h2⟩); exacts [hvnea₁ h2.symm, ha₁neu₀ h2])
      · constructor
        · intro hadj
          exact Or.inr ⟨hu₀uniq x hx hadj.symm, rfl⟩
        · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact absurd h2.symm hvneu₀
          · rw [h1]; exact hu₀f1.symm
    have hhole2 : IsHoleList G (SPGT.interior PP ++ [v, a₁, u₀]) := by
      refine PathGlue.glue_hole hPintFrom hR2 (hintdisj [v, a₁, u₀] ?_) hcross2
        (by simp only [List.length_cons, List.length_nil]; omega)
      intro t ht
      have htc : t = v ∨ t = a₁ ∨ t = u₀ := by simpa using ht
      rcases htc with h | h | h
      · rw [h]; exact hvF
      · rw [h]; exact hVSnotF a₁ ha₁S
      · rw [h]; exact hu₀N.1
    have hev1 := hG.1 _ hhole1
    have hev2 := hG.1 _ hhole2
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hev1 hev2
    rw [Nat.even_iff] at hev1 hev2
    omega
  obtain ⟨zv, hzvint, hzvadj⟩ := claim8v
  obtain ⟨zq, hzqint, hzqadj⟩ := claim8q
  obtain ⟨av, hav, havz⟩ := List.getElem_of_mem hzvint
  obtain ⟨bq, hbq, hbqz⟩ := List.getElem_of_mem hzqint
  rcases Nat.le_total av bq with hle | hle
  · have hmem1 : ((SPGT.interior PP)[av]'hav) ∈
        ((SPGT.interior PP).drop av).take (bq - av + 1) :=
      hmemslice av bq av hle hbq hav (le_refl av) hle
    have hmem2 : ((SPGT.interior PP)[bq]'hbq) ∈
        ((SPGT.interior PP).drop av).take (bq - av + 1) :=
      hmemslice av bq bq hle hbq hbq hle (le_refl bq)
    have hadjv : G.Adj v ((SPGT.interior PP)[av]'hav) := by rw [havz]; exact hzvadj
    have hadjq : G.Adj qk ((SPGT.interior PP)[bq]'hbq) := by rw [hbqz]; exact hzqadj
    obtain ⟨hav0, hbql⟩ := hslice av bq hav hbq hle ⟨_, hmem1, hadjv⟩ ⟨_, hmem2, hadjq⟩
    have hvf1 : G.Adj v f1 := by
      rw [← hf10, ← Aux.getElem_eq_index (SPGT.interior PP) hav (by omega) hav0, havz]
      exact hzvadj
    have hqkfn : G.Adj qk fn := by
      rw [← hfnl, ← Aux.getElem_eq_index (SPGT.interior PP) hbq (by omega) hbql, hbqz]
      exact hzqadj
    refine hcontraI hvf1 hqkfn ?_ ?_
    · intro z hz hzadj
      obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem hz
      have hcle : c ≤ (SPGT.interior PP).length - 1 := by omega
      have hm1 : ((SPGT.interior PP)[c]'hc) ∈
          ((SPGT.interior PP).drop c).take ((SPGT.interior PP).length - 1 - c + 1) :=
        hmemslice c ((SPGT.interior PP).length - 1) c hcle (by omega) hc (le_refl c) hcle
      have hm2 : ((SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega)) ∈
          ((SPGT.interior PP).drop c).take ((SPGT.interior PP).length - 1 - c + 1) :=
        hmemslice c ((SPGT.interior PP).length - 1) ((SPGT.interior PP).length - 1) hcle
          (by omega) (by omega) hcle (le_refl _)
      have ha1 : G.Adj v ((SPGT.interior PP)[c]'hc) := by rw [hcz]; exact hzadj
      have ha2 : G.Adj qk ((SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega)) := by
        rw [hfnl]; exact hqkfn
      have hres := hslice c ((SPGT.interior PP).length - 1) hc (by omega) hcle
        ⟨_, hm1, ha1⟩ ⟨_, hm2, ha2⟩
      rw [← hcz, ← hf10]
      exact Aux.getElem_eq_index _ hc (by omega) hres.1
    · intro z hz hzadj
      obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem hz
      have hcle : (0 : ℕ) ≤ c := Nat.zero_le c
      have hm1 : ((SPGT.interior PP)[0]'(by omega)) ∈
          ((SPGT.interior PP).drop 0).take (c - 0 + 1) :=
        hmemslice 0 c 0 hcle hc (by omega) (le_refl 0) hcle
      have hm2 : ((SPGT.interior PP)[c]'hc) ∈
          ((SPGT.interior PP).drop 0).take (c - 0 + 1) :=
        hmemslice 0 c c hcle hc hc hcle (le_refl c)
      have ha1 : G.Adj v ((SPGT.interior PP)[0]'(by omega)) := by rw [hf10]; exact hvf1
      have ha2 : G.Adj qk ((SPGT.interior PP)[c]'hc) := by rw [hcz]; exact hzadj
      have hres := hslice 0 c (by omega) hc hcle ⟨_, hm1, ha1⟩ ⟨_, hm2, ha2⟩
      rw [← hcz, ← hfnl]
      exact Aux.getElem_eq_index _ hc (by omega) hres.2
  · have hmem1 : ((SPGT.interior PP)[av]'hav) ∈
        ((SPGT.interior PP).drop bq).take (av - bq + 1) :=
      hmemslice bq av av hle hav hav hle (le_refl av)
    have hmem2 : ((SPGT.interior PP)[bq]'hbq) ∈
        ((SPGT.interior PP).drop bq).take (av - bq + 1) :=
      hmemslice bq av bq hle hav hbq (le_refl bq) hle
    have hadjv : G.Adj v ((SPGT.interior PP)[av]'hav) := by rw [havz]; exact hzvadj
    have hadjq : G.Adj qk ((SPGT.interior PP)[bq]'hbq) := by rw [hbqz]; exact hzqadj
    obtain ⟨hbq0, havl⟩ := hslice bq av hbq hav hle ⟨_, hmem1, hadjv⟩ ⟨_, hmem2, hadjq⟩
    have hqkf1 : G.Adj qk f1 := by
      rw [← hf10, ← Aux.getElem_eq_index (SPGT.interior PP) hbq (by omega) hbq0, hbqz]
      exact hzqadj
    have hvfn : G.Adj v fn := by
      rw [← hfnl, ← Aux.getElem_eq_index (SPGT.interior PP) hav (by omega) havl, havz]
      exact hzvadj
    refine hcontraII hqkf1 hvfn ?_ ?_
    · intro z hz hzadj
      obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem hz
      have hcle : c ≤ (SPGT.interior PP).length - 1 := by omega
      have hm1 : ((SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega)) ∈
          ((SPGT.interior PP).drop c).take ((SPGT.interior PP).length - 1 - c + 1) :=
        hmemslice c ((SPGT.interior PP).length - 1) ((SPGT.interior PP).length - 1) hcle
          (by omega) (by omega) hcle (le_refl _)
      have hm2 : ((SPGT.interior PP)[c]'hc) ∈
          ((SPGT.interior PP).drop c).take ((SPGT.interior PP).length - 1 - c + 1) :=
        hmemslice c ((SPGT.interior PP).length - 1) c hcle (by omega) hc (le_refl c) hcle
      have ha1 : G.Adj v ((SPGT.interior PP)[(SPGT.interior PP).length - 1]'(by omega)) := by
        rw [hfnl]; exact hvfn
      have ha2 : G.Adj qk ((SPGT.interior PP)[c]'hc) := by rw [hcz]; exact hzadj
      have hres := hslice c ((SPGT.interior PP).length - 1) hc (by omega) hcle
        ⟨_, hm1, ha1⟩ ⟨_, hm2, ha2⟩
      rw [← hcz, ← hf10]
      exact Aux.getElem_eq_index _ hc (by omega) hres.1
    · intro z hz hzadj
      obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem hz
      have hcle : (0 : ℕ) ≤ c := Nat.zero_le c
      have hm1 : ((SPGT.interior PP)[c]'hc) ∈
          ((SPGT.interior PP).drop 0).take (c - 0 + 1) :=
        hmemslice 0 c c hcle hc hc hcle (le_refl c)
      have hm2 : ((SPGT.interior PP)[0]'(by omega)) ∈
          ((SPGT.interior PP).drop 0).take (c - 0 + 1) :=
        hmemslice 0 c 0 hcle hc (by omega) (le_refl 0) hcle
      have ha1 : G.Adj v ((SPGT.interior PP)[c]'hc) := by rw [hcz]; exact hzadj
      have ha2 : G.Adj qk ((SPGT.interior PP)[0]'(by omega)) := by rw [hf10]; exact hqkf1
      have hres := hslice 0 c (by omega) hc hcle ⟨_, hm1, ha1⟩ ⟨_, hm2, ha2⟩
      rw [← hcz, ← hfnl]
      exact Aux.getElem_eq_index _ hc (by omega) hres.2


/-- **11.5** (printed p. 66)

PAPER: *"Let `G` be a Berge graph, such that there is no appearance of `K₄` in `G` and no even
prism in `G`.  If there is a 1-breaker in `G` then `G` admits a balanced skew partition."*

A 1-breaker is a triple `(S, F, Q)` with `S = (A, C, B)`, so *"there is a 1-breaker in `G`"*
is the existence of five sets `A, C, B, F, Q` with `IsOneBreaker G A C B F Q`. -/
theorem thm_11_5 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ∃ A C B F Q : Set V, IsOneBreaker G A C B F Q) :
    AdmitsBalancedSkewPartition G := by
  classical
  -- PAPER: *"We may assume that `G` admits no balanced skew partition, for otherwise the
  -- theorem holds."*
  by_contra hno
  obtain ⟨A, C, B, F₀, Q₀, hbr₀⟩ := hbreaker
  -- PAPER: *"… for fixed `G` and `S`, choose `F` and `Q` with `|F| + |Q|` maximum such that
  -- all the hypotheses of the theorem remain satisfied (possibly exchanging "left" and
  -- "right")."*
  obtain ⟨⟨F, Q⟩, hP, hmax⟩ :=
    Workspace.ProofLemmas.ExtremalChoice.exists_max_nat
      (fun FQ : Set V × Set V =>
        IsOneBreaker G A C B FQ.1 FQ.2 ∨ IsOneBreaker G B C A FQ.1 FQ.2)
      (fun FQ => FQ.1.ncard + FQ.2.ncard) (2 * Fintype.card V)
      (by
        rintro ⟨F', Q'⟩ -
        have h1 := Workspace.ProofLemmas.ExtremalChoice.ncard_le_card F'
        have h2 := Workspace.ProofLemmas.ExtremalChoice.ncard_le_card Q'
        simp only
        omega)
      ⟨(F₀, Q₀), Or.inl hbr₀⟩
  rcases hP with h | h
  · exact core hG hK4 hprism hno h (fun F' Q' hF' => hmax (F', Q') hF')
  · exact core hG hK4 hprism hno h (fun F' Q' hF' => hmax (F', Q') hF'.symm)


end SPGT

end Workspace.Statements.S11
