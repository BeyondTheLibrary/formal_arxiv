import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.Thm183EdgeCount
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# Counting the `Y`-complete edges of the holes built in the `|F| ≥ 2` line of 16.2

Claims (3), (4) and the endgame of 16.2 all build a hole out of the path `f₁-⋯-f_k` (or a
slight variant) and an arc of the rim, and then say the same thing about it:

> *"since this hole contains an odd number of `Y`-complete edges (since all neighbours of `f_k`
> have wheel-parity opposite from that of `p₁`) it follows from 2.3 that it contains exactly one
> such edge and only two `Y`-complete vertices."*

This module is that step, once:

* `parity_step` — the bridge between the parity function `π` of
  `OddWheelParityFacts.exists_parity'` and `EdgeComplete`: two **adjacent** rim vertices have
  different `π` exactly when the edge between them is `Y`-complete.
* `yEdges_append_reverse` — a hole assembled as `S ++ Q.reverse` where **no vertex of `S` is
  `Y`-complete** has exactly the `Y`-complete edges of `Q`.
* `arc_yEdges_ncard` — the `Y`-complete edges of an arc of the rim, counted by index.
* `odd_yEdges_of_arc` — combining the previous two with
  `OddWheelAttachmentArcs.parity_telescope`: an arc whose two ends have different `π` carries an
  **odd** number of `Y`-complete edges.
* `exactly_one_yEdge_of_odd` — the *"it follows from 2.3"*: a hole disjoint from `Y` carrying an
  odd number of `Y`-complete edges carries exactly one, and has exactly two `Y`-complete
  vertices, which are adjacent.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentYCount

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### `π` versus `EdgeComplete` on a rim edge -/

/-- **Two adjacent rim vertices have different wheel-parity exactly when the edge between them
is `Y`-complete.**  This is the `hstep` hypothesis of
`OddWheelAttachmentArcs.parity_telescope`, assembled from the two halves already proved in
`OddWheelParityFacts`. -/
theorem parity_step {G : SimpleGraph V} {C : List V} {Y : Set V} (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length)) {π : V → ℕ}
    (hπ : ∀ x y : V, x ∈ C → y ∈ C → x ≠ y → (SameWheelParity G C Y x y ↔ π x = π y))
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hadj : G.Adj x y) :
    (π x ≠ π y ↔ EdgeComplete G Y x y) := by
  constructor
  · intro hne
    have hnsame : ¬ SameWheelParity G C Y x y := fun hs => hne ((hπ x y hx hy hadj.ne).mp hs)
    have hxc : VertexComplete G x Y := by
      by_contra hcon
      exact hnsame (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hx hy
        hadj hcon)
    have hyc : VertexComplete G y Y := by
      by_contra hcon
      exact hnsame (WheelParity.sameWheelParity_symm
        (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hy hx hadj.symm
          hcon))
    exact ⟨hadj, hxc, hyc⟩
  · intro hE hpe
    exact OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hC heven hx hy hE
      ((hπ x y hx hy hadj.ne).mpr hpe)

/-! ### The `Y`-complete edges of `S ++ Q.reverse` -/

/-- A hole (or any list) of the form `S ++ Q.reverse` in which **no vertex of `S` is
`Y`-complete** has exactly the `Y`-complete edges of `Q`: every `Y`-complete edge has both ends
`Y`-complete, hence both ends in `Q`. -/
theorem yEdges_append_reverse [Fintype V] [DecidableEq V] {G : SimpleGraph V} {Y : Set V}
    {S Q : List V} (hS : ∀ z ∈ S, ¬ VertexComplete G z Y) :
    HoleYEdgeParity.yEdges G Y (S ++ Q.reverse) = HoleYEdgeParity.yEdges G Y Q := by
  ext e
  simp only [HoleYEdgeParity.yEdges, Set.mem_setOf_eq, List.mem_append, List.mem_reverse]
  constructor
  · rintro ⟨u, hu, v, hv, rfl, hE⟩
    have hu' : u ∈ Q := by
      rcases hu with h | h
      · exact absurd hE.2.1 (hS u h)
      · exact h
    have hv' : v ∈ Q := by
      rcases hv with h | h
      · exact absurd hE.2.2 (hS v h)
      · exact h
    exact ⟨u, hu', v, hv', rfl, hE⟩
  · rintro ⟨u, hu, v, hv, rfl, hE⟩
    exact ⟨u, Or.inr hu, v, Or.inr hv, rfl, hE⟩

/-! ### The `Y`-complete edges of an arc of the rim, counted by index -/

/-- The `Y`-complete edges of the arc `p_{b+1}-⋯-p_{b+L}` of the rim are its `Y`-complete
consecutive pairs, indexed by `t < L - 1`. -/
theorem arc_yEdges_ncard [Fintype V] [DecidableEq V] {G : SimpleGraph V} {D : List V}
    (hD : IsHoleList G D) (hpos : 0 < D.length) (Y : Set V) {b L : ℕ}
    (hL1 : 1 ≤ L) (hL2 : L + 1 ≤ D.length) :
    (HoleYEdgeParity.yEdges G Y (arc D hpos b L)).ncard
      = ((Finset.range (L - 1)).filter
          (fun t => EdgeComplete G Y (cyc D hpos (b + t)) (cyc D hpos (b + (t + 1))))).card := by
  classical
  have hlen : (arc D hpos b L).length = L := arc_length hpos b L
  have hadjstep : ∀ t : ℕ, t + 1 < L →
      G.Adj (cyc D hpos (b + t)) (cyc D hpos (b + (t + 1))) := by
    intro t ht
    refine (cyc_adj hD hpos (b + t) (b + (t + 1))).mpr (Or.inl ?_)
    rw [Nat.add_assoc]
  rw [Thm183EdgeCount.yEdges_ncard_eq_index_ncard (arc_isPathList hD hpos hL1 hL2)]
  have hset : Thm183EdgeCount.YEdgeIdx G Y (arc D hpos b L)
      = ↑((Finset.range (L - 1)).filter
          (fun t => EdgeComplete G Y (cyc D hpos (b + t)) (cyc D hpos (b + (t + 1))))) := by
    ext t
    simp only [Thm183EdgeCount.YEdgeIdx, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨ht, h1, h2⟩
      rw [hlen] at ht
      rw [arc_getElem] at h1 h2
      exact ⟨by omega, hadjstep t ht, h1, h2⟩
    · rintro ⟨ht, hE⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [arc_getElem]; exact hE.2.1
      · rw [arc_getElem]; exact hE.2.2
  rw [hset, Set.ncard_coe_finset]

/-- **An arc of the rim whose ends have different wheel-parity carries an odd number of
`Y`-complete edges.**

This is the printed *"since all neighbours of `f_k` have wheel-parity opposite from that of
`p₁`"* half of the recurring sentence. -/
theorem odd_yEdges_of_arc [Fintype V] [DecidableEq V] {G : SimpleGraph V} {D : List V}
    (hD : IsHoleList G D) (hpos : 0 < D.length) {Y : Set V} {π : V → ℕ}
    (hπ2 : ∀ x : V, π x < 2)
    (hstep : ∀ x y : V, x ∈ D → y ∈ D → G.Adj x y → (π x ≠ π y ↔ EdgeComplete G Y x y))
    {b s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 2 ≤ D.length)
    (hπne : π (cyc D hpos b) ≠ π (cyc D hpos (b + s))) :
    Odd (HoleYEdgeParity.yEdges G Y (arc D hpos b (s + 1))).ncard := by
  classical
  have hcount := arc_yEdges_ncard hD hpos Y (b := b) (L := s + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hcount
  have htel := parity_telescope (G := G) (C := D) (Y := Y) (π := π) hπ2 hstep
      (fun t => cyc D hpos (b + t)) 0 s (by omega)
      (fun t _ _ => cyc_mem hpos _)
      (fun t _ ht => (cyc_adj hD hpos (b + t) (b + (t + 1))).mpr (Or.inl (by rw [Nat.add_assoc])))
  simp only [Nat.add_zero] at htel
  rw [← Finset.range_eq_Ico] at htel
  have h1 := hπ2 (cyc D hpos b)
  have h2 := hπ2 (cyc D hpos (b + s))
  rw [Nat.odd_iff, hcount]
  omega

/-! ### *"…it follows from 2.3 that it contains exactly one such edge and only two `Y`-complete
vertices"* -/

/-- **The 2.3 step.**  A hole disjoint from an anticonnected `Y` in a Berge graph that carries
an odd number of `Y`-complete edges carries exactly one, and has exactly two `Y`-complete
vertices, which are adjacent. -/
theorem exactly_one_yEdge_of_odd [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hBerge : Berge G) {Y : Set V} (hY : AnticonnectedSet G Y) {H : List V}
    (hH : IsHoleList G H) (hHY : ∀ w ∈ H, w ∉ Y)
    (hodd : Odd (HoleYEdgeParity.yEdges G Y H).ncard) :
    (HoleYEdgeParity.yEdges G Y H).ncard = 1 ∧
      ∃ c d : V, {w : V | w ∈ H ∧ VertexComplete G w Y} = {c, d} ∧ c ≠ d ∧ G.Adj c d := by
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hY H (Or.inr hH) hHY).2 hH
  rw [Nat.odd_iff] at hodd
  rcases h23 with heven | ⟨c, d, hset, hcd, hadj⟩
  · exfalso
    obtain ⟨m, hm⟩ := heven
    simp only [HoleYEdgeParity.yEdges] at hodd hm
    omega
  · have hle := HoleYEdgeParity.yEdges_ncard_le_one_of_pair (G := G) (Y := Y) (C := H) hset
    exact ⟨by omega, c, d, hset, hcd, hadj⟩

/-! ### The recurring sentence, packaged -/

/-- **The whole recurring sentence of the `|F| ≥ 2` line of 16.2, in one lemma.**

PAPER (claim (4); and, mutatis mutandis, claim (3) and the paragraph after claim (4)):

> *"Since `q₁, q₂` have opposite wheel-parity, it follows that there are an odd number of
> `Y`-complete edges in the hole `f₁-⋯-f_k-q₂-Q-q₁-f₁`; so by 2.3 there is exactly one, and just
> two `Y`-complete vertices."*

`S` is the rim-disjoint path (`f₁-⋯-f_k`), the arc `[b, b+s]` is `Q`, and the hole is
`S ++ Q.reverse` — the shape `OddWheelAttachmentClaim4.hole_of_path_and_arc` produces.  Because
no vertex of `S` is `Y`-complete, all the hole's `Y`-complete edges lie on the arc, and the arc
has ends of different wheel-parity, so their number is odd.

The `Even` conjunct is the printed *"`Q` has parity `k − 1`"* / *"`R₁` and `Q₁` have lengths of
opposite parity"*: `G` is Berge, so the hole has even length, and its length is
`|S| + s + 1`. -/
theorem hole_yData [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hpos : 0 < C.length) {Y : Set V}
    (hBerge : Berge G) (hYanti : AnticonnectedSet G Y) (hCY : ∀ w ∈ C, w ∉ Y)
    {π : V → ℕ} (hπ2 : ∀ z : V, π z < 2)
    (hstep : ∀ z w : V, z ∈ C → w ∈ C → G.Adj z w → (π z ≠ π w ↔ EdgeComplete G Y z w))
    {b s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 2 ≤ C.length)
    {S : List V} (hSY : ∀ z ∈ S, z ∉ Y) (hSnc : ∀ z ∈ S, ¬ VertexComplete G z Y)
    (hπne : π (cyc C hpos b) ≠ π (cyc C hpos (b + s)))
    (hH : IsHoleList G (S ++ (arc C hpos b (s + 1)).reverse)) :
    Even (S.length + s + 1) ∧
      (HoleYEdgeParity.yEdges G Y (S ++ (arc C hpos b (s + 1)).reverse)).ncard = 1 ∧
      ∃ c d : V,
        {w : V | w ∈ (S ++ (arc C hpos b (s + 1)).reverse) ∧ VertexComplete G w Y} = {c, d} ∧
          c ≠ d ∧ G.Adj c d := by
  classical
  have hlen : (S ++ (arc C hpos b (s + 1)).reverse).length = S.length + (s + 1) := by
    rw [List.length_append, List.length_reverse, arc_length]
  have hHY : ∀ w ∈ (S ++ (arc C hpos b (s + 1)).reverse), w ∉ Y := by
    intro w hw
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hSY w hw'
    · rw [List.mem_reverse] at hw'
      obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hw'
      exact hCY w (by rw [← hte]; exact cyc_mem hpos _)
  have hodd : Odd (HoleYEdgeParity.yEdges G Y (S ++ (arc C hpos b (s + 1)).reverse)).ncard := by
    rw [yEdges_append_reverse hSnc]
    exact odd_yEdges_of_arc hC hpos hπ2 hstep hs1 hs2 hπne
  obtain ⟨h1, h2⟩ := exactly_one_yEdge_of_odd hBerge hYanti hH hHY hodd
  refine ⟨?_, h1, h2⟩
  have heven := hBerge.1 _ hH
  simp only [SPGT.holeLength, hlen] at heven
  obtain ⟨m, hm⟩ := heven
  exact ⟨m, by omega⟩

/-! ### *"there is no `Y`-complete vertex in `C` different from `p₁` with the same wheel-parity
as `p₁`, a contradiction"* -/

/-- **A second `Y`-complete rim vertex of any prescribed wheel-parity.**

PAPER (claim (3), and again in claim (5)): *"there are two disjoint `Y`-complete edges in `C`,
and an even number of `Y`-complete edges in `C`"*, used to produce a `Y`-complete rim vertex of
a named wheel-parity other than a named vertex.

A wheel carries two `Y`-complete rim edges with all four ends distinct; the two ends of a
`Y`-complete edge have *different* wheel-parity, so each edge contributes one vertex of each
parity, and the two contributions are distinct. -/
theorem exists_same_parity_yComplete [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {C : List V} {Y : Set V}
    (hBerge : Berge G) (hw : IsWheel G C Y) {π : V → ℕ} (hπ2 : ∀ z : V, π z < 2)
    (hπ : ∀ a b : V, a ∈ C → b ∈ C → a ≠ b → (SameWheelParity G C Y a b ↔ π a = π b))
    {p : V} :
    ∃ w : V, w ∈ C ∧ VertexComplete G w Y ∧ w ≠ p ∧ π w = π p := by
  have hC : IsHoleList G C := hw.1.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hac, had, hbc, hbd⟩ := hw.2.2
  have hπab : π a ≠ π b := (parity_step hC heven hπ haC hbC hab.1).mpr hab
  have hπcd : π c ≠ π d := (parity_step hC heven hπ hcC hdC hcd.1).mpr hcd
  have hu : ∃ u : V, (u = a ∨ u = b) ∧ π u = π p := by
    by_cases hpa : π a = π p
    · exact ⟨a, Or.inl rfl, hpa⟩
    · refine ⟨b, Or.inr rfl, ?_⟩
      have h1 := hπ2 a; have h2 := hπ2 b; have h3 := hπ2 p; omega
  have hv : ∃ v : V, (v = c ∨ v = d) ∧ π v = π p := by
    by_cases hpc : π c = π p
    · exact ⟨c, Or.inl rfl, hpc⟩
    · refine ⟨d, Or.inr rfl, ?_⟩
      have h1 := hπ2 c; have h2 := hπ2 d; have h3 := hπ2 p; omega
  obtain ⟨u, hu1, hu2⟩ := hu
  obtain ⟨v, hv1, hv2⟩ := hv
  have huC : u ∈ C := by rcases hu1 with rfl | rfl; exacts [haC, hbC]
  have hvC : v ∈ C := by rcases hv1 with rfl | rfl; exacts [hcC, hdC]
  have huY : VertexComplete G u Y := by rcases hu1 with rfl | rfl; exacts [hab.2.1, hab.2.2]
  have hvY : VertexComplete G v Y := by rcases hv1 with rfl | rfl; exacts [hcd.2.1, hcd.2.2]
  have huv : u ≠ v := by
    rcases hu1 with rfl | rfl <;> rcases hv1 with rfl | rfl <;> assumption
  by_cases hup : u = p
  · exact ⟨v, hvC, hvY, by rw [← hup]; exact fun he => huv he.symm, hv2⟩
  · exact ⟨u, huC, huY, hup, hu2⟩

/-! ### The closing move of claim (3) and of claim (5) -/

/-- **The `13.6`-then-`2.2` endgame, shared by claim (3) and claim (5) of 16.2.**

Both claims end with the identical five sentences:

> *"…and again its ends are `Y`-complete and its internal vertices are not.  So it has length 3,
> by 13.6, and so `k = 2`; and every `Y`-complete vertex is adjacent to one of `f₁, f₂`.
> Consequently there is no `Y`-complete vertex in `C` different from `p₁` with the same
> wheel-parity as `p₁`, a contradiction."*

`W` is the odd path (`p₁-f₁-⋯-f_k-Q-x` in claim (3), `p₁-f₁-⋯-f_k-P-x` in claim (5)); `f₁` and
`fk` are two distinct interior vertices of it.  13.6 forces `pathLength W = 3`, so the interior
is exactly `{f₁, f_k}` — this is the printed *"`k = 2`"*.  2.2 then says every `Y`-complete
vertex has a neighbour in that interior.  But the rim neighbours of `f₁` are only `p₁`
(`hnbr₁`, the printed `X₁ = {p₁}`), and every rim neighbour of `f_k` has wheel-parity opposite
to `p₁` (`hnbrk`); so no `Y`-complete rim vertex other than `p₁` can carry `p₁`'s wheel-parity,
contradicting `exists_same_parity_yComplete`. -/
theorem odd_YY_path_contradiction [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : InF6 G) {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    {π : V → ℕ} (hπ2 : ∀ z : V, π z < 2)
    (hπ : ∀ a b : V, a ∈ C → b ∈ C → a ≠ b → (SameWheelParity G C Y a b ↔ π a = π b))
    {W : List V} {p₁ x f₁ fk : V}
    (hW : IsPathFrom G W p₁ x) (hodd : Odd (pathLength W))
    (hp₁Y : VertexComplete G p₁ Y) (hxY : VertexComplete G x Y)
    (hintnc : ∀ z ∈ SPGT.interior W, ¬ VertexComplete G z Y)
    (hWY : ∀ z ∈ W, z ∉ Y)
    (hf₁ : f₁ ∈ SPGT.interior W) (hfk : fk ∈ SPGT.interior W) (hne : f₁ ≠ fk)
    (hnbr₁ : ∀ u : V, u ∈ C → G.Adj f₁ u → u = p₁)
    (hnbrk : ∀ u : V, u ∈ C → G.Adj fk u → π u ≠ π p₁) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have h0 : 0 < (SPGT.interior W).length := List.length_pos_of_mem hf₁
  rw [PathBasics.interior_length] at h0
  have hlen3 : 3 ≤ W.length := by omega
  have hW0 : (W[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hW.2.1 (by omega)
  have hWl : (W[W.length - 1]'(by omega)) = x := PathBasics.getElem_last_of_getLast? hW.2.2
    (by omega)
  -- *"its ends are `Y`-complete and its internal vertices are not"*: `W` has no `Y`-complete
  -- edge, since such an edge would join the two ends, which are non-adjacent.
  have hends : ∀ z : V, z ∈ W → VertexComplete G z Y → z = p₁ ∨ z = x := by
    intro z hzW hzY
    by_contra hcon
    push_neg at hcon
    exact hintnc z ((PathBasics.mem_interior_iff_of_pathFrom hW).mpr ⟨hzW, hcon.1, hcon.2⟩) hzY
  have hnoedge : ¬ ∃ u ∈ W, ∃ v ∈ W, EdgeComplete G Y u v := by
    rintro ⟨u, huW, v, hvW, hadj, huY, hvY⟩
    have hpx : G.Adj p₁ x := by
      rcases hends u huW huY with rfl | rfl <;> rcases hends v hvW hvY with rfl | rfl
      · exact absurd rfl hadj.ne
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hadj.ne
    rw [← hW0, ← hWl] at hpx
    exact PathBasics.path_ends_not_adj hW.1 hlen3 hpx
  have hXP : Y ⊆ {v : V | v ∈ W}ᶜ := fun y hy hmem => hWY y hmem hy
  -- *"So it has length 3, by 13.6, and so `k = 2`."*
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1 W p₁ x hW hodd Y hXP hYanti
    hp₁Y hxY with hedge | ⟨-, c, d, hcd, -⟩
  · exact hnoedge hedge
  have hcover : ∀ z : V, z ∈ SPGT.interior W → z = f₁ ∨ z = fk := by
    have hf₁' : f₁ = c ∨ f₁ = d := by
      have := hf₁; rw [hcd] at this; simpa using this
    have hfk' : fk = c ∨ fk = d := by
      have := hfk; rw [hcd] at this; simpa using this
    intro z hz
    rw [hcd] at hz
    have hz' : z = c ∨ z = d := by simpa using hz
    rcases hf₁' with rfl | rfl <;> rcases hfk' with rfl | rfl <;>
      rcases hz' with rfl | rfl <;> tauto
  -- *"and every `Y`-complete vertex is adjacent to one of `f₁, f₂`"*, by 2.2.
  have h22 := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti W p₁ x hW hWY
    hodd hp₁Y hxY hnoedge
  -- *"Consequently there is no `Y`-complete vertex in `C` different from `p₁` with the same
  -- wheel-parity as `p₁`, a contradiction."*
  obtain ⟨w, hwC, hwY, hwne, hwπ⟩ :=
    exists_same_parity_yComplete (p := p₁) hBerge hw hπ2 hπ
  obtain ⟨z, hzint, hzadj⟩ := h22 w hwY
  rcases hcover z hzint with rfl | rfl
  · exact hwne (hnbr₁ w hwC hzadj.symm)
  · exact hnbrk w hwC hzadj.symm hwπ

end Workspace.ProofLemmas.OddWheelAttachmentYCount
