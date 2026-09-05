import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OddWheelParityFacts

/-!
# The first assertion of 16.1, from claim (1) of its proof

PAPER (16.1, printed p. 96): *"Then in every path of `C` between them there is a
`Y ∪ {v}`-complete edge."*  PAPER (proof, printed p. 96): *"From (1) the first assertion of the
  theorem follows."*

Claim (1) of that proof is:

> *"Let `P` be a path in `C` of length ≥ 1, such that its ends are adjacent to `v` and have
> opposite wheel-parity.  Then either some internal vertex of `P` is a neighbour of `v`, or `P`
> has length 1."*

`Claim1` below states it on **cyclic positions** of the rim, which is the form the printed
argument uses (*"let `C` have vertices `p₁, …, pₙ` in order, and let `P` be the path
`p₁-⋯-p_j`"*) and the form in which `SegmentBasics` / `WheelParity` supply their machinery.

The printed *"from (1) the first assertion follows"* is an induction on the length of the path,
made explicit here:

* if the path has length `1` its two ends are adjacent rim vertices of opposite wheel-parity, so
  the edge between them is `Y`-complete
  (`OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete`, contrapositively) and both ends
  are adjacent to `v`, i.e. the edge is `Y ∪ {v}`-complete;
* otherwise claim (1) hands back an internal neighbour `z` of `v`; wheel-parity is two-valued
  (`OddWheelParityFacts.exists_parity'`), so `z` has opposite wheel-parity to exactly one of the
  two ends, and the corresponding strictly shorter sub-arc satisfies the same hypotheses.

Nothing here corresponds to a numbered result of the paper: `first_assertion` is the first
conjunct of 16.1's conclusion, and `Claim1` is an internal step of its proof.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelSpan

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V} {v : V}

/-! ### Small bridges -/

theorem vertexComplete_union {u : V} :
    VertexComplete G u (Y ∪ {v}) ↔ (VertexComplete G u Y ∧ G.Adj u v) := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), h v (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact h2

theorem oppositeWheelParity_symm {x y : V} (h : OppositeWheelParity G C Y x y) :
    OppositeWheelParity G C Y y x :=
  ⟨h.1.symm, h.2.2.1, h.2.1, fun hs => h.2.2.2 (WheelParity.sameWheelParity_symm hs)⟩

/-! ### Claim (1) of the printed proof of 16.1 -/

/-- **Claim (1)** of the printed proof of 16.1, on cyclic positions of the rim:

> *"Let `P` be a path in `C` of length ≥ 1, such that its ends are adjacent to `v` and have
> opposite wheel-parity.  Then either some internal vertex of `P` is a neighbour of `v`, or `P`
> has length 1."*

Here the path is the arc running from cyclic position `k` to cyclic position `k + L`, so its
length is `L`, its ends are the vertices `x`, `y` at those two positions, and its internal
vertices sit at the positions `k + t` for `0 < t < L`.  *"is a neighbour of `v`"* is
`SegmentBasics.CycVert G {v} C`, since `VertexComplete G u {v}` unfolds to `G.Adj u v`. -/
def Claim1 (G : SimpleGraph V) (C : List V) (Y : Set V) (v : V) : Prop :=
  ∀ (k L : ℕ) (x y : V), 1 ≤ L → L + 2 ≤ C.length →
    C[k % C.length]? = some x → C[(k + L) % C.length]? = some y →
    G.Adj v x → G.Adj v y →
    (∀ t, 0 < t → t < L → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t)) →
    OppositeWheelParity G C Y x y →
    L = 1

/-! ### The induction -/

private theorem base_edge (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length))
    {k : ℕ} {x y : V}
    (hx : C[k % C.length]? = some x) (hy : C[(k + 1) % C.length]? = some y)
    (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hopp : OppositeWheelParity G C Y x y) :
    WheelParity.CycEdge G (Y ∪ {v}) C k := by
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  have hxe : (C[k % C.length]'(Nat.mod_lt _ hn)) = x := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hx
    exact Option.some_injective _ hx
  have hye : (C[(k + 1) % C.length]'(Nat.mod_lt _ hn)) = y := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hy
    exact Option.some_injective _ hy
  have hadj : G.Adj x y := by
    rw [← hxe, ← hye]
    exact YEdgeConfiguration.adj_of_succ_pos hC hn k
  have hxC : x ∈ C := hopp.2.1
  have hyC : y ∈ C := hopp.2.2.1
  have hxY : VertexComplete G x Y := by
    by_contra hcon
    exact hopp.2.2.2
      (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hxC hyC hadj hcon)
  have hyY : VertexComplete G y Y := by
    by_contra hcon
    exact hopp.2.2.2 (WheelParity.sameWheelParity_symm
      (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hyC hxC hadj.symm
        hcon))
  exact ⟨x, y, hx, hy, hadj, vertexComplete_union.mpr ⟨hxY, hvx.symm⟩,
    vertexComplete_union.mpr ⟨hyY, hvy.symm⟩⟩

private theorem exists_ext_edge_aux (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length))
    (hcl : Claim1 G C Y v)
    (π : V → ℕ) (hπ2 : ∀ z : V, π z < 2)
    (hπ : ∀ z w : V, z ∈ C → w ∈ C → z ≠ w →
      (SameWheelParity G C Y z w ↔ π z = π w)) :
    ∀ (d L k : ℕ) (x y : V), L ≤ d → 1 ≤ L → L + 2 ≤ C.length →
      C[k % C.length]? = some x → C[(k + L) % C.length]? = some y →
      G.Adj v x → G.Adj v y → OppositeWheelParity G C Y x y →
      ∃ t, t < L ∧ WheelParity.CycEdge G (Y ∪ {v}) C (k + t) := by
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  intro d
  induction d with
  | zero => intro L k x y hd hL1 _ _ _ _ _ _; omega
  | succ d ih =>
      intro L k x y hd hL1 hLn hx hy hvx hvy hopp
      by_cases hnb : ∀ t, 0 < t → t < L → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t)
      · have hL : L = 1 := hcl k L x y hL1 hLn hx hy hvx hvy hnb hopp
        subst hL
        exact ⟨0, by omega, base_edge hC heven hx hy hvx hvy hopp⟩
      · push Not at hnb
        obtain ⟨t, ht0, htL, hcv⟩ := hnb
        obtain ⟨z, hzget, hzc⟩ := hcv
        have hvz : G.Adj v z := (hzc v rfl).symm
        have hzC : z ∈ C := SegmentBasics.mem_of_pos hn hzget
        have hxC : x ∈ C := hopp.2.1
        have hyC : y ∈ C := hopp.2.2.1
        have hzx : z ≠ x := by
          rintro rfl
          have hpu := SegmentBasics.pos_unique hC hzget hx
          have h1 : (k + t) % C.length = (k + 0) % C.length := by
            rw [Nat.add_zero]; exact hpu
          have hcancel : t % C.length = 0 % C.length := Nat.ModEq.add_left_cancel' k h1
          rw [Nat.mod_eq_of_lt (show t < C.length by omega), Nat.zero_mod] at hcancel
          omega
        have hzy : z ≠ y := by
          rintro rfl
          have hpu := SegmentBasics.pos_unique hC hzget hy
          have hcancel : t % C.length = L % C.length := Nat.ModEq.add_left_cancel' k hpu
          rw [Nat.mod_eq_of_lt (show t < C.length by omega),
            Nat.mod_eq_of_lt (show L < C.length by omega)] at hcancel
          omega
        have hpxy : π x ≠ π y := fun he => hopp.2.2.2 ((hπ x y hxC hyC hopp.1).mpr he)
        rcases (show π z ≠ π x ∨ π z ≠ π y by omega) with hcase | hcase
        · have hoppxz : OppositeWheelParity G C Y x z :=
            ⟨fun he => hzx he.symm, hxC, hzC,
              fun hs => hcase (((hπ x z hxC hzC (fun he => hzx he.symm)).mp hs).symm)⟩
          obtain ⟨s, hs, hce⟩ :=
            ih t k x z (by omega) (by omega) (by omega) hx hzget hvx hvz hoppxz
          exact ⟨s, by omega, hce⟩
        · have hoppzy : OppositeWheelParity G C Y z y :=
            ⟨hzy, hzC, hyC, fun hs => hcase ((hπ z y hzC hyC hzy).mp hs)⟩
          obtain ⟨s, hs, hce⟩ :=
            ih (L - t) (k + t) z y (by omega) (by omega) (by omega) hzget
              (by rw [show k + t + (L - t) = k + L from by omega]; exact hy) hvz hvy hoppzy
          exact ⟨t + s, by omega, by rw [show k + (t + s) = k + t + s from by omega]; exact hce⟩

/-- The first assertion of 16.1, on cyclic positions: an arc of the rim whose two ends are
neighbours of `v` of opposite wheel-parity carries a `Y ∪ {v}`-complete edge. -/
theorem exists_ext_edge (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length))
    (hcl : Claim1 G C Y v)
    {L k : ℕ} {x y : V} (hL1 : 1 ≤ L) (hLn : L + 2 ≤ C.length)
    (hx : C[k % C.length]? = some x) (hy : C[(k + L) % C.length]? = some y)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hopp : OppositeWheelParity G C Y x y) :
    ∃ t, t < L ∧ WheelParity.CycEdge G (Y ∪ {v}) C (k + t) := by
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  exact exists_ext_edge_aux hC heven hcl π hπ2 hπ L L k x y le_rfl hL1 hLn hx hy hvx hvy hopp

/-! ### The list form -/

private theorem core_edge (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length))
    (hcl : Claim1 G C Y v)
    {Q : List V} {u w : V} {k : ℕ} (hQpath : IsPathList G Q) (hpre : Q <+: C.rotate k)
    (hQfrom : IsPathFrom G Q u w) (hvu : G.Adj v u) (hvw : G.Adj v w)
    (hopp : OppositeWheelParity G C Y u w) :
    ∃ x ∈ Q, ∃ y ∈ Q, EdgeComplete G (Y ∪ {v}) x y := by
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  have hQlen : Q.length + 1 ≤ C.length := SegmentBasics.length_le_of_path_prefix hC hQpath hpre
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQpath
  have hQ2 : 2 ≤ Q.length := by
    by_contra hcon
    have h1 : Q.length = 1 := by omega
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp h1
    have e1 : z = u := by have hh := hQfrom.2.1; rw [hz] at hh; simpa using hh
    have e2 : z = w := by have hh := hQfrom.2.2; rw [hz] at hh; simpa using hh
    exact hopp.1 (e1.symm.trans e2)
  have hget : ∀ (i : ℕ) (hi : i < Q.length), C[(k + i) % C.length]? = some (Q[i]'hi) :=
    fun i hi => SegmentBasics.prefix_pos hn hpre hi
  have hu0 : (Q[0]'hQpos) = u := PathBasics.getElem_zero_of_head? hQfrom.2.1 hQpos
  have hwl : (Q[Q.length - 1]'(by omega)) = w :=
    PathBasics.getElem_last_of_getLast? hQfrom.2.2 hQpos
  have hxk : C[k % C.length]? = some u := by
    have hh := hget 0 hQpos
    rw [hu0] at hh
    simpa using hh
  have hyk : C[(k + (Q.length - 1)) % C.length]? = some w := by
    have hh := hget (Q.length - 1) (by omega)
    rw [hwl] at hh
    exact hh
  obtain ⟨t, ht, hce⟩ := exists_ext_edge hC heven hcl (L := Q.length - 1) (k := k)
    (by omega) (by omega) hxk hyk hvu hvw hopp
  obtain ⟨x, y, hx1, hy1, hE⟩ := hce
  have htlt : t < Q.length := by omega
  have ht1lt : t + 1 < Q.length := by omega
  have hxq : x = (Q[t]'htlt) := by
    have hh := hget t htlt
    exact Option.some_injective _ (hx1.symm.trans hh)
  have hyq : y = (Q[t + 1]'ht1lt) := by
    have hh := hget (t + 1) ht1lt
    exact Option.some_injective _ (hy1.symm.trans hh)
  exact ⟨x, by rw [hxq]; exact List.getElem_mem _, y, by rw [hyq]; exact List.getElem_mem _, hE⟩

/-- **The first assertion of 16.1.**

PAPER: *"Then in every path of `C` between them there is a `Y ∪ {v}`-complete edge."* -/
theorem first_assertion [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V}
    (hcl : Claim1 G C Y v) {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b) :
    ∀ P : List V, IsPathList G P →
      (∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k) →
      (IsPathFrom G P a b ∨ IsPathFrom G P b a) →
      ∃ x ∈ P, ∃ y ∈ P, EdgeComplete G (Y ∪ {v}) x y := by
  have hC : IsHoleList G C := hw.1.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  have hba : OppositeWheelParity G C Y b a := oppositeWheelParity_symm hab
  intro P hPpath harc hends
  obtain ⟨k, hk⟩ := harc
  rcases hk with hk | hk
  · rcases hends with h | h
    · exact core_edge hC heven hcl hPpath hk h hva hvb hab
    · exact core_edge hC heven hcl hPpath hk h hvb hva hba
  · have hRpath : IsPathList G P.reverse := PathBasics.isPathList_reverse hPpath
    have hmem : ∀ z : V, z ∈ P.reverse → z ∈ P := fun z hz => List.mem_reverse.mp hz
    rcases hends with h | h
    · obtain ⟨x, hx, y, hy, hE⟩ :=
        core_edge hC heven hcl hRpath hk (PathBasics.isPathFrom_reverse h) hvb hva hba
      exact ⟨x, hmem x hx, y, hmem y hy, hE⟩
    · obtain ⟨x, hx, y, hy, hE⟩ :=
        core_edge hC heven hcl hRpath hk (PathBasics.isPathFrom_reverse h) hva hvb hab
      exact ⟨x, hmem x hx, y, hmem y hy, hE⟩

end Workspace.ProofLemmas.OddWheelSpan
