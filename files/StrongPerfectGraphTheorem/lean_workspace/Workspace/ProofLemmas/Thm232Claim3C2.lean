import Workspace.ProofLemmas.Thm232Claim3C2Core
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.Statements.S02.Thm_2_3

/-!
# 23.2, claim (3): `y` is not adjacent to `c₂`

PAPER (23.2, claim (3), printed pp. 139–140):

> *"Next suppose that `y` is adjacent to `c₂`.  From the symmetry we may assume that
> `x₀ ≠ c₃`.  Let `Q` be the path of `C \ z` between `x₀, c₃`; so `Q` has length `> 0`, and
> even length by 2.3.  Since `x₀-Q-c₃-c₂-y-x₀` is not an odd hole, it follows that `y` is not
> adjacent to `x₀`.  But then the hole `x₀-Q-c₃-c₂-y-z-x₀` is the rim of an odd wheel with
> hub `Y`, contrary to `G ∈ F₈`.  So `y` is not adjacent to `c₂`."*

`orientation_absurd` is the printed argument for one arc of `C \ z`.  The symmetry
*"we may assume that `x₀ ≠ c₃`"* is discharged by `not_adj_c2`, which runs it on the arc from
`c₃` to `x₀` when `x₀ ≠ c₃`, and otherwise on the arc from `c₁` to `x₁` — one of the two must be
available, because `x₀ = c₃` and `x₁ = c₁` together would make `C` a four-cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232Claim3C2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A cyclic index below the length of the cycle is its own residue, and the length itself
has residue `0`. -/
theorem mod_le_self {n m : ℕ} (hn : 0 < n) (h : m ≤ n) : m % n = if m = n then 0 else m := by
  by_cases he : m = n
  · simp [he]
  · rw [if_neg he, Nat.mod_eq_of_lt (by omega)]

/-- The vertices of the cyclic arc of `C` that starts at position `m` and has `L` vertices. -/
theorem mem_rotate_take {C : List V} (hn : 0 < C.length) {m L : ℕ} (hL : L ≤ C.length)
    {v : V} :
    v ∈ (C.rotate m).take L ↔
      ∃ t, t < L ∧ v = C[(m + t) % C.length]'(Nat.mod_lt _ hn) := by
  have hlen : ((C.rotate m).take L).length = L := by
    simp only [List.length_take, List.length_rotate]; omega
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, by omega, ?_⟩
    rw [← htv]
    have h1 : ((C.rotate m).take L)[t]'ht = (C.rotate m)[t]'(by simp; omega) := by
      simp only [List.getElem_take]
    rw [h1, WheelParity.getElem_rotate_eq hn]
    congr 1
    rw [Nat.add_comm]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, by omega, ?_⟩
    have h1 : ((C.rotate m).take L)[t]'(by omega) = (C.rotate m)[t]'(by simp; omega) := by
      simp only [List.getElem_take]
    rw [h1, WheelParity.getElem_rotate_eq hn]
    congr 1
    rw [Nat.add_comm]

/-- Two cyclic positions of a hole carry different vertices when their residues differ. -/
theorem pos_ne {C : List V} (hnd : C.Nodup) (hn : 0 < C.length) (k i j : ℕ)
    (h : i % C.length ≠ j % C.length) :
    C[(k + i) % C.length]'(Nat.mod_lt _ hn) ≠ C[(k + j) % C.length]'(Nat.mod_lt _ hn) := by
  intro he
  apply h
  have hmod : (k + i) % C.length = (k + j) % C.length := hnd.getElem_inj_iff.mp he
  exact Nat.ModEq.add_left_cancel' k hmod


/-- Reading a vertex of a prefix of a rotation off the original cycle. -/
theorem prefix_getElem {C L : List V} (hn : 0 < C.length) {m i j : ℕ}
    (hpre : L <+: C.rotate m) (hi : i < L.length) (hj : j = m + i) :
    L[i]'hi = C[j % C.length]'(Nat.mod_lt _ hn) := by
  have hle := hpre.length_le
  have hiR : i < (C.rotate m).length := by simp only [List.length_rotate]; simp at hle; omega
  rw [hpre.getElem hi]
  simp only [List.getElem_rotate]
  congr 1
  subst hj
  congr 1
  omega

/-- A cyclic position outside the index range of an arc is not a vertex of that arc. -/
theorem not_mem_arc {C : List V} (hnd : C.Nodup) (hn : 0 < C.length) (k lo hi m : ℕ)
    (hlohi : lo ≤ hi) (hle : hi - lo + 1 ≤ C.length)
    (hne : ∀ j, lo ≤ j → j ≤ hi → m % C.length ≠ j % C.length) :
    C[(k + m) % C.length]'(Nat.mod_lt _ hn) ∉ (C.rotate (k + lo)).take (hi - lo + 1) := by
  intro hmem
  obtain ⟨t, ht, htv⟩ := (mem_rotate_take hn hle).mp hmem
  have heq : k + lo + t = k + (lo + t) := by omega
  rw [heq] at htv
  exact pos_ne hnd hn k m (lo + t) (hne (lo + t) (by omega) (by omega)) htv

/-- **PAPER (2.3)** applied to an arc of the rim that carries no `Y`-complete edge: the arc has
even length, because some `Y`-complete rim vertex lies outside it. -/
theorem arc_even {C : List V} {Y : Set V} (hBerge : Berge G) (hC : IsHoleList G C)
    (hCY : ∀ v ∈ C, v ∉ Y) (hYanti : AnticonnectedSet G Y)
    (A : List V) (m : ℕ) (hpre : A <+: C.rotate m)
    (u v : V) (hA : IsPathFrom G A u v)
    (huC : VertexComplete G u Y) (hvC : VertexComplete G v Y)
    (w : V) (hwC : w ∈ C) (hwY : VertexComplete G w Y) (hwu : w ≠ u) (hwv : w ≠ v)
    (hempty : ∀ p ∈ A, ∀ q ∈ A, ¬ EdgeComplete G Y p q) :
    Even (pathLength A) := by
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti C
    (Or.inr hC) hCY).1 A u v (Or.inr ⟨hC, ⟨m, hpre⟩⟩) hA huC hvC
  rcases h23 with h | h
  · have hz : {e : Sym2 V | ∃ p ∈ A, ∃ q ∈ A, e = s(p, q) ∧ EdgeComplete G Y p q} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨p, hp, q, hq, -, hE⟩
      exact hempty p hp q hq hE
    rw [hz, Set.ncard_empty] at h
    exact Nat.even_iff.mpr h.symm
  · exact absurd (h w hwC hwY) (by rintro (he | he) <;> [exact hwu he; exact hwv he])

/-- **PAPER (23.2, claim (3), printed pp. 139–140), the argument for one arc of `C \ z`.**

`a, z, b` are consecutive on the rim and `f, c₂, e` are consecutive, with the arc `Q` of
`C \ z` running from `f` to `a`.  In the printed orientation `(a,b,e,f) = (x₀,x₁,c₁,c₃)`; the
other orientation is `(x₁,x₀,c₃,c₁)`. -/
theorem orientation_absurd (hG : InF8 G) (C : List V) (Y : Set V)
    (hCY : ∀ v ∈ C, v ∉ Y) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (a z b e c₂ f y : V) (Q : List V)
    (hQ : IsPathFrom G Q f a) (hQsub : ∀ v ∈ Q, v ∈ C)
    (hQeven : Even (pathLength Q)) (hQpos : 0 < pathLength Q)
    (hzQ : z ∉ Q) (hbQ : b ∉ Q) (heQ : e ∉ Q) (hc2Q : c₂ ∉ Q)
    (hnb : IsRimNeighbours G C z a b) (hnbc : IsRimNeighbours G C c₂ f e)
    (hae : a ≠ e) (haf : a ≠ f) (hc2b : c₂ ≠ b) (hzc2 : z ≠ c₂)
    (hzmem : z ∈ C) (hc2mem : c₂ ∈ C)
    (haC : VertexComplete G a Y) (hzC : VertexComplete G z Y)
    (hc2C : VertexComplete G c₂ Y) (hfC : VertexComplete G f Y)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {a, z} ∨ ({u, v} : Set V) = {z, b} ∨
      ({u, v} : Set V) = {e, c₂} ∨ ({u, v} : Set V) = {c₂, f})
    (hnone : ∀ c : V, c ∈ C → c ≠ z → c ≠ a → c ≠ b → c ≠ c₂ → ¬ G.Adj y c)
    (hyz : G.Adj y z) (hyC : y ∉ C) (hyY : y ∉ Y) (hyNC : ¬ VertexComplete G y Y)
    (hyc2 : G.Adj y c₂) :
    False := by
  have haQ : a ∈ Q := getLast_mem hQ.2.2
  have hfQ : f ∈ Q := head_mem hQ.2.1
  have hQ2 : 2 ≤ pathLength Q := by
    obtain ⟨r, hr⟩ := hQeven
    omega
  have hQY : ∀ v ∈ Q, v ∉ Y := fun v hv => hCY v (hQsub v hv)
  have hyQ : y ∉ Q := fun h => hyC (hQsub y h)
  have hac2 : a ≠ c₂ := fun h => hc2Q (h ▸ haQ)
  have haz : a ≠ z := fun h => hzQ (h ▸ haQ)
  have hab : a ≠ b := hnb.1
  have hzadj : ∀ v ∈ Q, (G.Adj z v ↔ v = a) := by
    intro v hv
    constructor
    · intro h
      rcases hnb.2.2.2.2.2 v (hQsub v hv) h with h' | h'
      · exact h'
      · exact absurd (h' ▸ hv) hbQ
    · rintro rfl
      exact hnb.2.2.2.1
  have hc2adj : ∀ v ∈ Q, (G.Adj c₂ v ↔ v = f) := by
    intro v hv
    constructor
    · intro h
      rcases hnbc.2.2.2.2.2 v (hQsub v hv) h with h' | h'
      · exact h'
      · exact absurd (h' ▸ hv) heQ
    · rintro rfl
      exact hnbc.2.2.2.1
  have hnbrNC : ∀ v ∈ Q, G.Adj a v → ¬ VertexComplete G v Y := by
    intro v hv hadj hvC
    have hE : EdgeComplete G Y a v := ⟨hadj, haC, hvC⟩
    have hcases := hexh a v (hQsub a haQ) (hQsub v hv) hE
    have hz : z ∉ Q := hzQ
    rcases hcases with h | h | h | h <;>
      rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hzQ (h2 ▸ hv)
    · exact haz h1
    · exact haz h1
    · exact hab h1
    · exact hae h1
    · exact hac2 h1
    · exact hac2 h1
    · exact haf h1
  have hnay : ¬ G.Adj a y := by
    have := Thm232Claim3C2Core.no_adj_far_end hG.1.1.1.1.1 Q f a y c₂ hQ hQeven hQ2
      hyQ hc2Q hyc2 ?_ hc2adj
    · exact fun h => this h.symm
    · intro v hv hva hadj
      exact hnone v (hQsub v hv) (fun he => hzQ (he ▸ hv)) hva
        (fun he => hbQ (he ▸ hv)) (fun he => hc2Q (he ▸ hv)) hadj
  have hyadj : ∀ v ∈ Q, ¬ G.Adj y v := by
    intro v hv hadj
    by_cases hva : v = a
    · exact hnay (hva ▸ hadj.symm)
    · exact hnone v (hQsub v hv) (fun he => hzQ (he ▸ hv)) hva
        (fun he => hbQ (he ▸ hv)) (fun he => hc2Q (he ▸ hv)) hadj
  have hnac2 : ¬ G.Adj a c₂ := by
    intro h
    rcases hnbc.2.2.2.2.2 a (hQsub a haQ) h.symm with h' | h'
    · exact haf h'
    · exact hae h'
  have hnzc2 : ¬ G.Adj z c₂ := by
    intro h
    rcases hnb.2.2.2.2.2 c₂ hc2mem h with h' | h'
    · exact hac2 h'.symm
    · exact hc2b h'
  exact Thm232Claim3C2Core.odd_wheel_absurd hG Y hYne hYanti Q f a z y c₂ hQ hQ2 hQY
    hzQ hyQ hc2Q hyY (hCY z hzmem) (hCY c₂ hc2mem)
    hnb.2.2.2.1.symm hyz.symm hyc2 (fun h => hnay h) hnac2 hnzc2 hzc2
    hzadj hc2adj hyadj haC hzC hc2C hfC hyNC hnbrNC


/-- **PAPER (23.2, claim (3), printed pp. 139–140):** *"So `y` is not adjacent to `c₂`."*

The hypotheses are the ones the printed proof has in hand: the optimal wheel, the configuration
`x₀,z,x₁,c₁,c₂,c₃` of the four `Y`-complete rim edges (claim (1)), the neighbour `y` of `z` on
the path `T`, which is an interior vertex of `T` and so is neither in `Y` nor `Y`-complete, and
the first half of claim (3), that `y` has no neighbour in `A₀ \ {c₂}`. -/
theorem not_adj_c2 (hG : InF8 G) (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ y : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k) (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁) (hnbc : IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (hyz : G.Adj y z) (hyC : y ∉ C) (hyY : y ∉ Y) (hyNC : ¬ VertexComplete G y Y)
    (hnone : ∀ c : V, c ∈ C → c ≠ z → c ≠ x₀ → c ≠ x₁ → c ≠ c₂ → ¬ G.Adj y c) :
    ¬ G.Adj y c₂ := by
  intro hyc2
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hCY : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2
  have hYne : Y.Nonempty := hw.2.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have hBerge : Berge G := hG.1.1.1.1.1
  obtain ⟨hx0C, hzC, hx1C, -⟩ := hole_triple hC ⟨k, hpre1⟩
  obtain ⟨hc1C, hc2C, hc3C, -⟩ := hole_triple hC ⟨k + d, hpre2⟩
  have p0 : C[(k + 0) % C.length]'(Nat.mod_lt _ hn) = x₀ :=
    (prefix_getElem hn hpre1 (i := 0) (j := k + 0) (by simp) rfl).symm
  have p1 : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z :=
    (prefix_getElem hn hpre1 (i := 1) (j := k + 1) (by simp) rfl).symm
  have p2 : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ :=
    (prefix_getElem hn hpre1 (i := 2) (j := k + 2) (by simp) rfl).symm
  have pd : C[(k + d) % C.length]'(Nat.mod_lt _ hn) = c₁ :=
    (prefix_getElem hn hpre2 (i := 0) (j := k + d) (by simp) (by omega)).symm
  have pd1 : C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) = c₂ :=
    (prefix_getElem hn hpre2 (i := 1) (j := k + (d + 1)) (by simp) (by omega)).symm
  have pd2 : C[(k + (d + 2)) % C.length]'(Nat.mod_lt _ hn) = c₃ :=
    (prefix_getElem hn hpre2 (i := 2) (j := k + (d + 2)) (by simp) (by omega)).symm
  have hzc2 : z ≠ c₂ := by
    rw [← p1, ← pd1]
    exact pos_ne hC.2.1 hn k 1 (d + 1)
      (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]; split_ifs <;> omega)
  by_cases hx0c3 : x₀ = c₃
  · -- `x₀ = c₃`: run the argument on the arc from `c₁` to `x₁`.
    have hmod : (k + 0) % C.length = (k + (d + 2)) % C.length :=
      hC.2.1.getElem_inj_iff.mp (p0.trans (hx0c3.trans pd2.symm))
    have h0 : 0 % C.length = (d + 2) % C.length := Nat.ModEq.add_left_cancel' k hmod
    have hde : d + 2 = C.length := by
      rw [Nat.zero_mod, mod_le_self hn (by omega)] at h0
      split_ifs at h0 <;> omega
    have hd3 : 3 ≤ d := by omega
    set A0 : List V := (C.rotate (k + 2)).take (d - 2 + 1) with hA0def
    have hA0len : A0.length = d - 2 + 1 := by
      simp only [hA0def, List.length_take, List.length_rotate]; omega
    have hA0sub : ∀ v ∈ A0, v ∈ C := fun v hv =>
      List.mem_rotate.mp (List.mem_of_mem_take hv)
    have hA0from : IsPathFrom G A0 x₁ c₁ := by
      have h := WheelParity.arc_isPathFrom (G := G) (C := C) hC
        (k := k + 2) (L := d - 2 + 1) (p := (k + 2) % C.length)
        (q := (k + d) % C.length) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
        (by omega) (by omega) rfl
        (by
          have he : k + 2 + (d - 2 + 1) - 1 = k + d := by omega
          rw [he])
      rw [p2, pd] at h
      exact h
    have hnotmem : ∀ m : ℕ, (∀ j, 2 ≤ j → j ≤ d → m % C.length ≠ j % C.length) →
        C[(k + m) % C.length]'(Nat.mod_lt _ hn) ∉ A0 := by
      intro m hm
      have := not_mem_arc (C := C) hC.2.1 hn k 2 d m (by omega) (by omega) hm
      rw [show d - 2 + 1 = d - 2 + 1 from rfl] at this
      exact this
    have hzA : z ∉ A0 := by
      rw [← p1]
      exact hnotmem 1 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hx0A : x₀ ∉ A0 := by
      rw [← p0]
      exact hnotmem 0 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc3A : c₃ ∉ A0 := by
      rw [← pd2]
      exact hnotmem (d + 2) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc2A : c₂ ∉ A0 := by
      rw [← pd1]
      exact hnotmem (d + 1) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hempty : ∀ p ∈ A0, ∀ q ∈ A0, ¬ EdgeComplete G Y p q := by
      intro p hp q hq hE
      rcases hexh p q (hA0sub p hp) (hA0sub q hq) hE with h | h | h | h <;>
        rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hzA (h2 ▸ hq)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h2 ▸ hq)
      · exact hc2A (h2 ▸ hq)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h2 ▸ hq)
    have hA0even : Even (pathLength A0) :=
      arc_even hBerge hC hCY hYanti A0 (k + 2) (List.take_prefix _ _) x₁ c₁ hA0from
        h1Y hc1Y z hzC hzY (fun he => hzA (he ▸ head_mem hA0from.2.1))
        (fun he => hzA (he ▸ getLast_mem hA0from.2.2)) hempty
    have hQ : IsPathFrom G A0.reverse c₁ x₁ := isPathFrom_reverse hA0from
    refine orientation_absurd hG C Y hCY hYne hYanti x₁ z x₀ c₃ c₂ c₁ y A0.reverse hQ
      (fun v hv => hA0sub v (List.mem_reverse.mp hv)) ?_ ?_
      (fun h => hzA (List.mem_reverse.mp h)) (fun h => hx0A (List.mem_reverse.mp h))
      (fun h => hc3A (List.mem_reverse.mp h)) (fun h => hc2A (List.mem_reverse.mp h))
      (isRimNeighbours_symm hnb) hnbc ?_ ?_ ?_ hzc2 hzC hc2C h1Y hzY hc2Y hc1Y ?_ ?_
      hyz hyC hyY hyNC hyc2
    · rwa [pathLength_reverse]
    · rw [pathLength_reverse, PathBasics.pathLength_eq, hA0len]; omega
    · exact fun he => hc3A (he ▸ head_mem hA0from.2.1)
    · rw [← p2, ← pd]
      exact pos_ne hC.2.1 hn k 2 d
        (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]; split_ifs <;> omega)
    · rw [← pd1, ← p0]
      exact pos_ne hC.2.1 hn k (d + 1) 0
        (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]; split_ifs <;> omega)
    · intro u v huC hvC hE
      rcases hexh u v huC hvC hE with h | h | h | h
      · exact Or.inr (Or.inl (h.trans (Set.pair_comm x₀ z)))
      · exact Or.inl (h.trans (Set.pair_comm z x₁))
      · exact Or.inr (Or.inr (Or.inr (h.trans (Set.pair_comm c₁ c₂))))
      · exact Or.inr (Or.inr (Or.inl (h.trans (Set.pair_comm c₂ c₃))))
    · intro c hcC hcz hc1' hc0' hcc2
      exact hnone c hcC hcz hc0' hc1' hcc2
  · -- `x₀ ≠ c₃`: the printed orientation.
    have hlt : d + 2 < C.length := by
      rcases Nat.lt_or_ge (d + 2) C.length with h | h
      · exact h
      · exfalso
        have hde : d + 2 = C.length := by omega
        refine hx0c3 ?_
        rw [← p0, ← pd2]
        exact hC.2.1.getElem_inj_iff.mpr (by rw [hde]; simp)
    set A0 : List V := (C.rotate (k + (d + 2))).take (C.length - (d + 2) + 1) with hA0def
    have hA0len : A0.length = C.length - (d + 2) + 1 := by
      simp only [hA0def, List.length_take, List.length_rotate]; omega
    have hA0sub : ∀ v ∈ A0, v ∈ C := fun v hv =>
      List.mem_rotate.mp (List.mem_of_mem_take hv)
    have hA0from : IsPathFrom G A0 c₃ x₀ := by
      have h := WheelParity.arc_isPathFrom (G := G) (C := C) hC
        (k := k + (d + 2)) (L := C.length - (d + 2) + 1)
        (p := (k + (d + 2)) % C.length) (q := (k + 0) % C.length)
        (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by omega) (by omega) rfl
        (by
          have he : k + (d + 2) + (C.length - (d + 2) + 1) - 1 = k + C.length := by omega
          rw [he]
          simp)
      rw [pd2, p0] at h
      exact h
    have hnotmem : ∀ m : ℕ,
        (∀ j, d + 2 ≤ j → j ≤ C.length → m % C.length ≠ j % C.length) →
        C[(k + m) % C.length]'(Nat.mod_lt _ hn) ∉ A0 :=
      fun m hm => not_mem_arc (C := C) hC.2.1 hn k (d + 2) C.length m (by omega) (by omega) hm
    have hzA : z ∉ A0 := by
      rw [← p1]
      exact hnotmem 1 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hx1A : x₁ ∉ A0 := by
      rw [← p2]
      exact hnotmem 2 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc1A : c₁ ∉ A0 := by
      rw [← pd]
      exact hnotmem d (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc2A : c₂ ∉ A0 := by
      rw [← pd1]
      exact hnotmem (d + 1) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hempty : ∀ p ∈ A0, ∀ q ∈ A0, ¬ EdgeComplete G Y p q := by
      intro p hp q hq hE
      rcases hexh p q (hA0sub p hp) (hA0sub q hq) hE with h | h | h | h <;>
        rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hzA (h2 ▸ hq)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h2 ▸ hq)
      · exact hc2A (h2 ▸ hq)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h2 ▸ hq)
    have hA0even : Even (pathLength A0) :=
      arc_even hBerge hC hCY hYanti A0 (k + (d + 2)) (List.take_prefix _ _) c₃ x₀ hA0from
        hc3Y h0Y z hzC hzY (fun he => hzA (he ▸ head_mem hA0from.2.1))
        (fun he => hzA (he ▸ getLast_mem hA0from.2.2)) hempty
    refine orientation_absurd hG C Y hCY hYne hYanti x₀ z x₁ c₁ c₂ c₃ y A0 hA0from
      hA0sub hA0even ?_ hzA hx1A hc1A hc2A hnb (isRimNeighbours_symm hnbc) ?_ hx0c3 ?_ hzc2
      hzC hc2C h0Y hzY hc2Y hc3Y hexh hnone hyz hyC hyY hyNC hyc2
    · rw [PathBasics.pathLength_eq, hA0len]; omega
    · exact fun he => hc1A (he ▸ getLast_mem hA0from.2.2)
    · rw [← pd1, ← p2]
      exact pos_ne hC.2.1 hn k (d + 1) 2
        (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]; split_ifs <;> omega)

end Workspace.ProofLemmas.Thm232Claim3C2
