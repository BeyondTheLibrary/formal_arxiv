import Workspace.ProofLemmas.Thm232Claim4Antipath
import Workspace.ProofLemmas.Thm232Claim4Neighbours
import Workspace.ProofLemmas.Thm232Claim3C2

/-!
# 23.2, claim (4), the argument for one arc of `C \ z`

PAPER (23.2, claim (4), printed p. 140):

> *"For otherwise we may assume `v₂` is `Y`-complete.  From the symmetry we may assume that
> `x₀ ≠ c₃`.  Let `Q` be the path of `C \ z` between `x₀, c₃`; so `Q` has length `> 0`, and even
> length by 2.3.  Since `y, v₁` are not `Y`-complete, there is an antipath joining them with
> interior in `Y`, and it is odd since it can be completed to an antihole via `v₁-z-v₂-y`.
> Hence every `Y`-complete vertex is adjacent to one of `y, v₁`, and since `c₂, c₃` are
> `Y`-complete and not adjacent to `y` by (3), it follows that `v₁` is adjacent to `c₂, c₃`.
> By (2), `v₁` is adjacent to one of `x₀, x₁`, and so it has two nonadjacent neighbours in `C`,
> and two neighbours in `C` of opposite wheel-parity.  By 16.1, there are three consecutive
> vertices in `C`, all `Y`-complete and adjacent to `v₁`.  By 22.3, `v₁` has no other neighbours
> in `C`.  Hence `x₁ = c₁` and the neighbours of `v₁` in `C` are `c₁, c₂, c₃`.  Consequently
> `x₀` is adjacent to `y`; but then `x₀-Q-c₃-v₁-y-x₀` is an odd hole, a contradiction."*

`orientation_absurd` is that argument, stated for an abstract arc `Q` of `C \ z`, so that the
printed *"from the symmetry we may assume that `x₀ ≠ c₃`"* can be discharged by applying it
either to the arc from `c₃` to `x₀` or to the arc from `c₁` to `x₁` — exactly as
`Thm232Claim3C2.not_adj_c2` does for claim (3).  In the printed orientation
`(a, z, b, e, c₂, f) = (x₀, z, x₁, c₁, c₂, c₃)`.

The Lean route does not need the printed appeal to (2): the outcomes of 16.1 already give that
every rim neighbour of `v₁` is one of `e, c₂, f` (`Thm232Claim4Neighbours.nbrs_subset`), so `a`
is not one of them, and *"consequently `x₀` is adjacent to `y`"* follows.  The closing odd hole
`a-Q-f-v₁-y-a` is the one built for claim (3) by
`Thm232Claim3C2Core.no_adj_far_end`, with `v₁` in the place of `c₂` there.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232Claim4Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **PAPER (23.2, claim (4), printed p. 140), the argument for one arc of `C \ z`.**

`a, z, b` are consecutive on the rim and `f, c₂, e` are consecutive, with the arc `Q` of
`C \ z` running from `f` to `a`; `y-v₁` are the second and third vertices of the path `T`, and
`u` is the paper's `v₂`, the neighbour of `v₁` in `A₀` assumed `Y`-complete.  In the printed
orientation `(a, z, b, e, c₂, f) = (x₀, z, x₁, c₁, c₂, c₃)`; the other one is
`(x₁, z, x₀, c₃, c₂, c₁)`. -/
theorem orientation_absurd (hG : InF8 G) (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (a z b e c₂ f y v₁ u : V) (Q : List V)
    (hQ : IsPathFrom G Q f a) (hQsub : ∀ w ∈ Q, w ∈ C)
    (hQeven : Even (pathLength Q)) (hQpos : 0 < pathLength Q)
    (hzQ : z ∉ Q) (hbQ : b ∉ Q) (heQ : e ∉ Q) (hc2Q : c₂ ∉ Q)
    (hzmem : z ∈ C) (hc2mem : c₂ ∈ C)
    (hnb : IsRimNeighbours G C z a b) (hnbc : IsRimNeighbours G C c₂ f e)
    (hae : a ≠ e) (haf : a ≠ f) (hac2 : a ≠ c₂)
    (hze : z ≠ e) (hzf : z ≠ f) (hzc2 : z ≠ c₂)
    (hbf : b ≠ f) (hbc2 : b ≠ c₂)
    (haY : VertexComplete G a Y) (hzY : VertexComplete G z Y)
    (hc2Y : VertexComplete G c₂ Y) (hfY : VertexComplete G f Y)
    (hexh : ∀ p q : V, p ∈ C → q ∈ C → EdgeComplete G Y p q →
      ({p, q} : Set V) = {a, z} ∨ ({p, q} : Set V) = {z, b} ∨
      ({p, q} : Set V) = {e, c₂} ∨ ({p, q} : Set V) = {c₂, f})
    (hyC : y ∉ C) (hvC : v₁ ∉ C)
    (hyY : y ∉ Y) (hvY : v₁ ∉ Y)
    (hyNC : ¬ VertexComplete G y Y) (hvNC : ¬ VertexComplete G v₁ Y)
    (hzy : G.Adj z y) (hyv : G.Adj y v₁) (hzv : ¬ G.Adj z v₁)
    (huC : u ∈ C) (huz : u ≠ z) (hua : u ≠ a) (hub : u ≠ b)
    (huY : VertexComplete G u Y) (hvu : G.Adj v₁ u)
    (hyanti : ∀ c ∈ C, c ≠ z → c ≠ a → c ≠ b → ¬ G.Adj y c) :
    False := by
  have hCY : ∀ w ∈ C, w ∉ Y := hopt.1.2.1.2.2
  have hYanti : AnticonnectedSet G Y := hopt.1.2.1.2.1
  have hBerge : Berge G := hG.1.1.1.1.1
  have hfQ : f ∈ Q := head_mem hQ.2.1
  have haQ : a ∈ Q := getLast_mem hQ.2.2
  have hfC : f ∈ C := hnbc.2.1
  have hc2f : G.Adj c₂ f := hnbc.2.2.2.1
  have hQ2 : 2 ≤ pathLength Q := by
    obtain ⟨r, hr⟩ := hQeven
    omega
  -- the hypotheses of the antihole `y-Q'-v₁-z-u-y`
  have hzu : ¬ G.Adj z u := by
    intro h
    rcases hnb.2.2.2.2.2 u huC h with h' | h'
    · exact hua h'
    · exact hub h'
  have huy : ¬ G.Adj u y := fun h => hyanti u huC huz hua hub h.symm
  have hzune : z ≠ u := fun h => huz h.symm
  have hzvne : z ≠ v₁ := fun h => hvC (h ▸ hzmem)
  have huyne : u ≠ y := fun h => hyC (h ▸ huC)
  have huvne : u ≠ v₁ := fun h => hvC (h ▸ huC)
  -- "Hence every `Y`-complete vertex is adjacent to one of `y, v₁`."
  have hkey : ∀ t : V, VertexComplete G t Y → G.Adj t y ∨ G.Adj t v₁ := fun t ht =>
    Thm232Claim4Antipath.every_complete_adj hBerge Y hYanti y v₁ z u hyv hzy hvu hzv hzu huy
      hzune hzvne huyne huvne hyY hvY (hCY z hzmem) (hCY u huC) hyNC hvNC hzY huY t ht
  -- "and since `c₂, c₃` are `Y`-complete and not adjacent to `y` by (3), it follows that `v₁`
  -- is adjacent to `c₂, c₃`."
  have hvc2 : G.Adj v₁ c₂ := by
    rcases hkey c₂ hc2Y with h | h
    · exact absurd h.symm (hyanti c₂ hc2mem hzc2.symm hac2.symm hbc2.symm)
    · exact h.symm
  have hvf : G.Adj v₁ f := by
    rcases hkey f hfY with h | h
    · exact absurd h.symm (hyanti f hfC hzf.symm haf.symm hbf.symm)
    · exact h.symm
  -- claim (1): `c₂` is the only `Y`-complete rim neighbour of `f`
  have hfedge : ∀ x ∈ C, G.Adj f x → VertexComplete G x Y → x = c₂ := by
    intro x hxC hfx hxY
    rcases hexh f x hfC hxC ⟨hfx, hfY, hxY⟩ with h | h | h | h <;>
      rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1.symm haf
    · exact absurd h1.symm hzf
    · exact absurd h1.symm hzf
    · exact absurd h1.symm hbf
    · exact absurd h1 hnbc.1
    · exact absurd h1 hc2f.ne'
    · exact absurd h1 hc2f.ne'
    · exact h2
  -- "By 16.1 … By 22.3, `v₁` has no other neighbours in `C`."
  have hnbrs : ∀ w ∈ C, G.Adj v₁ w → w = e ∨ w = c₂ ∨ w = f :=
    Thm232Claim4Neighbours.nbrs_subset hG hbsp C Y hopt v₁ e c₂ f hvC hvY hvNC hc2mem hnbc
      hc2Y hfY hvc2 hvf hfedge
  -- "Consequently `x₀` is adjacent to `y`."
  have hnva : ¬ G.Adj v₁ a := by
    intro h
    rcases hnbrs a hnb.2.1 h with h' | h' | h'
    · exact hae h'
    · exact hac2 h'
    · exact haf h'
  have hya : G.Adj y a := by
    rcases hkey a haY with h | h
    · exact h.symm
    · exact absurd h.symm hnva
  -- "but then `x₀-Q-c₃-v₁-y-x₀` is an odd hole, a contradiction."
  refine Thm232Claim3C2Core.no_adj_far_end hBerge Q f a y v₁ hQ hQeven hQ2
    (fun h => hyC (hQsub y h)) (fun h => hvC (hQsub v₁ h)) hyv ?_ ?_ hya
  · intro w hw hwa
    exact hyanti w (hQsub w hw) (fun he => hzQ (he ▸ hw)) hwa (fun he => hbQ (he ▸ hw))
  · intro w hw
    constructor
    · intro h
      rcases hnbrs w (hQsub w hw) h with h' | h' | h'
      · exact absurd (h' ▸ hw) heQ
      · exact absurd (h' ▸ hw) hc2Q
      · exact h'
    · rintro rfl
      exact hvf

end Workspace.ProofLemmas.Thm232Claim4Core
