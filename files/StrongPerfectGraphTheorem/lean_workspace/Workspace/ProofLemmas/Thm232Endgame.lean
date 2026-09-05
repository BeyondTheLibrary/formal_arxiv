import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.Thm232Claim3
import Workspace.ProofLemmas.Thm232RemainingClaims
import Workspace.ProofLemmas.Thm232MinPath
import Workspace.ProofLemmas.Thm232NoDoubleNeighbour
import Workspace.ProofLemmas.Thm232Claim3C2

/-!
# 23.2 — steps (3), (4), (5) and the closing paragraph

PAPER (23.2, printed pp. 139–141).  Everything after step (2), in one obligation: from the
configuration `x₀, z, x₁, c₁, c₂, c₃` of `Thm232Configuration`, the path `T = z-y-⋯` of
`Thm232PathT`, and step (2) (`Thm232NoDoubleNeighbour`), the printed proof derives a
contradiction, thereby refuting the existence of a wheel.

The printed argument runs:

> ***(3) `y` has no neighbour in `A₀`.***  *For suppose first that it has a neighbour in
> `A₀ \ {c₂}`, say `c`.  Then `c, z` are nonadjacent and have opposite wheel-parity in the
> wheel `(C,Y)`; it is not the case that `c` and both its neighbours in `C` are `Y`-complete,
> by (1) and the fact that `c ∈ A₀`; not both neighbours of `z` in `C` are adjacent to `y`, by
> (2); so 16.1 implies that `(C, Y ∪ {y})` is a wheel, a contradiction.  So `y` has no
> neighbour in `A₀ \ {c₂}`.  Next suppose that `y` is adjacent to `c₂`.  From the symmetry we
> may assume that `x₀ ≠ c₃`.  Let `Q` be the path of `C \ z` between `x₀, c₃`; so `Q` has
> length `> 0`, and even length by 2.3.  Since `x₀-Q-c₃-c₂-y-x₀` is not an odd hole, it
> follows that `y` is not adjacent to `x₀`.  But then the hole `x₀-Q-c₃-c₂-y-z-x₀` is the rim
> of an odd wheel with hub `Y`, contrary to `G ∈ F₈`.  So `y` is not adjacent to `c₂`.  This
> proves (3).*
>
> *Let `T` have vertices `z-y-v₁-⋯-v_{n+1}`, where `v_{n+1} ∈ A₀`.  From (3), `n ≥ 1`.  By
> choosing `T` of minimum length we may assume that none of `y, v₁, …, v_{n−1}` have
> neighbours in `A₀`.*
>
> ***(4) If `n = 1` then no neighbour of `v₁` in `A₀` is `Y`-complete.*** …
>
> ***(5) One of `x₀, x₁` has no neighbours in `{y, v₁, …, v_n}`.*** …
>
> *Let `F = {y, v₁, …, v_n}`. … But then the hole formed by the union of `R` and the path
> `C \ x₀` is the rim of an odd wheel with hub `Y`, a contradiction.  This proves 23.2.*

**Status: statement only** — the body is `sorry`, to be discharged by splitting this file into
one module per printed claim ((3), (4), (5), endgame).  The hypotheses are exactly the data the
printed proof has in hand at the start of step (3).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (23.2, printed pp. 139–141), steps (3)–(5) and the closing paragraph.** -/
theorem no_wheel_contradiction (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (hmin : ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C')
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k) (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y) (h1Y : VertexComplete G x₁ Y)
    (hc1Y : VertexComplete G c₁ Y) (hc2Y : VertexComplete G c₂ Y)
    (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z) (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁)) :
    False := by
  classical
  -- PAPER: *"By choosing `T` of minimum length we may assume that none of `y, v₁, …, v_{n−1}`
  -- have neighbours in `A₀`."*  We re-choose `T` here, and re-derive (2) and (3) for it.
  have hwheel : IsWheel G C Y := hopt.1
  have hCl : IsHoleList G C := hwheel.1.1
  have hn6 : 6 ≤ C.length := hwheel.1.2
  have hn : 0 < C.length := by omega
  obtain ⟨hx0C, hzC, hx1C, -⟩ := KiteTailBasics.hole_triple hCl ⟨k, hpre1⟩
  obtain ⟨hc1C, hc2C, hc3C, -⟩ := KiteTailBasics.hole_triple hCl ⟨k + d, hpre2⟩
  have p0 : C[(k + 0) % C.length]'(Nat.mod_lt _ hn) = x₀ :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 0) (j := k + 0) (by simp) rfl).symm
  have p1 : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 1) (j := k + 1) (by simp) rfl).symm
  have p2 : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 2) (j := k + 2) (by simp) rfl).symm
  have pd : C[(k + d) % C.length]'(Nat.mod_lt _ hn) = c₁ :=
    (Thm232Claim3C2.prefix_getElem hn hpre2 (i := 0) (j := k + d) (by simp) (by omega)).symm
  have pd1 : C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) = c₂ :=
    (Thm232Claim3C2.prefix_getElem hn hpre2 (i := 1) (j := k + (d + 1)) (by simp)
      (by omega)).symm
  have pd2 : C[(k + (d + 2)) % C.length]'(Nat.mod_lt _ hn) = c₃ :=
    (Thm232Claim3C2.prefix_getElem hn hpre2 (i := 2) (j := k + (d + 2)) (by simp)
      (by omega)).symm
  -- a rim vertex at cyclic offset `3 ≤ j < |C|` is none of `x₀, z, x₁`
  have hoff : ∀ j : ℕ, 3 ≤ j → j < C.length →
      C[(k + j) % C.length]'(Nat.mod_lt _ hn) ≠ x₀ ∧
      C[(k + j) % C.length]'(Nat.mod_lt _ hn) ≠ z ∧
      C[(k + j) % C.length]'(Nat.mod_lt _ hn) ≠ x₁ := by
    intro j hj3 hjn
    have hmod : ∀ i : ℕ, i ≤ 2 → i % C.length ≠ j % C.length := by
      intro i hi
      rw [Thm232Claim3C2.mod_le_self hn (by omega), Thm232Claim3C2.mod_le_self hn (by omega)]
      split_ifs <;> omega
    refine ⟨?_, ?_, ?_⟩
    · rw [← p0]
      exact fun he => Thm232Claim3C2.pos_ne hCl.2.1 hn k j 0
        (fun hc => hmod 0 (by omega) hc.symm) he
    · rw [← p1]
      exact fun he => Thm232Claim3C2.pos_ne hCl.2.1 hn k j 1
        (fun hc => hmod 1 (by omega) hc.symm) he
    · rw [← p2]
      exact fun he => Thm232Claim3C2.pos_ne hCl.2.1 hn k j 2
        (fun hc => hmod 2 (by omega) hc.symm) he
  have hc2off := hoff (d + 1) (by omega) (by omega)
  rw [pd1] at hc2off
  -- the `Y`-complete edge of `C` avoiding `x₀, z, x₁` needed for (2)
  have hedge : ∃ u v : V, u ∈ C ∧ v ∈ C ∧
      (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧ (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧ EdgeComplete G Y u v := by
    rcases Nat.lt_or_ge d 3 with hd | hd
    · -- `d = 2`: use the edge `c₂c₃`, at offsets `3` and `4 < |C|`
      have hc3off := hoff (d + 2) (by omega) (by omega)
      rw [pd2] at hc3off
      exact ⟨c₂, c₃, hc2C, hc3C, hc2off, hc3off,
        hnbc.2.2.2.2.1, hc2Y, hc3Y⟩
    · -- `d ≥ 3`: use the edge `c₁c₂`
      have hc1off := hoff d (by omega) (by omega)
      rw [pd] at hc1off
      exact ⟨c₁, c₂, hc1C, hc2C, hc1off, hc2off,
        hnbc.2.2.2.1.symm, hc1Y, hc2Y⟩
  -- re-choose `T` of minimum length
  set A₀ : Set V := {v : V | v ∈ C} \ ({z, x₀, x₁} : Set V) with hA₀def
  have hzA : z ∉ A₀ := fun h => h.2 (by simp)
  have hAF : ∀ a ∈ A₀, a ∉ ({x₀, x₁} : Set V) := by
    intro a ha hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact ha.2 (by simp)
    · exact ha.2 (by simp)
  have hwA : w ∈ A₀ := by
    refine ⟨hwC, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hwz, hw0, hw1⟩
  have hT2 : 2 ≤ T.length := by rw [hTeq]; simp
  obtain ⟨S, v, hS2, hSpath, hvA, hSF, hSint, hSattach⟩ :=
    Workspace.ProofLemmas.Thm232MinPath.exists_min_clean_path (G := G) Y A₀
      ({x₀, x₁} : Set V) z hzA hAF T w hT2 hpath hwA
      (fun u hu => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨(havoid u hu).1, (havoid u hu).2⟩) hint
  have hShead : S.head? = some z := hSpath.2.1
  obtain ⟨y', R', hSeq⟩ : ∃ y' R', S = z :: y' :: R' := by
    cases hSl : S with
    | nil => rw [hSl] at hS2; simp at hS2
    | cons a t =>
      cases t with
      | nil => rw [hSl] at hS2; simp at hS2
      | cons b t' =>
        rw [hSl] at hShead
        simp only [List.head?_cons, Option.some.injEq] at hShead
        exact ⟨b, t', by rw [hShead]⟩
  have hSavoid : ∀ u ∈ S, u ≠ x₀ ∧ u ≠ x₁ := by
    intro u hu
    have := hSF u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  have hvC : v ∈ C := hvA.1
  have hvne : v ≠ z ∧ v ≠ x₀ ∧ v ≠ x₁ := by
    have := hvA.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  have h2' : ¬ (G.Adj y' x₀ ∧ G.Adj y' x₁) :=
    Workspace.ProofLemmas.Thm232NoDoubleNeighbour.not_adj_both G hG hbsp C Y hopt
      z x₀ x₁ y' S R' hzC hnb h0Y hzY h1Y hedge hSeq hSavoid
      ⟨v, hSpath, hvC, hvne.1, hvne.2.1, hvne.2.2⟩ hSint
  clear_value A₀
  subst hA₀def
  have h3 := Workspace.ProofLemmas.Thm232Claim3.claim3 G hG hbsp C Y hopt
    x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y
    hnb hnbc hexh S R' y' v hSeq hSpath hvC hvne.2.1 hvne.2.2 hSavoid hSint h2'
  clear hpath hTeq hwC hwz hw0 hw1 havoid hint h2
  let ctx : Workspace.ProofLemmas.Thm232RemainingClaims.EndgameContext
      G C Y x₀ z x₁ c₁ c₂ c₃ k d S R' y' v :=
    { hG := hG
      hbsp := hbsp
      hopt := hopt
      hmin := hmin
      hd2 := hd2
      hdn := hdn
      hpre1 := hpre1
      hpre2 := hpre2
      h0Y := h0Y
      hzY := hzY
      h1Y := h1Y
      hc1Y := hc1Y
      hc2Y := hc2Y
      hc3Y := hc3Y
      hnb := hnb
      hnbc := hnbc
      hexh := hexh
      hTeq := hSeq
      hpath := hSpath
      hwC := hvC
      hwz := hvne.1
      hw0 := hvne.2.1
      hw1 := hvne.2.2
      havoid := hSavoid
      hint := hSint
      h2 := h2'
      h3 := h3 }
  have h5 := Workspace.ProofLemmas.Thm232RemainingClaims.claim5 G hG hbsp C Y hopt
    x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y
    hnb hnbc hexh S R' y' v hSeq hSpath hvC hvne.1 hvne.2.1 hvne.2.2 hSavoid hSint h2' h3
    hSattach
  have horient :=
    Workspace.ProofLemmas.Thm232RemainingClaims.closing_orientation_gap G C Y
      x₀ z x₁ c₁ c₂ c₃ k d S R' y' v ctx h5
  obtain ⟨Q, hQ, hQF, hQiso⟩ :=
    Workspace.ProofLemmas.Thm232RemainingClaims.attachment_path_gap G C Y
      x₀ z x₁ c₁ c₂ c₃ k d S R' y' v ctx horient
  exact Workspace.ProofLemmas.Thm232RemainingClaims.final_odd_wheel_gap G C Y
    x₀ z x₁ c₁ c₂ c₃ k d S R' y' v ctx Q horient hQ hQF hQiso

end Workspace.ProofLemmas.Thm232Endgame
