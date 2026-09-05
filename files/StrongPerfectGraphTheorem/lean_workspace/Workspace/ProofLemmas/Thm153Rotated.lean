import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.Statements.S15.Thm_15_3

/-!
# 15.3 applied to a hole, at an arbitrary base offset

PAPER (15.3, printed p. 95).  The printed statement fixes a numbering `p₁, …, pₙ` of the cycle
in which the four `Y`-complete vertices are `pₙ, p₁, p_i, p_{i+1}`; the proofs that cite it
(16.2 claim (4), and twice in 16.2's endgame) each have a hole whose four `Y`-complete vertices
sit at *some* rotation of that pattern.

`Workspace.Statements.S15.SPGT.thm_15_3` is stated against a literal list `C` with the four
`Y`-complete vertices at positions `n-1, 0, i-1, i`.  This module supplies the rotation: given
an honest hole `D` and a base offset `b`, the list `arc D b n` **is** the rotation of `D` by
`b`, and every hypothesis of 15.3 transports along `cyc D (b + ·)`.

Nothing here corresponds to a numbered result of the paper; it is 15.3 verbatim, re-indexed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm153Rotated

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The full turn `arc D b n` of the rim is a duplicate-free list. -/
theorem rot_nodup {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length)
    (b : ℕ) : (arc D hpos b D.length).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro s hs t ht hst
  rw [List.mem_range] at hs ht
  have h' : s % D.length = t % D.length :=
    Nat.ModEq.add_left_cancel' b (cyc_inj hD hpos hst)
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h'
  exact h'

/-- **15.3, at an arbitrary base offset `b` of an honest hole `D`.**

PAPER (15.3): *"… then some vertex of `F` is `Y`-complete."*  The four `Y`-complete vertices of
`D` are `cyc (b + (n-1))`, `cyc b`, `cyc (b + (i-1))`, `cyc (b + i)` — two disjoint edges of the
rim — and `F` runs between `cyc (b + (h-1))` and `cyc (b + (j-1))`, one in each of the two open
gaps. -/
theorem clean_path_hits_yComplete {G : SimpleGraph V} (hG : InF6 G)
    {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length) (hn6 : 6 ≤ D.length)
    {Y : Set V} (hYD : ∀ y ∈ Y, y ∉ D) (hYanti : AnticonnectedSet G Y)
    (b : ℕ) {h i j : ℕ} (hh : 1 < h) (hhi : h < i) (hij : i + 1 < j) (hjn : j < D.length)
    (hYc : ∀ w ∈ D, (VertexComplete G w Y ↔
      (w = cyc D hpos (b + (D.length - 1)) ∨ w = cyc D hpos b ∨
        w = cyc D hpos (b + (i - 1)) ∨ w = cyc D hpos (b + i))))
    {F : List V}
    (hF : IsPathFrom G F (cyc D hpos (b + (h - 1))) (cyc D hpos (b + (j - 1))))
    (hFY : ∀ w ∈ F, w ∉ Y)
    (hFC : ∀ x ∈ SPGT.interior F, ∀ w ∈ D,
      w ≠ cyc D hpos (b + (h - 1)) → w ≠ cyc D hpos (b + (j - 1)) → ¬ G.Adj x w) :
    ∃ w ∈ F, VertexComplete G w Y := by
  classical
  set E : List V := arc D hpos b D.length with hE
  have hElen : E.length = D.length := arc_length hpos b D.length
  have hEget : ∀ (t : ℕ) (ht : t < E.length), E[t]'ht = cyc D hpos (b + t) := by
    intro t ht
    exact arc_getElem hpos ht
  have hEmem : ∀ w ∈ E, w ∈ D := by
    intro w hw
    obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hw
    rw [← hte]
    exact cyc_mem hpos _
  refine Workspace.Statements.S15.SPGT.thm_15_3 G hG E D.length h i j hElen hn6 hh hhi hij hjn
    (rot_nodup hD hpos b) ?_ ?_ Y ?_ hYanti ?_ F ?_ hFY ?_
  · -- the cycle edges
    intro s t hs ht hcase
    rw [hEget s hs, hEget t ht, cyc_adj hD hpos]
    rw [hElen] at hcase
    rcases hcase with hcase | hcase
    · left
      have ht' : t ≡ s + 1 [MOD D.length] := by rw [hcase]; exact Nat.mod_modEq _ _
      have hmod := Nat.ModEq.add_left b ht'
      rw [← Nat.add_assoc] at hmod
      exact hmod
    · right
      have hs' : s ≡ t + 1 [MOD D.length] := by rw [hcase]; exact Nat.mod_modEq _ _
      have hmod := Nat.ModEq.add_left b hs'
      rw [← Nat.add_assoc] at hmod
      exact hmod
  · -- no chords: `D` is an induced hole
    intro s t hs ht hadj
    rw [hElen] at hs ht
    rw [hEget s (by rw [hElen]; exact hs), hEget t (by rw [hElen]; exact ht),
      cyc_adj hD hpos] at hadj
    rw [hElen]
    left
    rcases hadj with hadj | hadj
    · left
      have h1 : (b + t) ≡ (b + (s + 1)) [MOD D.length] := by
        rw [← Nat.add_assoc]; exact hadj
      have h2 : t ≡ s + 1 [MOD D.length] := Nat.ModEq.add_left_cancel' b h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt ht] at h2
      exact h2
    · right
      have h1 : (b + s) ≡ (b + (t + 1)) [MOD D.length] := by
        rw [← Nat.add_assoc]; exact hadj
      have h2 : s ≡ t + 1 [MOD D.length] := Nat.ModEq.add_left_cancel' b h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hs] at h2
      exact h2
  · -- `Y` is disjoint from the rim
    intro y hy hmem
    exact hYD y hy (hEmem y hmem)
  · -- the four `Y`-complete vertices
    intro w hw
    rw [hYc w (hEmem w hw)]
    rw [hEget _ (by rw [hElen]; omega), hEget _ (by rw [hElen]; omega),
      hEget _ (by rw [hElen]; omega), hEget _ (by rw [hElen]; omega)]
    rw [Nat.add_zero]
  · -- the ends of `F`
    rw [hEget _ (by rw [hElen]; omega), hEget _ (by rw [hElen]; omega)]
    exact hF
  · -- the interior of `F` has no rim neighbours besides its ends
    intro x hx w hw hw1 hw2
    rw [hEget _ (by rw [hElen]; omega)] at hw1
    rw [hEget _ (by rw [hElen]; omega)] at hw2
    exact hFC x hx w (hEmem w hw) hw1 hw2

end Workspace.ProofLemmas.Thm153Rotated
