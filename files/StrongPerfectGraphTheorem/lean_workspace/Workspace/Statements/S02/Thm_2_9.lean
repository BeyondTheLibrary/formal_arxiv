/-  **2.9** — the assembly of the four printed branches.

The printed proof of 2.9 (perfect.pdf p. 11) splits into exactly four blocks, each of which is
already a sorry-free lemma of `Workspace.ProofLemmas`:

* *"If `P` has length 2, choose an antipath `Q` … and so exactly one of `Q`,`R` has odd length
  and the theorem holds."*  →  `Thm29Aux.branch_len2`  (gives alternative 3).
* *"So we may assume `P` has length ≥ 4. … Let `G₀` be obtained from `G \ Y` by adding a new
  vertex `y` with neighbour set `X ∪ {pₙ}`. … If `G₀` is Berge then by 2.1 there is a leap for
  `P'` in `X`, and the result follows."*  →  `Thm29Aux.branch_berge`  (gives alternative 1).
* *"Assume first that there is an odd hole `C` of length ≥ 7 in `G₀`. …"*  →
  `Thm29OddHole.branch_oddhole`  (gives alternative 2).
* *"Since an odd hole of length 5 is also an odd antihole, we may assume that there is an odd
  antihole in `G₀`, say `D`. … a contradiction.  This proves 2.9."*  →
  `Thm29OddAntihole.branch_antihole`  (gives `False`).

This file only performs the case split the paper performs, in the paper's order:

  length 2  |  length ≥ 4 and `G₀` Berge  |  `G₀` not Berge, odd hole  |  `G₀` not Berge, odd antihole

together with the paper's *"since an odd hole of length 5 is also an odd antihole"* (which is
`PathGlue.isHoleList_compl_of_length_five`), and finally the closing sentence *"In each case,
either `(V(P \ p₁), X)` or `(V(P \ pₙ), Y)` is not balanced"*, which is `Thm29Aux.second_of_first`.
-/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm29Aux
import Workspace.ProofLemmas.Thm29OddHole
import Workspace.ProofLemmas.Thm29OddAntihole

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.9** (printed p. 11)

PAPER: *"Let `G` be Berge, and let `X,Y` be disjoint nonempty anticonnected
subsets of `V(G)`, complete to each other.  Let `P` be a path in `G \ (X ∪ Y)`
with even length `> 0`, with vertices `p₁,…,pₙ` in order, such that `p₁` is the
unique `X`-complete vertex of `P` and `pₙ` is the unique `Y`-complete vertex of
`P`.  Then either:*

*1. `P` has length `≥ 4` and there are nonadjacent `x₁,x₂ ∈ X` such that
`x₁`-`p₂`-`⋯`-`pₙ`-`x₂` is a path, or*

*2. `P` has length `≥ 4` and there are nonadjacent `y₁,y₂ ∈ Y` such that
`y₁`-`p₁`-`⋯`-`pₙ₋₁`-`y₂` is a path, or*

*3. `P` has length `2` and there is an antipath `Q` between `p₂` and `p₃` with
interior in `X`, and an antipath `R` between `p₁` and `p₂` with interior in `Y`,
and exactly one of `Q`,`R` has odd length.*

*In each case, either `(V(P \ p₁), X)` or `(V(P \ pₙ),Y)` is not balanced."*

"`X` and `Y` are complete to each other" is `Complete G X Y` (adjacency is
symmetric, so this already says every vertex of `Y` is `X`-complete too).

`p₂`-`⋯`-`pₙ` is `p.tail` and `p₁`-`⋯`-`pₙ₋₁` is `p.dropLast`, so alternatives 1
and 2 assert that `x₁ :: (p.tail ++ [x₂])`, resp. `y₁ :: (p.dropLast ++ [y₂])`, is
a path of `G`.  In alternative 3, `P` has length `2`, i.e. `p = [p₁, c, pₙ]` with
`c = p₂` and `pₙ = p₃`.  "Exactly one of `Q`,`R` has odd length" is `Xor'`.
`V(P \ p₁)` is `{w | w ∈ p} \ {p₁}`.  The closing sentence "In each case, …" is
the second conjunct of the conclusion. -/
theorem thm_2_9 (G : SimpleGraph V) (hG : Berge G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pn : V) (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (heven : Even (pathLength p)) (hpos : 0 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pn)) :
    ((4 ≤ pathLength p ∧ ∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧
        IsPathList G (x₁ :: (p.tail ++ [x₂]))) ∨
      (4 ≤ pathLength p ∧ ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧
        IsPathList G (y₁ :: (p.dropLast ++ [y₂]))) ∨
      (pathLength p = 2 ∧ ∃ c : V, p = [p₁, c, pn] ∧
        ∃ Q R : List V,
          (IsAntipathFrom G Q c pn ∧ ∀ w ∈ SPGT.interior Q, w ∈ X) ∧
          (IsAntipathFrom G R p₁ c ∧ ∀ w ∈ SPGT.interior R, w ∈ Y) ∧
          Xor' (Odd (pathLength Q)) (Odd (pathLength R)))) ∧
    (¬ SPGT.Balanced G ({w : V | w ∈ p} \ {p₁}) X ∨
      ¬ SPGT.Balanced G ({w : V | w ∈ p} \ {pn}) Y) := by
  classical
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hc => hpXY w hw (Or.inl hc)
  have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp
  -- `Odd (holeLength [a,b,c,d,e])`, used for the `C₅` reindexing below.
  have hodd5 : ∀ a b c d e : V ⊕ Unit, Odd (holeLength [a, b, c, d, e]) := by
    intro a b c d e
    exact ⟨2, rfl⟩
  have hfirst :
      ((4 ≤ pathLength p ∧ ∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧
          IsPathList G (x₁ :: (p.tail ++ [x₂]))) ∨
        (4 ≤ pathLength p ∧ ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧
          IsPathList G (y₁ :: (p.dropLast ++ [y₂]))) ∨
        (pathLength p = 2 ∧ ∃ c : V, p = [p₁, c, pn] ∧
          ∃ Q R : List V,
            (IsAntipathFrom G Q c pn ∧ ∀ w ∈ SPGT.interior Q, w ∈ X) ∧
            (IsAntipathFrom G R p₁ c ∧ ∀ w ∈ SPGT.interior R, w ∈ Y) ∧
            Xor' (Odd (pathLength Q)) (Odd (pathLength R)))) := by
    rcases Nat.lt_or_ge (pathLength p) 4 with hlt4 | h4
    · -- *"If `P` has length 2 … the theorem holds."*  (even, positive and `< 4`, so `= 2`)
      have h2 : pathLength p = 2 := by
        obtain ⟨k, hk⟩ := heven
        omega
      exact Or.inr (Or.inr ⟨h2, Thm29Aux.branch_len2 hG hXY hXa hYa hcompl hp hpXY hhead hlast
        hXuniq hYuniq h2⟩)
    · -- *"So we may assume `P` has length ≥ 4."*
      have hn5 : 5 ≤ p.length := by omega
      by_cases hB : Berge (Thm29Aux.cG0 G p X pn)
      · -- *"If `G₀` is Berge then by 2.1 there is a leap for `P'` in `X`, and the result
        -- follows."*
        exact Or.inl ⟨h4, Thm29Aux.branch_berge hG hXa hp hpX hn5 hhead hlast hXuniq heven hB⟩
      · -- *"So we may assume `G₀` is not Berge."*
        have hB' : ¬ ((∀ c : List (V ⊕ Unit), IsHoleList (Thm29Aux.cG0 G p X pn) c →
              Even (holeLength c)) ∧
            (∀ c : List (V ⊕ Unit), IsHoleList (Thm29Aux.cG0 G p X pn)ᶜ c →
              Even (holeLength c))) := hB
        rcases not_and_or.mp hB' with hno | hno
        · -- `G₀` has an odd hole `C`
          obtain ⟨C, hCimp⟩ := not_forall.mp hno
          rw [Classical.not_imp] at hCimp
          obtain ⟨hC, hCne⟩ := hCimp
          have hCodd : Odd (holeLength C) := Nat.not_even_iff_odd.mp hCne
          have hC4 : 4 ≤ holeLength C := HoleBasics.hole_length_ge_four hC
          obtain ⟨k, hk⟩ := hCodd
          rcases (by omega : holeLength C = 5 ∨ 7 ≤ holeLength C) with h5 | h7
          · -- *"since an odd hole of length 5 is also an odd antihole"*
            exact absurd (Thm29OddAntihole.branch_antihole hG hXY hXa hYa hcompl hp hpXY heven h4
              hhead hlast hXuniq hYuniq
              (PathGlue.isHoleList_compl_of_length_five hC (show C.length = 5 from h5))
              (hodd5 _ _ _ _ _)) (fun h => h)
          · -- *"Assume first that there is an odd hole `C` of length ≥ 7 in `G₀`."*
            exact Or.inr (Or.inl ⟨h4, Thm29OddHole.branch_oddhole hG hXY hXa hYa hcompl hp hpXY
              heven h4 hhead hlast hXuniq hYuniq hC ⟨k, hk⟩ h7⟩)
        · -- *"we may assume that there is an odd antihole in `G₀`, say `D`."*
          obtain ⟨D, hDimp⟩ := not_forall.mp hno
          rw [Classical.not_imp] at hDimp
          obtain ⟨hD, hDne⟩ := hDimp
          exact absurd (Thm29OddAntihole.branch_antihole hG hXY hXa hYa hcompl hp hpXY heven h4
            hhead hlast hXuniq hYuniq hD (Nat.not_even_iff_odd.mp hDne)) (fun h => h)
  exact ⟨hfirst, Thm29Aux.second_of_first hp hhead hlast heven hpos hfirst⟩


end SPGT

end Workspace.Statements.S02
