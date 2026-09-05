import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.ProofLemmas.Thm192Claim7GapReflection
import Workspace.ProofLemmas.Thm192Claim7ShortCut
import Workspace.ProofLemmas.Thm192Claim7Separated

/-! Explicit local gaps in the parity analysis of claim (7) of 19.2.
The index `i` is the last neighbour of `x₂` in the interior of `P`.
These statements contain only the path information used by the indicated paragraphs;
the induction, minimality, symmetry, and final contradictions are handled elsewhere. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- LABELLED GAP. PAPER (printed p. 120, claim (7), first case):
"By 16.1, `pᵢ,z` have the same wheel-parity, and so there are an odd number of
`Y₀`-complete edges in `pᵢ-⋯-pₙ-x₁`. ... By 2.10, `Y` contains a leap ...
contrary to 13.6. So `C₁` has length 4, that is, `i = n`, and `pₙ` is
`Y₀`-complete. ... `y` is adjacent to `x₂`."
The reflection argument has already supplied `hycontact`. The remaining steps
are the 16.1 parity calculation and the 2.10/13.6 exclusion of a longer cut. -/
theorem noncomplete_short_cut_of_contact {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length) (hW : IsWheel G (z :: P) (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hzY : VertexComplete G z Y)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i))
    (hycontact : G.Adj y (x 2) ∨ G.Adj y (P[P.length - 2]'(by omega))) :
    i = P.length - 2 ∧ VertexComplete G (P[i]'(by omega)) (Y \ {y}) ∧ G.Adj y (x 2) := by
  obtain ⟨k, hk, hik, hkc⟩ := Thm192Claim7NoncompleteParity.exists_complete_after hG hws hHyp
    hP hPI hP5 hW hx2nc hx21 hzY hi hin hxI hlast
  have hiend : i = P.length - 2 := Thm192Claim7ShortCut.cut_length_four hG hws hHyp hyY hP hPI
    hP5 hx20 hx21 hzY hno hi hin hxI hlast hycontact hk hik hkc
  have hkc' : VertexComplete G (P[P.length - 2]'(by omega)) (Y \ {y}) := by
    rw [Thm192Claim7Aux.getElem_idx_congr (l := P) (show P.length - 2 = k by omega)
      (by omega) (by omega)]
    exact hkc
  have hpi : VertexComplete G (P[i]'(by omega)) (Y \ {y}) := by
    rw [Thm192Claim7Aux.getElem_idx_congr (l := P) hiend (by omega) (by omega)]
    exact hkc'
  refine ⟨hiend, hpi, ?_⟩
  rcases hycontact with h | h
  · exact h
  · exfalso
    refine hno (P.length - 2) (by omega) ⟨PathBasics.path_adj_succ hP.1 (by omega), ?_, ?_⟩
    · intro w hw
      by_cases hwy : w = y
      · subst hwy; exact h.symm
      · exact hkc' w ⟨hw, hwy⟩
    · rw [Thm192Claim7Aux.getElem_idx_congr (l := P)
        (show P.length - 2 + 1 = P.length - 1 by omega) (by omega) (by omega),
        PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
      exact hHyp.2.2.2.1

/-- PAPER (printed p. 120, claim (7), first case):
"So `C₁` has length 4, that is, `i = n`, and `pₙ` is `Y₀`-complete.
By (4) it follows that `pₙ` is nonadjacent to `y`, and therefore `y` is adjacent
to `x₂` (since we already showed that `y` is adjacent to one of `x₂,pᵢ,…,pₙ`)."
This is the one-sided endpoint reduction, before the symmetry and long prism.
The reflection exclusion is proved in `right_contact`; the parity calculation
and exclusion of a longer cut remain in `noncomplete_short_cut_of_contact`. -/
theorem noncomplete_short_cut {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length) (hW : IsWheel G (z :: P) (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hzY : VertexComplete G z Y)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i)) :
    i = P.length - 2 ∧ VertexComplete G (P[i]'(by omega)) (Y \ {y}) ∧ G.Adj y (x 2) := by
  have hycontact := Thm192Claim7GapReflection.right_contact hG hws hHyp hyY hyz hP hP5 hPI hx21
    ⟨⟨_, PathBasics.getElem_mem_interior hP.1 (by omega) hi hin, hxI⟩, hyI⟩
  exact noncomplete_short_cut_of_contact hG hws hHyp hyY hyz hP hPI hP5 hW hx2nc
    hx20 hx21 hzY hno hyI hi hin hxI hlast hycontact

/-- LABELLED GAP. PAPER (printed p. 120, claim (7)):
"Suppose `j ≠ i`. Then the path `x₂-pᵢ-⋯-pⱼ-y` is even and has length at
least 4. By 13.7 ... By 18.2 ... `pⱼ,pₙ` are both not `Y₀`-complete, and so
`(C₁,Y₀)` is an odd wheel, contrary to `G ∈ F₇`."
The last neighbour `i` of `x₂` and first neighbour `j` of `y` after it are
already chosen. Only the separated-index parity contradiction remains here. -/
theorem complete_separated_contact {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hfirst : (∃ w ∈ SPGT.interior P, VertexComplete G w (Y ∪ {x 2})) → VertexComplete G z Y)
    (hno : VertexComplete G z Y → ∀ k (hk : k + 1 < P.length),
      ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hend : ¬ VertexComplete G (P[P.length - 2]'(by omega)) (Y ∪ {x 2}))
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i))
    {j : ℕ} (hj : j + 1 < P.length) (hij : i < j)
    (hyj : G.Adj y (P[j]'(by omega)))
    (hmin : ∀ k (hk : k < P.length), i ≤ k → k < j → ¬ G.Adj y (P[k]'hk)) : False :=
  Thm192Claim7Separated.separated_contact hG hws hHyp hyY hyz hY0 hP hPI hP5 hx2c hx2y
    hx20 hx21 hno hyI hi hin hxI hlast hj hij hyj hmin

/-- PAPER (printed p. 120, claim (7), second case):
"Since `y` is adjacent to `pₙ`, we may choose `j` with `i ≤ j ≤ n` minimum such
that `y` is adjacent to `pⱼ`. ... This proves that `j = i`, that is, `y` is
adjacent to `pᵢ`."
The final neighbour of `y` is supplied by 17.1, as proved in `right_contact`.
We choose `j` and reduce to the separately labelled parity contradiction.
The following antihole argument proving `i = n` and the final application of
17.1 are proved separately. -/
theorem complete_last_neighbour_contact {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hfirst : (∃ w ∈ SPGT.interior P, VertexComplete G w (Y ∪ {x 2})) → VertexComplete G z Y)
    (hno : VertexComplete G z Y → ∀ k (hk : k + 1 < P.length),
      ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hend : ¬ VertexComplete G (P[P.length - 2]'(by omega)) (Y ∪ {x 2}))
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i)) :
    G.Adj y (P[i]'(by omega)) := by
  classical
  have hlastY : G.Adj y (P[P.length - 2]'(by omega)) := by
    rcases Thm192Claim7GapReflection.right_contact hG hws hHyp hyY hyz hP hP5 hPI hx21
      ⟨⟨_, PathBasics.getElem_mem_interior hP.1 (by omega) hi hin, hxI⟩, hyI⟩ with h | h
    · exact (hx2y h.symm).elim
    · exact h
  have hex : ∃ j : ℕ, ∃ hj : j + 1 < P.length, i ≤ j ∧ G.Adj y (P[j]'(by omega)) :=
    ⟨P.length - 2, by omega, by omega, hlastY⟩
  obtain ⟨hj, hij, hyj⟩ := Nat.find_spec hex
  by_cases hji : Nat.find hex = i
  · simpa only [hji] using hyj
  · have hmin : ∀ k (hk : k < P.length), i ≤ k → k < Nat.find hex → ¬ G.Adj y (P[k]'hk) := by
      intro k hk hik hkj hyk
      exact Nat.find_min hex hkj ⟨by omega, hik, hyk⟩
    exact (complete_separated_contact hG hws hHyp hyY hyz hY0 hP hPI hP5 hx2c hx2y
      hx20 hx21 hfirst hno hend hyI hi hin hxI hlast hj (by omega) hyj hmin).elim

end Workspace.ProofLemmas.Thm192Claim7GapParity
