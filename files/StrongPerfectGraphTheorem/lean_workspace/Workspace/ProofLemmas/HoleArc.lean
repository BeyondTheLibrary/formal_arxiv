import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics

/-!
# Arcs of a hole, and the `F₁₁` projections

Three facts that §§17, 23 and 24 use constantly and that were being re-proved privately in
individual attempt files.

* `hole_take_isPathList` — **a proper arc of a hole is an induced path.**  Deleting even one
  vertex of a hole destroys the wrap-around edge, so within the first `m` positions
  (`m + 1 ≤ c.length`) "cyclically consecutive" collapses to "consecutive", which is exactly
  the path condition.  Every *"let `p₁-⋯-pₙ` be the path `C \ {…}`"* in the paper is an
  instance; 24.5 and 24.6 both need it, and the proof of 24.6 needs precisely the version that
  drops the **last two** vertices.
* `prefix_three` — `[l[0], l[1], l[2]] <+: l`.  This is the shape the `F₁₀` clause of `InF10`
  wants for *"three consecutive neighbours in `C`"* (which is spelled `∃ k, [x,y,z] <+: C.rotate k`).
* `berge_of_inF11` and friends — the projection chain `F₁₁ ≤ F₁₀ ≤ ⋯ ≤ F₃`, whose first
  conjunct is `Berge`.  Writing `hG.1.1.1.1.1.1.1.1` by hand is both unreadable and fragile
  against any future re-bracketing of the class definitions.

None of these corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.HoleArc

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Arcs -/

/-- **A proper initial arc of a hole is an induced path.**  `m + 1 ≤ c.length` is what leaves
at least one vertex of the hole out, hence kills the wrap-around edge. -/
theorem hole_take_isPathList {cyc : List V} (hc : IsHoleList G cyc)
    {m : ℕ} (hm2 : 2 ≤ m) (hm : m + 1 ≤ cyc.length) : IsPathList G (cyc.take m) := by
  obtain ⟨hlen4, hnd, hadj⟩ := hc
  refine ⟨?_, List.Nodup.sublist (List.take_sublist m cyc) hnd, ?_⟩
  · intro h
    have h0 : (cyc.take m).length = 0 := by rw [h]; rfl
    rw [List.length_take] at h0
    omega
  · intro i j hi hj
    have hilt : i < min m cyc.length := by rw [← List.length_take]; exact hi
    have hjlt : j < min m cyc.length := by rw [← List.length_take]; exact hj
    have hi' : i < cyc.length := by omega
    have hj' : j < cyc.length := by omega
    rw [List.getElem_take, List.getElem_take, hadj i j hi' hj']
    have e1 : (i + 1) % cyc.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    have e2 : (j + 1) % cyc.length = j + 1 := Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    omega

/-- The named-ends form of `hole_take_isPathList`. -/
theorem hole_take_isPathFrom {cyc : List V} (hc : IsHoleList G cyc)
    {m : ℕ} (hm2 : 2 ≤ m) (hm : m + 1 ≤ cyc.length) :
    IsPathFrom G (cyc.take m) (cyc[0]'(by omega)) (cyc[m - 1]'(by omega)) := by
  refine ⟨hole_take_isPathList hc hm2 hm, ?_, ?_⟩
  · rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
      List.getElem?_eq_getElem (by omega)]
  · rw [List.getLast?_take, if_neg (by omega),
      List.getElem?_eq_getElem (by omega), Option.some_or]

/-! ### Prefixes of three -/

/-- Three named vertices sitting at positions `0, 1, 2` of a list form a prefix of it — the
shape `InF10`'s *"three consecutive neighbours"* clause asks for. -/
theorem prefix_three {l : List V} {x y z : V} (h : 3 ≤ l.length)
    (h0 : l[0]'(by omega) = x) (h1 : l[1]'(by omega) = y) (h2 : l[2]'(by omega) = z) :
    [x, y, z] <+: l := by
  subst h0
  subst h1
  subst h2
  match l, h with
  | (a :: b :: c :: t), _ => exact ⟨t, by simp⟩

/-! ### The `F` chain -/

theorem inF5_of_inF11 (hG : InF11 G) : InF5 G := hG.1.1.1.1.1.1

theorem inF3_of_inF11 (hG : InF11 G) : InF3 G := hG.1.1.1.1.1.1.1

/-- `F₁₁ ≤ F₁₀ ≤ ⋯ ≤ F₃`, and `F₃`'s first conjunct is `Berge`. -/
theorem berge_of_inF11 (hG : InF11 G) : Berge G := hG.1.1.1.1.1.1.1.1

/-- The `F₁₀` clause of `InF11`: no vertex has three consecutive neighbours on a hole of
length `≥ 6`. -/
theorem noThreeConsecutive_of_inF11 (hG : InF11 G) :
    ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
      ¬ ∃ v x y z : V, (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
          G.Adj v x ∧ G.Adj v y ∧ G.Adj v z := hG.1.2.1

/-- The defining clause of `InF11`: every antihole has length 4. -/
theorem antihole_length_of_inF11 (hG : InF11 G) :
    ∀ c : List V, IsAntiholeList G c → holeLength c = 4 := hG.2

end Workspace.ProofLemmas.HoleArc
