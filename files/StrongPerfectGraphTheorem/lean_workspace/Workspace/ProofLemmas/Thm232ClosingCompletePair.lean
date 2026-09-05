import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.Statements.S02.Thm_2_3

/-! An isolated complete edge on the auxiliary hole in the closing argument of 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingCompletePair

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete edge `p-z` is a segment when the vertices immediately before and
after it are not complete to the hub. -/
theorem pair_segment {G : SimpleGraph V} {Y : Set V} {S : List V} {p z y s : V}
    (hD : IsHoleList G (p :: z :: S)) (hD6 : 6 ≤ (p :: z :: S).length)
    (hS : IsPathFrom G S y s)
    (hpY : VertexComplete G p Y) (hzY : VertexComplete G z Y)
    (hyY : ¬ VertexComplete G y Y) (hsY : ¬ VertexComplete G s Y) :
    IsSegment G (p :: z :: S) Y [p,z] := by
  let D := p :: z :: S
  have hn : 0 < D.length := by simp [D]
  have hnext : D[2 % D.length]? = some y := by
    rw [Nat.mod_eq_of_lt (by change 2 < (p :: z :: S).length; omega)]
    change S[0]? = some y
    simpa only [List.head?_eq_getElem?] using hS.2.1
  have hlast : D[D.length - 1]? = some s := by
    rw [← List.getLast?_eq_getElem?]
    change ([p,z] ++ S).getLast? = some s
    rw [List.getLast?_append_of_ne_nil _ hS.1.1]
    exact hS.2.2
  have hseg := SegmentBasics.isSegment_of_run hD (k := 0) (L := 2) (by omega) (by omega)
    (by
      intro t ht
      interval_cases t
      · refine ⟨p, ?_, hpY⟩
        simp [D]
      · refine ⟨z, ?_, hzY⟩
        simp [D])
    (by
      rintro ⟨a, ha, haY⟩
      change D[2 % D.length]? = some a at ha
      exact hyY (Option.some.inj (hnext.symm.trans ha) ▸ haY))
    (by
      rintro ⟨a, ha, haY⟩
      change D[(0 + (D.length - 1)) % D.length]? = some a at ha
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega), hlast] at ha
      exact hsY (Option.some.inj ha ▸ haY))
  simpa using hseg

/-- PAPER (23.2, printed p. 141): “Since `(C',Y)` is not an odd wheel, it follows
that `(C',Y)` is not a wheel, and so `x₀,z` are the only `Y`-complete vertices in `C'`.”
Here 2.3 supplies the last implication: an even complete-edge count would provide
a second complete edge disjoint from the isolated edge. -/
theorem only_pair {G : SimpleGraph V} (hG : Berge G) {D : List V} {Y : Set V}
    (hD : IsHoleList G D) (hD6 : 6 ≤ D.length) (hYne : Y.Nonempty)
    (hY : AnticonnectedSet G Y) (hDY : ∀ w ∈ D, w ∉ Y)
    (hno : ¬ IsOddWheel G D Y) {p z : V} (hpD : p ∈ D) (hzD : z ∈ D)
    (he : EdgeComplete G Y p z) (hseg : IsSegment G D Y [p,z])
    (hpNbr : ∀ w ∈ D, G.Adj p w → VertexComplete G w Y → w = z)
    (hzNbr : ∀ w ∈ D, G.Adj z w → VertexComplete G w Y → w = p) :
    ∀ w ∈ D, VertexComplete G w Y → w = p ∨ w = z := by
  have hnw : ¬ IsWheel G D Y := fun hw => hno ⟨hw, [p,z], hseg, by change Odd 1; decide⟩
  let E : Set (Sym2 V) := {e | ∃ a ∈ D, ∃ b ∈ D, e = s(a,b) ∧ EdgeComplete G Y a b}
  have heE : s(p,z) ∈ E := ⟨p, hpD, z, hzD, rfl, he⟩
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hG Y hY D (Or.inr hD) hDY).2 hD with
      heven | ⟨a, b, hpair, hab, _⟩
  · have hother : ∃ e ∈ E, e ≠ s(p,z) := by
      by_contra hh
      push Not at hh
      have hE : E = {s(p,z)} := Set.Subset.antisymm
        (fun e he => hh e he) (by rintro e rfl; exact heE)
      change Even E.ncard at heven
      rw [hE, Set.ncard_singleton] at heven
      norm_num at heven
    obtain ⟨e, ⟨a, ha, b, hb, heab, hab⟩, hne⟩ := hother
    have hap : a ≠ p := by
      intro hh
      have hbz := hpNbr b hb (hh ▸ hab.1) hab.2.2
      exact hne (by rw [heab, hh, hbz])
    have haz : a ≠ z := by
      intro hh
      have hbp := hzNbr b hb (hh ▸ hab.1) hab.2.2
      exact hne (by rw [heab, hh, hbp, Sym2.eq_swap])
    have hbp : b ≠ p := by
      intro hh
      have haz := hpNbr a ha (hh ▸ hab.1.symm) hab.2.1
      exact hne (by rw [heab, hh, haz, Sym2.eq_swap])
    have hbz : b ≠ z := by
      intro hh
      have hap := hzNbr a ha (hh ▸ hab.1.symm) hab.2.1
      exact hne (by rw [heab, hh, hap])
    exact (hnw ⟨⟨hD, hD6⟩, ⟨hYne, hY, hDY⟩, p, z, a, b, hpD, hzD, ha, hb,
      he, hab, hap.symm, hbp.symm, haz.symm, hbz.symm⟩).elim
  · have hpab : p = a ∨ p = b := by
      change p ∈ ({a,b} : Set V)
      rw [← hpair]
      exact ⟨hpD, he.2.1⟩
    have hzab : z = a ∨ z = b := by
      change z ∈ ({a,b} : Set V)
      rw [← hpair]
      exact ⟨hzD, he.2.2⟩
    intro w hw hwY
    have hwab : w = a ∨ w = b := by
      change w ∈ ({a,b} : Set V)
      rw [← hpair]
      exact ⟨hw, hwY⟩
    have hpz := he.1.ne
    grind

end Workspace.ProofLemmas.Thm232ClosingCompletePair
