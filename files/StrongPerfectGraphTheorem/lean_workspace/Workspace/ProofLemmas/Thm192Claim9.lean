import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim3
import Workspace.ProofLemmas.Thm192Claim7
import Workspace.ProofLemmas.Thm192Claim8
import Workspace.ProofLemmas.Thm192Claim9MinimalityWitness
import Workspace.ProofLemmas.Thm192Claim9YAdjX2
import Workspace.ProofLemmas.Thm192Claim9NotAdjX2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ReflectionAntihole
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S17.Thm_17_3

/-!
# Claim (9) of the printed proof of 19.2

PAPER (printed p. 121):

> **(9)** *There is no connected `F ⊆ A` containing neighbours of all of `x₀, x₁, x₂` except
> `A` itself.*
>
> *For suppose that such a set `F` exists with `F ≠ A`, and choose `f ∈ A \ F` such that
> `A \ {f}` is connected.  From the minimality of `A`, there exists `y₀ ∈ Y` nonadjacent to
> `x₂` with no neighbour in `A \ {f}`, and therefore `f` is the unique neighbour of `y₀` in
> `A`.  If `y₀ ∈ Y₀`, then `x₂` is not `Y₀`-complete, and therefore by (2) there are two
> `Y₀`-complete vertices in `A`, a contradiction.  So `y₀ = y`, and therefore `y` is not
> adjacent to `x₂`.  Suppose that `x₂` is not adjacent to `f`.  Then both `z, y` have unique
> neighbours in `A ∪ {x₂}`, namely `x₂, f`; `z, y` are `{x₀,x₁}`-complete, and `x₂, f` are
> not; `f-y-z-x₂` is a path; and `x₀, x₁` both have neighbours in `A`, contrary to 17.3.  So
> `x₂` is adjacent to `f`.  By (8) `x₂` is nonadjacent to both `x₀, x₁`.  Since `f` is not
> `{x₀,x₁}`-complete, we may assume from the symmetry that `f` is nonadjacent to `x₁`.  Now
> `A ∪ {x₂}` catches the triangle `{z,y,x₁}`; the only neighbour of `z` in `A ∪ {x₂}` is
> `x₂`; the only neighbour of `y` in `A ∪ {x₂}` is `f`; `x₂, f` are both nonadjacent to
> `x₁`; and so by 17.1, `A ∪ {x₂}` contains a reflection of the triangle.  Hence there
> exists `f₁ ∈ A \ {f}`, adjacent to `x₁, x₂, f` and not to `y` (and therefore not to `x₀`).
> Since every path between `x₀, x₁` with interior in `A` has length `≥ 4` it follows that
> `x₀` is nonadjacent to `f, f₁`, and this restores the symmetry between `x₀, x₁`; and
> consequently by the same argument there exists `f₀ ∈ A \ {f}` adjacent to `x₂, f, x₀` and
> not to `y, x₁`.  Since `z-x₀-f₀-f₁-x₁-z` is not an odd hole, `f₀` is nonadjacent to `f₁`;
> but then `x₀-f₀-f-f₁-x₁` violates (7).  This proves (9).*

Encoding: as for claim (3), *"there is no connected `F ⊆ A` … except `A` itself"* is
rendered as: every such `F` equals `A`.  The list of vertices whose neighbours `F` must
contain is `x₀, x₁, x₂` — `y` is **not** in it, which is exactly what distinguishes (9)
from (3).

**`hcex`, the minimum-counterexample hypothesis.**  Claim (9) does not cite claim (4)
directly, but it does cite claims (7) and (8), *both of which do*:

* *"By (8) `x₂` is nonadjacent to both `x₀, x₁`"*;
* *"but then `x₀-f₀-f-f₁-x₁` violates (7)"*.

Claims (7) and (8) each carry `(hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)` because their own
printed proofs cite the `hcex`-dependent conjuncts of claim (4) (see the module docstrings of
`Thm192Claim7` and `Thm192Claim8`), so (9) must *thread* `hcex` through to those two calls
and therefore carries the binder itself, in the same slot as claims (4)–(8), (10), (11) and
(12).  On the assembly side (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by
`by_contra` on the goal `Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim9

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas

/-- A five-element list with exactly its four consecutive edges is an induced path. -/
private theorem isPathList_five {G : SimpleGraph V} {a b c d e : V}
    (hnd : [a, b, c, d, e].Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d e)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj a e)
    (n4 : ¬ G.Adj b d) (n5 : ¬ G.Adj b e) (n6 : ¬ G.Adj c e) :
    IsPathList G [a, b, c, d, e] := by
  have key : ∀ i j : ℕ, i < 5 → j < 5 →
      ∀ (hi : i < [a, b, c, d, e].length) (hj : j < [a, b, c, d, e].length),
        (G.Adj ([a, b, c, d, e][i]'hi) ([a, b, c, d, e][j]'hj) ↔
          (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi5 hj5
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h3 (by first | omega | simp | tauto)
      | exact iff_of_true h4 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_true h3.symm (by first | omega | simp | tauto)
      | exact iff_of_true h4.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false n2 (by first | omega | simp | tauto)
      | exact iff_of_false n3 (by first | omega | simp | tauto)
      | exact iff_of_false n4 (by first | omega | simp | tauto)
      | exact iff_of_false n5 (by first | omega | simp | tauto)
      | exact iff_of_false n6 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n4 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n5 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n6 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

private theorem triple_distinct {a b c : V} (h : ({a, b, c} : Set V).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have pair_le : ∀ p q : V, ({p, q} : Set V).ncard ≤ 2 := by
    intro p q
    have hh := Set.ncard_insert_le p ({q} : Set V)
    simpa using hh
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have he : ({a, a, c} : Set V) = {a, c} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a c; omega)
  · have he : ({a, b, a} : Set V) = {a, b} := by ext; simp; tauto
    rw [he] at h
    exact (by have := pair_le a b; omega)
  · have he : ({a, b, b} : Set V) = {a, b} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a b; omega)

/-- Every vertex of the first triangle has its matched vertex in a reflection, and it has
no other neighbour in the reflected triangle. -/
private theorem reflection_partner {G : SimpleGraph V} {a₀ a₁ a₂ b₀ b₁ b₂ u : V}
    (h : IsReflectionOfTriangle G a₀ a₁ a₂ b₀ b₁ b₂)
    (hu : u ∈ ({a₀, a₁, a₂} : Set V)) :
    ∃ v ∈ ({b₀, b₁, b₂} : Set V), G.Adj u v ∧
      ∀ w ∈ ({a₀, a₁, a₂} : Set V), w ≠ u → ¬ G.Adj w v := by
  obtain ⟨hb₀₁, hb₀₂, hb₁₂⟩ := triple_distinct h.2.1.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨b₀, by simp, (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₀ (by simp)).mp hadj with hw | hw | hw
    · exact hne hw.1
    · exact hb₀₁ hw.2
    · exact hb₀₂ hw.2
  · refine ⟨b₁, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₁ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₁ hw.2.symm
    · exact hne hw.1
    · exact hb₁₂ hw.2
  · refine ⟨b₂, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₂ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₂ hw.2.symm
    · exact hb₁₂ hw.2.symm
    · exact hne hw.1

/-- The application of 17.1 used twice in claim (9).  The vertices `x₂` and `f` are the
partners of `z` and `y`, so the third partner lies in `A \ {f}` and is adjacent to both. -/
private theorem endpoint_reflection (G : SimpleGraph V) (hG : InF7 G)
    (z y x₂ a b f : V) (A : Set V)
    (hzx₂ : G.Adj z x₂) (hzy : G.Adj z y) (hza : G.Adj z a)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyx₂ : ¬ G.Adj y x₂)
    (hx₂a : ¬ G.Adj x₂ a) (hfa : ¬ G.Adj f a)
    (hfA : f ∈ A) (hyf : G.Adj y f) (hx₂f : G.Adj x₂ f)
    (hyuniq : ∀ g ∈ A, G.Adj y g → g = f)
    (hAconn : ConnectedSet G A) (haA : ∃ g ∈ A, G.Adj a g)
    (hzA : ∀ g ∈ A, ¬ G.Adj z g) (hznotA : z ∉ A)
    (hnoc : ∀ g ∈ A, ¬ (G.Adj g a ∧ G.Adj g b))
    (hzne_y : z ≠ y) (hzne_a : z ≠ a) (hyne_a : y ≠ a)
    (hx₂ne_z : x₂ ≠ z) (hx₂ne_y : x₂ ≠ y) (hx₂ne_a : x₂ ≠ a) :
    ∃ g ∈ A \ {f}, G.Adj a g ∧ G.Adj x₂ g ∧ G.Adj f g ∧
      ¬ G.Adj y g ∧ ¬ G.Adj b g := by
  classical
  let T : Set V := {z, y, a}
  let F : Set V := A ∪ {x₂}
  have htri : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr ⟨z, y, a, hzne_y, hzne_a, hyne_a, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact hzy
    · exact hza
    · exact hzy.symm
    · exact (huv rfl).elim
    · exact hya
    · exact hza.symm
    · exact hya.symm
    · exact (huv rfl).elim
  have hyA : y ∉ A := by
    intro hyA
    exact hnoc y hyA ⟨hya, hyb⟩
  have ha_notA : a ∉ A := fun ha => hzA a ha hza
  have hFsub : F ⊆ Tᶜ := by
    intro g hgF hgT
    rcases hgF with hgA | hg2
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hznotA (h ▸ hgA)
      · exact hyA (h ▸ hgA)
      · exact ha_notA (h ▸ hgA)
    · have hg : g = x₂ := by simpa using hg2
      subst g
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hx₂ne_z h
      · exact hx₂ne_y h
      · exact hx₂ne_a h
  have hFconn : ConnectedSet G F := by
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hAconn ⟨f, hfA, hx₂f⟩
  have hcatch : Catches G F T := by
    refine ⟨htri, hFconn, Set.disjoint_left.mpr hFsub, ?_⟩
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨x₂, Or.inr rfl, hzx₂⟩
    · exact ⟨f, Or.inl hfA, hyf⟩
    · obtain ⟨g, hgA, hag⟩ := haA
      exact ⟨g, Or.inl hgA, hag⟩
  have hnoTwo : ¬ ∃ g ∈ F, 2 ≤ (G.neighborSet g ∩ T).ncard := by
    rintro ⟨g, hgF, hcard⟩
    have hsubsingle : (G.neighborSet g ∩ T).Subsingleton := by
      intro u hu v hv
      rcases hgF with hgA | hg2
      · have hzu : u ≠ z := fun h => hzA g hgA (h ▸ hu.1).symm
        have hzv : v ≠ z := fun h => hzA g hgA (h ▸ hv.1).symm
        have huT : u = z ∨ u = y ∨ u = a := by simpa [T] using hu.2
        have hvT : v = z ∨ v = y ∨ v = a := by simpa [T] using hv.2
        have hu' : u = y ∨ u = a := huT.resolve_left hzu
        have hv' : v = y ∨ v = a := hvT.resolve_left hzv
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
        · rfl
        · have hgf : g = f := hyuniq g hgA hu.1.symm
          exact absurd (hgf ▸ hv.1) hfa
        · have hgf : g = f := hyuniq g hgA hv.1.symm
          exact absurd (hgf ▸ hu.1) hfa
        · rfl
      · have hg : g = x₂ := by simpa using hg2
        subst g
        have hu' : u = z := by
          simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          rcases hu.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hu.1.symm hyx₂
          · exact absurd hu.1 hx₂a
        have hv' : v = z := by
          simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hv.1.symm hyx₂
          · exact absurd hv.1 hx₂a
        exact hu'.trans hv'.symm
    have hle : (G.neighborSet g ∩ T).ncard ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).mpr hsubsingle
    omega
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFsub hcatch with
    href | htwo
  · obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, hTeq, hBsub, hreff⟩ := href
    have hzT : z ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have hyT : y ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have haT : a ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨bz, hbzB, hzbz, hbzonly⟩ := reflection_partner hreff hzT
    obtain ⟨byv, hbyB, hyby, hbyonly⟩ := reflection_partner hreff hyT
    obtain ⟨g, hgB, hag, hgonly⟩ := reflection_partner hreff haT
    have hbzF := hBsub hbzB
    have hbyF := hBsub hbyB
    have hgF := hBsub hgB
    have hbz : bz = x₂ := by
      rcases hbzF with hbzA | hbz2
      · exact absurd hzbz (hzA bz hbzA)
      · simpa using hbz2
    have hby : byv = f := by
      rcases hbyF with hbyA | hby2
      · exact hyuniq byv hbyA hyby
      · have he : byv = x₂ := by simpa using hby2
        exact absurd (he ▸ hyby) hyx₂
    have hzg : ¬ G.Adj z g := hgonly z (by rw [← hTeq]; simp [T]) hzne_a
    have hyg : ¬ G.Adj y g := hgonly y (by rw [← hTeq]; simp [T]) hyne_a
    have hg2 : g ≠ x₂ := by
      intro he
      exact hzg (he ▸ hzx₂)
    have hgA : g ∈ A := by
      rcases hgF with h | h
      · exact h
      · exact absurd (by simpa using h) hg2
    have hgf : g ≠ f := by
      intro he
      exact hyg (he ▸ hyf)
    have hbzg : bz ≠ g := by intro he; exact hg2 (he.symm.trans hbz)
    have hbyg : byv ≠ g := by intro he; exact hgf (he.symm.trans hby)
    have h2g : G.Adj x₂ g := by
      rw [← hbz]
      exact hreff.2.1.2 bz hbzB g hgB hbzg
    have hfg : G.Adj f g := by
      rw [← hby]
      exact hreff.2.1.2 byv hbyB g hgB hbyg
    have hbg : ¬ G.Adj b g := by
      intro hbg
      exact hnoc g hgA ⟨hag.symm, hbg.symm⟩
    exact ⟨g, ⟨hgA, by simpa using hgf⟩, hag, h2g, hfg, hyg, hbg⟩
  · exact (hnoTwo htwo).elim

/-- Claim **(9)** of the printed proof: *"There is no connected `F ⊆ A` containing
neighbours of all of `x₀, x₁, x₂` except `A` itself."* -/
theorem claim9 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y) :
    ∀ F : Set V, F ⊆ A → ConnectedSet G F →
      (∃ a ∈ F, G.Adj (x 0) a) → (∃ a ∈ F, G.Adj (x 1) a) → (∃ a ∈ F, G.Adj (x 2) a) →
      F = A := by
  classical
  -- The printed proof derives *"`y` is not adjacent to `x₂`"* from the minimality of its
  -- own choice of `A`.  The project's `GoodA` carries one extra clause, so that derivation
  -- is unavailable and the case `G.Adj (x 2) y` has to be split off; see the module header
  -- of `Thm192Claim9YAdjX2` and `lean_workspace/REPORT.md`.
  by_cases h2y : G.Adj (x 2) y
  · exact Thm192Claim9YAdjX2.claim9_of_x2_adj_y G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
      hY0 A hA hAmin hcex h2y
  · exact Thm192Claim9NotAdjX2.claim9_of_not_x2_adj_y G hG z A₀ hframe x hws Y hHyp ih
      y hyY hyz hY0 A hA hAmin hcex h2y

end Workspace.ProofLemmas.Thm192Claim9
