import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.NonCutVertices
import Workspace.ProofLemmas.Thm192Setup

/-!
# Claim (1) of the printed proof of 19.2

PAPER (printed p. 118):

> **(1)** *There exists `y ∈ Y` adjacent to `z` and with a neighbour in `A`, such that
> `Y \ {y}` is empty or anticonnected.*
>
> *For if `|Y| = 1`, let `Y = {y}`; then since `x₂` is not `Y`-complete it follows that
> `y` is nonadjacent to `x₂`, and therefore is adjacent to `z` and has a neighbour in `A`
> and the claim holds.  So assume `|Y| > 1`, and choose distinct `y₁, y₂ ∈ Y` such that
> `Y \ {yᵢ}` is anticonnected (`i = 1, 2`).  Not both `y₁, y₂` is the unique nonneighbour
> of `x₂` in `Y`; so we may assume that `x₂` is not `Y \ {y₂}`-complete.  By the minimality
> of `|Y|`, `z` is `Y \ {y₂}`-complete and there is a `Y \ {y₂}`-complete vertex in `A`;
> and in particular, `y₁` is adjacent to `z` and has a neighbour in `A`, so we may set
> `y = y₁`.  This proves (1).*

## The repair, and why it changes nothing

The printed sentence *"By the minimality of `|Y|`, `z` is `Y \ {y₂}`-complete and there is
a `Y \ {y₂}`-complete vertex in `A`"* is **wrong as printed**: minimality of `|Y|` yields
19.2's conclusion at `Y \ {y₂}`, whose wheel has rim in `{x₀,x₁,z} ∪ A₁`, so the complete
vertex lands in **`A₁`, not in the minimal `A ⊆ A₁`** (which at this point of the argument
has not even been chosen in a way that could contain it).

The repair does not touch the argument: it takes the paper's two extremal choices in the
opposite order.  Claim (1) is proved with `A₁`; only afterwards is `A ⊆ A₁` chosen minimal
subject to the printed properties *and* *"`y` has a neighbour in `A`"*.  `A₁` still
satisfies all of them (`Thm192Setup.goodA_A1`), and claim (3) presupposes exactly this,
since it lists `y` alongside `x₀,x₁,x₂` among the vertices `F` must have neighbours of.
See the header of `Workspace.ProofLemmas.Thm192Setup` and `AMBIGUITIES.md`.

The upgrade from *"there is a `Y \ {y₂}`-complete vertex in `A₁`"* to what the wheel
literally gives is `Thm192Setup.wheel_complete_vertex_in_A1`: a wheel supplies two
**disjoint** `Y \ {y₂}`-complete edges of its rim, i.e. four distinct complete rim
vertices, and `{x₀,x₁,z}` has only three elements.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(1)** of the printed proof of 19.2: *"There exists `y ∈ Y` adjacent to `z` and
with a neighbour in `A`, such that `Y \ {y}` is empty or anticonnected."*

Stated with `A₁` in place of `A`; see the module header for why the two extremal choices
have to be taken in the opposite order to the printed one. -/
theorem claim1 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard) :
    ∃ y ∈ Y, G.Adj y z ∧ (∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj y a) ∧
      (Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y})) := by
  obtain ⟨hYsub, hYanti, hx0, hx1, hx2, hnb⟩ := hHyp
  have hAY : ∀ w ∈ Y, ¬ G.Adj w (x 2) → ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj w a :=
    fun w hw hnw => (hnb w hw hnw).1
  -- *"since `x₂` is not `Y`-complete it follows that `y` is nonadjacent to `x₂`"*
  obtain ⟨ystar, hystarY, hystar2⟩ :=
    exists_nonneighbour_x2 (A₀ := A₀) ⟨hYsub, hYanti, hx0, hx1, hx2, hnb⟩
  by_cases hsub : Y.Subsingleton
  · -- *"For if `|Y| = 1`, let `Y = {y}` …"*
    refine ⟨ystar, hystarY, (hnb ystar hystarY hystar2).2, hAY ystar hystarY hystar2, Or.inl ?_⟩
    ext w
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact fun hw => hsub hw hystarY
  · -- *"So assume `|Y| > 1`, and choose distinct `y₁, y₂ ∈ Y` such that `Y \ {yᵢ}`
    -- is anticonnected (`i = 1, 2`)."*
    obtain ⟨y1, hy1, y2, hy2, hne, hanti1, hanti2⟩ :=
      Workspace.ProofLemmas.NonCutVertices.exists_two_nonanticut hYanti hsub
    by_cases hc1 : ¬ G.Adj y1 (x 2)
    · exact ⟨y1, hy1, (hnb y1 hy1 hc1).2, hAY y1 hy1 hc1, Or.inr hanti1⟩
    by_cases hc2 : ¬ G.Adj y2 (x 2)
    · exact ⟨y2, hy2, (hnb y2 hy2 hc2).2, hAY y2 hy2 hc2, Or.inr hanti2⟩
    -- Both `y₁, y₂` are adjacent to `x₂`, so `ystar ∉ {y₁, y₂}` and `x₂` is not
    -- `Y \ {y₂}`-complete.  *"By the minimality of `|Y|`, `z` is `Y \ {y₂}`-complete
    -- and there is a `Y \ {y₂}`-complete vertex in `A`."*
    push_neg at hc1 hc2
    have hstar1 : ystar ≠ y1 := fun h => hystar2 (h ▸ hc1)
    have hstar2 : ystar ≠ y2 := fun h => hystar2 (h ▸ hc2)
    set Y' : Set V := Y \ {y2} with hY'
    have hstarY' : ystar ∈ Y' := ⟨hystarY, hstar2⟩
    have hY'sub : Y' ⊆ Y := fun w hw => hw.1
    have hcard : Y'.ncard < Y.ncard := by
      have h1 : Y'.ncard = Y.ncard - 1 := Set.ncard_diff_singleton_of_mem hy2
      have h2 : 0 < Y.ncard := (Set.ncard_pos (Set.toFinite Y)).mpr ⟨y2, hy2⟩
      omega
    have hHyp' : Hyp192 G z A₀ x Y' :=
      ⟨fun w hw => hYsub w (hY'sub hw), hanti2,
        fun w hw => hx0 w (hY'sub hw), fun w hw => hx1 w (hY'sub hw),
        fun hcon => hystar2 (hcon ystar hstarY').symm,
        fun w hw hw2 => hnb w (hY'sub hw) hw2⟩
    obtain ⟨hzY', C, hwheel, -, -, -, hCsub⟩ := ih.1 Y' hcard hHyp'
    have hy1Y' : y1 ∈ Y' := ⟨hy1, fun h => hne (h ▸ rfl)⟩
    refine ⟨y1, hy1, (hzY' y1 hy1Y').symm, ?_, Or.inr hanti1⟩
    -- PAPER: *"and there is a `Y \ {y₂}`-complete vertex in `A`; and in particular,
    -- `y₁` … has a neighbour in `A`"*.
    obtain ⟨a, haA1, haW⟩ :=
      wheel_complete_vertex_in_A1 (A₀ := A₀) (x := x) hwheel hCsub
    exact ⟨a, haA1, (haW y1 hy1Y').symm⟩

end Workspace.ProofLemmas.Thm192Claim1
