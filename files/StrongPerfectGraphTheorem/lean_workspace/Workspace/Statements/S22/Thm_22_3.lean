import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Statements.S22.Thm_22_2
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelSystemBasics

/-!
# 22.3 — an optimal wheel has no kite

PAPER (printed p. 138), the whole printed proof:

> *"Assume `y` is a kite for `(C, Y)`.  Let `x₀-z-x₁` be a subpath of `C`, all `Y`-complete and
> adjacent to `y`.  Let `A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a wheel system with respect to
> `(z, A₀)`, and `x₀, x₁` are `Y ∪ {y}`-complete.  Thus every member of `Y ∪ {y}` has a
> neighbour in `A₀`, and yet there is no wheel with hub `Y ∪ {y}`, contrary to 22.2 with
> `s = 1`.  This proves 22.3."*

The Lean proof follows it sentence for sentence:

| printed sentence | Lean |
|---|---|
| *"Let `x₀-z-x₁` be a subpath of `C`, all `Y`-complete and adjacent to `y`"* | `KiteTailBasics.kite_spec` |
| *"so `x₀, x₁` is a wheel system with respect to `(z, A₀)`"* | `KiteTailBasics.isFrame_rim_minus`, `KiteTailBasics.isWheelSystem_rim_pair` |
| *"`x₀, x₁` are `Y ∪ {y}`-complete"* | `KiteTailBasics.vertexComplete_union_singleton` |
| *"every member of `Y ∪ {y}` has a neighbour in `A₀`"* | `KiteTailBasics.exists_hub_nbr_outside` (for `Y`), `KiteTailBasics.kite_exists_nbr_outside` (for `y`), pushed into `A₁` by `KiteTailBasics.rim_minus_subset_wheelSystemA` |
| *"there is no wheel with hub `Y ∪ {y}`"* | `KiteTailBasics.no_wheel_hub_union_singleton` (this is the only use of optimality) |
| *"contrary to 22.2 with `s = 1`"* | `thm_22_2 … (s := 1)`, whose conclusion asserts `1 ≤ r < 1` |

Two steps the paper leaves implicit and that the Lean proof has to supply:

* `Y ∪ {y}` is **anticonnected**: `y` is not `Y`-complete, so it has a non-neighbour in `Y`,
  i.e. a `Ḡ`-neighbour (`KiteTailBasics.anticonnectedSet_union_singleton`).
* 22.2's hypothesis is *"at most one member of `Y` has no neighbour in `A₁`"*; here the set of
  such members is **empty**, since every member has a neighbour in `A₀ ⊆ A₁`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S22

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **22.3** (printed p. 136).

PAPER: *"Let `G ∈ F₈`, not admitting a balanced skew partition, and let `(C, Y)` be
an optimal wheel in `G`.  Then there is no kite for `(C, Y)`."*

Encoding notes: `OptimalWheel G C Y` is §22's *optimal wheel* (*"if `(C, Y)` is a
wheel in `G`, and there is no wheel `(C', Y')` with `Y ⊂ Y'`"*) and `IsKite G C Y v`
is §22's *kite* (*"a vertex `y ∈ V(G) \ (Y ∪ V(C))`, not `Y`-complete, that has at
least four neighbours in `C`, three of which are consecutive and `Y`-complete"*);
*"there is no kite for `(C, Y)`"* quantifies over all vertices of `G`. -/
theorem thm_22_3 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y) :
    ¬ ∃ v : V, IsKite G C Y v := by
  rintro ⟨y, hkite⟩
  -- The wheel `(C, Y)`.
  have hwheel : IsWheel G C Y := KiteTailBasics.optimalWheel_isWheel hopt
  have hC : IsHoleList G C := KiteTailBasics.wheel_isHoleList hwheel
  have hlen5 : 5 ≤ C.length := by
    have := KiteTailBasics.wheel_six_le_length hwheel; omega
  -- "Let `x₀-z-x₁` be a subpath of `C`, all `Y`-complete and adjacent to `y`."
  obtain ⟨x₀, z, x₁, hz, hnb, h0Y, hzY, h1Y, hy0, hyz, hy1⟩ :=
    KiteTailBasics.kite_spec hkite
  -- Package `x₀, x₁` as the first two terms of a sequence `x : ℕ → V`.
  obtain ⟨x, hx0, hx1⟩ : ∃ x : ℕ → V, x 0 = x₀ ∧ x 1 = x₁ :=
    ⟨fun i => if i = 0 then x₀ else x₁, by simp, by simp⟩
  have hnb' : KiteTailBasics.IsRimNeighbours G C z (x 0) (x 1) := by rw [hx0, hx1]; exact hnb
  have hx₀C : x₀ ∈ C := hnb.2.1
  have hx₁C : x₁ ∈ C := hnb.2.2.1
  -- "Let `A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a wheel system with respect to `(z, A₀)`."
  have hframe : IsFrame G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) :=
    KiteTailBasics.isFrame_rim_minus hC hz hnb'
  have hws : IsWheelSystem G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1 :=
    KiteTailBasics.isWheelSystem_rim_pair hC hlen5 hz x hnb'
  -- The enlarged hub `Y ∪ {y}`.
  have hyY : y ∉ Y := KiteTailBasics.kite_notMem_hub hkite
  have hYne : (Y ∪ ({y} : Set V)).Nonempty := ⟨y, Or.inr rfl⟩
  have hYanti : AnticonnectedSet G (Y ∪ ({y} : Set V)) :=
    KiteTailBasics.anticonnectedSet_union_singleton
      (KiteTailBasics.wheel_hub_anticonnected hwheel)
      (KiteTailBasics.kite_not_vertexComplete hkite)
  -- No member of `Y ∪ {y}` lies on the rim.
  have hnotC : ∀ w : V, w ∈ Y ∪ ({y} : Set V) → w ∉ C := by
    rintro w (hwY | hwy)
    · exact fun hwC => KiteTailBasics.wheel_rim_notMem_hub hwheel w hwC hwY
    · rw [Set.mem_singleton_iff] at hwy
      subst hwy
      exact KiteTailBasics.kite_notMem_rim hkite
  have hYdisj : ∀ w ∈ Y ∪ ({y} : Set V),
      w ∉ ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) ∧ w ≠ z ∧ ∀ i ≤ 1, w ≠ x i := by
    intro w hw
    have hwC := hnotC w hw
    refine ⟨fun hm => hwC (KiteTailBasics.mem_rim_minus.mp hm).1, ?_, ?_⟩
    · rintro rfl; exact hwC hz
    · intro i hi
      interval_cases i
      · rw [hx0]; rintro rfl; exact hwC hx₀C
      · rw [hx1]; rintro rfl; exact hwC hx₁C
  -- "`x₀, x₁` are `Y ∪ {y}`-complete" (and so is `z`).
  have hzY' : VertexComplete G z (Y ∪ ({y} : Set V)) :=
    KiteTailBasics.vertexComplete_union_singleton hzY hyz.symm
  have hxY : ∀ i ≤ 1, VertexComplete G (x i) (Y ∪ ({y} : Set V)) := by
    intro i hi
    interval_cases i
    · rw [hx0]; exact KiteTailBasics.vertexComplete_union_singleton h0Y hy0.symm
    · rw [hx1]; exact KiteTailBasics.vertexComplete_union_singleton h1Y hy1.symm
  -- "Thus every member of `Y ∪ {y}` has a neighbour in `A₀`" — and `A₀ ⊆ A₁`.
  have hsub := KiteTailBasics.rim_minus_subset_wheelSystemA hC hlen5 hz x hnb'
  have hYAs : ∀ w ∈ Y ∪ ({y} : Set V),
      ∃ a ∈ wheelSystemA G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1, G.Adj w a := by
    intro w hw
    rcases hw with hwY | hwy
    · obtain ⟨v, hvC, hadj, hv1, hv2, hv3⟩ :=
        KiteTailBasics.exists_hub_nbr_outside hwheel hwY z (x 0) (x 1)
      exact ⟨v, hsub (KiteTailBasics.mem_rim_minus.mpr ⟨hvC, hv1, hv2, hv3⟩), hadj⟩
    · rw [Set.mem_singleton_iff] at hwy
      subst hwy
      obtain ⟨v, hvC, hadj, hv1, hv2, hv3⟩ :=
        KiteTailBasics.kite_exists_nbr_outside hkite z (x 0) (x 1)
      exact ⟨v, hsub (KiteTailBasics.mem_rim_minus.mpr ⟨hvC, hv1, hv2, hv3⟩), hadj⟩
  -- Hence the set 22.2 asks to be a subsingleton is in fact empty.
  have hone : Set.Subsingleton
      {w ∈ Y ∪ ({y} : Set V) | VertexAnticomplete G w
        (wheelSystemA G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1)} := by
    intro a ha b hb
    exfalso
    obtain ⟨v, hv, hadj⟩ := hYAs a ha.1
    exact ha.2 v hv hadj
  -- "and yet there is no wheel with hub `Y ∪ {y}`" — the one use of optimality.
  have hnowheel : ¬ ∃ C' : List V, IsWheel G C' (Y ∪ ({y} : Set V)) :=
    KiteTailBasics.no_wheel_hub_union_singleton hopt hyY
  -- "contrary to 22.2 with `s = 1`": 22.2 produces `r` with `1 ≤ r < 1`.
  obtain ⟨r, hr1, hr2, -⟩ :=
    thm_22_2 G hG hbsp z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) hframe x 1 hws
      (Y ∪ ({y} : Set V)) hYdisj hYne hYanti hzY' hxY hYAs hone hnowheel
  omega


end SPGT

end Workspace.Statements.S22
