import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems

/-!
# Bookkeeping facts used by the proof of 20.1

Two routine facts that the published proof of 20.1 uses without comment.

* `wheel_hub_mono` — a wheel `(C, Y')` is also a wheel `(C, Y)` whenever
  `Y ⊆ Y'` and `Y` is itself nonempty and anticonnected.  This is exactly the
  authors' own remark after 20.2: *"There is some annoying wastage in 20.2; we
  produce a wheel with hub `Y ∪ {x₃}`, and all we use in proving 20.1 is that
  there is a wheel with hub `Y`."*

* `hub_avoids_frame_of_wheelSystem` — if `x₀,…,x_t` is a wheel system with
  `t ≥ 2`, `z ∉ Y`, and `x₀,…,x_{t−1}` are all `Y`-complete, then
  `Y ⊆ V(G) \ (A₀ ∪ {z})`.  Indeed a vertex `y ∈ Y ∩ A₀` would be adjacent to
  both `x₀` and `x₁`, i.e. `X₁`-complete, contrary to the defining property of a
  frame recorded in `IsWheelSystem`.  This is the side condition that the printed
  proof of 20.1 tacitly assumes when it feeds the set `Y'` produced by 20.3 back
  into the induction (see the encoding note on 20.3).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm201HubBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `VertexComplete` is monotone downward in its set argument. -/
theorem vertexComplete_mono {G : SimpleGraph V} {v : V} {Y Y' : Set V}
    (hsub : Y ⊆ Y') (h : VertexComplete G v Y') : VertexComplete G v Y :=
  fun y hy => h y (hsub hy)

/-- `EdgeComplete` is monotone downward in its set argument. -/
theorem edgeComplete_mono {G : SimpleGraph V} {a b : V} {Y Y' : Set V}
    (hsub : Y ⊆ Y') (h : EdgeComplete G Y' a b) : EdgeComplete G Y a b :=
  ⟨h.1, vertexComplete_mono hsub h.2.1, vertexComplete_mono hsub h.2.2⟩

/-- A wheel with hub `Y'` is a wheel with hub any nonempty anticonnected
`Y ⊆ Y'`.  (The paper's "annoying wastage" remark, printed p. 126.) -/
theorem wheel_hub_mono {G : SimpleGraph V} {C : List V} {Y Y' : Set V}
    (hsub : Y ⊆ Y') (hne : Y.Nonempty) (hanti : AnticonnectedSet G Y)
    (hW : IsWheel G C Y') : IsWheel G C Y := by
  obtain ⟨hhole, ⟨-, -, hdisj⟩, a, b, c, d, ha, hb, hc, hd, hab, hcd, h1, h2, h3, h4⟩ := hW
  refine ⟨hhole, ⟨hne, hanti, fun v hv hvY => hdisj v hv (hsub hvY)⟩, a, b, c, d, ha, hb, hc,
    hd, edgeComplete_mono hsub hab, edgeComplete_mono hsub hcd, h1, h2, h3, h4⟩

/-- If `x₀,…,x_t` is a wheel system (with `t ≥ 2`), `z ∉ Y`, and `x₀,…,x_{t−1}`
are all `Y`-complete, then `Y ⊆ V(G) \ (A₀ ∪ {z})`. -/
theorem hub_avoids_frame_of_wheelSystem {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (hws : IsWheelSystem G z A₀ x t) (ht : 2 ≤ t)
    (hzY : z ∉ Y) (hcomp : ∀ i < t, VertexComplete G (x i) Y) :
    ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z := by
  have hA₀ : ∀ a ∈ A₀, ¬ VertexComplete G a ({x 0, x 1} : Set V) := hws.2.2.2.1.2.2
  intro y hy
  refine ⟨?_, ?_⟩
  · intro hyA
    refine hA₀ y hyA ?_
    intro w hw
    rcases hw with hw | hw
    · subst hw
      exact ((hcomp 0 (by omega)) y hy).symm
    · simp only [Set.mem_singleton_iff] at hw
      subst hw
      exact ((hcomp 1 (by omega)) y hy).symm
  · rintro rfl
    exact hzY hy

end Workspace.ProofLemmas.Thm201HubBasics
