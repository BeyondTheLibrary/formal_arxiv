import Workspace.ProofLemmas.Thm232FinalRim
import Workspace.ProofLemmas.Thm232ClosingGeometry

/-! The final contradiction of 23.2, in either orientation of the rim. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232Final

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “But then the hole formed by the union of `R` and
the path `C \ x₀` is the rim of an odd wheel with hub `Y`, a contradiction.”

We build this hole using `RimSurgery`.  The surviving edges already make it a wheel
with two fewer complete edges, so the opening minimum choice gives the contradiction. -/
theorem closing (G : SimpleGraph V) (C : List V) (Y : Set V)
    (hw : IsWheel G C Y)
    (hmin : ∀ D : List V, IsWheel G D Y → yEdgeCount G Y C ≤ yEdgeCount G Y D)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁)
    (hnbc : IsRimNeighbours G C c₂ c₁ c₃)
    (horient : x₀ = c₃ ∨ x₁ = c₁)
    (Q : List V) (hQ : IsPathFrom G Q z c₂)
    (hQY : ∀ v ∈ SPGT.interior Q, v ∉ Y)
    (hQnc : ∀ v ∈ SPGT.interior Q, ¬ VertexComplete G v Y)
    (hQiso : ∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = z ∨ c = c₂) :
    False := by
  have hzC := (hole_triple hw.1.1 ⟨k, hpre1⟩).2.1
  have hcC := (hole_triple hw.1.1 ⟨k + d, hpre2⟩).2.1
  have hzc := Thm232ClosingGeometry.middles_ne hw.1.1 hd2 hdn hpre1 hpre2
  rcases horient with he | he
  · have hnbc' : IsRimNeighbours G C c₂ c₁ x₀ := by rwa [he]
    exact Thm232FinalRim.common_end_absurd hw hmin hzC hcC hzc hnb hnbc'
      h0Y hzY hc2Y h1Y hc1Y hQ hQY hQnc hQiso
  · have hnbc' : IsRimNeighbours G C c₂ c₃ x₁ := by
      rw [he]
      exact isRimNeighbours_symm hnbc
    exact Thm232FinalRim.common_end_absurd hw hmin hzC hcC hzc
      (isRimNeighbours_symm hnb) hnbc' h1Y hzY hc2Y h0Y hc3Y hQ hQY hQnc hQiso

end Workspace.ProofLemmas.Thm232Final
