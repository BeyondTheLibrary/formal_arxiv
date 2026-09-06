import Workspace.ProofLemmas.Thm232FinalRim
import Workspace.ProofLemmas.Thm232ClosingGeometry
import Workspace.Types.Classes

/-! The final contradiction of 23.2 — the odd wheel of the last printed sentence — in
either orientation of the rim. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232Final

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “But then the hole formed by the union of `R` and
the path `C \ x₀` is the rim of an odd wheel with hub `Y`, a contradiction.”

We build this hole using `RimSurgery`.  On it, the segment through `z` is the single edge
`z`-`x₁`: the interior of `R` carries no `Y`-complete vertex, `x₀` has been deleted, and the
four `Y`-complete edges of `C` listed in `hexh` leave `x₁` no other `Y`-complete neighbour.
So the new wheel is odd, contrary to the no-odd-wheel clause of `G ∈ F₈`. -/
theorem closing (G : SimpleGraph V) (hG : InF8 G) (C : List V) (Y : Set V)
    (hw : IsWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
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
  · -- `x₀ = c₃`: the deleted vertex is `x₀`, and the four complete edges are
    -- `x₀z`, `zx₁`, `c₁c₂`, `c₂x₀`.
    subst he
    exact Thm232FinalRim.common_end_absurd hG hw hzC hcC hzc hnb hnbc
      h0Y hzY hc2Y h1Y hc1Y (fun a ha b hb hE => hexh a b ha hb hE) hQ hQY hQnc hQiso
  · -- `x₁ = c₁`: the same with the two sides of the rim exchanged.
    subst he
    refine Thm232FinalRim.common_end_absurd hG hw hzC hcC hzc
      (isRimNeighbours_symm hnb) (isRimNeighbours_symm hnbc) h1Y hzY hc2Y h0Y hc3Y
      ?_ hQ hQY hQnc hQiso
    intro a ha b hb hE
    rcases hexh a b ha hb hE with h | h | h | h
    · exact Or.inr (Or.inl (h.trans (Set.pair_comm x₀ z)))
    · exact Or.inl (h.trans (Set.pair_comm z x₁))
    · exact Or.inr (Or.inr (Or.inr (h.trans (Set.pair_comm x₁ c₂))))
    · exact Or.inr (Or.inr (Or.inl (h.trans (Set.pair_comm c₂ c₃))))

end Workspace.ProofLemmas.Thm232Final
