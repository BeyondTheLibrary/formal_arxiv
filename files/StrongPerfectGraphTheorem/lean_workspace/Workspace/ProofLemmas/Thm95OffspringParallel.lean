import Workspace.ProofLemmas.Thm95OffspringFacts

/-!
# The first bullet of 9.5(1): `S₀` is parallel or co-parallel with each offspring

PAPER (9.5(1), printed p. 52): *"• for all `j` with `1 ≤ j ≤ n`, `S₀` is parallel or
antiparallel with the offspring of `Tⱼ`"*.

Which of the two it is, is determined by the side: `S₀ = ({f₁}, {f₂,…,f_{k-1}}, {f_k})` is
parallel with the offspring `Mⱼ` belonging to `U` (the neighbours of `f₁`) and co-parallel with
the offspring `Nⱼ` belonging to `V` (the neighbours of `f_k`).  Both statements are read off
from the consequences of 9.3.3 listed in `Thm95Offspring.offspring_striation`, once the paper's
*"every `Tⱼ`-antirung has one end in `U` and the other in `V`"* is available; that sentence is
the hypothesis `hsplit` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringParallel

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} {G : SimpleGraph V}

section

variable {Tx : Set V × Set V × Set V} {R : List V} {r s : V}

/-- A vertex of the offspring belonging to `W` lying in `Y` is the last vertex of an antirung
whose first vertex lies in `W`. -/
theorem exists_antirung_of_mem_Y (hTx : IsAntistrip G Tx) {W : Set V} {v : V}
    (hv : v ∈ offVerts G Tx W) (hvY : v ∈ Tx.2.2) :
    ∃ (Q : List V) (x : V), IsSRung Gᶜ Tx Q ∧ IsPathFrom Gᶜ Q x v ∧ x ∈ W := by
  obtain ⟨Q, hQ, hvQ, x, hx, hxW⟩ := hv
  obtain ⟨X, Z, Y⟩ := Tx
  obtain ⟨a, b, hpath, ha, hb, htail, hlast, hint⟩ := id hQ
  have hax : a = x := Option.some.inj (hpath.2.1.symm.trans hx)
  have hbv : b = v :=
    Option.some.inj (hpath.2.2.symm.trans (last_of_mem_Y hTx hQ hvQ hvY))
  exact ⟨Q, x, hQ, hax ▸ hbv ▸ hpath, hxW⟩

/-- **PAPER (9.5(1), p. 52, first bullet).**  `S₀` is parallel with the offspring belonging to
the neighbours of `f₁`. -/
theorem parallel_newStrip (hTx : IsAntistrip G Tx)
    (hsplit : ∀ (Q : List V) (x y : V), IsSRung Gᶜ Tx Q → IsPathFrom Gᶜ Q x y →
      (G.Adj r x ∧ G.Adj s y) ∨ (G.Adj s x ∧ G.Adj r y))
    (hZx : ∀ z ∈ Tx.2.1, G.Adj r z ∧ G.Adj s z)
    (hXYx : ∀ z ∈ Tx.1 ∪ Tx.2.2, ¬ (G.Adj r z ∧ G.Adj s z))
    (hintx : Anticomplete G {v : V | v ∈ SPGT.interior R} (stripVertices Tx)) :
    ParallelStripAntistrip G (newStrip R r s)
      (offspring G Tx {z : V | G.Adj r z}) := by
  have hY : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj r z} → v ∈ Tx.2.2 → G.Adj s v := by
    intro v hv hvY
    obtain ⟨Q, x, hQ, hpath, hxW⟩ := exists_antirung_of_mem_Y hTx hv hvY
    rcases hsplit Q x v hQ hpath with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · obtain ⟨a, b, hpath', ha, -, -, -, -⟩ := id hQ
      have hax : a = x := Option.some.inj (hpath'.2.1.symm.trans hpath.2.1)
      exact absurd ⟨hxW, h⟩ (hXYx x (Or.inl (hax ▸ ha)))
  have hX : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj r z} → v ∈ Tx.1 → G.Adj r v :=
    fun v hv hvX => mem_W_of_mem_offVerts_X hTx hv hvX
  have hnoint : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj r z} →
      ∀ w ∈ SPGT.interior R, ¬ G.Adj v w :=
    fun v hv w hw hadj => hintx w hw v (offVerts_subset Tx _ hv) hadj.symm
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro v rfl w (hw | hw)
    · exact hX w hw.1 hw.2
    · exact (hZx w hw.2).1
  · rintro v rfl w (hw | hw)
    · exact hY w hw.1 hw.2
    · exact (hZx w hw.2).2
  · rintro x hx w (rfl | hw) hadj
    · exact hXYx x (Or.inl hx.2) ⟨hX x hx.1 hx.2, hadj.symm⟩
    · exact hnoint x hx.1 w hw hadj
  · rintro y hy w (rfl | hw) hadj
    · exact hXYx y (Or.inr hy.2) ⟨hadj.symm, hY y hy.1 hy.2⟩
    · exact hnoint y hy.1 w hw hadj

/-- **PAPER (9.5(1), p. 52, first bullet).**  `S₀` is co-parallel with the offspring belonging
to the neighbours of `f_k`. -/
theorem coParallel_newStrip (hTx : IsAntistrip G Tx)
    (hsplit : ∀ (Q : List V) (x y : V), IsSRung Gᶜ Tx Q → IsPathFrom Gᶜ Q x y →
      (G.Adj r x ∧ G.Adj s y) ∨ (G.Adj s x ∧ G.Adj r y))
    (hZx : ∀ z ∈ Tx.2.1, G.Adj r z ∧ G.Adj s z)
    (hXYx : ∀ z ∈ Tx.1 ∪ Tx.2.2, ¬ (G.Adj r z ∧ G.Adj s z))
    (hintx : Anticomplete G {v : V | v ∈ SPGT.interior R} (stripVertices Tx)) :
    CoParallel G (newStrip R r s) (offspring G Tx {z : V | G.Adj s z}) := by
  have hY : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj s z} → v ∈ Tx.2.2 → G.Adj r v := by
    intro v hv hvY
    obtain ⟨Q, x, hQ, hpath, hxW⟩ := exists_antirung_of_mem_Y hTx hv hvY
    rcases hsplit Q x v hQ hpath with ⟨h, -⟩ | ⟨-, h⟩
    · obtain ⟨a, b, hpath', ha, -, -, -, -⟩ := id hQ
      have hax : a = x := Option.some.inj (hpath'.2.1.symm.trans hpath.2.1)
      exact absurd ⟨h, hxW⟩ (hXYx x (Or.inl (hax ▸ ha)))
    · exact h
  have hX : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj s z} → v ∈ Tx.1 → G.Adj s v :=
    fun v hv hvX => mem_W_of_mem_offVerts_X hTx hv hvX
  have hnoint : ∀ v, v ∈ offVerts G Tx {z : V | G.Adj s z} →
      ∀ w ∈ SPGT.interior R, ¬ G.Adj v w :=
    fun v hv w hw hadj => hintx w hw v (offVerts_subset Tx _ hv) hadj.symm
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro v rfl w (hw | hw)
    · exact hY w hw.1 hw.2
    · exact (hZx w hw.2).1
  · rintro v rfl w (hw | hw)
    · exact hX w hw.1 hw.2
    · exact (hZx w hw.2).2
  · rintro y hy w (rfl | hw) hadj
    · exact hXYx y (Or.inr hy.2) ⟨hY y hy.1 hy.2, hadj.symm⟩
    · exact hnoint y hy.1 w hw hadj
  · rintro x hx w (rfl | hw) hadj
    · exact hXYx x (Or.inl hx.2) ⟨hadj.symm, hX x hx.1 hx.2⟩
    · exact hnoint x hx.1 w hw hadj

end

/-- Monotonicity of `IsTwist` in the two antistrips: an offspring keeps the twist of its
parent. -/
theorem isTwist_mono {S₁ S₂ T₁ T₂ T₁' T₂' : Set V × Set V × Set V}
    (h : IsTwist G S₁ S₂ T₁ T₂)
    (h1 : T₁'.1 ⊆ T₁.1) (h2 : T₁'.2.1 ⊆ T₁.2.1) (h3 : T₁'.2.2 ⊆ T₁.2.2)
    (k1 : T₂'.1 ⊆ T₂.1) (k2 : T₂'.2.1 ⊆ T₂.2.1) (k3 : T₂'.2.2 ⊆ T₂.2.2) :
    IsTwist G S₁ S₂ T₁' T₂' := by
  have hpar1 : ∀ Sx, ParallelStripAntistrip G Sx T₁ → ParallelStripAntistrip G Sx T₁' :=
    fun Sx h => parallel_mono h h1 h2 h3
  have hcop1 : ∀ Sx, CoParallel G Sx T₁ → CoParallel G Sx T₁' :=
    fun Sx h => coParallel_mono h h1 h2 h3
  have hpar2 : ∀ Sx, ParallelStripAntistrip G Sx T₂ → ParallelStripAntistrip G Sx T₂' :=
    fun Sx h => parallel_mono h k1 k2 k3
  have hcop2 : ∀ Sx, CoParallel G Sx T₂ → CoParallel G Sx T₂' :=
    fun Sx h => coParallel_mono h k1 k2 k3
  rcases h with ⟨hag, hd⟩ | ⟨hag, hd⟩
  · exact Or.inl ⟨hag.imp (fun h => ⟨hpar1 _ h.1, hpar1 _ h.2⟩)
      (fun h => ⟨hcop1 _ h.1, hcop1 _ h.2⟩),
      hd.imp (fun h => ⟨hpar2 _ h.1, hcop2 _ h.2⟩) (fun h => ⟨hcop2 _ h.1, hpar2 _ h.2⟩)⟩
  · exact Or.inr ⟨hag.imp (fun h => ⟨hpar2 _ h.1, hpar2 _ h.2⟩)
      (fun h => ⟨hcop2 _ h.1, hcop2 _ h.2⟩),
      hd.imp (fun h => ⟨hpar1 _ h.1, hcop1 _ h.2⟩) (fun h => ⟨hcop1 _ h.1, hpar1 _ h.2⟩)⟩

/-- Monotonicity of `IsTwist` for the offspring of two antistrips. -/
theorem isTwist_offspring {S₁ S₂ T₁ T₂ : Set V × Set V × Set V} (W₁ W₂ : Set V)
    (h : IsTwist G S₁ S₂ T₁ T₂) :
    IsTwist G S₁ S₂ (offspring G T₁ W₁) (offspring G T₂ W₂) :=
  isTwist_mono h (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)
    (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)

end Workspace.ProofLemmas.Thm95OffspringParallel
