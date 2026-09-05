import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.Statements.S16.Thm_16_1
import Workspace.Statements.S22.Thm_22_3

/-!
# 23.2, claim (4): the rim-neighbours of `v₁`

PAPER (23.2, claim (4), printed p. 140):

> *"… it follows that `v₁` is adjacent to `c₂, c₃`. … By 16.1, there are three consecutive
> vertices in `C`, all `Y`-complete and adjacent to `v₁`.  By 22.3, `v₁` has no other
> neighbours in `C`.  Hence `x₁ = c₁` and the neighbours of `v₁` in `C` are `c₁, c₂, c₃`."*

`nbrs_subset` is that passage, in the orientation-free form the proof of claim (4) uses it:
a vertex `v` outside an optimal wheel, adjacent to two consecutive `Y`-complete rim vertices
`c₂` and `f`, has all its rim-neighbours among `e, c₂, f`, where `e, f` are the two rim
neighbours of `c₂`.

16.1 offers three outcomes for `v`.  The first names the two rim neighbours of `v`
explicitly, and they must then be `c₂, f`.  The third enlarges the hub, contrary to
optimality.  In the second, a fourth rim neighbour would make `v` a kite, contrary to 22.3, so
the three consecutive `Y`-complete vertices are all the rim neighbours there are; the middle
one is `c₂` (the hypothesis `hfedge`, which is claim (1), pins it down), so the other two are
the rim neighbours `e, f` of `c₂`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232Claim4Neighbours

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Four distinct rim vertices adjacent to `v` make *"at least four neighbours in `C`"*. -/
private theorem four_neighbours {G : SimpleGraph V} {C : List V}
    {v p₁ p₂ p₃ r : V} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hp₁C : p₁ ∈ C) (hp₂C : p₂ ∈ C) (hp₃C : p₃ ∈ C) (hrC : r ∈ C)
    (hvp₁ : G.Adj v p₁) (hvp₂ : G.Adj v p₂) (hvp₃ : G.Adj v p₃) (hvr : G.Adj v r)
    (hr₁ : r ≠ p₁) (hr₂ : r ≠ p₂) (hr₃ : r ≠ p₃) :
    4 ≤ {c : V | c ∈ C ∧ G.Adj v c}.ncard := by
  have hcard : ({p₁, p₂, p₃, r} : Set V).ncard = 4 := by
    simp [h12, h13, h23, Ne.symm hr₁, Ne.symm hr₂, Ne.symm hr₃]
  have hsub : ({p₁, p₂, p₃, r} : Set V) ⊆ {c : V | c ∈ C ∧ G.Adj v c} := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨hp₁C, hvp₁⟩
    · exact ⟨hp₂C, hvp₂⟩
    · exact ⟨hp₃C, hvp₃⟩
    · exact ⟨hrC, hvr⟩
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

private theorem mem_rim_of_block {G : SimpleGraph V} {C : List V} {a b c : V}
    (hblock : ∃ k : ℕ, [a, b, c] <+: C.rotate k ∨ [c, b, a] <+: C.rotate k) :
    a ∈ C ∧ b ∈ C ∧ c ∈ C := by
  obtain ⟨k, h | h⟩ := hblock
  · exact ⟨List.mem_rotate.mp (h.subset (by simp)),
      List.mem_rotate.mp (h.subset (by simp)), List.mem_rotate.mp (h.subset (by simp))⟩
  · exact ⟨List.mem_rotate.mp (h.subset (by simp)),
      List.mem_rotate.mp (h.subset (by simp)), List.mem_rotate.mp (h.subset (by simp))⟩

/-- **PAPER (23.2, claim (4)):** *"By 16.1, there are three consecutive vertices in `C`, all
`Y`-complete and adjacent to `v₁`.  By 22.3, `v₁` has no other neighbours in `C`."*

`e, f` are the two rim neighbours of `c₂`, and `hfedge` is the consequence of claim (1) that
`c₂` is the only `Y`-complete rim neighbour of `f`. -/
theorem nbrs_subset {G : SimpleGraph V} (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (v e c₂ f : V) (hvC : v ∉ C) (hvY : v ∉ Y) (hvNC : ¬ VertexComplete G v Y)
    (hc2C : c₂ ∈ C) (hnbc : IsRimNeighbours G C c₂ f e)
    (hc2Y : VertexComplete G c₂ Y) (hfY : VertexComplete G f Y)
    (hvc2 : G.Adj v c₂) (hvf : G.Adj v f)
    (hfedge : ∀ x ∈ C, G.Adj f x → VertexComplete G x Y → x = c₂) :
    ∀ w ∈ C, G.Adj v w → w = e ∨ w = c₂ ∨ w = f := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hBerge : Berge G := hG.1.1.1.1.1
  have hfC : f ∈ C := hnbc.2.1
  have heC : e ∈ C := hnbc.2.2.1
  have hc2f : G.Adj c₂ f := hnbc.2.2.2.1
  have hc2e : G.Adj c₂ e := hnbc.2.2.2.2.1
  have hfe : f ≠ e := hnbc.1
  have hnokite : ¬ ∃ q : V, IsKite G C Y q :=
    _root_.Workspace.Statements.S22.SPGT.thm_22_3 G hG hbsp C Y hopt
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  have hopp : OppositeWheelParity G C Y c₂ f :=
    ⟨hc2f.ne, hc2C, hfC,
      OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hC heven hc2C hfC
        ⟨hc2f, hc2Y, hfY⟩⟩
  have htri := _root_.Workspace.Statements.S16.SPGT.thm_16_1
    G hG.1.1 C Y hw v hvC hvY hvNC c₂ f hvc2 hvf hopp
  rcases htri.2 with ⟨a₁, a₂, ha₁a₂, hneighbors, -, -, -⟩ |
      ⟨p₁, p₂, p₃, hP, hblock, hp₁, hp₂, hp₃, -⟩ | hlarger
  · -- the two rim neighbours of `v` are named: they are `c₂` and `f`
    intro w hwC hvw
    have hmem : ∀ x : V, x ∈ C → G.Adj v x → x = a₁ ∨ x = a₂ := by
      intro x hxC hvx
      have : x ∈ ({a₁, a₂} : Set V) := by rw [← hneighbors]; exact ⟨hxC, hvx⟩
      simpa using this
    have hc2m := hmem c₂ hc2C hvc2
    have hfm := hmem f hfC hvf
    have hwm := hmem w hwC hvw
    have hne : c₂ ≠ f := hc2f.ne
    rcases hc2m with hc | hc <;> rcases hfm with hf | hf <;>
      rcases hwm with hh | hh
    · exact absurd (hc.trans hf.symm) hne
    · exact absurd (hc.trans hf.symm) hne
    · exact Or.inr (Or.inl (hh.trans hc.symm))
    · exact Or.inr (Or.inr (hh.trans hf.symm))
    · exact Or.inr (Or.inr (hh.trans hf.symm))
    · exact Or.inr (Or.inl (hh.trans hc.symm))
    · exact absurd (hc.trans hf.symm) hne
    · exact absurd (hc.trans hf.symm) hne
  · -- three consecutive `Y`-complete rim vertices, all adjacent to `v`
    obtain ⟨hp₁C, hp₂C, hp₃C⟩ := mem_rim_of_block (G := G) hblock
    have hvp₁ : G.Adj v p₁ := (hp₁ v (Or.inr rfl)).symm
    have hvp₂ : G.Adj v p₂ := (hp₂ v (Or.inr rfl)).symm
    have hvp₃ : G.Adj v p₃ := (hp₃ v (Or.inr rfl)).symm
    have hp₁Y : VertexComplete G p₁ Y := fun x hx => hp₁ x (Or.inl hx)
    have hp₂Y : VertexComplete G p₂ Y := fun x hx => hp₂ x (Or.inl hx)
    have hp₃Y : VertexComplete G p₃ Y := fun x hx => hp₃ x (Or.inl hx)
    have hnd : ([p₁, p₂, p₃] : List V).Nodup := hP.2.1
    have h12 : p₁ ≠ p₂ := by intro h; subst h; simp at hnd
    have h13 : p₁ ≠ p₃ := by intro h; subst h; simp at hnd
    have h23 : p₂ ≠ p₃ := by intro h; subst h; simp at hnd
    have hadj12 : G.Adj p₁ p₂ := by
      simpa using path_adj_succ hP (i := 0) (by simp)
    have hadj23 : G.Adj p₂ p₃ := by
      simpa using path_adj_succ hP (i := 1) (by simp)
    have hnadj13 : ¬ G.Adj p₁ p₃ := by
      have := path_adj_iff hP (i := 0) (j := 2) (by simp) (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
      rw [this]
      omega
    -- "By 22.3, `v₁` has no other neighbours in `C`."
    have hall : ∀ x : V, x ∈ C → G.Adj v x → x = p₁ ∨ x = p₂ ∨ x = p₃ := by
      intro x hxC hvx
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx1, hx2, hx3⟩ := hcon
      refine hnokite ⟨v, hw, hvY, hvC, hvNC,
        four_neighbours h12 h13 h23 hp₁C hp₂C hp₃C hxC hvp₁ hvp₂ hvp₃ hvx hx1 hx2 hx3, ?_⟩
      obtain ⟨k, hk | hk⟩ := hblock
      · exact ⟨p₁, p₂, p₃, ⟨k, hk⟩, hvp₁, hvp₂, hvp₃, hp₁Y, hp₂Y, hp₃Y⟩
      · exact ⟨p₃, p₂, p₁, ⟨k, hk⟩, hvp₃, hvp₂, hvp₁, hp₃Y, hp₂Y, hp₁Y⟩
    have hc2P := hall c₂ hc2C hvc2
    have hfP := hall f hfC hvf
    -- the middle vertex of the three is `c₂`
    have hmid : p₂ = c₂ := by
      by_cases hp2f : p₂ = f
      · -- `c₂` is an end of the triple, and the other end is a `Y`-complete neighbour of `f`
        exfalso
        subst hp2f
        rcases hc2P with h | h | h
        · have := hfedge p₃ hp₃C hadj23 hp₃Y
          exact h13 (h.symm.trans this.symm)
        · exact hc2f.ne h
        · have := hfedge p₁ hp₁C hadj12.symm hp₁Y
          exact h13 (this.trans h)
      · by_cases hp2c : p₂ = c₂
        · exact hp2c
        · exfalso
          -- `c₂` and `f` are the two ends, but they are adjacent
          have hc : c₂ = p₁ ∨ c₂ = p₃ := by
            rcases hc2P with h | h | h
            · exact Or.inl h
            · exact absurd h.symm hp2c
            · exact Or.inr h
          have hf : f = p₁ ∨ f = p₃ := by
            rcases hfP with h | h | h
            · exact Or.inl h
            · exact absurd h.symm hp2f
            · exact Or.inr h
          rcases hc with hc | hc <;> rcases hf with hf | hf
          · exact hc2f.ne (hc.trans hf.symm)
          · exact hnadj13 (hc ▸ hf ▸ hc2f)
          · exact hnadj13 (hc ▸ hf ▸ hc2f.symm)
          · exact hc2f.ne (hc.trans hf.symm)
    -- the other two are the rim neighbours `f, e` of `c₂`
    have hp₁ef : p₁ = f ∨ p₁ = e :=
      hnbc.2.2.2.2.2 p₁ hp₁C (hmid ▸ hadj12.symm)
    have hp₃ef : p₃ = f ∨ p₃ = e :=
      hnbc.2.2.2.2.2 p₃ hp₃C (hmid ▸ hadj23)
    intro w hwC hvw
    rcases hall w hwC hvw with h | h | h
    · rcases hp₁ef with he | he
      · exact Or.inr (Or.inr (h.trans he))
      · exact Or.inl (h.trans he)
    · exact Or.inr (Or.inl (h.trans hmid))
    · rcases hp₃ef with he | he
      · exact Or.inr (Or.inr (h.trans he))
      · exact Or.inl (h.trans he)
  · exact (hopt.2 ⟨C, Y ∪ {v}, hlarger,
      KiteTailBasics.ssubset_union_singleton hvY⟩).elim

end Workspace.ProofLemmas.Thm232Claim4Neighbours
