import Workspace.ProofLemmas.Thm192Claim7Aux
import Workspace.ProofLemmas.Thm192Claim7GapUniqueEdge
import Workspace.Statements.S16.Thm_16_1

/-!
# The 16.1 parity calculation in claim (7) of 19.2

PAPER (printed p. 119, claim (7), the case `x₂` not `Y₀`-complete):

> *"By 16.1, `pᵢ, z` have the same wheel-parity, and so there are an odd number of
> `Y₀`-complete edges in `pᵢ-⋯-pₙ-x₁`."*

The paper's *"same wheel-parity"* comes from the first assertion of 16.1: if `pᵢ` and `z`
had opposite wheel-parity, then the arc `pᵢ-⋯-pₙ-x₁-z` of the rim would carry a
`Y₀ ∪ {x₂}`-complete edge, i.e. two consecutive rim vertices both adjacent to `x₂`.  But
`i` is the *last* neighbour of `x₂` on `P`, and `x₂` is nonadjacent to `x₁`, so `pᵢ` and
`z` are the only neighbours of `x₂` on that arc, and they are not adjacent.

What the rest of claim (7) actually uses from the odd count is only that the count is
nonzero, i.e. that some vertex of `pᵢ, …, pₙ` is `Y₀`-complete; that is what
`exists_complete_after` returns.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim7NoncompleteParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arc `pᵢ-⋯-pₙ-x₁-z` of the rim `C = z-x₀-p₁-⋯-pₙ-x₁-z`, as a list. -/
private theorem rotate_arc (z : V) (P : List V) {i : ℕ} (hi : i + 1 < P.length) :
    (z :: P).rotate (i + 1) = (P.drop i ++ [z]) ++ P.take i := by
  rw [List.rotate_eq_drop_append_take (by simp only [List.length_cons]; omega)]
  simp

/-- PAPER: *"By 16.1, `pᵢ, z` have the same wheel-parity."* -/
theorem same_parity {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V}
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length) (hW : IsWheel G (z :: P) (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx21 : ¬ G.Adj (x 2) (x 1))
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i)) :
    SameWheelParity G (z :: P) (Y \ {y}) (P[i]'(by omega)) z := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, hC, -⟩ :=
    Thm192Claim6Basics.path_facts hBerge hws Set.Subset.rfl hP hPI (by omega)
  have hlastP : (P[P.length - 1]'(by omega)) = x 1 :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hzint : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w :=
    fun w hw => wheelSystemA_no_z w (hPI w hw)
  -- the arc `Q = pᵢ-⋯-pₙ-x₁-z`
  set Q : List V := P.drop i ++ [z] with hQdef
  have hQfrom : IsPathFrom G Q (P[i]'(by omega)) z := by
    refine Thm192Claim7Aux.isPathFrom_snoc
      (Thm192Claim7Aux.isPathFrom_drop hP.1 hin) ?_ ?_ ?_
    · rw [hlastP]
      exact hws.2.2.2.2.2.2 1 (by omega)
    · intro hmem
      exact hzP (List.mem_of_mem_drop hmem)
    · intro w hw hwne
      obtain ⟨k, hk, hik, hkw⟩ := Thm192Claim7Aux.mem_drop_index hw
      have hklt : k < P.length - 1 := by
        rcases Nat.lt_or_ge k (P.length - 1) with h | h
        · exact h
        · exact absurd (hkw.symm.trans (by
            rw [hP.1.2.1.getElem_inj_iff.mpr (show k = P.length - 1 by omega)])) hwne
      rw [← hkw]
      exact hzint _ (PathBasics.getElem_mem_interior hP.1 hk (by omega) (by omega))
  have hQpre : Q <+: (z :: P).rotate (i + 1) := by
    rw [rotate_arc z P hin]
    exact List.prefix_append _ _
  -- the only neighbours of `x₂` on the arc are `pᵢ` and `z`
  have hQnb : ∀ w ∈ Q, G.Adj (x 2) w → w = (P[i]'(by omega)) ∨ w = z := by
    intro w hw hadj
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨k, hk, hik, hkw⟩ := Thm192Claim7Aux.mem_drop_index hw
      left
      rw [← hkw, hP.1.2.1.getElem_inj_iff.mpr ((hlast k hk hik).mp (by rwa [hkw]))]
    · right
      simpa using hw
  by_contra hns
  have hopp : OppositeWheelParity G (z :: P) (Y \ {y}) (P[i]'(by omega)) z := by
    refine ⟨?_, ?_, by simp, hns⟩
    · intro he
      exact hzP (he ▸ List.getElem_mem (show i < P.length by omega))
    · exact List.mem_cons_of_mem _ (List.getElem_mem (show i < P.length by omega))
  have hx2C : x 2 ∉ z :: P := by
    intro hmem
    rcases List.mem_cons.mp hmem with he | he
    · exact (hws.2.2.1 2 le_rfl).2 he
    · exact hx2P he
  have hx2Y : x 2 ∉ Y \ {y} := fun h => (hHyp.1 _ h.1).2.2.2 rfl
  obtain ⟨u, huQ, v, hvQ, hE⟩ :=
    (Workspace.Statements.S16.SPGT.thm_16_1 G hG.1 (z :: P) (Y \ {y}) hW (x 2) hx2C hx2Y
      hx2nc _ _ hxI (hws.2.2.2.2.2.2 2 le_rfl).symm hopp).1 Q hQfrom.1
      ⟨i + 1, Or.inl hQpre⟩ (Or.inl hQfrom)
  have hux : G.Adj (x 2) u := (hE.2.1 (x 2) (Or.inr rfl)).symm
  have hvx : G.Adj (x 2) v := (hE.2.2 (x 2) (Or.inr rfl)).symm
  have hpiI : (P[i]'(show i < P.length by omega)) ∈ SPGT.interior P :=
    PathBasics.getElem_mem_interior hP.1 (by omega) hi hin
  have hzpi : ¬ G.Adj z (P[i]'(show i < P.length by omega)) := hzint _ hpiI
  rcases hQnb u huQ hux with rfl | rfl <;> rcases hQnb v hvQ hvx with hv | hv
  · exact G.irrefl (hv ▸ hE.1)
  · exact hzpi (hv ▸ hE.1).symm
  · exact hzpi (hv ▸ hE.1)
  · exact G.irrefl (hv ▸ hE.1)

/-- PAPER: *"…and so there are an odd number of `Y₀`-complete edges in `pᵢ-⋯-pₙ-x₁`."*
Only the consequence that the count is nonzero is recorded: some `pₖ` with `i ≤ k ≤ n`
is `Y₀`-complete. -/
theorem exists_complete_after {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V}
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length) (hW : IsWheel G (z :: P) (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx21 : ¬ G.Adj (x 2) (x 1)) (hzY : VertexComplete G z Y)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i)) :
    ∃ k, ∃ hk : k + 1 < P.length, i ≤ k ∧
      VertexComplete G (P[k]'(by omega)) (Y \ {y}) := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, hC, -⟩ :=
    Thm192Claim6Basics.path_facts hBerge hws Set.Subset.rfl hP hPI (by omega)
  have hlastP : (P[P.length - 1]'(by omega)) = x 1 :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hClen : (z :: P).length = P.length + 1 := by simp
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hW
  rw [hClen] at heven
  have hsame := same_parity hG hws hHyp hP hPI hP5 hW hx2nc hx21 hi hin hxI hlast
  have hcnt : WheelParity.cycCount G (Y \ {y}) (z :: P) (i + 1) % 2
      = WheelParity.cycCount G (Y \ {y}) (z :: P) 0 % 2 := by
    rw [← WheelParity.sameWheelParity_iff hC (by rw [hClen]; exact heven)
      (i := i + 1) (j := 0) (by omega) (by omega) (by omega)]
    simpa using hsame
  rw [WheelParity.cycCount_zero] at hcnt
  -- the rim edge `x₁z` is `Y₀`-complete
  have hxlast : (z :: P)[P.length]? = some (x 1) := by
    obtain ⟨m, hmdef⟩ : ∃ m, P.length = m + 1 := ⟨P.length - 1, by omega⟩
    rw [hmdef, List.getElem?_cons_succ,
      List.getElem?_eq_getElem (show m < P.length by omega)]
    congr 1
    rw [← hlastP]
    exact hP.1.2.1.getElem_inj_iff.mpr (by omega)
  have hcelast : WheelParity.CycEdge G (Y \ {y}) (z :: P) P.length := by
    refine ⟨x 1, z, ?_, ?_, (hws.2.2.2.2.2.2 1 (by omega)).symm,
      fun w hw => hHyp.2.2.2.1 w hw.1, fun w hw => hzY w hw.1⟩
    · rw [hClen, Nat.mod_eq_of_lt (by omega)]
      exact hxlast
    · rw [hClen, Nat.mod_self]
      simp
  have hsucc : WheelParity.cycCount G (Y \ {y}) (z :: P) (P.length + 1)
      = WheelParity.cycCount G (Y \ {y}) (z :: P) P.length + 1 := by
    rw [WheelParity.cycCount_succ, if_pos hcelast]
  obtain ⟨r, hr⟩ := heven
  have hodd : WheelParity.cycCount G (Y \ {y}) (z :: P) P.length % 2 = 1 := by omega
  have hmono := WheelParity.cycCount_mono (G := G) (Y := Y \ {y}) (C := z :: P)
    (show i + 1 ≤ P.length by omega)
  obtain ⟨m, hm1, hm2, hce⟩ := Thm192Claim7Aux.exists_cycEdge_of_cycCount_lt
    (show WheelParity.cycCount G (Y \ {y}) (z :: P) (i + 1)
        < WheelParity.cycCount G (Y \ {y}) (z :: P) P.length by omega)
  obtain ⟨u, v, hu, hv, hE⟩ := hce
  rw [hClen, Nat.mod_eq_of_lt (show m < P.length + 1 by omega)] at hu
  have hu2 : (z :: P)[m - 1 + 1]? = some u := by rwa [show m - 1 + 1 = m by omega]
  rw [List.getElem?_cons_succ,
    List.getElem?_eq_getElem (show m - 1 < P.length by omega)] at hu2
  exact ⟨m - 1, by omega, by omega, (Option.some.inj hu2) ▸ hE.2.1⟩

end Workspace.ProofLemmas.Thm192Claim7NoncompleteParity
