import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.ProofLemmas.OddWheelAttachmentEndgame

/-!
# 16.2: *"From (4) we may assume that `X₁` has only one member, say `p₁`.  Choose `i, j` …"*

`OddWheelAttachmentEndgame.Setup` is the index picture the closing part of 16.2 works in — the
rim read as `q d = p_{d+1}` from a base offset `b` with `p₁ = q 0`, the path `P` read as
`f t = p_t`, and the two extreme rim neighbours `p_i = q a`, `p_j = q c` of `f_k`.  This module
builds that picture out of an `OddWheelAttachmentMain.Config` together with claim (4)'s output
`|X₁| = 1`, and hence reduces `OddWheelAttachmentMain.Endgame` to
`OddWheelAttachmentEndgame.Contradiction`.

Every field is the mechanical reading of one printed phrase:

* *"`X₁` has only one member, say `p₁`"* — `adjFst`.  The single member is forced to be `x₁`,
  the first vertex of the path `P = p₁-f₁-⋯-f_k-p_m`, because `x₁` is adjacent to `f₁`.
* *"there are no edges between the interior of `F` and `C`"* (the paragraph before claim (4)) —
  `adjMid`.
* *"Choose `i, j` with `2 ≤ i, j ≤ n`, such that `p_i, p_j` are adjacent to `f_k`, with `i`
  minimum and `j` maximum"* — `adjLstMin`, `adjLstMax`, `minSpec`, `maxSpec`, and the four range
  side conditions `alb`, `aub`, `clb`, `cub`.  `p_m = x₂` is a neighbour of `f_k` and is
  non-adjacent to `p₁`, which is what pins `2 ≤ i` and `j ≤ n − 1` — i.e. what keeps the arcs
  `H₁`, `H₂` proper.
* *"…contradicting that there are nonadjacent vertices in `X` of opposite wheel-parity"* —
  `midNbr`, again witnessed by `x₂`.
* *"all members of `X₂` have the opposite wheel-parity"* — `oppLst`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentEndgameSetup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- **The closing part of 16.2, reduced to `OddWheelAttachmentEndgame.Contradiction`.** -/
theorem endgame_of_contradiction [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hcon : OddWheelAttachmentEndgame.Contradiction G) :
    OddWheelAttachmentMain.Endgame G := by
  classical
  rintro C Y F P x₁ x₂ f₁ fk h hX₁ hX₂ hcross hone
  ------------------------------------------------------------------ the rim and the path
  have hl : 4 ≤ P.length := h.len
  have hC : IsHoleList G C := h.wheel.1.1
  have hn6 : 6 ≤ C.length := h.wheel.1.2
  have hnpos : 0 < C.length := by omega
  have hP : IsPathList G P := h.path.1
  obtain ⟨k, hplen⟩ : ∃ k : ℕ, P.length = k + 2 := ⟨P.length - 2, by omega⟩
  have hk2 : 2 ≤ k := by omega
  -- `f t = P[t]`
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → V, ∀ t : ℕ, t < P.length → P[t]? = some (f t) :=
    ⟨fun t => (P[t]?).getD x₁, fun t ht => by simp [List.getElem?_eq_getElem ht]⟩
  have hfval : ∀ (t : ℕ) (ht : t < P.length), f t = (P[t]'ht) := by
    intro t ht
    have hd := hfdef t ht
    rw [List.getElem?_eq_getElem ht] at hd
    exact (Option.some_injective _ hd).symm
  have hf0 : f 0 = x₁ := by
    rw [hfval 0 (by omega)]
    exact PathBasics.getElem_zero_of_head? h.path.2.1 (by omega)
  have hf1 : f 1 = f₁ := by
    rw [hfval 1 (by omega)]
    exact OddWheelAttachmentMain.fst_getElem h
  have hfk : f k = fk := by
    rw [hfval k (by omega)]
    rw [← OddWheelAttachmentMain.lst_getElem h]
    exact HoleArithmetic.getElem_congr_idx P _ _ (by omega)
  have hfx₂ : f (k + 1) = x₂ := by
    rw [hfval (k + 1) (by omega)]
    rw [← PathBasics.getElem_last_of_getLast? h.path.2.2 (show 0 < P.length by omega)]
    exact HoleArithmetic.getElem_congr_idx P _ _ (by omega)
  have hfF : ∀ t : ℕ, 1 ≤ t → t ≤ k → f t ∈ F := by
    intro t h1 h2
    rw [h.interiorEq, Set.mem_setOf_eq, hfval t (by omega)]
    exact PathBasics.getElem_mem_interior hP (by omega) h1 (by omega)
  have hfne : ∀ s t : ℕ, s < P.length → t < P.length → s ≠ t → f s ≠ f t := by
    intro s t hs ht hst he
    rw [hfval s hs, hfval t ht] at he
    exact hst ((List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp he)
  ------------------------------------------------------------------ the rim as `q d = p_{d+1}`
  have hx₁C : x₁ ∈ C := h.att₁.1
  have hx₂C : x₂ ∈ C := h.att₂.1
  obtain ⟨b, hb, hbx⟩ := List.getElem_of_mem hx₁C
  have hq0 : cyc C hnpos (b + 0) = x₁ := by rw [Nat.add_zero, cyc_eq hnpos hb]; exact hbx
  have hqmem : ∀ t : ℕ, cyc C hnpos (b + t) ∈ C := fun t => cyc_mem hnpos _
  have hadj01 : G.Adj (cyc C hnpos (b + 0)) (cyc C hnpos (b + 1)) :=
    (cyc_adj hC hnpos (b + 0) (b + 1)).mpr (Or.inl rfl)
  have hadj0n : G.Adj (cyc C hnpos (b + 0)) (cyc C hnpos (b + (C.length - 1))) := by
    refine (cyc_adj hC hnpos (b + 0) (b + (C.length - 1))).mpr (Or.inr ?_)
    rw [Nat.add_zero, show b + (C.length - 1) + 1 = b + C.length by omega, Nat.add_mod_right]
  ------------------------------------------------------------------ `X₁` and `X₂`
  have hx₁f₁ : G.Adj x₁ f₁ := by
    have := PathBasics.path_adj_succ hP (i := 0) (by omega)
    rw [← hfval 0 (by omega), ← hfval 1 (by omega), hf0, hf1] at this
    exact this
  have hfkx₂ : G.Adj fk x₂ := by
    have := PathBasics.path_adj_succ hP (i := k) (by omega)
    rw [← hfval k (by omega), ← hfval (k + 1) (by omega), hfk, hfx₂] at this
    exact this
  have hx₁mem : x₁ ∈ OddWheelAttachmentMain.Att G C (F \ {fk}) := by
    rw [hX₁]; exact ⟨hx₁C, hx₁f₁.symm⟩
  have hmemX₂ : ∀ u : V, u ∈ C → G.Adj fk u → u ∈ OddWheelAttachmentMain.Att G C (F \ {f₁}) := by
    intro u huC hadj
    rw [hX₂]; exact ⟨huC, hadj⟩
  -- *"`X₁` has only one member, say `p₁`"*
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hone
  have hX₁sing : ∀ u : V, u ∈ C → G.Adj f₁ u → u = x₁ := by
    intro u huC hadj
    have h1 : u ∈ ({w} : Set V) := by rw [← hw]; exact ⟨huC, hadj⟩
    have h2 : x₁ ∈ ({w} : Set V) := by rw [← hw]; exact ⟨hx₁C, hx₁f₁.symm⟩
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  -- *"`X₁ ∩ X₂ = ∅`"*
  have hdisj : ∀ u : V, u ∈ OddWheelAttachmentMain.Att G C (F \ {fk}) →
      u ∈ OddWheelAttachmentMain.Att G C (F \ {f₁}) → False :=
    fun u h1 h2 => (hcross u h1 u h2).1 rfl
  ------------------------------------------------------------------ the offset of `p_m = x₂`
  obtain ⟨d₂, hd₂lt, hd₂x⟩ := OddWheelAttachmentClaim4.exists_offset_cyc hnpos b hx₂C
  have hd₂0 : d₂ ≠ 0 := by
    intro he
    rw [he, hq0] at hd₂x
    exact h.opp.1 hd₂x
  have hd₂1 : d₂ ≠ 1 := by
    intro he
    refine h.nadj ?_
    rw [← hq0, ← hd₂x, he]
    exact hadj01
  have hd₂n : d₂ ≠ C.length - 1 := by
    intro he
    refine h.nadj ?_
    rw [← hq0, ← hd₂x, he]
    exact hadj0n
  have hd₂adj : G.Adj (f k) (cyc C hnpos (b + d₂)) := by rw [hfk, hd₂x]; exact hfkx₂
  ------------------------------------------------------------------ `i` minimum and `j` maximum
  have hex : ∃ d : ℕ, 1 ≤ d ∧ d < C.length ∧ G.Adj (f k) (cyc C hnpos (b + d)) :=
    ⟨d₂, by omega, hd₂lt, hd₂adj⟩
  obtain ⟨a, ⟨ha1, ha2, ha3⟩, hamin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun d : ℕ => 1 ≤ d ∧ d < C.length ∧ G.Adj (f k) (cyc C hnpos (b + d))) id hex
  obtain ⟨c, ⟨hc1, hc2, hc3⟩, hcmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun d : ℕ => 1 ≤ d ∧ d < C.length ∧ G.Adj (f k) (cyc C hnpos (b + d))) id C.length
      (fun d hd => le_of_lt hd.2.1) hex
  simp only [id_eq] at hamin hcmax
  have had₂ : a ≤ d₂ := hamin d₂ ⟨by omega, hd₂lt, hd₂adj⟩
  have hcd₂ : d₂ ≤ c := hcmax d₂ ⟨by omega, hd₂lt, hd₂adj⟩
  ------------------------------------------------------------------ assemble
  refine hcon C Y P (fun t => cyc C hnpos (b + t)) f b a c k ?_
  refine
    { inF6 := h.inF6
      wheel := h.wheel
      blt := hb
      qdef := ?_
      path := hP
      plen := hplen
      klb := hk2
      fdef := hfdef
      base := ?_
      fnotC := ?_
      fnotY := ?_
      fnotComplete := ?_
      adjFst := ?_
      adjMid := ?_
      notAdjLstBase := ?_
      adjLstMin := ha3
      adjLstMax := hc3
      minSpec := ?_
      maxSpec := ?_
      alb := ha1
      aub := by omega
      clb := by omega
      cub := by omega
      ac := by omega
      midNbr := ⟨d₂, by omega, by omega, hd₂adj⟩
      oppLst := ?_ }
  · intro t
    exact List.getElem?_eq_getElem (Nat.mod_lt _ hnpos)
  · rw [hf0, hq0]
  · intro t h1 h2
    exact h.notC (f t) (hfF t h1 h2)
  · intro t h1 h2
    exact h.notY (f t) (hfF t h1 h2)
  · intro t h1 h2
    exact h.notComplete (f t) (hfF t h1 h2)
  · intro u huC
    rw [hf1]
    constructor
    · intro hadj
      rw [hq0]
      exact hX₁sing u huC hadj
    · intro he
      rw [he, hq0]
      exact hx₁f₁.symm
  · intro t ht2 htk u huC hadj
    have hmemF : f t ∈ F := hfF t (by omega) (by omega)
    have hne1 : f t ≠ f₁ := by rw [← hf1]; exact hfne t 1 (by omega) (by omega) (by omega)
    have hnek : f t ≠ fk := by rw [← hfk]; exact hfne t k (by omega) (by omega) (by omega)
    refine hdisj u ⟨huC, f t, ⟨hmemF, hnek⟩, hadj.symm⟩ ⟨huC, f t, ⟨hmemF, hne1⟩, hadj.symm⟩
  · intro hadj
    rw [hq0] at hadj
    exact hdisj x₁ hx₁mem (hmemX₂ x₁ hx₁C (by rw [← hfk]; exact hadj))
  · intro d hd1 hda hadj
    have := hamin d ⟨hd1, by omega, hadj⟩
    omega
  · intro d hdc hdn hadj
    have := hcmax d ⟨by omega, hdn, hadj⟩
    omega
  · intro d hadj
    rw [hq0]
    exact hcross x₁ hx₁mem (cyc C hnpos (b + d))
      (hmemX₂ (cyc C hnpos (b + d)) (hqmem d) (by rw [← hfk]; exact hadj))

end Workspace.ProofLemmas.OddWheelAttachmentEndgameSetup
