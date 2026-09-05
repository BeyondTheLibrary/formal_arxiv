import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.Statements.S02.Thm_2_3

/-!
# *"Since `(C,Y)` is not an odd wheel, `u,v` are the only `Y`-complete vertices of `C`"*

Sections 20–23 use this reading of `G ∈ F₇` over and over (21.2(4), 21.2(8), 22.4, 23.2):
a hole `C` carries an adjacent pair `u,v` of `Y`-complete vertices whose *other* neighbours
on `C` are not `Y`-complete, and one concludes that `u` and `v` are the only `Y`-complete
vertices of `C`, so that 2.10 applies at the edge `uv`.

The argument is the printed one.  By 2.3, either the number of `Y`-complete edges of `C` is
even, or `C` has exactly two `Y`-complete vertices and they are adjacent.  In the second case
those two vertices must be `u` and `v`.  In the first case `uv` is one `Y`-complete edge, so
there is a second one, and it is disjoint from `uv` because the two remaining neighbours of
`u` and `v` on `C` are not `Y`-complete; hence `(C,Y)` is a wheel, whose maximal run of
`Y`-complete positions through `u,v` has the even length `2`, so `(C,Y)` is an odd wheel —
contradicting `G ∈ F₇`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm212OnlyTwoComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two shifts of a base index by distinct amounts below the modulus stay distinct. -/
private theorem mod_shift_ne {n : ℕ} (k : ℕ) {a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : (k + a) % n ≠ (k + b) % n := by
  intro he
  have h : a % n = b % n := Nat.ModEq.add_left_cancel' k he
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hab h

/-- The rim positions of `u` and `v`, with `v` the cyclic successor of `u` (after possibly
swapping the two). -/
private theorem exists_consecutive_index {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) {u v : V} (hu : u ∈ C) (hv : v ∈ C) (huv : G.Adj u v) :
    ∃ k : ℕ, ∃ hk : k % C.length < C.length,
      ∃ hk1 : (k + 1) % C.length < C.length,
      ((C[k % C.length]'hk = u ∧ C[(k + 1) % C.length]'hk1 = v) ∨
        (C[k % C.length]'hk = v ∧ C[(k + 1) % C.length]'hk1 = u)) := by
  have hn : 0 < C.length := by have := hC.1; omega
  obtain ⟨a, ha, hau⟩ := List.getElem_of_mem hu
  obtain ⟨b, hb, hbv⟩ := List.getElem_of_mem hv
  have hcyc : b = (a + 1) % C.length ∨ a = (b + 1) % C.length :=
    (HoleBasics.hole_adj_iff hC ha hb).mp (by rw [hau, hbv]; exact huv)
  rcases hcyc with hcyc | hcyc
  · refine ⟨a, by rwa [Nat.mod_eq_of_lt ha], Nat.mod_lt _ hn, Or.inl ⟨?_, ?_⟩⟩
    · exact (HoleArithmetic.getElem_congr_idx C _ ha (Nat.mod_eq_of_lt ha)).trans hau
    · exact (HoleArithmetic.getElem_congr_idx C _ hb hcyc.symm).trans hbv
  · refine ⟨b, by rwa [Nat.mod_eq_of_lt hb], Nat.mod_lt _ hn, Or.inr ⟨?_, ?_⟩⟩
    · exact (HoleArithmetic.getElem_congr_idx C _ hb (Nat.mod_eq_of_lt hb)).trans hbv
    · exact (HoleArithmetic.getElem_congr_idx C _ ha hcyc.symm).trans hau

/-- **The printed step.**  In a graph with no odd wheel, an adjacent pair `u,v` of
`Y`-complete vertices of a hole `C` of length `≥ 6` whose other neighbours on `C` are not
`Y`-complete are the only `Y`-complete vertices of `C`. -/
theorem only_two_complete {G : SimpleGraph V} (hBerge : Berge G)
    (hno : ¬ ∃ (C' : List V) (Y' : Set V), IsOddWheel G C' Y')
    {C : List V} {Y : Set V} (hC : IsHoleList G C) (h6 : 6 ≤ C.length)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y) (hCY : ∀ w ∈ C, w ∉ Y)
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (huv : G.Adj u v)
    (hcu : VertexComplete G u Y) (hcv : VertexComplete G v Y)
    (hnbr : ∀ w ∈ C, (G.Adj w u ∨ G.Adj w v) → VertexComplete G w Y → w = u ∨ w = v) :
    ∀ w ∈ C, VertexComplete G w Y → w = u ∨ w = v := by
  classical
  have hn : 0 < C.length := by omega
  rcases (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti C
      (Or.inr hC) hCY).2 hC with heven | ⟨a, b, hset, hab, hadjab⟩
  · -- *"the number of `Y`-complete edges is even"*: we build a wheel, and an odd one.
    exfalso
    set E : Set (Sym2 V) :=
      {e : Sym2 V | ∃ u' ∈ C, ∃ v' ∈ C, e = s(u', v') ∧ EdgeComplete G Y u' v'} with hE
    have huvE : s(u, v) ∈ E := ⟨u, hu, v, hv, rfl, huv, hcu, hcv⟩
    have hEfin : E.Finite := Set.toFinite _
    have hpos : 0 < E.ncard := Set.ncard_pos hEfin |>.mpr ⟨_, huvE⟩
    have h2 : 2 ≤ E.ncard := by
      obtain ⟨d, hd⟩ := heven
      omega
    obtain ⟨e, heE, hene⟩ : ∃ e ∈ E, e ≠ s(u, v) := by
      by_contra hcon
      push Not at hcon
      have hsub : E ⊆ {s(u, v)} := fun e he => by
        simpa using hcon e he
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      simp only [Set.ncard_singleton] at this
      omega
    obtain ⟨a', ha'C, b', hb'C, rfl, hadj', hca', hcb'⟩ := heE
    have hkey : ∀ w ∈ C, ∀ w' ∈ C, VertexComplete G w Y → VertexComplete G w' Y →
        G.Adj w w' → s(w, w') ≠ s(u, v) → (w ≠ u ∧ w ≠ v) := by
      intro w hw w' hw' hcw hcw' hadjw hne
      constructor
      · rintro rfl
        rcases hnbr w' hw' (Or.inl hadjw.symm) hcw' with rfl | rfl
        · exact G.irrefl hadjw
        · exact hne rfl
      · rintro rfl
        rcases hnbr w' hw' (Or.inr hadjw.symm) hcw' with rfl | rfl
        · exact hne (by rw [Sym2.eq_swap])
        · exact G.irrefl hadjw
    obtain ⟨ha'u, ha'v⟩ := hkey a' ha'C b' hb'C hca' hcb' hadj' hene
    obtain ⟨hb'u, hb'v⟩ := hkey b' hb'C a' ha'C hcb' hca' hadj'.symm
      (by rw [Sym2.eq_swap]; exact hene)
    have hwheel : IsWheel G C Y :=
      ⟨⟨hC, by simpa only [holeLength] using h6⟩, ⟨hYne, hYanti, hCY⟩,
        u, v, a', b', hu, hv, ha'C, hb'C, ⟨huv, hcu, hcv⟩, ⟨hadj', hca', hcb'⟩,
        fun he => ha'u he.symm, fun he => hb'u he.symm,
        fun he => ha'v he.symm, fun he => hb'v he.symm⟩
    -- the maximal run through `u,v` has the even length `2`
    obtain ⟨k, hk, hk1, hor⟩ := exists_consecutive_index hC hu hv huv
    have hrun : ∀ (c d : V), C[k % C.length]'hk = c → C[(k + 1) % C.length]'hk1 = d →
        VertexComplete G c Y → VertexComplete G d Y →
        (∀ w ∈ C, (G.Adj w c ∨ G.Adj w d) → VertexComplete G w Y → w = c ∨ w = d) →
        False := by
      intro c d hkc hk1d hcc hcd hnb
      have hnextpos : ¬ SegmentBasics.CycVert G Y C (k + 2) := by
        intro hcv2
        obtain ⟨w, hw, hwY⟩ := hcv2
        have hwlt : (k + 2) % C.length < C.length := Nat.mod_lt _ hn
        rw [List.getElem?_eq_getElem hwlt] at hw
        have hwe : C[(k + 2) % C.length]'hwlt = w := Option.some.inj hw
        have hadjw : G.Adj (C[(k + 1) % C.length]'hk1) (C[(k + 2) % C.length]'hwlt) := by
          have := YEdgeConfiguration.adj_of_succ_pos hC hn (k + 1)
          simpa only [Nat.add_assoc] using this
        rcases hnb w (hwe ▸ List.getElem_mem hwlt)
            (Or.inr (by rw [← hwe, ← hk1d]; exact hadjw.symm)) hwY with he | he
        · rw [← hwe, ← hkc] at he
          exact mod_shift_ne k (n := C.length) (a := 2) (b := 0) (by omega) (by omega)
            (by omega) (by simpa using hC.2.1.getElem_inj_iff.mp he)
        · rw [← hwe, ← hk1d] at he
          exact mod_shift_ne k (n := C.length) (a := 2) (b := 1) (by omega) (by omega)
            (by omega) (by simpa using hC.2.1.getElem_inj_iff.mp he)
      have hprevpos : ¬ SegmentBasics.CycVert G Y C (k + (C.length - 1)) := by
        intro hcv2
        obtain ⟨w, hw, hwY⟩ := hcv2
        have hwlt : (k + (C.length - 1)) % C.length < C.length := Nat.mod_lt _ hn
        rw [List.getElem?_eq_getElem hwlt] at hw
        have hwe : C[(k + (C.length - 1)) % C.length]'hwlt = w := Option.some.inj hw
        have hadjw : G.Adj (C[(k + (C.length - 1)) % C.length]'hwlt)
            (C[k % C.length]'hk) := by
          have hh := YEdgeConfiguration.adj_of_succ_pos hC hn (k + (C.length - 1))
          have heq : (k + (C.length - 1) + 1) % C.length = k % C.length := by
            have h' : k + (C.length - 1) + 1 = k + C.length := by omega
            rw [h', Nat.add_mod_right]
          rwa [HoleArithmetic.getElem_congr_idx C (Nat.mod_lt _ hn) hk heq] at hh
        rcases hnb w (hwe ▸ List.getElem_mem hwlt)
            (Or.inl (by rw [← hwe, ← hkc]; exact hadjw)) hwY with he | he
        · rw [← hwe, ← hkc] at he
          exact mod_shift_ne k (n := C.length) (a := C.length - 1) (b := 0) (by omega)
            (by omega) (by omega) (by simpa using hC.2.1.getElem_inj_iff.mp he)
        · rw [← hwe, ← hk1d] at he
          exact mod_shift_ne k (n := C.length) (a := C.length - 1) (b := 1) (by omega)
            (by omega) (by omega) (by simpa using hC.2.1.getElem_inj_iff.mp he)
      refine YEdgeConfiguration.run_odd_of_not_isOddWheel hC hwheel
        (fun hodd => hno ⟨C, Y, hodd⟩) (L := 2) (by omega) (by omega) ?_ hnextpos hprevpos
        ⟨1, rfl⟩
      intro s hs
      interval_cases s
      · exact ⟨_, by rw [Nat.add_zero, List.getElem?_eq_getElem hk], by rw [hkc]; exact hcc⟩
      · exact ⟨_, by rw [List.getElem?_eq_getElem hk1], by rw [hk1d]; exact hcd⟩
    rcases hor with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact hrun u v h1 h2' hcu hcv hnbr
    · exact hrun v u h1 h2' hcv hcu (fun w hw hadjw hcw => (hnbr w hw hadjw.symm hcw).symm)
  · -- *"there are exactly two `Y`-complete vertices and they are adjacent"*
    intro w hw hcw
    have huset : u ∈ ({a, b} : Set V) := by rw [← hset]; exact ⟨hu, hcu⟩
    have hvset : v ∈ ({a, b} : Set V) := by rw [← hset]; exact ⟨hv, hcv⟩
    have hwset : w ∈ ({a, b} : Set V) := by rw [← hset]; exact ⟨hw, hcw⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huset hvset hwset
    have huv' : u ≠ v := huv.ne
    rcases huset with rfl | rfl <;> rcases hvset with rfl | rfl <;>
      rcases hwset with rfl | rfl <;> simp_all

end Workspace.ProofLemmas.Thm212OnlyTwoComplete
