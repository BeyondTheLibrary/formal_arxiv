import Workspace.ProofLemmas.Thm192Claim4Rim
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathAttach

/-! The antihole argument in claim (4) of 19.2 (printed p. 119). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim4Antihole

open Workspace.Types.Core.SPGT Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup
open Workspace.ProofLemmas.Thm192Claim4Rim

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The part of claim (2) used in (4): "By (2), `x₂` is `Y₀`-complete and
nonadjacent to `y`." This follows directly from the induction hypothesis for `Y₀`. -/
theorem x2_complete_of_z_not_complete {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (hzY : ¬ VertexComplete G z Y) :
    VertexComplete G (x 2) (Y \ {y}) ∧ ¬ G.Adj (x 2) y := by
  have hx2 : VertexComplete G (x 2) (Y \ {y}) := by
    by_contra hn
    have ha : AnticonnectedSet G (Y \ {y}) := by
      rcases hY0 with he | ha
      · exact (hn (by rw [he]; intro w hw; exact hw.elim)).elim
      · exact ha
    have hcard : (Y \ {y}).ncard < Y.ncard := by
      rw [Set.ncard_diff_singleton_of_mem hyY]
      have := (Set.ncard_pos (Set.toFinite Y)).mpr ⟨y, hyY⟩
      omega
    have hh : Hyp192 G z A₀ x (Y \ {y}) :=
      ⟨fun w hw => hHyp.1 w hw.1, ha,
        (fun w hw => hHyp.2.2.1 w hw.1),
        (fun w hw => hHyp.2.2.2.1 w hw.1), hn,
        fun w hw => hHyp.2.2.2.2.2 w hw.1⟩
    have hz0 := (ih.1 _ hcard hh).1
    apply hzY
    intro w hw
    by_cases he : w = y
    · simpa [he] using hyz.symm
    · exact hz0 w ⟨hw, he⟩
  refine ⟨hx2, ?_⟩
  intro hxy
  apply hHyp.2.2.2.2.1
  intro w hw
  by_cases he : w = y
  · simpa [he] using hxy
  · exact hx2 w ⟨hw, he⟩

/-- PAPER: "Let `Q` be an antipath between `z,y` with interior in `Y₀`."
Attach `z` to the anticonnected set `Y` and extract an induced path in the complement. -/
theorem antipath_to_member {G : SimpleGraph V} {Y : Set V}
    (hY : AnticonnectedSet G Y) {z y : V} (hz : z ∉ Y) (hy : y ∈ Y)
    (hn : ¬ VertexComplete G z Y) :
    ∃ Q : List V, IsAntipathFrom G Q z y ∧ ∀ w ∈ interior Q, w ∈ Y \ {y} := by
  classical
  obtain ⟨w, hw, hnw⟩ : ∃ w ∈ Y, ¬ G.Adj z w := by
    simpa only [VertexComplete, not_forall, exists_prop] using hn
  have hconn : AnticonnectedSet G (Y ∪ {z}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hY
      ⟨w, hw, ⟨fun he => hz (he ▸ hw), hnw⟩⟩
  obtain ⟨Q, hQ, hQsub⟩ :=
    InducedPathExtraction.exists_isAntipathFrom_of_anticonnected hconn (Or.inr rfl) (Or.inl hy)
  refine ⟨Q, hQ, ?_⟩
  intro w hw
  have hi := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw
  refine ⟨?_, hi.2.2⟩
  rcases hQsub w hi.1 with hwY | hwz
  · exact hwY
  · exact (hi.2.1 hwz).elim

/-- PAPER: "Then `z-Q-y-x₂-R-pᵢ-z` is an antihole, meeting the hole `C`
in at least three vertices, contrary to 15.7." -/
theorem complete_of_interior_complete {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ interior P, w ∈ wheelSystemA G z A₀ x 1) (hPlen : 3 ≤ P.length)
    {w : V} (hw : w ∈ interior P) (hwc : VertexComplete G w (Y ∪ {x 2})) :
    VertexComplete G z Y := by
  classical
  by_contra hzY
  obtain ⟨h2c, h2y⟩ := x2_complete_of_z_not_complete hHyp ih hyY hyz hY0 hzY
  obtain ⟨Q, hQ, hQint⟩ := antipath_to_member hHyp.2.1
    (fun hz => (hHyp.1 z hz).1 rfl) hyY hzY
  have hrim := rim hG.1.1.1.1 hws hP hPint hPlen
  have hzP : z ∉ P := (List.nodup_cons.mp hrim.1.2.1).1
  have hwP := PathBasics.interior_subset hw
  have hwends := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
  have hx01 : x 0 ≠ x 1 := by
    intro he
    have := hws.2.1 0 (by omega) 1 (by omega) he
    omega
  have hX : AnticonnectedSet G ({x 0, x 1} : Set V) := by
    have hp := PathBasics.isPathList_pair (G := Gᶜ) ⟨hx01, x0_not_adj_x1 hws⟩
    simpa using InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp
  have hx2X : x 2 ∉ ({x 0, x 1} : Set V) := by
    rintro (he | he)
    · have := hws.2.1 2 (by omega) 0 (by omega) he; omega
    · have := hws.2.1 2 (by omega) 1 (by omega) he; omega
  have hwX : w ∉ ({x 0, x 1} : Set V) := by
    rintro (he | he)
    · exact hwends.2.1 he
    · exact hwends.2.2 he
  have h2n : ∃ a ∈ ({x 0, x 1} : Set V), ¬ G.Adj (x 2) a := by
    have hn := hws.2.2.2.2.2.1 2 (by omega) (by omega)
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one] at hn
    simpa only [VertexComplete, not_forall, exists_prop] using hn
  have hwn : ∃ a ∈ ({x 0, x 1} : Set V), ¬ G.Adj w a := by
    by_cases h0 : G.Adj w (x 0)
    · exact ⟨x 1, Or.inr rfl, fun h1 => no_common (hPint w hw) ⟨h0, h1⟩⟩
    · exact ⟨x 0, Or.inl rfl, h0⟩
  obtain ⟨R, hR, hRint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hX hx2X hwX h2n hwn
  have hw2 := hwc (x 2) (Or.inr rfl)
  have hR3 := AntiholeCompletion.three_le_length_of_antipath hR hw2.symm
  have hRmem : ∀ a ∈ R, a = x 2 ∨ a = w ∨ a ∈ ({x 0, x 1} : Set V) := by
    intro a ha
    by_cases h2 : a = x 2
    · exact Or.inl h2
    by_cases he : a = w
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (hRint a
        ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨ha, h2, he⟩)))
  have hyR : y ∉ R := by
    intro hy
    rcases hRmem y hy with he | he | he | he
    · exact (hHyp.1 y hyY).2.2.2 he
    · exact (hwc y (Or.inl hyY)).ne he.symm
    · exact (hHyp.1 y hyY).2.1 he
    · exact (hHyp.1 y hyY).2.2.1 he
  have hzR : z ∉ R := by
    intro hz
    rcases hRmem z hz with he | he | he | he
    · exact (hws.2.2.2.2.2.2 2 (by omega)).ne he
    · exact hzP (he ▸ hwP)
    · exact (hws.2.2.2.2.2.2 0 (by omega)).ne he
    · exact (hws.2.2.2.2.2.2 1 (by omega)).ne he
  have hS : IsAntipathFrom G (y :: (R ++ [z])) y z := by
    apply PathAttach.isPathFrom_cons_concat hR
    · exact ⟨(hHyp.1 y hyY).2.2.2, fun h => h2y h.symm⟩
    · exact ⟨fun he => hzP (he ▸ hwP), wheelSystemA_no_z w (hPint w hw)⟩
    · exact fun h => h.2 hyz
    · exact hyz.ne
    · exact hyR
    · exact hzR
    · intro a ha hn hcon
      apply hcon.2
      rcases hRmem a ha with he | he | he | he
      · exact (hn he).elim
      · rw [he]; exact (hwc y (Or.inl hyY)).symm
      · rw [he]; exact (hHyp.2.2.1 y hyY).symm
      · rw [he]; exact (hHyp.2.2.2.1 y hyY).symm
    · intro a ha hn hcon
      apply hcon.2
      rcases hRmem a ha with he | he | he | he
      · rw [he]; exact hws.2.2.2.2.2.2 2 (by omega)
      · exact (hn he).elim
      · rw [he]; exact hws.2.2.2.2.2.2 0 (by omega)
      · rw [he]; exact hws.2.2.2.2.2.2 1 (by omega)
  have hSint : interior (y :: (R ++ [z])) = R := by simp [Workspace.Types.Core.SPGT.interior]
  have hSc : ∀ a ∈ interior (y :: (R ++ [z])), VertexComplete G a (Y \ {y}) := by
    rw [hSint]
    intro a ha b hb
    rcases hRmem a ha with he | he | he | he
    · rw [he]; exact h2c b hb
    · rw [he]; exact hwc b (Or.inl hb.1)
    · rw [he]; exact hHyp.2.2.1 b hb.1
    · rw [he]; exact hHyp.2.2.2.1 b hb.1
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (PathBasics.interior_ne_nil hR.1 hR3)
  have hrX := hRint r hr
  have hrP : r ∈ P := by
    rcases hrX with he | he
    · rw [he]; exact PathBasics.head_mem hP.2.1
    · rw [he]; exact PathBasics.getLast_mem hP.2.2
  have hwr : w ≠ r := by
    intro he
    exact hwX (he ▸ hrX)
  apply Thm192Infra.antipathExtendToAntihole hG.1 hyz.symm hQ hQint hS
    (by simp only [List.length_cons, List.length_append, List.length_singleton]; omega)
    hSc hrim.1 (by have := hrim.2; omega)
    (c₀ := z) (c₁ := w) (c₂ := r)
    (fun he => hzP (he ▸ hwP)) (fun he => hzP (he ▸ hrP)) hwr
    List.mem_cons_self (List.mem_cons_of_mem _ hwP) (List.mem_cons_of_mem _ hrP)
  · exact List.mem_append_left _ (PathBasics.head_mem hQ.2.1)
  · rw [hSint]; exact List.mem_append_right _ (PathBasics.getLast_mem hR.2.2)
  · rw [hSint]; exact List.mem_append_right _ (PathBasics.interior_subset hr)

end Workspace.ProofLemmas.Thm192Claim4Antihole
