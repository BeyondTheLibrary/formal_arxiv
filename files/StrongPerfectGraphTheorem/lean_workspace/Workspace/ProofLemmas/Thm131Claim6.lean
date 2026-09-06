import Workspace.ProofLemmas.Thm131Enlarge
import Workspace.ProofLemmas.Thm131EdgeCases
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Claim (6) of the printed proof of 13.1

PAPER (printed pp. 80–81):

*"(6) If `b` is not `(W \ {wₙ})`-complete and no edge of `R` is
`(W \ {wₙ})`-complete then the theorem holds.*

*For choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`.  Then `a₁-a-R-b-b₂` is an odd path,
its ends are `(W \ {wₙ})`-complete, and none of its edges are
`(W \ {wₙ})`-complete.  Suppose first that `R` has length ≥ 3.  Then by 2.1
there is a leap in `W \ {wₙ}`; and so there are nonadjacent vertices
`x, y ∈ W \ {wₙ}` such that `x-a-R-b-y` is a path.  But then
`((A ∪ {x}, ∅, B ∪ {y}), a-R-b)` is a staircase, contrary to the maximality of
`(S, R₀)`.  So `R` has length 1, and there exists `i` with `1 ≤ i < n` such that
`a-w₁-⋯-w_i-b` is an odd antipath.  But then the theorem holds.  This proves
(6)."*
-/

namespace Workspace.ProofLemmas.Thm131Claim6

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131EdgeCases
open Workspace.ProofLemmas.Thm131Enlarge
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim (6). -/
theorem claim_six
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (P₁ P₂ P₃ : List V), IsEvenPrism G s t P₁ P₂ P₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    {a b last : V} {R w : List V}
    (hR : IsBanister G A C B a R b)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length) (hwlong : 1 < w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hbmiss : ¬ VertexComplete G b {z : V | z ∈ w.dropLast})
    (hnoedge : ¬ ∃ u ∈ R, ∃ v ∈ R, EdgeComplete G {z : V | z ∈ w.dropLast} u v) :
    TrajectoryConclusion G a R b w := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  set W' : Set V := {z : V | z ∈ w.dropLast} with hW'def
  have hwnodup : w.Nodup := (List.nodup_cons.mp hanti.1.2.1).2
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  have hlastEq : w.getLast hwne = last := by
    have hh := hlastW
    rw [List.getLast?_eq_some_getLast hwne] at hh
    exact Option.some.inj hh
  have hlastElem : w[w.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW (by omega)
  have hW'mem : ∀ z ∈ W', z ∈ w ∧ z ≠ last := by
    intro z hz
    have h := (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hwnodup hwne).1 hz
    exact ⟨h.1, by rw [← hlastEq]; exact h.2⟩
  have hW'of : ∀ (j : ℕ) (hj : j + 1 < w.length), (w[j]'(by omega)) ∈ W' := by
    intro j hj
    apply (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hwnodup hwne).2
    refine ⟨List.getElem_mem _, ?_⟩
    rw [hlastEq]
    intro he
    have : j = w.length - 1 := (List.Nodup.getElem_inj_iff hwnodup).mp
      (he.trans hlastElem.symm)
    omega
  -- the first index at which `b` misses the trajectory
  have hex : ∃ k : ℕ, ∃ hk : k < w.length, ¬ G.Adj b (w[k]'hk) := by
    rw [VertexComplete] at hbmiss
    push Not at hbmiss
    obtain ⟨z, hzW, hbz⟩ := hbmiss
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp (hW'mem z hzW).1
    exact ⟨k, hk, by simpa [hkz] using hbz⟩
  set k : ℕ := Nat.find hex with hkdef
  obtain ⟨hk, hbk⟩ := Nat.find_spec hex
  have hbprev : ∀ (j : ℕ) (hj : j < k), G.Adj b (w[j]'(by omega)) := by
    intro j hj
    by_contra hn
    exact Nat.find_min hex hj ⟨by omega, hn⟩
  have hkearly : k + 1 < w.length := by
    rw [VertexComplete] at hbmiss
    push Not at hbmiss
    obtain ⟨z, hzW, hbz⟩ := hbmiss
    obtain ⟨k₀, hk₀, hk₀z⟩ := List.mem_iff_getElem.mp (hW'mem z hzW).1
    have hk₀ne : k₀ ≠ w.length - 1 := by
      intro he
      apply (hW'mem z hzW).2
      rw [← hk₀z]
      exact (getElem_congr rfl he hk₀ : w[k₀] = w[w.length - 1]'(by omega)).trans hlastElem
    have hkk₀ : k ≤ k₀ := Nat.find_le ⟨hk₀, by simpa [hk₀z] using hbz⟩
    omega
  by_cases hRone : pathLength R = 1
  · -- PAPER: *"So `R` has length 1, and there exists `i` with `1 ≤ i < n` such
    -- that `a-w₁-⋯-w_i-b` is an odd antipath.  But then the theorem holds."*
    have hab : G.Adj a b :=
      Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hR.1 hRone
    obtain ⟨hkeven, hantiPrefix⟩ := early_miss_gives_second_outcome
      hG hS hR.2.2.1 hR.2.2.2.1 hab hanti hbeforeA hwB hbnotw k hk hbk hbprev hkearly
    exact ⟨hodd, Or.inr ⟨hRone, k + 1, hkeven, by omega, hkearly, hantiPrefix⟩⟩
  · exfalso
    -- PAPER: *"Suppose first that `R` has length ≥ 3."*
    have hRodd : Odd (pathLength R) :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b R hR).2
    have hR3 : 3 ≤ pathLength R := by
      obtain ⟨m, hm⟩ := hRodd
      omega
    have hRlen : R.length = pathLength R + 1 :=
      Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hR.1.1
    have hRpos : 0 < R.length := by omega
    have hR0 : R[0]'hRpos = a :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR.1.2.1 hRpos
    have hRb : R[R.length - 1]'(by omega) = b :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.1.2.2 hRpos
    obtain ⟨b', hb'B⟩ := hS.2.1.2
    -- PAPER: *"For choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`."*
    obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
    obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
    have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
    have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
      intro hadj
      rcases (hstep.2.2.2 a₁
        (Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1) b₂
        (Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2)).1 hadj with h | h
      · exact Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1 (h.2 ▸ hb₂B)
      · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hstep.1.2.2.1)
    have ha₁ne : a₁ ≠ b₂ := fun he => Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₂B)
    have ha₁a : G.Adj a₁ a := (hR.2.2.1.2.1 a₁ ha₁A).symm
    have hb₂b : G.Adj b₂ b := (hR.2.2.2.1.2.1 b₂ hb₂B).symm
    have ha₁notR : a₁ ∉ R := fun h => hR.2.1 a₁ h (Or.inl (Or.inl ha₁A))
    have hb₂notR : b₂ ∉ R := fun h => hR.2.1 b₂ h (Or.inl (Or.inr hb₂B))
    have ha₁other : ∀ z ∈ R, z ≠ a → ¬ G.Adj a₁ z := by
      intro z hz hza hadj
      by_cases hzb : z = b
      · exact hR.2.2.2.1.2.2 a₁ (Or.inl ha₁A) (hzb ▸ hadj).symm
      · exact hR.2.2.2.2 z
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
            ⟨hz, hza, hzb⟩) a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
    have hb₂other : ∀ z ∈ R, z ≠ b → ¬ G.Adj b₂ z := by
      intro z hz hzb hadj
      by_cases hza : z = a
      · exact hR.2.2.1.2.2 b₂ (Or.inl hb₂B) (hza ▸ hadj).symm
      · exact hR.2.2.2.2 z
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
            ⟨hz, hza, hzb⟩) b₂ (Or.inl (Or.inr hb₂B)) hadj.symm
    -- PAPER: *"Then `a₁-a-R-b-b₂` is an odd path"*
    set U : List V := a₁ :: (R ++ [b₂]) with hUdef
    have hU : IsPathFrom G U a₁ b₂ :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hR.1 ha₁a hb₂b
        ha₁b₂ ha₁ne ha₁notR hb₂notR ha₁other hb₂other
    have hUlen : U.length = R.length + 2 :=
      Workspace.ProofLemmas.PathAttach.length_cons_append_singleton a₁ b₂ R
    have hUplen : pathLength U = R.length + 1 :=
      Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton a₁ b₂ R
    have hUget : ∀ (j : ℕ) (hj : j < R.length),
        U[j + 1]'(by omega) = R[j]'hj := by
      intro j hj
      simp only [hUdef, List.getElem_cons_succ, List.getElem_append_left hj]
    have hUodd : Odd (pathLength U) := by
      obtain ⟨m, hm⟩ := hRodd
      exact ⟨m + 1, by omega⟩
    have hU5 : 5 ≤ pathLength U := by omega
    have hUmem : ∀ z ∈ U, z = a₁ ∨ z ∈ R ∨ z = b₂ := by
      intro z hz
      simpa [hUdef] using
        (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton (x := z)
          (s := a₁) (t := b₂) (p := R)).1 (by simpa [hUdef] using hz)
    have hRW' : ∀ z ∈ R, z ∉ W' := by
      intro z hz hzW
      have hzw : z ∈ w := (hW'mem z hzW).1
      by_cases hza : z = a
      · exact (List.nodup_cons.mp hanti.1.2.1).1 (hza ▸ hzw)
      by_cases hzb : z = b
      · exact hbnotw (hzb ▸ hzw)
      · exact hR.2.2.2.2 z
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
            ⟨hz, hza, hzb⟩) b' (Or.inl (Or.inr hb'B)) (hwB z hzw b' hb'B)
    have hUW' : ∀ z ∈ U, z ∉ W' := by
      intro z hz hzW
      rcases hUmem z hz with hz₁ | hz₂ | hz₃
      · exact bComplete_not_mem_strip hS (hwB z (hW'mem z hzW).1)
          (hz₁ ▸ Or.inl (Or.inl ha₁A))
      · exact hRW' z hz₂ hzW
      · exact bComplete_not_mem_strip hS (hwB z (hW'mem z hzW).1)
          (hz₃ ▸ Or.inl (Or.inr hb₂B))
    have ha₁W' : VertexComplete G a₁ W' := fun z hz =>
      (hbeforeA z (hW'mem z hz).1 (hW'mem z hz).2 a₁ ha₁A).symm
    have hb₂W' : VertexComplete G b₂ W' := fun z hz =>
      (hwB z (hW'mem z hz).1 b₂ hb₂B).symm
    have hW'anti : AnticonnectedSet G W' := by
      apply Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      have htail : IsPathList Gᶜ w :=
        HyperprismRungStructure.isPathList_tail hanti.1 (by simp; omega)
      exact HyperprismRungStructure.isPathList_dropLast htail (by omega)
    have haNotW' : ¬ VertexComplete G a W' := by
      intro hc
      have h0 : (w[0]'(by omega)) ∈ W' := hW'of 0 (by omega)
      have hadj : Gᶜ.Adj a (w[0]'(by omega)) := by
        have hp := Workspace.ProofLemmas.PathBasics.path_adj_succ hanti.1 (i := 0)
          (by simp; omega)
        simpa using hp
      exact hadj.2 (hc _ h0)
    rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG W' hW'anti U a₁ b₂ hU hUW'
        hUodd ha₁W' hb₂W' with hedge | hleap | hshort
    · -- PAPER: *"… and none of its edges are `(W \ {wₙ})`-complete."*
      obtain ⟨u, hu, v, hv, huv, huW, hvW⟩ := hedge
      rcases hUmem u hu with hu₁ | hu₂ | hu₃ <;> rcases hUmem v hv with hv₁ | hv₂ | hv₃
      · exact huv.ne (hu₁.trans hv₁.symm)
      · by_cases hva : v = a
        · exact haNotW' (hva ▸ hvW)
        · exact ha₁other v hv₂ hva (hu₁ ▸ huv)
      · exact ha₁b₂ (hu₁ ▸ hv₃ ▸ huv)
      · by_cases hua : u = a
        · exact haNotW' (hua ▸ huW)
        · exact ha₁other u hu₂ hua (hv₁ ▸ huv.symm)
      · exact hnoedge ⟨u, hu₂, v, hv₂, huv, huW, hvW⟩
      · by_cases hub : u = b
        · exact hbmiss (hub ▸ huW)
        · exact hb₂other u hu₂ hub (hv₃ ▸ huv.symm)
      · exact ha₁b₂ (hv₁ ▸ hu₃ ▸ huv.symm)
      · by_cases hvb : v = b
        · exact hbmiss (hvb ▸ hvW)
        · exact hb₂other v hv₂ hvb (hu₃ ▸ huv)
      · exact huv.ne (hu₃.trans hv₃.symm)
    · -- PAPER: *"Then by 2.1 there is a leap in `W \ {wₙ}`; and so there are
      -- nonadjacent vertices `x, y ∈ W \ {wₙ}` such that `x-a-R-b-y` is a path."*
      obtain ⟨-, x, hxW, y, hyW, hleapxy⟩ := hleap
      obtain ⟨-, -, hxyne, hxynadj, hxadj, hyadj⟩ := hleapxy
      have hxw : x ∈ w := (hW'mem x hxW).1
      have hyw : y ∈ w := (hW'mem y hyW).1
      have hxAB : VertexComplete G x (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hbeforeA x hxw (hW'mem x hxW).2 z hzA
        · exact hwB x hxw z hzB
      have hyAB : VertexComplete G y (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hbeforeA y hyw (hW'mem y hyW).2 z hzA
        · exact hwB y hyw z hzB
      have hxout : x ∉ A ∪ B ∪ C := bComplete_not_mem_strip hS (hwB x hxw)
      have hyout : y ∉ A ∪ B ∪ C := bComplete_not_mem_strip hS (hwB y hyw)
      have hxa : G.Adj x a := by
        have := (hxadj 1 (by omega)).2 (Or.inr (Or.inl rfl))
        rw [hUget 0 hRpos, hR0] at this
        exact this
      have hxother : ∀ z ∈ R, z ≠ a → ¬ G.Adj x z := by
        intro z hz hza hadj
        obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
        have hj0 : j ≠ 0 := by
          intro he
          apply hza
          rw [← hjz]
          exact (getElem_congr rfl he hj : R[j] = R[0]'hRpos).trans hR0
        have hxj : G.Adj x (U[j + 1]'(by omega)) := by
          rw [hUget j hj, hjz]; exact hadj
        rcases (hxadj (j + 1) (by omega)).1 hxj with h | h | h <;> omega
      have hyb : G.Adj y b := by
        have hlt : U.length - 2 < U.length := by omega
        have h1 := (hyadj (U.length - 2) hlt).2 (Or.inr (Or.inl rfl))
        have hidx : U.length - 2 = (R.length - 1) + 1 := by omega
        have heq : (U[U.length - 2]'hlt) = b := by
          rw [(getElem_congr rfl hidx hlt :
            U[U.length - 2]'hlt = U[(R.length - 1) + 1]'(by omega))]
          rw [hUget (R.length - 1) (by omega)]
          exact hRb
        rw [heq] at h1
        exact h1
      have hyother : ∀ z ∈ R, z ≠ b → ¬ G.Adj y z := by
        intro z hz hzb hadj
        obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
        have hjne : j ≠ R.length - 1 := by
          intro he
          exact hzb (hjz.symm.trans
            ((getElem_congr rfl he hj : R[j] = R[R.length - 1]'(by omega)).trans hRb))
        have hyj : G.Adj y (U[j + 1]'(by omega)) := by
          rw [hUget j hj, hjz]; exact hadj
        rcases (hyadj (j + 1) (by omega)).1 hyj with h | h | h <;> omega
      -- PAPER: *"But then `((A ∪ {x}, ∅, B ∪ {y}), a-R-b)` is a staircase,
      -- contrary to the maximality of `(S, R₀)`."*
      exact adjoin_complete_pair_absurd hK.1 hxout
        (staircase_adjoin_complete_pair hS hxout hyout hxAB hyAB hxyne hxynadj
          hR hxa hyb hxother hyother hR3)
    · obtain ⟨h3, -⟩ := hshort
      omega

end Workspace.ProofLemmas.Thm131Claim6
