import Workspace.ProofLemmas.Thm131Enlarge
import Workspace.ProofLemmas.Thm131Prefix
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_8
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Claim (2) of the printed proof of 13.1

PAPER (printed p. 79):

*"(2) If `wₙ` has a neighbour in `A` then the theorem holds.*

*For choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂` such that `wₙ` is adjacent to `a₁` and
not to `a₂`.  Then `a₁`, `b₂` are `W`-complete.  Suppose first that there are no
`W`-complete vertices in `R`.  Then `a₁-a-R-b-b₂` is an odd path between
`W`-complete vertices.  If `R` has length 1 then there is an antipath `Q` joining
`a`, `b` with interior in `W`, and since it can be completed to an antihole via
`b-a₁-b₂-a`, it has odd length and the theorem holds.  So we may assume `R` has
length > 1, and hence by 2.1 `W` contains a leap.  Since all vertices of `W`
except `w₁` are adjacent to `a`, the leap is `w₁, w₂`; and hence the only edges
between `w₁, w₂` and `R` are `w₁b` and `w₂a`.  Since `n` is odd it follows that
`n > 2` and so `w₁, w₂` are both `A ∪ B`-complete.  But then
`S' = (A ∪ {w₂}, C, B ∪ {w₁})` is a step-connected strip, and `(S', a-R-b)` is a
staircase, contrary to the maximality of `(S, R₀)`.  So we may assume there are
`W`-complete vertices in `R`.  If `b` is the only one then the theorem holds, so
assume there is another.  But then `W` can be linked onto the triangle
`{a, a₁, a₂}`, via a subpath of `R \ b`, the 1-vertex path `a₁`, and a subpath of
`R₂`.  Since `b₁` is `W`-complete and nonadjacent to both `a`, `a₂`, this
contradicts 2.8.  This proves (2)."*
-/

namespace Workspace.ProofLemmas.Thm131Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131Enlarge
open Workspace.ProofLemmas.Thm131Prefix
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim (2). -/
theorem claim_two
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (P₁ P₂ P₃ : List V), IsEvenPrism G s t P₁ P₂ P₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    {a b last : V} {R w : List V}
    (hR : IsBanister G A C B a R b)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hnbA : ∃ z ∈ A, G.Adj last z)
    (hmissA : ∃ z ∈ A, ¬ G.Adj last z) :
    TrajectoryConclusion G a R b w := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hwpos : 0 < w.length := by obtain ⟨k, hk⟩ := hodd; omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  have hwnodup : w.Nodup := (List.nodup_cons.mp hanti.1.2.1).2
  have hanodup : (a :: w).Nodup := hanti.1.2.1
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  have hlastw : last ∈ w := Workspace.ProofLemmas.PathBasics.getLast_mem hlastW
  have hlastElem : w[w.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW hwpos
  set W : Set V := {u : V | u ∈ w} with hWdef
  have hWanti : AnticonnectedSet G W := by
    apply Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    exact HyperprismRungStructure.isPathList_tail hanti.1 (by simp; omega)
  -- `a` sees every trajectory vertex but the first
  have haw : ∀ (j : ℕ) (hj : j < w.length), j ≠ 0 → G.Adj a (w[j]'hj) := by
    intro j hj hj0
    have h1 : ((a :: w)[0]'(by simp)) = a := by simp
    have h2 : ((a :: w)[j + 1]'(by simp; omega)) = w[j]'hj := by simp
    have hnadj : ¬ Gᶜ.Adj ((a :: w)[0]'(by simp))
        ((a :: w)[j + 1]'(by simp; omega)) := by
      intro hadj
      have := (Workspace.ProofLemmas.PathBasics.path_adj_iff hanti.1 (by simp)
        (by simp; omega)).1 hadj
      omega
    rw [h1, h2] at hnadj
    have hne : a ≠ w[j]'hj := by
      intro he
      have heq : ((a :: w)[0]'(by simp)) = ((a :: w)[j + 1]'(by simp; omega)) := by
        rw [h1, h2]; exact he
      have := (List.Nodup.getElem_inj_iff hanodup).mp heq
      omega
    by_contra hadj
    exact hnadj ((G.compl_adj a _).mpr ⟨hne, hadj⟩)
  have haNotW : ¬ VertexComplete G a W := by
    intro hc
    have h0 : (w[0]'hwpos) ∈ W := List.getElem_mem hwpos
    have hadj : Gᶜ.Adj a (w[0]'hwpos) := by
      have hp := Workspace.ProofLemmas.PathBasics.path_adj_succ hanti.1 (i := 0)
        (by simp; omega)
      simpa using hp
    exact hadj.2 (hc _ h0)
  -- PAPER: *"choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂` such that `wₙ` is adjacent to
  -- `a₁` and not to `a₂`"*
  obtain ⟨c₀, hc₀A, hc₀adj⟩ := hnbA
  obtain ⟨d₀, hd₀A, hd₀adj⟩ := hmissA
  have hstepEx : ∃ (a₁ : V) (R₁ : List V) (b₁ a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ a₁ ∈ A ∧ G.Adj last a₁ ∧
        a₂ ∈ A ∧ ¬ G.Adj last a₂ := by
    let X : Set V := {z : V | z ∈ A ∧ G.Adj last z}
    let Y : Set V := {z : V | z ∈ A ∧ ¬ G.Adj last z}
    have hXYunion : X ∪ Y = A := by
      ext z
      simp only [X, Y, Set.mem_union, Set.mem_setOf_eq]
      tauto
    have hXYdis : Disjoint X Y := Set.disjoint_left.mpr fun z hzX hzY => hzY.2 hzX.2
    have hXne : X.Nonempty := ⟨c₀, hc₀A, hc₀adj⟩
    have hYne : Y.Nonempty := ⟨d₀, hd₀A, hd₀adj⟩
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hfirst, hsecond⟩ :=
      hS.2.2.2.2 X Y (Or.inl hXYunion) hXYdis hXne hYne
    have ha₁X : a₁ ∈ X := by
      rcases hfirst with ha₁X | hb₁X
      · exact ha₁X
      · exact absurd hb₁X.1 (Set.disjoint_right.mp hS.1.1 hs.1.2.2.1)
    have ha₂Y : a₂ ∈ Y := by
      rcases hsecond with ha₂Y | hb₂Y
      · exact ha₂Y
      · exact absurd hb₂Y.1 (Set.disjoint_right.mp hS.1.1 hs.2.1.2.2.1)
    exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, ha₁X.1, ha₁X.2, ha₂Y.1, ha₂Y.2⟩
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, ha₁A, hlasta₁, ha₂A, hlasta₂⟩ := hstepEx
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ := Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ :=
    Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := Workspace.ProofLemmas.PathBasics.head_mem hstep.2.1.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ :=
    Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2
  -- PAPER: *"Then `a₁`, `b₂` are `W`-complete."*
  have ha₁W : VertexComplete G a₁ W := by
    intro z hz
    by_cases hzl : z = last
    · exact hzl ▸ hlasta₁.symm
    · exact (hbeforeA z hz hzl a₁ ha₁A).symm
  have hb₂W : VertexComplete G b₂ W := fun z hz => (hwB z hz b₂ hb₂B).symm
  have hb₁W : VertexComplete G b₁ W := fun z hz => (hwB z hz b₁ hb₁B).symm
  have ha₂NotW : ¬ VertexComplete G a₂ W := fun hc => hlasta₂ (hc last hlastw).symm
  have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
    intro hadj
    rcases (hstep.2.2.2 a₁ ha₁R₁ b₂ hb₂R₂).1 hadj with h | h
    · exact Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1 (h.2 ▸ hb₂B)
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hb₁B)
  have hb₁a₂ : ¬ G.Adj b₁ a₂ := by
    intro hadj
    rcases (hstep.2.2.2 b₁ hb₁R₁ a₂ ha₂R₂).1 hadj with h | h
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1 ▸ hb₁B)
    · exact Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1 (h.2 ▸ hb₂B)
  have hb₁a : ¬ G.Adj b₁ a := fun hadj =>
    hR.2.2.1.2.2 b₁ (Or.inl hb₁B) hadj.symm
  -- structural facts about the banister
  have hRodd : Odd (pathLength R) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b R hR).2
  have hRlen : R.length = pathLength R + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hR.1.1
  have hRpos : 0 < R.length := by omega
  have hR0 : R[0]'hRpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR.1.2.1 hRpos
  have hRb : R[R.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.1.2.2 hRpos
  have hRnodup : R.Nodup := Workspace.ProofLemmas.PathBasics.path_nodup hR.1.1
  have haR : a ∈ R := Workspace.ProofLemmas.PathBasics.head_mem hR.1.2.1
  have hbR : b ∈ R := Workspace.ProofLemmas.PathBasics.getLast_mem hR.1.2.2
  obtain ⟨b', hb'B⟩ := hS.2.1.2
  have hRw : ∀ z ∈ R, z ∉ w := by
    intro z hz hzw
    by_cases hza : z = a
    · exact (List.nodup_cons.mp hanodup).1 (hza ▸ hzw)
    by_cases hzb : z = b
    · exact hbnotw (hzb ▸ hzw)
    · exact hR.2.2.2.2 z
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
          ⟨hz, hza, hzb⟩) b' (Or.inl (Or.inr hb'B)) (hwB z hzw b' hb'B)
  have ha₁a : G.Adj a₁ a := (hR.2.2.1.2.1 a₁ ha₁A).symm
  have hb₂b : G.Adj b₂ b := (hR.2.2.2.1.2.1 b₂ hb₂B).symm
  have ha₁notR : a₁ ∉ R := fun h => hR.2.1 a₁ h (Or.inl (Or.inl ha₁A))
  have hb₂notR : b₂ ∉ R := fun h => hR.2.1 b₂ h (Or.inl (Or.inr hb₂B))
  have ha₁ne : a₁ ≠ b₂ := fun he => Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₂B)
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
  by_cases hcomp : ∃ r ∈ R, VertexComplete G r W
  · -- PAPER: *"So we may assume there are `W`-complete vertices in `R`."*
    by_cases hother : ∃ r ∈ R, r ≠ b ∧ VertexComplete G r W
    · exfalso
      -- PAPER: *"But then `W` can be linked onto the triangle `{a, a₁, a₂}` …
      -- this contradicts 2.8."*
      have hex : ∃ k : ℕ, ∃ hk : k < R.length,
          VertexComplete G (R[k]'hk) W := by
        obtain ⟨r, hrR, -, hrW⟩ := hother
        obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hrR
        exact ⟨k, hk, by rw [hkr]; exact hrW⟩
      obtain ⟨hmR, hmW⟩ := Nat.find_spec hex
      set m : ℕ := Nat.find hex with hmdef
      have hmmin : ∀ (k : ℕ) (hk : k < R.length), k < m →
          ¬ VertexComplete G (R[k]'hk) W := by
        intro k hk hlt hc
        exact Nat.find_min hex hlt ⟨hk, hc⟩
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h1
        · exfalso
          apply haNotW
          have hEq : R[m]'hmR = a := by
            rw [(getElem_congr rfl h0 hmR : R[m]'hmR = R[0]'hRpos)]
            exact hR0
          exact hEq ▸ hmW
        · exact h1
      have hmlt : m < R.length - 1 := by
        obtain ⟨r, hrR, hrb, hrW⟩ := hother
        obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hrR
        have hkne : k ≠ R.length - 1 := by
          intro he
          apply hrb
          rw [← hkr]
          exact (getElem_congr rfl he hk :
            R[k]'hk = R[R.length - 1]'(by omega)).trans hRb
        have hle : m ≤ k := Nat.find_le ⟨hk, by rw [hkr]; exact hrW⟩
        omega
      -- the subpath `a-P₁-p` of `R \ b`
      have htakelen : (R.take (m + 1)).length = m + 1 := by
        simp only [List.length_take]; omega
      have htakeget : ∀ (k : ℕ) (hk : k < (R.take (m + 1)).length),
          (R.take (m + 1))[k]'hk = R[k]'(by rw [htakelen] at hk; omega) := by
        intro k hk; simp
      have hP₁ : IsPathFrom G (R.take (m + 1)) a (R[m]'hmR) := by
        refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hR.1.1 (by omega),
          ?_, ?_⟩
        · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          rw [htakeget 0 (by omega)]
          rw [hR0]
        · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          rw [htakeget ((R.take (m + 1)).length - 1) (by omega)]
          exact congrArg some (getElem_congr rfl (by omega) (by omega))
      have hP₁mem : ∀ z ∈ R.take (m + 1), ∃ (k : ℕ) (hk : k < R.length),
          k ≤ m ∧ z = R[k]'hk := by
        intro z hz
        obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
        rw [htakeget k hk] at hkz
        have hkR : k < R.length := by rw [htakelen] at hk; omega
        exact ⟨k, hkR, by rw [htakelen] at hk; omega, hkz.symm⟩
      have hu₁ : ∀ z ∈ R.take (m + 1),
          (VertexComplete G z W ↔ z = R[m]'hmR) := by
        intro z hz
        obtain ⟨k, hkR, hkm, hkz⟩ := hP₁mem z hz
        constructor
        · intro hc
          rcases lt_or_eq_of_le hkm with hlt | heq
          · exact absurd (hkz ▸ hc) (hmmin k hkR hlt)
          · rw [hkz]; exact getElem_congr rfl heq hkR
        · intro he
          rw [he]; exact hmW
      -- the subpath `a₂-P₃-q` of `R₂`
      have hR₂len : 0 < R₂.length :=
        Workspace.ProofLemmas.PathBasics.path_length_pos hstep.2.1.1.1
      have hR₂0 : R₂[0]'hR₂len = a₂ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hstep.2.1.1.2.1 hR₂len
      have hR₂b : R₂[R₂.length - 1]'(by omega) = b₂ :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hstep.2.1.1.2.2
          hR₂len
      have hex₂ : ∃ k : ℕ, ∃ hk : k < R₂.length,
          VertexComplete G (R₂[k]'hk) W :=
        ⟨R₂.length - 1, by omega, by rw [hR₂b]; exact hb₂W⟩
      obtain ⟨hkR₂, hkW⟩ := Nat.find_spec hex₂
      set k : ℕ := Nat.find hex₂ with hkdef
      have hkmin : ∀ (j : ℕ) (hj : j < R₂.length), j < k →
          ¬ VertexComplete G (R₂[j]'hj) W := by
        intro j hj hlt hc
        exact Nat.find_min hex₂ hlt ⟨hj, hc⟩
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h1
        · exfalso
          apply ha₂NotW
          have hEq : R₂[k]'hkR₂ = a₂ := by
            rw [(getElem_congr rfl h0 hkR₂ : R₂[k]'hkR₂ = R₂[0]'hR₂len)]
            exact hR₂0
          exact hEq ▸ hkW
        · exact h1
      have htake₂len : (R₂.take (k + 1)).length = k + 1 := by
        simp only [List.length_take]; omega
      have htake₂get : ∀ (j : ℕ) (hj : j < (R₂.take (k + 1)).length),
          (R₂.take (k + 1))[j]'hj = R₂[j]'(by rw [htake₂len] at hj; omega) := by
        intro j hj; simp
      have hP₃ : IsPathFrom G (R₂.take (k + 1)) a₂ (R₂[k]'hkR₂) := by
        refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hstep.2.1.1.1
          (by omega), ?_, ?_⟩
        · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          rw [htake₂get 0 (by omega)]
          rw [hR₂0]
        · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          rw [htake₂get ((R₂.take (k + 1)).length - 1) (by omega)]
          exact congrArg some (getElem_congr rfl (by omega) (by omega))
      have hu₃ : ∀ z ∈ R₂.take (k + 1),
          (VertexComplete G z W ↔ z = R₂[k]'hkR₂) := by
        intro z hz
        obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
        rw [htake₂get j hj] at hjz
        have hjR : j < R₂.length := by rw [htake₂len] at hj; omega
        have hjk : j ≤ k := by rw [htake₂len] at hj; omega
        constructor
        · intro hc
          rcases lt_or_eq_of_le hjk with hlt | heq
          · exact absurd (hjz ▸ hc) (hkmin j hjR hlt)
          · rw [← hjz]; exact getElem_congr rfl heq hjR
        · intro he
          rw [← hjz] at he ⊢
          rw [he]
          exact hkW
      -- the linkage
      have hlink : SetLinkedOntoTriangle G W a a₁ a₂
          (R.take (m + 1)) [a₁] (R₂.take (k + 1)) := by
        refine ⟨⟨hP₁.1, Workspace.ProofLemmas.PathBasics.isPathList_singleton G a₁,
          hP₃.1⟩, ⟨?_, ?_, ?_⟩, ⟨Or.inl hP₁.2.1, Or.inl rfl, Or.inl hP₃.2.1⟩,
          ⟨?_, ?_, ?_⟩, ⟨⟨R[m]'hmR, ?_, hmW⟩, ⟨a₁, by simp, ha₁W⟩,
            ⟨R₂[k]'hkR₂, ?_, hkW⟩⟩⟩
        · intro z hz hz'
          have hza₁ : z = a₁ := by simpa using hz'
          exact ha₁notR (hza₁ ▸ List.mem_of_mem_take hz)
        · intro z hz hz'
          exact hR.2.1 z (List.mem_of_mem_take hz)
            (rung_mem_strip hstep.2.1 z (List.mem_of_mem_take hz'))
        · intro z hz hz'
          have hza₁ : z = a₁ := by simpa using hz
          exact hstep.2.2.1 a₁ ha₁R₁ (hza₁ ▸ List.mem_of_mem_take hz')
        · intro x hx y hy
          have hya₁ : y = a₁ := by simpa using hy
          obtain ⟨j, hjR, hjm, hjx⟩ := hP₁mem x hx
          constructor
          · intro hadj
            refine ⟨?_, hya₁⟩
            by_contra hxa
            exact ha₁other x (List.mem_of_mem_take hx) hxa (hya₁ ▸ hadj.symm)
          · rintro ⟨hxa, hyy⟩
            rw [hxa, hyy]
            exact ha₁a.symm
        · intro x hx y hy
          constructor
          · intro hadj
            have hyR₂ : y ∈ R₂ := List.mem_of_mem_take hy
            have hxR : x ∈ R := List.mem_of_mem_take hx
            have hxa : x = a := by
              by_contra hxa
              have hxint : x ∈ SPGT.interior R :=
                (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom
                  hR.1).2 ⟨hxR, hxa, ?_⟩
              · exact hR.2.2.2.2 x hxint y (rung_mem_strip hstep.2.1 y hyR₂) hadj
              · intro he
                obtain ⟨j, hjR, hjm, hjx⟩ := hP₁mem x hx
                have : R[j]'hjR = R[R.length - 1]'(by omega) := by
                  rw [← hjx, he, hRb]
                have := (List.Nodup.getElem_inj_iff hRnodup).mp this
                omega
            have hya₂ : y = a₂ := by
              by_contra hya
              have hyA : y ∉ A := by
                intro hyA
                exact hya (hstep.2.1.2.2.2.1 y hyR₂ hyA)
              rcases rung_mem_strip hstep.2.1 y hyR₂ with (h | h) | h
              · exact hyA h
              · exact hR.2.2.1.2.2 y (Or.inl h) (hxa ▸ hadj)
              · exact hR.2.2.1.2.2 y (Or.inr h) (hxa ▸ hadj)
            exact ⟨hxa, hya₂⟩
          · rintro ⟨hxa, hya⟩
            rw [hxa, hya]
            exact hR.2.2.1.2.1 a₂ ha₂A
        · intro x hx y hy
          have hxa₁ : x = a₁ := by simpa using hx
          have hyR₂ : y ∈ R₂ := List.mem_of_mem_take hy
          constructor
          · intro hadj
            refine ⟨hxa₁, ?_⟩
            rcases (hstep.2.2.2 a₁ ha₁R₁ y hyR₂).1 (hxa₁ ▸ hadj) with h | h
            · exact h.2
            · exact absurd h.1.symm (fun he =>
                Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₁B))
          · rintro ⟨hx1, hy2⟩
            rw [hx1, hy2]
            exact ((hstep.2.2.2 a₁ ha₁R₁ a₂ ha₂R₂).2 (Or.inl ⟨rfl, rfl⟩))
        · have hlt : m < (R.take (m + 1)).length := by rw [htakelen]; omega
          have := htakeget m hlt
          exact this ▸ List.getElem_mem hlt
        · have hlt : k < (R₂.take (k + 1)).length := by rw [htake₂len]; omega
          have := htake₂get k hlt
          exact this ▸ List.getElem_mem hlt
      have hlen₁ : pathLength (R.take (m + 1)) = m := by
        simp only [pathLength, htakelen]
        omega
      have hlen₃ : pathLength (R₂.take (k + 1)) = k := by
        simp only [pathLength, htake₂len]
        omega
      have hu₂ : ∀ z ∈ [a₁], (VertexComplete G z W ↔ z = a₁) := by
        intro z hz
        have hz1 : z = a₁ := by simpa using hz
        rw [hz1]
        exact iff_of_true ha₁W rfl
      rcases Workspace.Statements.S02.SPGT.thm_2_8 G hG W hWanti a a₁ a₂
          (R[m]'hmR) a₁ (R₂[k]'hkR₂) (R.take (m + 1)) [a₁] (R₂.take (k + 1))
          hlink hP₁ ⟨Workspace.ProofLemmas.PathBasics.isPathList_singleton G a₁,
            rfl, rfl⟩ hP₃ hu₁ hu₂ hu₃ with
        hfirst | hsecond
      · rcases hfirst with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h3⟩ <;> omega
      · rcases hsecond with ⟨h3, -⟩ | ⟨-, -, -, hall⟩ | ⟨h1, -⟩
        · omega
        · rcases hall b₁ hb₁W with h | h
          · exact hb₁a h
          · exact hb₁a₂ h
        · omega
    · -- PAPER: *"If `b` is the only one then the theorem holds"*
      push Not at hother
      have hkey : ∀ z ∈ R, VertexComplete G z W → z = b := by
        intro z hz hc
        by_contra hne
        exact hother z hz hne hc
      obtain ⟨r, hrR, hrW⟩ := hcomp
      have hrb : r = b := hkey r hrR hrW
      refine ⟨hodd, Or.inl ?_⟩
      intro z hzR
      constructor
      · intro hc
        exact hkey z hzR hc
      · rintro rfl
        exact hrb ▸ hrW
  · -- PAPER: *"Suppose first that there are no `W`-complete vertices in `R`."*
    push Not at hcomp
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
      obtain ⟨mm, hmm⟩ := hRodd
      exact ⟨mm + 1, by omega⟩
    have hUmem : ∀ z ∈ U, z = a₁ ∨ z ∈ R ∨ z = b₂ := by
      intro z hz
      simpa [hUdef] using
        (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton (x := z)
          (s := a₁) (t := b₂) (p := R)).1 (by simpa [hUdef] using hz)
    have hUW : ∀ z ∈ U, z ∉ W := by
      intro z hz hzW
      rcases hUmem z hz with hz₁ | hz₂ | hz₃
      · exact bComplete_not_mem_strip hS (hwB z hzW) (hz₁ ▸ Or.inl (Or.inl ha₁A))
      · exact hRw z hz₂ hzW
      · exact bComplete_not_mem_strip hS (hwB z hzW) (hz₃ ▸ Or.inl (Or.inr hb₂B))
    rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG W hWanti U a₁ b₂ hU hUW
        hUodd ha₁W hb₂W with hedge | hleap | hshort
    · exfalso
      obtain ⟨u, hu, v, hv, huv, huW, hvW⟩ := hedge
      rcases hUmem u hu with hu₁ | hu₂ | hu₃ <;> rcases hUmem v hv with hv₁ | hv₂ | hv₃
      · exact huv.ne (hu₁.trans hv₁.symm)
      · exact hcomp v hv₂ hvW
      · exact ha₁b₂ (hu₁ ▸ hv₃ ▸ huv)
      · exact hcomp u hu₂ huW
      · exact hcomp u hu₂ huW
      · exact hcomp u hu₂ huW
      · exact ha₁b₂ (hv₁ ▸ hu₃ ▸ huv.symm)
      · exact hcomp v hv₂ hvW
      · exact huv.ne (hu₃.trans hv₃.symm)
    · exfalso
      -- PAPER: *"by 2.1 `W` contains a leap … the leap is `w₁, w₂` … a
      -- staircase, contrary to the maximality of `(S, R₀)`"*
      obtain ⟨h5, x, hxW, y, hyW, hleapxy⟩ := hleap
      obtain ⟨-, -, hxyne, hxynadj, hxadj, hyadj⟩ := hleapxy
      have hxw : x ∈ w := hxW
      have hyw : y ∈ w := hyW
      have hRlen4 : 4 ≤ R.length := by omega
      have hR3 : 3 ≤ pathLength R := by omega
      -- `y` is the first trajectory vertex
      have hya : ¬ G.Adj y a := by
        intro hadj
        have h1 : G.Adj y (U[1]'(by omega)) := by
          rw [hUget 0 hRpos, hR0]; exact hadj
        rcases (hyadj 1 (by omega)).1 h1 with h | h | h <;> omega
      obtain ⟨ky, hky, hkyy⟩ := List.mem_iff_getElem.mp hyw
      have hky0 : ky = 0 := by
        by_contra hne
        exact hya (by rw [← hkyy]; exact (haw ky hky hne).symm)
      have hy0 : y = w[0]'hwpos := by
        rw [← hkyy]; exact getElem_congr rfl hky0 hky
      -- `x` is the second
      obtain ⟨kx, hkx, hkxx⟩ := List.mem_iff_getElem.mp hxw
      have hxyc : Gᶜ.Adj x y := (G.compl_adj x y).mpr ⟨hxyne, hxynadj⟩
      have hkx1 : kx = 1 := by
        have h1 : ((a :: w)[kx + 1]'(by simp; omega)) = x := by simpa using hkxx
        have h2 : ((a :: w)[0 + 1]'(by simp; omega)) = y := by
          simpa using hy0.symm
        have hadj : Gᶜ.Adj ((a :: w)[kx + 1]'(by simp; omega))
            ((a :: w)[0 + 1]'(by simp; omega)) := by
          rw [h1, h2]; exact hxyc
        have := (Workspace.ProofLemmas.PathBasics.path_adj_iff hanti.1
          (by simp; omega) (by simp; omega)).1 hadj
        omega
      have hwlen2 : 2 ≤ w.length := by omega
      have hwlen3 : 3 ≤ w.length := by
        obtain ⟨kk, hkk⟩ := hodd
        omega
      have hxlast : x ≠ last := by
        rw [← hkxx]
        intro he
        have := (List.Nodup.getElem_inj_iff hwnodup).mp (he.trans hlastElem.symm)
        omega
      have hylast : y ≠ last := by
        rw [← hkyy]
        intro he
        have := (List.Nodup.getElem_inj_iff hwnodup).mp (he.trans hlastElem.symm)
        omega
      have hxAB : VertexComplete G x (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hbeforeA x hxw hxlast z hzA
        · exact hwB x hxw z hzB
      have hyAB : VertexComplete G y (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hbeforeA y hyw hylast z hzA
        · exact hwB y hyw z hzB
      have hxout : x ∉ A ∪ B ∪ C := bComplete_not_mem_strip hS (hwB x hxw)
      have hyout : y ∉ A ∪ B ∪ C := bComplete_not_mem_strip hS (hwB y hyw)
      have hxa : G.Adj x a := by
        have h1 := (hxadj 1 (by omega)).2 (Or.inr (Or.inl rfl))
        rw [hUget 0 hRpos, hR0] at h1
        exact h1
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
      exact adjoin_complete_pair_absurd hK.1 hxout
        (staircase_adjoin_complete_pair hS hxout hyout hxAB hyAB hxyne hxynadj
          hR hxa hyb hxother hyother hR3)
    · -- PAPER: *"If `R` has length 1 then there is an antipath `Q` joining
      -- `a`, `b` with interior in `W` … it has odd length and the theorem holds."*
      obtain ⟨h3, c, d, hint, Q, hQ, hQodd, hQint⟩ := hshort
      have hRone : pathLength R = 1 := by omega
      have hRlen2 : R.length = 2 := by omega
      have hUint : SPGT.interior U = R := by
        simp only [hUdef, SPGT.interior, List.tail_cons]
        exact List.dropLast_concat
      have hRcd : R = [c, d] := by rw [← hUint]; exact hint
      have hca : c = a := by
        have h := hR.1.2.1
        rw [hRcd] at h
        simpa using h
      have hdb : d = b := by
        have h := hR.1.2.2
        rw [hRcd] at h
        simpa using h
      rw [hca, hdb] at hQ
      have hab : G.Adj a b :=
        Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hR.1 hRone
      have hQ3 : 3 ≤ Q.length :=
        Workspace.ProofLemmas.AntiholeCompletion.three_le_length_of_antipath hQ hab
      obtain ⟨mm, hmm1, hmmw, hQeq⟩ :=
        antipath_prefix hanti.1 hQ (fun z hz => hQint z hz) hQ3
      have hQlen : pathLength Q = mm + 1 := by
        have hc : Q.length = mm + 2 := by
          rw [hQeq]
          simp only [List.length_cons, List.length_append, List.length_nil,
            List.length_take, Nat.min_eq_left hmmw]
        simp only [pathLength, hc]
        omega
      have hmmeven : Even mm := by
        obtain ⟨kk, hkk⟩ := hQodd
        exact ⟨mm / 2, by omega⟩
      have hmmlt : mm < w.length := by
        rcases lt_or_eq_of_le hmmw with h | h
        · exact h
        · exfalso
          obtain ⟨kk, hkk⟩ := hQodd
          obtain ⟨ll, hll⟩ := hodd
          omega
      refine ⟨hodd, Or.inr ⟨hRone, mm, hmmeven, hmm1, hmmlt, ?_⟩⟩
      rw [← hQeq]
      exact hQ.1

end Workspace.ProofLemmas.Thm131Claim2
