import Workspace.ProofLemmas.Thm131OptimalLength
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.PathAttach

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm131EdgeCases

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A named path of length one is the two-element list of its ends. -/
theorem path_eq_pair_of_length_one {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hlen : pathLength P = 1) : P = [a, b] := by
  have hPtwo : P.length = 2 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
    omega
  obtain ⟨p, q, rfl⟩ := Workspace.ProofLemmas.PathGlue.length_eq_two hPtwo
  have hp : p = a := by simpa using hP.2.1
  have hq : q = b := by simpa using hP.2.2
  simp [hp, hq]

/-- The right end of an optimal banister cannot itself occur in the trajectory
tail.  Otherwise axiom 3 at that occurrence supplies a strictly earlier-born
banister with the same right end. -/
theorem optimal_right_end_not_mem_trajectory
    {G : SimpleGraph V} {A C B : Set V} (hS : StepConnected G A C B)
    {x : List V}
    (hx : IsRightSequence G A C B x)
    {a b : V} {R w : List V}
    (hb : IsRightStar G A C B b)
    (hopt : BOptimalBanister G A C B x a R b)
    (htraj : trajectoryOfVertex G A x a (a :: w)) : b ∉ w := by
  classical
  obtain ⟨i, hi, lastIndex, hlastIndex, habirth, hanti, hidx⟩ :=
    trajectoryOfVertex_data hS hx hopt.1.2.2.1 htraj
  intro hbw
  obtain ⟨k, hk, hki, hxkb⟩ := hidx b hbw
  have hbanti : VertexAnticomplete G x[k] A := by
    simpa [hxkb] using (show VertexAnticomplete G b A from
      fun z hz => hb.2.2 z (Or.inl hz))
  obtain ⟨r, Q, hQ, y, hy, hry⟩ := hx.2.2 k hk hbanti
  have hyx : y ∈ x := List.mem_of_mem_take hy
  have hrnc : ¬ VertexComplete G r {z : V | z ∈ x} := by
    intro hrc
    exact hry (hrc y hyx)
  obtain ⟨j, hj, hrbirth⟩ := exists_birth hQ.2.2.1 hrnc
  obtain ⟨ell, hell, helly⟩ := List.mem_iff_getElem.mp hy
  have hellk : ell < k := by
    have := hell
    simp only [List.length_take] at this
    omega
  have hyget : (x.take k)[ell]'hell = x[ell]'(by omega) := by simp
  have hjle : j ≤ ell := by
    by_contra hn
    have hellj : ell < j := by omega
    obtain ⟨-, -, j', hj', hj'eq, -, hjbefore⟩ := hrbirth
    have hj'j : j' = j := (List.Nodup.getElem_inj_iff hx.1.1).mp hj'eq
    subst j'
    have hadj := hjbefore ell hellj
    apply hry
    rw [← helly, hyget]
    exact hadj
  have hji : j < i := lt_of_le_of_lt hjle (lt_of_lt_of_le hellk hki)
  have hQb : IsBanister G A C B r Q b := by simpa [hxkb] using hQ
  apply hopt.2.2
  refine ⟨r, Q, hQb, hrnc, x[j], x[i], hrbirth, habirth, ?_⟩
  exact ⟨j, i, hj, hi, rfl, rfl, hji⟩

/-- If the right end first misses a trajectory vertex before the terminal
vertex, the required even prefix antipath exists. -/
theorem early_miss_gives_second_outcome
    {G : SimpleGraph V} (hG : Berge G)
    {A C B : Set V} (hS : StepConnected G A C B)
    {a b : V} (ha : IsLeftStar G A C B a)
    (hb : IsRightStar G A C B b) (hab : G.Adj a b)
    {w : List V} {last : V}
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (k : ℕ) (hk : k < w.length)
    (hbmiss : ¬ G.Adj b w[k])
    (hbprev : ∀ (j : ℕ) (hj : j < k), G.Adj b (w[j]'(by omega)))
    (hkearly : k + 1 < w.length) :
    Even (k + 1) ∧ IsAntipathList G (a :: (w.take (k + 1) ++ [b])) := by
  classical
  let Q : List V := a :: (w.take (k + 1) ++ [b])
  let L : List V := a :: w.take (k + 1)
  have htake : (a :: w).take (k + 2) = L := by simp [L]
  have hpref₀ := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hanti.1
    (i := 0) (j := k + 1) (by omega) (by simp; omega)
  have hpref : IsAntipathFrom G L a w[k] := by
    rw [show ((a :: w).drop 0).take (k + 1 - 0 + 1) = L by simpa [L]] at hpref₀
    simpa using hpref₀
  have hb_ne_wk : b ≠ w[k] := fun he => hbnotw (he ▸ List.getElem_mem hk)
  have hbc : Gᶜ.Adj b w[k] := (G.compl_adj b w[k]).2 ⟨hb_ne_wk, hbmiss⟩
  have hbnotL : b ∉ L := by
    intro hmem
    rcases List.mem_cons.mp hmem with hba | hwt
    · exact hab.ne' hba
    · exact hbnotw (List.mem_of_mem_take hwt)
  have hbother : ∀ z ∈ L, z ≠ w[k] → ¬ Gᶜ.Adj b z := by
    intro z hz hzne hcomp
    apply hcomp.2
    rcases List.mem_cons.mp hz with hza | hzt
    · subst z; exact hab.symm
    · obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hzt
      have hjlt : j < k + 1 := by
        have := hj
        simp only [List.length_take] at this
        omega
      have hjw : j < w.length := by omega
      have hget : (w.take (k + 1))[j]'hj = w[j]'hjw := by simp
      have hjne : j ≠ k := by
        intro he
        subst j
        apply hzne
        exact hjz.symm.trans hget
      have : G.Adj b w[j] := hbprev j (by omega)
      simpa [← hjz, hget] using this
  have hQfrom : IsAntipathFrom G Q a b := by
    simpa [Q, L] using
      (Workspace.ProofLemmas.PathAttach.isPathFrom_concat hpref hbc hbnotL hbother)

  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, -⟩ :=
    hS.2.2.2.1 (Classical.choose hS.2.1.1)
      (Or.inl (Or.inl (Classical.choose_spec hS.2.1.1)))
  have ha₁A := hs.1.2.1
  have hb₂B := hs.2.1.2.2.1
  have ha₁R := Workspace.ProofLemmas.PathBasics.head_mem hs.1.1.2.1
  have hb₂R := Workspace.ProofLemmas.PathBasics.getLast_mem hs.2.1.1.2.2
  have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
    intro hadj
    rcases (hs.2.2.2 a₁ ha₁R b₂ hb₂R).1 hadj with h | h
    · exact Set.disjoint_left.mp hS.1.1 hs.2.1.2.1 (h.2 ▸ hb₂B)
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hs.1.2.2.1)
  let S : List V := [b, a₁, b₂, a]
  have hSfrom : IsAntipathFrom G S b a := by
    have hmid : IsPathFrom Gᶜ [a₁, b₂] a₁ b₂ := by
      refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair ?_, rfl, by simp⟩
      exact (G.compl_adj a₁ b₂).2
        ⟨fun he => Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₂B), ha₁b₂⟩
    simpa [S] using (Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hmid
      ((G.compl_adj b a₁).2
        ⟨fun he => hb.1 (he ▸ Or.inl (Or.inl ha₁A)), hb.2.2 a₁ (Or.inl ha₁A)⟩)
      ((G.compl_adj a b₂).2
        ⟨fun he => ha.1 (he ▸ Or.inl (Or.inr hb₂B)), ha.2.2 b₂ (Or.inl hb₂B)⟩)
      (fun h => h.2 hab.symm) hab.ne'
      (by intro h; simp at h; rcases h with h | h; exact hb.1 (h ▸ Or.inl (Or.inl ha₁A));
          exact hb.1 (h ▸ Or.inl (Or.inr hb₂B)))
      (by intro h; simp at h; rcases h with h | h; exact ha.1 (h ▸ Or.inl (Or.inl ha₁A));
          exact ha.1 (h ▸ Or.inl (Or.inr hb₂B)))
      (by
        intro z hz hza hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · exact hza hz
        · subst z; exact hc.2 (hb.2.1 b₂ hb₂B))
      (by
        intro z hz hzb hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · subst z; exact hc.2 (ha.2.1 a₁ ha₁A)
        · exact hzb hz))
  let X : Set V := {z : V | z ∈ w.take (k + 1)}
  let Y : Set V := {a₁, b₂}
  have hXY : Disjoint X Y := Set.disjoint_left.mpr fun z hzX hzY => by
    have hzw : z ∈ w := List.mem_of_mem_take hzX
    have hzout := bComplete_not_mem_strip hS (hwB z hzw)
    simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hzY
    rcases hzY with rfl | rfl
    · exact hzout (Or.inl (Or.inl ha₁A))
    · exact hzout (Or.inl (Or.inr hb₂B))
  have hXYcomp : Complete G X Y := by
    intro z hzX y hyY
    have hzw : z ∈ w := List.mem_of_mem_take hzX
    have hzneLast : z ≠ last := by
      obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hzX
      have hjlt : j < k + 1 := by
        simp only [List.length_take] at hj
        omega
      intro he
      have hlastW : w.getLast? = some last := by
        have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
        have hh := hanti.2.2
        rw [List.getLast?_cons_of_ne_nil hwne] at hh
        exact hh
      have hlastElem : w[w.length - 1]'(by omega) = last :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW (by omega)
      have hget : (w.take (k + 1))[j]'hj = w[j]'(by omega) := by simp
      have heq : w[j]'(by omega) = w[w.length - 1]'(by omega) :=
        hget.symm.trans (hjz.trans (he.trans hlastElem.symm))
      have := (List.Nodup.getElem_inj_iff hanti.1.2.1.tail).1 heq
      omega
    simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hyY
    rcases hyY with hya | hyb
    · subst y; exact hbeforeA z hzw hzneLast a₁ ha₁A
    · subst y; exact hwB z hzw b₂ hb₂B
  have haX : a ∉ X := fun h =>
    (List.nodup_cons.mp hanti.1.2.1).1 (List.mem_of_mem_take h)
  have hbX : b ∉ X := fun h => hbnotw (List.mem_of_mem_take h)
  have haY : a ∉ Y := by
    intro h; simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact ha.1 (h ▸ Or.inl (Or.inl ha₁A))
    · exact ha.1 (h ▸ Or.inl (Or.inr hb₂B))
  have hbY : b ∉ Y := by
    intro h; simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact hb.1 (h ▸ Or.inl (Or.inl ha₁A))
    · exact hb.1 (h ▸ Or.inl (Or.inr hb₂B))
  have hQint : ∀ z ∈ interior Q, z ∈ X := by
    intro z hz
    have hmem := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQfrom).1 hz
    simpa [Q, X, hmem.2.1, hmem.2.2] using hmem.1
  have hSint : ∀ z ∈ interior S, z ∈ Y := by
    intro z hz
    simp [S, Y, Workspace.Types.Core.SPGT.interior] at hz ⊢
    exact hz
  have hSintRev : ∀ z ∈ interior S.reverse, z ∈ Y := by
    intro z hz
    simp [S, Y, Workspace.Types.Core.SPGT.interior] at hz ⊢
    tauto
  have hYXcomp : Complete G Y X := by
    intro y hy x hx
    exact (hXYcomp x hx y hy).symm
  have hsum := Workspace.ProofLemmas.AntiholeCompletion.even_add_pathLength_of_two_antipaths
    (X := Y) (Y := X) hG hXY.symm hYXcomp hab haY hbY haX hbX hQfrom hQint
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hSfrom) hSintRev
  have hQlen : pathLength Q = k + 2 := by
    simp only [Q, pathLength, List.length_cons, List.length_append, List.length_singleton]
    simp [List.length_take]
    omega
  have hSlen : pathLength S = 3 := by simp [S, pathLength]
  obtain ⟨t, ht⟩ := hsum
  constructor
  · refine ⟨t - 2, ?_⟩
    rw [hQlen] at ht
    simp [S, pathLength] at ht
    omega
  · exact hQfrom.1

/-- If the terminal trajectory vertex has both a neighbour and a non-neighbour
in `A`, the terminal-only missing pattern at the right end produces two
antipaths of opposite total parity. -/
theorem terminal_miss_neighbor_absurd
    {G : SimpleGraph V} (hG : Berge G)
    {A C B : Set V} (hS : StepConnected G A C B)
    {a b last : V} (ha : IsLeftStar G A C B a)
    (hb : IsRightStar G A C B b) (hab : G.Adj a b)
    {w : List V} (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hbBefore : ∀ z ∈ w, z ≠ last → G.Adj b z)
    (hbmiss : ¬ G.Adj b last)
    {c d : V} (hcA : c ∈ A) (hclast : G.Adj last c)
    (hdA : d ∈ A) (hdlast : ¬ G.Adj last d) : False := by
  classical
  let X : Set V := {z : V | z ∈ A ∧ G.Adj last z}
  let Y : Set V := {z : V | z ∈ A ∧ ¬ G.Adj last z}
  have hXYunion : X ∪ Y = A := by
    ext z
    simp only [X, Y, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hXYdis : Disjoint X Y := Set.disjoint_left.mpr fun z hzX hzY => hzY.2 hzX.2
  have hXne : X.Nonempty := ⟨c, hcA, hclast⟩
  have hYne : Y.Nonempty := ⟨d, hdA, hdlast⟩
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
  have ha₁A : a₁ ∈ A := ha₁X.1
  have hb₂B : b₂ ∈ B := hs.2.1.2.2.1
  have hlasta₁ : G.Adj last a₁ := ha₁X.2
  have ha₁R := Workspace.ProofLemmas.PathBasics.head_mem hs.1.1.2.1
  have hb₂R := Workspace.ProofLemmas.PathBasics.getLast_mem hs.2.1.1.2.2
  have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
    intro hadj
    rcases (hs.2.2.2 a₁ ha₁R b₂ hb₂R).1 hadj with h | h
    · exact Set.disjoint_left.mp hS.1.1 hs.2.1.2.1 (h.2 ▸ hb₂B)
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hs.1.2.2.1)

  let Q : List V := (a :: w) ++ [b]
  have hblastC : Gᶜ.Adj b last := (G.compl_adj b last).2
    ⟨fun he => hbnotw (he ▸ Workspace.ProofLemmas.PathBasics.getLast_mem (by
      have hwne : w ≠ [] := List.ne_nil_of_length_pos (by
        obtain ⟨k, hk⟩ := hodd
        omega)
      simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2)), hbmiss⟩
  have hbnot : b ∉ a :: w := by
    intro hm
    rcases List.mem_cons.mp hm with hba | hbw
    · exact hab.ne' hba
    · exact hbnotw hbw
  have hbother : ∀ z ∈ a :: w, z ≠ last → ¬ Gᶜ.Adj b z := by
    intro z hz hzlast hadj
    apply (G.compl_adj b z).mp hadj |>.2
    rcases List.mem_cons.mp hz with hza | hzw
    · subst z; exact hab.symm
    · exact hbBefore z hzw hzlast
  have hQfrom : IsAntipathFrom G Q a b := by
    simpa [Q] using Workspace.ProofLemmas.PathAttach.isPathFrom_concat
      hanti hblastC hbnot hbother

  let S : List V := [b, a₁, b₂, a]
  have hSfrom : IsAntipathFrom G S b a := by
    have hmid : IsPathFrom Gᶜ [a₁, b₂] a₁ b₂ := by
      refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair ?_, rfl, by simp⟩
      exact (G.compl_adj a₁ b₂).2
        ⟨fun he => Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₂B), ha₁b₂⟩
    simpa [S] using (Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hmid
      ((G.compl_adj b a₁).2
        ⟨fun he => hb.1 (he ▸ Or.inl (Or.inl ha₁A)),
          hb.2.2 a₁ (Or.inl ha₁A)⟩)
      ((G.compl_adj a b₂).2
        ⟨fun he => ha.1 (he ▸ Or.inl (Or.inr hb₂B)),
          ha.2.2 b₂ (Or.inl hb₂B)⟩)
      (fun h => h.2 hab.symm) hab.ne'
      (by intro h; simp at h; rcases h with h | h
          · exact hb.1 (h ▸ Or.inl (Or.inl ha₁A))
          · exact hb.1 (h ▸ Or.inl (Or.inr hb₂B)))
      (by intro h; simp at h; rcases h with h | h
          · exact ha.1 (h ▸ Or.inl (Or.inl ha₁A))
          · exact ha.1 (h ▸ Or.inl (Or.inr hb₂B)))
      (by
        intro z hz hza hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · exact hza hz
        · subst z; exact hc.2 (hb.2.1 b₂ hb₂B))
      (by
        intro z hz hzb hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · subst z; exact hc.2 (ha.2.1 a₁ ha₁A)
        · exact hzb hz))

  let W : Set V := {z : V | z ∈ w}
  let Z : Set V := {a₁, b₂}
  have hWZ : Disjoint W Z := Set.disjoint_left.mpr fun z hzW hzZ => by
    have hzout := bComplete_not_mem_strip hS (hwB z hzW)
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hzZ
    rcases hzZ with rfl | rfl
    · exact hzout (Or.inl (Or.inl ha₁A))
    · exact hzout (Or.inl (Or.inr hb₂B))
  have hWZcomp : Complete G W Z := by
    intro z hzw u hu
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hua₁ | hub₂
    · subst u
      by_cases hzl : z = last
      · simpa [hzl] using hlasta₁
      · exact hbeforeA z hzw hzl a₁ ha₁A
    · subst u
      exact hwB z hzw b₂ hb₂B
  have haW : a ∉ W := fun h => (List.nodup_cons.mp hanti.1.2.1).1 h
  have hbW : b ∉ W := hbnotw
  have haZ : a ∉ Z := by
    intro h
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact ha.1 (h ▸ Or.inl (Or.inl ha₁A))
    · exact ha.1 (h ▸ Or.inl (Or.inr hb₂B))
  have hbZ : b ∉ Z := by
    intro h
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact hb.1 (h ▸ Or.inl (Or.inl ha₁A))
    · exact hb.1 (h ▸ Or.inl (Or.inr hb₂B))
  have hQint : ∀ z ∈ interior Q, z ∈ W := by
    intro z hz
    simp [Q, W, Workspace.Types.Core.SPGT.interior] at hz ⊢
    exact hz
  have hSintRev : ∀ z ∈ interior S.reverse, z ∈ Z := by
    intro z hz
    simp [S, Z, Workspace.Types.Core.SPGT.interior] at hz ⊢
    tauto
  have hZWcomp : Complete G Z W := by
    intro z hz u hu
    exact (hWZcomp u hu z hz).symm
  have hsum := Workspace.ProofLemmas.AntiholeCompletion.even_add_pathLength_of_two_antipaths
    (X := Z) (Y := W) hG hWZ.symm hZWcomp hab haZ hbZ haW hbW hQfrom hQint
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hSfrom) hSintRev
  obtain ⟨ke, hke⟩ := hsum
  obtain ⟨ko, hko⟩ := hodd
  simp [Q, S, pathLength] at hke
  omega

end Workspace.ProofLemmas.Thm131EdgeCases
