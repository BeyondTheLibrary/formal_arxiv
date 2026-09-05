import Workspace.ProofLemmas.Thm132Infrastructure

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Trajectories used in the proof of 13.1

The definition in Section 13 records the recursive predecessor conditions and
the paper immediately observes that they determine a unique antipath.  This
module proves that observation.  It is kept independent of statement 13.1 so
that the induction in that statement can use it.
-/

namespace Workspace.ProofLemmas.Thm131Trajectory

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The conclusion of statement 13.1, named so its strong-induction step can
be passed to helper lemmas without restating the full ambient theorem. -/
def TrajectoryConclusion (G : SimpleGraph V) (a : V) (R : List V) (b : V)
    (w : List V) : Prop :=
  Odd w.length ∧
    ((∀ r ∈ R, (VertexComplete G r {u : V | u ∈ w} ↔ r = b)) ∨
      (pathLength R = 1 ∧
        ∃ m : ℕ, Even m ∧ 1 ≤ m ∧ m < w.length ∧
          IsAntipathList G (a :: (w.take m ++ [b]))))

/-- Every vertex of a rung belongs to the underlying strip. -/
theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  exact Or.inr (hR.2.2.2.2.2 z
    ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
      ⟨hz, hza, hzb⟩))

/-- The earliest earlier non-neighbour of a term of a right-sequence is
unique. -/
theorem predecessor_unique {G : SimpleGraph V} {x : List V} {u p q : V}
    (hx : x.Nodup) (hp : Predecessor G x u p) (hq : Predecessor G x u q) :
    p = q := by
  obtain ⟨i, hi, hiu, h, hh, hhp, hn, hmin⟩ := hp
  obtain ⟨i', hi', hiu', h', hh', h'hq, hn', hmin'⟩ := hq
  have hii : i = i' := by
    apply (List.Nodup.getElem_inj_iff hx).mp
    exact hiu.trans hiu'.symm
  subst i'
  have hhh : h = h' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hn (hmin' h hlt)
    · exact hn' (hmin h' hgt)
  subst h'
  exact hhp.symm.trans h'hq

/-- Removing the first term of a nontrivial trajectory leaves the trajectory
of its predecessor. -/
theorem trajectoryOfIndex_tail
    {G : SimpleGraph V} {A : Set V} {x : List V} {i : ℕ} {w : List V}
    (hx : x.Nodup) (hi : i < x.length) (hw : trajectoryOfIndex G A x i w)
    (hlen : 2 ≤ w.length) :
    ∃ (h : ℕ) (hh : h < x.length), h < i ∧
      Predecessor G x x[i] x[h] ∧ trajectoryOfIndex G A x h w.tail := by
  have hpos : 0 < w.length := by have := hw.1.1; omega
  have hstep := hw.2.2 0 (by omega)
  obtain ⟨ii, hii, hiiw, h, hh, hhp, hnon, hmin⟩ := hstep.2
  have hw0 : w[0]'hpos = x[i]'hi := by
    have hxi : x[i]? = some (x[i]'hi) := List.getElem?_eq_getElem hi
    have hhead := hw.1.2
    rw [hxi] at hhead
    exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hpos
  have hii_eq : ii = i := by
    apply (List.Nodup.getElem_inj_iff (by
      exact hx)).mp
    exact hiiw.trans hw0
  subst ii
  have hhx : h < x.length := lt_trans hh hi
  have hpred : Predecessor G x x[i] x[h] := by
    exact ⟨i, hi, rfl, h, hh, rfl, hnon, hmin⟩
  refine ⟨h, hhx, hh, hpred, ?_⟩
  have htailpos : 1 ≤ w.tail.length := by
    rw [List.length_tail]
    omega
  have hw1 : w[1]'(by omega) = x[h]'hhx := hhp.symm
  refine ⟨⟨htailpos, ?_⟩, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem hhx]
    simpa using hw1
  · obtain ⟨u, hu, a, ha, hna⟩ := hw.2.1
    refine ⟨u, ?_, a, ha, hna⟩
    cases w with
    | nil => simp at hlen
    | cons y ys =>
        cases ys with
        | nil => simp at hlen
        | cons z zs => simpa using hu
  · intro j hj
    have hj' : (j + 1) + 1 < w.length := by
      rw [List.length_tail] at hj
      omega
    simpa [List.getElem_tail] using hw.2.2 (j + 1) hj'

/-- A trajectory ending immediately at a term which is not `A`-complete has
one vertex. -/
theorem trajectoryOfIndex_length_one_of_not_complete
    {G : SimpleGraph V} {A : Set V} {x : List V} {i : ℕ} {w : List V}
    (hi : i < x.length) (hw : trajectoryOfIndex G A x i w)
    (hn : ¬ VertexComplete G x[i] A) : w.length = 1 := by
  have hpos : 0 < w.length := by have := hw.1.1; omega
  by_contra hne
  have htwo : 2 ≤ w.length := by omega
  have hc := (hw.2.2 0 (by omega)).1
  have hw0 : w[0]'hpos = x[i]'hi := by
    have hhead := hw.1.2
    rw [List.getElem?_eq_getElem hi] at hhead
    exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hpos
  exact hn (by simpa [hw0] using hc)

/-- The recursive conditions in `trajectoryOfIndex` determine its list
uniquely. -/
theorem trajectoryOfIndex_unique
    {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) :
    ∀ (i : ℕ) (hi : i < x.length) (p q : List V),
      trajectoryOfIndex G A x i p → trajectoryOfIndex G A x i q → p = q := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
      intro hi p q hp hq
      by_cases hc : VertexComplete G x[i] A
      · have hp2 : 2 ≤ p.length := by
          by_contra hn
          have hp1 : p.length = 1 := by have := hp.1.1; omega
          obtain ⟨u, hu, a, ha, hna⟩ := hp.2.1
          have hphead : p[0]'(by omega) = x[i]'hi := by
            have hh := hp.1.2
            rw [List.getElem?_eq_getElem hi] at hh
            exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hh (by omega)
          have hplast : p[0]'(by omega) = u := by
            have := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hu (by omega)
            simpa [hp1] using this
          exact hna (by rw [← hplast, hphead]; exact hc a ha)
        have hq2 : 2 ≤ q.length := by
          by_contra hn
          have hq1 : q.length = 1 := by have := hq.1.1; omega
          obtain ⟨u, hu, a, ha, hna⟩ := hq.2.1
          have hqhead : q[0]'(by omega) = x[i]'hi := by
            have hh := hq.1.2
            rw [List.getElem?_eq_getElem hi] at hh
            exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hh (by omega)
          have hqlast : q[0]'(by omega) = u := by
            have := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hu (by omega)
            simpa [hq1] using this
          exact hna (by rw [← hqlast, hqhead]; exact hc a ha)
        obtain ⟨j, hj, hji, hpj, hpt⟩ := trajectoryOfIndex_tail hx.1.1 hi hp hp2
        obtain ⟨k, hk, hki, hqk, hqt⟩ := trajectoryOfIndex_tail hx.1.1 hi hq hq2
        have hxjk : x[j] = x[k] := predecessor_unique hx.1.1 hpj hqk
        have hjk : j = k := (List.Nodup.getElem_inj_iff hx.1.1).mp hxjk
        subst k
        have htails : p.tail = q.tail := IH j hji hj p.tail q.tail hpt hqt
        have hphead : p.head? = some x[i] := by
          simpa [List.getElem?_eq_getElem hi] using hp.1.2
        have hqhead : q.head? = some x[i] := by
          simpa [List.getElem?_eq_getElem hi] using hq.1.2
        cases p with
        | nil => simp at hphead
        | cons pu pt =>
            cases q with
            | nil => simp at hqhead
            | cons qu qt =>
                simp only [List.head?_cons, Option.some.injEq] at hphead hqhead
                simp only [List.tail_cons] at htails
                subst pu
                subst qu
                simp [htails]
      · have hp1 := trajectoryOfIndex_length_one_of_not_complete hi hp hc
        have hq1 := trajectoryOfIndex_length_one_of_not_complete hi hq hc
        obtain ⟨pu, rfl⟩ := List.length_eq_one_iff.mp hp1
        obtain ⟨qu, rfl⟩ := List.length_eq_one_iff.mp hq1
        simpa [List.getElem?_eq_getElem hi] using hp.1.2.trans hq.1.2.symm

/-- The trajectory of a general vertex is unique as well: its first term is
the earliest non-neighbour, and the remaining predecessor trajectory is
unique by `trajectoryOfIndex_unique`. -/
theorem trajectoryOfVertex_unique
    {G : SimpleGraph V} {A C B : Set V} {x : List V} {a : V} {p q : List V}
    (hx : IsRightSequence G A C B x)
    (hp : trajectoryOfVertex G A x a p)
    (hq : trajectoryOfVertex G A x a q) : p = q := by
  obtain ⟨-, i, hi, wi, hfirsti, hwi, rfl⟩ := hp
  obtain ⟨-, j, hj, wj, hfirstj, hwj, rfl⟩ := hq
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hfirsti.1 (hfirstj.2 i hlt)
    · exact hfirstj.1 (hfirsti.2 j hgt)
  subst j
  have hww : wi = wj := trajectoryOfIndex_unique hx i hi wi wj hwi hwj
  simp [hww]

/-- Any list satisfying `trajectoryOfVertex` is the canonical antipath, and
all of its terms occur no later than the birth of the left-star. -/
theorem trajectoryOfVertex_data
    {G : SimpleGraph V} {A C B : Set V} {x : List V} {a : V} {w : List V}
    (hS : StepConnected G A C B) (hx : IsRightSequence G A C B x)
    (ha : IsLeftStar G A C B a)
    (htraj : trajectoryOfVertex G A x a (a :: w)) :
    ∃ (i : ℕ) (hi : i < x.length) (j : ℕ) (hj : j < x.length),
      birth G A C B x a x[i] ∧
      IsAntipathFrom G (a :: w) a x[j] ∧
      (∀ z ∈ w, ∃ (k : ℕ) (hk : k < x.length), k ≤ i ∧ x[k] = z) := by
  obtain ⟨wc, i, hi, j, hj, hcanonical, hbirth, hanti, hidx⟩ :=
    exists_trajectoryOfVertex_of_leftStar hS hx ha htraj.1.2.2
  have heq : a :: w = a :: wc := trajectoryOfVertex_unique hx htraj hcanonical
  have hww : w = wc := (List.cons.inj heq).2
  subst wc
  exact ⟨i, hi, j, hj, hbirth, hanti, hidx⟩

/-- Every vertex of the left class of a step-connected strip has a
non-neighbour in its right class.  Take the opposite rung in a step containing
the given vertex. -/
theorem exists_right_nonneighbor
    {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {a : V} (ha : a ∈ A) :
    ∃ b ∈ B, ¬ G.Adj a b := by
  obtain ⟨⟨hdAB, -, -⟩, -, -, hinstep, -⟩ := hS
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ :=
    hinstep a (Or.inl (Or.inl ha))
  obtain ⟨hr₁, hr₂, -, hcross⟩ := hstep
  have hne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := by
    intro x hx y hy hxy
    exact Set.disjoint_left.mp hdAB hx (hxy ▸ hy)
  rcases hmem with hmem | hmem
  · refine ⟨b₂, hr₂.2.2.1, ?_⟩
    intro hadj
    rcases (hcross a hmem b₂
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2).mp hadj with
      ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hne a₂ hr₂.2.1 b₂ hr₂.2.2.1 h2.symm
    · exact hne a ha b₁ hr₁.2.2.1 h1
  · refine ⟨b₁, hr₁.2.2.1, ?_⟩
    intro hadj
    rcases (hcross b₁
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).2 a hmem).mp hadj.symm with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne a₁ hr₁.2.1 b₁ hr₁.2.2.1 h1.symm
    · exact hne a ha b₂ hr₂.2.2.1 h2

/-- A prescribed vertex of `A` can be used as the left end of the first rung
of a step (renaming the two rungs if necessary). -/
theorem exists_step_with_left_end
    {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {a : V} (ha : a ∈ A) :
    ∃ (R₁ : List V) (b₁ a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a R₁ b₁ a₂ R₂ b₂ := by
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hm⟩ :=
    hS.2.2.2.1 a (Or.inl (Or.inl ha))
  rcases hm with hm | hm
  · have haa₁ : a = a₁ := hs.1.2.2.2.1 a hm ha
    subst a₁
    exact ⟨R₁, b₁, a₂, R₂, b₂, hs⟩
  · have haa₂ : a = a₂ := hs.2.1.2.2.2.1 a hm ha
    subst a₂
    refine ⟨R₂, b₂, a₁, R₁, b₁, hs.2.1, hs.1, ?_, ?_⟩
    · intro z hzR₂ hzR₁
      exact hs.2.2.1 z hzR₁ hzR₂
    · intro z hzR₂ y hyR₁
      rw [G.adj_comm, hs.2.2.2 y hyR₁ z hzR₂]
      tauto

/-- The last vertex displayed by an antipath trajectory is the terminal term
of `trajectoryOfIndex`, hence has a non-neighbour in `A`. -/
theorem trajectory_last_misses_left
    {G : SimpleGraph V} {A : Set V} {x : List V} {a last : V} {w : List V}
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hanti : IsAntipathFrom G (a :: w) a last) :
    ∃ a₁ ∈ A, ¬ G.Adj last a₁ := by
  rcases htraj with ⟨happ, ti, hti, wt, hfirst, hwt, hshape⟩
  have hwtw : wt = w := (List.cons.inj hshape).2.symm
  have hwt' := hwt
  rw [hwtw] at hwt'
  have hwpos : 0 < w.length := by have := hwt'.1.1; omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  have hlast : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  obtain ⟨u, hu, a₁, ha₁, hnon⟩ := hwt'.2.1
  have hulast : u = last := by rw [hu] at hlast; exact Option.some.inj hlast
  exact ⟨a₁, ha₁, by simpa [hulast] using hnon⟩

/-- Every nonterminal tail vertex of a trajectory is complete to the left
class. -/
theorem trajectory_before_last_left_complete
    {G : SimpleGraph V} {A : Set V} {x : List V} {a last : V} {w : List V}
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hanti : IsAntipathFrom G (a :: w) a last) :
    ∀ z ∈ w, z ≠ last → VertexComplete G z A := by
  rcases htraj with ⟨happ, ti, hti, wt, hfirst, hwt₀, hshape⟩
  have hwtw : wt = w := (List.cons.inj hshape).2.symm
  have hwt : trajectoryOfIndex G A x ti w := by simpa [hwtw] using hwt₀
  have hwpos : 0 < w.length := by have := hwt.1.1; omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  intro z hz hzne
  obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
  have hklast : k ≠ w.length - 1 := by
    intro heq
    have hlastElem : w[w.length - 1]'(by omega) = last :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW hwpos
    subst k
    exact hzne (hkz.symm.trans hlastElem)
  have hkstep : k + 1 < w.length := by omega
  simpa [hkz] using (hwt.2.2 k hkstep).1

/-- Every tail vertex of a right-sequence trajectory is complete to the right
class of the strip. -/
theorem trajectory_tail_right_complete
    {G : SimpleGraph V} {A C B : Set V} (hS : StepConnected G A C B)
    {x : List V} (hx : IsRightSequence G A C B x)
    {a : V} (ha : IsLeftStar G A C B a)
    {last : V} {w : List V}
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hanti : IsAntipathFrom G (a :: w) a last) :
    ∀ z ∈ w, VertexComplete G z B := by
  obtain ⟨i, hi, j, hj, hbirth, hanti', hidx⟩ :=
    trajectoryOfVertex_data hS hx ha htraj
  intro z hz
  obtain ⟨k, hk, -, hkz⟩ := hidx z hz
  simpa [hkz] using hx.1.2 x[k] (List.getElem_mem hk)

/-- Claim (1) of the printed proof of 13.1: a left-star trajectory has odd
tail length.  The cycle `b₁-a-w₁-⋯-wₙ-a₂-b₁` is an antihole. -/
theorem trajectory_tail_odd
    {G : SimpleGraph V} (hG : Berge G)
    {A C B : Set V} (hS : StepConnected G A C B)
    {x : List V} (hx : IsRightSequence G A C B x)
    {a : V} (ha : IsLeftStar G A C B a)
    {w : List V} (htraj : trajectoryOfVertex G A x a (a :: w)) :
    Odd w.length := by
  classical
  obtain ⟨i, hi, j, hj, -, hanti, hidx⟩ :=
    trajectoryOfVertex_data hS hx ha htraj
  let last : V := x[j]
  have hanti' : IsAntipathFrom G (a :: w) a last := by simpa [last] using hanti
  have hwpos : 0 < w.length := by
    obtain ⟨_, _, _, wt, _, hindexTraj, hshape⟩ := htraj
    have hwtw : wt = w := (List.cons.inj hshape).2.symm
    have hlen : 1 ≤ wt.length := hindexTraj.1.1
    rw [hwtw] at hlen
    have := hlen
    omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti'.2.2
  obtain ⟨-, ti, hti, wt, -, hwt, hshape⟩ := htraj
  have hwtw : wt = w := (List.cons.inj hshape).2.symm
  subst wt
  obtain ⟨u, hu, a₂, ha₂A, hua₂⟩ := hwt.2.1
  have hulast : u = last := by
    rw [hu] at hlastW
    exact Option.some.inj hlastW
  have hlasta₂ : ¬ G.Adj last a₂ := by simpa [hulast] using hua₂
  have hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A := by
    intro z hz hzne
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
    have hklast : k ≠ w.length - 1 := by
      intro heq
      have hlastElem : w[w.length - 1]'(by omega) = last :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW hwpos
      subst k
      exact hzne (hkz.symm.trans hlastElem)
    have hkstep : k + 1 < w.length := by omega
    simpa [hkz] using (hwt.2.2 k hkstep).1
  have hwB : ∀ z ∈ w, VertexComplete G z B := by
    intro z hz
    obtain ⟨k, hk, -, hkz⟩ := hidx z hz
    simpa [hkz] using hx.1.2 x[k] (List.getElem_mem hk)
  obtain ⟨b₁, hb₁B, ha₂b₁⟩ := exists_right_nonneighbor hS ha₂A
  have ha₂_ne_b₁ : a₂ ≠ b₁ := by
    intro heq
    exact Set.disjoint_left.mp hS.1.1 ha₂A (heq ▸ hb₁B)
  have hR : IsPathFrom Gᶜ [a₂, b₁] a₂ b₁ := by
    refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair ?_, rfl, by simp⟩
    exact (G.compl_adj a₂ b₁).mpr ⟨ha₂_ne_b₁, ha₂b₁⟩
  have hQout : ∀ z ∈ a :: w, z ∉ A ∪ B ∪ C := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha.1
    · exact bComplete_not_mem_strip hS (hwB z hz)
  have hdisj : ∀ z ∈ a :: w, z ∉ [a₂, b₁] := by
    intro z hz hzr
    simp at hzr
    rcases hzr with hza₂ | hzb₁
    · exact hQout z hz (hza₂ ▸ Or.inl (Or.inl ha₂A))
    · exact hQout z hz (hzb₁ ▸ Or.inl (Or.inr hb₁B))
  have hcross : ∀ z ∈ a :: w, ∀ y ∈ [a₂, b₁],
      (Gᶜ.Adj z y ↔ (z = last ∧ y = a₂) ∨ (z = a ∧ y = b₁)) := by
    intro z hz y hy
    simp at hy
    rcases hy with hya₂ | hyb₁
    · subst y
      constructor
      · intro hza₂
        left
        refine ⟨?_, rfl⟩
        by_contra hzne
        have hzad : G.Adj z a₂ := by
          rcases List.mem_cons.mp hz with rfl | hzw
          · exact ha.2.1 a₂ ha₂A
          · exact hbeforeA z hzw hzne a₂ ha₂A
        exact hza₂.2 hzad
      · rintro (⟨hzlast, -⟩ | ⟨hza, hbad⟩)
        · subst z
          exact (G.compl_adj last a₂).mpr
            ⟨fun heq => hQout last
                (List.mem_cons.mpr
                  (Or.inr (Workspace.ProofLemmas.PathBasics.getLast_mem hlastW)))
                (heq ▸ Or.inl (Or.inl ha₂A)), hlasta₂⟩
        · exact absurd hbad ha₂_ne_b₁
    · subst y
      constructor
      · intro hzb₁
        right
        refine ⟨?_, rfl⟩
        rcases List.mem_cons.mp hz with hza | hzw
        · exact hza
        · exact absurd (hwB z hzw b₁ hb₁B) hzb₁.2
      · rintro (⟨hzl, hbad⟩ | ⟨hza, -⟩)
        · exact absurd hbad ha₂_ne_b₁.symm
        · subst z
          exact (G.compl_adj a b₁).mpr
            ⟨fun heq => ha.1 (heq ▸ Or.inl (Or.inr hb₁B)),
              ha.2.2 b₁ (Or.inl hb₁B)⟩
  have hhole : IsHoleList Gᶜ ((a :: w) ++ [a₂, b₁]) :=
    Workspace.ProofLemmas.PathGlue.glue_hole hanti' hR hdisj hcross (by simp; omega)
  have hev := hG.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons,
    List.length_nil] at hev
  rw [Nat.even_iff] at hev
  rw [Nat.odd_iff]
  omega

end Workspace.ProofLemmas.Thm131Trajectory
