import Workspace.ProofLemmas.Thm131Enlarge
import Workspace.ProofLemmas.Thm131LastCase
import Workspace.Statements.S03.Thm_3_2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# The closing paragraph of the printed proof of 13.1

PAPER (printed p. 81):

*"We may therefore assume that some vertex of `R \ b` is `W`-complete, for
otherwise the theorem holds by (7).  Let `a-P-p` be the subpath of `R \ b` such
that `p` is the unique `W`-complete vertex of `P`.  Choose `a₁ ∈ A` and
`b₁ ∈ B`, adjacent (this is possible by (5)).  Let us apply 3.2 to the path
`p-P-a-a₁-b₁`, and the even antipath `a-w₁-⋯-wₙ-a₁`.  Both ends of the path are
complete to the interior of the antipath, so by 3.2 it follows that `P` has
length 2, and if `q` denotes its middle vertex then `q` is nonadjacent to `wₙ`
and adjacent to `w₁, …, wₙ₋₁`.  But then `((B ∪ {p}, ∅, A ∪ {q}), a-w₁-⋯-wₙ)` is
a staircase in `G`, a contradiction.  This completes the proof of 13.1."*

The path `p-P-a-a₁-b₁` is used in the opposite order, as `b₁-a₁-a-P-p`; the
antipath is then read backwards as `a₁-wₙ-⋯-w₁-a`, so that 3.2 is applied with
`s = 2` and its first outcome (which needs `3 ≤ s`) is impossible.
-/

namespace Workspace.ProofLemmas.Thm131Closing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131Enlarge
open Workspace.ProofLemmas.Thm131LastCase
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closing paragraph: a `W`-complete vertex of `R \ b` is impossible. -/
theorem closing_absurd
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
    (hlast : IsRightStar G A C B last)
    (hgood : ∃ p ∈ R, p ≠ b ∧ VertexComplete G p {u : V | u ∈ w}) :
    False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hleft : IsLeftStar G A C B a := hR.2.2.1
  -- PAPER (5): *"`C = ∅`"*
  have hCempty : C = ∅ :=
    middle_empty_of_last_rightStar hG heven hK hleft hlast hanti hodd hwlong
      hbeforeA hwB
  subst hCempty
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hwnodup : w.Nodup := (List.nodup_cons.mp hanti.1.2.1).2
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  have hlastw : last ∈ w := Workspace.ProofLemmas.PathBasics.getLast_mem hlastW
  have hlastElem : w[w.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW (by omega)
  have hw3 : 3 ≤ w.length := by obtain ⟨k, hk⟩ := hodd; omega
  have hRpos : 0 < R.length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hR.1.1
  have hR0 : R[0]'hRpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR.1.2.1 hRpos
  have hRb : R[R.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.1.2.2 hRpos
  have hRnodup : R.Nodup := Workspace.ProofLemmas.PathBasics.path_nodup hR.1.1
  -- the first `W`-complete vertex along `R`
  have hex : ∃ k : ℕ, ∃ hk : k < R.length,
      VertexComplete G (R[k]'hk) {u : V | u ∈ w} := by
    obtain ⟨p₀, hp₀R, -, hp₀W⟩ := hgood
    obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp₀R
    exact ⟨k, hk, by rw [hkp]; exact hp₀W⟩
  obtain ⟨hmR, hmW⟩ := Nat.find_spec hex
  set m : ℕ := Nat.find hex with hmdef
  have hmmin : ∀ (k : ℕ) (hk : k < R.length), k < m →
      ¬ VertexComplete G (R[k]'hk) {u : V | u ∈ w} := by
    intro k hk hlt hc
    exact Nat.find_min hex hlt ⟨hk, hc⟩
  have haNotW : ¬ VertexComplete G a {u : V | u ∈ w} := by
    intro hc
    have hadj : Gᶜ.Adj a (w[0]'(by omega)) := by
      have hp := Workspace.ProofLemmas.PathBasics.path_adj_succ hanti.1 (i := 0)
        (by simp; omega)
      simpa using hp
    exact hadj.2 (hc _ (List.getElem_mem (by omega)))
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
    obtain ⟨p₀, hp₀R, hp₀b, hp₀W⟩ := hgood
    obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp₀R
    have hkne : k ≠ R.length - 1 := by
      intro he
      apply hp₀b
      rw [← hkp]
      exact (getElem_congr rfl he hk :
        R[k]'hk = R[R.length - 1]'(by omega)).trans hRb
    have hle : m ≤ k := Nat.find_le ⟨hk, by rw [hkp]; exact hp₀W⟩
    omega
  -- `a₁ ∈ A` and `b₁ ∈ B`, adjacent
  obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have hR₁ : IsRungOfStrip G A (∅ : Set V) B a₁ R₁ b₁ := hstep.1
  have ha₁b₁ : G.Adj a₁ b₁ := by
    have hint : SPGT.interior R₁ = [] := by
      rcases hh : SPGT.interior R₁ with _ | ⟨z, rest⟩
      · rfl
      · exact absurd (hR₁.2.2.2.2.2 z (by rw [hh]; simp)) (Set.notMem_empty z)
    have hlenI := Workspace.ProofLemmas.PathBasics.interior_length R₁
    rw [hint] at hlenI
    simp only [List.length_nil] at hlenI
    have hne : a₁ ≠ b₁ := fun he =>
      Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₁B)
    have h2 : 2 ≤ R₁.length := by
      by_contra hlt
      have h1 : R₁.length = 1 := by
        have := Workspace.ProofLemmas.PathBasics.path_length_pos hR₁.1.1
        omega
      have hhead : R₁[0]'(by omega) = a₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR₁.1.2.1 (by omega)
      have hlastR : R₁[R₁.length - 1]'(by omega) = b₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR₁.1.2.2 (by omega)
      apply hne
      rw [← hhead, ← hlastR]
      exact getElem_congr rfl (by omega) (by omega)
    have hpl : pathLength R₁ = 1 := by
      simp only [pathLength]
      omega
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hR₁.1 hpl
  have ha₁a : G.Adj a₁ a := (hleft.2.1 a₁ ha₁A).symm
  have ha₁last : ¬ G.Adj a₁ last := fun h => hlast.2.2 a₁ (Or.inl ha₁A) h.symm
  -- the path `b₁-a₁-a-P-p`
  have htakelen : (R.take (m + 1)).length = m + 1 := by
    simp only [List.length_take]
    omega
  have htakeget : ∀ (k : ℕ) (hk : k < (R.take (m + 1)).length),
      (R.take (m + 1))[k]'hk = R[k]'(by rw [htakelen] at hk; omega) := by
    intro k hk
    simp
  have htakeFrom : IsPathFrom G (R.take (m + 1)) a (R[m]'hmR) := by
    refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hR.1.1 (by omega),
      ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [htakeget 0 (by omega)]
      rw [hR0]
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [htakeget ((R.take (m + 1)).length - 1) (by omega)]
      exact congrArg some (getElem_congr rfl (by omega) (by omega))
  set Rt : List V := (R.take (m + 1)).tail with hRtdef
  have htakecons : R.take (m + 1) = a :: Rt := by
    obtain ⟨hd, tl, hc⟩ : ∃ hd tl, R.take (m + 1) = hd :: tl := by
      cases hc : R.take (m + 1) with
      | nil => exact absurd (hc ▸ htakeFrom.2.1) (by simp)
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    have hhd : hd = a := by
      have := htakeFrom.2.1
      rw [hc] at this
      simpa using this
    rw [hRtdef, hc, hhd]
    simp
  have hRtlen : Rt.length = m := by
    have := htakelen
    rw [htakecons] at this
    simpa using this
  have hRtget : ∀ (k : ℕ) (hk : k < Rt.length),
      Rt[k]'hk = R[k + 1]'(by rw [hRtlen] at hk; omega) := by
    intro k hk
    have hk' : k + 1 < (R.take (m + 1)).length := by
      rw [htakelen]; rw [hRtlen] at hk; omega
    have h1 : Rt[k]'hk = (R.take (m + 1))[k + 1]'hk' := by
      simp only [hRtdef]
      exact List.getElem_tail _
    rw [h1, htakeget (k + 1) hk']
  have hanotRt : a ∉ Rt := by
    intro hmem
    have hnd : (R.take (m + 1)).Nodup := List.Nodup.sublist (List.take_sublist _ _) hRnodup
    rw [htakecons] at hnd
    exact (List.nodup_cons.mp hnd).1 hmem
  have hRtsub : ∀ z ∈ Rt, z ∈ R ∧ z ≠ a := by
    intro z hz
    have hzt : z ∈ R.take (m + 1) := by
      rw [htakecons]; exact List.mem_cons_of_mem _ hz
    exact ⟨List.mem_of_mem_take hzt, fun he => hanotRt (he ▸ hz)⟩
  have hRtint : ∀ z ∈ Rt, z ∈ SPGT.interior R := by
    intro z hz
    obtain ⟨hzR, hza⟩ := hRtsub z hz
    have hzb : z ≠ b := by
      intro he
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
      rw [hRtget k hk] at hkz
      have hkR : k + 1 < R.length := by rw [hRtlen] at hk; omega
      have heq : R[k + 1]'hkR = R[R.length - 1]'(by omega) := by
        rw [hkz, he, hRb]
      have := (List.Nodup.getElem_inj_iff hRnodup).mp heq
      rw [hRtlen] at hk
      omega
    exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
      ⟨hzR, hza, hzb⟩
  -- the path list `L`
  have hcons1 : IsPathFrom G (a₁ :: (R.take (m + 1))) a₁ (R[m]'hmR) := by
    refine Workspace.ProofLemmas.PathAttach.isPathFrom_cons htakeFrom ha₁a ?_ ?_
    · intro hmem
      rw [htakecons] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hleft.1 (h ▸ Or.inl (Or.inl ha₁A))
      · exact hR.2.1 a₁ (hRtsub a₁ h).1 (Or.inl (Or.inl ha₁A))
    · intro z hz hza hadj
      rw [htakecons] at hz
      rcases List.mem_cons.mp hz with h | h
      · exact hza h
      · exact hR.2.2.2.2 z (hRtint z h) a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
  have hcons2 : IsPathFrom G (b₁ :: (a₁ :: (R.take (m + 1)))) b₁ (R[m]'hmR) := by
    refine Workspace.ProofLemmas.PathAttach.isPathFrom_cons hcons1 ha₁b₁.symm ?_ ?_
    · intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact Set.disjoint_left.mp hS.1.1 ha₁A (h ▸ hb₁B)
      · rw [htakecons] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hleft.1 (h1 ▸ Or.inl (Or.inr hb₁B))
        · exact hR.2.1 b₁ (hRtsub b₁ h1).1 (Or.inl (Or.inr hb₁B))
    · intro z hz hza hadj
      rcases List.mem_cons.mp hz with h | h
      · exact hza h
      · rw [htakecons] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hleft.2.2 b₁ (Or.inl hb₁B) (h1 ▸ hadj).symm
        · exact hR.2.2.2.2 z (hRtint z h1) b₁ (Or.inl (Or.inr hb₁B)) hadj.symm
  set L : List V := b₁ :: a₁ :: a :: Rt with hLdef
  have hLeq : b₁ :: (a₁ :: (R.take (m + 1))) = L := by
    rw [hLdef, htakecons]
  have hL : IsPathList G L := by rw [← hLeq]; exact hcons2.1
  have hLlen : L.length = m + 3 := by
    simp only [hLdef, List.length_cons, hRtlen]
  -- the antipath `a₁-wₙ-⋯-w₁-a`
  have hrev : IsAntipathFrom G (w.reverse ++ [a]) last a := by
    have := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hanti
    simpa using this
  have hQ0 : IsAntipathFrom G (a₁ :: (w.reverse ++ [a])) a₁ a := by
    refine Workspace.ProofLemmas.PathAttach.isPathFrom_cons hrev ?_ ?_ ?_
    · exact (G.compl_adj a₁ last).mpr
        ⟨fun he => hlast.1 (Or.inl (Or.inl (he ▸ ha₁A))), ha₁last⟩
    · intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact bComplete_not_mem_strip hS (hwB a₁ (by simpa using h))
          (Or.inl (Or.inl ha₁A))
      · exact hleft.1 ((by simpa using h : a₁ = a) ▸ Or.inl (Or.inl ha₁A))
    · intro z hz hzl hadj
      rcases List.mem_append.mp hz with h | h
      · have hzw : z ∈ w := by simpa using h
        exact hadj.2 (hbeforeA z hzw hzl a₁ ha₁A).symm
      · have hza : z = a := by simpa using h
        exact hadj.2 (hza ▸ ha₁a)
  -- 3.2 applied to `L` and `w.reverse`, with `s = 2`
  have hL1 : L[1]'(by omega) = a₁ := by simp [hLdef]
  have hL2 : L[2]'(by omega) = a := by simp [hLdef]
  have hL3 : ∀ (h : 3 < L.length), L[3]'h = R[1]'(by omega) := by
    intro h
    have hRt0 : (0 : ℕ) < Rt.length := by rw [hRtlen]; omega
    have h1 : L[3]'h = Rt[0]'hRt0 := by simp [hLdef]
    rw [h1, hRtget 0 hRt0]
  have hL4 : ∀ (h : 4 < L.length), L[4]'h = R[2]'(by omega) := by
    intro h
    have hRt1 : (1 : ℕ) < Rt.length := by rw [hRtlen]; rw [hLlen] at h; omega
    have h1 : L[4]'h = Rt[1]'hRt1 := by simp [hLdef]
    rw [h1, hRtget 1 hRt1]
  have hQ : IsAntipathFrom G ((L[2 - 1]'(by omega)) ::
      (w.reverse ++ [L[2]'(by omega)])) (L[2 - 1]'(by omega)) (L[2]'(by omega)) := by
    have h1 : L[2 - 1]'(by omega) = a₁ := hL1
    rw [h1, hL2]
    exact hQ0
  have hqleft : ∀ z ∈ w.reverse, ∃ y ∈ L.take (2 - 1), G.Adj z y := by
    intro z hz
    refine ⟨b₁, by simp [hLdef], ?_⟩
    exact hwB z (by simpa using hz) b₁ hb₁B
  have hqright : ∀ z ∈ w.reverse, ∃ y ∈ L.drop (2 + 1), G.Adj z y := by
    intro z hz
    have hdrop : L.drop 3 = Rt := by simp [hLdef]
    have hmRt : (R[m]'hmR) ∈ Rt := by
      have hk : m - 1 < Rt.length := by rw [hRtlen]; omega
      have := hRtget (m - 1) hk
      have heq : R[m - 1 + 1]'(by rw [hRtlen] at hk; omega) = R[m]'hmR :=
        getElem_congr rfl (by omega) (by omega)
      rw [heq] at this
      exact this ▸ List.getElem_mem hk
    refine ⟨R[m]'hmR, by rw [hdrop]; exact hmRt, ?_⟩
    exact (hmW z (by simpa using hz)).symm
  have hnrev : w.reverse.length = w.length := List.length_reverse
  rcases Workspace.Statements.S03.SPGT.thm_3_2 G hG L.length w.length 2 L w.reverse
      hL rfl (by omega) (by omega) hnrev (by omega) hodd hQ hqleft hqright with
    hleftout | hrightout
  · exact absurd hleftout.1 (by omega)
  obtain ⟨hs3, hpat⟩ := hrightout
  have hL5 : 5 ≤ L.length := by omega
  have hmemtake : ∀ (i : ℕ) (hi : i < L.length), i < 5 → (L[i]'hi) ∈ L.take 5 := by
    intro i hi h5
    have hlt : i < (L.take 5).length := by
      simp only [List.length_take]
      omega
    have heq : (L.take 5)[i]'hlt = L[i]'hi := by simp
    exact heq ▸ List.getElem_mem hlt
  have hwindow : (L.drop (2 - 2)).take 5 = L.take 5 := by simp
  have hpat' : ∀ x ∈ L.take 5, ∀ y ∈ w.reverse,
      (¬ G.Adj x y ↔
        (x = L[2 - 1]'(by omega) ∧ y = w.reverse[0]'(by rw [hnrev]; omega)) ∨
        (x = L[2]'(by omega) ∧
          y = w.reverse[w.length - 1]'(by rw [hnrev]; omega)) ∨
        (x = L[2 + 1]'(by omega) ∧
          y = w.reverse[0]'(by rw [hnrev]; omega))) := by
    intro x hx y hy
    rw [← hwindow] at hx
    exact hpat x hx y hy
  have hq0 : w.reverse[0]'(by rw [hnrev]; omega) = last := by
    rw [List.getElem_reverse]
    exact (getElem_congr rfl (by omega) (by omega)).trans hlastElem
  have hqn : w.reverse[w.length - 1]'(by rw [hnrev]; omega) = w[0]'(by omega) := by
    rw [List.getElem_reverse]
    exact getElem_congr rfl (by omega) (by omega)
  have hLne : ∀ z ∈ R, z ≠ a₁ ∧ z ≠ b₁ := by
    intro z hz
    exact ⟨fun he => hR.2.1 z hz (he ▸ Or.inl (Or.inl ha₁A)),
      fun he => hR.2.1 z hz (he ▸ Or.inl (Or.inr hb₁B))⟩
  -- PAPER: *"it follows that `P` has length 2"*
  have hm2 : m = 2 := by
    by_contra hne
    have hm3 : 3 ≤ m := by omega
    have hR2lt : 2 < R.length := by omega
    have hcomp : VertexComplete G (R[2]'hR2lt) {u : V | u ∈ w} := by
      intro y hy
      by_contra hadj
      have hyrev : y ∈ w.reverse := by simpa using hy
      have h4 : (4 : ℕ) < L.length := by omega
      have hx : (R[2]'hR2lt) ∈ L.take 5 := by
        have := hmemtake 4 h4 (by omega)
        rw [hL4 h4] at this
        exact this
      rcases (hpat' _ hx y hyrev).1 hadj with ⟨hx1, -⟩ | ⟨hx2, -⟩ | ⟨hx3, -⟩
      · rw [hL1] at hx1
        exact (hLne (R[2]'hR2lt) (List.getElem_mem hR2lt)).1 hx1
      · rw [hL2] at hx2
        have := (List.Nodup.getElem_inj_iff hRnodup).mp (hx2.trans hR0.symm)
        omega
      · rw [hL3 (by omega)] at hx3
        have := (List.Nodup.getElem_inj_iff hRnodup).mp hx3
        omega
    exact hmmin 2 hR2lt (by omega) hcomp
  -- the two vertices `p` and `q` of the printed proof
  have hp2 : (2 : ℕ) < R.length := by omega
  have hq1 : (1 : ℕ) < R.length := by omega
  have hpW0 : VertexComplete G (R[2]'hp2) {u : V | u ∈ w} := by
    rw [← (getElem_congr rfl hm2 hmR : R[m]'hmR = R[2]'hp2)]
    exact hmW
  set p : V := R[2]'hp2 with hpdef
  set q : V := R[1]'hq1 with hqdef
  have hpW : VertexComplete G p {u : V | u ∈ w} := hpW0
  have hpq : G.Adj q p := by
    have := Workspace.ProofLemmas.PathBasics.path_adj_succ hR.1.1 (i := 1) hp2
    exact this
  have hpint : p ∈ SPGT.interior R :=
    Workspace.ProofLemmas.PathBasics.getElem_mem_interior hR.1.1 hp2 (by omega)
      (by omega)
  have hqint : q ∈ SPGT.interior R :=
    Workspace.ProofLemmas.PathBasics.getElem_mem_interior hR.1.1 hq1 (by omega)
      (by omega)
  have hpOut : p ∉ A ∪ B ∪ (∅ : Set V) :=
    hR.2.1 p (Workspace.ProofLemmas.PathBasics.interior_subset hpint)
  have hqOut : q ∉ A ∪ B ∪ (∅ : Set V) :=
    hR.2.1 q (Workspace.ProofLemmas.PathBasics.interior_subset hqint)
  have hpAB : VertexAnticomplete G p (A ∪ B) := by
    intro z hz
    exact hR.2.2.2.2 p hpint z (Or.inl hz)
  have hqAB : VertexAnticomplete G q (A ∪ B) := by
    intro z hz
    exact hR.2.2.2.2 q hqint z (Or.inl hz)
  -- PAPER: *"`q` is nonadjacent to `wₙ` and adjacent to `w₁, …, wₙ₋₁`"*
  have hqmiss : ¬ G.Adj q last := by
    have h3 : (3 : ℕ) < L.length := by omega
    have hxmem : q ∈ L.take 5 := by
      have := hmemtake 3 h3 (by omega)
      rw [hL3 h3] at this
      exact this
    have hlastrev : last ∈ w.reverse := by simpa using hlastw
    refine (hpat' q hxmem last hlastrev).2 (Or.inr (Or.inr ⟨?_, ?_⟩))
    · rw [hL3 (by omega)]
    · rw [hq0]
  have hqbefore : ∀ z ∈ w, z ≠ last → G.Adj q z := by
    intro z hz hzl
    by_contra hadj
    have hzrev : z ∈ w.reverse := by simpa using hz
    have h3 : (3 : ℕ) < L.length := by omega
    have hxmem : q ∈ L.take 5 := by
      have := hmemtake 3 h3 (by omega)
      rw [hL3 h3] at this
      exact this
    rcases (hpat' q hxmem z hzrev).1 hadj with ⟨hx1, -⟩ | ⟨hx2, -⟩ | ⟨-, hy3⟩
    · rw [hL1] at hx1
      exact (hLne q (List.getElem_mem hq1)).1 hx1
    · rw [hL2] at hx2
      have := (List.Nodup.getElem_inj_iff hRnodup).mp (hx2.trans hR0.symm)
      omega
    · rw [hq0] at hy3
      exact hzl hy3
  -- the enlarged staircase in the complement
  have hRw : ∀ z ∈ R, z ∉ w := by
    intro z hz hzw
    obtain ⟨b', hb'B⟩ := hS.2.1.2
    by_cases hza : z = a
    · exact (List.nodup_cons.mp hanti.1.2.1).1 (hza ▸ hzw)
    by_cases hzb : z = b
    · exact hbnotw (hzb ▸ hzw)
    · exact hR.2.2.2.2 z
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
          ⟨hz, hza, hzb⟩) b' (Or.inl (Or.inr hb'B)) (hwB z hzw b' hb'B)
  have hpa : ¬ G.Adj p a := by
    intro hadj
    have h1 : G.Adj (R[0]'hRpos) (R[2]'hp2) := by rw [hR0]; exact hadj.symm
    have := (Workspace.ProofLemmas.PathBasics.path_adj_iff hR.1.1 hRpos hp2).1 h1
    omega
  have hpane : p ≠ a := by
    intro he
    have := (List.Nodup.getElem_inj_iff hRnodup).mp (he.trans hR0.symm)
    omega
  have hqane : q ≠ a := by
    intro he
    have := (List.Nodup.getElem_inj_iff hRnodup).mp (he.trans hR0.symm)
    omega
  have hqa : G.Adj q a := by
    have := Workspace.ProofLemmas.PathBasics.path_adj_succ hR.1.1 (i := 0) hq1
    rw [hR0] at this
    exact this.symm
  have hpT : ∀ z ∈ a :: w, (Gᶜ.Adj p z ↔ z = a) := by
    intro z hz
    constructor
    · intro hadj
      rcases List.mem_cons.mp hz with h | h
      · exact h
      · exact absurd (hpW z h) hadj.2
    · rintro rfl
      exact (G.compl_adj p z).mpr ⟨hpane, hpa⟩
  have hqT : ∀ z ∈ a :: w, (Gᶜ.Adj q z ↔ z = last) := by
    intro z hz
    constructor
    · intro hadj
      rcases List.mem_cons.mp hz with h | h
      · exact absurd (h ▸ hqa) hadj.2
      · by_contra hzl
        exact hadj.2 (hqbefore z h hzl)
    · rintro rfl
      exact (G.compl_adj q z).mpr
        ⟨fun he => hRw q (List.getElem_mem hq1) (he ▸ hlastw), hqmiss⟩
  have hpnotT : p ∉ a :: w := by
    intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hpane h
    · exact hRw p (List.getElem_mem hp2) h
  have hqnotT : q ∉ a :: w := by
    intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hqane h
    · exact hRw q (List.getElem_mem hq1) h
  have hT3 : 3 ≤ pathLength (a :: w) := by
    simp only [pathLength, List.length_cons]
    omega
  have hSnew : StepConnected Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) :=
    stepConnected_compl_adjoin_interior_pair hS hpOut hqOut hpAB hqAB hpq.symm
  have hstair : IsStaircase Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) a (a :: w) last :=
    staircase_compl_adjoin_pair hS hSnew hleft hlast hbeforeA hwB hanti hT3
      hpT hqT hpnotT hqnotT
  exact compl_adjoin_pair_absurd hK rfl hpOut hstair

end Workspace.ProofLemmas.Thm131Closing
