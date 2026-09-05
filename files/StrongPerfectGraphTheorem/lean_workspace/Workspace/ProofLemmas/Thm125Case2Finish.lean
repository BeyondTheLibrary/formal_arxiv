import Workspace.ProofLemmas.Thm125Case2Geometry
import Workspace.ProofLemmas.Thm132ComplementStaircase
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S12.Thm_12_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Finishing case (2) of Theorem 12.5

After the 3.2 configuration has produced `t-u-b₀`, a short odd-antihole argument shows
that the right endpoint of the displayed antipath is complete to `A`.  Applying the same
configuration to every step makes `C` empty.  The complementary staircase from Section 13's
elementary staircase bookkeeping then contradicts strong maximality.
-/

namespace Workspace.ProofLemmas.Thm125Case2Finish

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [SimpleGraph.adj_comm, h.2.2.2 v hv u hu]
    tauto

private theorem exists_step_first {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {v : V} (hv : v ∈ A ∪ B ∪ C) :
    ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ v ∈ R₁ := by
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hv₁ | hv₂⟩ := hS.2.2.2.1 v hv
  · exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hv₁⟩
  · exact ⟨a₂, R₂, b₂, a₁, R₁, b₁, step_symm hs, hv₂⟩

/-- Case (2) of the printed proof: `q₁a₀` is an edge and `q_kb₀` is a nonedge. -/
theorem case2
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  classical
  obtain ⟨hqodd, t₀, ht₀int, ht₀Q⟩ :=
    Workspace.ProofLemmas.Thm125Case2Prelude.case2_prelude G hG hprism hbreaker
      A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
  have hleft := Workspace.ProofLemmas.Thm125Case2LeftStar.leftStar G hG hK4 hprism hbreaker
    A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
    t₀ ht₀int ht₀Q
  refine ⟨hleft, ?_⟩
  by_contra hnright
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS : StepConnected G A C B := hstair.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hstair.2.1
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    by_contra hc
    have hlen : q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : x = q₁ := by simpa using hq.2.1
    have hk : x = qk := by simpa using hq.2.2
    exact hne (h1.symm.trans hk)

  -- 12.1 puts `qk` in its major case: the minor and star cases conflict with its
  -- `B`-completeness and the present assumption that it is not a right-star.
  have hmajor : MajorForStaircase G A C B a₀ R₀ b₀ qk := by
    obtain ⟨j, hj, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 hprism
      hbreaker A C B a₀ b₀ R₀ hK.1 qk hqk.1.1
    fin_cases j
    · exfalso
      rcases hj.2.2 with hr | hnB
      · exact hnright hr
      · exact hnB (fun b hb => hqk.1.2 b (Or.inl hb))
    · exact hj.1
    · exfalso
      rcases hj with hl | hr
      · obtain ⟨b, hb⟩ := hS.2.1.2
        exact hl.1.2.2 b (Or.inl hb) (hqk.1.2 b (Or.inl hb))
      · exact hnright hr.1
  obtain ⟨aneigh, haneighA, hqkaneigh⟩ := hmajor.2.1

  -- If an `A`-nonneighbour existed, step-connectedness supplies a step crossing the
  -- neighbour/nonneighbour partition.  The geometry lemma supplies `u`; then
  -- `a₂-u-q₁-⋯-qk-a₂` is an odd hole in the complement.
  have hqkA : VertexComplete G qk A := by
    intro a haA
    by_contra hqka
    let A₁ : Set V := {x : V | x ∈ A ∧ G.Adj qk x}
    let A₂ : Set V := {x : V | x ∈ A ∧ ¬ G.Adj qk x}
    have hAunion : A₁ ∪ A₂ = A := by
      ext x
      simp only [A₁, A₂, Set.mem_union, Set.mem_setOf_eq]
      by_cases hx : G.Adj qk x <;> simp [hx]
    have hAdisj : Disjoint A₁ A₂ := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ ⟨-, hnx⟩
      exact hnx hx
    have hA₁ne : A₁.Nonempty := ⟨aneigh, haneighA, hqkaneigh⟩
    have hA₂ne : A₂.Nonempty := ⟨a, haA, hqka⟩
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hend₁, hend₂⟩ :=
      hS.2.2.2.2 A₁ A₂ (Or.inl hAunion) hAdisj hA₁ne hA₂ne
    have ha₁A₁ : a₁ ∈ A₁ := by
      rcases hend₁ with ha | hb
      · exact ha
      · exact (Set.disjoint_left.mp hS.1.1 hb.1 hstep.1.2.2.1).elim
    have ha₂A₂ : a₂ ∈ A₂ := by
      rcases hend₂ with ha | hb
      · exact ha
      · exact (Set.disjoint_left.mp hS.1.1 hb.1 hstep.2.1.2.2.1).elim
    obtain ⟨t, u, htint, huit, htu, hub₀, htb₀, htQ, huQ, huq₁, -⟩ :=
      Workspace.ProofLemmas.Thm125Case2Geometry.geometry G hG A C B a₀ b₀ R₀ hK
        q q₁ qk hq hqint hq₁ hqk hleft hqa₀ hqodd ⟨t₀, ht₀int, ht₀Q⟩ hqkb₀
        a₁ b₁ a₂ b₂ R₁ R₂ hstep ha₁A₁.2
    have ha₂q₁ : G.Adj a₂ q₁ := (hq₁.1.2 a₂ (Or.inl ha₂A₂.1)).symm
    have ha₂qk : ¬ G.Adj a₂ qk := fun h => ha₂A₂.2 h.symm
    have hua₂ : ¬ G.Adj u a₂ :=
      hban.2.2.2.2 u huit a₂ (Or.inl (Or.inl ha₂A₂.1))
    have huout : u ∉ q := by
      intro huq
      exact outside_of_mem hq hqint hq₁.1 hqk.1 huq
        (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset huit))
    have ha₂out : a₂ ∉ q := by
      intro haq
      exact outside_of_mem hq hqint hq₁.1 hqk.1 haq (Or.inr (Or.inl (Or.inl ha₂A₂.1)))
    have hoddHole : IsHoleList Gᶜ (a₂ :: u :: q) := by
      apply Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_two_vertices hq
        (by rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]; omega)
      · exact (G.compl_adj u q₁).2 ⟨fun he => huout (he ▸
          Workspace.ProofLemmas.PathBasics.head_mem hq.2.1), huq₁⟩
      · exact (G.compl_adj a₂ qk).2 ⟨fun he => ha₂out (he ▸
          Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2), ha₂qk⟩
      · exact (G.compl_adj u a₂).2 ⟨fun he => hban.2.1 u
          (Workspace.ProofLemmas.PathBasics.interior_subset huit)
          (he ▸ Or.inl (Or.inl ha₂A₂.1)), hua₂⟩
      · exact huout
      · exact ha₂out
      · intro hc
        exact hc.2 (huQ qk ⟨Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2, hne.symm⟩)
      · intro hc
        exact hc.2 ha₂q₁
      · intro z hz hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hz
        have hz₁ := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.1
        exact hc.2 (huQ z ⟨hzq, hz₁⟩)
      · intro z hz hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hz
        have hzk := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.2
        exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2
          a₂ (Or.inl ha₂A₂.1)).symm
    have heven := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hoddHole
    have hlen : holeLength (a₂ :: u :: q) = q.length + 2 := by
      simp [holeLength]
    rw [hlen] at heven
    exact (Nat.not_even_iff_odd.mpr (hqodd.add_even (by simp))).elim heven

  -- Choose one step and retain its `t,u`; these will be the two vertices adjoined to
  -- the old strip in the complementary staircase.
  obtain ⟨aA, haA⟩ := hS.2.1.1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, haR₁⟩ :=
    exists_step_first hS (Or.inl (Or.inl haA))
  have haa₁ : aA = a₁ := hstep.1.2.2.2.1 aA haR₁ haA
  obtain ⟨t, u, htint, huit, htu, hub₀, htb₀, htQ, huQ, huq₁, hR₁one⟩ :=
    Workspace.ProofLemmas.Thm125Case2Geometry.geometry G hG A C B a₀ b₀ R₀ hK
      q q₁ qk hq hqint hq₁ hqk hleft hqa₀ hqodd ⟨t₀, ht₀int, ht₀Q⟩ hqkb₀
      a₁ b₁ a₂ b₂ R₁ R₂ hstep (haa₁ ▸ hqkA aA haA)

  have hCempty : C = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro c hcC
    obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hcP₁⟩ :=
      exists_step_first hS (Or.inr hcC)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hP₁one⟩ :=
      Workspace.ProofLemmas.Thm125Case2Geometry.geometry G hG A C B a₀ b₀ R₀ hK
        q q₁ qk hq hqint hq₁ hqk hleft hqa₀ hqodd ⟨t₀, ht₀int, ht₀Q⟩ hqkb₀
        c₁ d₁ c₂ d₂ P₁ P₂ hs (hqkA c₁ hs.1.2.1)
    have hcne₁ : c ≠ c₁ := fun he =>
      Set.disjoint_left.mp hS.1.2.1 (he ▸ hs.1.2.1) hcC
    have hcned₁ : c ≠ d₁ := fun he =>
      Set.disjoint_left.mp hS.1.2.2 (he ▸ hs.1.2.2.1) hcC
    have hcint : c ∈ interior P₁ :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).2
        ⟨hcP₁, hcne₁, hcned₁⟩
    rw [Workspace.ProofLemmas.Thm114Aux.mem_interior_iff_index hs.1.1] at hcint
    obtain ⟨i, hi, hi1, hi2, -⟩ := hcint
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hP₁one
    omega

  subst C
  have hS₀ : StepConnected G A (∅ : Set V) B := hS
  have hleft₀ : IsLeftStar G A (∅ : Set V) B q₁ := hleft
  have hright₀ : IsRightStar G A (∅ : Set V) B b₀ := hban.2.2.2.1
  let T : List V := q ++ [b₀]
  have hb₀outq : b₀ ∉ q := by
    intro hbq
    exact outside_of_mem hq hqint hq₁.1 hqk.1 hbq
      (Or.inl (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2))
  have hTb : IsPathFrom Gᶜ T q₁ b₀ := by
    dsimp [T]
    apply Workspace.ProofLemmas.PathAttach.isPathFrom_concat hq
    · exact (G.compl_adj b₀ qk).2 ⟨fun he => hb₀outq
          (he ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2), fun h => hqkb₀ h.symm⟩
    · exact hb₀outq
    · intro z hz hzk hc
      have hadj := (leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2 b₀ (Or.inr rfl)
      exact hc.2 hadj.symm
  have hTlen : 3 ≤ pathLength T := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
    simp only [T, List.length_append, List.length_singleton]
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hTout : ∀ z ∈ T, z ∉ A ∪ B := by
    intro z hz hAB
    rcases List.mem_append.1 hz with hzq | hzb
    · exact outside_of_mem hq hqint hq₁.1 hqk.1 hzq (Or.inr (by simpa using hAB))
    · rw [List.mem_singleton] at hzb
      exact hban.2.2.2.1.1 (hzb ▸ (by simpa using hAB))
  have hTint : ∀ z ∈ interior T, VertexComplete G z (A ∪ B) := by
    intro z hzint
    have hzT := Workspace.ProofLemmas.PathBasics.interior_subset hzint
    have hzq : z ∈ q := by
      rcases List.mem_append.1 hzT with h | h
      · exact h
      · rw [List.mem_singleton] at h
        exact (((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hTb).1
          hzint).2.2 h).elim
    have hzq₁ : z ≠ q₁ := by
      intro he
      exact ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hTb).1 hzint).2.1 he
    intro w hw
    rcases hw with hwA | hwB
    · by_cases hzk : z = qk
      · simpa [hzk] using hqkA w hwA
      · exact (leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2 w (Or.inl hwA)
    · exact (rightDiagonal_of_mem_ne_first hq hqint hqk.1 hzq hzq₁).2 w (Or.inl hwB)
  have huoutAB : u ∉ A ∪ B := fun hu =>
    hban.2.1 u (Workspace.ProofLemmas.PathBasics.interior_subset huit) (by simpa using hu)
  have htoutAB : t ∉ A ∪ B := fun ht =>
    hban.2.1 t (Workspace.ProofLemmas.PathBasics.interior_subset htint) (by simpa using ht)
  have huT : u ∉ T := by
    intro hu
    rcases List.mem_append.1 hu with huq | hub
    · exact outside_of_mem hq hqint hq₁.1 hqk.1 huq
        (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset huit))
    · rw [List.mem_singleton] at hub
      exact ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 huit).2.2 hub
  have htT : t ∉ T := by
    intro ht
    rcases List.mem_append.1 ht with htq | htb
    · exact outside_of_mem hq hqint hq₁.1 hqk.1 htq
        (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset htint))
    · rw [List.mem_singleton] at htb
      exact ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 htint).2.2 htb
  have huanti : VertexAnticomplete G u (A ∪ B) := by
    intro z hz
    exact hban.2.2.2.2 u huit z (by simpa using hz)
  have htanti : VertexAnticomplete G t (A ∪ B) := by
    intro z hz
    exact hban.2.2.2.2 t htint z (by simpa using hz)
  let Q : List V := u :: (T ++ [t])
  have hQ : IsPathFrom Gᶜ Q u t := by
    dsimp [Q]
    apply Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hTb
    · exact (G.compl_adj u q₁).2 ⟨fun he => huT (he ▸
          Workspace.ProofLemmas.PathBasics.head_mem hTb.2.1), huq₁⟩
    · exact (G.compl_adj t b₀).2 ⟨fun he => htT (he ▸
          Workspace.ProofLemmas.PathBasics.getLast_mem hTb.2.2), htb₀⟩
    · intro hc
      exact hc.2 htu.symm
    · exact htu.ne'
    · exact huT
    · exact htT
    · intro z hz hzq₁ hc
      rcases List.mem_append.1 hz with hzq | hzb
      · exact hc.2 (huQ z ⟨hzq, hzq₁⟩)
      · rw [List.mem_singleton] at hzb
        exact hc.2 (hzb ▸ hub₀)
    · intro z hz hzb₀ hc
      rcases List.mem_append.1 hz with hzq | hzb
      · exact hc.2 (htQ z hzq)
      · rw [List.mem_singleton] at hzb
        exact hzb₀ hzb
  have hnew := Workspace.ProofLemmas.Thm132ComplementStaircase.staircase_compl_of_outer_path
    G A B u t q₁ b₀ T Q hS₀ hleft₀ hright₀ hTb hTlen hTout hTint
    huoutAB htoutAB huT htT htu.symm huanti htanti hQ rfl
  have hnnew : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R' : List V) (b₀' : V),
      IsStaircase Gᶜ A' C' B' a₀' R' b₀' ∧
        (A ∪ B ∪ (∅ : Set V)) ⊂ (A' ∪ B' ∪ C') := by
    rcases hK.2 with hneC | hn
    · exact (Set.not_nonempty_empty hneC).elim
    · exact hn
  apply hnnew
  refine ⟨B ∪ {u}, ∅, A ∪ {t}, q₁, T, b₀, hnew, ?_⟩
  have hsub : A ∪ B ∪ (∅ : Set V) ⊆ (B ∪ {u}) ∪ (A ∪ {t}) ∪ (∅ : Set V) := by
    intro z hz
    rcases hz with (hzA | hzB) | hz0
    · exact Or.inl (Or.inr (Or.inl hzA))
    · exact Or.inl (Or.inl (Or.inl hzB))
    · exact hz0.elim
  apply (Set.ssubset_iff_of_subset hsub).2
  refine ⟨u, Or.inl (Or.inl (Or.inr rfl)), ?_⟩
  simpa using huoutAB

end Workspace.ProofLemmas.Thm125Case2Finish
