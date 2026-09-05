import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The complementary staircase in the short-path case of 13.2

When the middle class of a step-connected strip is empty, every old rung is
an edge.  Two vertices anticomplete to the old strip and adjacent to one
another then turn every such edge into a two-rung step in the complement.
This is the elementary strip construction suppressed in claim (5).
-/

namespace Workspace.ProofLemmas.Thm132ComplementStaircase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

private theorem rung_edge_of_empty
    {G : SimpleGraph V} {A B : Set V} {a b : V} {P : List V}
    (hAB : Disjoint A B) (hP : IsRungOfStrip G A (∅ : Set V) B a P b) :
    G.Adj a b := by
  have hab : a ≠ b := fun he =>
    Set.disjoint_left.mp hAB hP.2.1 (he ▸ hP.2.2.1)
  have hlen : pathLength P = 1 := by
    by_contra hne
    have hpos : 0 < P.length := PathBasics.path_length_pos hP.1.1
    have htwo : 2 ≤ pathLength P := by
      have hzero : pathLength P ≠ 0 := by
        intro hz
        have hL : P.length = 1 := by
          rw [PathBasics.pathLength_eq] at hz
          omega
        have ha : P[0]'hpos = a :=
          PathBasics.getElem_zero_of_head? hP.1.2.1 hpos
        have hb : P[P.length - 1]'(by omega) = b :=
          PathBasics.getElem_last_of_getLast? hP.1.2.2 hpos
        apply hab
        rw [← ha, ← hb]
        congr 1
        omega
      omega
    have hL3 : 3 ≤ P.length := by
      rw [PathBasics.pathLength_eq] at htwo
      omega
    have hm := hP.2.2.2.2.2 (P[1]'(by omega))
      (PathBasics.getElem_mem_interior hP.1.1 (by omega) (by omega) (by omega))
    exact Set.notMem_empty _ hm
  exact PathBasics.isPathFrom_ends_adj_of_length_one hP.1 hlen

/-- If `x,y` are consecutive vertices of a banister and hence anticomplete to
the old strip, adjoining them on opposite sides produces the complementary
step-connected strip used in claim (5). -/
theorem stepConnected_compl_adjoin_pair
    (G : SimpleGraph V) (A B : Set V) (x y : V)
    (hS : StepConnected G A (∅ : Set V) B)
    (hxout : x ∉ A ∪ B) (hyout : y ∉ A ∪ B)
    (hxy : G.Adj x y)
    (hxanti : VertexAnticomplete G x (A ∪ B))
    (hyanti : VertexAnticomplete G y (A ∪ B)) :
    StepConnected Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y}) := by
  classical
  have hAB : Disjoint A B := hS.1.1
  have hxA : x ∉ A := fun h => hxout (Or.inl h)
  have hxB : x ∉ B := fun h => hxout (Or.inr h)
  have hyA : y ∉ A := fun h => hyout (Or.inl h)
  have hyB : y ∉ B := fun h => hyout (Or.inr h)
  have hxyne : x ≠ y := hxy.ne

  have rung_for_A : ∀ a ∈ A, ∃ b ∈ B, G.Adj a b := by
    intro a ha
    obtain ⟨a', P, b, hP, haP⟩ :=
      hS.2.2.1 a (Or.inl (Or.inl ha))
    have haa : a = a' := hP.2.2.2.1 a haP ha
    subst a'
    exact ⟨b, hP.2.2.1, rung_edge_of_empty hAB hP⟩
  have rung_for_B : ∀ b ∈ B, ∃ a ∈ A, G.Adj a b := by
    intro b hb
    obtain ⟨a, P, b', hP, hbP⟩ :=
      hS.2.2.1 b (Or.inl (Or.inr hb))
    have hbb : b = b' := hP.2.2.2.2.1 b hbP hb
    subst b'
    exact ⟨a, hP.2.1, rung_edge_of_empty hAB hP⟩

  have new_step : ∀ (a b : V), a ∈ A → b ∈ B → G.Adj a b →
      IsStep Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y})
        b [b, y] y x [x, a] a := by
    intro a b ha hb hab
    have hb_y : Gᶜ.Adj b y := by
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hyB (he.symm ▸ hb), fun hadj => hyanti b (Or.inr hb) hadj.symm⟩
    have hx_a : Gᶜ.Adj x a := by
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hxA (he ▸ ha), hxanti a (Or.inl ha)⟩
    have hb_x : Gᶜ.Adj b x := by
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hxB (he.symm ▸ hb), fun hadj => hxanti b (Or.inr hb) hadj.symm⟩
    have hy_a : Gᶜ.Adj y a := by
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hyA (he ▸ ha), hyanti a (Or.inl ha)⟩
    have hba : b ≠ a := fun he => Set.disjoint_left.mp hAB (he.symm ▸ ha) hb
    have hbneY : b ≠ y := fun he => hyB (he.symm ▸ hb)
    have hxneA : x ≠ a := fun he => hxA (he ▸ ha)
    have hr1 : IsRungOfStrip Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y})
        b [b, y] y := by
      refine ⟨⟨PathBasics.isPathList_pair hb_y, rfl, by simp⟩,
        Or.inl hb, Or.inr rfl, ?_, ?_, ?_⟩
      · intro z hz hzL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rfl
        · rcases hzL with hyB' | hyx
          · exact absurd hyB' hyB
          · exact absurd hyx hxyne.symm
      · intro z hz hzR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rcases hzR with hbA | hby
          · exact absurd hbA (Set.disjoint_right.mp hAB hb)
          · exact absurd hby hbneY
        · rfl
      · simp [Workspace.Types.Core.SPGT.interior]
    have hr2 : IsRungOfStrip Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y})
        x [x, a] a := by
      refine ⟨⟨PathBasics.isPathList_pair hx_a, rfl, by simp⟩,
        Or.inr rfl, Or.inl ha, ?_, ?_, ?_⟩
      · intro z hz hzL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rfl
        · rcases hzL with haB | hax
          · exact absurd haB (Set.disjoint_left.mp hAB ha)
          · exact absurd hax hxneA.symm
      · intro z hz hzR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rcases hzR with hxA' | hxy'
          · exact absurd hxA' hxA
          · exact absurd hxy' hxyne
        · rfl
      · simp [Workspace.Types.Core.SPGT.interior]
    refine ⟨hr1, hr2, ?_, ?_⟩
    · intro z hz1 hz2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz1 hz2
      rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl
      · exact hxB hb
      · exact hba rfl
      · exact hxyne.symm rfl
      · exact hyA ha
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact iff_of_true hb_x (Or.inl ⟨rfl, rfl⟩)
      · exact iff_of_false
          (by rw [SimpleGraph.compl_adj]; exact fun h => h.2 hab.symm)
          (by rintro (⟨-, h⟩ | ⟨h, -⟩); exact hxneA h.symm; exact hbneY h)
      · exact iff_of_false
          (by rw [SimpleGraph.compl_adj]; exact fun h => h.2 hxy.symm)
          (by rintro (⟨h, -⟩ | ⟨-, h⟩); exact hbneY h.symm; exact hxneA h)
      · exact iff_of_true hy_a (Or.inr ⟨rfl, rfl⟩)

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, Set.disjoint_empty _, Set.disjoint_empty _⟩
    exact Set.disjoint_left.mpr fun z hzL hzR => by
      rcases hzL with hzB | hzx <;> rcases hzR with hzA | hzy
      · exact Set.disjoint_right.mp hAB hzB hzA
      · exact hyB (hzy ▸ hzB)
      · exact hxA (hzx ▸ hzA)
      · exact hxyne (hzx.symm.trans hzy)
  · exact ⟨⟨x, Or.inr rfl⟩, ⟨y, Or.inr rfl⟩⟩
  · intro z hz
    rcases hz with ((hzB | hzx) | (hzA | hzy)) | hz0
    · obtain ⟨a, ha, hab⟩ := rung_for_B z hzB
      exact ⟨z, [z, y], y, (new_step a z ha hzB hab).1, by simp⟩
    · subst z
      obtain ⟨a, ha⟩ := hS.2.1.1
      obtain ⟨b, hb, hab⟩ := rung_for_A a ha
      exact ⟨x, [x, a], a, (new_step a b ha hb hab).2.1, by simp⟩
    · obtain ⟨b, hb, hab⟩ := rung_for_A z hzA
      exact ⟨x, [x, z], z, (new_step z b hzA hb hab).2.1, by simp⟩
    · subst z
      obtain ⟨b, hb⟩ := hS.2.1.2
      obtain ⟨a, ha, hab⟩ := rung_for_B b hb
      exact ⟨b, [b, y], y, (new_step a b ha hb hab).1, by simp⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · intro z hz
    rcases hz with ((hzB | hzx) | (hzA | hzy)) | hz0
    · obtain ⟨a, ha, hab⟩ := rung_for_B z hzB
      exact ⟨z, [z, y], y, x, [x, a], a, new_step a z ha hzB hab, Or.inl (by simp)⟩
    · subst z
      obtain ⟨a, ha⟩ := hS.2.1.1
      obtain ⟨b, hb, hab⟩ := rung_for_A a ha
      exact ⟨b, [b, y], y, x, [x, a], a, new_step a b ha hb hab, Or.inr (by simp)⟩
    · obtain ⟨b, hb, hab⟩ := rung_for_A z hzA
      exact ⟨b, [b, y], y, x, [x, z], z, new_step z b hzA hb hab, Or.inr (by simp)⟩
    · subst z
      obtain ⟨b, hb⟩ := hS.2.1.2
      obtain ⟨a, ha, hab⟩ := rung_for_B b hb
      exact ⟨b, [b, y], y, x, [x, a], a, new_step a b ha hb hab, Or.inl (by simp)⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · intro X Y hXY hdis hX hY
    rcases hXY with hL | hR
    · by_cases hxX : x ∈ X
      · obtain ⟨b, hbY⟩ := hY
        have hbL : b ∈ B ∪ {x} := by rw [← hL]; exact Or.inr hbY
        have hbB : b ∈ B := hbL.resolve_right (fun he =>
          Set.disjoint_left.mp hdis hxX (he ▸ hbY))
        obtain ⟨a, ha, hab⟩ := rung_for_B b hbB
        exact ⟨x, [x, a], a, b, [b, y], y,
          step_symm (new_step a b ha hbB hab),
          Or.inl hxX, Or.inl hbY⟩
      · have hxY : x ∈ Y := (show x ∈ X ∪ Y by rw [hL]; exact Or.inr rfl).resolve_left hxX
        obtain ⟨b, hbX⟩ := hX
        have hbL : b ∈ B ∪ {x} := by rw [← hL]; exact Or.inl hbX
        have hbB : b ∈ B := hbL.resolve_right (fun he => hxX (he ▸ hbX))
        obtain ⟨a, ha, hab⟩ := rung_for_B b hbB
        exact ⟨b, [b, y], y, x, [x, a], a, new_step a b ha hbB hab,
          Or.inl hbX, Or.inl hxY⟩
    · by_cases hyX : y ∈ X
      · obtain ⟨a, haY⟩ := hY
        have haR : a ∈ A ∪ {y} := by rw [← hR]; exact Or.inr haY
        have haA : a ∈ A := haR.resolve_right (fun he =>
          Set.disjoint_left.mp hdis hyX (he ▸ haY))
        obtain ⟨b, hb, hab⟩ := rung_for_A a haA
        exact ⟨b, [b, y], y, x, [x, a], a,
          new_step a b haA hb hab,
          Or.inr hyX, Or.inr haY⟩
      · have hyY : y ∈ Y := (show y ∈ X ∪ Y by rw [hR]; exact Or.inr rfl).resolve_left hyX
        obtain ⟨a, haX⟩ := hX
        have haR : a ∈ A ∪ {y} := by rw [← hR]; exact Or.inl haX
        have haA : a ∈ A := haR.resolve_right (fun he => hyX (he ▸ haX))
        obtain ⟨b, hb, hab⟩ := rung_for_A a haA
        exact ⟨x, [x, a], a, b, [b, y], y, step_symm (new_step a b haA hb hab),
          Or.inr haX, Or.inr hyY⟩

/-- An induced path whose interior lies in another induced path and which
contains both ends of that inner path must traverse it in order.  The two
displayed end adjacencies choose the orientation. -/
theorem path_eq_cons_append_of_inner_path
    {H : SimpleGraph V} {T Q : List V} {r s x y : V}
    (hT : IsPathFrom H T r s) (hT2 : 2 ≤ T.length)
    (hQ : IsPathFrom H Q x y)
    (hxT : x ∉ T) (hyT : y ∉ T)
    (hinner : ∀ z ∈ interior Q, z ∈ T)
    (hrQ : r ∈ Q) (hsQ : s ∈ Q)
    (hxr : H.Adj x r) (hys : H.Adj y s) :
    Q = x :: (T ++ [y]) := by
  classical
  have hTpos : 0 < T.length := by omega
  have hT0 : T[0]'hTpos = r :=
    PathBasics.getElem_zero_of_head? hT.2.1 hTpos
  have hTlast : T[T.length - 1]'(by omega) = s :=
    PathBasics.getElem_last_of_getLast? hT.2.2 hTpos
  have hrs : r ≠ s := PathBasics.isPathFrom_ends_ne hT (by
    rw [PathBasics.pathLength_eq]
    omega)
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hQ0 : Q[0]'hQpos = x :=
    PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = y :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  obtain ⟨ir, hir, heir⟩ := List.mem_iff_getElem.mp hrQ
  obtain ⟨is, his, heis⟩ := List.mem_iff_getElem.mp hsQ
  have hir1 : ir = 1 := by
    have hadj : H.Adj (Q[0]'hQpos) (Q[ir]'hir) := by
      simpa [hQ0, heir] using hxr
    rcases (PathBasics.path_adj_iff hQ.1 hQpos hir).mp hadj with h | h
    · omega
    · omega
  have hisLast : is = Q.length - 2 := by
    have hadj : H.Adj (Q[Q.length - 1]'(by omega)) (Q[is]'his) := by
      simpa [hQlast, heis] using hys
    rcases (PathBasics.path_adj_iff hQ.1 (by omega) his).mp hadj with h | h
    · omega
    · omega
  have his0 : is ≠ 0 := by
    intro hz
    have h0is : Q[0]'hQpos = Q[is]'his := by
      apply hQ.1.2.1.getElem_inj_iff.mpr
      omega
    have hxs : x = s := by
      exact hQ0.symm.trans (h0is.trans heis)
    exact hxT (hxs ▸ PathBasics.getLast_mem hT.2.2)
  have his1 : is ≠ 1 := by
    intro hz
    apply hrs
    have hris : Q[ir]'hir = Q[is]'his := by
      apply hQ.1.2.1.getElem_inj_iff.mpr
      omega
    exact heir.symm.trans (hris.trans heis)
  have hisgt : 1 < is := by omega

  have hmap : ∀ k (hk : k < T.length),
      ∃ (hqk : k + 1 < Q.length),
        Q[k + 1]'hqk = T[k]'hk ∧ k + 1 ≤ is := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero =>
          have hq1 : 1 < Q.length := by rw [← hir1]; exact hir
          refine ⟨hq1, ?_, by omega⟩
          calc
            Q[1]'hq1 = Q[ir]'hir := by
              apply hQ.1.2.1.getElem_inj_iff.mpr
              omega
            _ = r := heir
            _ = T[0]'hk := hT0.symm
      | succ n =>
          have hnT : n < T.length := by omega
          obtain ⟨hqn, heqn, hnle⟩ := ih n (by omega) hnT
          have hnlt : n + 1 < is := by
            by_contra hnot
            have heqni : n + 1 = is := by omega
            have hTs : T[n]'hnT = s := by
              have hqi : Q[n + 1]'hqn = Q[is]'his := by
                apply hQ.1.2.1.getElem_inj_iff.mpr
                exact heqni
              exact heqn.symm.trans (hqi.trans heis)
            have hnlast : n = T.length - 1 := by
              have hlastlt : T.length - 1 < T.length := by omega
              apply hT.1.2.1.getElem_inj_iff.mp
              exact hTs.trans hTlast.symm
            omega
          have hqcur : n + 2 < Q.length := by
            rw [hisLast] at hnlt
            omega
          have hqadj : H.Adj (Q[n + 1]'hqn) (Q[n + 2]'hqcur) :=
            PathBasics.path_adj_succ hQ.1 (i := n + 1) (by omega)
          by_cases hcur : n + 2 = is
          · have hnadjS : H.Adj (T[n]'hnT) s := by
              have hqcurS : Q[n + 2]'hqcur = s := by
                have hqi : Q[n + 2]'hqcur = Q[is]'his := by
                  apply hQ.1.2.1.getElem_inj_iff.mpr
                  exact hcur
                exact hqi.trans heis
              simpa only [heqn, hqcurS] using hqadj
            have hnlast : n + 1 = T.length - 1 := by
              have hadj : H.Adj (T[n]'hnT) (T[T.length - 1]'(by omega)) := by
                simpa [hTlast] using hnadjS
              rcases (PathBasics.path_adj_iff hT.1 hnT (by omega)).mp hadj with h | h
              · omega
              · omega
            refine ⟨hqcur, ?_, by omega⟩
            calc
              Q[n + 2]'hqcur = Q[is]'his := by
                apply hQ.1.2.1.getElem_inj_iff.mpr
                exact hcur
              _ = s := heis
              _ = T[n + 1]'hk := by
                rw [← hTlast]
                apply hT.1.2.1.getElem_inj_iff.mpr
                omega
          · have hcurLt : n + 2 < is := by omega
            have hqint : Q[n + 2]'hqcur ∈ interior Q :=
              PathBasics.getElem_mem_interior hQ.1 hqcur (by omega) (by
                rw [hisLast] at hcurLt
                omega)
            have hqT := hinner _ hqint
            obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp hqT
            have hTadj : H.Adj (T[n]'hnT) (T[j]'hj) := by
              rw [← heqn, hej]
              exact hqadj
            rcases (PathBasics.path_adj_iff hT.1 hnT hj).mp hTadj with hfwd | hback
            · refine ⟨hqcur, ?_, by omega⟩
              calc
                Q[n + 2]'hqcur = T[j]'hj := hej.symm
                _ = T[n + 1]'hk := by
                  apply hT.1.2.1.getElem_inj_iff.mpr
                  omega
            · have hnpos : 0 < n := by omega
              obtain ⟨hqm, heqm, -⟩ := ih (n - 1) (by omega) (by omega)
              have hjm : j = n - 1 := by omega
              have hrepeat : Q[n]'(by omega) = Q[n + 2]'hqcur := by
                calc
                  Q[n]'(by omega) = Q[(n - 1) + 1]'hqm := by
                    apply hQ.1.2.1.getElem_inj_iff.mpr
                    omega
                  _ = T[n - 1]'(by omega) := heqm
                  _ = T[j]'hj := by
                    apply hT.1.2.1.getElem_inj_iff.mpr
                    omega
                  _ = Q[n + 2]'hqcur := hej
              exact absurd (hQ.1.2.1.getElem_inj_iff.mp hrepeat) (by omega)

  obtain ⟨hqend, hqendEq, hendLe⟩ := hmap (T.length - 1) (by omega)
  have hqTlen : T.length < Q.length := by omega
  have hqendS : Q[T.length]'hqTlen = s := by
    calc
      Q[T.length]'hqTlen = Q[(T.length - 1) + 1]'hqend := by
        apply hQ.1.2.1.getElem_inj_iff.mpr
        omega
      _ = T[T.length - 1]'(by omega) := hqendEq
      _ = s := hTlast
  have hTi : T.length = is := by
    have heq : Q[T.length]'hqTlen = Q[is]'his := hqendS.trans heis.symm
    exact hQ.1.2.1.getElem_inj_iff.mp heq
  have hlen : Q.length = T.length + 2 := by omega
  apply List.ext_getElem (by simp [hlen])
  intro j hjQ hjR
  cases j with
  | zero => simpa using hQ0
  | succ j =>
      by_cases hjT : j < T.length
      · obtain ⟨hqj, heqj, -⟩ := hmap j hjT
        rw [List.getElem_cons_succ, List.getElem_append_left hjT]
        simpa using heqj
      · have hjEq : j = T.length := by
          simp only [List.length_cons, List.length_append, List.length_singleton] at hjR
          omega
        subst j
        rw [List.getElem_cons_succ, List.getElem_append_right (le_refl T.length)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        have : Q[T.length + 1]'hjQ = y := by
          simpa [hlen] using hQlast
        exact this

private theorem path_head_neighbor_unique
    {H : SimpleGraph V} {T : List V} {r s z : V}
    (hT : IsPathFrom H T r s) (hT2 : 2 ≤ T.length)
    (hz : z ∈ T) (hrz : H.Adj r z) : z = T[1]'(by omega) := by
  have hpos : 0 < T.length := by omega
  have h0 : T[0]'hpos = r :=
    PathBasics.getElem_zero_of_head? hT.2.1 hpos
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp hz
  have hadj : H.Adj (T[0]'hpos) (T[j]'hj) := by
    simpa only [h0, hej] using hrz
  have hj1 : j = 1 := by
    rcases (PathBasics.path_adj_iff hT.1 hpos hj).mp hadj with h | h <;> omega
  calc
    z = T[j]'hj := hej.symm
    _ = T[1]'(by omega) := by
      apply hT.1.2.1.getElem_inj_iff.mpr
      exact hj1

/-- If an outer induced path has all of its internal vertices in `T`, and
contains the first end of `T`, then that end is adjacent to one of the two
outer ends. -/
private theorem inner_head_adj_outer_end
    {H : SimpleGraph V} {T Q : List V} {r s x y : V}
    (hT : IsPathFrom H T r s) (hT2 : 2 ≤ T.length)
    (hQ : IsPathFrom H Q x y)
    (hxT : x ∉ T) (hyT : y ∉ T)
    (hinner : ∀ z ∈ interior Q, z ∈ T)
    (hrQ : r ∈ Q) : H.Adj x r ∨ H.Adj y r := by
  have hrT : r ∈ T := PathBasics.head_mem hT.2.1
  have hrx : r ≠ x := fun he => hxT (he.symm ▸ hrT)
  have hry : r ≠ y := fun he => hyT (he.symm ▸ hrT)
  have hrint : r ∈ interior Q :=
    (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hrQ, hrx, hry⟩
  obtain ⟨i, hi, hi1, hi2, hei⟩ :=
    PathBasics.exists_getElem_of_mem_interior hQ.1 hrint
  have hQpos : 0 < Q.length := by omega
  have hQ0 : Q[0]'hQpos = x :=
    PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = y :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  by_cases hfirst : i = 1
  · left
    have hadj : H.Adj (Q[0]'hQpos) (Q[i]'hi) :=
      (PathBasics.path_adj_iff hQ.1 hQpos hi).mpr (Or.inl (by omega))
    simpa only [hQ0, hei] using hadj
  by_cases hlast : i + 2 = Q.length
  · right
    have hadj : H.Adj (Q[Q.length - 1]'(by omega)) (Q[i]'hi) :=
      (PathBasics.path_adj_iff hQ.1 (by omega) hi).mpr (Or.inr (by omega))
    simpa only [hQlast, hei] using hadj
  · have hprev : i - 1 < Q.length := by omega
    have hnext : i + 1 < Q.length := by omega
    have hprevInt : Q[i - 1]'hprev ∈ interior Q :=
      PathBasics.getElem_mem_interior hQ.1 hprev (by omega) (by omega)
    have hnextInt : Q[i + 1]'hnext ∈ interior Q :=
      PathBasics.getElem_mem_interior hQ.1 hnext (by omega) (by omega)
    have hprevT := hinner _ hprevInt
    have hnextT := hinner _ hnextInt
    have hadjPrev : H.Adj r (Q[i - 1]'hprev) := by
      have hadj : H.Adj (Q[i]'hi) (Q[i - 1]'hprev) :=
        (PathBasics.path_adj_iff hQ.1 hi hprev).mpr (Or.inr (by omega))
      simpa only [hei] using hadj
    have hadjNext : H.Adj r (Q[i + 1]'hnext) := by
      have hadj : H.Adj (Q[i]'hi) (Q[i + 1]'hnext) :=
        (PathBasics.path_adj_iff hQ.1 hi hnext).mpr (Or.inl rfl)
      simpa only [hei] using hadj
    have hp := path_head_neighbor_unique hT hT2 hprevT hadjPrev
    have hn := path_head_neighbor_unique hT hT2 hnextT hadjNext
    have heq : Q[i - 1]'hprev = Q[i + 1]'hnext := hp.trans hn.symm
    exact absurd (hQ.1.2.1.getElem_inj_iff.mp heq) (by omega)

private theorem path_head_adjacent_members_eq
    {H : SimpleGraph V} {Q : List V} {x y u v : V}
    (hQ : IsPathFrom H Q x y) (hu : u ∈ Q) (hv : v ∈ Q)
    (hxu : H.Adj x u) (hxv : H.Adj x v) : u = v := by
  have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have h0 : Q[0]'hpos = x :=
    PathBasics.getElem_zero_of_head? hQ.2.1 hpos
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp hv
  have hi1 : i = 1 := by
    have hadj : H.Adj (Q[0]'hpos) (Q[i]'hi) := by
      simpa only [h0, hei] using hxu
    rcases (PathBasics.path_adj_iff hQ.1 hpos hi).mp hadj with h | h <;> omega
  have hj1 : j = 1 := by
    have hadj : H.Adj (Q[0]'hpos) (Q[j]'hj) := by
      simpa only [h0, hej] using hxv
    rcases (PathBasics.path_adj_iff hQ.1 hpos hj).mp hadj with h | h <;> omega
  calc
    u = Q[i]'hi := hei.symm
    _ = Q[j]'hj := by
      apply hQ.1.2.1.getElem_inj_iff.mpr
      omega
    _ = v := hej

/-- The orientation-free form needed after 2.1: the outer antipath consists
of its first end, all of `T` in one of the two orientations, and its last end. -/
theorem path_orientation_of_inner_subset
    {H : SimpleGraph V} {T Q : List V} {r s x y : V}
    (hT : IsPathFrom H T r s) (hT2 : 2 ≤ T.length)
    (hQ : IsPathFrom H Q x y)
    (hxT : x ∉ T) (hyT : y ∉ T)
    (hinner : ∀ z ∈ interior Q, z ∈ T)
    (hrQ : r ∈ Q) (hsQ : s ∈ Q) :
    Q = x :: (T ++ [y]) ∨ Q = x :: (T.reverse ++ [y]) := by
  have hrend := inner_head_adj_outer_end hT hT2 hQ hxT hyT hinner hrQ
  have hTrev : IsPathFrom H T.reverse s r := PathBasics.isPathFrom_reverse hT
  have hinnerRev : ∀ z ∈ interior Q.reverse, z ∈ T.reverse := by
    intro z hz
    have hzmem : z ∈ Q := by
      have := PathBasics.interior_subset hz
      simpa using this
    have hzy : z ≠ y :=
      (PathBasics.mem_interior_iff_of_pathFrom
        (PathBasics.isPathFrom_reverse hQ)).mp hz |>.2.1
    have hzx : z ≠ x :=
      (PathBasics.mem_interior_iff_of_pathFrom
        (PathBasics.isPathFrom_reverse hQ)).mp hz |>.2.2
    have hzint : z ∈ interior Q :=
      (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hzmem, hzx, hzy⟩
    simpa using hinner z hzint
  have hsend := inner_head_adj_outer_end hTrev (by simpa using hT2)
    (PathBasics.isPathFrom_reverse hQ) (by simpa using hyT) (by simpa using hxT)
    hinnerRev (by simpa using hsQ)
  have hrs : r ≠ s := PathBasics.isPathFrom_ends_ne hT (by
    rw [PathBasics.pathLength_eq]
    omega)
  rcases hrend with hxr | hyr <;> rcases hsend with hys | hxs
  · exact Or.inl (path_eq_cons_append_of_inner_path hT hT2 hQ hxT hyT
      hinner hrQ hsQ hxr hys)
  · exfalso
    exact hrs (path_head_adjacent_members_eq hQ hrQ hsQ hxr hxs)
  · exfalso
    have heqrs : r = s := path_head_adjacent_members_eq
      (PathBasics.isPathFrom_reverse hQ) (by simpa using hrQ) (by simpa using hsQ) hyr hys
    exact hrs heqrs
  · exact Or.inr (path_eq_cons_append_of_inner_path hTrev (by simpa using hT2)
      hQ (by simpa using hxT) (by simpa using hyT)
      (fun z hz => by simpa using hinner z hz) hsQ hrQ hxs hyr)

/-- The exact complementary staircase used to finish the short-path branch.
The path `Q = x-T-y` records that `x` attaches only to the left end of the
complement-banister and `y` only to its right end. -/
theorem staircase_compl_of_outer_path
    (G : SimpleGraph V) (A B : Set V) (x y r s : V) (T Q : List V)
    (hS : StepConnected G A (∅ : Set V) B)
    (hleft : IsLeftStar G A (∅ : Set V) B r)
    (hright : IsRightStar G A (∅ : Set V) B s)
    (hT : IsPathFrom Gᶜ T r s) (hT3 : 3 ≤ pathLength T)
    (hTout : ∀ z ∈ T, z ∉ A ∪ B)
    (hTint : ∀ z ∈ interior T, VertexComplete G z (A ∪ B))
    (hxout : x ∉ A ∪ B) (hyout : y ∉ A ∪ B)
    (hxT : x ∉ T) (hyT : y ∉ T)
    (hxy : G.Adj x y)
    (hxanti : VertexAnticomplete G x (A ∪ B))
    (hyanti : VertexAnticomplete G y (A ∪ B))
    (hQ : IsPathFrom Gᶜ Q x y) (hQeq : Q = x :: (T ++ [y])) :
    IsStaircase Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y}) r T s := by
  classical
  have hSnew := stepConnected_compl_adjoin_pair G A B x y hS hxout hyout
    hxy hxanti hyanti
  have hTpos : 0 < T.length := PathBasics.path_length_pos hT.1
  have hT0 : T[0]'hTpos = r :=
    PathBasics.getElem_zero_of_head? hT.2.1 hTpos
  have hTlast : T[T.length - 1]'(by omega) = s :=
    PathBasics.getElem_last_of_getLast? hT.2.2 hTpos
  have hQ' : IsPathFrom Gᶜ (x :: (T ++ [y])) x y := by
    simpa [hQeq] using hQ
  have hxAdj : ∀ z ∈ T, (Gᶜ.Adj x z ↔ z = r) := by
    intro z hz
    obtain ⟨k, hk, hek⟩ := List.mem_iff_getElem.mp hz
    have hqk : k + 1 < (x :: (T ++ [y])).length := by simp; omega
    have hq0 : 0 < (x :: (T ++ [y])).length := by simp
    have helem : (x :: (T ++ [y]))[k + 1]'hqk = T[k]'hk := by
      simp only [List.getElem_cons_succ, List.getElem_append_left hk]
    constructor
    · intro hadj
      have hi := (PathBasics.path_adj_iff hQ'.1 hq0 hqk).mp (by
        simpa only [List.getElem_cons_zero, helem, hek] using hadj)
      have hk0 : k = 0 := by rcases hi with h | h <;> omega
      calc
        z = T[k]'hk := hek.symm
        _ = T[0]'hTpos := by
          apply hT.1.2.1.getElem_inj_iff.mpr
          exact hk0
        _ = r := hT0
    · intro hzr
      have hk0 : k = 0 := by
        apply hT.1.2.1.getElem_inj_iff.mp
        calc
          T[k]'hk = z := hek
          _ = r := hzr
          _ = T[0]'hTpos := hT0.symm
      have hadj : Gᶜ.Adj ((x :: (T ++ [y]))[0]'hq0)
          ((x :: (T ++ [y]))[k + 1]'hqk) :=
        (PathBasics.path_adj_iff hQ'.1 hq0 hqk).mpr (Or.inl (by omega))
      simpa only [List.getElem_cons_zero, helem, hek] using hadj
  have hyAdj : ∀ z ∈ T, (Gᶜ.Adj y z ↔ z = s) := by
    intro z hz
    obtain ⟨k, hk, hek⟩ := List.mem_iff_getElem.mp hz
    have hqk : k + 1 < (x :: (T ++ [y])).length := by simp; omega
    have hqlast : (x :: (T ++ [y])).length - 1 <
        (x :: (T ++ [y])).length := by simp
    have helem : (x :: (T ++ [y]))[k + 1]'hqk = T[k]'hk := by
      simp only [List.getElem_cons_succ, List.getElem_append_left hk]
    have hlastElem : (x :: (T ++ [y]))[(x :: (T ++ [y])).length - 1]'hqlast = y := by
      simpa using PathBasics.getElem_last_of_getLast? hQ'.2.2 (by simp)
    constructor
    · intro hadj
      have hi := (PathBasics.path_adj_iff hQ'.1 hqlast hqk).mp (by
        simpa only [hlastElem, helem, hek] using hadj)
      have hklast : k = T.length - 1 := by
        simp only [List.length_cons, List.length_append, List.length_singleton] at hi
        rcases hi with h | h <;> omega
      calc
        z = T[k]'hk := hek.symm
        _ = T[T.length - 1]'(by omega) := by
          apply hT.1.2.1.getElem_inj_iff.mpr
          exact hklast
        _ = s := hTlast
    · intro hzs
      have hklast : k = T.length - 1 := by
        apply hT.1.2.1.getElem_inj_iff.mp
        calc
          T[k]'hk = z := hek
          _ = s := hzs
          _ = T[T.length - 1]'(by omega) := hTlast.symm
      have hadj : Gᶜ.Adj
          ((x :: (T ++ [y]))[(x :: (T ++ [y])).length - 1]'hqlast)
          ((x :: (T ++ [y]))[k + 1]'hqk) :=
        (PathBasics.path_adj_iff hQ'.1 hqlast hqk).mpr (Or.inr (by
          have hlenOuter : (x :: (T ++ [y])).length = T.length + 2 := by simp
          rw [hlenOuter, hklast]
          omega))
      simpa only [hlastElem, helem, hek] using hadj

  have hrs : r ≠ s := PathBasics.isPathFrom_ends_ne hT (by omega)
  have hrT : r ∈ T := PathBasics.head_mem hT.2.1
  have hsT : s ∈ T := PathBasics.getLast_mem hT.2.2
  have hban : IsBanister Gᶜ (B ∪ {x}) (∅ : Set V) (A ∪ {y}) r T s := by
    refine ⟨hT, ?_, ?_, ?_, ?_⟩
    · intro z hz hznew
      rcases hznew with ((hzB | hzx) | (hzA | hzy)) | hz0
      · exact hTout z hz (Or.inr hzB)
      · exact hxT (hzx ▸ hz)
      · exact hTout z hz (Or.inl hzA)
      · exact hyT (hzy ▸ hz)
      · exact absurd hz0 (Set.notMem_empty z)
    · refine ⟨?_, ?_, ?_⟩
      · intro hrnew
        rcases hrnew with ((hrB | hrx) | (hrA | hry)) | hr0
        · exact hTout r hrT (Or.inr hrB)
        · exact hxT (hrx ▸ hrT)
        · exact hTout r hrT (Or.inl hrA)
        · exact hyT (hry ▸ hrT)
        · exact absurd hr0 (Set.notMem_empty r)
      · intro z hz
        rcases hz with hzB | hzx
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => hleft.1 (he ▸ Or.inl (Or.inr hzB)),
            fun hadj => hleft.2.2 z (Or.inl hzB) hadj⟩
        · subst z
          exact (hxAdj r hrT |>.mpr rfl).symm
      · intro z hz hadj
        rcases hz with (hzA | hzy) | hz0
        · exact (G.compl_adj r z).mp hadj |>.2 (hleft.2.1 z hzA)
        · subst z
          exact hrs ((hyAdj r hrT).mp hadj.symm)
        · exact absurd hz0 (Set.notMem_empty z)
    · refine ⟨?_, ?_, ?_⟩
      · intro hsnew
        rcases hsnew with ((hsB | hsx) | (hsA | hsy)) | hs0
        · exact hTout s hsT (Or.inr hsB)
        · exact hxT (hsx ▸ hsT)
        · exact hTout s hsT (Or.inl hsA)
        · exact hyT (hsy ▸ hsT)
        · exact absurd hs0 (Set.notMem_empty s)
      · intro z hz
        rcases hz with hzA | hzy
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => hright.1 (he ▸ Or.inl (Or.inl hzA)),
            fun hadj => hright.2.2 z (Or.inl hzA) hadj⟩
        · subst z
          exact (hyAdj s hsT |>.mpr rfl).symm
      · intro z hz hadj
        rcases hz with (hzB | hzx) | hz0
        · exact (G.compl_adj s z).mp hadj |>.2 (hright.2.1 z hzB)
        · subst z
          exact hrs ((hxAdj s hsT).mp hadj.symm).symm
        · exact absurd hz0 (Set.notMem_empty z)
    · intro z hz w hw hadj
      have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hT).mp hz
      rcases hw with ((hwB | hwx) | (hwA | hwy)) | hw0
      · exact (G.compl_adj z w).mp hadj |>.2 (hTint z hz w (Or.inr hwB))
      · subst w
        exact hzdata.2.1 ((hxAdj z hzdata.1).mp hadj.symm)
      · exact (G.compl_adj z w).mp hadj |>.2 (hTint z hz w (Or.inl hwA))
      · subst w
        exact hzdata.2.2 ((hyAdj z hzdata.1).mp hadj.symm)
      · exact absurd hw0 (Set.notMem_empty w)
  exact ⟨hSnew, hban, hT3⟩

end Workspace.ProofLemmas.Thm132ComplementStaircase
