import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Classes
import Workspace.Statements.S02.Thm_2_3
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.SegmentBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.Types.NoPathMeetsThreeCatchNeighborSets

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas

private theorem anticonnected_singleton {V : Type*} {G : SimpleGraph V} (c : V) :
    AnticonnectedSet G ({c} : Set V) := by
  intro u v
  have huv : u = v := Subtype.ext (u.2.trans v.2.symm)
  subst v
  exact SimpleGraph.Reachable.refl u

private theorem isPathList_infix {V : Type*} {G : SimpleGraph V} {Q P : List V}
    (hP : IsPathList G P) (hQP : Q <:+: P) (hne : Q ≠ []) : IsPathList G Q := by
  rcases hQP with ⟨L, R, rfl⟩
  have hdrop : IsPathList G ((L ++ Q ++ R).drop L.length) :=
    PathBasics.isPathList_drop hP (by
      have := List.length_pos_of_ne_nil hne
      simp only [List.length_append]
      omega)
  have htake := PathBasics.isPathList_take hdrop (List.length_pos_of_ne_nil hne)
  simpa using htake

private theorem last_mem_tail_of_path {V : Type*} {G : SimpleGraph V} {Q : List V} {x y : V}
    (hQ : IsPathFrom G Q x y) (hlen : 2 ≤ Q.length) : y ∈ Q.tail := by
  rcases Q with _ | ⟨q, T⟩
  · simp at hlen
  · simp only [List.tail_cons]
    have hT : T ≠ [] := by intro h; simp [h] at hlen
    apply List.mem_of_mem_getLast?
    simpa [List.getLast?_cons_of_ne_nil hT] using hQ.2.2

private theorem oddWheel_of_three_colored_path
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hBerge : Berge G)
    (hnoOddWheel : ¬ ∃ (C : List V) (Y : Set V), IsOddWheel G C Y)
    (Q : List V) (x y a b c : V)
    (hQ : IsPathFrom G Q x y) (hQlen : 3 ≤ Q.length)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (haQ : a ∉ Q) (hbQ : b ∉ Q) (hcQ : c ∉ Q)
    (ha : ∀ q ∈ Q, G.Adj a q ↔ q = x)
    (hb : ∀ q ∈ Q, G.Adj b q ↔ q = y)
    (hcends : ¬ G.Adj c x ∧ ¬ G.Adj c y)
    (hcmid : ∃ z ∈ interior Q, G.Adj c z) : False := by
  have hQlength : 1 ≤ pathLength Q := by
    simp only [pathLength]
    omega
  have hxy : x ≠ y := PathBasics.isPathFrom_ends_ne hQ hQlength
  have hxQ : x ∈ Q := PathBasics.head_mem hQ.2.1
  have hyQ : y ∈ Q := PathBasics.getLast_mem hQ.2.2
  have hhole : IsHoleList G (b :: a :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hQ hQlength
      ((ha x hxQ).mpr rfl) ((hb y hyQ).mpr rfl) hab haQ hbQ ?_ ?_ ?_ ?_
    · intro hay
      exact hxy.symm ((ha y hyQ).mp hay)
    · intro hbx
      exact hxy ((hb x hxQ).mp hbx)
    · intro q hq h
      have hqi := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hq
      exact hqi.2.1 ((ha q hqi.1).mp h)
    · intro q hq h
      have hqi := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hq
      exact hqi.2.2 ((hb q hqi.1).mp h)
  let Y : Set V := {c}
  have hYanti : AnticonnectedSet G Y := anticonnected_singleton c
  have hCY : ∀ w ∈ b :: a :: Q, w ∉ Y := by
    intro w hw
    simp only [List.mem_cons, Y, Set.mem_singleton_iff] at hw ⊢
    rintro rfl
    rcases hw with h | h | h
    · exact hbc.ne h.symm
    · exact hac.ne h.symm
    · exact hcQ h
  have haY : VertexComplete G a Y := by
    intro z hz
    have : z = c := by simpa [Y] using hz
    subst z
    exact hac
  have hbY : VertexComplete G b Y := by
    intro z hz
    have : z = c := by simpa [Y] using hz
    subst z
    exact hbc
  obtain ⟨z, hzint, hcz⟩ := hcmid
  have hzQ : z ∈ Q := PathBasics.interior_subset hzint
  have hzY : VertexComplete G z Y := by
    intro d hd
    have : d = c := by simpa [Y] using hd
    subst d
    exact hcz.symm
  have hzxa : z ≠ a := fun h => haQ (h ▸ hzQ)
  have hzxb : z ≠ b := fun h => hbQ (h ▸ hzQ)
  have habne : a ≠ b := hab.ne
  have he0 : s(a, b) ∈ HoleYEdgeParity.yEdges G Y (b :: a :: Q) := by
    exact ⟨a, by simp, b, by simp, rfl, hab, haY, hbY⟩
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti
    (b :: a :: Q) (Or.inr hhole) hCY).2 hhole
  have hsecond : ∃ e ∈ HoleYEdgeParity.yEdges G Y (b :: a :: Q), e ≠ s(a, b) := by
    rcases h23 with heven | ⟨u, v, hpair, -, -⟩
    · have hpos : 0 < (HoleYEdgeParity.yEdges G Y (b :: a :: Q)).ncard :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(a, b), he0⟩
      have heven' : Even (HoleYEdgeParity.yEdges G Y (b :: a :: Q)).ncard := heven
      have htwo : 1 < (HoleYEdgeParity.yEdges G Y (b :: a :: Q)).ncard := by
        rw [Nat.even_iff] at heven'
        omega
      exact Set.exists_ne_of_one_lt_ncard htwo s(a, b)
    · exfalso
      have hma : a ∈ ({u, v} : Set V) := by
        rw [← hpair]
        exact ⟨by simp, haY⟩
      have hmb : b ∈ ({u, v} : Set V) := by
        rw [← hpair]
        exact ⟨by simp, hbY⟩
      have hmz : z ∈ ({u, v} : Set V) := by
        rw [← hpair]
        exact ⟨by simp [hzQ], hzY⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hma hmb hmz
      rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl <;>
        rcases hmz with rfl | rfl <;> simp_all
  obtain ⟨e, he, hene⟩ := hsecond
  obtain ⟨u, huC, v, hvC, rfl, huvE⟩ := he
  have hu_ne_a : u ≠ a := by
    intro hua
    subst u
    have hvY := huvE.2.2
    have hvC' : v = b ∨ v = a ∨ v ∈ Q := by simpa using hvC
    rcases hvC' with rfl | rfl | hvQ
    · exact hene rfl
    · exact G.irrefl huvE.1
    · have hav : G.Adj a v := huvE.1
      have hvx : v = x := (ha v hvQ).mp hav
      subst v
      exact hcends.1 (huvE.2.2 c (by simp [Y])).symm
  have hu_ne_b : u ≠ b := by
    intro hub
    subst u
    have hvC' : v = b ∨ v = a ∨ v ∈ Q := by simpa using hvC
    rcases hvC' with rfl | rfl | hvQ
    · exact G.irrefl huvE.1
    · exact hene Sym2.eq_swap
    · have hbv : G.Adj b v := huvE.1
      have hvy : v = y := (hb v hvQ).mp hbv
      subst v
      exact hcends.2 (huvE.2.2 c (by simp [Y])).symm
  have hv_ne_a : v ≠ a := by
    intro hva
    subst v
    have huC' : u = b ∨ u = a ∨ u ∈ Q := by simpa using huC
    rcases huC' with rfl | rfl | huQ
    · exact hene Sym2.eq_swap
    · exact G.irrefl huvE.1
    · have hau : G.Adj a u := huvE.1.symm
      have hux : u = x := (ha u huQ).mp hau
      subst u
      exact hcends.1 (huvE.2.1 c (by simp [Y])).symm
  have hv_ne_b : v ≠ b := by
    intro hvb
    subst v
    have huC' : u = b ∨ u = a ∨ u ∈ Q := by simpa using huC
    rcases huC' with rfl | rfl | huQ
    · exact G.irrefl huvE.1
    · exact hene rfl
    · have hbu : G.Adj b u := huvE.1.symm
      have huy : u = y := (hb u huQ).mp hbu
      subst u
      exact hcends.2 (huvE.2.1 c (by simp [Y])).symm
  have hWheel : IsWheel G (b :: a :: Q) Y := by
    refine ⟨⟨hhole, ?_⟩, ⟨by simp [Y], hYanti, hCY⟩,
      a, b, u, v, by simp, by simp, huC, hvC, ⟨hab, haY, hbY⟩, huvE,
      hu_ne_a.symm, hv_ne_a.symm, hu_ne_b.symm, hv_ne_b.symm⟩
    have heven := hBerge.1 (b :: a :: Q) hhole
    rw [Nat.even_iff] at heven
    simp only [holeLength, List.length_cons]
    simp only [holeLength, List.length_cons] at heven
    omega
  have hseg : IsSegment G (b :: a :: Q) Y [b, a] := by
    have htake : ((b :: a :: Q).rotate 0).take 2 = [b, a] := by simp
    rw [← htake]
    apply SegmentBasics.isSegment_of_run hhole (k := 0) (L := 2) (by omega) (by simp; omega)
    · intro t ht
      interval_cases t
      · refine ⟨b, ?_, hbY⟩
        simp
      · refine ⟨a, ?_, haY⟩
        simp
    · intro hnext
      obtain ⟨d, hdpos, hdY⟩ := hnext
      have hdpos' : d = x := by
        have hlt : 2 < (b :: a :: Q).length := by simp; omega
        rw [Nat.mod_eq_of_lt hlt] at hdpos
        have hQhead : Q[0]? = some x := by
          rw [← List.head?_eq_getElem?]
          exact hQ.2.1
        have hhead : (b :: a :: Q)[2]? = some x := by simpa using hQhead
        exact Option.some_injective _ (hdpos.symm.trans hhead)
      subst d
      exact hcends.1 ((hdY c (by simp [Y])).symm)
    · intro hprev
      obtain ⟨d, hdpos, hdY⟩ := hprev
      have hdpos' : d = y := by
        have hlt : 0 + ((b :: a :: Q).length - 1) < (b :: a :: Q).length := by
          simp only [List.length_cons]
          omega
        rw [Nat.mod_eq_of_lt hlt] at hdpos
        have hlast : (b :: a :: Q)[(b :: a :: Q).length - 1]? = some y := by
          rw [← List.getLast?_eq_getElem?]
          rw [List.getLast?_cons_of_ne_nil (by simp : a :: Q ≠ [])]
          rw [List.getLast?_cons_of_ne_nil hQ.1.1]
          exact hQ.2.2
        exact Option.some_injective _ (hdpos.symm.trans (by simpa using hlast))
      subst d
      exact hcends.2 ((hdY c (by simp [Y])).symm)
  apply hnoOddWheel
  exact ⟨b :: a :: Q, Y, hWheel, [b, a], hseg, by simp [pathLength]⟩

theorem noPathMeetsThreeCatchNeighborSets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF7 G)
    (A F : Set V) (a₁ a₂ a₃ : V)
    (hA : IsTriangle G A)
    (hAeq : A = {a₁, a₂, a₃})
    (hdistinct : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hcatch : Catches G F A)
    (hatMostOne : ∀ f ∈ F, ¬ 2 ≤ (G.neighborSet f ∩ A).ncard) :
    ¬ ∃ P : List V,
      IsPathList G P ∧
      (∀ p ∈ P, p ∈ F) ∧
      (∃ b₁ ∈ P, b₁ ∈ F ∧ G.Adj a₁ b₁) ∧
      (∃ b₂ ∈ P, b₂ ∈ F ∧ G.Adj a₂ b₂) ∧
      (∃ b₃ ∈ P, b₃ ∈ F ∧ G.Adj a₃ b₃) := by
  classical
  rintro ⟨P, hP, hPF, hb₁, hb₂, hb₃⟩
  obtain ⟨b₁, hb₁P, -, ha₁b₁⟩ := hb₁
  obtain ⟨b₂, hb₂P, -, ha₂b₂⟩ := hb₂
  obtain ⟨b₃, hb₃P, -, ha₃b₃⟩ := hb₃
  let av : Fin 3 → V := ![a₁, a₂, a₃]
  have havinj : Function.Injective av := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [av]
  have havA : ∀ i : Fin 3, av i ∈ A := by
    intro i
    fin_cases i <;> simp [av, hAeq]
  have hcolor : ∀ f ∈ F, ∀ i j : Fin 3, i ≠ j →
      ¬ (G.Adj (av i) f ∧ G.Adj (av j) f) := by
    intro f hf i j hij hadj
    have haij : av i ≠ av j := fun h => hij (havinj h)
    have hsub : ({av i, av j} : Set V) ⊆ G.neighborSet f ∩ A := by
      rintro z (rfl | rfl)
      · exact ⟨hadj.1.symm, havA i⟩
      · exact ⟨hadj.2.symm, havA j⟩
    apply hatMostOne f hf
    calc
      2 = ({av i, av j} : Set V).ncard := (Set.ncard_pair haij).symm
      _ ≤ (G.neighborSet f ∩ A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  let Meets : List V → Fin 3 → Prop := fun Q i => ∃ q ∈ Q, G.Adj (av i) q
  have hPmeets : ∀ i : Fin 3, Meets P i := by
    intro i
    fin_cases i
    · exact ⟨b₁, hb₁P, ha₁b₁⟩
    · exact ⟨b₂, hb₂P, ha₂b₂⟩
    · exact ⟨b₃, hb₃P, ha₃b₃⟩
  let Good : List V → Prop := fun Q => Q <:+: P ∧ ∀ i : Fin 3, Meets Q i
  have hex : ∃ n : ℕ, ∃ Q : List V, Good Q ∧ Q.length = n :=
    ⟨P.length, P, ⟨List.infix_refl P, hPmeets⟩, rfl⟩
  obtain ⟨Q, hQgood, hQlen⟩ := Nat.find_spec hex
  have hmin : ∀ R : List V, Good R → Q.length ≤ R.length := by
    intro R hR
    rw [hQlen]
    exact Nat.find_min' hex ⟨R, hR, rfl⟩
  have hQsub : ∀ q ∈ Q, q ∈ P := hQgood.1.subset
  have hQF : ∀ q ∈ Q, q ∈ F := fun q hq => hPF q (hQsub q hq)
  have hQne : Q ≠ [] := by
    intro hnil
    have := hQgood.2 0
    simp [Meets, hnil] at this
  have hQpath : IsPathList G Q := isPathList_infix hP hQgood.1 hQne
  have hQlen3 : 3 ≤ Q.length := by
    choose q hqQ hadjq using hQgood.2
    have hqF : ∀ i : Fin 3, q i ∈ F := fun i => hQF _ (hqQ i)
    have hqne : ∀ i j : Fin 3, i ≠ j → q i ≠ q j := by
      intro i j hij heq
      apply hcolor (q i) (hqF i) i j hij
      exact ⟨hadjq i, heq ▸ hadjq j⟩
    have hsub : ({q 0, q 1, q 2} : Set V) ⊆ {z : V | z ∈ Q} := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hz ⊢
      rcases hz with rfl | rfl | rfl
      exacts [hqQ 0, hqQ 1, hqQ 2]
    have hcard : ({q 0, q 1, q 2} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hqne 0 1 (by decide), hqne 0 2 (by decide)])
        (Set.toFinite _), Set.ncard_pair (hqne 1 2 (by decide))]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hset : {z : V | z ∈ Q} = (Q.toFinset : Set V) := by ext z; simp
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hQpath.2.1] at hle
    omega
  let x := Q[0]'(by omega)
  let y := Q[Q.length - 1]'(by omega)
  have hQfrom : IsPathFrom G Q x y := by
    refine ⟨hQpath, ?_, ?_⟩
    · simp [x, List.head?_eq_getElem?]
    · simp [y, List.getLast?_eq_getElem?]
  have htailQ : Q.tail <:+: Q := by
    simpa [List.drop_one] using (List.drop_suffix 1 Q).isInfix
  have hdropQ : Q.dropLast <:+: Q := Q.dropLast_prefix.isInfix
  have htailInfix : Q.tail <:+: P := htailQ.trans hQgood.1
  have hdropInfix : Q.dropLast <:+: P := hdropQ.trans hQgood.1
  have htailNot : ¬ ∀ k : Fin 3, Meets Q.tail k := by
    intro h
    have hgood : Good Q.tail := ⟨htailInfix, h⟩
    have := hmin Q.tail hgood
    simp only [List.length_tail] at this
    omega
  have hdropNot : ¬ ∀ k : Fin 3, Meets Q.dropLast k := by
    intro h
    have hgood : Good Q.dropLast := ⟨hdropInfix, h⟩
    have := hmin Q.dropLast hgood
    simp only [List.length_dropLast] at this
    omega
  obtain ⟨i, hi⟩ := not_forall.mp htailNot
  obtain ⟨j, hj⟩ := not_forall.mp hdropNot
  have hxadj : G.Adj (av i) x := by
    obtain ⟨q, hqQ, hadj⟩ := hQgood.2 i
    have hqx : q = x := by
      by_contra hne
      apply hi
      refine ⟨q, ?_, hadj⟩
      rcases Q with _ | ⟨q₀, T⟩
      · simp at hQlen3
      · simp only [List.tail_cons]
        rcases List.mem_cons.mp hqQ with h | h
        · exact absurd (by simpa [x] using h) hne
        · exact h
    simpa [hqx] using hadj
  have hyadj : G.Adj (av j) y := by
    obtain ⟨q, hqQ, hadj⟩ := hQgood.2 j
    have hqy : q = y := by
      by_contra hne
      apply hj
      refine ⟨q, ?_, hadj⟩
      have hyget : Q.getLast hQpath.1 = y := by
        have := hQfrom.2.2
        rw [List.getLast?_eq_some_getLast hQpath.1] at this
        exact Option.some_injective _ this
      exact (PathBasics.mem_dropLast_iff hQpath.2.1 hQpath.1).mpr
        ⟨hqQ, by simpa [hyget] using hne⟩
    simpa [hqy] using hadj
  have hij : i ≠ j := by
    intro hij
    subst j
    apply hi
    exact ⟨y, last_mem_tail_of_path hQfrom (by omega), hyadj⟩
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ |
      exact ⟨2, by decide, by decide⟩
  obtain ⟨z, hzQ, hzad⟩ := hQgood.2 k
  have hzint : z ∈ interior Q := by
    apply (PathBasics.mem_interior_iff_of_pathFrom hQfrom).mpr
    refine ⟨hzQ, ?_, ?_⟩
    · intro hzx
      apply hcolor z (hQF z hzQ) k i hik
      exact ⟨hzad, hzx ▸ hxadj⟩
    · intro hzy
      apply hcolor z (hQF z hzQ) k j hjk
      exact ⟨hzad, hzy ▸ hyadj⟩
  have haexact : ∀ q ∈ Q, G.Adj (av i) q ↔ q = x := by
    intro q hq
    constructor
    · intro hadj
      by_contra hqx
      apply hi
      refine ⟨q, ?_, hadj⟩
      rcases Q with _ | ⟨q₀, T⟩
      · simp at hQlen3
      · simp only [List.tail_cons]
        rcases List.mem_cons.mp hq with h | h
        · exact absurd (by simpa [x] using h) hqx
        · exact h
    · rintro rfl
      exact hxadj
  have hbexact : ∀ q ∈ Q, G.Adj (av j) q ↔ q = y := by
    intro q hq
    constructor
    · intro hadj
      by_contra hqy
      apply hj
      have hyget : Q.getLast hQpath.1 = y := by
        have := hQfrom.2.2
        rw [List.getLast?_eq_some_getLast hQpath.1] at this
        exact Option.some_injective _ this
      exact ⟨q, (PathBasics.mem_dropLast_iff hQpath.2.1 hQpath.1).mpr
        ⟨hq, by simpa [hyget] using hqy⟩, hadj⟩
    · rintro rfl
      exact hyadj
  have hcx : ¬ G.Adj (av k) x := by
    intro h
    exact hcolor x (hQF x (PathBasics.head_mem hQfrom.2.1)) k i hik ⟨h, hxadj⟩
  have hcy : ¬ G.Adj (av k) y := by
    intro h
    exact hcolor y (hQF y (PathBasics.getLast_mem hQfrom.2.2)) k j hjk ⟨h, hyadj⟩
  have htri : ∀ r s : Fin 3, r ≠ s → G.Adj (av r) (av s) := by
    intro r s hrs
    exact hA.2 _ (havA r) _ (havA s) (fun h => hrs (havinj h))
  have haQ : av i ∉ Q := by
    intro h
    exact (Set.disjoint_left.mp hcatch.2.2.1) (hQF _ h) (havA i)
  have hbQ : av j ∉ Q := by
    intro h
    exact (Set.disjoint_left.mp hcatch.2.2.1) (hQF _ h) (havA j)
  have hcQ : av k ∉ Q := by
    intro h
    exact (Set.disjoint_left.mp hcatch.2.2.1) (hQF _ h) (havA k)
  exact oddWheel_of_three_colored_path G hG.1.1.1.1
    hG.2.1 Q x y (av i) (av j) (av k) hQfrom hQlen3
    (htri i j hij) (htri i k hik.symm) (htri j k hjk.symm)
    haQ hbQ hcQ haexact hbexact ⟨hcx, hcy⟩ ⟨z, hzint, hzad⟩

end Workspace.Types.NoPathMeetsThreeCatchNeighborSets
