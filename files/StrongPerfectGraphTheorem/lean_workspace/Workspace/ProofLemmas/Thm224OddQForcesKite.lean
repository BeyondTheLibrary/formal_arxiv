import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.PathGlueInduced
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S16.Thm_16_1

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

theorem Thm224OddQForcesKite
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u : List V} {Y A₀ : Set V} {z y : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    {un p : V} (hun : u.getLast? = some un)
    {P : List V} (hP : IsPathFrom G P un p)
    (hPsub : ∀ v ∈ P, v ≠ un → v ∈ wheelSystemA G z A₀ x t)
    (hp : VertexComplete G p Y)
    (hPunique : ∀ v ∈ P, v ≠ p → ¬ VertexComplete G v Y)
    (hPpos : 0 < pathLength P) :
    let Q := [z, y] ++ u ++ P.tail
    ¬ Odd (pathLength Q) := by
  classical
  dsimp
  intro hodd
  have hw : IsWheel G C Y := KiteTailBasics.tail_isWheel hT
  have hBerge : Berge G := hG.1.1.1.1.1
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  have hA_two : ∀ v : V, v ∈ wheelSystemA G z A₀ x t →
      ∃ c ∈ wheelSystemA G z A₀ x t, c ≠ v := by
    intro v hv
    by_cases hva : v = a
    · refine ⟨b, hA₀sub hb, ?_⟩
      simpa [hva] using hab.symm
    · exact ⟨a, hA₀sub ha, fun hav => hva hav.symm⟩
  have hanti_not_mem : ∀ v : V,
      VertexAnticomplete G v (wheelSystemA G z A₀ x t) →
      v ∉ wheelSystemA G z A₀ x t := by
    intro v hvanti hvA
    obtain ⟨c, hc, hcv⟩ := hA_two v hvA
    obtain ⟨L, hL, hLmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hvA hc
    have hLpos : 0 < L.length := PathBasics.path_length_pos hL.1
    have hL2 : 2 ≤ L.length := by
      by_contra hlt
      have hL1 : L.length = 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, L = [d] := by
        cases L with
        | nil => simp at hL1
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hL1
      have hdv : d = v := Option.some_injective _ hL.2.1
      have hdc : d = c := Option.some_injective _ hL.2.2
      exact hcv (hdc.symm.trans hdv)
    have hadj := PathBasics.path_adj_succ hL.1 (i := 0) (hi := by omega)
    have hv0 : L[0]'hLpos = v :=
      PathBasics.getElem_zero_of_head? hL.2.1 hLpos
    rw [hv0] at hadj
    exact hvanti _ (hLmem _ (List.getElem_mem (show 1 < L.length by omega))) hadj
  have hyAanti : VertexAnticomplete G y (wheelSystemA G z A₀ x t) := by
    intro v hv
    exact hcon v (Or.inl hv)
  have hzNotA : z ∉ wheelSystemA G z A₀ x t := hanti_not_mem z hzA
  have hyNotA : y ∉ wheelSystemA G z A₀ x t := hanti_not_mem y hyAanti
  have hlast : u.getLast hu.2.1 = un := by
    apply Option.some.inj
    rw [← List.getLast?_eq_some_getLast hu.2.1]
    exact hun
  have hund : u.Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).2
  have hdrop_of_mem_ne {v : V} (hvu : v ∈ u) (hvun : v ≠ un) :
      v ∈ u.dropLast := by
    refine (PathBasics.mem_dropLast_iff hund hu.2.1).mpr ⟨hvu, ?_⟩
    simpa [hlast] using hvun
  have hdropNotA : ∀ v ∈ u.dropLast, v ∉ wheelSystemA G z A₀ x t := by
    intro v hv
    exact hanti_not_mem v (hu.2.2.2.1 v hv)
  have hzuFrom : IsPathFrom G (z :: y :: u) z un := by
    refine ⟨hpath, by simp, ?_⟩
    rw [List.getLast?_cons_of_ne_nil (by simp),
      List.getLast?_cons_of_ne_nil hu.2.1, hun]
  have hQpath : IsPathFrom G ((z :: y :: u) ++ P.tail) z p := by
    refine Workspace.ProofLemmas.PathGlueInduced.isPathList_append_at_end hzuFrom hP ?_ ?_
    · intro v hvzu hvP
      by_cases hvun : v = un
      · exact hvun
      have hvA : v ∈ wheelSystemA G z A₀ x t := hPsub v hvP hvun
      have hvshape : v = z ∨ v = y ∨ v ∈ u := by simpa using hvzu
      rcases hvshape with hvz | hvy | hvu
      · subst v
        exact (hzNotA hvA).elim
      · subst v
        exact (hyNotA hvA).elim
      · exact (hdropNotA v (hdrop_of_mem_ne hvu hvun) hvA).elim
    · intro v hvzu hvneun w hwP hwneun hadj
      have hvAanti : VertexAnticomplete G v (wheelSystemA G z A₀ x t) := by
        have hvshape : v = z ∨ v = y ∨ v ∈ u := by simpa using hvzu
        rcases hvshape with hvz | hvy | hvu
        · subst v
          exact hzA
        · subst v
          exact hyAanti
        · exact hu.2.2.2.1 v (hdrop_of_mem_ne hvu hvneun)
      exact hvAanti w (hPsub w hwP hwneun) hadj
  have hQpath' : IsPathFrom G ([z, y] ++ u ++ P.tail) z p := by
    simpa only [List.cons_append, List.nil_append] using hQpath
  obtain ⟨S, hpre⟩ := hu.1
  obtain ⟨w, hTfrom, hwC, hwz, hw0, hw1⟩ := KiteTailBasics.tail_exists_end hT
  have hznotu : z ∉ u := by
    intro hmem
    exact (List.nodup_cons.mp hpath.2.1).1 (List.mem_cons_of_mem _ hmem)
  have huNotY : ∀ v ∈ u, v ∉ Y := by
    intro v hv hvY
    have hvT : v ∈ T := by
      rw [← hpre]
      simp [hv]
    have hvz : v ≠ z := by
      intro hvz
      subst v
      exact hznotu hv
    by_cases hvw : v = w
    · subst v
      exact (KiteTailBasics.wheel_rim_notMem_hub hw w hwC) hvY
    · exact (KiteTailBasics.tail_interior hT v
        ((PathBasics.mem_interior_iff_of_pathFrom hTfrom).mpr ⟨hvT, hvz, hvw⟩)).1 hvY
  obtain ⟨y', R', hTspec, hRne, hzy, hy0, hy1, hyC, hyz, hyx0, hyx1,
      hyint, hyNotY', hyNC'⟩ := KiteTailBasics.tail_snd_spec hT
  have hyy : y = y' ∧ R = R' := by
    simpa only [List.cons.injEq, true_and] using hTshape.symm.trans hTspec
  have hyNotY : y ∉ Y := by
    rw [hyy.1]
    exact hyNotY'
  have hyNC : ¬ VertexComplete G y Y := by
    rw [hyy.1]
    exact hyNC'
  have hzY : VertexComplete G z Y := fun v hv => hzYy v (Or.inl hv)
  have hzNotY : z ∉ Y := fun hzmem => G.irrefl (hzY z hzmem)
  have hPnotY : ∀ v ∈ P, v ∉ Y := by
    intro v hv hvY
    by_cases hvp : v = p
    · subst v
      exact G.irrefl (hp p hvY)
    by_cases hvun : v = un
    · subst v
      exact huNotY un (PathBasics.getLast_mem hun) hvY
    · exact (Set.disjoint_left.mp hAY (hPsub v hv hvun) hvY)
  have hYoutside : Y ⊆ {v : V | v ∈ ([z, y] ++ u ++ P.tail)}ᶜ := by
    intro v hvY
    change v ∉ ([z, y] ++ u ++ P.tail)
    intro hvQ
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvQ
    rcases hvQ with ((rfl | rfl) | hvu) | hvP
    · exact hzNotY hvY
    · exact hyNotY hvY
    · exact huNotY v hvu hvY
    · exact hPnotY v (List.mem_of_mem_tail hvP) hvY
  have hQComplete : ∀ v ∈ ([z, y] ++ u ++ P.tail),
      VertexComplete G v Y → v = z ∨ v = p := by
    intro v hvQ hvY
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvQ
    rcases hvQ with ((hvz | hvy) | hvu) | hvP
    · exact Or.inl hvz
    · subst v
      exact (hyNC hvY).elim
    · exact (hu.2.2.2.2 v hvu hvY).elim
    · have hvPin : v ∈ P := List.mem_of_mem_tail hvP
      by_cases hvp : v = p
      · exact Or.inr hvp
      · exact (hPunique v hvPin hvp hvY).elim
  have hP2 : 2 ≤ P.length := by
    have hPlen := PathBasics.length_eq_pathLength_add_one hP.1
    omega
  have hQlen3 : 3 ≤ ([z, y] ++ u ++ P.tail).length := by
    have huLen : 0 < u.length := List.length_pos_of_ne_nil hu.2.1
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega
  have hQpos : 0 < ([z, y] ++ u ++ P.tail).length :=
    PathBasics.path_length_pos hQpath'.1
  have hQfirst : ([z, y] ++ u ++ P.tail)[0]'hQpos = z :=
    PathBasics.getElem_zero_of_head? hQpath'.2.1 hQpos
  have hQlast : ([z, y] ++ u ++ P.tail)[([z, y] ++ u ++ P.tail).length - 1]'
      (by omega) = p :=
    PathBasics.getElem_last_of_getLast? hQpath'.2.2 hQpos
  have hzP : ¬ G.Adj z p := by
    have hEnds := PathBasics.path_ends_not_adj hQpath'.1 hQlen3
    rw [hQfirst, hQlast] at hEnds
    exact hEnds
  have hnoedge : ¬ ∃ r ∈ ([z, y] ++ u ++ P.tail), ∃ s ∈ ([z, y] ++ u ++ P.tail),
      EdgeComplete G Y r s := by
    rintro ⟨r, hr, s, hs, hrs⟩
    rcases hQComplete r hr hrs.2.1 with rfl | rfl <;>
      rcases hQComplete s hs hrs.2.2 with rfl | rfl
    · exact G.irrefl hrs.1
    · exact hzP hrs.1
    · exact hzP hrs.1.symm
    · exact G.irrefl hrs.1
  have hQlength : pathLength ([z, y] ++ u ++ P.tail) = 1 + u.length + pathLength P := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_tail, pathLength]
    omega
  have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1.1
    ([z, y] ++ u ++ P.tail) z p hQpath' hodd Y hYoutside
    (KiteTailBasics.wheel_hub_anticonnected hw) hzY hp
  rcases h136 with hedge | ⟨hQ3, c, d, hint, L, hL, hLodd, hLint⟩
  · exact hnoedge hedge
  · have hQarith := hQ3
    rw [hQlength] at hQarith
    have huLen : u.length = 1 := by
      have huPos : 0 < u.length := List.length_pos_of_ne_nil hu.2.1
      omega
    have hPpathLen : pathLength P = 1 := by omega
    have hPlen : P.length = 2 := by
      have hPlen' := PathBasics.length_eq_pathLength_add_one hP.1
      omega
    obtain ⟨un', huEq⟩ := List.length_eq_one_iff.mp huLen
    have hun' : un' = un := by
      have hh := hun
      rw [huEq] at hh
      simpa using hh
    subst un'
    subst u
    obtain ⟨p₀, p₁, hPeq⟩ := PathGlue.length_eq_two hPlen
    have hp₀ : p₀ = un := by
      have hh := hP.2.1
      rw [hPeq] at hh
      simpa using hh
    have hp₁ : p₁ = p := by
      have hh := hP.2.2
      rw [hPeq] at hh
      simpa using hh
    subst p₀
    subst p₁
    subst P
    have hcdlist : [c, d] = [y, un] := by
      simpa [Workspace.Types.Core.SPGT.interior] using hint.symm
    have hcd : c = y ∧ d = un := by
      simpa only [List.cons.injEq, true_and, and_true] using hcdlist
    rcases hcd with ⟨hc, hd⟩
    subst c
    subst d
    have hyun : G.Adj y un := by
      have hstep := PathBasics.path_adj_succ hpath (i := 1) (hi := by simp)
      simpa using hstep
    have hunX : VertexComplete G un (wheelSystemX x t) :=
      (hu.2.2.1 un (by simp)).2
    have hunNC : ¬ VertexComplete G un Y := hu.2.2.2.2 un (by simp)
    have hcover : ∀ w : V, VertexComplete G w Y → G.Adj w y ∨ G.Adj w un := by
      intro w hwY
      by_cases hwy : G.Adj w y
      · exact Or.inl hwy
      by_cases hwun : G.Adj w un
      · exact Or.inr hwun
      have hwney : w ≠ y := by
        rintro rfl
        exact hyNC hwY
      have hwneun : w ≠ un := by
        rintro rfl
        exact hunNC hwY
      have hEven := Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
        hBerge hyun hwY hwy hwun hwney hwneun hL hLint
      exact False.elim ((Nat.not_even_iff_odd.mpr hLodd) hEven)
    have huna : G.Adj un a := by
      rcases hcover a haY with hay | hau
      · exact (hcon a (Or.inl (hA₀sub ha)) hay.symm).elim
      · exact hau.symm
    have hunb : G.Adj un b := by
      rcases hcover b hbY with hby | hbu
      · exact (hcon b (Or.inl (hA₀sub hb)) hby.symm).elim
      · exact hbu.symm
    have hun0 : G.Adj un (x 0) :=
      hunX (x 0) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    have hun1 : G.Adj un (x 1) :=
      hunX (x 1) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    have hunT : un ∈ T := by
      rw [← hpre]
      simp
    have hunz : un ≠ z := by
      intro huz
      have hzmem : z ∈ y :: [un] := by simp [huz]
      exact (List.nodup_cons.mp hpath.2.1).1 hzmem
    obtain ⟨hun0avoid, hun1avoid⟩ := KiteTailBasics.tail_avoids hT un hunT
    have hunNotC : un ∉ C := by
      intro hunC
      have hunA₀ : un ∈ A₀ := by
        rw [hA₀]
        simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or]
        exact ⟨hunC, hunz, hun0avoid, hun1avoid⟩
      exact hAnoX un (hA₀sub hunA₀) hunX
    have hunNotY : un ∉ Y := huNotY un (by simp)
    have haOutside : a ∉ ({x 0, z, x 1} : Set V) := by
      have h := ha
      rw [hA₀] at h
      intro hmem
      apply h.2
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc,
        or_left_comm, or_comm] using hmem
    have hbOutside : b ∉ ({x 0, z, x 1} : Set V) := by
      have h := hb
      rw [hA₀] at h
      intro hmem
      apply h.2
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc,
        or_left_comm, or_comm] using hmem
    have hnb := KiteTailBasics.tail_rimNeighbours hT
    have ha0 : a ≠ x 0 := fun h => haOutside (by simp [h])
    have ha1 : a ≠ x 1 := fun h => haOutside (by simp [h])
    have hb0 : b ≠ x 0 := fun h => hbOutside (by simp [h])
    have hb1 : b ≠ x 1 := fun h => hbOutside (by simp [h])
    have hfixed4 : ({x 0, x 1, a, b} : Set V).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hnb.1, ha0.symm, hb0.symm]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [hab]) (Set.toFinite _), Set.ncard_singleton]
    have hfixedNbr : ∀ e : V, e ∈ ({x 0, x 1, a, b} : Set V) →
        e ∈ C ∧ G.Adj un e := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with he | he | he | he
      · subst e
        exact ⟨hnb.2.1, hun0⟩
      · subst e
        exact ⟨hnb.2.2.1, hun1⟩
      · subst e
        exact ⟨haC, huna⟩
      · subst e
        exact ⟨hbC, hunb⟩
    have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
    have hopp : OppositeWheelParity G C Y a b :=
      ⟨hab, haC, hbC,
        OddWheelParityFacts.not_sameWheelParity_of_edgeComplete
          (KiteTailBasics.wheel_isHoleList hw) heven haC hbC ⟨habAdj, haY, hbY⟩⟩
    have h16 := _root_.Workspace.Statements.S16.SPGT.thm_16_1 G hG.1.1 C Y hw un
      hunNotC hunNotY hunNC a b huna hunb hopp
    rcases h16.2 with htwo | hthree | hwplus
    · obtain ⟨r, s, hrs, hset, hrsadj, hrY, hsY⟩ := htwo
      have hsub : ({x 0, x 1, a, b} : Set V) ⊆ ({r, s} : Set V) := by
        intro e he
        obtain ⟨heC, headj⟩ := hfixedNbr e he
        rw [← hset]
        exact ⟨heC, headj⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have htwoCard : ({r, s} : Set V).ncard = 2 := Set.ncard_pair hrs
      rw [hfixed4, htwoCard] at hle
      omega
    · obtain ⟨p₁, p₂, p₃, hp123, harc, hp₁, hp₂, hp₃, hother⟩ := hthree
      have hp₁parts := Workspace.ProofLemmas.OddWheelSpan.vertexComplete_union.mp hp₁
      have hp₂parts := Workspace.ProofLemmas.OddWheelSpan.vertexComplete_union.mp hp₂
      have hp₃parts := Workspace.ProofLemmas.OddWheelSpan.vertexComplete_union.mp hp₃
      have hfourth : ∃ e : V, e ∈ ({x 0, x 1, a, b} : Set V) ∧
          e ≠ p₁ ∧ e ≠ p₂ ∧ e ≠ p₃ := by
        by_contra hbad
        push Not at hbad
        have hsub : ({x 0, x 1, a, b} : Set V) ⊆ ({p₁, p₂, p₃} : Set V) := by
          intro e he
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          by_cases he1 : e = p₁
          · exact Or.inl he1
          by_cases he2 : e = p₂
          · exact Or.inr (Or.inl he2)
          · exact Or.inr (Or.inr (hbad e he he1 he2))
        have hthreeCard : ({p₁, p₂, p₃} : Set V).ncard ≤ 3 := by
          refine le_trans (Set.ncard_insert_le _ _) ?_
          have h := Set.ncard_insert_le p₂ ({p₃} : Set V)
          rw [Set.ncard_singleton] at h
          omega
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hfixed4] at hle
        omega
      obtain ⟨e, he, he1, he2, he3⟩ := hfourth
      obtain ⟨heC, headj⟩ := hfixedNbr e he
      rcases harc with ⟨k, hk | hk⟩
      · exact hnokite ⟨un,
          KiteTailBasics.isKite_of_triple_and_fourth hw hunNotY hunNotC hunNC
            ⟨k, hk⟩ hp₁parts.2.symm hp₂parts.2.symm hp₃parts.2.symm
            hp₁parts.1 hp₂parts.1 hp₃parts.1 heC headj he1 he2 he3⟩
      · exact hnokite ⟨un,
          KiteTailBasics.isKite_of_triple_and_fourth hw hunNotY hunNotC hunNC
            ⟨k, hk⟩ hp₃parts.2.symm hp₂parts.2.symm hp₁parts.2.symm
            hp₃parts.1 hp₂parts.1 hp₁parts.1 heC headj he3 he2 he1⟩
    · exact (KiteTailBasics.no_wheel_hub_union_singleton hopt hunNotY) ⟨C, hwplus⟩

end Workspace.ProofLemmas
