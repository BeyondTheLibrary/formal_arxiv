import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Pseudowheels
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.Thm224Claim1
import Workspace.ProofLemmas.PathGlueInduced
import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.Statements.S02.Thm_2_11

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(4)** *"`x_{t+1}` is not `Y`-complete."* -/
theorem claim4 {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length)
    (hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v) :
    ¬ VertexComplete G (x (t + 1)) Y := by
  classical
  intro hqY
  let A := wheelSystemA G z A₀ x t
  let X := wheelSystemX x t
  let q := x (t + 1)
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  let un := u.getLast hu.2.1
  have hun : u.getLast? = some un := List.getLast?_eq_some_getLast hu.2.1
  have hunmem : un ∈ u := Workspace.ProofLemmas.PathBasics.getLast_mem hun
  have hunopt : un ∈ u.getLast? := by simp [hun]
  have hundata := hu.2.2.1 un hunopt
  let B : Set V := {w | VertexComplete G w Y}
  have hunY : un ∉ B := by
    simpa [B] using hu.2.2.2.2 un hunmem
  have hAB : (A ∩ B).Nonempty := ⟨a, hA₀sub ha, by simpa [B] using haY⟩
  obtain ⟨p, ⟨hpA, hpY⟩, P, hP, hPpos, hPsub, hPunique⟩ :=
    Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet
      G A B un hAconn hundata.1 hAB hunY
  have hPunion : ∀ w ∈ P, w ∈ (A ∪ {un} : Set V) := by
    intro w hw
    by_cases hwu : w = un
    · exact Or.inr (by simpa [hwu])
    · exact Or.inl (hPsub w hw hwu)
  have hPnc : ∀ w ∈ P, w ≠ p → ¬ VertexComplete G w Y := by
    intro w hw hwp hwY
    exact hwp ((hPunique w hw).mp (by simpa [B] using hwY))
  have hPodd : Odd (pathLength P) :=
    Workspace.ProofLemmas.Thm224Claim1.claim1
      hG hopt hT hTshape hA₀ hhub hcon hu hun hP hPunion
      (by simpa [B] using hpY) hPnc
  have hw : IsWheel G C Y :=
    Workspace.ProofLemmas.KiteTailBasics.tail_isWheel hT
  have hBerge : Berge G := hG.1.1.1.1.1
  have hYne : Y.Nonempty :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_nonempty hw
  have hYanti : AnticonnectedSet G Y :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_anticonnected hw
  have hA_two : ∀ v : V, v ∈ A → ∃ c ∈ A, c ≠ v := by
    intro v hv
    by_cases hva : v = a
    · exact ⟨b, hA₀sub hb, by simpa [hva] using hab.symm⟩
    · exact ⟨a, hA₀sub ha, fun hav => hva hav.symm⟩
  have hanti_not_mem : ∀ v : V, VertexAnticomplete G v A → v ∉ A := by
    intro v hvanti hvA
    obtain ⟨c, hc, hcv⟩ := hA_two v hvA
    obtain ⟨L, hL, hLmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hvA hc
    have hLpos : 0 < L.length := Workspace.ProofLemmas.PathBasics.path_length_pos hL.1
    have hLtwo : 2 ≤ L.length := by
      by_contra hlt
      have hLone : L.length = 1 := by omega
      obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hLone
      have hdv : d = v := Option.some_injective _ hL.2.1
      have hdc : d = c := Option.some_injective _ hL.2.2
      exact hcv (hdc.symm.trans hdv)
    have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hL.1 (i := 0) (by omega)
    have hzero : L[0]'hLpos = v :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hL.2.1 hLpos
    rw [hzero] at hadj
    exact hvanti _ (hLmem _ (List.getElem_mem (show 1 < L.length by omega))) hadj
  have hyAanti : VertexAnticomplete G y A := by
    intro v hv
    exact hcon v (Or.inl hv)
  have hzNotA : z ∉ A := hanti_not_mem z hzA
  have hyNotA : y ∉ A := hanti_not_mem y hyAanti
  have hlast : u.getLast hu.2.1 = un := by
    apply Option.some.inj
    rw [← List.getLast?_eq_some_getLast hu.2.1]
  have hund : u.Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).2
  have hdrop_of_mem_ne {v : V} (hvu : v ∈ u) (hvun : v ≠ un) : v ∈ u.dropLast := by
    refine (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hund hu.2.1).mpr ⟨hvu, ?_⟩
    simpa [hlast] using hvun
  have hdropNotA : ∀ v ∈ u.dropLast, v ∉ A := by
    intro v hv
    exact hanti_not_mem v (hu.2.2.2.1 v hv)
  have hzneun : z ≠ un := by
    intro h
    have hzmemu : z ∈ u := by rw [h]; exact hunmem
    exact (List.nodup_cons.mp hpath.2.1).1 (List.mem_cons_of_mem y hzmemu)
  have hzPanti : VertexAnticomplete G z {v : V | v ∈ P} := by
    intro v hv
    by_cases hvun : v = un
    · subst v
      exact hzu un hunmem
    · exact hzA v (hPsub v hv hvun)
  have hzuFrom : IsPathFrom G (z :: y :: u) z un := by
    refine ⟨hpath, by simp, ?_⟩
    rw [List.getLast?_cons_of_ne_nil (by simp),
      List.getLast?_cons_of_ne_nil hu.2.1, hun]
  let Q : List V := [z, y] ++ u ++ P.tail
  have hQpath : IsPathFrom G Q z p := by
    have hglue : IsPathFrom G ((z :: y :: u) ++ P.tail) z p := by
      refine Workspace.ProofLemmas.PathGlueInduced.isPathList_append_at_end hzuFrom hP ?_ ?_
      · intro v hvzu hvP
        by_cases hvun : v = un
        · exact hvun
        have hvA : v ∈ A := hPsub v hvP hvun
        have hvshape : v = z ∨ v = y ∨ v ∈ u := by simpa using hvzu
        rcases hvshape with hvz | hvy | hvu
        · subst v
          exact (hzNotA hvA).elim
        · subst v
          exact (hyNotA hvA).elim
        · exact (hdropNotA v (hdrop_of_mem_ne hvu hvun) hvA).elim
      · intro v hvzu hvneun w hwP hwneun hadj
        have hvAanti : VertexAnticomplete G v A := by
          have hvshape : v = z ∨ v = y ∨ v ∈ u := by simpa using hvzu
          rcases hvshape with hvz | hvy | hvu
          · subst v
            exact hzA
          · subst v
            exact hyAanti
          · exact hu.2.2.2.1 v (hdrop_of_mem_ne hvu hvneun)
        exact hvAanti w (hPsub w hwP hwneun) hadj
    simpa only [Q, List.cons_append, List.nil_append] using hglue
  obtain ⟨S, hpre⟩ := hu.1
  obtain ⟨wlast, hTfrom, hwlastC, hwlastz, hwlast0, hwlast1⟩ :=
    Workspace.ProofLemmas.KiteTailBasics.tail_exists_end hT
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
    by_cases hvw : v = wlast
    · subst v
      exact (Workspace.ProofLemmas.KiteTailBasics.wheel_rim_notMem_hub hw wlast hwlastC) hvY
    · exact (Workspace.ProofLemmas.KiteTailBasics.tail_interior hT v
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hTfrom).mpr
          ⟨hvT, hvz, hvw⟩)).1 hvY
  obtain ⟨y', R', hTspec, hRne, hzy, hy0, hy1, hyC, hyz, hyx0, hyx1,
      hyint, hyNotY', hyNC'⟩ := Workspace.ProofLemmas.KiteTailBasics.tail_snd_spec hT
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
      exact G.irrefl (hpY p hvY)
    by_cases hvun : v = un
    · subst v
      exact huNotY un hunmem hvY
    · exact (Set.disjoint_left.mp hAY (hPsub v hv hvun) hvY)
  have hQNotY : ∀ v ∈ Q, v ∉ Y := by
    intro v hvQ hvY
    simp only [Q, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvQ
    rcases hvQ with ((rfl | rfl) | hvu) | hvP
    · exact hzNotY hvY
    · exact hyNotY hvY
    · exact huNotY v hvu hvY
    · exact hPnotY v (List.mem_of_mem_tail hvP) hvY
  have hzNotXq : z ∉ X ∪ {q} := fun hzmem => G.irrefl (hzXq z hzmem)
  have hyNotXq : y ∉ X ∪ {q} := by
    rintro (hyXmem | hyq)
    · exact G.irrefl (hyX y hyXmem)
    · rw [Set.mem_singleton_iff] at hyq
      exact hqYy (Or.inr hyq.symm)
  have hQNotXq : ∀ v ∈ Q, v ∉ X ∪ {q} := by
    intro v hvQ hvXq
    simp only [Q, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvQ
    rcases hvQ with ((rfl | rfl) | hvu) | hvP
    · exact hzNotXq hvXq
    · exact hyNotXq hvXq
    · exact hzu v hvu (hzXq v hvXq)
    · exact hzPanti v (List.mem_of_mem_tail hvP) (hzXq v hvXq)
  have hXqYdisj : Disjoint (X ∪ {q}) Y := by
    rw [Set.disjoint_left]
    intro v hvXq hvY
    rcases hvXq with hvX | hvq
    · exact G.irrefl (hXY v hvX v hvY)
    · rw [Set.mem_singleton_iff] at hvq
      subst v
      exact hqYy (Or.inl hvY)
  have hXqY : Complete G (X ∪ {q}) Y := by
    intro v hvXq w hwY
    rcases hvXq with hvX | hvq
    · exact hXY v hvX w hwY
    · rw [Set.mem_singleton_iff] at hvq
      subst v
      exact hqY w hwY
  have hYXq : Complete G Y (X ∪ {q}) := by
    intro v hvY w hwXq
    exact (hXqY w hwXq v hvY).symm
  have hYunique : ∀ v ∈ Q, (VertexComplete G v Y ↔ v = z ∨ v = p) := by
    intro v hvQ
    constructor
    · intro hvY
      simp only [Q, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvQ
      rcases hvQ with ((hvz | hvy) | hvu) | hvP
      · exact Or.inl hvz
      · subst v
        exact (hyNC hvY).elim
      · exact (hu.2.2.2.2 v hvu hvY).elim
      · have hvPin : v ∈ P := List.mem_of_mem_tail hvP
        by_cases hvp : v = p
        · exact Or.inr hvp
        · exact (hPnc v hvPin hvp hvY).elim
    · rintro (rfl | rfl)
      · exact hzY
      · exact hpY
  have hpNotXq : ¬ VertexComplete G p (X ∪ {q}) := by
    intro hpXq
    exact hAnoX p hpA (fun v hv => hpXq v (Or.inl hv))
  have hyNotCompleteXq : ¬ VertexComplete G y (X ∪ {q}) := by
    intro hyXq
    exact hcon q (Or.inr rfl) (hyXq q (Or.inr rfl))
  have hPtwo : 2 ≤ P.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hPpos
    omega
  have hQlen5 : 5 ≤ Q.length := by
    have huPos : 0 < u.length := List.length_pos_of_ne_nil hu.2.1
    have huTwo : 2 ≤ u.length := by
      obtain ⟨i, hi⟩ := hlen
      omega
    simp only [Q, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega
  have hQsecond : Q.tail.head? = some y := by
    simp [Q]
  have hQoutsideYXq : ∀ v ∈ Q, v ∉ Y ∧ v ∉ X ∪ {q} := by
    exact fun v hv => ⟨hQNotY v hv, hQNotXq v hv⟩
  have hXqunique : ∀ v ∈ Q, (VertexComplete G v (X ∪ {q}) ↔ v = z) :=
    Workspace.ProofLemmas.PseudowheelBuilder.unique_vertexComplete_of_no_pseudowheel
      hG.2.1 (Disjoint.symm hXqYdisj) hYne hXqne hYanti hXqanti hYXq
      hQpath hQsecond hQoutsideYXq hQlen5 hYunique (by simp [Q]) hzXq
      hyNotCompleteXq hpNotXq
  have hQlength : pathLength Q = 1 + u.length + pathLength P := by
    simp only [Q, List.length_append, List.length_cons, List.length_nil,
      List.length_tail, pathLength]
    omega
  have hQeven : Even (pathLength Q) := by
    obtain ⟨i, hi⟩ := hlen
    obtain ⟨j, hj⟩ := hPodd
    refine ⟨i + j + 1, ?_⟩
    rw [hQlength]
    omega
  have hQlength4 : 4 ≤ pathLength Q := by
    have hlenEq := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hQpath.1
    omega
  have h211 := _root_.Workspace.Statements.S02.SPGT.thm_2_11 G hBerge (X ∪ {q}) Y
    hXqYdisj hXqne hYne hXqanti hYanti hXqY Q z p hQpath.1
    (fun v hv hmem => hmem.elim (hQNotXq v hv) (hQNotY v hv))
    hQeven hQlength4 hQpath.2.1 hQpath.2.2 hXqunique hYunique
  rcases h211 with ⟨r, hrXq, hno⟩ | ⟨x₁, hx₁, x₂, hx₂, hx₁x₂, hL⟩
  · rcases hrXq with hrX | hrq
    · have hyQtail : y ∈ Q.tail := by simp [Q]
      exact hno y hyQtail (hyX r hrX).symm
    · rw [Set.mem_singleton_iff] at hrq
      subst r
      obtain ⟨v, hvdrop, hqv⟩ := hadj
      have hvu : v ∈ u := List.dropLast_subset _ hvdrop
      have hvQtail : v ∈ Q.tail := by simp [Q, hvu]
      exact hno v hvQtail hqv
  · let L : List V := x₁ :: (Q.tail ++ [x₂])
    have hLpath : IsPathList G L := by simpa [L] using hL
    have hQpos : 0 < Q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hQpath.1
    have hLlen : L.length = Q.length + 1 := by
      simp only [L, List.length_cons, List.length_append, List.length_tail,
        List.length_singleton, List.length_nil]
      omega
    have hx₁y : G.Adj x₁ y := by
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hLpath (i := 0) (by omega)
      simpa [L, Q] using hadj
    have hx₁neq : x₁ ≠ q := by
      intro heq
      subst x₁
      exact hcon q (Or.inr rfl) hx₁y.symm
    have hx₁X : x₁ ∈ X := by
      rcases hx₁ with hx | hx
      · exact hx
      · exact (hx₁neq (Set.mem_singleton_iff.mp hx)).elim
    have hLone : L[1]'(by omega) = y := by simp [L, Q]
    have hLlast : L[L.length - 1]'(by omega) = x₂ := by
      apply Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
      simp only [L]
      rw [List.getLast?_cons_of_ne_nil (by simp),
        List.getLast?_append_of_ne_nil _ (by simp : [x₂] ≠ [])]
      rfl
      exact Workspace.ProofLemmas.PathBasics.path_length_pos hLpath
    have hx₂notX : x₂ ∉ X := by
      intro hx₂X
      have hadjL : G.Adj (L[1]'(by omega)) (L[L.length - 1]'(by omega)) := by
        rw [hLone, hLlast]
        exact hyX x₂ hx₂X
      have hidx := (Workspace.ProofLemmas.PathBasics.path_adj_iff hLpath
        (i := 1) (j := L.length - 1) (by omega) (by omega)).mp hadjL
      rcases hidx with hidx | hidx <;> omega
    have hx₂q : x₂ = q := by
      rcases hx₂ with hx | hx
      · exact (hx₂notX hx).elim
      · exact Set.mem_singleton_iff.mp hx
    subst x₂
    obtain ⟨v, hvdrop, hqv⟩ := hadj
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hvdrop
    simp only [List.length_dropLast] at hj
    have hjU : j < u.length := by omega
    have hjvU : u[j]'hjU = v := by
      simpa only [List.getElem_dropLast] using hjv
    have hQu : Q[j + 2]'(by
        simp only [Q, List.length_append, List.length_cons, List.length_nil,
          List.length_tail]
        omega) = v := by
      simp only [Q]
      rw [List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp)]
      simpa using hjvU
    have hjQtail : j + 1 < Q.tail.length := by
      simp only [Q, List.length_tail, List.length_append, List.length_cons, List.length_nil]
      omega
    have hLv : L[j + 2]'(by
        rw [hLlen]
        simp only [Q, List.length_append, List.length_cons, List.length_nil,
          List.length_tail]
        omega) = v := by
      simp only [L]
      rw [List.getElem_cons_succ, List.getElem_append_left hjQtail,
        List.getElem_tail]
      exact hQu
    have hLq : L[L.length - 1]'(by omega) = q := by
      apply Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
      simp only [L]
      rw [List.getLast?_cons_of_ne_nil (by simp),
        List.getLast?_append_of_ne_nil _ (by simp : [q] ≠ [])]
      rfl
      exact Workspace.ProofLemmas.PathBasics.path_length_pos hLpath
    have hQlenExact : Q.length = 2 + u.length + P.tail.length := by
      simp only [Q, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    have hLlenExact : L.length = 3 + u.length + P.tail.length := by omega
    have hjL : j + 2 < L.length := by omega
    have hadjL : G.Adj (L[j + 2]'hjL) (L[L.length - 1]'(by omega)) := by
      rw [hLv, hLq]
      exact hqv.symm
    have hidx := (Workspace.ProofLemmas.PathBasics.path_adj_iff hLpath
      (i := j + 2) (j := L.length - 1) hjL (by omega)).mp hadjL
    have hPtailpos : 0 < P.tail.length := by simp; omega
    rcases hidx with hidx | hidx <;> rw [hLlenExact] at hidx <;> omega

end Workspace.ProofLemmas.Thm224Claim4
