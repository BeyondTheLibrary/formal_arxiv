import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.Thm224Claim4
import Workspace.ProofLemmas.Thm224Claim5
import Workspace.ProofLemmas.Thm224Claim6
import Workspace.ProofLemmas.PathGlueInduced
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_7

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim7Reduction

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

private theorem pathLength_one_of_ends_adj
    {V : Type*} {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hab : G.Adj a b) :
    pathLength P = 1 := by
  have hpos : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have h0 : P[0]'hpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hpos
  have hn : P[P.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  have hidx := (Workspace.ProofLemmas.PathBasics.path_adj_iff hP.1 hpos
    (show P.length - 1 < P.length by omega)).mp (by simpa [h0, hn] using hab)
  rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
  omega

/-- If an induced path starts outside an induced list and otherwise stays in that
list, then an interior occurrence of the list's first vertex must be adjacent to
the new start.  This is the small path-geometric step used in claim (7). -/
private theorem start_adj_head_of_internal
    {V : Type*} {G : SimpleGraph V} {U S : List V} {q s w : V}
    (hU : IsPathList G U) (hS : IsPathFrom G S q s)
    (hwhead : U.head? = some w) (hwS : w ∈ S)
    (hwq : w ≠ q) (hws : w ≠ s)
    (hsub : ∀ v ∈ S, v = q ∨ v ∈ U) :
    G.Adj q w := by
  classical
  obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwS
  have hSpos : 0 < S.length := Workspace.ProofLemmas.PathBasics.path_length_pos hS.1
  have hS0 : S[0]'hSpos = q :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hS.2.1 hSpos
  have hSn : S[S.length - 1]'(by omega) = s :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hS.2.2 hSpos
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    apply hwq
    exact hiw.symm.trans hS0
  have hin : i ≠ S.length - 1 := by
    intro h
    apply hws
    exact hiw.symm.trans (by simpa [h] using hSn)
  have him : i - 1 < S.length := by omega
  have hip : i + 1 < S.length := by omega
  let p := S[i - 1]'him
  let n := S[i + 1]'hip
  have hpw : G.Adj p w := by
    have := Workspace.ProofLemmas.PathBasics.path_adj_succ hS.1
      (i := i - 1) (by omega)
    have helem : S[i - 1 + 1]'(by omega) = w :=
      (getElem_congr rfl (show i - 1 + 1 = i by omega) (by omega)).trans hiw
    simpa only [p, helem] using this
  have hwn : G.Adj w n := by
    have := Workspace.ProofLemmas.PathBasics.path_adj_succ hS.1 (i := i) (by omega)
    simpa [n, hiw] using this
  by_contra hqw
  have hpU : p ∈ U := by
    rcases hsub p (List.getElem_mem him) with hpq | hpU
    · exact (hqw (hpq ▸ hpw)).elim
    · exact hpU
  have hnU : n ∈ U := by
    rcases hsub n (List.getElem_mem hip) with hnq | hnU
    · exact (hqw ((hnq ▸ hwn).symm)).elim
    · exact hnU
  have hUne : U ≠ [] := by
    intro h
    rw [h] at hwhead
    simp at hwhead
  have hUpos : 0 < U.length := List.length_pos_of_ne_nil hUne
  have hU0 : U[0]'hUpos = w :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hwhead hUpos
  obtain ⟨j, hj, hjp⟩ := List.mem_iff_getElem.mp hpU
  obtain ⟨k, hk, hkn⟩ := List.mem_iff_getElem.mp hnU
  have hj1 : j = 1 := by
    have hadj : G.Adj (U[0]'hUpos) (U[j]'hj) := by
      simpa [hU0, hjp] using hpw.symm
    have := (Workspace.ProofLemmas.PathBasics.path_adj_iff hU hUpos hj).mp hadj
    omega
  have hk1 : k = 1 := by
    have hadj : G.Adj (U[0]'hUpos) (U[k]'hk) := by simpa [hU0, hkn] using hwn
    have := (Workspace.ProofLemmas.PathBasics.path_adj_iff hU hUpos hk).mp hadj
    omega
  have hpn : p = n := by
    subst j
    subst k
    exact hjp.symm.trans hkn
  exact (Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hS.1 him hip (by omega)) hpn

theorem thm224Claim7Reduction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u : List V} {Y A₀ : Set V} {z y : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hlen : Even u.length)
    (hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v)
    (hXcomplete : ∃ v ∈ u.dropLast, VertexComplete G v (wheelSystemX x t)) :
    ∃ s ∈ u.dropLast,
      ∃ r ∈ wheelSystemA G z A₀ x t,
        ∃ a ∈ A₀, ∃ b ∈ A₀,
          a ≠ b ∧ a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧
          VertexComplete G a Y ∧ VertexComplete G b Y ∧
          ∃ S Rp LY : List V,
            IsPathFrom G S (x (t + 1)) s ∧
            pathLength S = 1 ∧
            IsPathFrom G Rp (x (t + 1)) r ∧
            pathLength Rp = 1 ∧
            IsAntipathFrom G LY s (x (t + 1)) ∧
            (∀ w ∈ interior LY, w ∈ Y) ∧
            Odd (pathLength LY) ∧
            ¬ VertexComplete G (x (t + 1)) Y ∧
            VertexComplete G s (wheelSystemX x t) ∧
            VertexComplete G r Y ∧
            (∀ w : V, VertexComplete G w Y →
              G.Adj w s ∨ G.Adj w (x (t + 1))) ∧
            G.Adj (x (t + 1)) a ∧
            G.Adj (x (t + 1)) b ∧
            G.Adj (x (t + 1)) z := by
  classical
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  have hw : IsWheel G C Y :=
    Workspace.ProofLemmas.KiteTailBasics.tail_isWheel hT
  have hYne : Y.Nonempty :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_nonempty hw
  have hYanti : AnticonnectedSet G Y :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_anticonnected hw
  have hBerge : Berge G := hG.1.1.1.1.1
  have hqY : ¬ VertexComplete G (x (t + 1)) Y :=
    Workspace.ProofLemmas.Thm224Claim4.claim4
      hG hopt hT hTshape hA₀ hhub hcon hu hlen hadj

  -- The first `Y`-complete vertex reached from `x_{t+1}` through `A_t`.
  let BY : Set V := {w : V | VertexComplete G w Y}
  have hABY : (wheelSystemA G z A₀ x t ∩ BY).Nonempty :=
    ⟨a, hA₀sub ha, by simpa [BY] using haY⟩
  obtain ⟨r, ⟨hrA, hrBY⟩, Rp, hRp, hRppos, hRpsub, hRpunique⟩ :=
    Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet
      G (wheelSystemA G z A₀ x t) BY (x (t + 1)) hAconn
        (hxNbr (t + 1) (by omega)) hABY (by simpa [BY] using hqY)
  have hrY : VertexComplete G r Y := by simpa [BY] using hrBY
  have hRpnc : ∀ w ∈ Rp, w ≠ r → ¬ VertexComplete G w Y := by
    intro w hwRp hwr hwY
    exact hwr ((hRpunique w hwRp).mp (by simpa [BY] using hwY))
  have hRpodd : Odd (pathLength Rp) :=
    Workspace.ProofLemmas.Thm224Claim5.claim5
      hG hopt hT hTshape hA₀ hhub hcon hu hlen hqY hRp hRpsub hrY hRpnc

  -- The first `X_t`-complete vertex reached through `u.dropLast`.
  have huPath : IsPathList G u := by
    have h := Workspace.ProofLemmas.PathBasics.isPathList_drop hpath (k := 2)
      (by
        have hupos : 0 < u.length := List.length_pos_of_ne_nil hu.2.1
        simp only [List.length_cons]
        omega)
    simpa using h
  have hdropne : u.dropLast ≠ [] := by
    obtain ⟨v, hv, -⟩ := hadj
    intro he
    rw [he] at hv
    simp at hv
  have hdroppos : 0 < u.length - 1 := by
    have := List.length_pos_of_ne_nil hdropne
    simpa only [List.length_dropLast] using this
  have hdropPath : IsPathList G u.dropLast := by
    simpa only [List.dropLast_eq_take] using
      (Workspace.ProofLemmas.PathBasics.isPathList_take huPath hdroppos)
  have hdropConn : ConnectedSet G {v : V | v ∈ u.dropLast} :=
    Workspace.ProofLemmas.KiteTailBasics.connectedSet_of_isPathList hdropPath
  let BX : Set V := {w : V | VertexComplete G w (wheelSystemX x t)}
  have hdropBX : ({v : V | v ∈ u.dropLast} ∩ BX).Nonempty := by
    obtain ⟨v, hv, hvX⟩ := hXcomplete
    exact ⟨v, hv, by simpa [BX] using hvX⟩
  obtain ⟨s, ⟨hsdrop, hsBX⟩, S, hS, hSpos, hSsub, hSunique⟩ :=
    Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet
      G {v : V | v ∈ u.dropLast} BX (x (t + 1)) hdropConn hadj hdropBX
        (by simpa [BX] using hqXnc)
  have hsX : VertexComplete G s (wheelSystemX x t) := by simpa [BX] using hsBX
  have hSall : ∀ w ∈ S, w = x (t + 1) ∨ w ∈ u.dropLast := by
    intro w hwS
    by_cases hwq : w = x (t + 1)
    · exact Or.inl hwq
    · exact Or.inr (hSsub w hwS hwq)
  have hSuniqX : ∀ w ∈ S,
      VertexComplete G w (wheelSystemX x t) → w = s := by
    intro w hwS hwX
    exact (hSunique w hwS).mp (by simpa [BX] using hwX)

  -- `S` is odd.  Otherwise 2.2 applied to `z-x_{t+1}-S-s` forces `y`
  -- to see the first vertex of `u`, and claim (6) contradicts the choice of `s`.
  have hSodd : Odd (pathLength S) := by
    by_contra hnotOdd
    have hSeven : Even (pathLength S) := Nat.not_odd_iff_even.mp hnotOdd
    have hzq : G.Adj z (x (t + 1)) := hzXq _ (Or.inr rfl)
    have hznotu : z ∉ u := by
      intro hzu'
      exact (List.nodup_cons.mp hpath.2.1).1 (List.mem_cons_of_mem y hzu')
    have hznotS : z ∉ S := by
      intro hzS
      rcases hSall z hzS with hzqeq | hzu'
      · exact G.irrefl (hzqeq ▸ hzq)
      · exact hznotu (List.mem_of_mem_dropLast hzu')
    have hzsingleton : IsPathFrom G [z] z z := by
      simp [IsPathFrom, IsPathList]
    have hcross : ∀ zz ∈ [z], ∀ w ∈ S,
        (G.Adj zz w ↔ (zz = z ∧ w = x (t + 1))) := by
      intro zz hzz w hwS
      simp only [List.mem_singleton] at hzz
      subst zz
      constructor
      · intro hzw
        rcases hSall w hwS with rfl | hwu
        · exact ⟨rfl, rfl⟩
        · exact (hzu w (List.mem_of_mem_dropLast hwu) hzw).elim
      · rintro ⟨-, rfl⟩
        exact hzq
    have hzSpath : IsPathFrom G (z :: S) z s := by
      simpa using Workspace.ProofLemmas.PathGlue.glue_path hzsingleton hS
        (by simpa using hznotS) hcross
    have hzSodd : Odd (pathLength (z :: S)) := by
      have hSlen : 2 ≤ S.length := by
        have := Workspace.ProofLemmas.PathBasics.pathLength_eq S
        omega
      have hlenEq : pathLength (z :: S) = pathLength S + 1 := by
        simp only [pathLength, List.length_cons]
        omega
      rw [hlenEq, Nat.odd_iff]
      rw [Nat.even_iff] at hSeven
      omega
    have hznotX : z ∉ wheelSystemX x t := by
      intro hzX
      exact G.irrefl (hzXq z (Or.inl hzX))
    have hzSoutside : ∀ w ∈ z :: S, w ∉ wheelSystemX x t := by
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hwS
      · exact hznotX
      · rcases hSall w hwS with rfl | hwu
        · exact hqX
        · intro hwX
          exact hzu w (List.mem_of_mem_dropLast hwu) (hzXq w (Or.inl hwX))
    have hcompleteEnds : ∀ w ∈ z :: S,
        VertexComplete G w (wheelSystemX x t) → w = z ∨ w = s := by
      intro w hw hwX
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hwS
      · exact Or.inl rfl
      · exact Or.inr (hSuniqX w hwS hwX)
    have hzs : ¬ G.Adj z s := hzu s (List.mem_of_mem_dropLast hsdrop)
    have hnoedge : ¬ ∃ v ∈ z :: S, ∃ w ∈ z :: S,
        EdgeComplete G (wheelSystemX x t) v w := by
      rintro ⟨v, hv, w, hw', hvw, hvX, hwX⟩
      rcases hcompleteEnds v hv hvX with rfl | rfl <;>
        rcases hcompleteEnds w hw' hwX with rfl | rfl
      · exact G.irrefl hvw
      · exact hzs hvw
      · exact hzs hvw.symm
      · exact G.irrefl hvw
    obtain ⟨w, hwint, hyw⟩ :=
      _root_.Workspace.Statements.S02.SPGT.thm_2_2
        G hBerge (wheelSystemX x t) hXanti (z :: S) z s hzSpath hzSoutside
          hzSodd (fun v hv => hzXq v (Or.inl hv)) hsX hnoedge y hyX
    have hwdata :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hzSpath).mp hwint
    have hwS : w ∈ S := by
      rcases List.mem_cons.mp hwdata.1 with hwz | hwS
      · exact (hwdata.2.1 hwz).elim
      · exact hwS
    have hwneS : w ≠ s := hwdata.2.2
    rcases hSall w hwS with hwq | hwU
    · exact hcon (x (t + 1)) (Or.inr rfl) (hwq ▸ hyw)
    · have hwhead : u.head? = some w :=
        (hyu w (List.mem_of_mem_dropLast hwU)).mp hyw
      have hwneq : w ≠ x (t + 1) := by
        intro he
        exact hcon (x (t + 1)) (Or.inr rfl) (he ▸ hyw)
      have hqw : G.Adj (x (t + 1)) w :=
        start_adj_head_of_internal huPath hS hwhead hwS hwneq hwneS
          (fun v hv => (hSall v hv).imp_right List.mem_of_mem_dropLast)
      have hwX := Workspace.ProofLemmas.Thm224Claim6.claim6
        hG hopt hT hTshape hA₀ hhub hcon hu hlen w (by simpa [hwhead]) hqw
      exact hwneS (hSuniqX w hwS hwX)

  -- A vertex anticomplete to the connected, nontrivial set `A_t` cannot lie in it.
  have hA_two : ∀ v : V, v ∈ wheelSystemA G z A₀ x t →
      ∃ c ∈ wheelSystemA G z A₀ x t, c ≠ v := by
    intro v hv
    by_cases hva : v = a
    · exact ⟨b, hA₀sub hb, by simpa [hva] using hab.symm⟩
    · exact ⟨a, hA₀sub ha, fun hav => hva hav.symm⟩
  have hanti_not_mem : ∀ v : V,
      VertexAnticomplete G v (wheelSystemA G z A₀ x t) →
      v ∉ wheelSystemA G z A₀ x t := by
    intro v hvanti hvA
    obtain ⟨c, hc, hcv⟩ := hA_two v hvA
    obtain ⟨L, hL, hLmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hvA hc
    have hLtwo : 2 ≤ L.length := by
      have hLpos := Workspace.ProofLemmas.PathBasics.path_length_pos hL.1
      by_contra hlt
      have hLone : L.length = 1 := by omega
      obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hLone
      have hdv : d = v := by simpa using hL.2.1
      have hdc : d = c := by simpa using hL.2.2
      exact hcv (hdc.symm.trans hdv)
    have hfirst := Workspace.ProofLemmas.PathBasics.path_adj_succ hL.1
      (i := 0) (by omega)
    have hzero : L[0]'(by omega) = v :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hL.2.1 (by omega)
    rw [hzero] at hfirst
    exact hvanti _ (hLmem _ (List.getElem_mem (show 1 < L.length by omega))) hfirst
  have hdropNotA : ∀ v ∈ u.dropLast, v ∉ wheelSystemA G z A₀ x t := by
    intro v hv
    exact hanti_not_mem v (hu.2.2.2.1 v hv)
  have hqNotA : x (t + 1) ∉ wheelSystemA G z A₀ x t := by
    intro hqA
    exact hzA _ hqA (hzXq _ (Or.inr rfl))

  -- Splice `S` and `Rp` at their common end `x_{t+1}`.
  let P := S.reverse ++ Rp.tail
  have hP : IsPathFrom G P s r := by
    have hmeet : ∀ w, w ∈ S.reverse → w ∈ Rp → w = x (t + 1) := by
      intro w hwS hwRp
      have hwS' : w ∈ S := List.mem_reverse.mp hwS
      by_cases hwq : w = x (t + 1)
      · exact hwq
      · exact (hdropNotA w (hSsub w hwS' hwq) (hRpsub w hwRp hwq)).elim
    have hanti : ∀ v ∈ S.reverse, v ≠ x (t + 1) →
        ∀ w ∈ Rp, w ≠ x (t + 1) → ¬ G.Adj v w := by
      intro v hvS hvq w hwRp hwq
      exact hu.2.2.2.1 v (hSsub v (List.mem_reverse.mp hvS) hvq) w
        (hRpsub w hwRp hwq)
    exact Workspace.ProofLemmas.PathGlueInduced.isPathList_append_at_end
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hS) hRp hmeet hanti
  have hPlen : pathLength P = pathLength S + pathLength Rp := by
    have hSlen : 2 ≤ S.length := by
      have := Workspace.ProofLemmas.PathBasics.pathLength_eq S
      omega
    have hRplen : 2 ≤ Rp.length := by
      have := Workspace.ProofLemmas.PathBasics.pathLength_eq Rp
      omega
    simp only [P, pathLength, List.length_append, List.length_reverse, List.length_tail]
    omega
  have hPeven : Even (pathLength P) := by
    rw [hPlen, Nat.even_iff]
    rw [Nat.odd_iff] at hSodd hRpodd
    omega
  have hPpos : 0 < pathLength P := by rw [hPlen]; omega
  have hXYdisj : Disjoint (wheelSystemX x t) Y := by
    rw [Set.disjoint_left]
    intro v hvX hvY
    exact G.irrefl (hXY v hvX v hvY)
  have hPuniqX : ∀ w ∈ P,
      (VertexComplete G w (wheelSystemX x t) ↔ w = s) := by
    intro w hwP
    constructor
    · intro hwX
      rcases List.mem_append.mp hwP with hwS | hwRp
      · exact hSuniqX w (List.mem_reverse.mp hwS) hwX
      · have hwRp' : w ∈ Rp := List.mem_of_mem_tail hwRp
        by_cases hwq : w = x (t + 1)
        · exact (hqXnc (hwq ▸ hwX)).elim
        · exact (hAnoX w (hRpsub w hwRp' hwq) hwX).elim
    · rintro rfl
      exact hsX
  have hPuniqY : ∀ w ∈ P, (VertexComplete G w Y ↔ w = r) := by
    intro w hwP
    constructor
    · intro hwY
      rcases List.mem_append.mp hwP with hwS | hwRp
      · have hwS' := List.mem_reverse.mp hwS
        rcases hSall w hwS' with hwq | hwU
        · exact (hqY (hwq ▸ hwY)).elim
        · exact (hu.2.2.2.2 w (List.mem_of_mem_dropLast hwU) hwY).elim
      · exact (hRpunique w (List.mem_of_mem_tail hwRp)).mp (by simpa [BY] using hwY)
    · rintro rfl
      exact hrY
  obtain ⟨hPtwo, c, hPshape, QX, LY, hQX, hLY, hxor⟩ :=
    _root_.Workspace.Statements.S13.SPGT.thm_13_7
      G hG.1.1.1 (wheelSystemX x t) Y hXYdisj hXne hYne hXanti hYanti hXY
        P s r hP.1 hPeven hPpos hP.2.1 hP.2.2 hPuniqX hPuniqY
  have hqP : x (t + 1) ∈ P := by
    apply List.mem_append_left
    exact List.mem_reverse.mpr
      (Workspace.ProofLemmas.PathBasics.head_mem hS.2.1)
  have hqneS : x (t + 1) ≠ s := by
    intro he
    exact hqXnc (he ▸ hsX)
  have hqneR : x (t + 1) ≠ r := by
    intro he
    exact hqY (he ▸ hrY)
  have hqc : x (t + 1) = c := by
    rw [hPshape] at hqP
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hqP
    rcases hqP with h | h | h
    · exact (hqneS h).elim
    · exact h
    · exact (hqneR h).elim
  subst c
  have hP' : IsPathFrom G [s, x (t + 1), r] s r := hPshape ▸ hP
  have hsq : G.Adj s (x (t + 1)) := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hP'.1
      (i := 0) (by simp)
    simpa using h
  have hqr : G.Adj (x (t + 1)) r := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hP'.1
      (i := 1) (by simp)
    simpa using h
  have hSlen : pathLength S = 1 :=
    pathLength_one_of_ends_adj hS hsq.symm
  have hRplen : pathLength Rp = 1 :=
    pathLength_one_of_ends_adj hRp hqr

  -- The `X_t`-antipath cannot be odd: `y` closes it to an antihole.
  have hyq : ¬ G.Adj y (x (t + 1)) := hcon _ (Or.inr rfl)
  have hyr : ¬ G.Adj y r := hcon _ (Or.inl hrA)
  have hyneQ : y ≠ x (t + 1) := by
    intro he
    exact hqYy (by rw [← he]; exact Or.inr rfl)
  have hyNotA : y ∉ wheelSystemA G z A₀ x t :=
    hanti_not_mem y (fun v hv => hcon v (Or.inl hv))
  have hyneR : y ≠ r := by
    intro he
    exact hyNotA (he ▸ hrA)
  have hQeven : Even (pathLength QX) :=
    Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
      hBerge hqr hyX hyq hyr hyneQ hyneR hQX.1 hQX.2
  have hLYodd : Odd (pathLength LY) := by
    rcases hxor with ⟨hQodd, -⟩ | ⟨hLYodd, -⟩
    · exact ((Nat.not_even_iff_odd.mpr hQodd) hQeven).elim
    · exact hLYodd
  have hcover : ∀ w : V, VertexComplete G w Y →
      G.Adj w s ∨ G.Adj w (x (t + 1)) := by
    intro w hwY
    by_contra hnone
    push_neg at hnone
    have hwneS : w ≠ s := by
      intro he
      exact hu.2.2.2.2 s (List.mem_of_mem_dropLast hsdrop) (he ▸ hwY)
    have hwneQ : w ≠ x (t + 1) := by
      intro he
      exact hqY (he ▸ hwY)
    have hLYeven : Even (pathLength LY) :=
      Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
        hBerge hsq hwY hnone.1 hnone.2 hwneS hwneQ hLY.1 hLY.2
    exact (Nat.not_even_iff_odd.mpr hLYodd) hLYeven
  have hqa : G.Adj (x (t + 1)) a := by
    rcases hcover a haY with has | haq
    · exact (hu.2.2.2.1 s hsdrop a (hA₀sub ha) has.symm).elim
    · exact haq.symm
  have hqb : G.Adj (x (t + 1)) b := by
    rcases hcover b hbY with hbs | hbq
    · exact (hu.2.2.2.1 s hsdrop b (hA₀sub hb) hbs.symm).elim
    · exact hbq.symm
  exact ⟨s, hsdrop, r, hrA, a, ha, b, hb, hab, haC, hbC, habAdj,
    haY, hbY, S, Rp, LY, hS, hSlen, hRp, hRplen, hLY.1, hLY.2,
    hLYodd, hqY, hsX, hrY, hcover, hqa, hqb, (hzXq _ (Or.inr rfl)).symm⟩

end Workspace.ProofLemmas.Thm224Claim7Reduction
