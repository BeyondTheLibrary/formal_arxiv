import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_9

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(1)** *"`P` is odd."* -/
theorem claim1 {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u)
    {un p : V} (hun : u.getLast? = some un)
    {P : List V} (hP : IsPathFrom G P un p)
    (hPsub : ∀ v ∈ P, v ∈ (wheelSystemA G z A₀ x t ∪ {un} : Set V))
    (hp : VertexComplete G p Y)
    (hPnc : ∀ v ∈ P, v ≠ p → ¬ VertexComplete G v Y) :
    Odd (pathLength P) := by
  classical
  let A := wheelSystemA G z A₀ x t
  let X := wheelSystemX x t
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  have hunmem : un ∈ u := Workspace.ProofLemmas.PathBasics.getLast_mem hun
  have hunopt : un ∈ u.getLast? := by simp [hun]
  have hunX : VertexComplete G un X := (hu.2.2.1 un hunopt).2
  have hunY : ¬ VertexComplete G un Y := hu.2.2.2.2 un hunmem
  have hzneun : z ≠ un := by
    intro h
    have hzmemu : z ∈ u := by rw [h]; exact hunmem
    exact (List.nodup_cons.mp hpath.2.1).1 (List.mem_cons_of_mem y hzmemu)
  have hBerge : Berge G := hG.1.1.1.1.1
  have hYne : Y.Nonempty :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_nonempty
      (Workspace.ProofLemmas.KiteTailBasics.optimalWheel_isWheel hopt)
  have hYanti : AnticonnectedSet G Y :=
    Workspace.ProofLemmas.KiteTailBasics.wheel_hub_anticonnected
      (Workspace.ProofLemmas.KiteTailBasics.optimalWheel_isWheel hopt)
  have hzX : VertexComplete G z X := fun w hw => hzXq w (Or.inl hw)
  have hzY : VertexComplete G z Y := fun w hw => hzYy w (Or.inl hw)
  have hXYdisj : Disjoint X Y := by
    rw [Set.disjoint_left]
    intro v hvX hvY
    exact G.irrefl (hXY v hvX v hvY)
  have hunp : un ≠ p := by
    intro h
    subst p
    exact hunY hp
  have hzNotA : z ∉ A := by
    intro hzA'
    obtain ⟨c, hc⟩ := hframe.1
    have hcA : c ∈ A := hA₀sub hc
    have hcz : c ≠ z := by
      intro h
      apply hframe.2.2.1
      rw [← h]
      exact hc
    obtain ⟨Q, hQ, hQmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hzA' hcA
    have hQpos : 0 < Q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hQ.1
    have hQtwo : 2 ≤ Q.length := by
      by_contra hlt
      have hQone : Q.length = 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, Q = [d] := by
        cases Q with
        | nil => simp at hQone
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hQone
      have hdz : d = z := Option.some_injective _ hQ.2.1
      have hdc : d = c := Option.some_injective _ hQ.2.2
      exact hcz (hdc.symm.trans hdz)
    have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1 (i := 0) (hi := by omega)
    have hQzero : Q[0]'hQpos = z :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
    rw [hQzero] at hadj
    exact hzA _ (hQmem _ (List.getElem_mem (show 1 < Q.length by omega))) hadj
  have hzP : VertexAnticomplete G z {v : V | v ∈ P} := by
    intro v hv
    rcases hPsub v hv with hvA | hvun
    · exact hzA v hvA
    · have hvun' : v = un := Set.mem_singleton_iff.mp hvun
      subst v
      exact hzu un hunmem
  have hPpos : 0 < pathLength P := by
    have hPllen : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
    have hPtwo : 2 ≤ P.length := by
      by_contra hlt
      have hPone : P.length = 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, P = [d] := by
        cases P with
        | nil => simp at hPone
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hPone
      have hdun : d = un := Option.some_injective _ hP.2.1
      have hdp : d = p := Option.some_injective _ hP.2.2
      exact hunp (hdun.symm.trans hdp)
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
    omega
  have hPXY : ∀ v ∈ P, v ∉ X ∪ Y := by
    intro v hv hvXY
    rcases hvXY with hvX | hvY
    · exact hzP v hv (hzX v hvX)
    · exact hzP v hv (hzY v hvY)
  have hXuniq : ∀ v ∈ P, (VertexComplete G v X ↔ v = un) := by
    intro v hv
    constructor
    · intro hvX
      rcases hPsub v hv with hvA | hvun
      · exact (hAnoX v hvA hvX).elim
      · simpa only [Set.mem_singleton_iff] using hvun
    · intro hvun
      subst v
      exact hunX
  have hYuniq : ∀ v ∈ P, (VertexComplete G v Y ↔ v = p) := by
    intro v hv
    constructor
    · intro hvY
      by_contra hvnp
      exact hPnc v hv hvnp hvY
    · intro hvp
      subst v
      exact hp
  have hzNotX : z ∉ X := fun hz => G.irrefl (hzX z hz)
  have hzNotY : z ∉ Y := fun hz => G.irrefl (hzY z hz)
  have hzNotPdropUn : z ∉ ({v : V | v ∈ P} \ {un}) := by
    intro hz
    rcases hPsub z hz.1 with hzA' | hzun
    · exact hzNotA hzA'
    · exact hz.2 hzun
  have hzNotPdropP : z ∉ ({v : V | v ∈ P} \ {p}) := by
    intro hz
    rcases hPsub z hz.1 with hzA' | hzun
    · exact hzNotA hzA'
    · exact hzneun (Set.mem_singleton_iff.mp hzun)
  have hdisjX : Disjoint ({v : V | v ∈ P} \ {un}) X := by
    rw [Set.disjoint_left]
    intro v hv hvX
    exact hPXY v hv.1 (Or.inl hvX)
  have hdisjY : Disjoint ({v : V | v ∈ P} \ {p}) Y := by
    rw [Set.disjoint_left]
    intro v hv hvY
    exact hPXY v hv.1 (Or.inr hvY)
  have hbalX : Balanced G ({v : V | v ∈ P} \ {un}) X :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
      ({v : V | v ∈ P} \ {un}) X hdisjX z
      (by rintro (hz | hz); exact hzNotPdropUn hz; exact hzNotX hz)
      hzX (fun v hv => hzP v hv.1)
  have hbalY : Balanced G ({v : V | v ∈ P} \ {p}) Y :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
      ({v : V | v ∈ P} \ {p}) Y hdisjY z
      (by rintro (hz | hz); exact hzNotPdropP hz; exact hzNotY hz)
      hzY (fun v hv => hzP v hv.1)
  by_contra hodd
  have heven : Even (pathLength P) := Nat.not_odd_iff_even.mp hodd
  have h29 := _root_.Workspace.Statements.S02.SPGT.thm_2_9 G hBerge X Y
    hXYdisj hXne hYne hXanti hYanti hXY P un p hP.1 hPXY heven hPpos hP.2.1 hP.2.2
    hXuniq hYuniq
  rcases h29.2 with hbadX | hbadY
  · exact hbadX hbalX
  · exact hbadY hbalY

end Workspace.ProofLemmas.Thm224Claim1
