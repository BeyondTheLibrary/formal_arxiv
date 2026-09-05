import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.Thm224Claim5LengthTwoExclusion
import Workspace.Statements.S13.Thm_13_6

/-!
# 22.4, claim (5)

PAPER (perfect.pdf, printed pp. 136–137):

> *Since `x_{t+1}` has a neighbour in `A_t`, there is a path `R` from `x_{t+1}` to some
> `Y`-complete vertex `r` in `A_t` with `V(R \ x_{t+1}) ⊆ A_t` such that no vertex of `R \ r` is
> `Y`-complete.*
>
> **(5) `R` has odd length.**
>
> *For certainly `R` has length `≥ 1`; suppose it has length 2, and let its middle vertex be `a`
> say.  There is an antipath joining `x_{t+1}, a` with interior in `Y`, and it is odd since it can
> be completed to an antihole via `a-z-r-x_{t+1}`.  Now `x_{t+1}, a` are not `X_t`-complete (since
> `a ∈ A_t`) and so there is an antipath joining `x_{t+1}, a` with interior in `X_t`, which is
> therefore also odd, since its union with the antipath with interior in `Y` is an antihole.  But
> `y` is `X_t`-complete and nonadjacent to both `x_{t+1}` and `a` (since it has no neighbour in
> `A_t`), and so this antipath can be completed to an odd antihole via `a-y-x_{t+1}`, a
> contradiction.  This proves that `R` does not have length 2.  Hence the path `z-x_{t+1}-R-r`
> does not have length 3; its ends are `Y`-complete and its internal vertices are not, and it has
> length `> 1`, so by 13.6 it has even length, that is, `R` has odd length.  This proves (5).*

Cited: **13.6**, and claim **(4)** (`x_{t+1}` is not `Y`-complete, so `z-x_{t+1}-R-r` really is a
path whose internal vertices are not `Y`-complete).

The path is called `Rp` here because the name `R` is already taken by the tail's remainder list in
the frozen statement of 22.4.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim5

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(5)** *"`R` has odd length."* -/
theorem claim5 {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length)
    (hxt1 : ¬ VertexComplete G (x (t + 1)) Y)
    {Rp : List V} {r : V} (hRp : IsPathFrom G Rp (x (t + 1)) r)
    (hRsub : ∀ v ∈ Rp, v ≠ x (t + 1) → v ∈ wheelSystemA G z A₀ x t)
    (hr : VertexComplete G r Y)
    (hRnc : ∀ v ∈ Rp, v ≠ r → ¬ VertexComplete G v Y) :
    Odd (pathLength Rp) := by
  classical
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨-, -, -, -, -, hzA, hAnoX, -, -, hXanti, -, -, -, hqYy, -, hzXq,
    hzYy, -, -, hAY, -, -, -, -⟩ := hcons
  have hzq : G.Adj z (x (t + 1)) := hzXq _ (Or.inr rfl)
  have hqzne : x (t + 1) ≠ z := hzq.ne.symm
  have hqrne : x (t + 1) ≠ r := by
    intro hqr
    apply hxt1
    rwa [hqr]
  have hrRp : r ∈ Rp := PathBasics.getLast_mem hRp.2.2
  have hrA : r ∈ wheelSystemA G z A₀ x t := hRsub r hrRp hqrne.symm
  have hzr : ¬ G.Adj z r := hzA r hrA
  have hzNotRp : z ∉ Rp := by
    intro hzRp
    have hzA' : z ∈ wheelSystemA G z A₀ x t := hRsub z hzRp hqzne.symm
    exact hAnoX z hzA' (fun w hw => hzXq w (Or.inl hw))
  have hzpath : IsPathFrom G [z] z z := by
    simp [IsPathFrom, IsPathList]
  have hcross : ∀ zz ∈ [z], ∀ w ∈ Rp,
      (G.Adj zz w ↔ (zz = z ∧ w = x (t + 1))) := by
    intro zz hzz w hw
    simp only [List.mem_singleton] at hzz
    subst zz
    constructor
    · intro hzw
      by_cases hwq : w = x (t + 1)
      · exact ⟨rfl, hwq⟩
      · exact (hzA w (hRsub w hw hwq) hzw).elim
    · rintro ⟨-, rfl⟩
      exact hzq
  have hZR : IsPathFrom G (z :: Rp) z r := by
    simpa using PathGlue.glue_path hzpath hRp (by simpa using hzNotRp) hcross
  have hlenZR : pathLength (z :: Rp) = pathLength Rp + 1 := by
    rw [PathBasics.pathLength_cons, PathBasics.length_eq_pathLength_add_one hRp.1]
  have hYanti : AnticonnectedSet G Y :=
    KiteTailBasics.wheel_hub_anticonnected (KiteTailBasics.tail_isWheel hT)
  have hYP : Y ⊆ {v : V | v ∈ z :: Rp}ᶜ := by
    intro w hwY hwP
    simp only [List.mem_cons] at hwP
    rcases hwP with rfl | hwRp
    · exact G.irrefl (hzYy _ (Or.inl hwY))
    · by_cases hwq : w = x (t + 1)
      · subst w
        exact hqYy (Or.inl hwY)
      · exact (Set.disjoint_left.mp hAY) (hRsub w hwRp hwq) hwY
  have hYuniq : ∀ w ∈ z :: Rp, VertexComplete G w Y → w = z ∨ w = r := by
    intro w hwP hwc
    simp only [List.mem_cons] at hwP
    rcases hwP with rfl | hwRp
    · exact Or.inl rfl
    · by_cases hwr : w = r
      · exact Or.inr hwr
      · exact (hRnc w hwRp hwr hwc).elim
  by_contra hnotOdd
  have hevenRp : Even (pathLength Rp) := Nat.not_odd_iff_even.mp hnotOdd
  have hoddZR : Odd (pathLength (z :: Rp)) := by
    rw [hlenZR, Nat.odd_iff]
    have hmod := Nat.even_iff.mp hevenRp
    omega
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1.1
      (z :: Rp) z r hZR hoddZR Y hYP hYanti
      (fun w hw => hzYy w (Or.inl hw)) hr with hedge | hthree
  · obtain ⟨a, haP, b, hbP, hab, haY, hbY⟩ := hedge
    rcases hYuniq a haP haY with rfl | rfl <;>
      rcases hYuniq b hbP hbY with rfl | rfl
    · exact G.irrefl hab
    · exact hzr hab
    · exact hzr hab.symm
    · exact G.irrefl hab
  · obtain ⟨hthree, -⟩ := hthree
    have hnotTwo :=
      Workspace.ProofLemmas.Thm224Claim5LengthTwoExclusion.thm224Claim5LengthTwoExclusion
        hG hopt hT hTshape hA₀ hhub hcon hu hxt1 hRp hRsub hr hRnc
    apply hnotTwo
    omega

end Workspace.ProofLemmas.Thm224Claim5
