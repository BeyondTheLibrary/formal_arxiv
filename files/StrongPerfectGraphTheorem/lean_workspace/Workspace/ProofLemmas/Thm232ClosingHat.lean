import Workspace.ProofLemmas.Thm192Claim7GapReflection

/-! The triangle-catching contradiction for the hat in 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingHat

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “the only neighbour of `x₀` in `F ∪ A₀` is its
neighbour in `S`, say `s`; the only neighbour of `z` in `F ∪ A₀` is `y`; and `s,y`
are nonadjacent, and both nonadjacent to `y₀`, contrary to 17.1.” -/
theorem hat_absurd {G : SimpleGraph V} (hG : InF7 G)
    {C D : List V} (hC : IsHoleList G C) (hC6 : 6 ≤ C.length)
    {z p y s : V} {B Y : Set V}
    (hzC : z ∈ C) (hpC : p ∈ C) (hsC : s ∈ C)
    (hBconn : ConnectedSet G B)
    (hBdisj : ∀ w ∈ B, w ≠ z ∧ w ≠ p ∧ w ∉ Y)
    (hyB : y ∈ B) (hsB : s ∈ B) (hyD : y ∈ D) (hsD : s ∈ D)
    (hzy : G.Adj z y) (hps : G.Adj p s) (hys : y ≠ s)
    (hzuniq : ∀ w ∈ B, G.Adj z w → w = y)
    (hpunique : ∀ w ∈ B, G.Adj p w → w = s)
    (hYattach : ∀ h ∈ Y, ∃ w ∈ B, G.Adj h w)
    {h : V} (hhY : h ∈ Y) (hhat : IsHatForHole G D z p h) : False := by
  have hzp := hhat.2.2.2.1
  have hhz := hhat.2.2.2.2.1
  have hhp := hhat.2.2.2.2.2.1
  have htri : IsTriangle G ({z,p,h} : Set V) := by
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_insert_of_notMem (by simp [hzp.ne, hhz.ne']), Set.ncard_pair hhp.ne']
    · intro a ha b hb hab
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
      all_goals rw [ha, hb]
      all_goals first
        | exact hzp | exact hzp.symm | exact hhz | exact hhz.symm
        | exact hhp | exact hhp.symm | exact (hab (ha.trans hb.symm)).elim
  have hcatch : Catches G B ({z,p,h} : Set V) := by
    refine ⟨htri, hBconn, Set.disjoint_left.mpr ?_, ?_⟩
    · intro w hw hwt
      rcases hwt with he | he | he
      · exact (hBdisj w hw).1 he
      · exact (hBdisj w hw).2.1 he
      · exact (hBdisj w hw).2.2 (he ▸ hhY)
    · intro w hw
      rcases hw with he | he | he
      · exact he ▸ ⟨y, hyB, hzy⟩
      · exact he ▸ ⟨s, hsB, hps⟩
      · exact he ▸ hYattach h hhY
  have hnoR := Thm192Claim7GapReflection.no_reflection hG.1 hC
    (by change 4 < C.length; omega) hzC hpC hsC hzp.ne
    (hBdisj s hsB).1.symm hps.ne hpunique (y := h)
  have hcontact := Thm192Claim7GapReflection.catches_forces_contact hG hcatch
    hzuniq hpunique hys hnoR
  rcases hcontact with hhy | hhs
  · exact hhat.2.2.2.2.2.2 y hyD (hBdisj y hyB).1 (hBdisj y hyB).2.1 hhy
  · exact hhat.2.2.2.2.2.2 s hsD (hBdisj s hsB).1 (hBdisj s hsB).2.1 hhs

end Workspace.ProofLemmas.Thm232ClosingHat
