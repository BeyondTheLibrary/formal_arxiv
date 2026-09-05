import Workspace.ProofLemmas.Thm95OffspringGapReach
import Workspace.ProofLemmas.Thm95OffspringGapHole

/-!
# `Mⱼ` is complete to `Nⱼ`

PAPER (9.5(1), printed p. 52): *"Since there is no `Tⱼ`-antirung with both ends in `Mⱼ` or both
ends in `Nⱼ`, it follows that `Mⱼ ∩ Nⱼ = ∅`, and there are no nonedges between `Mⱼ` and `Nⱼ`
except possibly between `Mⱼ ∩ Xⱼ` and `Nⱼ ∩ Xⱼ`, or between `Mⱼ ∩ Yⱼ` and `Nⱼ ∩ Yⱼ`.  Suppose
there is such a nonedge; and choose `Tⱼ`-antirungs `xⱼ-Qⱼ-yⱼ`, `x'ⱼ-Q'ⱼ-y'ⱼ` where `xⱼ ∈ U` is
nonadjacent to `x'ⱼ ∈ V`, say.  Now `xⱼ, x'ⱼ` have a common neighbour `d₁ ∈ A₁ ∪ B₁`, and then
`d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁` is an odd hole.  This proves that `Mⱼ` is complete to `Nⱼ`."*

Take a nonedge between `u ∈ Mⱼ` and `v ∈ Nⱼ`, and let `xⱼ-Qⱼ-yⱼ` be an antirung through `u`
with `xⱼ ∈ U` and `x'ⱼ-Q'ⱼ-y'ⱼ` one through `v` with `x'ⱼ ∈ V`.  By the paper's *"every
`Tⱼ`-antirung has one end in `U` and the other in `V`"*, `yⱼ ∈ V` and `y'ⱼ ∈ U`.  Each of `u`
and `v` lies in `Xⱼ`, `Yⱼ` or `Zⱼ`.

* If both lie in `Xⱼ` then `u = xⱼ` and `v = x'ⱼ`, and the displayed odd hole applies.
* If both lie in `Yⱼ` then `u = yⱼ` and `v = y'ⱼ`, and the same hole applies with the roles of
  `f₁` and `f_k` exchanged.
* In every other case the nonedge can be routed: `u` reaches one end of `Qⱼ` and `v` an end of
  `Q'ⱼ` through `Zⱼ`, and the two ends can be chosen one in `Xⱼ` and one in `Yⱼ` and both in
  `U`, or both in `V`.  Gluing along the nonedge produces a `Tⱼ`-antirung between them
  (`Thm95OffspringGapReach.exists_srung_of_reach`), which the quoted sentence forbids.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95OffspringGapComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs
open Workspace.ProofLemmas.Thm95OffspringGapReach

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(1), p. 52):** *"`xⱼ, x'ⱼ` have a common neighbour `d₁ ∈ A₁ ∪ B₁`"*.  Two
vertices of `Xⱼ`, or two vertices of `Yⱼ`, have a common neighbour on any strip of the
striation: one of the two ends of that strip is complete to `Xⱼ ∪ Zⱼ` and the other to
`Yⱼ ∪ Zⱼ`, whichever way round the strip and the antistrip are parallel. -/
theorem exists_common_neighbour {G : SimpleGraph V} {Sx Tx : Set V × Set V × Set V}
    (hS : IsStrip G Sx) (hpc : ParallelStripAntistrip G Sx Tx ∨ CoParallel G Sx Tx)
    {p q : V} (hpos : (p ∈ Tx.1 ∧ q ∈ Tx.1) ∨ (p ∈ Tx.2.2 ∧ q ∈ Tx.2.2)) :
    ∃ d ∈ stripVertices Sx, G.Adj d p ∧ G.Adj d q := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  obtain ⟨a, ha⟩ := hS.2.2.2.1
  obtain ⟨b, hb⟩ := hS.2.2.2.2.1
  have hA : a ∈ stripVertices (A, C, B) := Or.inl (Or.inl ha)
  have hB : b ∈ stripVertices (A, C, B) := Or.inl (Or.inr hb)
  rcases hpos with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rcases hpc with h | h
    · exact ⟨a, hA, h.1.1 a ha p (Or.inl hp), h.1.1 a ha q (Or.inl hq)⟩
    · exact ⟨b, hB, h.1.2 b hb p (Or.inl hp), h.1.2 b hb q (Or.inl hq)⟩
  · rcases hpc with h | h
    · exact ⟨b, hB, h.1.2 b hb p (Or.inl hp), h.1.2 b hb q (Or.inl hq)⟩
    · exact ⟨a, hA, h.1.1 a ha p (Or.inl hp), h.1.1 a ha q (Or.inl hq)⟩

/-- **PAPER (9.5(1), p. 52):** *"This proves that `Mⱼ` is complete to `Nⱼ`."*  `hsplit` is the
paper's *"every `Tⱼ`-antirung has one end in `U` and the other in `V`"*, and `hcomm` is its
*"`xⱼ, x'ⱼ` have a common neighbour `d₁ ∈ A₁ ∪ B₁`"*. -/
theorem offVerts_complete_aux {G : SimpleGraph V} (hG : Berge G)
    {Tx : Set V × Set V × Set V} (hTx : IsAntistrip G Tx)
    {R : List V} {r s : V} (hR : IsPathFrom G R r s) (hodd : Odd (pathLength R))
    (hsplit : ∀ (Q : List V) (x y : V), IsSRung Gᶜ Tx Q → IsPathFrom Gᶜ Q x y →
      (G.Adj r x ∧ G.Adj s y) ∨ (G.Adj s x ∧ G.Adj r y))
    (hXY : ∀ z ∈ Tx.1 ∪ Tx.2.2, ¬ (G.Adj r z ∧ G.Adj s z))
    (hout : ∀ z ∈ stripVertices Tx, z ∉ R)
    (hintanti : ∀ z ∈ stripVertices Tx, ∀ w ∈ SPGT.interior R, ¬ G.Adj z w)
    (hcomm : ∀ p q : V, ((p ∈ Tx.1 ∧ q ∈ Tx.1) ∨ (p ∈ Tx.2.2 ∧ q ∈ Tx.2.2)) →
      ∃ d : V, G.Adj d p ∧ G.Adj d q ∧ d ∉ R ∧ ∀ w ∈ R, ¬ G.Adj d w) :
    Complete G (offVerts G Tx {z : V | G.Adj r z}) (offVerts G Tx {z : V | G.Adj s z}) := by
  classical
  -- Componentwise bookkeeping about the antistrip.
  have hloc : ∀ w, w ∈ stripVertices Tx → w ∈ Tx.1 ∨ w ∈ Tx.2.2 ∨ w ∈ Tx.2.1 := by
    obtain ⟨X, Z, Y⟩ := Tx
    rintro w ((h | h) | h)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
  have hdXY : ∀ w, w ∈ Tx.1 → w ∉ Tx.2.2 := by
    obtain ⟨X, Z, Y⟩ := Tx; exact fun w hw => Set.disjoint_left.mp hTx.1 hw
  have hdXZ : ∀ w, w ∈ Tx.1 → w ∉ Tx.2.1 := by
    obtain ⟨X, Z, Y⟩ := Tx; exact fun w hw => Set.disjoint_left.mp hTx.2.1 hw
  have hdYZ : ∀ w, w ∈ Tx.2.2 → w ∉ Tx.2.1 := by
    obtain ⟨X, Z, Y⟩ := Tx; exact fun w hw => Set.disjoint_left.mp hTx.2.2.1 hw
  have hXsub : Tx.1 ⊆ stripVertices Tx := by
    obtain ⟨X, Z, Y⟩ := Tx; exact fun z hz => Or.inl (Or.inl hz)
  have hYsub : Tx.2.2 ⊆ stripVertices Tx := by
    obtain ⟨X, Z, Y⟩ := Tx; exact fun z hz => Or.inl (Or.inr hz)
  intro u hu v hv
  by_contra hno
  -- The antirung through `u`, with its end in `Xⱼ` adjacent to `f₁`.
  obtain ⟨Q, hQ, huQ, x₁, hx₁h, hrx₁⟩ := hu
  obtain ⟨a, b, hpath, haX, hbY⟩ := Thm95OffspringSplit.rung_ends Tx Q hQ
  have hax : a = x₁ := Option.some.inj (hpath.2.1.symm.trans hx₁h)
  subst hax
  have hsa : ¬ G.Adj s a := fun h => hXY a (Or.inl haX) ⟨hrx₁, h⟩
  have hsb : G.Adj s b := by
    rcases hsplit Q a b hQ hpath with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hsa
  have hrb : ¬ G.Adj r b := fun h => hXY b (Or.inr hbY) ⟨h, hsb⟩
  -- The antirung through `v`, with its end in `Xⱼ` adjacent to `f_k`.
  obtain ⟨Q', hQ', hvQ', x₂, hx₂h, hsx₂⟩ := hv
  obtain ⟨a', b', hpath', haX', hbY'⟩ := Thm95OffspringSplit.rung_ends Tx Q' hQ'
  have hax' : a' = x₂ := Option.some.inj (hpath'.2.1.symm.trans hx₂h)
  subst hax'
  have hra' : ¬ G.Adj r a' := fun h => hXY a' (Or.inl haX') ⟨h, hsx₂⟩
  have hrb' : G.Adj r b' := by
    rcases hsplit Q' a' b' hQ' hpath' with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hra'
    · exact h
  have hsb' : ¬ G.Adj s b' := fun h => hXY b' (Or.inr hbY') ⟨hrb', h⟩
  -- Where `u` and `v` sit on their antirungs.
  have huV : u ∈ stripVertices Tx := mem_stripVertices_of_mem_srung hQ huQ
  have hvV : v ∈ stripVertices Tx := mem_stripVertices_of_mem_srung hQ' hvQ'
  have huX : u ∈ Tx.1 → u = a := by
    intro h
    exact Option.some.inj ((head_of_mem_X hTx hQ huQ h).symm.trans hpath.2.1)
  have huY : u ∈ Tx.2.2 → u = b := by
    intro h
    exact Option.some.inj ((last_of_mem_Y hTx hQ huQ h).symm.trans hpath.2.2)
  have hvX : v ∈ Tx.1 → v = a' := by
    intro h
    exact Option.some.inj ((head_of_mem_X hTx hQ' hvQ' h).symm.trans hpath'.2.1)
  have hvY : v ∈ Tx.2.2 → v = b' := by
    intro h
    exact Option.some.inj ((last_of_mem_Y hTx hQ' hvQ' h).symm.trans hpath'.2.2)
  -- The paper's odd hole, in the form used twice below.
  have hole : ∀ p q : V, p ∈ stripVertices Tx → q ∈ stripVertices Tx →
      G.Adj r p → ¬ G.Adj s p → G.Adj s q → ¬ G.Adj r q → ¬ G.Adj p q →
      ((p ∈ Tx.1 ∧ q ∈ Tx.1) ∨ (p ∈ Tx.2.2 ∧ q ∈ Tx.2.2)) → False := by
    intro p q hpV hqV hrp hsp hsq hrq hpq hpos
    obtain ⟨d, hdp, hdq, hdR, hdnone⟩ := hcomm p q hpos
    exact Thm95OffspringGapHole.no_nonedge_with_common_neighbour hG hR hodd hrp hsp hsq hrq
      hpq hdp hdq (hout p hpV) (hout q hqV) hdR (hintanti p hpV) (hintanti q hqV) hdnone
  -- The routed antirung, in the form used in every remaining case.
  have route : ∀ p q : V, p ∈ Tx.1 → q ∈ Tx.2.2 →
      ReachThroughZ G Tx.2.1 u p → ReachThroughZ G Tx.2.1 v q → ¬ G.Adj u v →
      (G.Adj r p ∧ G.Adj s q) ∨ (G.Adj s p ∧ G.Adj r q) := by
    intro p q hp hq hup hvq hnadj
    obtain ⟨P, hP, hPfrom⟩ := exists_srung_of_reach hTx hp hq hup hvq hnadj
    exact hsplit P p q hP hPfrom
  have route' : ∀ p q : V, p ∈ Tx.1 → q ∈ Tx.2.2 →
      ReachThroughZ G Tx.2.1 v p → ReachThroughZ G Tx.2.1 u q → ¬ G.Adj v u →
      (G.Adj r p ∧ G.Adj s q) ∨ (G.Adj s p ∧ G.Adj r q) := by
    intro p q hp hq hvp huq hnadj
    obtain ⟨P, hP, hPfrom⟩ := exists_srung_of_reach hTx hp hq hvp huq hnadj
    exact hsplit P p q hP hPfrom
  rcases hloc u huV with hu1 | hu2 | hu3
  · -- `u ∈ Xⱼ`, so `u = xⱼ ∈ U`.
    have hux : u = a := huX hu1
    have hru : G.Adj r u := by rw [hux]; exact hrx₁
    have hsu : ¬ G.Adj s u := by rw [hux]; exact hsa
    have hune : u ≠ b := fun h => hdXY u hu1 (h ▸ hbY)
    rcases hloc v hvV with hv1 | hv2 | hv3
    · -- both in `Xⱼ`: the displayed odd hole.
      have hvx : v = a' := hvX hv1
      have hsv : G.Adj s v := by rw [hvx]; exact hsx₂
      have hrv : ¬ G.Adj r v := by rw [hvx]; exact hra'
      exact hole u v huV hvV hru hsu hsv hrv hno (Or.inl ⟨hu1, hv1⟩)
    · -- `v ∈ Yⱼ`: route from `xⱼ ∈ U` to `y'ⱼ ∈ U`.
      have hvne : v ≠ a' := fun h => hdXY a' haX' (h ▸ hv2)
      rcases route a b' haX hbY' (reach_head hQ hpath huQ hune)
          (reach_last hQ' hpath' hvQ' hvne) hno with ⟨-, h⟩ | ⟨h, -⟩
      · exact hsb' h
      · exact hsa h
    · -- `v ∈ Zⱼ`.
      have hvne : v ≠ a' := fun h => hdXZ a' haX' (h ▸ hv3)
      rcases route a b' haX hbY' (reach_head hQ hpath huQ hune)
          (reach_last hQ' hpath' hvQ' hvne) hno with ⟨-, h⟩ | ⟨h, -⟩
      · exact hsb' h
      · exact hsa h
  · -- `u ∈ Yⱼ`, so `u = yⱼ ∈ V`.
    have huy : u = b := huY hu2
    have hsu : G.Adj s u := by rw [huy]; exact hsb
    have hru : ¬ G.Adj r u := by rw [huy]; exact hrb
    have hune : u ≠ a := fun h => hdXY a haX (h ▸ hu2)
    rcases hloc v hvV with hv1 | hv2 | hv3
    · -- `v ∈ Xⱼ`: route from `x'ⱼ ∈ V` to `yⱼ ∈ V`.
      have hvne : v ≠ b' := fun h => hdXY v hv1 (h ▸ hbY')
      rcases route' a' b haX' hbY (reach_head hQ' hpath' hvQ' hvne)
          (reach_last hQ hpath huQ hune) (fun h => hno h.symm) with ⟨h, -⟩ | ⟨-, h⟩
      · exact hra' h
      · exact hrb h
    · -- both in `Yⱼ`: the displayed odd hole with `f₁, f_k` exchanged.
      have hvb : v = b' := hvY hv2
      have hrv : G.Adj r v := by rw [hvb]; exact hrb'
      have hsv : ¬ G.Adj s v := by rw [hvb]; exact hsb'
      exact hole v u hvV huV hrv hsv hsu hru (fun h => hno h.symm) (Or.inr ⟨hv2, hu2⟩)
    · -- `v ∈ Zⱼ`.
      have hvne : v ≠ b' := fun h => hdYZ b' hbY' (h ▸ hv3)
      rcases route' a' b haX' hbY (reach_head hQ' hpath' hvQ' hvne)
          (reach_last hQ hpath huQ hune) (fun h => hno h.symm) with ⟨h, -⟩ | ⟨-, h⟩
      · exact hra' h
      · exact hrb h
  · -- `u ∈ Zⱼ`.
    have hune : u ≠ b := fun h => hdYZ b hbY (h ▸ hu3)
    have hune' : u ≠ a := fun h => hdXZ a haX (h ▸ hu3)
    rcases hloc v hvV with hv1 | hv2 | hv3
    · have hvne : v ≠ b' := fun h => hdXY v hv1 (h ▸ hbY')
      rcases route' a' b haX' hbY (reach_head hQ' hpath' hvQ' hvne)
          (reach_last hQ hpath huQ hune') (fun h => hno h.symm) with ⟨h, -⟩ | ⟨-, h⟩
      · exact hra' h
      · exact hrb h
    · have hvne : v ≠ a' := fun h => hdXY a' haX' (h ▸ hv2)
      rcases route a b' haX hbY' (reach_head hQ hpath huQ hune)
          (reach_last hQ' hpath' hvQ' hvne) hno with ⟨-, h⟩ | ⟨h, -⟩
      · exact hsb' h
      · exact hsa h
    · have hvne : v ≠ a' := fun h => hdXZ a' haX' (h ▸ hv3)
      rcases route a b' haX hbY' (reach_head hQ hpath huQ hune)
          (reach_last hQ' hpath' hvQ' hvne) hno with ⟨-, h⟩ | ⟨h, -⟩
      · exact hsb' h
      · exact hsa h

end Workspace.ProofLemmas.Thm95OffspringGapComplete
