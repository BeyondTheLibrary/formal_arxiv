import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentYCount
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm162ClaimFourHelpers
import Workspace.ProofLemmas.Thm162ClaimFourTracks
import Workspace.ProofLemmas.Thm162ClaimFourRim

/-!
# 16.2, claim (4)

PAPER (16.2, printed p. 99): *"(4) At least one of `f₁, f_k` has only one neighbour in `C`."*

Its Lean form is `Workspace.ProofLemmas.OddWheelAttachmentMain.Claim4`; the three extra
hypotheses are the paragraph between (3) and (4) (*"So `X₁` is the set of neighbours of `f₁` in
`C`, and `X₂` is the set of neighbours of `f_k` in `C`"*, and that the two sets are
cross-opposite in wheel-parity).

`OddWheelAttachmentClaim4.exists_two_trans_arcs` and `…hole_of_path_and_arc` already discharge
the claim's opening (*"Then there are disjoint paths `Q, R` of `C`, both containing neighbours
of both `f₁, f_k` … Choose `Q, R` minimal"*, and the hole `f₁-⋯-f_k-q₂-Q-q₁-f₁`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm162ClaimFour

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentMain

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Claim (4) of 16.2.** -/
theorem claim_four (G : SimpleGraph V) : OddWheelAttachmentMain.Claim4 G := by
  classical
  intro C Y F P x₁ x₂ f₁ fk h hX₁eq hX₂eq hcross
  by_contra hcon
  push Not at hcon
  obtain ⟨hZ₁ne, hZ₂ne⟩ := hcon
  let Z₁ : Set V := {u : V | u ∈ C ∧ G.Adj f₁ u}
  let Z₂ : Set V := {u : V | u ∈ C ∧ G.Adj fk u}
  have hZ₁C : ∀ z ∈ Z₁, z ∈ C := fun _ hz => hz.1
  have hZ₂C : ∀ z ∈ Z₂, z ∈ C := fun _ hz => hz.1
  have hX₁Z₁ : Att G C (F \ {fk}) = Z₁ := hX₁eq
  have hX₂Z₂ : Att G C (F \ {f₁}) = Z₂ := hX₂eq
  have hZdisj : ∀ z : V, z ∈ Z₁ → z ∈ Z₂ → False := by
    intro z hz₁ hz₂
    have ho := hcross z (by rw [hX₁Z₁]; exact hz₁) z
      (by rw [hX₂Z₂]; exact hz₂)
    exact ho.1 rfl
  have hZ₁nonempty : Z₁.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ z ∈ Att G C F, z ∈ Att G C (F \ {f₁}) := by
      intro z hz
      rw [h.union] at hz
      rcases hz with hz | hz
      · exfalso
        have : z ∈ Z₁ := by rw [← hX₁Z₁]; exact hz
        rw [hne] at this
        simpa using this
      · exact hz
    apply h.dich₂
    refine ⟨⟨x₁, hall x₁ h.att₁, x₂, hall x₂ h.att₂, h.opp⟩,
      ⟨x₁, hall x₁ h.att₁, x₂, hall x₂ h.att₂, h.opp.1, h.nadj⟩⟩
  have hZ₂nonempty : Z₂.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ z ∈ Att G C F, z ∈ Att G C (F \ {fk}) := by
      intro z hz
      rw [h.union] at hz
      rcases hz with hz | hz
      · exact hz
      · exfalso
        have : z ∈ Z₂ := by rw [← hX₂Z₂]; exact hz
        rw [hne] at this
        simpa using this
    apply h.dich₁
    refine ⟨⟨x₁, hall x₁ h.att₁, x₂, hall x₂ h.att₂, h.opp⟩,
      ⟨x₁, hall x₁ h.att₁, x₂, hall x₂ h.att₂, h.opp.1, h.nadj⟩⟩
  have hZ₁two : 2 ≤ Z₁.ncard := by
    have hp : 0 < Z₁.ncard := (Set.ncard_pos (Set.toFinite Z₁)).mpr hZ₁nonempty
    have hn : Z₁.ncard ≠ 1 := by simpa only [Z₁] using hZ₁ne
    omega
  have hZ₂two : 2 ≤ Z₂.ncard := by
    have hp : 0 < Z₂.ncard := (Set.ncard_pos (Set.toFinite Z₂)).mpr hZ₂nonempty
    have hn : Z₂.ncard ≠ 1 := by simpa only [Z₂] using hZ₂ne
    omega
  have hC : IsHoleList G C := h.wheel.1.1
  have hp : 0 < C.length := by have := hC.1; omega
  obtain ⟨b, s, b', s', hs, hs', hsep₁, hsep₂⟩ :=
    OddWheelAttachmentClaim4.exists_two_trans_arcs hC hp hZ₁C hZ₂C hZdisj hZ₁two hZ₂two

  -- The path `f₁-⋯-fk`, inherited from the interior of `P`.
  let S : List V := (P.drop 1).take (P.length - 2 - 1 + 1)
  have hPlen : 4 ≤ P.length := h.len
  have hS : IsPathFrom G S f₁ fk := by
    have hS' := PathBasics.isPathFrom_slice h.path.1
      (show (1 : ℕ) < P.length - 2 by omega) (show P.length - 2 < P.length by omega)
    rw [fst_getElem h, lst_getElem h] at hS'
    exact hS'
  have hSlen : S.length = P.length - 2 := by
    dsimp only [S]
    rw [PathBasics.length_slice P (show (1 : ℕ) ≤ P.length - 2 by omega)
      (show P.length - 2 < P.length by omega)]
    omega
  have hS2 : 2 ≤ S.length := by omega
  have hSmemF : ∀ z ∈ S, z ∈ F := by
    intro z hz
    have hz' := (PathBasics.mem_slice_iff P
      (show (1 : ℕ) ≤ P.length - 2 by omega)
      (show P.length - 2 < P.length by omega)).mp hz
    obtain ⟨t, ht, ht1, ht2, rfl⟩ := hz'
    rw [h.interiorEq]
    exact PathBasics.getElem_mem_interior h.path.1 ht (by omega) (by omega)
  have hSnotC : ∀ z ∈ S, z ∉ C := fun z hz => h.notC z (hSmemF z hz)
  have hSnotY : ∀ z ∈ S, z ∉ Y := fun z hz => h.notY z (hSmemF z hz)
  have hSnc : ∀ z ∈ S, ¬ VertexComplete G z Y :=
    fun z hz => h.notComplete z (hSmemF z hz)
  have hfkne : f₁ ≠ fk := fst_ne_lst h
  have hSC : ∀ z ∈ S, ∀ u ∈ C,
      (G.Adj z u ↔ (z = f₁ ∧ u ∈ Z₁) ∨ (z = fk ∧ u ∈ Z₂)) := by
    intro z hz u hu
    constructor
    · intro hzu
      by_cases hz₁ : z = f₁
      · left
        exact ⟨hz₁, by subst z; exact ⟨hu, hzu⟩⟩
      · right
        have hu₂ : u ∈ Z₂ := by
          rw [← hX₂Z₂]
          exact ⟨hu, z, ⟨hSmemF z hz, hz₁⟩, hzu.symm⟩
        refine ⟨?_, hu₂⟩
        by_contra hzk
        have hu₁ : u ∈ Z₁ := by
          rw [← hX₁Z₁]
          exact ⟨hu, z, ⟨hSmemF z hz, hzk⟩, hzu.symm⟩
        exact hZdisj u hu₁ hu₂
    · rintro (⟨rfl, hu⟩ | ⟨rfl, hu⟩)
      · exact hu.2
      · exact hu.2

  have hBerge : Berge G := h.inF6.1.1.1
  have hYanti : AnticonnectedSet G Y := h.wheel.2.1.2.1
  have hCY : ∀ z ∈ C, z ∉ Y := h.wheel.2.1.2.2
  have hcycEven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge h.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC hcycEven
  have hstep : ∀ z w : V, z ∈ C → w ∈ C → G.Adj z w →
      (π z ≠ π w ↔ EdgeComplete G Y z w) := by
    intro z w hz hw hzw
    exact OddWheelAttachmentYCount.parity_step hC hcycEven hπ hz hw hzw
  have hopp : ∀ z ∈ Z₁, ∀ w ∈ Z₂, OppositeWheelParity G C Y z w := by
    intro z hz w hw
    exact hcross z (by rw [hX₁Z₁]; exact hz) w (by rw [hX₂Z₂]; exact hw)
  have hcompleteCross : ∀ z ∈ Z₁, ∀ w ∈ Z₂, G.Adj z w →
      VertexComplete G z Y ∧ VertexComplete G w Y := by
    intro z hz w hw hzw
    have ho := hopp z hz w hw
    have hpne : π z ≠ π w := by
      intro he
      exact ho.2.2.2 ((hπ z w ho.2.1 ho.2.2.1 ho.1).mpr he)
    exact ((hstep z w ho.2.1 ho.2.2.1 hzw).mp hpne).2

  have hQdata := Thm162ClaimFourRim.transition_data hC hp hBerge hYanti hCY hπ2 hπ hstep
    hS hS2 hSnotC hSnotY hSnc hSC hZ₁C hZ₂C hZdisj hopp hs
  have hRdata := Thm162ClaimFourRim.transition_data hC hp hBerge hYanti hCY hπ2 hπ hstep
    hS hS2 hSnotC hSnotY hSnc hSC hZ₁C hZ₂C hZdisj hopp hs'
  rcases hQdata with ⟨Q, q₁, q₂, c, d, hQlen, hQpath, hq₁Z, hq₂Z, hQC,
    hSQdisj, hSQ, hQY, hQc, hcd, hcdadj, hQeven, hQorient⟩
  rcases hRdata with ⟨R, r₁, r₂, e, g, hRlen, hRpath, hr₁Z, hr₂Z, hRC,
    hSRdisj, hSR, hRY, hRc, heg, hegadj, hReven, hRorient⟩
  have hs1 : 1 ≤ s := hs.1
  have hs'1 : 1 ≤ s' := hs'.1
  have hQ2 : 2 ≤ Q.length := by rw [hQlen]; omega
  have hR2 : 2 ≤ R.length := by rw [hRlen]; omega
  have hQRnat := Thm162ClaimFourRim.separated_arcs_adj_iff hC hp hs.2.1 hs'.2.1 hsep₁ hsep₂
  have hdisjNat := Thm162ClaimFourRim.separated_arcs_disjoint hC hp hs.2.1 hsep₁ hsep₂
  have hshortNat : s = 1 → s' = 1 →
      G.Adj (OddWheelAttachmentArcs.cyc C hp (b + s))
        (OddWheelAttachmentArcs.cyc C hp b') →
      G.Adj (OddWheelAttachmentArcs.cyc C hp b)
        (OddWheelAttachmentArcs.cyc C hp (b' + s')) → False := by
    exact Thm162ClaimFourRim.separated_short_not_both hC hp h.wheel.1.2 hsep₁ hsep₂
  have hfinal : S.length = 2 → (∀ w : V, VertexComplete G w Y →
      ∃ z ∈ ([f₁, fk] : List V), G.Adj w z) → False := by
    intro hSshort hall
    have hclass : ∀ w ∈ C, VertexComplete G w Y → w ∈ Z₁ ∨ w ∈ Z₂ := by
      intro w hwC hwY
      obtain ⟨z, hz, hwz⟩ := hall w hwY
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact Or.inl ⟨hwC, hwz.symm⟩
      · exact Or.inr ⟨hwC, hwz.symm⟩
    have hπcross : ∀ u ∈ Z₁, ∀ v ∈ Z₂, π u ≠ π v := by
      intro u hu v hv he
      have ho := hopp u hu v hv
      exact ho.2.2.2 ((hπ u v ho.2.1 ho.2.2.1 ho.1).mpr he)
    have hnoZ₁edge : ∀ u ∈ Z₁, ∀ v ∈ Z₁, ¬ EdgeComplete G Y u v := by
      intro u hu v hv hE
      obtain ⟨w, hw⟩ := hZ₂nonempty
      have huv : π u ≠ π v :=
        (hstep u v (hZ₁C u hu) (hZ₁C v hv) hE.1).mpr hE
      have h1 := hπcross u hu w hw
      have h2 := hπcross v hv w hw
      have bu := hπ2 u
      have bv := hπ2 v
      have bw := hπ2 w
      omega
    have hnoZ₂edge : ∀ u ∈ Z₂, ∀ v ∈ Z₂, ¬ EdgeComplete G Y u v := by
      intro u hu v hv hE
      obtain ⟨w, hw⟩ := hZ₁nonempty
      have huv : π u ≠ π v :=
        (hstep u v (hZ₂C u hu) (hZ₂C v hv) hE.1).mpr hE
      have h1 := hπcross w hw u hu
      have h2 := hπcross w hw v hv
      have bu := hπ2 u
      have bv := hπ2 v
      have bw := hπ2 w
      omega
    have horient : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
        ∃ a b : V, a ∈ Z₁ ∧ b ∈ Z₂ ∧ EdgeComplete G Y a b ∧
          ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
      intro u v huC hvC hE
      rcases hclass u huC hE.2.1 with hu₁ | hu₂ <;>
        rcases hclass v hvC hE.2.2 with hv₁ | hv₂
      · exact absurd hE (hnoZ₁edge u hu₁ v hv₁)
      · exact ⟨u, v, hu₁, hv₂, hE, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨v, u, hv₁, hu₂, WheelParity.edgeComplete_symm hE,
          Or.inr ⟨rfl, rfl⟩⟩
      · exact absurd hE (hnoZ₂edge u hu₂ v hv₂)
    have hpairAttach : ∀ a ∈ Z₁, ∀ b ∈ Z₂, ∀ x ∈ S,
        ∀ y ∈ ([a, b] : List V),
          (G.Adj x y ↔ (x = f₁ ∧ y = a) ∨ (x = fk ∧ y = b)) := by
      intro a ha b hb x hx y hy
      have hab : a ≠ b := fun he => hZdisj a ha (he ▸ hb)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hya | hyb
      · subst y
        rw [hSC x hx a (hZ₁C a ha)]
        constructor
        · rintro (⟨hxf, -⟩ | ⟨-, ha₂⟩)
          · exact Or.inl ⟨hxf, rfl⟩
          · exact absurd ha₂ (hZdisj a ha)
        · rintro (⟨hxf, -⟩ | ⟨-, he⟩)
          · exact Or.inl ⟨hxf, ha⟩
          · exact absurd he hab
      · subst y
        rw [hSC x hx b (hZ₂C b hb)]
        constructor
        · rintro (⟨-, hb₁⟩ | ⟨hxf, -⟩)
          · exact absurd hb₁ (fun hb₁ => hZdisj b hb₁ hb)
          · exact Or.inr ⟨hxf, rfl⟩
        · rintro (⟨-, he⟩ | ⟨hxf, -⟩)
          · exact absurd he.symm hab
          · exact Or.inr ⟨hxf, hb⟩
    have hedgePair : ∀ a b : V, EdgeComplete G Y a b →
        {x : V | x ∈ ([a, b] : List V) ∧ VertexComplete G x Y} = {a, b} := by
      intro a b hE
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨Or.inl rfl, hE.2.1⟩
        · exact ⟨Or.inr rfl, hE.2.2⟩
    have hantiFinish : ∀ q₁ q₂ r₁ r₂ : V,
        q₁ ∈ Z₁ → q₂ ∈ Z₂ → r₁ ∈ Z₁ → r₂ ∈ Z₂ →
        EdgeComplete G Y q₁ q₂ → EdgeComplete G Y r₁ r₂ →
        (∀ x ∈ ([q₁, q₂] : List V), ∀ y ∈ ([r₁, r₂] : List V), ¬ G.Adj x y) →
        False := by
      intro q₁ q₂ r₁ r₂ hq₁ hq₂ hr₁ hr₂ hqE hrE hanti
      have hQS : ∀ x ∈ S, x ∉ ([q₁, q₂] : List V) := by
        intro x hxS hxQ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxQ
        rcases hxQ with hxQ | hxQ
        · subst x; exact hSnotC q₁ hxS (hZ₁C q₁ hq₁)
        · subst x; exact hSnotC q₂ hxS (hZ₂C q₂ hq₂)
      have hRS : ∀ x ∈ S, x ∉ ([r₁, r₂] : List V) := by
        intro x hxS hxR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
        rcases hxR with hxR | hxR
        · subst x; exact hSnotC r₁ hxS (hZ₁C r₁ hr₁)
        · subst x; exact hSnotC r₂ hxS (hZ₂C r₂ hr₂)
      have hQRd : ∀ x ∈ ([q₁, q₂] : List V), x ∉ ([r₁, r₂] : List V) := by
        intro x hxQ hxR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxQ hxR
        rcases hxQ with hx1 | hx2 <;> rcases hxR with hr1 | hr2
        · have he : q₁ = r₁ := hx1.symm.trans hr1
          exact hanti q₂ (by simp) r₁ (by simp) (by rw [← he]; exact hqE.1.symm)
        · have he : q₁ = r₂ := hx1.symm.trans hr2
          exact hanti q₂ (by simp) r₂ (by simp) (by rw [← he]; exact hqE.1.symm)
        · have he : q₂ = r₁ := hx2.symm.trans hr1
          exact hanti q₁ (by simp) r₁ (by simp) (by rw [← he]; exact hqE.1)
        · have he : q₂ = r₂ := hx2.symm.trans hr2
          exact hanti q₁ (by simp) r₂ (by simp) (by rw [← he]; exact hqE.1)
      exact Thm162ClaimFourHelpers.no_banister h.inF6 hYanti hS hS2
        ⟨PathBasics.isPathList_pair hqE.1, rfl, rfl⟩ (by simp)
        ⟨PathBasics.isPathList_pair hrE.1, rfl, rfl⟩ (by simp)
        hQS hRS hQRd
        (hpairAttach q₁ hq₁ q₂ hq₂)
        (hpairAttach r₁ hr₁ r₂ hr₂) hanti hSnotY
        (fun x hx => hCY x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · subst x; exact hZ₁C q₁ hq₁
          · subst x; exact hZ₂C q₂ hq₂))
        (fun x hx => hCY x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · subst x; exact hZ₁C r₁ hr₁
          · subst x; exact hZ₂C r₂ hr₂)) hSnc
        (hedgePair q₁ q₂ hqE) hqE.1.ne hqE.1
        (hedgePair r₁ r₂ hrE) hrE.1.ne hrE.1
    have hevenYE := WheelBasics.even_ncard_yEdges_of_wheel hBerge h.wheel
    by_cases hfour : 4 ≤ (HoleYEdgeParity.yEdges G Y C).ncard
    · obtain ⟨a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hanti⟩ :=
        Thm162ClaimFourRim.four_yEdges_give_anticomplete_pair hC hp h.wheel.1.2 hfour
      obtain ⟨q₁, q₂, hq₁, hq₂, hqE, hqo⟩ := horient a b haC hbC hab
      obtain ⟨r₁, r₂, hr₁, hr₂, hrE, hro⟩ := horient c d hcC hdC hcd
      apply hantiFinish q₁ q₂ r₁ r₂ hq₁ hq₂ hr₁ hr₂ hqE hrE
      intro x hx y hy
      apply hanti x
      · rcases hqo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          exact hx.symm
      · rcases hro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hy
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
          exact hy.symm
    · obtain ⟨a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hac, had, hbc, hbd⟩ :=
        h.wheel.2.2
      have heab : s(a, b) ∈ HoleYEdgeParity.yEdges G Y C :=
        ⟨a, haC, b, hbC, rfl, hab⟩
      have hecd : s(c, d) ∈ HoleYEdgeParity.yEdges G Y C :=
        ⟨c, hcC, d, hdC, rfl, hcd⟩
      have habcd : s(a, b) ≠ s(c, d) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hac h1
        · exact had h1
      have htwo : 2 ≤ (HoleYEdgeParity.yEdges G Y C).ncard := by
        have hsub : ({s(a, b), s(c, d)} : Set (Sym2 V)) ⊆
            HoleYEdgeParity.yEdges G Y C := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact heab
          · exact hecd
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_pair habcd] at hle
        exact hle
      have htwoEq : (HoleYEdgeParity.yEdges G Y C).ncard = 2 := by
        change Even (HoleYEdgeParity.yEdges G Y C).ncard at hevenYE
        obtain ⟨m, hm⟩ := hevenYE
        omega
      obtain ⟨q₁, q₂, hq₁, hq₂, hqE, hqo⟩ := horient a b haC hbC hab
      obtain ⟨r₁, r₂, hr₁, hr₂, hrE, hro⟩ := horient c d hcC hdC hcd
      have hq₁r₁ : q₁ ≠ r₁ := by
        rcases hqo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq₁r₂ : q₁ ≠ r₂ := by
        rcases hqo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq₂r₁ : q₂ ≠ r₁ := by
        rcases hqo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq₂r₂ : q₂ ≠ r₂ := by
        rcases hqo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hro with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hEdgesNe : s(q₁, q₂) ≠ s(r₁, r₂) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hq₁r₁ h1
        · exact hq₁r₂ h1
      have hpairSub : ({s(q₁, q₂), s(r₁, r₂)} : Set (Sym2 V)) ⊆
          HoleYEdgeParity.yEdges G Y C := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨q₁, hZ₁C q₁ hq₁, q₂, hZ₂C q₂ hq₂, rfl, hqE⟩
        · exact ⟨r₁, hZ₁C r₁ hr₁, r₂, hZ₂C r₂ hr₂, rfl, hrE⟩
      have hpairEq : ({s(q₁, q₂), s(r₁, r₂)} : Set (Sym2 V)) =
          HoleYEdgeParity.yEdges G Y C := by
        apply Set.eq_of_subset_of_ncard_le hpairSub
        rw [htwoEq, Set.ncard_pair hEdgesNe]
      have hnoCross : ∀ u ∈ Z₁, ∀ v ∈ Z₂,
          s(u, v) ≠ s(q₁, q₂) → s(u, v) ≠ s(r₁, r₂) → ¬ G.Adj u v := by
        intro u hu v hv hneQ hneR huv
        have hE := hcompleteCross u hu v hv huv
        have hm : s(u, v) ∈ HoleYEdgeParity.yEdges G Y C :=
          ⟨u, hZ₁C u hu, v, hZ₂C v hv, rfl, huv, hE.1, hE.2⟩
        rw [← hpairEq] at hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        exact hm.elim hneQ hneR
      have hn12Q : s(q₁, r₂) ≠ s(q₁, q₂) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hq₂r₂ h2.symm
        · exact hqE.1.ne h1
      have hn12R : s(q₁, r₂) ≠ s(r₁, r₂) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hq₁r₁ h1
        · exact hq₁r₂ h1
      have hn21Q : s(r₁, q₂) ≠ s(q₁, q₂) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hq₁r₁ h1.symm
        · exact hq₂r₁ h1.symm
      have hn21R : s(r₁, q₂) ≠ s(r₁, r₂) := by
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hq₂r₂ h2
        · exact hrE.1.ne h1
      have hn12 : ¬ G.Adj q₁ r₂ := hnoCross q₁ hq₁ r₂ hr₂
        hn12Q hn12R
      have hn21 : ¬ G.Adj q₂ r₁ := by
        intro ha
        exact hnoCross r₁ hr₁ q₂ hq₂ hn21Q hn21R ha.symm
      have hQRd : ∀ x ∈ ([q₁, q₂] : List V), x ∉ ([r₁, r₂] : List V) := by
        intro x hx hxR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hxR
        rcases hx with hx1 | hx2 <;> rcases hxR with hr1 | hr2
        · exact hq₁r₁ (hx1.symm.trans hr1)
        · exact hq₁r₂ (hx1.symm.trans hr2)
        · exact hq₂r₁ (hx2.symm.trans hr1)
        · exact hq₂r₂ (hx2.symm.trans hr2)
      have hQRss : ∀ x ∈ ([q₁, q₂] : List V), ∀ y ∈ ([r₁, r₂] : List V),
          (G.Adj x y ↔
            (x = q₁ ∧ y = r₁ ∧ G.Adj q₁ r₁) ∨
            (x = q₂ ∧ y = r₂ ∧ G.Adj q₂ r₂)) := by
        intro x hx y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
        rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2
        · subst x; subst y
          simp [hqE.1.ne, hqE.1.ne.symm, hrE.1.ne, hrE.1.ne.symm,
            hq₁r₁, hq₁r₂, hq₂r₁, hq₂r₂]
        · subst x; subst y
          simp [hqE.1.ne, hqE.1.ne.symm, hrE.1.ne, hrE.1.ne.symm,
            hq₁r₁, hq₁r₂, hq₂r₁, hq₂r₂, hn12]
        · subst x; subst y
          simp [hqE.1.ne, hqE.1.ne.symm, hrE.1.ne, hrE.1.ne.symm,
            hq₁r₁, hq₁r₂, hq₂r₁, hq₂r₂, hn21]
        · subst x; subst y
          simp [hqE.1.ne, hqE.1.ne.symm, hrE.1.ne, hrE.1.ne.symm,
            hq₁r₁, hq₁r₂, hq₂r₁, hq₂r₂]
      have hQS : ∀ x ∈ S, x ∉ ([q₁, q₂] : List V) := by
        intro x hxS hxQ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxQ
        rcases hxQ with hxQ | hxQ
        · subst x; exact hSnotC q₁ hxS (hZ₁C q₁ hq₁)
        · subst x; exact hSnotC q₂ hxS (hZ₂C q₂ hq₂)
      have hRS : ∀ x ∈ S, x ∉ ([r₁, r₂] : List V) := by
        intro x hxS hxR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
        rcases hxR with hxR | hxR
        · subst x; exact hSnotC r₁ hxS (hZ₁C r₁ hr₁)
        · subst x; exact hSnotC r₂ hxS (hZ₂C r₂ hr₂)
      exact Thm162ClaimFourTracks.same_side_tracks_false h.inF6 hYanti hS hS2
        ⟨PathBasics.isPathList_pair hqE.1, rfl, rfl⟩ (by simp)
        ⟨PathBasics.isPathList_pair hrE.1, rfl, rfl⟩ (by simp)
        hQS hRS hQRd (hpairAttach q₁ hq₁ q₂ hq₂)
        (hpairAttach r₁ hr₁ r₂ hr₂) hQRss hSnotY
        (fun x hx => hCY x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · subst x; exact hZ₁C q₁ hq₁
          · subst x; exact hZ₂C q₂ hq₂))
        (fun x hx => hCY x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · subst x; exact hZ₁C r₁ hr₁
          · subst x; exact hZ₂C r₂ hr₂)) hSnc
        (hedgePair q₁ q₂ hqE) hqE.1.ne hqE.1
        (hedgePair r₁ r₂ hrE) hrE.1.ne hrE.1
        (by rw [hSshort]; exact ⟨2, rfl⟩) (by rw [hSshort]; exact ⟨2, rfl⟩)
        (fun _ _ _ h11 h22 =>
          Thm162ClaimFourRim.no_square_on_long_hole hC h.wheel.1.2
            (hZ₁C q₁ hq₁) (hZ₂C q₂ hq₂)
            (hZ₁C r₁ hr₁) (hZ₂C r₂ hr₂)
            hqE.1.ne hq₁r₁ hq₁r₂ hq₂r₁ hq₂r₂ hrE.1.ne
            hqE.1 hrE.1 h11 h22)
  rcases hQorient with hQf | hQr <;> rcases hRorient with hRf | hRr
  · rcases hQf with ⟨rfl, rfl, rfl⟩
    rcases hRf with ⟨rfl, rfl, rfl⟩
    have hQRdisj : ∀ x ∈ OddWheelAttachmentArcs.arc C hp b (s + 1),
        x ∉ OddWheelAttachmentArcs.arc C hp b' (s' + 1) := hdisjNat
    have hQR : ∀ x ∈ OddWheelAttachmentArcs.arc C hp b (s + 1),
        ∀ y ∈ OddWheelAttachmentArcs.arc C hp b' (s' + 1),
        (G.Adj x y ↔
          (x = OddWheelAttachmentArcs.cyc C hp b ∧
            y = OddWheelAttachmentArcs.cyc C hp (b' + s') ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp b)
              (OddWheelAttachmentArcs.cyc C hp (b' + s'))) ∨
          (x = OddWheelAttachmentArcs.cyc C hp (b + s) ∧
            y = OddWheelAttachmentArcs.cyc C hp b' ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp (b + s))
              (OddWheelAttachmentArcs.cyc C hp b'))) := by
      intro x hx y hy
      rw [hQRnat x hx y hy]
      tauto
    exact Thm162ClaimFourTracks.opposite_tracks_false h.inF6 hYanti hS hS2 hQpath hQ2
      hRpath hR2 hSQdisj hSRdisj hQRdisj hSQ hSR hQR hSnotY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj hQeven hReven
      (fun ha => hcompleteCross _ hq₁Z _ hr₂Z ha)
      (by
        intro ha
        have hh := hcompleteCross _ hr₁Z _ hq₂Z ha.symm
        exact ⟨hh.2, hh.1⟩)
      (fun hQl hRl ho hi => hshortNat (by omega) (by omega) hi ho) hfinal
  · rcases hQf with ⟨rfl, rfl, rfl⟩
    rcases hRr with ⟨rfl, rfl, rfl⟩
    have hQRdisj : ∀ x ∈ OddWheelAttachmentArcs.arc C hp b (s + 1),
        x ∉ (OddWheelAttachmentArcs.arc C hp b' (s' + 1)).reverse := by
      intro x hx hxR
      exact hdisjNat x hx (List.mem_reverse.mp hxR)
    have hQR : ∀ x ∈ OddWheelAttachmentArcs.arc C hp b (s + 1),
        ∀ y ∈ (OddWheelAttachmentArcs.arc C hp b' (s' + 1)).reverse,
        (G.Adj x y ↔
          (x = OddWheelAttachmentArcs.cyc C hp b ∧
            y = OddWheelAttachmentArcs.cyc C hp (b' + s') ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp b)
              (OddWheelAttachmentArcs.cyc C hp (b' + s'))) ∨
          (x = OddWheelAttachmentArcs.cyc C hp (b + s) ∧
            y = OddWheelAttachmentArcs.cyc C hp b' ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp (b + s))
              (OddWheelAttachmentArcs.cyc C hp b'))) := by
      intro x hx y hy
      rw [hQRnat x hx y (List.mem_reverse.mp hy)]
      tauto
    exact Thm162ClaimFourTracks.same_side_tracks_false h.inF6 hYanti hS hS2 hQpath hQ2
      hRpath hR2 hSQdisj hSRdisj hQRdisj hSQ hSR hQR hSnotY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj hQeven hReven
      (fun hQl hRl hSl ho hi => hshortNat (by omega) (by omega) hi ho)
  · rcases hQr with ⟨rfl, rfl, rfl⟩
    rcases hRf with ⟨rfl, rfl, rfl⟩
    have hQRdisj : ∀ x ∈ (OddWheelAttachmentArcs.arc C hp b (s + 1)).reverse,
        x ∉ OddWheelAttachmentArcs.arc C hp b' (s' + 1) := by
      intro x hx hxR
      exact hdisjNat x (List.mem_reverse.mp hx) hxR
    have hQR : ∀ x ∈ (OddWheelAttachmentArcs.arc C hp b (s + 1)).reverse,
        ∀ y ∈ OddWheelAttachmentArcs.arc C hp b' (s' + 1),
        (G.Adj x y ↔
          (x = OddWheelAttachmentArcs.cyc C hp (b + s) ∧
            y = OddWheelAttachmentArcs.cyc C hp b' ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp (b + s))
              (OddWheelAttachmentArcs.cyc C hp b')) ∨
          (x = OddWheelAttachmentArcs.cyc C hp b ∧
            y = OddWheelAttachmentArcs.cyc C hp (b' + s') ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp b)
              (OddWheelAttachmentArcs.cyc C hp (b' + s')))) := by
      intro x hx y hy
      exact hQRnat x (List.mem_reverse.mp hx) y hy
    exact Thm162ClaimFourTracks.same_side_tracks_false h.inF6 hYanti hS hS2 hQpath hQ2
      hRpath hR2 hSQdisj hSRdisj hQRdisj hSQ hSR hQR hSnotY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj hQeven hReven
      (fun hQl hRl hSl hi ho => hshortNat (by omega) (by omega) hi ho)
  · rcases hQr with ⟨rfl, rfl, rfl⟩
    rcases hRr with ⟨rfl, rfl, rfl⟩
    have hQRdisj : ∀ x ∈ (OddWheelAttachmentArcs.arc C hp b (s + 1)).reverse,
        x ∉ (OddWheelAttachmentArcs.arc C hp b' (s' + 1)).reverse := by
      intro x hx hxR
      exact hdisjNat x (List.mem_reverse.mp hx) (List.mem_reverse.mp hxR)
    have hQR : ∀ x ∈ (OddWheelAttachmentArcs.arc C hp b (s + 1)).reverse,
        ∀ y ∈ (OddWheelAttachmentArcs.arc C hp b' (s' + 1)).reverse,
        (G.Adj x y ↔
          (x = OddWheelAttachmentArcs.cyc C hp (b + s) ∧
            y = OddWheelAttachmentArcs.cyc C hp b' ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp (b + s))
              (OddWheelAttachmentArcs.cyc C hp b')) ∨
          (x = OddWheelAttachmentArcs.cyc C hp b ∧
            y = OddWheelAttachmentArcs.cyc C hp (b' + s') ∧
            G.Adj (OddWheelAttachmentArcs.cyc C hp b)
              (OddWheelAttachmentArcs.cyc C hp (b' + s')))) := by
      intro x hx y hy
      exact hQRnat x (List.mem_reverse.mp hx) y (List.mem_reverse.mp hy)
    exact Thm162ClaimFourTracks.opposite_tracks_false h.inF6 hYanti hS hS2 hQpath hQ2
      hRpath hR2 hSQdisj hSRdisj hQRdisj hSQ hSR hQR hSnotY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj hQeven hReven
      (fun ha => hcompleteCross _ hq₁Z _ hr₂Z ha)
      (by
        intro ha
        have hh := hcompleteCross _ hr₁Z _ hq₂Z ha.symm
        exact ⟨hh.2, hh.1⟩)
      (fun hQl hRl hi ho => hshortNat (by omega) (by omega) hi ho) hfinal

end Workspace.ProofLemmas.Thm162ClaimFour
