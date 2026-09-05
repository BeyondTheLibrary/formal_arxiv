import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.ProofLemmas.OddWheelAttachmentClaim3
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentYCount
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlueInduced
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm101LinkOntoTriangle
import Workspace.ProofLemmas.Thm162ClaimFive
import Workspace.ProofLemmas.Thm162SetupBasics
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S13.Thm_13_6

/-!
# 16.2, claim (3)

PAPER (16.2, printed p. 98): *"(3) If `X₁` has members of opposite wheel-parity then the theorem
holds."*

The printed proof of (3) ends *"…a contradiction.  This proves (3)"*, so its Lean form —
`Workspace.ProofLemmas.OddWheelAttachmentMain.Claim3` — is the negation: under the configuration
of the paragraph after claim (1), `X₁` does **not** have members of opposite wheel-parity.

`OddWheelAttachmentClaim3.exists_setup3` already discharges the claim's first paragraph
(*"Then we may assume its only members are `p₁, p₂` … In particular, `p₁` has no neighbour in
`F \ {f₁}`"*).  What remains is the rest of the printed paragraph: the triangle `{p₁,p₂,f₁}`
case, and then the long `R₁/R₂/Q₁/Q₂` computation ending in 13.6.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm162ClaimThree

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentMain

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

private theorem pathFrom_dropLast {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ p.length) :
    IsPathFrom G p.dropLast u (p[p.length - 2]'(by omega)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.dropLast_eq_take]
    exact PathBasics.isPathList_take hp.1 (by omega)
  · have h0 : p[0]'(by omega) = u :=
      PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
    have hh := PathBasics.head?_slice p (i := 0) (j := p.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : p.length - 2 - 0 + 1 = p.length - 1 := by omega
    rw [he] at hh
    simpa [h0] using hh
  · have hl := PathBasics.getLast?_slice p
      (i := 0) (j := p.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : p.length - 2 - 0 + 1 = p.length - 1 := by omega
    rw [he] at hl
    exact hl

/-- The final 13.6/2.2 move in claim (3).  Unlike the shared claim-(5) version, `f₁` may
also see `p₂`; this harmless second possibility has wheel parity opposite to `p₁`. -/
private theorem odd_path_endgame {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    {pi : V → ℕ} (hpi2 : ∀ z : V, pi z < 2)
    (hpi : ∀ a b : V, a ∈ C → b ∈ C → a ≠ b →
      (SameWheelParity G C Y a b ↔ pi a = pi b))
    {W : List V} {p₁ x f₁ fk : V}
    (hW : IsPathFrom G W p₁ x) (hodd : Odd (pathLength W))
    (hp₁Y : VertexComplete G p₁ Y) (hxY : VertexComplete G x Y)
    (hintnc : ∀ z ∈ SPGT.interior W, ¬ VertexComplete G z Y)
    (hWY : ∀ z ∈ W, z ∉ Y)
    (hf₁ : f₁ ∈ SPGT.interior W) (hfk : fk ∈ SPGT.interior W) (hne : f₁ ≠ fk)
    (hnbr₁ : ∀ u : V, u ∈ C → G.Adj f₁ u → u = p₁ ∨ pi u ≠ pi p₁)
    (hnbrk : ∀ u : V, u ∈ C → G.Adj fk u → pi u ≠ pi p₁) : False := by
  classical
  have hBerge : Berge G := hG.1.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have h0 : 0 < (SPGT.interior W).length := List.length_pos_of_mem hf₁
  rw [PathBasics.interior_length] at h0
  have hlen3 : 3 ≤ W.length := by omega
  have hW0 : W[0]'(by omega) = p₁ :=
    PathBasics.getElem_zero_of_head? hW.2.1 (by omega)
  have hWl : W[W.length - 1]'(by omega) = x :=
    PathBasics.getElem_last_of_getLast? hW.2.2 (by omega)
  have hends : ∀ z : V, z ∈ W → VertexComplete G z Y → z = p₁ ∨ z = x := by
    intro z hzW hzY
    by_contra hc
    push Not at hc
    exact hintnc z ((PathBasics.mem_interior_iff_of_pathFrom hW).mpr
      ⟨hzW, hc.1, hc.2⟩) hzY
  have hnoedge : ¬ ∃ u ∈ W, ∃ v ∈ W, EdgeComplete G Y u v := by
    rintro ⟨u, huW, v, hvW, hadj, huY, hvY⟩
    have hpx : G.Adj p₁ x := by
      rcases hends u huW huY with rfl | rfl <;>
        rcases hends v hvW hvY with rfl | rfl
      · exact absurd rfl hadj.ne
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hadj.ne
    rw [← hW0, ← hWl] at hpx
    exact PathBasics.path_ends_not_adj hW.1 hlen3 hpx
  have hXP : Y ⊆ {v : V | v ∈ W}ᶜ := fun y hy hmem => hWY y hmem hy
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1 W p₁ x hW hodd
      Y hXP hYanti hp₁Y hxY with hedge | ⟨-, c, d, hcd, -⟩
  · exact hnoedge hedge
  have hcover : ∀ z : V, z ∈ SPGT.interior W → z = f₁ ∨ z = fk := by
    have hf₁' : f₁ = c ∨ f₁ = d := by
      have h := hf₁
      rw [hcd] at h
      simpa using h
    have hfk' : fk = c ∨ fk = d := by
      have h := hfk
      rw [hcd] at h
      simpa using h
    intro z hz
    rw [hcd] at hz
    have hz' : z = c ∨ z = d := by simpa using hz
    rcases hf₁' with rfl | rfl <;> rcases hfk' with rfl | rfl <;>
      rcases hz' with rfl | rfl <;> tauto
  have h22 := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti W p₁ x
    hW hWY hodd hp₁Y hxY hnoedge
  obtain ⟨w, hwC, hwY, hwne, hwpi⟩ :=
    OddWheelAttachmentYCount.exists_same_parity_yComplete (p := p₁)
      hBerge hw hpi2 hpi
  obtain ⟨z, hzint, hzadj⟩ := h22 w hwY
  rcases hcover z hzint with rfl | rfl
  · rcases hnbr₁ w hwC hzadj.symm with rfl | hnepi
    · exact hwne rfl
    · exact hnepi hwpi
  · exact hnbrk w hwC hzadj.symm hwpi

/-- **Claim (3) of 16.2.** -/
theorem claim_three (G : SimpleGraph V) : OddWheelAttachmentMain.Claim3 G := by
  classical
  intro C Y F P x₁ x₂ f₁ fk h hc2 hopp
  obtain ⟨p₁, p₂, pi, hs⟩ := OddWheelAttachmentClaim3.exists_setup3 h hc2 hopp
  have hC : IsHoleList G C := h.wheel.1.1
  have hn6 : 6 ≤ C.length := h.wheel.1.2
  have hP4 : 4 ≤ P.length := h.len
  have hBerge : Berge G := h.inF6.1.1.1
  have hYanti : AnticonnectedSet G Y := h.wheel.2.1.2.1
  have hCY : ∀ z ∈ C, z ∉ Y := h.wheel.2.1.2.2
  have hfkne : f₁ ≠ fk := fst_ne_lst h
  have hf₁F : f₁ ∈ F := fst_mem h
  have hfkF : fk ∈ F := lst_mem h
  obtain ⟨D, hD, hDn, hDC, hpos, hpos1, hD0, hD1⟩ :=
    exists_reorient hC hs.p₁C hs.p₂C hs.adj12
  have hD6 : 6 ≤ D.length := by omega
  have hp₁ : cyc D hpos 0 = p₁ := by rw [cyc_eq hpos (by omega)]; exact hD0
  have hp₂ : cyc D hpos 1 = p₂ := by rw [cyc_eq hpos (by omega)]; exact hD1
  have hcycC : ∀ t : ℕ, cyc D hpos t ∈ C := by
    intro t
    exact (hDC _).mp (cyc_mem hpos t)
  have hcycY : ∀ t : ℕ, cyc D hpos t ∉ Y := fun t => hCY _ (hcycC t)
  have hcycNe : ∀ {s t : ℕ}, s < D.length → t < D.length → s ≠ t →
      cyc D hpos s ≠ cyc D hpos t := by
    intro s t hsl htl hst
    exact cyc_ne hD hpos hsl htl hst

  -- The path `f₁-⋯-fk`, i.e. the interior of `P` in its inherited order.
  let S : List V := (P.drop 1).take (P.length - 2 - 1 + 1)
  have hS : IsPathFrom G S f₁ fk := by
    have hS' := PathBasics.isPathFrom_slice h.path.1
      (show (1 : ℕ) < P.length - 2 by omega) (show P.length - 2 < P.length by omega)
    rw [OddWheelAttachmentMain.fst_getElem h, OddWheelAttachmentMain.lst_getElem h] at hS'
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

  -- The first paragraph's description of all `F`--rim edges.
  have hFCedge : ∀ f ∈ F, ∀ u ∈ C, G.Adj f u → f = fk ∨ u = p₁ ∨ u = p₂ := by
    intro f hf u hu hadj
    by_cases hffk : f = fk
    · exact Or.inl hffk
    · have huX : u ∈ Att G C (F \ {fk}) := ⟨hu, f, ⟨hf, hffk⟩, hadj.symm⟩
      rw [hs.X₁eq] at huX
      exact Or.inr (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using huX)
  have hp₁_unique : ∀ f ∈ F, G.Adj p₁ f → f = f₁ := by
    intro f hf hadj
    by_contra hne
    exact hs.p₁notX₂ ⟨hs.p₁C, f, ⟨hf, hne⟩, hadj⟩
  have hf₁nbr : ∀ u ∈ C, G.Adj f₁ u → u = p₁ ∨ u = p₂ := by
    intro u hu hadj
    rcases hFCedge f₁ hf₁F u hu hadj with he | he
    · exact absurd he hfkne
    · exact he
  have hfkpi : ∀ u ∈ C, G.Adj fk u → pi u ≠ pi p₁ := by
    intro u hu hadj heq
    have huX : u ∈ Att G C (F \ {f₁}) :=
      ⟨hu, fk, ⟨hfkF, fun he => hfkne he.symm⟩, hadj.symm⟩
    exact hs.piNe (heq.symm.trans (hs.X₂par u huX))
  have hfkp₁ : ¬ G.Adj fk p₁ := by
    intro hadj
    exact hfkpi p₁ hs.p₁C hadj rfl

  -- Some neighbour of `fk` is outside the edge `p₁p₂`; otherwise every attachment of
  -- `F` would lie on that edge, contrary to the chosen nonadjacent pair `x₁,x₂`.
  obtain ⟨r₀, hr₀C, hfr₀, hr₀p₁, hr₀p₂⟩ :
      ∃ r : V, r ∈ C ∧ G.Adj fk r ∧ r ≠ p₁ ∧ r ≠ p₂ := by
    by_contra hc
    push Not at hc
    have hall : ∀ u ∈ Att G C F, u = p₁ ∨ u = p₂ := by
      intro u hu
      obtain ⟨huC, f, hfF, huf⟩ := hu
      rcases hFCedge f hfF u huC huf.symm with rfl | hup
      · by_cases hu1 : u = p₁
        · exact Or.inl hu1
        · exact Or.inr (hc u huC huf.symm hu1)
      · exact hup
    rcases hall x₁ h.att₁ with hx | hx <;> rcases hall x₂ h.att₂ with hy | hy
    · exact h.opp.1 (hx.trans hy.symm)
    · exact h.nadj (hx ▸ hy ▸ hs.adj12)
    · exact h.nadj (hx ▸ hy ▸ hs.adj12.symm)
    · exact h.opp.1 (hx.trans hy.symm)
  obtain ⟨r₀i, hr₀il, hr₀ie⟩ := cyc_surj hpos ((hDC r₀).mpr hr₀C)
  have hr₀i2 : 2 ≤ r₀i := by
    by_contra hc
    have hc' : r₀i = 0 ∨ r₀i = 1 := by omega
    rcases hc' with rfl | rfl
    · exact hr₀p₁ (hr₀ie.symm.trans hp₁)
    · exact hr₀p₂ (hr₀ie.symm.trans hp₂)

  -- First exclude the temporary case in which `p₂`, like `p₁`, sees only `f₁` in `F`.
  have hp₂att : ∃ g ∈ F \ {f₁}, G.Adj p₂ g := by
    by_contra hp₂no
    push Not at hp₂no
    have hp₂X₁ : p₂ ∈ Att G C (F \ {fk}) := by rw [hs.X₁eq]; simp
    obtain ⟨-, g₁, hg₁F, hp₂g₁⟩ := hp₂X₁
    have hg₁f₁ : g₁ = f₁ := by
      by_contra hne
      exact hp₂no g₁ ⟨hg₁F.1, hne⟩ hp₂g₁
    have hp₂f₁ : G.Adj p₂ f₁ := hg₁f₁ ▸ hp₂g₁
    have hp₂_unique : ∀ g ∈ F, G.Adj p₂ g → g = f₁ := by
      intro g hgF hadj
      by_contra hne
      exact hp₂no g ⟨hgF, hne⟩ hadj
    let N : ℕ → Prop := fun t => 2 ≤ t ∧ t < D.length ∧ G.Adj fk (cyc D hpos t)
    have hr₀N : N r₀i := ⟨hr₀i2, hr₀il, by rw [hr₀ie]; exact hfr₀⟩
    by_cases huniq : ∀ t : ℕ, N t → t = r₀i
    · -- With one `fk`-neighbour, the two holes on either side of it have incompatible
      -- parity (the rim itself is even).
      have hleft : IsHoleList G (S ++ (arc D hpos 1 r₀i).reverse) := by
        have hs1 : 1 ≤ r₀i - 1 := by omega
        have hs2 : (r₀i - 1) + 2 ≤ D.length := by omega
        simpa [Nat.sub_add_cancel (show 1 ≤ r₀i by omega)] using
          (OddWheelAttachmentClaim4.hole_of_path_and_arc hD hpos hs1 hs2
            hS hS2 (fun z hz hzD => hSnotC z hz ((hDC z).mp hzD)) (by
        intro z hz t ht
        have hti : 1 + t < D.length := by omega
        have huC : cyc D hpos (1 + t) ∈ C := hcycC _
        constructor
        · intro hadj
          rcases hFCedge z (hSmemF z hz) _ huC hadj with hzk | hu
          · subst z
            by_cases ht0 : t = 0
            · subst t
              rw [Nat.add_zero, hp₂] at hadj
              exact absurd (hp₂_unique fk hfkF hadj.symm) (fun e => hfkne e.symm)
            · have hNi : N (1 + t) := ⟨by omega, hti, hadj⟩
              have he := huniq (1 + t) hNi
              exact Or.inr ⟨rfl, by omega⟩
          · rcases hu with hu | hu
            · have he : cyc D hpos (1 + t) = cyc D hpos 0 := hu.trans hp₁.symm
              exact absurd he (hcycNe hti (by omega) (by omega))
            · have he : 1 + t = 1 := by
                have hm := cyc_inj hD hpos (hu.trans hp₂.symm)
                rw [Nat.mod_eq_of_lt hti, Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hm
                exact hm
              have hzf : z = f₁ := hp₂_unique z (hSmemF z hz) (by rw [← hu]; exact hadj.symm)
              exact Or.inl ⟨hzf, by omega⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, ht⟩)
          · simpa [hp₂] using hp₂f₁.symm
          · subst t
            have he : 1 + (r₀i - 1) = r₀i := by omega
            rw [he, hr₀ie]
            exact hfr₀))
      have hright : IsHoleList G
          (S.reverse ++ (arc D hpos r₀i (D.length - r₀i + 1)).reverse) := by
        have hs1 : 1 ≤ D.length - r₀i := by omega
        have hs2 : D.length - r₀i + 2 ≤ D.length := by omega
        refine OddWheelAttachmentClaim4.hole_of_path_and_arc hD hpos hs1 hs2
          (PathBasics.isPathFrom_reverse hS) (by simpa using hS2)
          (fun z hz hzD => hSnotC z (List.mem_reverse.mp hz) ((hDC z).mp hzD)) ?_
        intro z hz t ht
        have hzS : z ∈ S := List.mem_reverse.mp hz
        have htle : r₀i + t ≤ D.length := by omega
        have huC : cyc D hpos (r₀i + t) ∈ C := hcycC _
        constructor
        · intro hadj
          rcases hFCedge z (hSmemF z hzS) _ huC hadj with hzk | hu
          · subst z
            by_cases htend : t = D.length - r₀i
            · subst t
              have he : cyc D hpos (r₀i + (D.length - r₀i)) = p₁ := by
                rw [show r₀i + (D.length - r₀i) = D.length by omega]
                exact (cyc_congr hpos (by simp)).trans hp₁
              exact absurd (he ▸ hadj) hfkp₁
            · have hlt : r₀i + t < D.length := by omega
              have hNi : N (r₀i + t) := ⟨by omega, hlt, hadj⟩
              have he := huniq _ hNi
              exact Or.inl ⟨rfl, by omega⟩
          · rcases hu with hu | hu
            · have htend : t = D.length - r₀i := by
                by_contra hne
                have hlt : r₀i + t < D.length := by omega
                have he : cyc D hpos (r₀i + t) = cyc D hpos 0 := hu.trans hp₁.symm
                exact absurd he (hcycNe hlt (by omega) (by omega))
              have hzf : z = f₁ := hp₁_unique z (hSmemF z hzS)
                (by rw [← hu]; exact hadj.symm)
              exact Or.inr ⟨hzf, htend⟩
            · by_cases htend : t = D.length - r₀i
              · subst t
                have he : cyc D hpos (r₀i + (D.length - r₀i)) = p₁ := by
                  rw [show r₀i + (D.length - r₀i) = D.length by omega]
                  exact (cyc_congr hpos (by simp)).trans hp₁
                exact absurd (he.symm.trans hu) hs.adj12.ne
              · have hlt : r₀i + t < D.length := by omega
                have he : cyc D hpos (r₀i + t) = cyc D hpos 1 := hu.trans hp₂.symm
                exact absurd he (hcycNe hlt (by omega) (by omega))
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · rw [Nat.add_zero, hr₀ie]
            exact hfr₀
          · have he : cyc D hpos (r₀i + (D.length - r₀i)) = p₁ := by
              rw [show r₀i + (D.length - r₀i) = D.length by omega]
              exact (cyc_congr hpos (by simp)).trans hp₁
            rw [he]
            exact hs.adjp₁f₁.symm
      have heL := hBerge.1 _ hleft
      have heR := hBerge.1 _ hright
      have heC := hBerge.1 C hC
      simp only [SPGT.holeLength, List.length_append, List.length_reverse, arc_length,
        hSlen, hDn] at heL heR heC
      obtain ⟨a, ha⟩ := heL
      obtain ⟨b, hb⟩ := heR
      obtain ⟨c, hc⟩ := heC
      omega
    · by_cases hpair : ∃ a b : ℕ, N a ∧ N b ∧ a ≠ b ∧
          ¬ G.Adj (cyc D hpos a) (cyc D hpos b)
      · obtain ⟨a₀, b₀, haN, hbN, hab, habnadj⟩ := hpair
        obtain ⟨a, b, haN, hbN, hablt, habnadj⟩ :
            ∃ a b : ℕ, N a ∧ N b ∧ a < b ∧
              ¬ G.Adj (cyc D hpos a) (cyc D hpos b) := by
          rcases lt_or_gt_of_ne hab with hlt | hgt
          · exact ⟨a₀, b₀, haN, hbN, hlt, habnadj⟩
          · exact ⟨b₀, a₀, hbN, haN, hgt, fun h' => habnadj h'.symm⟩
        have ha2 := haN.1
        have hal := haN.2.1
        have hfa := haN.2.2
        have hb2 := hbN.1
        have hbl := hbN.2.1
        have hfb := hbN.2.2
        have hcycn : cyc D hpos D.length = p₁ :=
          (cyc_congr hpos (by simp)).trans hp₁
        let A : List V := arc D hpos 1 a
        let B : List V := (arc D hpos b (D.length - b + 1)).reverse
        let T : List V := S.dropLast
        let q : V := S[S.length - 2]'(by omega)
        have hA : IsPathFrom G A p₂ (cyc D hpos a) := by
          have hh := arc_isPathFrom hD hpos (a := 1) (L := a) (by omega) (by omega)
          rw [show 1 + a - 1 = a by omega, hp₂] at hh
          exact hh
        have hB : IsPathFrom G B p₁ (cyc D hpos b) := by
          have hh := arc_isPathFrom hD hpos (a := b) (L := D.length - b + 1)
            (by omega) (by omega)
          have he : b + (D.length - b + 1) - 1 = D.length := by omega
          rw [he, hcycn] at hh
          exact PathBasics.isPathFrom_reverse hh
        have hT : IsPathFrom G T f₁ q := by
          simpa only [T, q] using pathFrom_dropLast hS hS2
        have hTsub : ∀ z ∈ T, z ∈ S := fun z hz => List.mem_of_mem_dropLast hz
        have hfkT : fk ∉ T := by
          intro hmem
          have hh := (PathBasics.mem_dropLast_iff (PathBasics.path_nodup hS.1)
            (PathBasics.path_ne_nil hS.1)).mp hmem
          exact hh.2 (by
            rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
            exact hS.2.2.symm)
        have hBT : ∀ z ∈ B, z ∉ T := by
          intro z hzB hzT
          exact hSnotC z (hTsub z hzT) ((hDC z).mp (by
            rw [List.mem_reverse] at hzB
            obtain ⟨t, ht, rfl⟩ := (mem_arc hpos).mp hzB
            exact cyc_mem hpos _))
        have hAT : ∀ z ∈ A, z ∉ T := by
          intro z hzA hzT
          exact hSnotC z (hTsub z hzT) ((hDC z).mp (by
            obtain ⟨t, ht, rfl⟩ := (mem_arc hpos).mp hzA
            exact cyc_mem hpos _))
        have hBA : ∀ z ∈ B, z ∉ A := by
          intro z hzB hzA
          rw [List.mem_reverse] at hzB
          obtain ⟨t, ht, htz⟩ := (mem_arc hpos).mp hzB
          obtain ⟨s, hs', hsz⟩ := (mem_arc hpos).mp hzA
          have hit : b + t ≤ D.length := by omega
          have his : 1 + s < D.length := by omega
          by_cases hend : b + t = D.length
          · have he0 : cyc D hpos (b + t) = cyc D hpos 0 := cyc_congr hpos (by simp [hend])
            have hm := cyc_inj hD hpos (he0.symm.trans (htz.trans hsz.symm))
            rw [Nat.zero_mod, Nat.mod_eq_of_lt his] at hm
            omega
          · have hit' : b + t < D.length := by omega
            have hm := cyc_inj hD hpos (htz.trans hsz.symm)
            rw [Nat.mod_eq_of_lt hit', Nat.mod_eq_of_lt his] at hm
            omega
        have hBTcross : ∀ x ∈ B, ∀ z ∈ T,
            (G.Adj x z ↔ x = p₁ ∧ z = f₁) := by
          intro x hx z hz
          have hzS := hTsub z hz
          constructor
          · intro hadj
            rcases hFCedge z (hSmemF z hzS) x (hDC x |>.mp (by
              rw [List.mem_reverse] at hx
              obtain ⟨t, ht, rfl⟩ := (mem_arc hpos).mp hx
              exact cyc_mem hpos _)) hadj.symm with hzk | hxp
            · exact absurd (hzk ▸ hz) hfkT
            · rcases hxp with hxp | hxp
              · exact ⟨hxp, hp₁_unique z (hSmemF z hzS) (hxp ▸ hadj)⟩
              · exfalso
                rw [List.mem_reverse] at hx
                obtain ⟨t, ht, htx⟩ := (mem_arc hpos).mp hx
                have hit : b + t ≤ D.length := by omega
                by_cases he : b + t = D.length
                · have hx1 : x = p₁ := by rw [← htx, he, hcycn]
                  exact hs.adj12.ne (hx1.symm.trans hxp)
                · have hit' : b + t < D.length := by omega
                  have hm := cyc_inj hD hpos (htx.trans (hxp.trans hp₂.symm))
                  rw [Nat.mod_eq_of_lt hit', Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hm
                  omega
          · rintro ⟨rfl, rfl⟩
            exact hs.adjp₁f₁
        have hATcross : ∀ x ∈ A, ∀ z ∈ T,
            (G.Adj x z ↔ x = p₂ ∧ z = f₁) := by
          intro x hx z hz
          have hzS := hTsub z hz
          constructor
          · intro hadj
            have hxC : x ∈ C := by
              obtain ⟨t, ht, rfl⟩ := (mem_arc hpos).mp hx
              exact hcycC _
            rcases hFCedge z (hSmemF z hzS) x hxC hadj.symm with hzk | hxp
            · exact absurd (hzk ▸ hz) hfkT
            · rcases hxp with hxp | hxp
              · exfalso
                obtain ⟨t, ht, htx⟩ := (mem_arc hpos).mp hx
                have hit : 1 + t < D.length := by omega
                have hm := cyc_inj hD hpos (htx.trans (hxp.trans hp₁.symm))
                rw [Nat.mod_eq_of_lt hit, Nat.zero_mod] at hm
                omega
              · exact ⟨hxp, hp₂_unique z (hSmemF z hzS) (hxp ▸ hadj)⟩
          · rintro ⟨rfl, rfl⟩
            exact hp₂f₁
        have hBAcross : ∀ x ∈ B, ∀ y ∈ A,
            (G.Adj x y ↔ x = p₁ ∧ y = p₂) := by
          intro x hx y hy
          rw [List.mem_reverse] at hx
          obtain ⟨t, ht, htx⟩ := (mem_arc hpos).mp hx
          obtain ⟨s, hs', hsy⟩ := (mem_arc hpos).mp hy
          have hit : b + t ≤ D.length := by omega
          have his : 1 + s < D.length := by omega
          constructor
          · intro hadj
            by_cases hend : b + t = D.length
            · have hx1 : x = p₁ := by rw [← htx, hend, hcycn]
              have hi := cyc_adj_index hD hpos (show 0 < D.length by omega) his
                (by simpa only [hp₁, hsy, hx1] using hadj)
              have hsi : 1 + s = 1 := by rcases hi with h | h | h | h <;> omega
              have hy2 : y = p₂ := by rw [← hsy, show 1 + s = 1 by omega, hp₂]
              exact ⟨hx1, hy2⟩
            · have hit' : b + t < D.length := by omega
              have hi := cyc_adj_index hD hpos hit' his (by rw [htx, hsy]; exact hadj)
              have hbound : b + t = b ∧ 1 + s = a ∧ b = a + 1 := by
                rcases hi with h | h | h | h <;> omega
              exfalso
              apply habnadj
              rw [← hbound.2.1, ← hbound.1, hsy, htx]
              exact hadj.symm
          · rintro ⟨rfl, rfl⟩
            exact hs.adj12
        have hqT : q ∈ T := (PathBasics.isPathFrom_ends_mem hT).2
        have hfkq : G.Adj fk q := by
          have hadj := PathBasics.path_adj_succ hS.1
            (i := S.length - 2) (show S.length - 2 + 1 < S.length by omega)
          have hlast : S[S.length - 1]'(by omega) = fk :=
            PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)
          simpa only [q, show S.length - 2 + 1 = S.length - 1 by omega, hlast] using hadj.symm
        have hlink : Workspace.Types.RousselRubio.SPGT.VertexCanBeLinkedOntoTriangle
            G fk p₁ p₂ f₁ := by
          refine ⟨B, A, T, ⟨hB.1, hA.1, hT.1⟩,
            ⟨hBA, hBT, hAT⟩, ?_, ⟨hBAcross, hBTcross, hATcross⟩, ?_⟩
          · exact ⟨Or.inl hB.2.1, Or.inl hA.2.1, Or.inl hT.2.1⟩
          · exact ⟨⟨cyc D hpos b, (PathBasics.isPathFrom_ends_mem hB).2, hfb⟩,
              ⟨cyc D hpos a, (PathBasics.isPathFrom_ends_mem hA).2, hfa⟩,
              ⟨q, hqT, hfkq⟩⟩
        rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hBerge fk p₁ p₂ f₁ hlink with
          h12 | h13 | h23
        · exact hfkp₁ h12.1
        · exact hfkp₁ h13.1
        · exact hp₂no fk ⟨hfkF, fun e => hfkne e.symm⟩ h23.1.symm
      · have hNadj : ∀ {s t : ℕ}, N s → N t → s ≠ t →
            G.Adj (cyc D hpos s) (cyc D hpos t) := by
          intro s t hsN htN hst
          by_contra hnadj
          exact hpair ⟨s, t, hsN, htN, hst, hnadj⟩
        push Not at huniq
        obtain ⟨r₁, hr₁N, hr₁ne⟩ := huniq
        have hNtwo : ∀ t : ℕ, N t → t = r₀i ∨ t = r₁ := by
          intro t htN
          by_cases ht0 : t = r₀i
          · exact Or.inl ht0
          by_cases ht1 : t = r₁
          · exact Or.inr ht1
          exfalso
          exact no_triangle hD hpos hr₀N.2.1 hr₁N.2.1 htN.2.1 hr₁ne.symm
            (Ne.symm ht0) (Ne.symm ht1) (hNadj hr₀N hr₁N hr₁ne.symm)
            (hNadj hr₀N htN (Ne.symm ht0)) (hNadj hr₁N htN (Ne.symm ht1))
        obtain ⟨a, b, haN, hbN, hablt, hNab⟩ :
            ∃ a b : ℕ, N a ∧ N b ∧ a < b ∧ (∀ t : ℕ, N t → t = a ∨ t = b) := by
          rcases lt_or_gt_of_ne hr₁ne with hlt | hgt
          · refine ⟨r₁, r₀i, hr₁N, hr₀N, hlt, ?_⟩
            intro t ht
            rcases hNtwo t ht with h | h
            · exact Or.inr h
            · exact Or.inl h
          · exact ⟨r₀i, r₁, hr₀N, hr₁N, hgt, hNtwo⟩
        have habadj : G.Adj (cyc D hpos a) (cyc D hpos b) :=
          hNadj haN hbN (ne_of_lt hablt)
        have hbsucc : b = a + 1 := by
          have hi := cyc_adj_index hD hpos haN.2.1 hbN.2.1 habadj
          rcases hi with hi | hi | hi | hi <;> omega
        have hSD : ∀ z ∈ S, z ∉ D := by
          intro z hzS hzD
          exact hSnotC z hzS ((hDC z).mp hzD)
        have hcross : ∀ p ∈ S, ∀ q ∈ D, (G.Adj p q ↔
            ((p = f₁ ∧ (q = cyc D hpos 0 ∨ q = cyc D hpos 1)) ∨
              (p = fk ∧ (q = cyc D hpos a ∨ q = cyc D hpos (a + 1))))) := by
          intro p hpS q hqD
          have hpF := hSmemF p hpS
          have hqC : q ∈ C := (hDC q).mp hqD
          constructor
          · intro hadj
            rcases hFCedge p hpF q hqC hadj with hpfk | hqend
            · refine Or.inr ⟨hpfk, ?_⟩
              have hadj' : G.Adj fk q := hpfk ▸ hadj
              obtain ⟨t, ht, htq⟩ := cyc_surj hpos hqD
              have hfkt : G.Adj fk (cyc D hpos t) := by rw [htq]; exact hadj'
              have ht0 : t ≠ 0 := by
                intro he
                rw [he, hp₁] at hfkt
                exact hfkp₁ hfkt
              have ht1 : t ≠ 1 := by
                intro he
                rw [he, hp₂] at hfkt
                exact hp₂no fk ⟨hfkF, fun e => hfkne e.symm⟩ hfkt.symm
              have htN : N t := ⟨by omega, ht, hfkt⟩
              rcases hNab t htN with hta | htb
              · exact Or.inl (by rw [← htq, hta])
              · exact Or.inr (by rw [← htq, htb, hbsucc])
            · rcases hqend with hq1 | hq2
              · refine Or.inl ⟨hp₁_unique p hpF (hq1 ▸ hadj.symm), Or.inl ?_⟩
                exact hq1.trans hp₁.symm
              · refine Or.inl ⟨hp₂_unique p hpF (hq2 ▸ hadj.symm), Or.inr ?_⟩
                exact hq2.trans hp₂.symm
          · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
            · rcases hq with rfl | rfl
              · rw [hp₁]
                exact hs.adjp₁f₁.symm
              · rw [hp₂]
                exact hp₂f₁.symm
            · rcases hq with rfl | rfl
              · exact haN.2.2
              · rw [← hbsucc]
                exact hbN.2.2
        have hprism := OddWheelAttachmentClaim2.long_prism hD hpos hD6
          (γ := a) haN.1 (by omega) hS hfkne hSD hcross
        exact h.inF6.1.2.1 hprism
  obtain ⟨g₂, hg₂F, hp₂g₂⟩ := hp₂att

  -- The paper's path `R₂`, from `p₂` to `f_k` with interior in `F \ {f₁}`.
  have hF₂conn : ConnectedSet G (F \ {f₁}) := by
    rw [h.interiorEq, ← fst_getElem h]
    exact connectedSet_sdiff_first h.path.1 h.len
  have hF₂plus : ConnectedSet G ((F \ {f₁}) ∪ {p₂}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hF₂conn
      ⟨g₂, hg₂F, hp₂g₂⟩
  have hp₂notF : p₂ ∉ F := fun hp₂F => h.notC p₂ hp₂F hs.p₂C
  have hfkF₂ : fk ∈ F \ {f₁} := ⟨hfkF, fun e => hfkne e.symm⟩
  obtain ⟨R₂, hR₂, hR₂mem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hF₂plus
      (show p₂ ∈ (F \ {f₁}) ∪ {p₂} from Or.inr rfl) (Or.inl hfkF₂)
  have hR₂shape : ∀ z ∈ R₂, z = p₂ ∨ z ∈ F \ {f₁} := by
    intro z hz
    rcases hR₂mem z hz with hzF | hz2
    · exact Or.inr hzF
    · exact Or.inl hz2
  have hp₂nefk : p₂ ≠ fk := by
    intro he
    exact hp₂notF (he ▸ hfkF)
  have hR₂len : 2 ≤ R₂.length := by
    have hposR := PathBasics.path_length_pos hR₂.1
    have h0 : R₂[0]'hposR = p₂ :=
      PathBasics.getElem_zero_of_head? hR₂.2.1 hposR
    have hl : R₂[R₂.length - 1]'(by omega) = fk :=
      PathBasics.getElem_last_of_getLast? hR₂.2.2 hposR
    by_contra hc
    have hone : R₂.length = 1 := by omega
    exact hp₂nefk (by rw [← h0, ← hl]; congr 1; omega)

  -- Choose the neighbour of `f_k` furthest towards `p_n`; this gives `Q₁`.
  let J : ℕ → Prop := fun t => 2 ≤ t ∧ t < D.length ∧ G.Adj fk (cyc D hpos t)
  have hr₀J : J r₀i := ⟨hr₀i2, hr₀il, by rw [hr₀ie]; exact hfr₀⟩
  obtain ⟨j, hjJ, hjmax⟩ := ExtremalChoice.exists_max_nat J (fun t => t) D.length
    (fun t ht => Nat.le_of_lt ht.2.1) ⟨r₀i, hr₀J⟩
  have hj2 : 2 ≤ j := hjJ.1
  have hjn : j < D.length := hjJ.2.1
  have hfkj : G.Adj fk (cyc D hpos j) := hjJ.2.2
  have hcycn : cyc D hpos D.length = p₁ :=
    (cyc_congr hpos (by simp)).trans hp₁
  have hpnC : cyc D hpos (D.length - 1) ∈ C := hcycC _
  let A₁ : List V := arc D hpos j (D.length - j)
  have hA₁ : IsPathFrom G A₁ (cyc D hpos j) (cyc D hpos (D.length - 1)) := by
    have hh := arc_isPathFrom hD hpos (a := j) (L := D.length - j) (by omega) (by omega)
    rw [show j + (D.length - j) - 1 = D.length - 1 by omega] at hh
    exact hh
  have hA₁mem : ∀ z ∈ A₁, ∃ t : ℕ, t < D.length - j ∧ cyc D hpos (j + t) = z := by
    intro z hz
    exact (mem_arc hpos).mp hz
  have hfkA₁ : fk ∉ A₁ := by
    intro hmem
    obtain ⟨t, ht, hte⟩ := hA₁mem fk hmem
    exact h.notC fk hfkF (by rw [← hte]; exact hcycC _)
  have hQ₁ : IsPathFrom G (fk :: A₁) fk (cyc D hpos (D.length - 1)) := by
    refine PathAttach.isPathFrom_cons hA₁ hfkj hfkA₁ ?_
    intro z hz hzne hadj
    obtain ⟨t, ht, hte⟩ := hA₁mem z hz
    have htJ : J (j + t) := ⟨by omega, by omega, by rw [hte]; exact hadj⟩
    have hle := hjmax (j + t) htJ
    have ht0 : t = 0 := by omega
    exact hzne (by rw [← hte, ht0, Nat.add_zero])

  -- Closing `R₁` with the rim arc of `Q₁` is the hole used in the parity computation.
  have hH₁ : IsHoleList G
      (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) := by
    refine OddWheelAttachmentClaim4.hole_of_path_and_arc hD hpos
      (show 1 ≤ D.length - j by omega) (show D.length - j + 2 ≤ D.length by omega)
      (PathBasics.isPathFrom_reverse hS) (by simpa using hS2)
      (fun z hz hzD => hSnotC z (List.mem_reverse.mp hz) ((hDC z).mp hzD)) ?_
    intro z hz t ht
    have hzS : z ∈ S := List.mem_reverse.mp hz
    have htle : j + t ≤ D.length := by omega
    have huC : cyc D hpos (j + t) ∈ C := hcycC _
    constructor
    · intro hadj
      rcases hFCedge z (hSmemF z hzS) _ huC hadj with hzk | hu
      · subst z
        by_cases htend : t = D.length - j
        · subst t
          rw [show j + (D.length - j) = D.length by omega, hcycn] at hadj
          exact absurd hadj hfkp₁
        · have hJ : J (j + t) := ⟨by omega, by omega, hadj⟩
          have hle := hjmax (j + t) hJ
          exact Or.inl ⟨rfl, by omega⟩
      · rcases hu with hu | hu
        · have htend : t = D.length - j := by
            by_contra hne
            have hlt : j + t < D.length := by omega
            have he : cyc D hpos (j + t) = cyc D hpos 0 := hu.trans hp₁.symm
            exact absurd he (hcycNe hlt (by omega) (by omega))
          have hzf : z = f₁ := hp₁_unique z (hSmemF z hzS)
            (by rw [← hu]; exact hadj.symm)
          exact Or.inr ⟨hzf, htend⟩
        · by_cases htend : t = D.length - j
          · subst t
            have he : cyc D hpos (j + (D.length - j)) = p₁ := by
              rw [show j + (D.length - j) = D.length by omega, hcycn]
            exact absurd (he.symm.trans hu) hs.adj12.ne
          · have hlt : j + t < D.length := by omega
            have he : cyc D hpos (j + t) = cyc D hpos 1 := hu.trans hp₂.symm
            exact absurd he (hcycNe hlt (by omega) (by omega))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hfkj
      · rw [show j + (D.length - j) = D.length by omega, hcycn]
        exact hs.adjp₁f₁.symm
  have hcycEven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge h.wheel
  have hstepD : ∀ u v : V, u ∈ D → v ∈ D → G.Adj u v →
      (pi u ≠ pi v ↔ EdgeComplete G Y u v) := by
    intro u v hu hv huv
    exact OddWheelAttachmentYCount.parity_step hC hcycEven hs.piSpec
      ((hDC u).mp hu) ((hDC v).mp hv) huv
  have hpij : pi (cyc D hpos j) ≠ pi (cyc D hpos (j + (D.length - j))) := by
    rw [show j + (D.length - j) = D.length by omega, hcycn]
    exact hfkpi _ (hcycC j) hfkj
  obtain ⟨hHpar, -, c₁, d₁, hHset, hc₁d₁, hadjc₁d₁⟩ :=
    OddWheelAttachmentYCount.hole_yData hD hpos hBerge hYanti
      (fun z hzD => hCY z ((hDC z).mp hzD)) hs.pi2 hstepD
      (show 1 ≤ D.length - j by omega) (show D.length - j + 2 ≤ D.length by omega)
      (fun z hz => hSnotY z (List.mem_reverse.mp hz))
      (fun z hz => hSnc z (List.mem_reverse.mp hz)) hpij hH₁
  have hp₁H : p₁ ∈ (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) := by
    apply List.mem_append.mpr
    right
    rw [List.mem_reverse, mem_arc hpos]
    exact ⟨D.length - j, by omega, by rw [show j + (D.length - j) = D.length by omega, hcycn]⟩
  have hp₁pair : p₁ = c₁ ∨ p₁ = d₁ := by
    have hm : p₁ ∈ {w : V | w ∈ (S.reverse ++
        (arc D hpos j (D.length - j + 1)).reverse) ∧ VertexComplete G w Y} :=
      ⟨hp₁H, hs.yc1⟩
    rw [hHset] at hm
    simpa using hm
  have hother_is_pn : ∀ q : V,
      q ∈ (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) →
      VertexComplete G q Y → q ≠ p₁ → G.Adj p₁ q →
      q = cyc D hpos (D.length - 1) := by
    intro q hqH hqY hqp₁ hadj
    rcases List.mem_append.mp hqH with hqS | hqA
    · exact absurd hqY (hSnc q (List.mem_reverse.mp hqS))
    · rw [List.mem_reverse] at hqA
      obtain ⟨t, ht, htq⟩ := (mem_arc hpos).mp hqA
      by_cases htend : t = D.length - j
      · exfalso
        apply hqp₁
        rw [← htq, htend, show j + (D.length - j) = D.length by omega, hcycn]
      · have hit : j + t < D.length := by omega
        have hi := cyc_adj_index hD hpos (show 0 < D.length by omega) hit
          (by simpa only [hp₁, htq] using hadj)
        have he : j + t = D.length - 1 := by
          rcases hi with hi | hi | hi | hi <;> omega
        rw [← htq, he]
  have hHcomplete :
      {w : V | w ∈ (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) ∧
        VertexComplete G w Y} = {p₁, cyc D hpos (D.length - 1)} := by
    rcases hp₁pair with hp₁c | hp₁d
    · have hdset : d₁ ∈ {w : V | w ∈ (S.reverse ++
          (arc D hpos j (D.length - j + 1)).reverse) ∧ VertexComplete G w Y} := by
        rw [hHset]
        exact Or.inr rfl
      have hdpn := hother_is_pn d₁ hdset.1 hdset.2
        (fun he => hc₁d₁ (hp₁c.symm.trans he.symm)) (by rw [hp₁c]; exact hadjc₁d₁)
      rw [hHset, ← hp₁c, hdpn]
    · have hcset : c₁ ∈ {w : V | w ∈ (S.reverse ++
          (arc D hpos j (D.length - j + 1)).reverse) ∧ VertexComplete G w Y} := by
        rw [hHset]
        exact Or.inl rfl
      have hcpn := hother_is_pn c₁ hcset.1 hcset.2
        (fun he => hc₁d₁ (he.trans hp₁d)) (by rw [hp₁d]; exact hadjc₁d₁.symm)
      rw [hHset, ← hp₁d, hcpn, Set.pair_comm]
  have hpnY : VertexComplete G (cyc D hpos (D.length - 1)) Y := by
    have hpnH : cyc D hpos (D.length - 1) ∈
        (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) := by
      apply List.mem_append.mpr
      right
      rw [List.mem_reverse, mem_arc hpos]
      exact ⟨D.length - 1 - j, by omega, by congr 1 <;> omega⟩
    have hm : cyc D hpos (D.length - 1) ∈
        ({p₁, cyc D hpos (D.length - 1)} : Set V) := by simp
    rw [← hHcomplete] at hm
    exact hm.2

  -- There is a complete rim vertex strictly between `p₃` and `p_n`.  If not, the
  -- three already complete consecutive rim vertices would force an odd number of
  -- complete edges around the wheel.
  obtain ⟨s, hs3, hsn, hsY⟩ : ∃ s : ℕ, 3 ≤ s ∧ s + 2 ≤ D.length ∧
      VertexComplete G (cyc D hpos s) Y := by
    by_contra hcon
    have hnoMid : ∀ t : ℕ, 3 ≤ t → t + 2 ≤ D.length →
        ¬ VertexComplete G (cyc D hpos t) Y := by
      intro t ht3 htn htY
      exact hcon ⟨t, ht3, htn, htY⟩
    have hadjsucc : ∀ t : ℕ, G.Adj (cyc D hpos t) (cyc D hpos (t + 1)) := by
      intro t
      exact (cyc_adj hD hpos t (t + 1)).mpr (Or.inl rfl)
    have hadjwrap : G.Adj (cyc D hpos 0) (cyc D hpos (D.length - 1)) := by
      refine (cyc_adj hD hpos 0 (D.length - 1)).mpr (Or.inr ?_)
      simp only [Nat.zero_mod]
      rw [show D.length - 1 + 1 = D.length by omega, Nat.mod_self]
    have hpi01 : pi (cyc D hpos 0) ≠ pi (cyc D hpos 1) :=
      (hstepD _ _ (cyc_mem hpos _) (cyc_mem hpos _) (hadjsucc 0)).mpr
        ⟨hadjsucc 0, by simpa only [hp₁] using hs.yc1,
          by simpa only [hp₂] using hs.yc2⟩
    have hpi0n : pi (cyc D hpos 0) ≠ pi (cyc D hpos (D.length - 1)) :=
      (hstepD _ _ (cyc_mem hpos _) (cyc_mem hpos _) hadjwrap).mpr
        ⟨hadjwrap, by simpa only [hp₁] using hs.yc1, hpnY⟩
    have htel := parity_telescope (G := G) (C := D) (Y := Y) (π := pi)
      hs.pi2 hstepD (fun t => cyc D hpos t) 2 (D.length - 1) (by omega)
      (fun t _ _ => cyc_mem hpos t) (fun t _ _ => hadjsucc t)
    have hempty : (Finset.Ico 2 (D.length - 1)).filter
        (fun t => EdgeComplete G Y (cyc D hpos t) (cyc D hpos (t + 1))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht
      obtain ⟨⟨ht2, htn⟩, htE⟩ := ht
      by_cases he : t = 2
      · exact hnoMid (t + 1) (by omega) (by omega) htE.2.2
      · exact hnoMid t (by omega) (by omega) htE.2.1
    rw [hempty] at htel
    simp only [Finset.card_empty, Nat.zero_add] at htel
    have hnotY2 : ¬ VertexComplete G (cyc D hpos 2) Y := by
      intro hY2
      have hpi12 : pi (cyc D hpos 1) ≠ pi (cyc D hpos 2) :=
        (hstepD _ _ (cyc_mem hpos _) (cyc_mem hpos _) (hadjsucc 1)).mpr
          ⟨hadjsucc 1, by simpa only [hp₂] using hs.yc2, hY2⟩
      have h0 := hs.pi2 (cyc D hpos 0)
      have h1 := hs.pi2 (cyc D hpos 1)
      have h2 := hs.pi2 (cyc D hpos 2)
      have hn := hs.pi2 (cyc D hpos (D.length - 1))
      omega
    have hall : ∀ z : V, z ∈ C → VertexComplete G z Y →
        z = p₁ ∨ z = p₂ ∨ z = cyc D hpos (D.length - 1) := by
      intro z hzC hzY
      obtain ⟨t, ht, htz⟩ := cyc_surj hpos ((hDC z).mpr hzC)
      by_cases ht0 : t = 0
      · exact Or.inl (by rw [← htz, ht0, hp₁])
      by_cases ht1 : t = 1
      · exact Or.inr (Or.inl (by rw [← htz, ht1, hp₂]))
      by_cases htn : t = D.length - 1
      · exact Or.inr (Or.inr (by rw [← htz, htn]))
      exfalso
      by_cases ht2 : t = 2
      · apply hnotY2
        rw [← htz] at hzY
        simpa only [ht2] using hzY
      · exact hnoMid t (by omega) (by omega) (by rw [htz]; exact hzY)
    obtain ⟨A, B, E, K, hAC, hBC, hEC, hKC, hAY, hBY, hEY, hKY,
        hAB, hAE, hAK, hBE, hBK, hEK⟩ := Thm162SetupBasics.four_yComplete h.wheel
    exact Thm162SetupBasics.not_four_in_three (hall A hAC hAY) (hall B hBC hBY)
      (hall E hEC hEY) (hall K hKC hKY) hAB hAE hAK hBE hBK hEK
  have hslt : s < D.length := by omega
  have hsj : s < j := by
    by_contra hnot
    have hsH : cyc D hpos s ∈
        (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) := by
      apply List.mem_append.mpr
      right
      rw [List.mem_reverse, mem_arc hpos]
      exact ⟨s - j, by omega, by congr 1 <;> omega⟩
    have hm : cyc D hpos s ∈
        {w : V | w ∈ (S.reverse ++ (arc D hpos j (D.length - j + 1)).reverse) ∧
          VertexComplete G w Y} := ⟨hsH, hsY⟩
    rw [hHcomplete] at hm
    have hm' : cyc D hpos s = p₁ ∨
        cyc D hpos s = cyc D hpos (D.length - 1) := by simpa using hm
    rcases hm' with he | he
    · exact (hcycNe hslt (by omega) (by omega)) (he.trans hp₁.symm)
    · have hi := cyc_inj hD hpos he
      rw [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt (show D.length - 1 < D.length by omega)] at hi
      omega
  have hj4 : 4 ≤ j := by omega

  -- The path `p₂-R₂-f_k-Q₁-p_n` is induced; `s < j` is exactly what excludes
  -- the possible chord from `p₂` into the first rim vertex of `Q₁`.
  have hA₁len : A₁.length = D.length - j := by
    simp only [A₁, arc_length]
  have hR₂A₁disj : ∀ x ∈ R₂, x ∉ A₁ := by
    intro x hxR hxA
    obtain ⟨t, ht, htx⟩ := hA₁mem x hxA
    rcases hR₂shape x hxR with rfl | hxF
    · have hi := cyc_inj hD hpos (htx.trans hp₂.symm)
      rw [Nat.mod_eq_of_lt (show j + t < D.length by omega),
        Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hi
      omega
    · exact h.notC x hxF.1 (by rw [← htx]; exact hcycC _)
  have hR₂A₁cross : ∀ x ∈ R₂, ∀ y ∈ A₁,
      (G.Adj x y ↔ x = fk ∧ y = cyc D hpos j) := by
    intro x hxR y hyA
    obtain ⟨t, ht, hty⟩ := hA₁mem y hyA
    have he : j + t < D.length := by omega
    constructor
    · intro hadj
      rcases hR₂shape x hxR with rfl | hxF
      · have hi := cyc_adj_index hD hpos (show 1 < D.length by omega) he
          (by simpa only [hp₂, hty] using hadj)
        rcases hi with hi | hi | hi | hi <;> omega
      · rcases hFCedge x hxF.1 y (by rw [← hty]; exact hcycC _) hadj with hxfk | hyend
        · refine ⟨hxfk, ?_⟩
          have hJ : J (j + t) := ⟨by omega, he, by
            rw [hxfk] at hadj
            rw [hty]
            exact hadj⟩
          have hle := hjmax (j + t) hJ
          have ht0 : t = 0 := by omega
          rw [← hty, ht0, Nat.add_zero]
        · rcases hyend with hy1 | hy2
          · have hi := cyc_inj hD hpos (hty.trans (hy1.trans hp₁.symm))
            rw [Nat.mod_eq_of_lt he, Nat.zero_mod] at hi
            omega
          · have hi := cyc_inj hD hpos (hty.trans (hy2.trans hp₂.symm))
            rw [Nat.mod_eq_of_lt he,
              Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hi
            omega
    · rintro ⟨rfl, rfl⟩
      exact hfkj
  have hW₂₁ : IsPathFrom G (R₂ ++ A₁) p₂ (cyc D hpos (D.length - 1)) :=
    PathGlue.glue_path hR₂ hA₁ hR₂A₁disj hR₂A₁cross
  have hW₂₁Y : ∀ x ∈ R₂ ++ A₁, x ∉ Y := by
    intro x hx
    rcases List.mem_append.mp hx with hxR | hxA
    · rcases hR₂shape x hxR with rfl | hxF
      · simpa only [hp₂] using hcycY 1
      · exact h.notY x hxF.1
    · obtain ⟨t, ht, htx⟩ := hA₁mem x hxA
      rw [← htx]
      exact hcycY (j + t)
  have hW₂₁int : ∀ x ∈ SPGT.interior (R₂ ++ A₁),
      ¬ VertexComplete G x Y ∧ ¬ G.Adj p₁ x := by
    intro x hx
    obtain ⟨hxW, hxne2, hxnen⟩ := (PathBasics.mem_interior_iff_of_pathFrom hW₂₁).mp hx
    rcases List.mem_append.mp hxW with hxR | hxA
    · rcases hR₂shape x hxR with hxp₂ | hxF
      · exact absurd hxp₂ hxne2
      · refine ⟨h.notComplete x hxF.1, ?_⟩
        intro hadj
        exact hxF.2 (hp₁_unique x hxF.1 hadj)
    · obtain ⟨t, ht, htx⟩ := hA₁mem x hxA
      have he : j + t < D.length := by omega
      refine ⟨?_, ?_⟩
      · intro hxY
        have hxH : x ∈ (S.reverse ++
            (arc D hpos j (D.length - j + 1)).reverse) := by
          apply List.mem_append.mpr
          right
          rw [List.mem_reverse, mem_arc hpos]
          exact ⟨t, by omega, htx⟩
        have hm : x ∈ {w : V | w ∈ (S.reverse ++
            (arc D hpos j (D.length - j + 1)).reverse) ∧ VertexComplete G w Y} :=
          ⟨hxH, hxY⟩
        rw [hHcomplete] at hm
        have hm' : x = p₁ ∨ x = cyc D hpos (D.length - 1) := by simpa using hm
        rcases hm' with hx1 | hxn
        · have hi := cyc_inj hD hpos (htx.trans (hx1.trans hp₁.symm))
          rw [Nat.mod_eq_of_lt he, Nat.zero_mod] at hi
          omega
        · exact hxnen hxn
      · intro hadj
        have hi := cyc_adj_index hD hpos (show 0 < D.length by omega) he
          (by simpa only [hp₁, htx] using hadj)
        have hend : j + t = D.length - 1 := by
          rcases hi with hi | hi | hi | hi <;> omega
        apply hxnen
        rw [← htx, hend]
  have hW₂₁even : Even (pathLength (R₂ ++ A₁)) := by
    refine Thm162ClaimFiveAux.even_of_clean hBerge hYanti hW₂₁ ?_ hW₂₁Y
      hs.yc2 hpnY (fun x hx => (hW₂₁int x hx).1) hs.yc1
      (fun x hx => (hW₂₁int x hx).2)
    simp only [List.length_append, hA₁len]
    omega

  -- The other ingredient for `Q₂`: `f_k` has a neighbour away from the three
  -- boundary vertices `p₁,p₂,p_n`.  Otherwise the attachment pair supplied by
  -- the configuration forces the neighbour to be `p₃`, while maximality makes
  -- `p_n` another neighbour, closing an odd hole.
  have hadjwrap : G.Adj p₁ (cyc D hpos (D.length - 1)) := by
    rw [← hp₁]
    refine (cyc_adj hD hpos 0 (D.length - 1)).mpr (Or.inr ?_)
    simp only [Nat.zero_mod]
    rw [show D.length - 1 + 1 = D.length by omega, Nat.mod_self]
  have hp₂nepn : p₂ ≠ cyc D hpos (D.length - 1) := by
    rw [← hp₂]
    exact hcycNe (by omega) (by omega) (by omega)
  have hpip₂pn : pi p₂ = pi (cyc D hpos (D.length - 1)) := by
    have hpi0n : pi p₁ ≠ pi (cyc D hpos (D.length - 1)) := by
      have hh := (hstepD p₁ (cyc D hpos (D.length - 1))
        ((hDC p₁).mpr hs.p₁C) (cyc_mem hpos _) hadjwrap).mpr
          ⟨hadjwrap, hs.yc1, hpnY⟩
      exact hh
    have h0 := hs.pi2 p₁
    have h1 := hs.pi2 p₂
    have hn := hs.pi2 (cyc D hpos (D.length - 1))
    have h01 := hs.piNe
    omega
  have hsame₂n : SameWheelParity G C Y p₂ (cyc D hpos (D.length - 1)) :=
    (hs.piSpec p₂ (cyc D hpos (D.length - 1)) hs.p₂C hpnC hp₂nepn).mpr hpip₂pn
  obtain ⟨u₀, hu₀Att, hu₀p₁, hu₀p₂, hu₀pn⟩ :
      ∃ u ∈ Att G C F, u ≠ p₁ ∧ u ≠ p₂ ∧ u ≠ cyc D hpos (D.length - 1) := by
    by_contra hcon
    have hall : ∀ u : V, u ∈ Att G C F →
        u = p₁ ∨ u = p₂ ∨ u = cyc D hpos (D.length - 1) := by
      intro u hu
      by_contra hout
      push Not at hout
      exact hcon ⟨u, hu, hout.1, hout.2.1, hout.2.2⟩
    have hx₁ := hall x₁ h.att₁
    have hx₂ := hall x₂ h.att₂
    rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with rfl | rfl | rfl
    · exact h.opp.1 rfl
    · exact h.nadj hs.adj12
    · exact h.nadj hadjwrap
    · exact h.nadj hs.adj12.symm
    · exact h.opp.1 rfl
    · exact h.opp.2.2.2 hsame₂n
    · exact h.nadj hadjwrap.symm
    · exact h.opp.2.2.2 (WheelParity.sameWheelParity_symm hsame₂n)
    · exact h.opp.1 rfl
  obtain ⟨hu₀C, g₀, hg₀F, hu₀g₀⟩ := hu₀Att
  have hg₀fk : g₀ = fk := by
    rcases hFCedge g₀ hg₀F u₀ hu₀C hu₀g₀.symm with hgf | huend
    · exact hgf
    · rcases huend with hu1 | hu2
      · exact absurd hu1 hu₀p₁
      · exact absurd hu2 hu₀p₂
  have hfku₀ : G.Adj fk u₀ := by rw [← hg₀fk]; exact hu₀g₀.symm
  obtain ⟨u₀i, hu₀il, hu₀ie⟩ := cyc_surj hpos ((hDC u₀).mpr hu₀C)
  have hu₀i0 : u₀i ≠ 0 := by
    intro he
    exact hu₀p₁ (by rw [← hu₀ie, he, hp₁])
  have hu₀i1 : u₀i ≠ 1 := by
    intro he
    exact hu₀p₂ (by rw [← hu₀ie, he, hp₂])
  have hu₀in : u₀i ≠ D.length - 1 := by
    intro he
    exact hu₀pn (by rw [← hu₀ie, he])
  have hfku₀i : G.Adj fk (cyc D hpos u₀i) := by rw [hu₀ie]; exact hfku₀
  obtain ⟨g, hg3, hgn, hfg⟩ : ∃ g : ℕ, 3 ≤ g ∧ g + 2 ≤ D.length ∧
      G.Adj fk (cyc D hpos g) := by
    by_contra hcon
    have hnoMidNbr : ∀ t : ℕ, 3 ≤ t → t + 2 ≤ D.length →
        ¬ G.Adj fk (cyc D hpos t) := by
      intro t ht3 htn hadj
      exact hcon ⟨t, ht3, htn, hadj⟩
    have hu₀i2 : u₀i = 2 := by
      by_contra hne
      exact hnoMidNbr u₀i (by omega) (by omega) hfku₀i
    have hfk2 : G.Adj fk (cyc D hpos 2) := by rw [← hu₀i2]; exact hfku₀i
    have hjlast : j = D.length - 1 := by
      by_contra hne
      exact hnoMidNbr j (by omega) (by omega) hfkj
    have hfkpn : G.Adj fk (cyc D hpos (D.length - 1)) := by rw [← hjlast]; exact hfkj
    let A₀ : List V := arc D hpos 2 (D.length - 2)
    have hA₀ : IsPathFrom G A₀ (cyc D hpos 2) (cyc D hpos (D.length - 1)) := by
      have hh := arc_isPathFrom hD hpos (a := 2) (L := D.length - 2) (by omega) (by omega)
      rw [show 2 + (D.length - 2) - 1 = D.length - 1 by omega] at hh
      exact hh
    have hA₀len : A₀.length = D.length - 2 := by simp only [A₀, arc_length]
    have hfkA₀ : fk ∉ A₀ := by
      intro hmem
      obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hmem
      exact h.notC fk hfkF (by rw [← hte]; exact hcycC _)
    have hfkA₀int : ∀ x ∈ SPGT.interior A₀, ¬ G.Adj fk x := by
      intro x hx hadj
      obtain ⟨hxA, hxne0, hxnel⟩ := (PathBasics.mem_interior_iff_of_pathFrom hA₀).mp hx
      obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hxA
      have ht0 : t ≠ 0 := by
        intro he
        apply hxne0
        rw [← hte, he, Nat.add_zero]
      have htlast : t ≠ D.length - 3 := by
        intro he
        apply hxnel
        rw [← hte, he]
        congr 1 <;> omega
      apply hnoMidNbr (2 + t) (by omega) (by omega)
      rw [hte]
      exact hadj
    have hoddHole : IsHoleList G (fk :: A₀) :=
      PrismBasics.isHoleList_of_path_add_vertex hA₀
        (by simp only [pathLength, hA₀len]; omega) hfk2 hfkpn hfkA₀ hfkA₀int
    have hDeven : Even D.length := by
      rw [hDn]
      exact hBerge.1 C hC
    have hoddlen : Odd (holeLength (fk :: A₀)) := by
      rw [Nat.odd_iff]
      simp only [holeLength, List.length_cons, hA₀len]
      obtain ⟨m, hm⟩ := hDeven
      omega
    have hevenlen := hBerge.1 (fk :: A₀) hoddHole
    obtain ⟨a, ha⟩ := hoddlen
    obtain ⟨b, hb⟩ := hevenlen
    omega

  -- Choose a closest pair consisting of an `f_k`-neighbour and a complete rim
  -- vertex in the middle interval.  The intervening arc is `Q₂ \ {f_k}`.
  have hexpair : ∃ p : ℕ × ℕ,
      (3 ≤ p.1 ∧ p.1 + 2 ≤ D.length ∧ G.Adj fk (cyc D hpos p.1)) ∧
      (3 ≤ p.2 ∧ p.2 + 2 ≤ D.length ∧ VertexComplete G (cyc D hpos p.2) Y) :=
    ⟨(g, s), ⟨hg3, hgn, hfg⟩, ⟨hs3, hsn, hsY⟩⟩
  obtain ⟨⟨r, t⟩, ⟨⟨hr3, hrn, hfr⟩, ⟨ht3, htn, htY⟩⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : ℕ × ℕ =>
        (3 ≤ p.1 ∧ p.1 + 2 ≤ D.length ∧ G.Adj fk (cyc D hpos p.1)) ∧
        (3 ≤ p.2 ∧ p.2 + 2 ≤ D.length ∧ VertexComplete G (cyc D hpos p.2) Y))
      (fun p => max p.1 p.2 - min p.1 p.2) hexpair
  simp only at hmin hr3 hrn hfr ht3 htn htY
  have hbetweenAdj : ∀ z : ℕ, min r t < z → z < max r t →
      ¬ G.Adj fk (cyc D hpos z) := by
    intro z hz1 hz2 hadjz
    have hh := hmin (z, t) ⟨⟨by omega, by omega, hadjz⟩, ⟨ht3, htn, htY⟩⟩
    simp only at hh
    omega
  have hbetweenY : ∀ z : ℕ, min r t < z → z < max r t →
      ¬ VertexComplete G (cyc D hpos z) Y := by
    intro z hz1 hz2 hzY
    have hh := hmin (r, z) ⟨⟨hr3, hrn, hfr⟩, ⟨by omega, by omega, hzY⟩⟩
    simp only at hh
    omega
  have hrnotY : r ≠ t → ¬ VertexComplete G (cyc D hpos r) Y := by
    intro hrt hrY
    have hh := hmin (r, r) ⟨⟨hr3, hrn, hfr⟩, ⟨hr3, hrn, hrY⟩⟩
    simp only at hh
    omega
  have htnotAdj : r ≠ t → ¬ G.Adj fk (cyc D hpos t) := by
    intro hrt hadjt
    have hh := hmin (t, t) ⟨⟨ht3, htn, hadjt⟩, ⟨ht3, htn, htY⟩⟩
    simp only at hh
    omega
  obtain ⟨A₂, hA₂, hA₂len, hA₂mem⟩ :=
    Thm162ClaimFiveAux.exists_arc_between hD hpos 0 r t (by omega)
  simp only [Nat.zero_add] at hA₂ hA₂mem
  have hA₂sub : ∀ x : V, x ∈ A₂ → ∃ z : ℕ,
      min r t ≤ z ∧ z ≤ max r t ∧ cyc D hpos z = x :=
    fun x hx => (hA₂mem x).mp hx
  have hA₂C : ∀ x ∈ A₂, x ∈ C := by
    intro x hx
    obtain ⟨z, -, -, hzx⟩ := hA₂sub x hx
    rw [← hzx]
    exact hcycC z
  have hfkA₂ : fk ∉ A₂ := by
    intro hmem
    exact h.notC fk hfkF (hA₂C fk hmem)
  have hfkArc : ∀ z : ℕ, min r t ≤ z → z ≤ max r t →
      (G.Adj fk (cyc D hpos z) ↔ z = r) := by
    intro z hz1 hz2
    constructor
    · intro hadjz
      by_contra hzr
      rcases Nat.lt_or_ge (min r t) z with hlow | hlow
      · rcases Nat.lt_or_ge z (max r t) with hhigh | hhigh
        · exact hbetweenAdj z hlow hhigh hadjz
        · exact htnotAdj (by omega) (by rw [show t = z by omega]; exact hadjz)
      · exact htnotAdj (by omega) (by rw [show t = z by omega]; exact hadjz)
    · rintro rfl
      exact hfr
  have hQ₂ : IsPathFrom G (fk :: A₂) fk (cyc D hpos t) := by
    refine PathAttach.isPathFrom_cons hA₂ hfr hfkA₂ ?_
    intro x hxA hxne hadj
    obtain ⟨z, hz1, hz2, hzx⟩ := hA₂sub x hxA
    have hzr := (hfkArc z hz1 hz2).mp (by rw [hzx]; exact hadj)
    apply hxne
    rw [← hzx, hzr]
  have hA₂unique : ∀ x ∈ A₂, VertexComplete G x Y → x = cyc D hpos t := by
    intro x hxA hxY
    obtain ⟨z, hz1, hz2, hzx⟩ := hA₂sub x hxA
    by_contra hxne
    have hzt : z ≠ t := by
      intro he
      exact hxne (by rw [← hzx, he])
    by_cases hzr : z = r
    · apply hrnotY (by omega)
      rw [← hzr, hzx]
      exact hxY
    · exact hbetweenY z (by omega) (by omega) (by rw [hzx]; exact hxY)
  have hA₂range : ∀ x ∈ A₂, ∃ z : ℕ, 3 ≤ z ∧ z + 2 ≤ D.length ∧
      cyc D hpos z = x := by
    intro x hx
    obtain ⟨z, hz1, hz2, hzx⟩ := hA₂sub x hx
    exact ⟨z, by omega, by omega, hzx⟩
  have hA₂lenpos : 1 ≤ A₂.length := by rw [hA₂len]; omega

  have hR₂A₂disj : ∀ x ∈ R₂, x ∉ A₂ := by
    intro x hxR hxA
    obtain ⟨z, hz3, hzn, hzx⟩ := hA₂range x hxA
    rcases hR₂shape x hxR with rfl | hxF
    · have hi := cyc_inj hD hpos (hzx.trans hp₂.symm)
      rw [Nat.mod_eq_of_lt (show z < D.length by omega),
        Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hi
      omega
    · exact h.notC x hxF.1 (by rw [← hzx]; exact hcycC z)
  have hR₂A₂cross : ∀ x ∈ R₂, ∀ y ∈ A₂,
      (G.Adj x y ↔ x = fk ∧ y = cyc D hpos r) := by
    intro x hxR y hyA
    obtain ⟨z, hz1, hz2, hzy⟩ := hA₂sub y hyA
    have hzlt : z < D.length := by omega
    constructor
    · intro hadj
      rcases hR₂shape x hxR with rfl | hxF
      · have hi := cyc_adj_index hD hpos (show 1 < D.length by omega) hzlt
          (by simpa only [hp₂, hzy] using hadj)
        rcases hi with hi | hi | hi | hi <;> omega
      · rcases hFCedge x hxF.1 y (hA₂C y hyA) hadj with hxfk | hyend
        · refine ⟨hxfk, ?_⟩
          have hzr := (hfkArc z hz1 hz2).mp (by
            rw [hxfk] at hadj
            rw [hzy]
            exact hadj)
          rw [← hzy, hzr]
        · rcases hyend with hy1 | hy2
          · have hi := cyc_inj hD hpos (hzy.trans (hy1.trans hp₁.symm))
            rw [Nat.mod_eq_of_lt hzlt, Nat.zero_mod] at hi
            omega
          · have hi := cyc_inj hD hpos (hzy.trans (hy2.trans hp₂.symm))
            rw [Nat.mod_eq_of_lt hzlt,
              Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hi
            omega
    · rintro ⟨rfl, rfl⟩
      exact hfr
  have hW₂₂ : IsPathFrom G (R₂ ++ A₂) p₂ (cyc D hpos t) :=
    PathGlue.glue_path hR₂ hA₂ hR₂A₂disj hR₂A₂cross

  let R₁ : List V := p₁ :: S
  have hR₁ : IsPathFrom G R₁ p₁ fk := by
    dsimp only [R₁]
    refine PathAttach.isPathFrom_cons hS hs.adjp₁f₁
      (fun hp₁S => hSnotC p₁ hp₁S hs.p₁C) ?_
    intro x hxS hxf₁ hadj
    exact hxf₁ (hp₁_unique x (hSmemF x hxS) hadj)
  have hR₁len : R₁.length = S.length + 1 := by simp only [R₁, List.length_cons]
  have hR₁A₂disj : ∀ x ∈ R₁, x ∉ A₂ := by
    intro x hxR hxA
    obtain ⟨z, hz3, hzn, hzx⟩ := hA₂range x hxA
    have hxR' : x = p₁ ∨ x ∈ S := by simpa only [R₁, List.mem_cons] using hxR
    rcases hxR' with rfl | hxS
    · have hi := cyc_inj hD hpos (hzx.trans hp₁.symm)
      rw [Nat.mod_eq_of_lt (show z < D.length by omega), Nat.zero_mod] at hi
      omega
    · exact hSnotC x hxS (hA₂C x hxA)
  have hR₁A₂cross : ∀ x ∈ R₁, ∀ y ∈ A₂,
      (G.Adj x y ↔ x = fk ∧ y = cyc D hpos r) := by
    intro x hxR y hyA
    obtain ⟨z, hz1, hz2, hzy⟩ := hA₂sub y hyA
    have hzlt : z < D.length := by omega
    constructor
    · intro hadj
      have hxR' : x = p₁ ∨ x ∈ S := by simpa only [R₁, List.mem_cons] using hxR
      rcases hxR' with rfl | hxS
      · have hi := cyc_adj_index hD hpos (show 0 < D.length by omega) hzlt
          (by simpa only [hp₁, hzy] using hadj)
        rcases hi with hi | hi | hi | hi <;> omega
      · rcases hFCedge x (hSmemF x hxS) y (hA₂C y hyA) hadj with hxfk | hyend
        · refine ⟨hxfk, ?_⟩
          have hzr := (hfkArc z hz1 hz2).mp (by
            rw [hxfk] at hadj
            rw [hzy]
            exact hadj)
          rw [← hzy, hzr]
        · rcases hyend with hy1 | hy2
          · have hi := cyc_inj hD hpos (hzy.trans (hy1.trans hp₁.symm))
            rw [Nat.mod_eq_of_lt hzlt, Nat.zero_mod] at hi
            omega
          · have hi := cyc_inj hD hpos (hzy.trans (hy2.trans hp₂.symm))
            rw [Nat.mod_eq_of_lt hzlt,
              Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hi
            omega
    · rintro ⟨rfl, rfl⟩
      exact hfr
  have hW₁₂ : IsPathFrom G (R₁ ++ A₂) p₁ (cyc D hpos t) :=
    PathGlue.glue_path hR₁ hA₂ hR₁A₂disj hR₁A₂cross

  have hW₂₂Y : ∀ x ∈ R₂ ++ A₂, x ∉ Y := by
    intro x hx
    rcases List.mem_append.mp hx with hxR | hxA
    · rcases hR₂shape x hxR with rfl | hxF
      · simpa only [hp₂] using hcycY 1
      · exact h.notY x hxF.1
    · exact hCY x (hA₂C x hxA)
  have hW₂₂int : ∀ x ∈ SPGT.interior (R₂ ++ A₂),
      ¬ VertexComplete G x Y ∧ ¬ G.Adj p₁ x := by
    intro x hx
    obtain ⟨hxW, hxne2, hxnet⟩ := (PathBasics.mem_interior_iff_of_pathFrom hW₂₂).mp hx
    rcases List.mem_append.mp hxW with hxR | hxA
    · rcases hR₂shape x hxR with hxp₂ | hxF
      · exact absurd hxp₂ hxne2
      · refine ⟨h.notComplete x hxF.1, ?_⟩
        intro hadj
        exact hxF.2 (hp₁_unique x hxF.1 hadj)
    · refine ⟨?_, ?_⟩
      · intro hxY
        exact hxnet (hA₂unique x hxA hxY)
      · intro hadj
        obtain ⟨z, hz3, hzn, hzx⟩ := hA₂range x hxA
        have hi := cyc_adj_index hD hpos (show 0 < D.length by omega)
          (show z < D.length by omega) (by simpa only [hp₁, hzx] using hadj)
        rcases hi with hi | hi | hi | hi <;> omega
  have hW₂₂even : Even (pathLength (R₂ ++ A₂)) := by
    refine Thm162ClaimFiveAux.even_of_clean hBerge hYanti hW₂₂ ?_ hW₂₂Y
      hs.yc2 htY (fun x hx => (hW₂₂int x hx).1) hs.yc1
      (fun x hx => (hW₂₂int x hx).2)
    simp only [List.length_append]
    omega

  have hW₁₂Y : ∀ x ∈ R₁ ++ A₂, x ∉ Y := by
    intro x hx
    rcases List.mem_append.mp hx with hxR | hxA
    · have hxR' : x = p₁ ∨ x ∈ S := by simpa only [R₁, List.mem_cons] using hxR
      rcases hxR' with rfl | hxS
      · exact hCY x hs.p₁C
      · exact hSnotY x hxS
    · exact hCY x (hA₂C x hxA)
  have hW₁₂int : ∀ x ∈ SPGT.interior (R₁ ++ A₂),
      ¬ VertexComplete G x Y := by
    intro x hx
    obtain ⟨hxW, hxne1, hxnet⟩ := (PathBasics.mem_interior_iff_of_pathFrom hW₁₂).mp hx
    rcases List.mem_append.mp hxW with hxR | hxA
    · have hxR' : x = p₁ ∨ x ∈ S := by simpa only [R₁, List.mem_cons] using hxR
      rcases hxR' with hxp₁ | hxS
      · exact absurd hxp₁ hxne1
      · exact hSnc x hxS
    · intro hxY
      exact hxnet (hA₂unique x hxA hxY)
  have hHpar' : Even (S.length + (D.length - j) + 1) := by
    simpa only [List.length_reverse] using hHpar
  have hW₁₂odd : Odd (pathLength (R₁ ++ A₂)) := by
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at hHpar' hW₂₁even hW₂₂even
    simp only [pathLength, List.length_append, hA₁len] at hW₂₁even
    simp only [pathLength, List.length_append] at hW₂₂even
    simp only [pathLength, List.length_append, hR₁len]
    omega
  have hf₁W : f₁ ∈ R₁ ++ A₂ := by
    apply List.mem_append.mpr
    left
    have hf₁S := (PathBasics.isPathFrom_ends_mem hS).1
    simpa only [R₁, List.mem_cons] using (Or.inr hf₁S : f₁ = p₁ ∨ f₁ ∈ S)
  have hfkW : fk ∈ R₁ ++ A₂ := by
    apply List.mem_append.mpr
    left
    have hfkS := (PathBasics.isPathFrom_ends_mem hS).2
    simpa only [R₁, List.mem_cons] using (Or.inr hfkS : fk = p₁ ∨ fk ∈ S)
  have hf₁int : f₁ ∈ SPGT.interior (R₁ ++ A₂) := by
    refine (PathBasics.mem_interior_iff_of_pathFrom hW₁₂).mpr ⟨hf₁W, ?_, ?_⟩
    · intro he
      exact h.notC f₁ hf₁F (he ▸ hs.p₁C)
    · intro he
      exact h.notC f₁ hf₁F (by rw [he]; exact hcycC t)
  have hfkint : fk ∈ SPGT.interior (R₁ ++ A₂) := by
    refine (PathBasics.mem_interior_iff_of_pathFrom hW₁₂).mpr ⟨hfkW, ?_, ?_⟩
    · intro he
      exact h.notC fk hfkF (he ▸ hs.p₁C)
    · intro he
      exact h.notC fk hfkF (by rw [he]; exact hcycC t)
  refine odd_path_endgame h.inF6 h.wheel hs.pi2 hs.piSpec hW₁₂ hW₁₂odd
    hs.yc1 htY hW₁₂int hW₁₂Y hf₁int hfkint hfkne ?_ hfkpi
  intro u huC hfu
  rcases hf₁nbr u huC hfu with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Ne.symm hs.piNe)

end Workspace.ProofLemmas.Thm162ClaimThree
