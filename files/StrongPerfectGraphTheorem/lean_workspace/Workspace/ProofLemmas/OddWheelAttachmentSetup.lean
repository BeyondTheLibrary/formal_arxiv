import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelTrichotomy
import Workspace.ProofLemmas.OddWheelAttachmentBase

/-!
# 16.2: the minimality reduction, and the shape of the remaining work

PAPER (16.2, printed p. 98): *"Proof.  We may assume that `F` is minimal.  If `|F| = 1` then the
result follows from 16.1, so we assume `|F| ≥ 2`."*

This module carries the scaffolding of 16.2:

* `GoodF` — the hypotheses 16.2 places on the connected set `F`, bundled;
* `Concl` — the three-bullet conclusion of 16.2, for a given `F`;
* `exists_minimal` and `concl_mono` — the printed *"we may assume that `F` is minimal"*: a
  minimal `F' ⊆ F` still satisfies the hypotheses, and the conclusion for `F'` implies the
  conclusion for `F`, since every bullet mentions `F` only positively;
* `ClaimOneHolds` and `BigCaseFalse` — the two remaining pieces, wrapped as hypotheses so that
  the assembly `thm_16_2_of_pieces` can be checked before either is proved.

`BigCaseFalse` is the `|F| ≥ 2` line of the printed proof — claims (2), (3), (4), (5) and the
closing paragraph.  Note that it concludes `False`: claim (3) is *stated* as *"then the theorem
holds"* but its printed proof derives a contradiction, so it holds vacuously, and the closing
paragraph likewise ends *"contradicting that there are nonadjacent vertices in `X` of opposite
wheel-parity"*.  Consequently 16.2's conclusion is only ever produced by the base case `|F| = 1`
(which gives the first two bullets, via 16.1) and by claim (1) (which gives the third).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentSetup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### The hypotheses and the conclusion, bundled -/

/-- The hypotheses 16.2 places on the connected set `F`. -/
def GoodF (G : SimpleGraph V) (C : List V) (Y : Set V) (F : Set V) : Prop :=
  ConnectedSet G F ∧ (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧
    (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
    (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
      OppositeWheelParity G C Y a b) ∧
    (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
      a ≠ b ∧ ¬ G.Adj a b)

/-- The three-bullet conclusion of 16.2, for a given `F`. -/
def Concl (G : SimpleGraph V) (C : List V) (Y : Set V) (F : Set V) : Prop :=
  (∃ v ∈ F, IsWheel G C (Y ∪ {v})) ∨
  (∃ v ∈ F, 4 ≤ (G.neighborSet v ∩ {u : V | u ∈ C}).ncard ∧
    ∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
      (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
      VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
      VertexComplete G p₃ (Y ∪ {v}) ∧
      ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
  (∃ p₁ p₂ p₃ : V,
    (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
    VertexComplete G p₁ Y ∧ VertexComplete G p₂ Y ∧ VertexComplete G p₃ Y ∧
    ∃ P : List V, IsPathFrom G P p₁ p₃ ∧ (∀ x ∈ SPGT.interior P, x ∈ F) ∧
      ∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u)

/-- **Piece C**, wrapped: claim (1) of the printed proof of 16.2.

PAPER: *"(1) If there do not exist nonadjacent vertices in `X` with different wheel-parity, then
the theorem holds."* -/
def ClaimOneHolds (G : SimpleGraph V) (C : List V) (Y : Set V) : Prop :=
  ∀ F : Set V, GoodF G C Y F →
    (¬ ∃ x₁ ∈ attachments G F {u : V | u ∈ C}, ∃ x₂ ∈ attachments G F {u : V | u ∈ C},
      x₁ ≠ x₂ ∧ ¬ G.Adj x₁ x₂ ∧ OppositeWheelParity G C Y x₁ x₂) →
    Concl G C Y F

/-- **Piece D**, wrapped: the `|F| ≥ 2` line of the printed proof of 16.2 — claims (2), (3), (4),
(5) and the closing paragraph — which ends in a contradiction. -/
def BigCaseFalse (G : SimpleGraph V) (C : List V) (Y : Set V) : Prop :=
  ∀ F : Set V, GoodF G C Y F →
    (∀ F' : Set V, F' ⊆ F → GoodF G C Y F' → F.ncard ≤ F'.ncard) →
    2 ≤ F.ncard →
    (∃ x₁ ∈ attachments G F {u : V | u ∈ C}, ∃ x₂ ∈ attachments G F {u : V | u ∈ C},
      x₁ ≠ x₂ ∧ ¬ G.Adj x₁ x₂ ∧ OppositeWheelParity G C Y x₁ x₂) →
    False

/-! ### Piece B — *"we may assume that `F` is minimal"* -/

/-- Every bullet of 16.2's conclusion mentions `F` only positively, so the conclusion for a
subset carries up. -/
theorem concl_mono {F F' : Set V} (hsub : F' ⊆ F) (h : Concl G C Y F') : Concl G C Y F := by
  rcases h with h | h | h
  · obtain ⟨v, hvF, hw⟩ := h
    exact Or.inl ⟨v, hsub hvF, hw⟩
  · obtain ⟨v, hvF, hrest⟩ := h
    exact Or.inr (Or.inl ⟨v, hsub hvF, hrest⟩)
  · obtain ⟨p₁, p₂, p₃, harc, hc₁, hc₂, hc₃, P, hP, hint, hno⟩ := h
    exact Or.inr (Or.inr ⟨p₁, p₂, p₃, harc, hc₁, hc₂, hc₃, P, hP,
      fun x hx => hsub (hint x hx), hno⟩)

/-- PAPER: *"We may assume that `F` is minimal."* -/
theorem exists_minimal {F : Set V} (hF : GoodF G C Y F) :
    ∃ F' : Set V, F' ⊆ F ∧ GoodF G C Y F' ∧
      ∀ F'' : Set V, F'' ⊆ F' → GoodF G C Y F'' → F'.ncard ≤ F''.ncard := by
  classical
  obtain ⟨F', ⟨hsub, hgood⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat (fun S : Set V => S ⊆ F ∧ GoodF G C Y S)
      (fun S => S.ncard) ⟨F, subset_rfl, hF⟩
  exact ⟨F', hsub, hgood, fun F'' h1 h2 => hmin F'' ⟨h1.trans hsub, h2⟩⟩

/-- A set satisfying 16.2's hypotheses is nonempty: it has an attachment, and an attachment has
a neighbour in it. -/
theorem goodF_nonempty {F : Set V} (hF : GoodF G C Y F) : F.Nonempty := by
  obtain ⟨-, -, -, -, ⟨a, ha, -⟩, -⟩ := hF
  obtain ⟨-, f, hfF, -⟩ := ha
  exact ⟨f, hfF⟩

/-! ### The assembly -/

/-- **16.2, modulo claim (1) and the `|F| ≥ 2` line.**

The printed proof's skeleton: minimise `F`; if `|F| = 1` the result follows from 16.1
(`OddWheelAttachmentBase.base_case`); otherwise either there is no nonadjacent pair of opposite
wheel-parity in `X`, and claim (1) applies, or there is one, and the rest of the printed proof
derives a contradiction. -/
theorem thm_16_2_of_pieces (hG : InF6 G) (hwheel : IsWheel G C Y)
    (hC1 : ClaimOneHolds G C Y) (hD : BigCaseFalse G C Y)
    {F : Set V} (hF : GoodF G C Y F) : Concl G C Y F := by
  classical
  obtain ⟨F', hsub, hgood, hmin⟩ := exists_minimal hF
  refine concl_mono hsub ?_
  by_cases hbig : 2 ≤ F'.ncard
  · by_cases hpair : ∃ x₁ ∈ attachments G F' {u : V | u ∈ C},
        ∃ x₂ ∈ attachments G F' {u : V | u ∈ C},
        x₁ ≠ x₂ ∧ ¬ G.Adj x₁ x₂ ∧ OppositeWheelParity G C Y x₁ x₂
    · exact absurd (hD F' hgood hmin hbig hpair) (fun h => h)
    · exact hC1 F' hgood hpair
  · -- `|F'| = 1`: the base case, via 16.1
    obtain ⟨v, hvF⟩ := goodF_nonempty hgood
    have hcard : F' = {v} := by
      have hfin : F'.Finite := Set.toFinite _
      have h1 : ({v} : Set V) ⊆ F' := Set.singleton_subset_iff.mpr hvF
      have h2 : F'.ncard ≤ ({v} : Set V).ncard := by
        rw [Set.ncard_singleton]
        omega
      exact (Set.eq_of_subset_of_ncard_le h1 h2 hfin).symm
    obtain ⟨hconn, hFC, hFY, hFnc, ⟨a, ha, b, hb, hab⟩, ⟨x, hxa, y, hyb, hxyne, hnadj⟩⟩ :
        ConnectedSet G F' ∧ (∀ f ∈ F', f ∉ C) ∧ (∀ f ∈ F', f ∉ Y) ∧
          (∀ f ∈ F', ¬ VertexComplete G f Y) ∧
          (∃ a ∈ attachments G F' {u : V | u ∈ C}, ∃ b ∈ attachments G F' {u : V | u ∈ C},
            OppositeWheelParity G C Y a b) ∧
          (∃ a ∈ attachments G F' {u : V | u ∈ C}, ∃ b ∈ attachments G F' {u : V | u ∈ C},
            a ≠ b ∧ ¬ G.Adj a b) := hgood
    -- attachments of a singleton are its neighbours on the rim
    have hatt : ∀ w : V, w ∈ attachments G F' {u : V | u ∈ C} ↔ (w ∈ C ∧ G.Adj w v) := by
      intro w
      constructor
      · rintro ⟨hwC, f, hfF, hadj⟩
        rw [hcard] at hfF
        rw [Set.mem_singleton_iff.mp hfF] at hadj
        exact ⟨hwC, hadj⟩
      · rintro ⟨hwC, hadj⟩
        exact ⟨hwC, v, hvF, hadj⟩
    obtain ⟨haC, hva⟩ := (hatt a).mp ha
    obtain ⟨hbC, hvb⟩ := (hatt b).mp hb
    obtain ⟨hxC, hvx⟩ := (hatt x).mp hxa
    obtain ⟨hyC, hvy⟩ := (hatt y).mp hyb
    exact OddWheelAttachmentBase.base_case hG hwheel (hFC v hvF) (hFY v hvF) (hFnc v hvF)
      hva.symm hvb.symm hab ⟨x, hxC, y, hyC, hvx.symm, hvy.symm, hxyne, hnadj⟩ hvF

/-! ### Piece C — claim (1) -/

/-- **Claim (1)** of the printed proof of 16.2.

PAPER: *"(1) If there do not exist nonadjacent vertices in `X` with different wheel-parity, then
the theorem holds.  For there exist vertices in `X` with different wheel-parity, which are
therefore adjacent; say `p₁, p₂` … So `p₁, p₂` are both `Y`-complete … There is a third
attachment of `F` … therefore `p₂, p_i` are adjacent, that is, `i = 3`, and `p₃` is `Y`-complete.
Suppose `F` has a fourth attachment `p_j` … a contradiction.  So `p₁, p₂, p₃` are the only
attachments of `F`, and then the theorem holds."* -/
theorem claim_one (hG : InF6 G) (hwheel : IsWheel G C Y) : ClaimOneHolds G C Y := by
  classical
  intro F hF hno
  have hBerge : Berge G := hG.1.1.1
  have hC : IsHoleList G C := hwheel.1.1
  have hn6 : 6 ≤ C.length := hwheel.1.2
  have hn : 0 < C.length := by omega
  have hnd : C.Nodup := hC.2.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hwheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  obtain ⟨hconn, hFC, hFY, hFnc, ⟨a, ha, b, hb, hab⟩, ⟨x, hxa, y, hyb, hxyne, hnadj⟩⟩ :
      ConnectedSet G F ∧ (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧
        (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
        (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
          OppositeWheelParity G C Y a b) ∧
        (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
          a ≠ b ∧ ¬ G.Adj a b) := hF
  have hattach : ∀ w : V, w ∈ attachments G F {u : V | u ∈ C} ↔ (w ∈ C ∧ ∃ f ∈ F, G.Adj w f) :=
    fun w => Iff.rfl
  -- *"vertices in `X` with different wheel-parity … are therefore adjacent"*
  have hkey : ∀ u w : V, u ∈ attachments G F {z : V | z ∈ C} →
      w ∈ attachments G F {z : V | z ∈ C} → OppositeWheelParity G C Y u w → G.Adj u w := by
    intro u w hu hw hopp
    by_contra hcon
    exact hno ⟨u, hu, w, hw, hopp.1, hcon, hopp⟩
  -- *"they are both `Y`-complete, since they have different wheel-parity"*
  have hedgeY : ∀ u w : V, u ∈ C → w ∈ C → G.Adj u w → OppositeWheelParity G C Y u w →
      VertexComplete G u Y ∧ VertexComplete G w Y := by
    intro u w hu hw hadj hopp
    constructor
    · by_contra hcon
      exact hopp.2.2.2
        (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hu hw hadj hcon)
    · by_contra hcon
      exact hopp.2.2.2 (WheelParity.sameWheelParity_symm
        (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hC heven hw hu hadj.symm hcon))
  have haC : a ∈ C := hab.2.1
  have hbC : b ∈ C := hab.2.2.1
  have hadjab : G.Adj a b := hkey a b ha hb hab
  have hpab : π a ≠ π b := fun he => hab.2.2.2 ((hπ a b haC hbC hab.1).mpr he)
  -- *"There is a third attachment of `F`, since there are two that are nonadjacent"*
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ attachments G F {z : V | z ∈ C}, c ≠ a ∧ c ≠ b := by
    rcases eq_or_ne x a with rfl | hxa'
    · rcases eq_or_ne y b with rfl | hyb'
      · exact absurd hadjab hnadj
      · exact ⟨y, hyb, fun he => hxyne he.symm, hyb'⟩
    · rcases eq_or_ne x b with rfl | hxb'
      · rcases eq_or_ne y a with rfl | hya'
        · exact absurd hadjab.symm hnadj
        · exact ⟨y, hyb, hya', fun he => hxyne he.symm⟩
      · exact ⟨x, hxa, hxa', hxb'⟩
  obtain ⟨hcC, -⟩ := (hattach c).mp hc
  -- three attachments in a row, the middle one of the opposite wheel-parity to both ends
  obtain ⟨u, m, w, huX, hmX, hwX, hum, hmw, huw, hpu, hpw⟩ :
      ∃ u m w : V, u ∈ attachments G F {z : V | z ∈ C} ∧
        m ∈ attachments G F {z : V | z ∈ C} ∧ w ∈ attachments G F {z : V | z ∈ C} ∧
        G.Adj u m ∧ G.Adj m w ∧ u ≠ w ∧ π u ≠ π m ∧ π w ≠ π m := by
    rcases (show π c ≠ π a ∨ π c ≠ π b by omega) with hcase | hcase
    · have hopp : OppositeWheelParity G C Y c a :=
        ⟨hca, hcC, haC, fun hs => hcase ((hπ c a hcC haC hca).mp hs)⟩
      exact ⟨c, a, b, hc, ha, hb, hkey c a hc ha hopp, hadjab, hcb, hcase,
        fun he => hpab he.symm⟩
    · have hopp : OppositeWheelParity G C Y c b :=
        ⟨hcb, hcC, hbC, fun hs => hcase ((hπ c b hcC hbC hcb).mp hs)⟩
      exact ⟨a, b, c, ha, hb, hc, hadjab, (hkey c b hc hb hopp).symm,
        fun he => hca he.symm, hpab, hcase⟩
  obtain ⟨huC, -⟩ := (hattach u).mp huX
  obtain ⟨hmC, -⟩ := (hattach m).mp hmX
  obtain ⟨hwC, -⟩ := (hattach w).mp hwX
  have hoppum : OppositeWheelParity G C Y u m :=
    ⟨hum.ne, huC, hmC, fun hs => hpu ((hπ u m huC hmC hum.ne).mp hs)⟩
  have hoppmw : OppositeWheelParity G C Y m w :=
    ⟨hmw.ne, hmC, hwC, fun hs => hpw ((hπ m w hmC hwC hmw.ne).mp hs).symm⟩
  obtain ⟨hcu, hcm⟩ := hedgeY u m huC hmC hum hoppum
  obtain ⟨-, hcw⟩ := hedgeY m w hmC hwC hmw hoppmw
  -- positions of the three attachments on the rim
  obtain ⟨iu, hiu, hiue⟩ := List.getElem_of_mem huC
  obtain ⟨im, him, hime⟩ := List.getElem_of_mem hmC
  obtain ⟨iw, hiw, hiwe⟩ := List.getElem_of_mem hwC
  have hidx : ∀ (i j : ℕ) (hi : i < C.length) (hj : j < C.length),
      G.Adj (C[i]'hi) (C[j]'hj) → (j = (i + 1) % C.length ∨ i = (j + 1) % C.length) :=
    fun i j hi hj h => (HoleBasics.hole_adj_iff hC hi hj).mp h
  have hmod : ∀ i : ℕ, i < C.length →
      (i + 1) % C.length = if i + 1 = C.length then 0 else i + 1 := by
    intro i hi
    by_cases h : i + 1 = C.length
    · simp [h]
    · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
  have hium : G.Adj (C[iu]'hiu) (C[im]'him) := by rw [hiue, hime]; exact hum
  have himw : G.Adj (C[im]'him) (C[iw]'hiw) := by rw [hime, hiwe]; exact hmw
  have hiuw : iu ≠ iw := by
    rintro rfl
    exact huw (hiue.symm.trans hiwe)
  -- *"`p₁, p₂, p₃` are the only attachments of `F`"*
  have honly : ∀ z : V, z ∈ attachments G F {t : V | t ∈ C} → z = u ∨ z = m ∨ z = w := by
    intro z hz
    by_contra hcon
    push Not at hcon
    obtain ⟨hzu, hzm, hzw⟩ := hcon
    obtain ⟨hzC, -⟩ := (hattach z).mp hz
    obtain ⟨iz, hiz, hize⟩ := List.getElem_of_mem hzC
    have hzune : iz ≠ iu := fun he => hzu (hize.symm.trans (he ▸ hiue))
    have hzmne : iz ≠ im := fun he => hzm (hize.symm.trans (he ▸ hime))
    have hzwne : iz ≠ iw := fun he => hzw (hize.symm.trans (he ▸ hiwe))
    -- `z` has the wheel-parity of `m`, since otherwise it would be adjacent to `m`,
    -- but the two rim neighbours of `m` are already `u` and `w`
    have hpz : π z = π m := by
      by_contra hpc
      have hadjzm : G.Adj z m :=
        hkey z m hz hmX ⟨hzm, hzC, hmC, fun hs => hpc ((hπ z m hzC hmC hzm).mp hs)⟩
      have hizm : G.Adj (C[iz]'hiz) (C[im]'him) := by rw [hize, hime]; exact hadjzm
      have h1 := hidx iz im hiz him hizm
      have h2 := hidx iu im hiu him hium
      have h3 := hidx im iw him hiw himw
      rw [hmod iz hiz, hmod im him] at h1
      rw [hmod iu hiu, hmod im him] at h2
      rw [hmod im him, hmod iw hiw] at h3
      split_ifs at h1 h2 h3 <;> omega
    have hpzu : π z ≠ π u := by rw [hpz]; exact fun he => hpu he.symm
    have hpzw : π z ≠ π w := by rw [hpz]; exact fun he => hpw he.symm
    have hadjzu : G.Adj z u := hkey z u hz huX
      ⟨hzu, hzC, huC, fun hs => hpzu ((hπ z u hzC huC hzu).mp hs)⟩
    have hadjzw : G.Adj z w := hkey z w hz hwX
      ⟨hzw, hzC, hwC, fun hs => hpzw ((hπ z w hzC hwC hzw).mp hs)⟩
    have hizu : G.Adj (C[iz]'hiz) (C[iu]'hiu) := by rw [hize, hiue]; exact hadjzu
    have hizw : G.Adj (C[iz]'hiz) (C[iw]'hiw) := by rw [hize, hiwe]; exact hadjzw
    have hA := hidx iz iu hiz hiu hizu
    have hB := hidx iz iw hiz hiw hizw
    have hC1 := hidx iu im hiu him hium
    have hC2 := hidx im iw him hiw himw
    rw [hmod iz hiz, hmod iu hiu] at hA
    rw [hmod iz hiz, hmod iw hiw] at hB
    rw [hmod iu hiu, hmod im him] at hC1
    rw [hmod im him, hmod iw hiw] at hC2
    split_ifs at hA hB hC1 hC2 <;> omega
  have hmemF : ∀ z : V, z ∈ C → (∃ f ∈ F, G.Adj z f) → z = u ∨ z = m ∨ z = w :=
    fun z hz hf => honly z ⟨hz, hf⟩
  -- the path from `u` to `w` with interior in `F`
  obtain ⟨fu, hfuF, hfu⟩ : ∃ f ∈ F, G.Adj u f := ((hattach u).mp huX).2
  obtain ⟨fw, hfwF, hfw⟩ : ∃ f ∈ F, G.Adj w f := ((hattach w).mp hwX).2
  obtain ⟨P, hP, hPint⟩ := MinimalConnectedIsPath.exists_path_interior_in hconn
    (fun hmem => hFC u hmem huC) (fun hmem => hFC w hmem hwC) ⟨fu, hfuF, hfu⟩ ⟨fw, hfwF, hfw⟩
  -- reading a cyclically consecutive triple off the rim
  have hstep : ∀ (s : ℕ) (hs : s < C.length) (t : ℕ) (ht : t < C.length) (z : V),
      (C[t]'ht) = z → (s + 1) % C.length = im → (im + 1) % C.length = t →
      ∃ k : ℕ, [C[s]'hs, m, z] <+: C.rotate k := by
    intro s hs t ht z hz h1 h2
    refine ⟨s, ?_⟩
    have hs2 : (s + 2) % C.length = t := by
      have e : (s + 2) % C.length = ((s + 1) % C.length + 1) % C.length := by
        rw [Nat.mod_add_mod]
      rw [e, h1, h2]
    have e1 : (C[s % C.length]'(Nat.mod_lt _ hn)) = (C[s]'hs) :=
      (List.Nodup.getElem_inj_iff hnd).mpr (Nat.mod_eq_of_lt hs)
    have e2 : (C[(s + 1) % C.length]'(Nat.mod_lt _ hn)) = m := by
      rw [(List.Nodup.getElem_inj_iff hnd).mpr h1]; exact hime
    have e3 : (C[(s + 2) % C.length]'(Nat.mod_lt _ hn)) = z := by
      rw [(List.Nodup.getElem_inj_iff hnd).mpr hs2]; exact hz
    have heq : (C.rotate s).take 3 = [C[s]'hs, m, z] := by
      rw [OddWheelTrichotomy.take_three_eq hn (show 3 ≤ C.length by omega) s, e1, e2, e3]
    rw [← heq]
    exact List.take_prefix _ _
  have hcases : ((iu + 1) % C.length = im ∧ (im + 1) % C.length = iw) ∨
      ((iw + 1) % C.length = im ∧ (im + 1) % C.length = iu) := by
    have h1 := hidx iu im hiu him hium
    have h2 := hidx im iw him hiw himw
    rw [hmod iu hiu, hmod im him] at h1
    rw [hmod im him, hmod iw hiw] at h2
    rw [hmod iu hiu, hmod im him, hmod iw hiw]
    split_ifs at h1 h2 ⊢ <;> omega
  refine Or.inr (Or.inr ⟨u, m, w, ?_, hcu, hcm, hcw, P, hP, hPint, ?_⟩)
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨k, hk⟩ := hstep iu hiu iw hiw w hiwe h1 h2
      rw [hiue] at hk
      exact ⟨k, Or.inl hk⟩
    · obtain ⟨k, hk⟩ := hstep iw hiw iu hiu u hiue h1 h2
      rw [hiwe] at hk
      exact ⟨k, Or.inr hk⟩
  · intro z hz t htC ht₁ ht₂ ht₃ hadj
    rcases hmemF t htC ⟨z, hPint z hz, hadj.symm⟩ with rfl | rfl | rfl
    · exact ht₁ rfl
    · exact ht₂ rfl
    · exact ht₃ rfl

/-- **16.2, modulo only the `|F| ≥ 2` line of its printed proof.**

Claim (1) is now discharged, so the sole remaining hypothesis is `BigCaseFalse` — claims (2),
(3), (4), (5) and the closing paragraph. -/
theorem thm_16_2_of_bigCase (hG : InF6 G) (hwheel : IsWheel G C Y)
    (hD : BigCaseFalse G C Y) {F : Set V} (hF : GoodF G C Y F) : Concl G C Y F :=
  thm_16_2_of_pieces hG hwheel (claim_one hG hwheel) hD hF

end Workspace.ProofLemmas.OddWheelAttachmentSetup
