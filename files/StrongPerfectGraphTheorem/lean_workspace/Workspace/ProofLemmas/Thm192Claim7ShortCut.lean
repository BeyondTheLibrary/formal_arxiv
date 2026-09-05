import Workspace.ProofLemmas.Thm192Claim7NoncompleteParity
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S13.Thm_13_6

/-!
# The hat-or-leap step of claim (7) of 19.2

PAPER (printed pp. 119–120, claim (7), the case `x₂` not `Y₀`-complete):

> *"Consequently `Y` contains no hat for `C₁`.  Assume that `C₁` has length `≥ 6`.  By 2.10,
> `Y` contains a leap, so there are nonadjacent `y₁, y₂ ∈ Y` such that
> `y₁-x₂-pᵢ-⋯-pₙ-y₂` is a path, of odd length `≥ 5`.  But the ends of this path are
> `{x₀,x₁}`-complete and its internal vertices are not, contrary to 13.6.  So `C₁` has
> length 4, that is, `i = n`."*

`C₁` is the hole `z-x₂-pᵢ-⋯-pₙ-x₁-z`; here it is the list `z :: x₂ :: P.drop i`.
The "no hat" step uses that every member of `Y` has a neighbour among `x₂, pᵢ, …, pₙ`:
for `y` this is the hypothesis `hycontact` supplied by the 17.1 reflection argument, and
for the rest of `Y` it is the `Y₀`-complete vertex `pₖ` produced by the 16.1 parity
calculation (`Thm192Claim7NoncompleteParity.exists_complete_after`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm192Claim7ShortCut

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The entries of the shortened rim `C₁ = z-x₂-pᵢ-⋯-pₙ-x₁` beyond its first two. -/
theorem cut_getElem {z u : V} {P : List V} {i m : ℕ} (hm : m < P.length) (him : i ≤ m)
    (ht : m - i + 2 < (z :: u :: P.drop i).length) :
    (z :: u :: P.drop i)[m - i + 2]'ht = (P[m]'hm) := by
  have he : i + (m - i) = m := by omega
  simp [List.getElem_drop, he]

/-- PAPER (claim (7)): *"So `C₁` has length 4, that is, `i = n`."* -/
theorem cut_length_four {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hzY : VertexComplete G z Y)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i))
    (hycontact : G.Adj y (x 2) ∨ G.Adj y (P[P.length - 2]'(by omega)))
    {k : ℕ} (hk : k + 1 < P.length) (hik : i ≤ k)
    (hkc : VertexComplete G (P[k]'(by omega)) (Y \ {y})) :
    i = P.length - 2 := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, hCP, -⟩ :=
    Thm192Claim6Basics.path_facts hBerge hws Set.Subset.rfl hP hPI (by omega)
  have hYout := Thm192Claim6Basics.Y_disjoint_path hHyp Set.Subset.rfl hP hPI
  have hlastP : (P[P.length - 1]'(by omega)) = x 1 :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hzint : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w :=
    fun w hw => wheelSystemA_no_z w (hPI w hw)
  have hnopair : ∀ m (hm : m < P.length), 0 < m → m + 1 < P.length →
      ¬ (G.Adj (P[m]'hm) (x 0) ∧ G.Adj (P[m]'hm) (x 1)) :=
    fun m hm h1 h2 => Thm192Claim6Basics.no_pair_complete (A := wheelSystemA G z A₀ x 1)
      Set.Subset.rfl _ (hPI _ (PathBasics.getElem_mem_interior hP.1 hm h1 h2))
  by_contra hine
  have hi3 : i + 2 < P.length := by omega
  set C₁ : List V := z :: x 2 :: P.drop i with hC₁def
  have hC₁len : C₁.length = P.length - i + 2 := by
    simp [hC₁def]
  have hC₁ : IsHoleList G C₁ :=
    Thm192Infra.holeFromCut hP hPI (fun w hw => wheelSystemA_no_z w hw)
      (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega))
      (hws.2.2.2.2.2.2 2 le_rfl) hzP hx2P hi (by omega) hlast
  have hC₁even : Even C₁.length := hBerge.1 _ hC₁
  have hL6 : 6 ≤ C₁.length := by obtain ⟨r, hr⟩ := hC₁even; omega
  -- reading `C₁` off `P`
  have hC1P : ∀ m (hm : m < P.length) (him : i ≤ m) (ht : m - i + 2 < C₁.length),
      (C₁[m - i + 2]'ht) = (P[m]'hm) := by
    intro m hm him ht
    exact cut_getElem hm him ht
  have hC1zero : ∀ (h : 0 < C₁.length), (C₁[0]'h) = z := fun h => by simp [hC₁def]
  have hC1one : ∀ (h : 1 < C₁.length), (C₁[1]'h) = x 2 := fun h => by simp [hC₁def]
  have hC1last : ∀ (h : C₁.length - 1 < C₁.length), (C₁[C₁.length - 1]'h) = x 1 := by
    intro h
    rw [Thm192Claim7Aux.getElem_idx_congr (l := C₁)
      (show C₁.length - 1 = (P.length - 1) - i + 2 by omega) h (by omega),
      hC1P (P.length - 1) (by omega) (by omega) (by omega)]
    exact hlastP
  have hC1pen : ∀ (h : C₁.length - 2 < C₁.length),
      (C₁[C₁.length - 2]'h) = (P[P.length - 2]'(show P.length - 2 < P.length by omega)) := by
    intro h
    rw [Thm192Claim7Aux.getElem_idx_congr (l := C₁)
      (show C₁.length - 2 = (P.length - 2) - i + 2 by omega) h (by omega)]
    exact hC1P (P.length - 2) (by omega) (by omega) (by omega)
  -- membership dictionary
  have hmemP : ∀ m (hm : m < P.length), i ≤ m → (P[m]'hm) ∈ C₁ := by
    intro m hm him
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    rw [List.mem_iff_getElem]
    exact ⟨m - i, by simp only [List.length_drop]; omega, by
      rw [List.getElem_drop]
      exact hP.1.2.1.getElem_inj_iff.mpr (by omega)⟩
  have hx1C : x 1 ∈ C₁ := by
    have := hmemP (P.length - 1) (by omega) (by omega)
    rwa [hlastP] at this
  have hzC : z ∈ C₁ := by simp [hC₁def]
  have hx2C : x 2 ∈ C₁ := by simp [hC₁def]
  have hCY : ∀ w ∈ C₁, w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with hw | hw
    · exact (hHyp.1 w hwY).1 hw
    rcases List.mem_cons.mp hw with hw | hw
    · exact (hHyp.1 w hwY).2.2.2 hw
    · exact hYout w (List.mem_of_mem_drop hw) hwY
  have honly := Thm192Claim7GapUniqueEdge.cut_only_complete hBerge hHyp.2.1 hP hi hin
    hC₁ hCY hzY hHyp.2.2.2.1 hHyp.2.2.2.2.1 (hws.2.2.2.2.2.2 1 (by omega))
    hzint hno
  have hPne1 : ∀ m (hm : m < P.length), m + 1 < P.length → (P[m]'hm) ≠ x 1 := by
    intro m hm hm1
    rw [← hlastP]
    exact fun he => by have := hP.1.2.1.getElem_inj_iff.mp he; omega
  have hPnez : ∀ m (hm : m < P.length), (P[m]'hm) ≠ z :=
    fun m hm he => hzP (he ▸ List.getElem_mem hm)
  have hx2ne1 : x 2 ≠ x 1 := fun he => by have := hws.2.1 2 le_rfl 1 (by omega) he; omega
  have hx2nez : x 2 ≠ z := (hws.2.2.1 2 le_rfl).2
  -- every member of `Y` has a neighbour among `x₂, pᵢ, …, pₙ`
  have hYnb : ∀ w ∈ Y, ∃ c ∈ C₁, c ≠ x 1 ∧ c ≠ z ∧ G.Adj w c := by
    intro w hw
    by_cases hwy : w = y
    · subst hwy
      rcases hycontact with h | h
      · exact ⟨x 2, hx2C, hx2ne1, hx2nez, h⟩
      · exact ⟨_, hmemP _ (by omega) (by omega), hPne1 _ (by omega) (by omega),
          hPnez _ (by omega), h⟩
    · exact ⟨_, hmemP k (by omega) hik, hPne1 k (by omega) (by omega), hPnez k (by omega),
        (hkc w ⟨hw, hwy⟩).symm⟩
  rcases Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y hHyp.2.1 C₁ hC₁ hCY
      (by simp only [holeLength]; omega) (x 1) z hx1C hzC
      (hws.2.2.2.2.2.2 1 (by omega)).symm hHyp.2.2.2.1 hzY
      (fun w hw hwc => (honly w hw hwc).symm) with ⟨h, hhY, hhat⟩ | ⟨a, haY, b, hbY, hl⟩
  · obtain ⟨c, hcC, hc1, hcz, hadj⟩ := hYnb h hhY
    exact hhat.2.2.2.2.2.2 c hcC hc1 hcz hadj
  -- the leap
  have hnd : C₁.Nodup := hC₁.2.1
  have hdel : ∀ c ∈ Y, ∀ w : V, (G.deleteEdges {s(x 1, z)}).Adj c w ↔ G.Adj c w := by
    intro c hc w
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨he, -⟩ | ⟨he, -⟩)
    · exact (hHyp.1 c hc).2.2.1 he
    · exact (hHyp.1 c hc).1 he
  have hlp : IsLeapForPath (G.deleteEdges {s(x 1, z)}) C₁ a b := by
    rcases hl with ⟨-, t, hhd, hlst, hlp⟩ | ⟨-, t, hhd, hlst, -⟩
    · have hrot : C₁.rotate t = C₁ := by
        have hr := Thm192Claim7Aux.rotate_index hnd (k := t) (j := 0)
          (show 0 < C₁.length by omega) (by rw [hC1zero]; exact hhd)
        simpa using hr
      rwa [hrot] at hlp
    · exfalso
      have hrot : C₁.rotate t = C₁.rotate (C₁.length - 1) :=
        Thm192Claim7Aux.rotate_index hnd (k := t) (j := C₁.length - 1)
          (by omega) (by rw [hC1last]; exact hhd)
      rw [hrot, Thm192Claim7Aux.getLast?_rotate (show 0 < C₁.length by omega),
        show (C₁.length - 1 + (C₁.length - 1)) % C₁.length = C₁.length - 2 by
          rw [show C₁.length - 1 + (C₁.length - 1) = C₁.length + (C₁.length - 2) by omega,
            Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega),
        List.getElem?_eq_getElem (show C₁.length - 2 < C₁.length by omega)] at hlst
      rw [hC1pen] at hlst
      exact hPnez _ (by omega) (Option.some.inj hlst)
  have hane : a ≠ b := hlp.2.2.1
  have hnab : ¬ G.Adj a b := fun hh => hlp.2.2.2.1 ((hdel a haY b).mpr hh)
  have haadj : ∀ (t : ℕ) (ht : t < C₁.length),
      (G.Adj a (C₁[t]'ht) ↔ (t = 0 ∨ t = 1 ∨ t = C₁.length - 1)) := by
    intro t ht
    rw [← hdel a haY]
    exact hlp.2.2.2.2.1 t ht
  have hbadj : ∀ (t : ℕ) (ht : t < C₁.length),
      (G.Adj b (C₁[t]'ht) ↔ (t = 0 ∨ t = C₁.length - 2 ∨ t = C₁.length - 1)) := by
    intro t ht
    rw [← hdel b hbY]
    exact hlp.2.2.2.2.2 t ht
  have hanot : ∀ m (hm : m < P.length), i ≤ m → m + 1 < P.length → ¬ G.Adj a (P[m]'hm) := by
    intro m hm him hm1 hadj
    rw [← hC1P m hm him (by omega)] at hadj
    have := (haadj (m - i + 2) (by omega)).mp hadj
    omega
  have hbnot : ∀ m (hm : m < P.length), i ≤ m → m + 2 < P.length → ¬ G.Adj b (P[m]'hm) := by
    intro m hm him hm2 hadj
    rw [← hC1P m hm him (by omega)] at hadj
    have := (hbadj (m - i + 2) (by omega)).mp hadj
    omega
  have hax2 : G.Adj a (x 2) := by
    have hh := (haadj 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    rwa [hC1one] at hh
  have hbx2 : ¬ G.Adj b (x 2) := by
    intro hadj
    have hh := (hbadj 1 (by omega)).mp (by rw [hC1one]; exact hadj)
    omega
  have hbpn : G.Adj b (P[P.length - 2]'(show P.length - 2 < P.length by omega)) := by
    have hh := (hbadj (C₁.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    rwa [hC1pen] at hh
  -- the path `a-x₂-pᵢ-⋯-pₙ-b`
  have hilt : i < P.length - 2 := by omega
  have hT : IsPathFrom G ((P.drop i).take (P.length - 2 - i + 1))
      (P[i]'(by omega)) (P[P.length - 2]'(by omega)) :=
    PathBasics.isPathFrom_slice hP.1 hilt (by omega)
  have hTmem : ∀ w ∈ (P.drop i).take (P.length - 2 - i + 1),
      ∃ m, ∃ hm : m < P.length, i ≤ m ∧ m ≤ P.length - 2 ∧ (P[m]'hm) = w :=
    fun w hw => (PathBasics.mem_slice_iff P (by omega) (show P.length - 2 < P.length by omega)).mp hw
  have hTP : ∀ w ∈ (P.drop i).take (P.length - 2 - i + 1), w ∈ P := by
    intro w hw
    obtain ⟨m, hm, -, -, rfl⟩ := hTmem w hw
    exact List.getElem_mem hm
  have hR1 : IsPathFrom G (x 2 :: (P.drop i).take (P.length - 2 - i + 1)) (x 2)
      (P[P.length - 2]'(by omega)) := by
    refine Thm192Claim7Aux.isPathFrom_cons hT hxI (fun hmem => hx2P (hTP _ hmem)) ?_
    intro w hw hwne
    obtain ⟨m, hm, him, hmn, rfl⟩ := hTmem w hw
    intro hadj
    exact hwne (hP.1.2.1.getElem_inj_iff.mpr ((hlast m hm him).mp hadj))
  have haY' : a ∉ P := fun hmem => hYout a hmem haY
  have hbY' : b ∉ P := fun hmem => hYout b hmem hbY
  have hane2 : a ≠ x 2 := fun he => (hHyp.1 a haY).2.2.2 he
  have hbne2 : b ≠ x 2 := fun he => (hHyp.1 b hbY).2.2.2 he
  have hR2 : IsPathFrom G (a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) a
      (P[P.length - 2]'(by omega)) := by
    refine Thm192Claim7Aux.isPathFrom_cons hR1 hax2 ?_ ?_
    · intro hmem
      rcases List.mem_cons.mp hmem with he | he
      · exact hane2 he
      · exact haY' (hTP _ he)
    · intro w hw hwne
      rcases List.mem_cons.mp hw with he | he
      · exact absurd he hwne
      · obtain ⟨m, hm, him, hmn, rfl⟩ := hTmem w he
        exact hanot m hm him (by omega)
  have hR : IsPathFrom G ((a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b]) a b := by
    refine Thm192Claim7Aux.isPathFrom_snoc hR2 hbpn ?_ ?_
    · intro hmem
      rcases List.mem_cons.mp hmem with he | he
      · exact hane he.symm
      rcases List.mem_cons.mp he with he | he
      · exact hbne2 he
      · exact hbY' (hTP _ he)
    · intro w hw hwne
      rcases List.mem_cons.mp hw with he | he
      · rw [he]; exact fun hadj => hnab hadj.symm
      rcases List.mem_cons.mp he with he | he
      · rw [he]; exact hbx2
      · obtain ⟨m, hm, him, hmn, rfl⟩ := hTmem w he
        refine hbnot m hm him ?_
        rcases Nat.lt_or_ge m (P.length - 2) with hlt | hge
        · omega
        · exact absurd (hP.1.2.1.getElem_inj_iff.mpr (show m = P.length - 2 by omega) ▸ rfl) hwne
  have hRlen : ((a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b]).length
      = C₁.length := by
    simp only [List.length_append, List.length_cons, List.length_take, List.length_drop,
      List.length_nil]
    omega
  -- 13.6 applied with the anticonnected set `{x₀, x₁}`
  have hX : AnticonnectedSet G ({x 0, x 1} : Set V) :=
    Thm192Claim7Aux.anticonnected_pair
      (fun he => by have := hws.2.1 0 (by omega) 1 (by omega) he; omega)
      (x0_not_adj_x1 hws)
  have hRmem : ∀ w ∈ (a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b],
      w = a ∨ w = x 2 ∨ (∃ m, ∃ hm : m < P.length, i ≤ m ∧ m ≤ P.length - 2 ∧
        (P[m]'hm) = w) ∨ w = b := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_cons.mp hw with he | hw
      · exact Or.inl he
      rcases List.mem_cons.mp hw with he | hw
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl (hTmem w hw)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hw)))
  have hxne0 : x 0 ≠ x 2 := fun he => by have := hws.2.1 0 (by omega) 2 le_rfl he; omega
  have hxne1 : x 1 ≠ x 2 := fun he => by have := hws.2.1 1 (by omega) 2 le_rfl he; omega
  have hXcompl : ∀ w ∈ (a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b],
      VertexComplete G w ({x 0, x 1} : Set V) → w = a ∨ w = b := by
    intro w hw hwc
    rcases hRmem w hw with he | he | ⟨m, hm, him, hmn, rfl⟩ | he
    · exact Or.inl he
    · exact (hx20 (he ▸ hwc (x 0) (by simp))).elim
    · exact (hnopair m hm (by omega) (by omega)
        ⟨hwc (x 0) (by simp), hwc (x 1) (by simp)⟩).elim
    · exact Or.inr he
  have hXP : ({x 0, x 1} : Set V) ⊆
      {v : V | v ∈ (a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b]}ᶜ := by
    intro v hv hmem
    have hv' : v = x 0 ∨ v = x 1 := by simpa using hv
    rcases hRmem v hmem with he | he | ⟨m, hm, him, hmn, rfl⟩ | he
    · rcases hv' with rfl | rfl
      · exact (hHyp.1 a haY).2.1 he.symm
      · exact (hHyp.1 a haY).2.2.1 he.symm
    · rcases hv' with rfl | rfl
      · exact hxne0 he
      · exact hxne1 he
    · rcases hv' with h0 | h1
      · have h00 : (P[0]'(by omega)) = x 0 :=
          PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
        rw [← h00] at h0
        have := hP.1.2.1.getElem_inj_iff.mp h0
        omega
      · rw [← hlastP] at h1
        have := hP.1.2.1.getElem_inj_iff.mp h1
        omega
    · rcases hv' with rfl | rfl
      · exact (hHyp.1 b hbY).2.1 he.symm
      · exact (hHyp.1 b hbY).2.2.1 he.symm
  have haXc : VertexComplete G a ({x 0, x 1} : Set V) := by
    intro w hw
    rcases (by simpa using hw : w = x 0 ∨ w = x 1) with rfl | rfl
    · exact (hHyp.2.2.1 a haY).symm
    · exact (hHyp.2.2.2.1 a haY).symm
  have hbXc : VertexComplete G b ({x 0, x 1} : Set V) := by
    intro w hw
    rcases (by simpa using hw : w = x 0 ∨ w = x 1) with rfl | rfl
    · exact (hHyp.2.2.1 b hbY).symm
    · exact (hHyp.2.2.2.1 b hbY).symm
  have hodd : Odd (pathLength ((a :: x 2 :: (P.drop i).take (P.length - 2 - i + 1)) ++ [b])) := by
    rw [PathBasics.pathLength_eq, hRlen]
    obtain ⟨r, hr⟩ := hC₁even
    exact ⟨r - 1, by omega⟩
  rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 _ a b hR hodd
      ({x 0, x 1} : Set V) hXP hX haXc hbXc with ⟨u, hu, v, hv, hE⟩ | ⟨h3, -⟩
  · rcases hXcompl u hu hE.2.1 with rfl | rfl
    · rcases hXcompl v hv hE.2.2 with rfl | rfl
      · exact G.irrefl hE.1
      · exact hnab hE.1
    · rcases hXcompl v hv hE.2.2 with rfl | rfl
      · exact hnab hE.1.symm
      · exact G.irrefl hE.1
  · rw [PathBasics.pathLength_eq, hRlen] at h3
    omega

end Workspace.ProofLemmas.Thm192Claim7ShortCut
