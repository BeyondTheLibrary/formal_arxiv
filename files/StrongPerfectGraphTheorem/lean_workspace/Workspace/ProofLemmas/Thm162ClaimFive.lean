import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentEndgame
-- extra imports needed only by the proof
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentYCount
import Workspace.ProofLemmas.Thm162SetupBasics
import Workspace.ProofLemmas.Thm153Rotated
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# 16.2, claim (5) and its mirror image

PAPER (16.2, printed p. 100).  Reproduces the printed argument step for step:

* *"If `p₁` is not `Y`-complete, then the `Y`-complete edge in `H₁` is disjoint from the path
  `p₁-f₁-⋯-f_k`, and so is the one in `H₂`; but this contradicts 15.3 applied to the hole
  `p₁-⋯-p_i-f_k-p_j-⋯-pₙ-p₁`.  So `p₁` is `Y`-complete."*  — `q0_yComplete_aux`, which builds
  that third hole as `[f_k] ++ arc C (b+c) (n-c+a+1)` and feeds it to `Thm153Rotated`.
* *"Since `H₁` contains only two `Y`-complete vertices and they are adjacent, the other is `p₂`,
  and similarly `pₙ` is `Y`-complete."*  — `preamble`.
* *"(5) `f_k` has no neighbour in `{p₃, …, p_{j−2}}`"* — `claim_five_core`, containing the
  counting argument for *"there is also a `Y`-complete vertex in this set"*, the choice of the
  path `P`, the even path `pₙ-⋯-p_j-f_k-P-x` (2.2) and the odd path `p₁-f₁-⋯-f_k-P-x` (13.6,
  then 2.2), packaged as `OddWheelAttachmentYCount.odd_YY_path_contradiction`.
* *"and similarly `f_k` has no neighbours in `{p_{i+2}, …, p_{n−1}}`"* — the same core lemma
  applied to the reversed rim `C.reverse`, whose cyclic reader is `t ↦ q (n - t)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm162ClaimFiveAux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentEndgame

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### A path with `Y`-complete ends and clean interior is even, if some `Y`-complete vertex
misses its interior.

PAPER (16.2, claim (5)): *"The path `pₙ-p_{n−1}-⋯-p_j-f_k-P-x` is even, since its ends are
`Y`-complete, no internal vertex is `Y`-complete, and the `Y`-complete vertex `p₁` has no
neighbour in its interior."* -/
theorem even_of_clean {G : SimpleGraph V} (hBerge : Berge G) {Y : Set V}
    (hYanti : AnticonnectedSet G Y) {W : List V} {u v z : V}
    (hW : IsPathFrom G W u v) (h3 : 3 ≤ W.length) (hWY : ∀ w ∈ W, w ∉ Y)
    (huY : VertexComplete G u Y) (hvY : VertexComplete G v Y)
    (hint : ∀ w ∈ SPGT.interior W, ¬ VertexComplete G w Y)
    (hzY : VertexComplete G z Y) (hznbr : ∀ w ∈ SPGT.interior W, ¬ G.Adj z w) :
    Even (pathLength W) := by
  classical
  by_contra hcon
  have hodd : Odd (pathLength W) := Nat.not_even_iff_odd.mp hcon
  have hW0 : (W[0]'(by omega)) = u := PathBasics.getElem_zero_of_head? hW.2.1 (by omega)
  have hWl : (W[W.length - 1]'(by omega)) = v :=
    PathBasics.getElem_last_of_getLast? hW.2.2 (by omega)
  have hends : ∀ x : V, x ∈ W → VertexComplete G x Y → x = u ∨ x = v := by
    intro x hxW hxY
    by_contra hc
    push Not at hc
    exact hint x ((PathBasics.mem_interior_iff_of_pathFrom hW).mpr ⟨hxW, hc.1, hc.2⟩) hxY
  have hnoedge : ¬ ∃ p ∈ W, ∃ r ∈ W, EdgeComplete G Y p r := by
    rintro ⟨p, hpW, r, hrW, hadj, hpY, hrY⟩
    have huv : G.Adj u v := by
      rcases hends p hpW hpY with rfl | rfl <;> rcases hends r hrW hrY with rfl | rfl
      · exact absurd rfl hadj.ne
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hadj.ne
    rw [← hW0, ← hWl] at huv
    exact PathBasics.path_ends_not_adj hW.1 h3 huv
  obtain ⟨w, hwint, hwadj⟩ :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti W u v hW hWY hodd huY hvY
      hnoedge z hzY
  exact hznbr w hwint hwadj

/-! ### The arc of the rim between two prescribed cyclic positions -/

theorem exists_arc_between {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D)
    (hpos : 0 < D.length) (β g h : ℕ) (hlen : max g h + 2 ≤ min g h + D.length) :
    ∃ A : List V, IsPathFrom G A (cyc D hpos (β + g)) (cyc D hpos (β + h)) ∧
      A.length = max g h - min g h + 1 ∧
      (∀ w : V, w ∈ A ↔ ∃ z : ℕ, min g h ≤ z ∧ z ≤ max g h ∧ cyc D hpos (β + z) = w) := by
  classical
  rcases Nat.le_total g h with hgh | hgh
  · refine ⟨arc D hpos (β + g) (h - g + 1), ?_, ?_, ?_⟩
    · have := arc_isPathFrom hD hpos (a := β + g) (L := h - g + 1) (by omega) (by omega)
      rw [show β + g + (h - g + 1) - 1 = β + h by omega] at this
      exact this
    · rw [arc_length]; omega
    · intro w
      rw [mem_arc hpos]
      constructor
      · rintro ⟨t, ht, hte⟩
        exact ⟨g + t, by omega, by omega, by rw [show β + (g + t) = β + g + t by omega]; exact hte⟩
      · rintro ⟨z, h1, h2, hze⟩
        refine ⟨z - g, by omega, ?_⟩
        rw [show β + g + (z - g) = β + z by omega]
        exact hze
  · refine ⟨(arc D hpos (β + h) (g - h + 1)).reverse, ?_, ?_, ?_⟩
    · have := arc_isPathFrom hD hpos (a := β + h) (L := g - h + 1) (by omega) (by omega)
      rw [show β + h + (g - h + 1) - 1 = β + g by omega] at this
      exact PathBasics.isPathFrom_reverse this
    · rw [List.length_reverse, arc_length]; omega
    · intro w
      rw [List.mem_reverse, mem_arc hpos]
      constructor
      · rintro ⟨t, ht, hte⟩
        exact ⟨h + t, by omega, by omega, by rw [show β + (h + t) = β + h + t by omega]; exact hte⟩
      · rintro ⟨z, h1, h2, hze⟩
        refine ⟨z - h, by omega, ?_⟩
        rw [show β + h + (z - h) = β + z by omega]
        exact hze

/-- A one-vertex list is a path from that vertex to itself. -/
theorem isPathFrom_singleton {G : SimpleGraph V} (x : V) : IsPathFrom G [x] x x := by
  refine ⟨⟨by simp, by simp, ?_⟩, rfl, rfl⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst hi0; subst hj0
  simp only [List.getElem_cons_zero]
  constructor
  · intro hadj; exact absurd hadj (G.irrefl (v := x))
  · rintro (h | h) <;> omega

/-! ### Claim (5) of 16.2, one direction -/

theorem claim_five_core {G : SimpleGraph V} (hG : InF6 G) {C : List V} {Y : Set V}
    (hw : IsWheel G C Y)
    {π : V → ℕ} (hπ2 : ∀ x : V, π x < 2)
    (hπ : ∀ x y : V, x ∈ C → y ∈ C → x ≠ y → (SameWheelParity G C Y x y ↔ π x = π y))
    {D : List V} (hD : IsHoleList G D) (hDpos : 0 < D.length)
    (hDC : ∀ w : V, w ∈ D ↔ w ∈ C) (hDn : D.length = C.length)
    (β : ℕ)
    {S : List V} {f : ℕ → V} {k : ℕ} (hk2 : 2 ≤ k)
    (hS : IsPathFrom G S (f 1) (f k)) (hSlen : S.length = k)
    (hSmem : ∀ x : V, x ∈ S ↔ ∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = x)
    (hf1k : f 1 ≠ f k)
    (hfinj : ∀ s t : ℕ, 1 ≤ s → s ≤ k → 1 ≤ t → t ≤ k → f s = f t → s = t)
    (hfnotC : ∀ t : ℕ, 1 ≤ t → t ≤ k → f t ∉ C)
    (hfnotY : ∀ t : ℕ, 1 ≤ t → t ≤ k → f t ∉ Y)
    (hfnc : ∀ t : ℕ, 1 ≤ t → t ≤ k → ¬ VertexComplete G (f t) Y)
    (hadjFst : ∀ u : V, u ∈ C → (G.Adj (f 1) u ↔ u = cyc D hDpos β))
    (hadjMid : ∀ t : ℕ, 2 ≤ t → t + 1 ≤ k → ∀ u : V, u ∈ C → ¬ G.Adj (f t) u)
    {a c : ℕ} (halb : 1 ≤ a) (hac2 : a + 2 ≤ c) (hcub : c + 1 ≤ C.length)
    (hnotAdj0 : ¬ G.Adj (f k) (cyc D hDpos β))
    (hadjc : G.Adj (f k) (cyc D hDpos (β + c)))
    (hrange : ∀ e : ℕ, e < C.length → G.Adj (f k) (cyc D hDpos (β + e)) → a ≤ e ∧ e ≤ c)
    (hY0 : VertexComplete G (cyc D hDpos β) Y)
    (hY1 : VertexComplete G (cyc D hDpos (β + 1)) Y)
    (hYn : VertexComplete G (cyc D hDpos (β + (C.length - 1))) Y)
    (hconfL : ∀ e : ℕ, 2 ≤ e → e ≤ a → ¬ VertexComplete G (cyc D hDpos (β + e)) Y)
    (hconfR : ∀ e : ℕ, c ≤ e → e + 2 ≤ C.length → ¬ VertexComplete G (cyc D hDpos (β + e)) Y)
    (hpar : Even (k + (C.length - c) + 1))
    (hnbrk : ∀ u : V, u ∈ C → G.Adj (f k) u → π u ≠ π (cyc D hDpos β)) :
    ∀ e : ℕ, 2 ≤ e → e + 2 ≤ c → ¬ G.Adj (f k) (cyc D hDpos (β + e)) := by
  classical
  intro d hd2 hdc hadjd
  ---------------------------------------------------------------- ambient facts
  have hCh : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hBerge : Berge G := hG.1.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have hCY : ∀ w ∈ C, w ∉ Y := hw.2.1.2.2
  have hcyccount : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  have hstep : ∀ x y : V, x ∈ C → y ∈ C → G.Adj x y → (π x ≠ π y ↔ EdgeComplete G Y x y) :=
    fun x y hx hy hadj => OddWheelAttachmentYCount.parity_step hCh hcyccount hπ hx hy hadj
  ---------------------------------------------------------------- the rim reader
  have hrmem : ∀ t : ℕ, cyc D hDpos (β + t) ∈ C := fun t => (hDC _).mp (cyc_mem hDpos _)
  have hrcongr : ∀ s t : ℕ, s % C.length = t % C.length →
      cyc D hDpos (β + s) = cyc D hDpos (β + t) := by
    intro s t h
    refine cyc_congr hDpos ?_
    rw [hDn]
    exact Nat.ModEq.add_left β h
  have hrinj : ∀ s t : ℕ, s < C.length → t < C.length →
      cyc D hDpos (β + s) = cyc D hDpos (β + t) → s = t := by
    intro s t hs ht he
    have h1 := cyc_inj hD hDpos he
    rw [hDn] at h1
    have h2 : s % C.length = t % C.length := Nat.ModEq.add_left_cancel' β h1
    rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h2
  have hradj : ∀ s t : ℕ, s < C.length → t < C.length →
      G.Adj (cyc D hDpos (β + s)) (cyc D hDpos (β + t)) →
      (t = s + 1 ∨ s = t + 1 ∨ (s = 0 ∧ t = C.length - 1) ∨ (t = 0 ∧ s = C.length - 1)) := by
    intro s t hs ht hadj
    rw [cyc_adj hD hDpos, hDn] at hadj
    rcases hadj with h | h
    · have h1 : (β + t) ≡ (β + (s + 1)) [MOD C.length] := by
        rw [← Nat.add_assoc]; exact h
      have h2 : t ≡ (s + 1) [MOD C.length] := Nat.ModEq.add_left_cancel' β h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt ht] at h2
      by_cases hsl : s + 1 < C.length
      · rw [Nat.mod_eq_of_lt hsl] at h2; omega
      · rw [show s + 1 = C.length by omega, Nat.mod_self] at h2; omega
    · have h1 : (β + s) ≡ (β + (t + 1)) [MOD C.length] := by
        rw [← Nat.add_assoc]; exact h
      have h2 : s ≡ (t + 1) [MOD C.length] := Nat.ModEq.add_left_cancel' β h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hs] at h2
      by_cases htl : t + 1 < C.length
      · rw [Nat.mod_eq_of_lt htl] at h2; omega
      · rw [show t + 1 = C.length by omega, Nat.mod_self] at h2; omega
  have hadjsucc : ∀ u : ℕ, G.Adj (cyc D hDpos (β + u)) (cyc D hDpos (β + (u + 1))) := by
    intro u
    refine (cyc_adj hD hDpos _ _).mpr (Or.inl ?_)
    rw [show β + (u + 1) = β + u + 1 by omega]
  have hadjwrap : G.Adj (cyc D hDpos β) (cyc D hDpos (β + (C.length - 1))) := by
    refine (cyc_adj hD hDpos _ _).mpr (Or.inr ?_)
    rw [hDn, show β + (C.length - 1) + 1 = β + C.length by omega, Nat.add_mod_right]
  have hrsurj : ∀ w : V, w ∈ C → ∃ z : ℕ, z < C.length ∧ cyc D hDpos (β + z) = w := by
    intro w hwC
    obtain ⟨t, ht, hte⟩ :=
      OddWheelAttachmentClaim4.exists_offset_cyc hDpos β ((hDC w).mpr hwC)
    exact ⟨t, by omega, hte⟩
  ---------------------------------------------------------------- π of the three known vertices
  have hne01 : π (cyc D hDpos β) ≠ π (cyc D hDpos (β + 1)) := by
    refine (hstep _ _ (by simpa using hrmem 0) (hrmem 1) ?_).mpr ⟨?_, hY0, hY1⟩ <;>
      simpa using hadjsucc 0
  have hne0n : π (cyc D hDpos β) ≠ π (cyc D hDpos (β + (C.length - 1))) :=
    (hstep _ _ (by simpa using hrmem 0) (hrmem _) hadjwrap).mpr ⟨hadjwrap, hY0, hYn⟩
  have hπ1n : π (cyc D hDpos (β + 1)) = π (cyc D hDpos (β + (C.length - 1))) := by
    have h1 := hπ2 (cyc D hDpos β)
    have h2 := hπ2 (cyc D hDpos (β + 1))
    have h3 := hπ2 (cyc D hDpos (β + (C.length - 1)))
    omega
  ---------------------------------------------------------------- Step A
  obtain ⟨e0, he0a, he0b, he0c⟩ :
      ∃ e : ℕ, 2 ≤ e ∧ e + 2 ≤ c ∧ VertexComplete G (cyc D hDpos (β + e)) Y := by
    by_contra hcon
    have hnoY : ∀ e : ℕ, 2 ≤ e → e + 2 ≤ c → ¬ VertexComplete G (cyc D hDpos (β + e)) Y :=
      fun e h1 h2 h3 => hcon ⟨e, h1, h2, h3⟩
    have hposcl : ∀ e : ℕ, e < C.length → VertexComplete G (cyc D hDpos (β + e)) Y →
        e = 0 ∨ e = 1 ∨ e = c - 1 ∨ e = C.length - 1 := by
      intro e he hec
      by_contra hc2
      push Not at hc2
      obtain ⟨h0, h1, h2, h3⟩ := hc2
      rcases Nat.lt_or_ge e (a + 1) with hcase | hcase
      · exact hconfL e (by omega) (by omega) hec
      · rcases Nat.lt_or_ge e c with hcase' | hcase'
        · exact hnoY e (by omega) (by omega) hec
        · exact hconfR e (by omega) (by omega) hec
    have htel := OddWheelAttachmentArcs.parity_telescope (G := G) (C := C) (Y := Y) (π := π)
      hπ2 hstep (fun t => cyc D hDpos (β + t)) 1 (C.length - 1) (by omega)
      (fun t _ _ => hrmem t) (fun t _ _ => hadjsucc t)
    simp only at htel
    have hcard1 : ((Finset.Ico 1 (C.length - 1)).filter
        (fun t => EdgeComplete G Y (cyc D hDpos (β + t)) (cyc D hDpos (β + (t + 1))))).card
          ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
      obtain ⟨⟨hx1, hx2⟩, hxE⟩ := hx
      obtain ⟨⟨hy1, hy2⟩, hyE⟩ := hy
      have hx3 := hposcl x (by omega) hxE.2.1
      have hx4 := hposcl (x + 1) (by omega) hxE.2.2
      have hy3 := hposcl y (by omega) hyE.2.1
      have hy4 := hposcl (y + 1) (by omega) hyE.2.2
      omega
    have hpp1 := hπ2 (cyc D hDpos (β + 1))
    have hpp2 := hπ2 (cyc D hDpos (β + (C.length - 1)))
    have hcard0 : ((Finset.Ico 1 (C.length - 1)).filter
        (fun t => EdgeComplete G Y (cyc D hDpos (β + t)) (cyc D hDpos (β + (t + 1))))).card
          = 0 := by
      rw [hπ1n] at htel
      omega
    have hempty : ∀ t : ℕ, 1 ≤ t → t + 1 < C.length →
        ¬ EdgeComplete G Y (cyc D hDpos (β + t)) (cyc D hDpos (β + (t + 1))) := by
      intro t h1 h2 hEc
      have hmem : t ∈ (Finset.Ico 1 (C.length - 1)).filter
          (fun t => EdgeComplete G Y (cyc D hDpos (β + t)) (cyc D hDpos (β + (t + 1)))) := by
        simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨h1, by omega⟩, hEc⟩
      rw [Finset.card_eq_zero] at hcard0
      rw [hcard0] at hmem
      exact absurd hmem (Finset.notMem_empty t)
    have hedge0 : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
        u = cyc D hDpos β ∨ v = cyc D hDpos β := by
      intro u v huC hvC hEc
      obtain ⟨x, hx, hxe⟩ := hrsurj u huC
      obtain ⟨y, hy, hye⟩ := hrsurj v hvC
      have hadj : G.Adj (cyc D hDpos (β + x)) (cyc D hDpos (β + y)) := by
        rw [hxe, hye]; exact hEc.1
      rcases hradj x y hx hy hadj with hcase | hcase | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · subst hcase
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · exact Or.inl hxe.symm
        · exact absurd (by rw [hxe, hye]; exact hEc) (hempty x hx0 (by omega))
      · subst hcase
        rcases Nat.eq_zero_or_pos y with rfl | hy0
        · exact Or.inr hye.symm
        · refine absurd (show EdgeComplete G Y (cyc D hDpos (β + y)) (cyc D hDpos (β + (y + 1)))
            by rw [hye, hxe]; exact ⟨hEc.1.symm, hEc.2.2, hEc.2.1⟩) (hempty y hy0 (by omega))
      · subst hc1
        exact Or.inl hxe.symm
      · subst hc1
        exact Or.inr hye.symm
    obtain ⟨A₀, B₀, D₀, E₀, hA₀, hB₀, hD₀, hE₀, hAB, hDE, hn1, hn2, hn3, hn4⟩ := hw.2.2
    rcases hedge0 A₀ B₀ hA₀ hB₀ hAB with hh | hh <;>
      rcases hedge0 D₀ E₀ hD₀ hE₀ hDE with hh' | hh'
    · exact hn1 (by rw [hh, hh'])
    · exact hn2 (by rw [hh, hh'])
    · exact hn3 (by rw [hh, hh'])
    · exact hn4 (by rw [hh, hh'])
  ---------------------------------------------------------------- Step B: the closest pair
  have hexpair : ∃ p : ℕ × ℕ,
      (2 ≤ p.1 ∧ p.1 + 2 ≤ c ∧ G.Adj (f k) (cyc D hDpos (β + p.1))) ∧
      (2 ≤ p.2 ∧ p.2 + 2 ≤ c ∧ VertexComplete G (cyc D hDpos (β + p.2)) Y) :=
    ⟨(d, e0), ⟨hd2, hdc, hadjd⟩, ⟨he0a, he0b, he0c⟩⟩
  obtain ⟨⟨g, h⟩, ⟨⟨hg2, hgc, hgadj⟩, ⟨hh2, hhc, hhY⟩⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : ℕ × ℕ =>
        (2 ≤ p.1 ∧ p.1 + 2 ≤ c ∧ G.Adj (f k) (cyc D hDpos (β + p.1))) ∧
        (2 ≤ p.2 ∧ p.2 + 2 ≤ c ∧ VertexComplete G (cyc D hDpos (β + p.2)) Y))
      (fun p => max p.1 p.2 - min p.1 p.2) hexpair
  simp only at hmin hg2 hgc hgadj hh2 hhc hhY
  have hbetweenAdj : ∀ z : ℕ, min g h < z → z < max g h →
      ¬ G.Adj (f k) (cyc D hDpos (β + z)) := by
    intro z hz1 hz2 hadjz
    have := hmin (z, h) ⟨⟨by omega, by omega, hadjz⟩, ⟨hh2, hhc, hhY⟩⟩
    simp only at this
    omega
  have hbetweenY : ∀ z : ℕ, min g h < z → z < max g h →
      ¬ VertexComplete G (cyc D hDpos (β + z)) Y := by
    intro z hz1 hz2 hYz
    have := hmin (g, z) ⟨⟨hg2, hgc, hgadj⟩, ⟨by omega, by omega, hYz⟩⟩
    simp only at this
    omega
  have hgnotY : g ≠ h → ¬ VertexComplete G (cyc D hDpos (β + g)) Y := by
    intro hne hYg
    have := hmin (g, g) ⟨⟨hg2, hgc, hgadj⟩, ⟨hg2, hgc, hYg⟩⟩
    simp only at this
    omega
  have hhnotAdj : g ≠ h → ¬ G.Adj (f k) (cyc D hDpos (β + h)) := by
    intro hne hadjh
    have := hmin (h, h) ⟨⟨hh2, hhc, hadjh⟩, ⟨hh2, hhc, hhY⟩⟩
    simp only at this
    omega
  ---------------------------------------------------------------- the arc `P \ f_k`
  obtain ⟨A, hA, hAlen, hAmem⟩ := exists_arc_between hD hDpos β g h (by omega)
  have hfkC : f k ∉ C := hfnotC k (by omega) le_rfl
  have hAsub : ∀ w : V, w ∈ A → ∃ z : ℕ, min g h ≤ z ∧ z ≤ max g h ∧
      cyc D hDpos (β + z) = w := fun w hw => (hAmem w).mp hw
  have hAmemC : ∀ w : V, w ∈ A → w ∈ C := by
    intro w hw
    obtain ⟨z, _, _, hze⟩ := hAsub w hw
    rw [← hze]; exact hrmem z
  have hfkA : ∀ z : ℕ, min g h ≤ z → z ≤ max g h →
      (G.Adj (f k) (cyc D hDpos (β + z)) ↔ z = g) := by
    intro z hz1 hz2
    constructor
    · intro hadjz
      by_contra hzne
      rcases Nat.lt_or_ge (min g h) z with hlt | hge
      · rcases Nat.lt_or_ge z (max g h) with hlt2 | hge2
        · exact hbetweenAdj z hlt hlt2 hadjz
        · exact hhnotAdj (by omega) (by rw [show h = z by omega]; exact hadjz)
      · exact hhnotAdj (by omega) (by rw [show h = z by omega]; exact hadjz)
    · rintro rfl; exact hgadj
  have hPrime : IsPathFrom G ([f k] ++ A) (f k) (cyc D hDpos (β + h)) := by
    refine PathGlue.glue_path (isPathFrom_singleton (f k)) hA ?_ ?_
    · intro x hx hxA
      rw [List.mem_singleton] at hx
      exact hfkC (by rw [← hx]; exact hAmemC x hxA)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨z, hz1, hz2, hze⟩ := hAsub y hy
      rw [← hze, hfkA z hz1 hz2]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨-, heq⟩
        exact hrinj z g (by omega) (by omega) heq
  ---------------------------------------------------------------- the arc `pₙ-⋯-p_j`
  obtain ⟨B, hB, hBlen, hBmem⟩ := exists_arc_between hD hDpos β (C.length - 1) c (by omega)
  have hBsub : ∀ w : V, w ∈ B → ∃ z : ℕ, c ≤ z ∧ z ≤ C.length - 1 ∧
      cyc D hDpos (β + z) = w := by
    intro w hw
    obtain ⟨z, h1, h2, h3⟩ := (hBmem w).mp hw
    exact ⟨z, by omega, by omega, h3⟩
  have hBmemC : ∀ w : V, w ∈ B → w ∈ C := by
    intro w hw
    obtain ⟨z, _, _, hze⟩ := hBsub w hw
    rw [← hze]; exact hrmem z
  have hBlen' : B.length = C.length - c := by rw [hBlen]; omega
  have hW2 : IsPathFrom G (B ++ ([f k] ++ A)) (cyc D hDpos (β + (C.length - 1)))
      (cyc D hDpos (β + h)) := by
    refine PathGlue.glue_path hB hPrime ?_ ?_
    · intro x hxB hxP
      obtain ⟨z, hz1, hz2, hze⟩ := hBsub x hxB
      rcases List.mem_append.mp hxP with hx1 | hx2
      · rw [List.mem_singleton] at hx1
        exact hfkC (by rw [← hx1]; exact hBmemC x hxB)
      · obtain ⟨w, hw1, hw2, hwe⟩ := hAsub x hx2
        have : z = w := hrinj z w (by omega) (by omega) (by rw [hze, hwe])
        omega
    · intro x hxB y hyP
      obtain ⟨z, hz1, hz2, hze⟩ := hBsub x hxB
      rcases List.mem_append.mp hyP with hy1 | hy2
      · rw [List.mem_singleton] at hy1
        subst hy1
        rw [← hze]
        constructor
        · intro hadjz
          refine ⟨?_, rfl⟩
          have := hrange z (by omega) hadjz.symm
          exact congrArg _ (by omega : β + z = β + c)
        · rintro ⟨heq, -⟩
          have : z = c := hrinj z c (by omega) (by omega) heq
          subst this
          exact hadjc.symm
      · obtain ⟨w, hw1, hw2, hwe⟩ := hAsub y hy2
        rw [← hze, ← hwe]
        constructor
        · intro hadjz
          exact absurd (hradj z w (by omega) (by omega) hadjz) (by omega)
        · rintro ⟨-, heq⟩
          exact absurd (by rw [← heq]; exact hrmem w) hfkC
  ---------------------------------------------------------------- membership in `W₂`
  have hW2mem : ∀ w : V, w ∈ (B ++ ([f k] ++ A)) →
      (∃ z : ℕ, c ≤ z ∧ z ≤ C.length - 1 ∧ cyc D hDpos (β + z) = w) ∨ w = f k ∨
        (∃ z : ℕ, min g h ≤ z ∧ z ≤ max g h ∧ cyc D hDpos (β + z) = w) := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact Or.inl (hBsub w h1)
    · rcases List.mem_append.mp h2 with h3 | h4
      · exact Or.inr (Or.inl (List.mem_singleton.mp h3))
      · exact Or.inr (Or.inr (hAsub w h4))
  have hW2Y : ∀ w ∈ (B ++ ([f k] ++ A)), w ∉ Y := by
    intro w hw
    rcases hW2mem w hw with ⟨z, _, _, hze⟩ | rfl | ⟨z, _, _, hze⟩
    · exact hCY w (by rw [← hze]; exact hrmem z)
    · exact hfnotY k (by omega) le_rfl
    · exact hCY w (by rw [← hze]; exact hrmem z)
  have hW2int : ∀ w ∈ SPGT.interior (B ++ ([f k] ++ A)),
      ¬ VertexComplete G w Y ∧ ¬ G.Adj (cyc D hDpos β) w := by
    intro w hw
    obtain ⟨hwW, hwne1, hwne2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hW2).mp hw
    rcases hW2mem w hwW with ⟨z, hz1, hz2, hze⟩ | rfl | ⟨z, hz1, hz2, hze⟩
    · have hzn : z ≠ C.length - 1 := by
        intro he; exact hwne1 (by rw [← hze, he])
      refine ⟨by rw [← hze]; exact hconfR z hz1 (by omega), ?_⟩
      intro hadjw
      rw [← hze] at hadjw
      exact absurd (hradj 0 z (by omega) (by omega) hadjw) (by omega)
    · exact ⟨hfnc k (by omega) le_rfl, fun hadjw => hnotAdj0 hadjw.symm⟩
    · have hzh : z ≠ h := by
        intro he; exact hwne2 (by rw [← hze, he])
      refine ⟨?_, ?_⟩
      · rw [← hze]
        rcases Nat.lt_or_ge (min g h) z with hlt | hge
        · rcases Nat.lt_or_ge z (max g h) with hlt2 | hge2
          · exact hbetweenY z hlt hlt2
          · rw [show z = g by omega]; exact hgnotY (by omega)
        · rw [show z = g by omega]; exact hgnotY (by omega)
      · intro hadjw
        rw [← hze] at hadjw
        exact absurd (hradj 0 z (by omega) (by omega) hadjw) (by omega)
  have hW2even : Even (pathLength (B ++ ([f k] ++ A))) := by
    refine even_of_clean hBerge hYanti hW2 ?_ hW2Y hYn hhY
      (fun w hw => (hW2int w hw).1) hY0 (fun w hw => (hW2int w hw).2)
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen', hAlen]
    omega
  ---------------------------------------------------------------- the odd path `p₁-f₁-⋯-f_k-P-x`
  have hS1 : IsPathFrom G ([cyc D hDpos β] ++ S) (cyc D hDpos β) (f k) := by
    refine PathGlue.glue_path (isPathFrom_singleton _) hS ?_ ?_
    · intro x hx hxS
      rw [List.mem_singleton] at hx
      obtain ⟨t, ht1, ht2, hte⟩ := (hSmem x).mp hxS
      exact hfnotC t ht1 ht2 (by rw [hte, hx]; exact hrmem 0)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨t, ht1, ht2, hte⟩ := (hSmem y).mp hy
      rw [← hte]
      constructor
      · intro hadjt
        refine ⟨rfl, ?_⟩
        by_cases htk : t = k
        · exact absurd (by rw [← htk]; exact hadjt.symm) hnotAdj0
        · by_cases ht1' : t = 1
          · rw [ht1']
          · exact absurd hadjt.symm (hadjMid t (by omega) (by omega) _ (hrmem 0))
      · rintro ⟨-, heq⟩
        rw [heq]
        exact ((hadjFst (cyc D hDpos β) (hrmem 0)).mpr rfl).symm
  have hW1 : IsPathFrom G (([cyc D hDpos β] ++ S) ++ A) (cyc D hDpos β)
      (cyc D hDpos (β + h)) := by
    refine PathGlue.glue_path hS1 hA ?_ ?_
    · intro x hx hxA
      obtain ⟨w, hw1, hw2, hwe⟩ := hAsub x hxA
      rcases List.mem_append.mp hx with h1 | h2
      · rw [List.mem_singleton] at h1
        subst h1
        have : (0 : ℕ) = w := hrinj 0 w (by omega) (by omega) hwe.symm
        omega
      · obtain ⟨t, ht1, ht2, hte⟩ := (hSmem x).mp h2
        exact hfnotC t ht1 ht2 (by rw [hte]; exact hAmemC x hxA)
    · intro x hx y hy
      obtain ⟨w, hw1, hw2, hwe⟩ := hAsub y hy
      rcases List.mem_append.mp hx with h1 | h2
      · rw [List.mem_singleton] at h1
        subst h1
        rw [← hwe]
        constructor
        · intro hadjw
          exact absurd (hradj 0 w (by omega) (by omega) hadjw) (by omega)
        · rintro ⟨heq, -⟩
          exact absurd (by rw [← heq]; exact hrmem 0) hfkC
      · obtain ⟨t, ht1, ht2, hte⟩ := (hSmem x).mp h2
        rw [← hte, ← hwe]
        by_cases htk : t = k
        · subst htk
          rw [hfkA w hw1 hw2]
          constructor
          · rintro rfl; exact ⟨rfl, rfl⟩
          · rintro ⟨-, heq⟩
            exact hrinj w g (by omega) (by omega) heq
        · constructor
          · intro hadjw
            by_cases ht1' : t = 1
            · subst ht1'
              have := (hadjFst _ (hrmem w)).mp hadjw
              have : w = 0 := hrinj w 0 (by omega) (by omega) this
              omega
            · exact absurd hadjw (hadjMid t (by omega) (by omega) _ (hrmem w))
          · rintro ⟨heq, -⟩
            exact absurd (hfinj t k ht1 ht2 (by omega) le_rfl heq) htk
  have hW1mem : ∀ w : V, w ∈ (([cyc D hDpos β] ++ S) ++ A) →
      w = cyc D hDpos β ∨ (∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = w) ∨
        (∃ z : ℕ, min g h ≤ z ∧ z ≤ max g h ∧ cyc D hDpos (β + z) = w) := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · rcases List.mem_append.mp h1 with h3 | h4
      · exact Or.inl (List.mem_singleton.mp h3)
      · exact Or.inr (Or.inl ((hSmem w).mp h4))
    · exact Or.inr (Or.inr (hAsub w h2))
  have hW1Y : ∀ w ∈ (([cyc D hDpos β] ++ S) ++ A), w ∉ Y := by
    intro w hw
    rcases hW1mem w hw with rfl | ⟨t, ht1, ht2, rfl⟩ | ⟨z, _, _, hze⟩
    · exact hCY _ (hrmem 0)
    · exact hfnotY t ht1 ht2
    · exact hCY w (by rw [← hze]; exact hrmem z)
  have hW1int : ∀ w ∈ SPGT.interior (([cyc D hDpos β] ++ S) ++ A),
      ¬ VertexComplete G w Y := by
    intro w hw
    obtain ⟨hwW, hwne1, hwne2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hW1).mp hw
    rcases hW1mem w hwW with rfl | ⟨t, ht1, ht2, rfl⟩ | ⟨z, hz1, hz2, hze⟩
    · exact absurd rfl hwne1
    · exact hfnc t ht1 ht2
    · have hzh : z ≠ h := by
        intro he; exact hwne2 (by rw [← hze, he])
      rw [← hze]
      rcases Nat.lt_or_ge (min g h) z with hlt | hge
      · rcases Nat.lt_or_ge z (max g h) with hlt2 | hge2
        · exact hbetweenY z hlt hlt2
        · rw [show z = g by omega]; exact hgnotY (by omega)
      · rw [show z = g by omega]; exact hgnotY (by omega)
  have hW1odd : Odd (pathLength (([cyc D hDpos β] ++ S) ++ A)) := by
    have hlen2 : (B ++ ([f k] ++ A)).length = (C.length - c) + (1 + A.length) := by
      simp only [List.length_append, List.length_cons, List.length_nil, hBlen']
    have hlen1 : (([cyc D hDpos β] ++ S) ++ A).length = (1 + k) + A.length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hSlen]
    have hAge : 1 ≤ A.length := by rw [hAlen]; omega
    have hcn : c ≤ C.length := by omega
    rw [Nat.odd_iff]
    rw [SPGT.pathLength, hlen2, Nat.even_iff] at hW2even
    rw [Nat.even_iff] at hpar
    rw [SPGT.pathLength, hlen1]
    omega
  ---------------------------------------------------------------- 13.6 and 2.2
  have hf1mem : f 1 ∈ (([cyc D hDpos β] ++ S) ++ A) := by
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    exact (hSmem (f 1)).mpr ⟨1, le_rfl, by omega, rfl⟩
  have hfkmem : f k ∈ (([cyc D hDpos β] ++ S) ++ A) := by
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    exact (hSmem (f k)).mpr ⟨k, by omega, le_rfl, rfl⟩
  refine OddWheelAttachmentYCount.odd_YY_path_contradiction hG hw hπ2 hπ hW1 hW1odd hY0 hhY
    hW1int hW1Y ?_ ?_ hf1k ?_ hnbrk
  · refine (PathBasics.mem_interior_iff_of_pathFrom hW1).mpr ⟨hf1mem, ?_, ?_⟩
    · intro he; exact hfnotC 1 le_rfl (by omega) (by rw [he]; exact hrmem 0)
    · intro he; exact hfnotC 1 le_rfl (by omega) (by rw [he]; exact hrmem h)
  · refine (PathBasics.mem_interior_iff_of_pathFrom hW1).mpr ⟨hfkmem, ?_, ?_⟩
    · intro he; exact hfkC (by rw [he]; exact hrmem 0)
    · intro he; exact hfkC (by rw [he]; exact hrmem h)
  · intro u huC hadju
    exact (hadjFst u huC).mp hadju

theorem mod_pair_eq {n x y : ℕ} (hn : 0 < n) (hx : x < n) (hy : y < n)
    (hh : (x + y) % n = (n - 1) % n) : x + y = n - 1 := by
  rw [Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hh
  rcases Nat.lt_or_ge (x + y) n with hc | hc
  · rwa [Nat.mod_eq_of_lt hc] at hh
  · exfalso
    have hrw : (x + y) % n = x + y - n := by
      conv_lhs => rw [show x + y = (x + y - n) + n by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### *"So `p₁` is `Y`-complete"* — 15.3 applied to `p₁-⋯-p_i-f_k-p_j-⋯-pₙ-p₁` -/

theorem q0_yComplete_aux {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V}
    {q f : ℕ → V} {b a c k : ℕ}
    (hs : Setup G C Y P q f b a c k) (hac2 : a + 2 ≤ c) (hp : 0 < C.length)
    {t s : ℕ} (ht1 : 1 ≤ t) (ht2 : t + 1 ≤ a) (hs1 : c ≤ s) (hs2 : s + 2 ≤ C.length)
    (hYt : VertexComplete G (q t) Y) (hYt1 : VertexComplete G (q (t + 1)) Y)
    (hYs : VertexComplete G (q s) Y) (hYs1 : VertexComplete G (q (s + 1)) Y)
    (hYleft : ∀ e : ℕ, e ≤ a → VertexComplete G (q e) Y → e = t ∨ e = t + 1)
    (hYright : ∀ e : ℕ, c ≤ e → e < C.length → VertexComplete G (q e) Y → e = s ∨ e = s + 1)
    (hq0 : ¬ VertexComplete G (q 0) Y) :
    False := by
  classical
  have hC : IsHoleList G C := Thm162SetupBasics.holeC hs
  have hn6 : 6 ≤ C.length := Thm162SetupBasics.n6 hs
  have hcub := hs.cub
  have hklb := hs.klb
  have halb := hs.alb
  have hCY : ∀ w ∈ C, w ∉ Y := hs.wheel.2.1.2.2
  have hfkC : f k ∉ C := hs.fnotC k (by omega) le_rfl
  have hqmod : ∀ x y : ℕ, q x = q y → x % C.length = y % C.length := by
    intro x y hxy
    rw [Thm162SetupBasics.q_eq hs hp x, Thm162SetupBasics.q_eq hs hp y] at hxy
    exact Nat.ModEq.add_left_cancel' b (cyc_inj hC hp hxy)
  ---------------------------------------------------------------- the arc `p_j-⋯-pₙ-p₁-⋯-p_i`
  have hL1 : 1 ≤ C.length - c + a + 1 := by omega
  have hL2 : C.length - c + a + 1 + 1 ≤ C.length := by omega
  have hqcu : ∀ u : ℕ, cyc C hp (b + c + u) = q (c + u) := by
    intro u
    rw [show b + c + u = b + (c + u) by omega, ← Thm162SetupBasics.q_eq hs hp (c + u)]
  have hmodsub : ∀ x : ℕ, C.length ≤ x → x % C.length = (x - C.length) % C.length := by
    intro x hx
    conv_lhs => rw [show x = (x - C.length) + C.length by omega]
    exact Nat.add_mod_right _ _
  have hqc0 : cyc C hp (b + c) = q c := (Thm162SetupBasics.q_eq hs hp c).symm
  have hqLend : q (c + (C.length - c + a + 1 - 1)) = q a :=
    Thm162SetupBasics.q_congr hs hp (by
      rw [show c + (C.length - c + a + 1 - 1) = a + C.length by omega]
      exact Nat.add_mod_right a C.length)
  have harc : IsPathFrom G (arc C hp (b + c) (C.length - c + a + 1)) (q c) (q a) := by
    have hh := arc_isPathFrom hC hp (a := b + c) (L := C.length - c + a + 1) hL1 hL2
    rw [hqc0, show b + c + (C.length - c + a + 1) - 1 = b + c + (C.length - c + a + 1 - 1) by omega,
      hqcu (C.length - c + a + 1 - 1), hqLend] at hh
    exact hh
  have harcinj : ∀ u u' : ℕ, u < C.length - c + a + 1 → u' < C.length - c + a + 1 →
      q (c + u) = q (c + u') → u = u' := by
    intro u u' hu hu' he
    have h1 := hqmod _ _ he
    have h2 : u % C.length = u' % C.length := Nat.ModEq.add_left_cancel' c h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  have hadjarc : ∀ u : ℕ, u < C.length - c + a + 1 →
      (G.Adj (f k) (q (c + u)) ↔ (u = 0 ∨ u = C.length - c + a + 1 - 1)) := by
    intro u hu
    constructor
    · intro hadj
      by_cases hlt : c + u < C.length
      · have := Thm162SetupBasics.fk_adj_range hs hp (d := c + u) hlt hadj
        omega
      · have he : q (c + u) = q (c + u - C.length) :=
          Thm162SetupBasics.q_congr hs hp (hmodsub (c + u) (by omega))
        rw [he] at hadj
        have := Thm162SetupBasics.fk_adj_range hs hp (d := c + u - C.length) (by omega) hadj
        omega
    · rintro (rfl | rfl)
      · simpa using hs.adjLstMax
      · rw [hqLend]; exact hs.adjLstMin
  have hqcqa : q c ≠ q a := by
    intro he
    have := hqmod _ _ he
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  ---------------------------------------------------------------- the hole `H₃`
  have hH3 : IsHoleList G ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) := by
    refine PathGlue.glue_hole (isPathFrom_singleton (f k)) harc ?_ ?_ ?_
    · intro x hx hxa
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨u, hu, hue⟩ := (mem_arc hp).mp hxa
      exact hfkC (by rw [← hue]; exact cyc_mem hp _)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨u, hu, hue⟩ := (mem_arc hp).mp hy
      rw [← hue, hqcu u, hadjarc u hu]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, by simp⟩
        · exact Or.inr ⟨rfl, hqLend⟩
      · rintro (⟨-, he⟩ | ⟨-, he⟩)
        · left
          refine harcinj u 0 hu (by omega) ?_
          simpa using he
        · right
          exact harcinj u _ hu (by omega) (by rw [he, hqLend])
    · rw [arc_length]; simp; omega
  have hm : ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length
      = C.length - c + a + 2 := by
    rw [List.length_append, arc_length]; simp; omega
  have hpos3 : 0 < ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length := by omega
  have hget0 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3 0 = f k := by
    rw [cyc_eq hpos3 (by omega)]
    simp
  have hgetu : ∀ z : ℕ, 1 ≤ z → z < C.length - c + a + 2 →
      cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3 z = q (c + (z - 1)) := by
    intro z h1 h2
    rw [cyc_eq hpos3 (by omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    rw [arc_getElem, hqcu (z - 1)]
  ---------------------------------------------------------------- the six special positions
  have hV2 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3 (2 + s - c)
      = q (s + 1) := by
    rw [hgetu (2 + s - c) (by omega) (by omega)]
    exact congrArg q (by omega)
  have hV1 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3
      (2 + s - c + (([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length - 1)) = q s := by
    rw [cyc_congr hpos3 (show (2 + s - c +
        (([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length - 1))
          % ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length
        = (1 + s - c) % ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length by
      rw [show 2 + s - c + (([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length - 1)
          = (1 + s - c) + ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length by omega,
        Nat.add_mod_right]),
      hgetu (1 + s - c) (by omega) (by omega)]
    exact congrArg q (by omega)
  have hV3 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3
      (2 + s - c + (C.length + t - s - 1)) = q t := by
    rw [hgetu _ (by omega) (by omega)]
    refine Thm162SetupBasics.q_congr hs hp ?_
    rw [show c + (2 + s - c + (C.length + t - s - 1) - 1) = t + C.length by omega]
    exact Nat.add_mod_right t C.length
  have hV4 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3
      (2 + s - c + (C.length + t - s)) = q (t + 1) := by
    rw [hgetu _ (by omega) (by omega)]
    refine Thm162SetupBasics.q_congr hs hp ?_
    rw [show c + (2 + s - c + (C.length + t - s) - 1) = (t + 1) + C.length by omega]
    exact Nat.add_mod_right (t + 1) C.length
  have hV5 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3
      (2 + s - c + (C.length - s - 1)) = q 0 := by
    rw [hgetu _ (by omega) (by omega)]
    refine Thm162SetupBasics.q_congr hs hp ?_
    rw [show c + (2 + s - c + (C.length - s - 1) - 1) = 0 + C.length by omega]
    exact Nat.add_mod_right 0 C.length
  have hV6 : cyc ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)) hpos3
      (2 + s - c + (C.length + a - s + 1 - 1)) = f k := by
    rw [cyc_congr hpos3 (show (2 + s - c + (C.length + a - s + 1 - 1))
        % ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length
        = 0 % ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length by
      rw [show 2 + s - c + (C.length + a - s + 1 - 1)
          = 0 + ([f k] ++ arc C hp (b + c) (C.length - c + a + 1)).length by omega,
        Nat.add_mod_right])]
    simpa using hget0
  ---------------------------------------------------------------- the path `p₁-f₁-⋯-f_k`
  have hFpath : IsPathFrom G ([q 0] ++ Thm162SetupBasics.fpath P k) (q 0) (f k) := by
    refine PathGlue.glue_path (isPathFrom_singleton _) (Thm162SetupBasics.fpath_isPathFrom hs)
      ?_ ?_
    · intro x hx hxS
      rw [List.mem_singleton] at hx
      obtain ⟨u, hu1, hu2, hue⟩ := (Thm162SetupBasics.mem_fpath hs).mp hxS
      exact hs.fnotC u hu1 hu2 (by rw [hue, hx]; exact Thm162SetupBasics.q_mem hs hp 0)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨u, hu1, hu2, hue⟩ := (Thm162SetupBasics.mem_fpath hs).mp hy
      rw [← hue]
      constructor
      · intro hadju
        refine ⟨rfl, ?_⟩
        by_cases huk : u = k
        · exact absurd (by rw [← huk]; exact hadju.symm) hs.notAdjLstBase
        · by_cases hu1' : u = 1
          · rw [hu1']
          · exact absurd hadju.symm
              (hs.adjMid u (by omega) (by omega) _ (Thm162SetupBasics.q_mem hs hp 0))
      · rintro ⟨-, heq⟩
        rw [heq]
        exact ((hs.adjFst (q 0) (Thm162SetupBasics.q_mem hs hp 0)).mpr rfl).symm
  ---------------------------------------------------------------- 15.3
  have hfinal := Thm153Rotated.clean_path_hits_yComplete hs.inF6 hH3 hpos3 (by omega)
    (fun y hy hmem => by
      rcases List.mem_append.mp hmem with h1 | h2
      · exact hs.fnotY k (by omega) le_rfl (by rw [← List.mem_singleton.mp h1]; exact hy)
      · obtain ⟨u, hu, hue⟩ := (mem_arc hp).mp h2
        exact hCY y (by rw [← hue]; exact cyc_mem hp _) hy)
    hs.wheel.2.1.2.1 (2 + s - c) (h := C.length - s) (i := C.length + t - s)
    (j := C.length + a - s + 1) (F := [q 0] ++ Thm162SetupBasics.fpath P k)
    (by omega) (by omega) (by omega) (by omega)
    ?_ ?_ ?_ ?_
  · obtain ⟨w, hwF, hwY⟩ := hfinal
    rcases List.mem_append.mp hwF with h1 | h2
    · exact hq0 (by rw [← List.mem_singleton.mp h1]; exact hwY)
    · obtain ⟨u, hu1, hu2, hue⟩ := (Thm162SetupBasics.mem_fpath hs).mp h2
      exact hs.fnotComplete u hu1 hu2 (by rw [hue]; exact hwY)
  · -- the four `Y`-complete vertices of `H₃`
    intro w hw
    rw [hV1, hV2, hV3, hV4]
    rcases List.mem_append.mp hw with h1 | h2
    · rw [List.mem_singleton.mp h1]
      constructor
      · intro hc; exact absurd hc (hs.fnotComplete k (by omega) le_rfl)
      · rintro (he | he | he | he) <;>
          exact absurd (by rw [he]; exact Thm162SetupBasics.q_mem hs hp _) hfkC
    · obtain ⟨u, hu, hue⟩ := (mem_arc hp).mp h2
      rw [← hue, hqcu u]
      by_cases hlt : c + u < C.length
      · constructor
        · intro hc
          rcases hYright (c + u) (by omega) hlt hc with he | he <;> rw [he]
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · rintro (he | he | he | he)
          · rw [he]; exact hYs
          · rw [he]; exact hYs1
          · exfalso
            have := hqmod _ _ he
            rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at this
            omega
          · exfalso
            have := hqmod _ _ he
            rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at this
            omega
      · have hred : q (c + u) = q (c + u - C.length) :=
          Thm162SetupBasics.q_congr hs hp (hmodsub (c + u) (by omega))
        rw [hred]
        constructor
        · intro hc
          rcases hYleft (c + u - C.length) (by omega) hc with he | he <;> rw [he]
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        · rintro (he | he | he | he)
          · exfalso
            have := hqmod _ _ he
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
            omega
          · exfalso
            have := hqmod _ _ he
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
            omega
          · rw [he]; exact hYt
          · rw [he]; exact hYt1
  · rw [hV5, hV6]; exact hFpath
  · intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · rw [List.mem_singleton.mp h1]
      exact hCY _ (Thm162SetupBasics.q_mem hs hp 0)
    · obtain ⟨u, hu1, hu2, hue⟩ := (Thm162SetupBasics.mem_fpath hs).mp h2
      rw [← hue]; exact hs.fnotY u hu1 hu2
  · rw [hV5, hV6]
    intro x hx w hwD hw1 hw2 hadjxw
    obtain ⟨hxF, hxne1, hxne2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hFpath).mp hx
    have hwC : w ∈ C := by
      rcases List.mem_append.mp hwD with h1 | h2
      · exact absurd (List.mem_singleton.mp h1) hw2
      · obtain ⟨u, hu, hue⟩ := (mem_arc hp).mp h2
        rw [← hue]; exact cyc_mem hp _
    rcases List.mem_append.mp hxF with h1 | h2
    · exact hxne1 (List.mem_singleton.mp h1)
    · obtain ⟨u, hu1, hu2, hue⟩ := (Thm162SetupBasics.mem_fpath hs).mp h2
      rw [← hue] at hadjxw hxne2
      by_cases huk : u = k
      · subst huk; exact hxne2 rfl
      · by_cases hu1' : u = 1
        · subst hu1'
          exact hw1 ((hs.adjFst w hwC).mp hadjxw)
        · exact hs.adjMid u (by omega) (by omega) w hwC hadjxw

/-! ### The paragraph before claim (5) -/

theorem preamble {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V}
    {q f : ℕ → V} {b a c k : ℕ}
    (hs : Setup G C Y P q f b a c k) (hac2 : a + 2 ≤ c) (hp : 0 < C.length) :
    VertexComplete G (q 0) Y ∧ VertexComplete G (q 1) Y ∧
      VertexComplete G (q (C.length - 1)) Y ∧
      (∀ e : ℕ, 2 ≤ e → e ≤ a → ¬ VertexComplete G (q e) Y) ∧
      (∀ e : ℕ, c ≤ e → e + 2 ≤ C.length → ¬ VertexComplete G (q e) Y) ∧
      Even (k + a + 1) ∧ Even (k + (C.length - c) + 1) := by
  classical
  have hn6 : 6 ≤ C.length := Thm162SetupBasics.n6 hs
  have hC : IsHoleList G C := Thm162SetupBasics.holeC hs
  have hBerge : Berge G := hs.inF6.1.1.1
  have hYanti : AnticonnectedSet G Y := hs.wheel.2.1.2.1
  have hCY : ∀ w ∈ C, w ∉ Y := hs.wheel.2.1.2.2
  have hcyc : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hs.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC hcyc
  have hstep : ∀ z w : V, z ∈ C → w ∈ C → G.Adj z w → (π z ≠ π w ↔ EdgeComplete G Y z w) :=
    fun z w hz hw hadj => OddWheelAttachmentYCount.parity_step hC hcyc hπ hz hw hadj
  have hka := hs.klb
  have halb := hs.alb
  have haub := hs.aub
  have hclb := hs.clb
  have hcub := hs.cub
  have hSY : ∀ z ∈ Thm162SetupBasics.fpath P k, z ∉ Y := by
    intro z hz
    obtain ⟨u, h1, h2, rfl⟩ := (Thm162SetupBasics.mem_fpath hs).mp hz
    exact hs.fnotY u h1 h2
  have hSnc : ∀ z ∈ Thm162SetupBasics.fpath P k, ¬ VertexComplete G z Y := by
    intro z hz
    obtain ⟨u, h1, h2, rfl⟩ := (Thm162SetupBasics.mem_fpath hs).mp hz
    exact hs.fnotComplete u h1 h2
  have hq0 : q 0 = cyc C hp b := Thm162SetupBasics.q_eq hs hp 0
  have hqa : q a = cyc C hp (b + a) := Thm162SetupBasics.q_eq hs hp a
  have hqc : q c = cyc C hp (b + c) := Thm162SetupBasics.q_eq hs hp c
  have hπa : π (q 0) ≠ π (q a) := by
    intro he
    exact (hs.oppLst a hs.adjLstMin).2.2.2
      ((hπ (q 0) (q a) (Thm162SetupBasics.q_mem hs hp 0) (Thm162SetupBasics.q_mem hs hp a)
        (hs.oppLst a hs.adjLstMin).1).mpr he)
  have hπc : π (q 0) ≠ π (q c) := by
    intro he
    exact (hs.oppLst c hs.adjLstMax).2.2.2
      ((hπ (q 0) (q c) (Thm162SetupBasics.q_mem hs hp 0) (Thm162SetupBasics.q_mem hs hp c)
        (hs.oppLst c hs.adjLstMax).1).mpr he)
  obtain ⟨h1even, h1edge, y₁, z₁, h1set, h1ne, h1adj⟩ :=
    OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep hs.alb hs.aub
      hSY hSnc (by rw [← hq0, ← hqa]; exact hπa) (Thm162SetupBasics.hole_one hs hp)
  have hqn : q 0 = cyc C hp (b + c + (C.length - c)) := by
    rw [show b + c + (C.length - c) = b + C.length by omega, hq0]
    exact cyc_congr hp (by rw [Nat.add_mod_right])
  obtain ⟨h2even, h2edge, y₂, z₂, h2set, h2ne, h2adj⟩ :=
    OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep
      (show 1 ≤ C.length - c by omega) (show C.length - c + 2 ≤ C.length by omega)
      (fun z hz => hSY z (List.mem_reverse.mp hz))
      (fun z hz => hSnc z (List.mem_reverse.mp hz))
      (by rw [← hqc, ← hqn]; exact fun he => hπc he.symm) (Thm162SetupBasics.hole_two hs hp)
  rw [Thm162SetupBasics.fpath_length hs] at h1even
  rw [List.length_reverse, Thm162SetupBasics.fpath_length hs] at h2even
  ---------------------------------------------------------------- reading the two hole data
  have hin1 : ∀ e : ℕ, e ≤ a → VertexComplete G (q e) Y → q e = y₁ ∨ q e = z₁ := by
    intro e he hce
    have hmem : q e ∈ (Thm162SetupBasics.fpath P k ++ (arc C hp b (a + 1)).reverse) :=
      (Thm162SetupBasics.mem_hole_one hs hp).mpr (Or.inr ⟨e, he, rfl⟩)
    have hh := (Set.ext_iff.mp h1set (q e)).mp ⟨hmem, hce⟩
    simpa using hh
  have hin2 : ∀ e : ℕ, c ≤ e → e ≤ C.length → VertexComplete G (q e) Y →
      q e = y₂ ∨ q e = z₂ := by
    intro e h1 h2 hce
    have hmem : q e ∈ ((Thm162SetupBasics.fpath P k).reverse ++
        (arc C hp (b + c) (C.length - c + 1)).reverse) :=
      (Thm162SetupBasics.mem_hole_two hs hp).mpr (Or.inr ⟨e, h1, h2, rfl⟩)
    have hh := (Set.ext_iff.mp h2set (q e)).mp ⟨hmem, hce⟩
    simpa using hh
  have hposA : ∀ w : V, (w = y₁ ∨ w = z₁) →
      VertexComplete G w Y ∧ ∃ e : ℕ, e ≤ a ∧ q e = w := by
    intro w hw
    have hmem2 : w ∈ (Thm162SetupBasics.fpath P k ++ (arc C hp b (a + 1)).reverse) ∧
        VertexComplete G w Y := by
      refine (Set.ext_iff.mp h1set w).mpr ?_
      rcases hw with rfl | rfl
      · simp
      · simp
    obtain ⟨hmem, hwc⟩ := hmem2
    refine ⟨hwc, ?_⟩
    rcases (Thm162SetupBasics.mem_hole_one hs hp).mp hmem with ⟨u, hu1, hu2, rfl⟩ | ⟨e, he, rfl⟩
    · exact absurd hwc (hs.fnotComplete u hu1 hu2)
    · exact ⟨e, he, rfl⟩
  have hposB : ∀ w : V, (w = y₂ ∨ w = z₂) →
      VertexComplete G w Y ∧ ∃ e : ℕ, c ≤ e ∧ e ≤ C.length ∧ q e = w := by
    intro w hw
    have hmem2 : w ∈ ((Thm162SetupBasics.fpath P k).reverse ++
        (arc C hp (b + c) (C.length - c + 1)).reverse) ∧ VertexComplete G w Y := by
      refine (Set.ext_iff.mp h2set w).mpr ?_
      rcases hw with rfl | rfl
      · simp
      · simp
    obtain ⟨hmem, hwc⟩ := hmem2
    refine ⟨hwc, ?_⟩
    rcases (Thm162SetupBasics.mem_hole_two hs hp).mp hmem with
      ⟨u, hu1, hu2, rfl⟩ | ⟨e, he1, he2, rfl⟩
    · exact absurd hwc (hs.fnotComplete u hu1 hu2)
    · exact ⟨e, he1, he2, rfl⟩
  have hqn0 : q C.length = q 0 := Thm162SetupBasics.q_congr hs hp (by simp)
  ---------------------------------------------------------------- *"So `p₁` is `Y`-complete"*
  have hY0 : VertexComplete G (q 0) Y := by
    by_contra hq0nc
    obtain ⟨t, ht1, ht2, hYt, hYt1, hYleft⟩ : ∃ t : ℕ, 1 ≤ t ∧ t + 1 ≤ a ∧
        VertexComplete G (q t) Y ∧ VertexComplete G (q (t + 1)) Y ∧
        (∀ e : ℕ, e ≤ a → VertexComplete G (q e) Y → e = t ∨ e = t + 1) := by
      obtain ⟨hy₁c, u₁, hu₁a, hu₁q⟩ := hposA y₁ (Or.inl rfl)
      obtain ⟨hz₁c, u₂, hu₂a, hu₂q⟩ := hposA z₁ (Or.inr rfl)
      have hu₁0 : u₁ ≠ 0 := by
        intro hh; subst hh; exact hq0nc (by rw [hu₁q]; exact hy₁c)
      have hu₂0 : u₂ ≠ 0 := by
        intro hh; subst hh; exact hq0nc (by rw [hu₂q]; exact hz₁c)
      have hadj : G.Adj (q u₁) (q u₂) := by rw [hu₁q, hu₂q]; exact h1adj
      have hcons : u₂ = u₁ + 1 ∨ u₁ = u₂ + 1 := by
        rcases Thm162SetupBasics.q_adj hs hp (show u₁ < C.length by omega)
            (show u₂ < C.length by omega) hadj with hq | hq
        · left; rwa [Nat.mod_eq_of_lt (show u₁ + 1 < C.length by omega)] at hq
        · right; rwa [Nat.mod_eq_of_lt (show u₂ + 1 < C.length by omega)] at hq
      have hYl : ∀ e : ℕ, e ≤ a → VertexComplete G (q e) Y → e = u₁ ∨ e = u₂ := by
        intro e he hce
        rcases hin1 e he hce with hh | hh
        · exact Or.inl (Thm162SetupBasics.q_inj hs hp (by omega) (by omega)
            (hh.trans hu₁q.symm))
        · exact Or.inr (Thm162SetupBasics.q_inj hs hp (by omega) (by omega)
            (hh.trans hu₂q.symm))
      rcases hcons with hc | hc
      · refine ⟨u₁, by omega, by omega, by rw [hu₁q]; exact hy₁c, ?_, ?_⟩
        · rw [← hc, hu₂q]; exact hz₁c
        · intro e he hce
          rcases hYl e he hce with hh | hh
          · exact Or.inl hh
          · exact Or.inr (by omega)
      · refine ⟨u₂, by omega, by omega, by rw [hu₂q]; exact hz₁c, ?_, ?_⟩
        · rw [← hc, hu₁q]; exact hy₁c
        · intro e he hce
          rcases hYl e he hce with hh | hh
          · exact Or.inr (by omega)
          · exact Or.inl hh
    obtain ⟨sg, hsg1, hsg2, hYs, hYs1, hYright⟩ : ∃ sg : ℕ, c ≤ sg ∧ sg + 2 ≤ C.length ∧
        VertexComplete G (q sg) Y ∧ VertexComplete G (q (sg + 1)) Y ∧
        (∀ e : ℕ, c ≤ e → e < C.length → VertexComplete G (q e) Y → e = sg ∨ e = sg + 1) := by
      obtain ⟨hy₂c, v₁, hv₁1, hv₁2, hv₁q⟩ := hposB y₂ (Or.inl rfl)
      obtain ⟨hz₂c, v₂, hv₂1, hv₂2, hv₂q⟩ := hposB z₂ (Or.inr rfl)
      have hv₁n : v₁ ≠ C.length := by
        intro hh; subst hh; exact hq0nc (by rw [← hqn0, hv₁q]; exact hy₂c)
      have hv₂n : v₂ ≠ C.length := by
        intro hh; subst hh; exact hq0nc (by rw [← hqn0, hv₂q]; exact hz₂c)
      have hadj : G.Adj (q v₁) (q v₂) := by rw [hv₁q, hv₂q]; exact h2adj
      have hcons : v₂ = v₁ + 1 ∨ v₁ = v₂ + 1 := by
        rcases Thm162SetupBasics.q_adj hs hp (show v₁ < C.length by omega)
            (show v₂ < C.length by omega) hadj with hq | hq
        · left
          by_cases hlt : v₁ + 1 < C.length
          · rwa [Nat.mod_eq_of_lt hlt] at hq
          · rw [show v₁ + 1 = C.length by omega, Nat.mod_self] at hq; omega
        · right
          by_cases hlt : v₂ + 1 < C.length
          · rwa [Nat.mod_eq_of_lt hlt] at hq
          · rw [show v₂ + 1 = C.length by omega, Nat.mod_self] at hq; omega
      have hYr : ∀ e : ℕ, c ≤ e → e < C.length → VertexComplete G (q e) Y →
          e = v₁ ∨ e = v₂ := by
        intro e h1 h2 hce
        rcases hin2 e h1 (by omega) hce with hh | hh
        · exact Or.inl (Thm162SetupBasics.q_inj hs hp (by omega) (by omega)
            (hh.trans hv₁q.symm))
        · exact Or.inr (Thm162SetupBasics.q_inj hs hp (by omega) (by omega)
            (hh.trans hv₂q.symm))
      rcases hcons with hc | hc
      · refine ⟨v₁, by omega, by omega, by rw [hv₁q]; exact hy₂c, ?_, ?_⟩
        · rw [← hc, hv₂q]; exact hz₂c
        · intro e h1 h2 hce
          rcases hYr e h1 h2 hce with hh | hh
          · exact Or.inl hh
          · exact Or.inr (by omega)
      · refine ⟨v₂, by omega, by omega, by rw [hv₂q]; exact hz₂c, ?_, ?_⟩
        · rw [← hc, hv₁q]; exact hy₂c
        · intro e h1 h2 hce
          rcases hYr e h1 h2 hce with hh | hh
          · exact Or.inr (by omega)
          · exact Or.inl hh
    exact q0_yComplete_aux hs hac2 hp ht1 ht2 hsg1 hsg2 hYt hYt1 hYs hYs1 hYleft hYright hq0nc
  ---------------------------------------------------------------- `p₂` and `pₙ`
  have hadj0e : ∀ e : ℕ, e ≤ a → e ≠ 0 → VertexComplete G (q e) Y → G.Adj (q 0) (q e) := by
    intro e he he0 hce
    have h0 := hin1 0 (by omega) hY0
    have hE := hin1 e he hce
    have hne : q 0 ≠ q e := by
      intro hq
      exact he0 (Thm162SetupBasics.q_inj hs hp (by omega) (by omega) hq).symm
    rcases h0 with h0 | h0 <;> rcases hE with hE | hE
    · exact absurd (h0.trans hE.symm) hne
    · rw [h0, hE]; exact h1adj
    · rw [h0, hE]; exact h1adj.symm
    · exact absurd (h0.trans hE.symm) hne
  have hadj0e2 : ∀ e : ℕ, c ≤ e → e < C.length → VertexComplete G (q e) Y →
      G.Adj (q 0) (q e) := by
    intro e h1 h2 hce
    have h0 : q 0 = y₂ ∨ q 0 = z₂ := by
      have hh := hin2 C.length (by omega) le_rfl (by rw [hqn0]; exact hY0)
      rwa [hqn0] at hh
    have hE := hin2 e h1 (by omega) hce
    have hne : q 0 ≠ q e := by
      intro hq
      have := Thm162SetupBasics.q_inj hs hp (show (0:ℕ) < C.length by omega) h2 hq
      omega
    rcases h0 with h0 | h0 <;> rcases hE with hE | hE
    · exact absurd (h0.trans hE.symm) hne
    · rw [h0, hE]; exact h2adj
    · rw [h0, hE]; exact h2adj.symm
    · exact absurd (h0.trans hE.symm) hne
  have hconfL : ∀ e : ℕ, 2 ≤ e → e ≤ a → ¬ VertexComplete G (q e) Y := by
    intro e h2 hea hce
    have hadj := hadj0e e hea (by omega) hce
    rcases Thm162SetupBasics.q_adj hs hp (show (0:ℕ) < C.length by omega)
        (show e < C.length by omega) hadj with hq | hq
    · rw [Nat.mod_eq_of_lt (show 0 + 1 < C.length by omega)] at hq; omega
    · by_cases hlt : e + 1 < C.length
      · rw [Nat.mod_eq_of_lt hlt] at hq; omega
      · omega
  have hconfR : ∀ e : ℕ, c ≤ e → e + 2 ≤ C.length → ¬ VertexComplete G (q e) Y := by
    intro e h1 h2 hce
    have hadj := hadj0e2 e h1 (by omega) hce
    rcases Thm162SetupBasics.q_adj hs hp (show (0:ℕ) < C.length by omega)
        (show e < C.length by omega) hadj with hq | hq
    · rw [Nat.mod_eq_of_lt (show 0 + 1 < C.length by omega)] at hq; omega
    · by_cases hlt : e + 1 < C.length
      · rw [Nat.mod_eq_of_lt hlt] at hq; omega
      · omega
  have hY1 : VertexComplete G (q 1) Y := by
    obtain ⟨e, hea, he0, hcew⟩ : ∃ e : ℕ, e ≤ a ∧ e ≠ 0 ∧ VertexComplete G (q e) Y := by
      rcases hin1 0 (by omega) hY0 with h0 | h0
      · obtain ⟨hzc, e, hea, hqe⟩ := hposA z₁ (Or.inr rfl)
        refine ⟨e, hea, ?_, by rw [hqe]; exact hzc⟩
        intro he0; subst he0
        exact h1ne (h0.symm.trans hqe)
      · obtain ⟨hyc, e, hea, hqe⟩ := hposA y₁ (Or.inl rfl)
        refine ⟨e, hea, ?_, by rw [hqe]; exact hyc⟩
        intro he0; subst he0
        exact h1ne (hqe.symm.trans h0)
    have he1 : e = 1 := by
      have hadj := hadj0e e hea he0 hcew
      rcases Thm162SetupBasics.q_adj hs hp (show (0:ℕ) < C.length by omega)
          (show e < C.length by omega) hadj with hq | hq
      · rw [Nat.mod_eq_of_lt (show 0 + 1 < C.length by omega)] at hq; omega
      · by_cases hlt : e + 1 < C.length
        · rw [Nat.mod_eq_of_lt hlt] at hq; omega
        · omega
    rw [← he1]; exact hcew
  have hYn : VertexComplete G (q (C.length - 1)) Y := by
    obtain ⟨e, he1, he2, hcew⟩ : ∃ e : ℕ, c ≤ e ∧ e < C.length ∧ VertexComplete G (q e) Y := by
      have h0 : q 0 = y₂ ∨ q 0 = z₂ := by
        have hh := hin2 C.length (by omega) le_rfl (by rw [hqn0]; exact hY0)
        rwa [hqn0] at hh
      rcases h0 with h0 | h0
      · obtain ⟨hzc, e, he1, he2, hqe⟩ := hposB z₂ (Or.inr rfl)
        have hne : e ≠ C.length := by
          intro hh; subst hh
          exact h2ne (h0.symm.trans (hqn0.symm.trans hqe))
        exact ⟨e, he1, by omega, by rw [hqe]; exact hzc⟩
      · obtain ⟨hyc, e, he1, he2, hqe⟩ := hposB y₂ (Or.inl rfl)
        have hne : e ≠ C.length := by
          intro hh; subst hh
          exact h2ne (hqe.symm.trans (hqn0.trans h0))
        exact ⟨e, he1, by omega, by rw [hqe]; exact hyc⟩
    have hen : e = C.length - 1 := by
      have hadj := hadj0e2 e he1 he2 hcew
      rcases Thm162SetupBasics.q_adj hs hp (show (0:ℕ) < C.length by omega) he2 hadj with hq | hq
      · rw [Nat.mod_eq_of_lt (show 0 + 1 < C.length by omega)] at hq; omega
      · by_cases hlt : e + 1 < C.length
        · rw [Nat.mod_eq_of_lt hlt] at hq; omega
        · omega
    rw [← hen]; exact hcew
  exact ⟨hY0, hY1, hYn, hconfL, hconfR, h1even, h2even⟩

/-! ### Claim (5) and its mirror image -/

theorem claim_five_final {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V}
    {q f : ℕ → V} {b a c k : ℕ}
    (hs : Setup G C Y P q f b a c k) (hac2 : a + 2 ≤ c) :
    (∀ d : ℕ, 2 ≤ d → d + 2 ≤ c → ¬ G.Adj (f k) (q d)) ∧
    (∀ d : ℕ, a + 2 ≤ d → d + 2 ≤ C.length → ¬ G.Adj (f k) (q d)) := by
  classical
  have hn6 : 6 ≤ C.length := Thm162SetupBasics.n6 hs
  have hp : 0 < C.length := by omega
  have hC : IsHoleList G C := Thm162SetupBasics.holeC hs
  have hBerge : Berge G := hs.inF6.1.1.1
  have hcyc : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hs.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC hcyc
  obtain ⟨hY0, hY1, hYn, hconfL, hconfR, hpar1, hpar2⟩ := preamble hs hac2 hp
  have hka := hs.klb
  have halb := hs.alb
  have haub := hs.aub
  have hclb := hs.clb
  have hcub := hs.cub
  have hac := hs.ac
  have hbl := hs.blt
  have hplen := hs.plen
  have hSlen := Thm162SetupBasics.fpath_length hs
  have hS := Thm162SetupBasics.fpath_isPathFrom hs
  have hSmem : ∀ x : V, x ∈ Thm162SetupBasics.fpath P k ↔ ∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = x :=
    fun x => Thm162SetupBasics.mem_fpath hs
  have hf1k : f 1 ≠ f k := Thm162SetupBasics.f_ne hs (by omega) (by omega) (by omega)
  have hfinj : ∀ s t : ℕ, 1 ≤ s → s ≤ k → 1 ≤ t → t ≤ k → f s = f t → s = t :=
    fun s t _ hsk _ htk he => Thm162SetupBasics.f_inj hs (by omega) (by omega) he
  have hqn0 : q C.length = q 0 := Thm162SetupBasics.q_congr hs hp (by simp)
  have hnbrk : ∀ u : V, u ∈ C → G.Adj (f k) u → π u ≠ π (q 0) := by
    intro u huC hadju
    obtain ⟨d, hd, rfl⟩ := Thm162SetupBasics.exists_q hs hp huC
    intro he
    exact (hs.oppLst d hadju).2.2.2
      ((hπ (q 0) (q d) (Thm162SetupBasics.q_mem hs hp 0) (Thm162SetupBasics.q_mem hs hp d)
        (hs.oppLst d hadju).1).mpr he.symm)
  have hqe : ∀ e : ℕ, cyc C hp (b + e) = q e :=
    fun e => (Thm162SetupBasics.q_eq hs hp e).symm
  have hqe0 : cyc C hp b = q 0 := (Thm162SetupBasics.q_eq hs hp 0).symm
  constructor
  · ---------------------------------------------------------------- claim (5) itself
    have hcore := claim_five_core (D := C) (hD := hC) (hDpos := hp) (β := b)
      (S := Thm162SetupBasics.fpath P k) hs.inF6 hs.wheel hπ2 hπ (fun w => Iff.rfl) rfl
      hs.klb hS hSlen hSmem hf1k hfinj
      (fun t h1 h2 => hs.fnotC t h1 h2) (fun t h1 h2 => hs.fnotY t h1 h2)
      (fun t h1 h2 => hs.fnotComplete t h1 h2)
      (by intro u huC; rw [hqe0]; exact hs.adjFst u huC)
      hs.adjMid halb hac2 hcub
      (by rw [hqe0]; exact hs.notAdjLstBase)
      (by rw [hqe c]; exact hs.adjLstMax)
      (by
        intro e he hadj
        rw [hqe e] at hadj
        exact Thm162SetupBasics.fk_adj_range hs hp he hadj)
      (by rw [hqe0]; exact hY0) (by rw [hqe 1]; exact hY1)
      (by rw [hqe (C.length - 1)]; exact hYn)
      (by intro e h1 h2; rw [hqe e]; exact hconfL e h1 h2)
      (by intro e h1 h2; rw [hqe e]; exact hconfR e h1 h2)
      hpar2
      (by intro u huC hadju; rw [hqe0]; exact hnbrk u huC hadju)
    intro d h1 h2
    rw [← hqe d]
    exact hcore d h1 h2
  · ---------------------------------------------------------------- *"and similarly"*
    have hrpos : 0 < C.reverse.length := by rw [List.length_reverse]; omega
    have hrl : C.reverse.length = C.length := List.length_reverse
    have hCrev : IsHoleList G C.reverse := HoleBasics.isHoleList_reverse hC
    have hbridge : ∀ t : ℕ, t ≤ C.length →
        cyc C.reverse hrpos (C.length - 1 - b + t) = q (C.length - t) := by
      intro t ht
      rw [Thm162SetupBasics.q_eq hs hp (C.length - t)]
      simp only [cyc]
      rw [List.getElem_reverse]
      refine HoleArithmetic.getElem_congr_idx C _ _ ?_
      rw [hrl]
      have hmx : ((C.length - 1 - b + t) % C.length) ≡ (C.length - 1 - b + t) [MOD C.length] :=
        Nat.mod_modEq _ _
      have hmy : ((b + (C.length - t)) % C.length) ≡ (b + (C.length - t)) [MOD C.length] :=
        Nat.mod_modEq _ _
      have hsum : (((C.length - 1 - b + t) % C.length) + ((b + (C.length - t)) % C.length))
          % C.length = (C.length - 1) % C.length := by
        have hadd := Nat.ModEq.add hmx hmy
        rw [show (C.length - 1 - b + t) + (b + (C.length - t)) = (C.length - 1) + C.length by
          omega] at hadd
        exact hadd.trans (Nat.add_mod_right _ _)
      have hkey := mod_pair_eq hp (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hsum
      omega
    have hbr0 : cyc C.reverse hrpos (C.length - 1 - b) = q 0 := by
      have hh := hbridge 0 (by omega)
      rw [Nat.add_zero, Nat.sub_zero, hqn0] at hh
      exact hh
    have hcore2 := claim_five_core (D := C.reverse) (hD := hCrev) (hDpos := hrpos)
      (β := C.length - 1 - b) (S := Thm162SetupBasics.fpath P k)
      hs.inF6 hs.wheel hπ2 hπ (fun w => List.mem_reverse) hrl
      hs.klb hS hSlen hSmem hf1k hfinj
      (fun t h1 h2 => hs.fnotC t h1 h2) (fun t h1 h2 => hs.fnotY t h1 h2)
      (fun t h1 h2 => hs.fnotComplete t h1 h2)
      (by intro u huC; rw [hbr0]; exact hs.adjFst u huC)
      hs.adjMid (a := C.length - c) (c := C.length - a) (by omega) (by omega) (by omega)
      (by rw [hbr0]; exact hs.notAdjLstBase)
      (by
        rw [hbridge (C.length - a) (by omega), show C.length - (C.length - a) = a by omega]
        exact hs.adjLstMin)
      (by
        intro e he hadj
        rw [hbridge e (by omega)] at hadj
        rcases Nat.eq_zero_or_pos e with rfl | he0
        · exfalso
          rw [Nat.sub_zero, hqn0] at hadj
          exact hs.notAdjLstBase hadj
        · have := Thm162SetupBasics.fk_adj_range hs hp
            (d := C.length - e) (by omega) hadj
          omega)
      (by rw [hbr0]; exact hY0)
      (by rw [hbridge 1 (by omega)]; exact hYn)
      (by
        rw [hbridge (C.length - 1) (by omega), show C.length - (C.length - 1) = 1 by omega]
        exact hY1)
      (by
        intro e h1 h2
        rw [hbridge e (by omega)]
        exact hconfR (C.length - e) (by omega) (by omega))
      (by
        intro e h1 h2
        rw [hbridge e (by omega)]
        exact hconfL (C.length - e) (by omega) (by omega))
      (by rw [show C.length - (C.length - a) = a by omega]; exact hpar1)
      (by intro u huC hadju; rw [hbr0]; exact hnbrk u huC hadju)
    intro d h1 h2 hadj
    refine hcore2 (C.length - d) (by omega) (by omega) ?_
    rw [hbridge (C.length - d) (by omega), show C.length - (C.length - d) = d by omega]
    exact hadj

end Workspace.ProofLemmas.Thm162ClaimFiveAux

namespace Workspace.ProofLemmas.Thm162ClaimFive

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentEndgame

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V} {q f : ℕ → V} {b a c k : ℕ}

/-- **Claim (5) of 16.2, together with its mirror image.**

PAPER: *"(5) `f_k` has no neighbour in `{p₃, …, p_{j−2}}`."* and *"… and similarly `f_k` has no
neighbours in `{p_{i+2}, …, p_{n−1}}`."* -/
theorem claim_five (hs : Setup G C Y P q f b a c k) (hac2 : a + 2 ≤ c) :
    (∀ d : ℕ, 2 ≤ d → d + 2 ≤ c → ¬ G.Adj (f k) (q d)) ∧
    (∀ d : ℕ, a + 2 ≤ d → d + 2 ≤ C.length → ¬ G.Adj (f k) (q d)) :=
  Workspace.ProofLemmas.Thm162ClaimFiveAux.claim_five_final hs hac2

end Workspace.ProofLemmas.Thm162ClaimFive
