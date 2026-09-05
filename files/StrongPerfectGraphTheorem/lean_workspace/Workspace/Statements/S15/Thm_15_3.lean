/-  Proof attempt for statement 15.3 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    PRINTED PROOF (perfect.pdf, printed p. 93):

      "Assume no vertex of F is Y-complete.  Since the hole
           p_1-...-p_h-F-p_j-...-p_n-p_1
       is even, and the path p_1-...-p_h-...-p_i is even (by 2.2), it follows that the path
           p_i-p_{i-1}-...-p_h-F-p_j-...-p_n
       is odd, and therefore has length 3 by 13.6.  So F has length 1, and i = h + 1 and
       n = j + 1.  Similarly h = 2 and j = i + 2, and so n = 6.  Then p_2, p_5 are adjacent,
       so there is an antipath Q joining them with interior in Y.  But then in Gbar, the
       three paths p_1-p_4, p_5-p_2, p_3-Q-p_6 form a long prism, a contradiction."

    The cyclically contiguous blocks of the (non-induced) cycle C are handled by the new
    module `Workspace.ProofLemmas.CycleArcPath`.                                          -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.CycleArcPath
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.CycleArcPath

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_15_3 (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (n h i j : ℕ) (hlen : C.length = n) (hn : 6 ≤ n)
    (hh : 1 < h) (hhi : h < i) (hij : i + 1 < j) (hjn : j < n)
    (hnodup : C.Nodup)
    (hcycle : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length),
      (b = (a + 1) % C.length ∨ a = (b + 1) % C.length) → G.Adj C[a] C[b])
    (hinduced : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length),
      G.Adj C[a] C[b] →
        ((b = (a + 1) % C.length ∨ a = (b + 1) % C.length) ∨
          ((a = h - 1 ∧ b = j - 1) ∨ (a = j - 1 ∧ b = h - 1))))
    (Y : Set V) (hYC : ∀ y ∈ Y, y ∉ C) (hYanti : AnticonnectedSet G Y)
    (hYcomplete : ∀ w ∈ C,
      (VertexComplete G w Y ↔ (w = C[n - 1] ∨ w = C[0] ∨ w = C[i - 1] ∨ w = C[i])))
    (F : List V) (hF : IsPathFrom G F C[h - 1] C[j - 1]) (hFY : ∀ w ∈ F, w ∉ Y)
    (hFC : ∀ x ∈ SPGT.interior F, ∀ w ∈ C, w ≠ C[h - 1] → w ≠ C[j - 1] → ¬ G.Adj x w) :
    ∃ w ∈ F, VertexComplete G w Y := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < C.length := by omega
  have hn4 : 4 ≤ C.length := by omega
  obtain ⟨x₀, -⟩ : ∃ x : V, True := ⟨C[0]'hpos, trivial⟩
  have hCk : ∀ (k : ℕ) (hk : k < C.length), cycAt C x₀ k = C[k]'hk := fun k hk => cycAt_of_lt hk
  -- distinctness at the index level
  have hcne : ∀ s t : ℕ, s % C.length ≠ t % C.length →
      cycAt C x₀ s ≠ cycAt C x₀ t := fun s t hst => cycAt_ne hnodup hpos hst
  have hceq : ∀ s t : ℕ, (cycAt C x₀ s = cycAt C x₀ t) ↔ s % C.length = t % C.length :=
    fun s t => ⟨fun he => cycAt_inj hnodup hpos he, fun he => cycAt_congr he⟩
  -- adjacency at the index level
  have hadjm : ∀ s t : ℕ,
      (t % C.length = (s + 1) % C.length ∨ s % C.length = (t + 1) % C.length) →
      G.Adj (cycAt C x₀ s) (cycAt C x₀ t) := by
    intro s t hst
    rw [cycAt_mod_lt hpos, cycAt_mod_lt hpos]
    refine hcycle _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) ?_
    rcases hst with hc | hc
    · left; rw [Nat.mod_add_mod]; exact hc
    · right; rw [Nat.mod_add_mod]; exact hc
  have hnadjm : ∀ s t : ℕ,
      t % C.length ≠ (s + 1) % C.length → s % C.length ≠ (t + 1) % C.length →
      ¬(s % C.length = h - 1 ∧ t % C.length = j - 1) →
      ¬(s % C.length = j - 1 ∧ t % C.length = h - 1) →
      ¬ G.Adj (cycAt C x₀ s) (cycAt C x₀ t) := by
    intro s t h1 h2 h3 h4 hadj
    rw [cycAt_mod_lt hpos, cycAt_mod_lt hpos] at hadj
    rcases hinduced _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hadj with hc | he
    · rcases hc with hc | hc
      · exact h1 (by rw [hc, Nat.mod_add_mod])
      · exact h2 (by rw [hc, Nat.mod_add_mod])
    · rcases he with he | he
      · exact h3 he
      · exact h4 he
  -- `Y`-completeness at the index level
  have hYidx : ∀ (k : ℕ), k < C.length →
      (VertexComplete G (cycAt C x₀ k) Y ↔ (k = n - 1 ∨ k = 0 ∨ k = i - 1 ∨ k = i)) := by
    intro k hk
    rw [hCk k hk, hYcomplete _ (List.getElem_mem hk)]
    have e1 : (C[k]'hk = C[n - 1]'(by omega)) ↔ k = n - 1 := List.Nodup.getElem_inj_iff hnodup
    have e2 : (C[k]'hk = C[0]'(by omega)) ↔ k = 0 := List.Nodup.getElem_inj_iff hnodup
    have e3 : (C[k]'hk = C[i - 1]'(by omega)) ↔ k = i - 1 := List.Nodup.getElem_inj_iff hnodup
    have e4 : (C[k]'hk = C[i]'(by omega)) ↔ k = i := List.Nodup.getElem_inj_iff hnodup
    rw [e1, e2, e3, e4]
  -- the path `F`, with its ends written cyclically
  have hF' : IsPathFrom G F (cycAt C x₀ (h - 1)) (cycAt C x₀ (j - 1)) := by
    rw [hCk (h - 1) (by omega), hCk (j - 1) (by omega)]; exact hF
  have hFCn : ∀ x ∈ SPGT.interior F, ∀ (k : ℕ),
      k % C.length ≠ h - 1 → k % C.length ≠ j - 1 → ¬ G.Adj x (cycAt C x₀ k) := by
    intro x hx k hk1 hk2
    rw [cycAt_mod_lt hpos]
    refine hFC x hx _ (List.getElem_mem _) ?_ ?_
    · exact fun he => hk1 ((List.Nodup.getElem_inj_iff hnodup).mp he)
    · exact fun he => hk2 ((List.Nodup.getElem_inj_iff hnodup).mp he)
  -- no interior vertex of `F` lies on `C`
  have hFCmem : ∀ x ∈ SPGT.interior F, x ∉ C := by
    intro x hx hxC
    obtain ⟨t, ht, hxt⟩ := List.mem_iff_getElem.mp hxC
    have hxc : x = cycAt C x₀ t := by rw [hCk t ht]; exact hxt.symm
    have hadj1 : G.Adj x (cycAt C x₀ (t + 1)) := by
      rw [hxc]; exact hadjm t (t + 1) (Or.inl rfl)
    have hadj2 : G.Adj x (cycAt C x₀ (t + (C.length - 1))) := by
      rw [hxc]
      refine (hadjm (t + (C.length - 1)) t ?_).symm
      left
      have e : t + (C.length - 1) + 1 = t + C.length := by omega
      rw [e, Nat.add_mod_right]
    have h1 : (t + 1) % C.length = h - 1 ∨ (t + 1) % C.length = j - 1 := by
      by_contra hc
      push Not at hc
      exact hFCn x hx (t + 1) hc.1 hc.2 hadj1
    have h2 : (t + (C.length - 1)) % C.length = h - 1 ∨
        (t + (C.length - 1)) % C.length = j - 1 := by
      by_contra hc
      push Not at hc
      exact hFCn x hx (t + (C.length - 1)) hc.1 hc.2 hadj2
    have e1 : (t + 1) % C.length = if t + 1 < C.length then t + 1 else t + 1 - C.length :=
      mod_two_cases hpos (by omega)
    have e2 : (t + (C.length - 1)) % C.length =
        if t + (C.length - 1) < C.length then t + (C.length - 1)
        else t + (C.length - 1) - C.length := mod_two_cases hpos (by omega)
    rcases Nat.lt_or_ge (t + 1) C.length with c1 | c1
    · rw [e1, if_pos c1] at h1
      rcases Nat.eq_zero_or_pos t with rfl | c2
      · rw [e2, if_pos (by omega)] at h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
      · rw [e2, if_neg (by omega)] at h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
    · rw [e1, if_neg (by omega)] at h1
      rcases h1 with h1 | h1 <;> omega
  have hFmemC : ∀ x ∈ F, x ∈ C → (x = cycAt C x₀ (h - 1) ∨ x = cycAt C x₀ (j - 1)) := by
    intro x hxF hxC
    by_contra hc
    push Not at hc
    exact hFCmem x ((PathBasics.mem_interior_iff_of_pathFrom hF').mpr ⟨hxF, hc.1, hc.2⟩) hxC
  ---------------------------------------------------------------------------
  -- Mod-free index calculus for adjacency and equality on `C`.
  ---------------------------------------------------------------------------
  have heqidx : ∀ (s t : ℕ), s < C.length → t < C.length →
      ((cycAt C x₀ s = cycAt C x₀ t) ↔ s = t) := by
    intro s t hs ht
    rw [hceq, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht]
  have hneidx : ∀ (s t : ℕ), s < C.length → t < C.length → s ≠ t →
      cycAt C x₀ s ≠ cycAt C x₀ t := fun s t hs ht hst he => hst ((heqidx s t hs ht).mp he)
  have hadjD : ∀ (s t : ℕ), s < C.length → t < C.length →
      G.Adj (cycAt C x₀ s) (cycAt C x₀ t) →
      (t = s + 1 ∨ s = t + 1 ∨ (s = 0 ∧ t = C.length - 1) ∨ (t = 0 ∧ s = C.length - 1) ∨
       (s = h - 1 ∧ t = j - 1) ∨ (s = j - 1 ∧ t = h - 1)) := by
    intro s t hs ht hadj
    by_contra hc
    push Not at hc
    refine hnadjm s t ?_ ?_ ?_ ?_ hadj
    · rw [Nat.mod_eq_of_lt ht, mod_two_cases hpos (show s + 1 < 2 * C.length by omega)]
      rcases Nat.lt_or_ge (s + 1) C.length with c | c
      · rw [if_pos c]; omega
      · rw [if_neg (by omega)]; omega
    · rw [Nat.mod_eq_of_lt hs, mod_two_cases hpos (show t + 1 < 2 * C.length by omega)]
      rcases Nat.lt_or_ge (t + 1) C.length with c | c
      · rw [if_pos c]; omega
      · rw [if_neg (by omega)]; omega
    · rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht]; omega
    · rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht]; omega
  have hadjU : ∀ (s t : ℕ), s < C.length → t < C.length →
      (t = s + 1 ∨ s = t + 1 ∨ (s = 0 ∧ t = C.length - 1) ∨ (t = 0 ∧ s = C.length - 1)) →
      G.Adj (cycAt C x₀ s) (cycAt C x₀ t) := by
    intro s t hs ht hcase
    refine hadjm s t ?_
    rcases hcase with e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left; rw [e]
    · right; rw [e]
    · right
      rw [e1, e2, show C.length - 1 + 1 = C.length from by omega, Nat.mod_self, Nat.zero_mod]
    · left
      rw [e1, e2, show C.length - 1 + 1 = C.length from by omega, Nat.mod_self, Nat.zero_mod]
  ---------------------------------------------------------------------------
  -- `F` has at least two vertices, and the wrap-around arc
  -- `W = p_{j+1}-⋯-p_n-p_1-⋯-p_{h-1}`.
  ---------------------------------------------------------------------------
  have hFlen2 : 2 ≤ F.length := by
    by_contra hc2
    have hp1 := PathBasics.path_length_pos hF'.1
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (show F.length = 1 by omega)
    rw [hx] at hF'
    have ea : x = cycAt C x₀ (h - 1) := by simpa using hF'.2.1
    have eb : x = cycAt C x₀ (j - 1) := by simpa using hF'.2.2
    exact hneidx (h - 1) (j - 1) (by omega) (by omega) (by omega) (ea.symm.trans eb)
  have hWexc : ∀ t, t < n - j + h - 1 → ∀ u, u < n - j + h - 1 →
      ¬ ((j + t) % C.length = h - 1 ∧ (j + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [mod_two_cases hpos (show j + t < 2 * C.length by omega)] at hcase
    rcases Nat.lt_or_ge (j + t) C.length with c | c
    · rw [if_pos c] at hcase; omega
    · rw [if_neg (by omega)] at hcase; omega
  have hW := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ j (n - j + h - 1)
    (by omega) (by omega) hWexc
  have hWend : cycAt C x₀ (j + (n - j + h - 1) - 1) = cycAt C x₀ (h - 2) := by
    refine cycAt_congr ?_
    rw [show j + (n - j + h - 1) - 1 = (h - 2) + C.length from by omega, Nat.add_mod_right]
  rw [hWend] at hW
  have hWmem : ∀ x ∈ arc C x₀ j (n - j + h - 1), ∃ b : ℕ, b < C.length ∧
      x = cycAt C x₀ b ∧ ((j ≤ b ∧ b ≤ n - 1) ∨ b ≤ h - 2) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_arc_iff C x₀ j (n - j + h - 1) x).mp hx
    refine ⟨(j + t) % C.length, Nat.mod_lt _ hpos,
      (cycAt_mod_lt hpos (j + t)).trans (cycAt_of_lt (Nat.mod_lt _ hpos)).symm, ?_⟩
    rw [mod_two_cases hpos (show j + t < 2 * C.length by omega)]
    rcases Nat.lt_or_ge (j + t) C.length with c | c
    · rw [if_pos c]; left; omega
    · rw [if_neg (by omega)]; right; omega
  ---------------------------------------------------------------------------
  -- `F ++ W` is a hole, hence of even length (`G` is Berge).
  ---------------------------------------------------------------------------
  have hcross : ∀ x ∈ F, ∀ y ∈ arc C x₀ j (n - j + h - 1),
      (G.Adj x y ↔ (x = cycAt C x₀ (j - 1) ∧ y = cycAt C x₀ j) ∨
                   (x = cycAt C x₀ (h - 1) ∧ y = cycAt C x₀ (h - 2))) := by
    intro x hxF y hyW
    obtain ⟨b, hb, rfl, hbr⟩ := hWmem y hyW
    have hjlt : j - 1 < C.length := by omega
    have hhlt : h - 1 < C.length := by omega
    have hh2lt : h - 2 < C.length := by omega
    have hjjlt : j < C.length := by omega
    by_cases e1 : x = cycAt C x₀ (h - 1)
    · subst e1
      constructor
      · intro hadj
        rcases hadjD (h - 1) b hhlt hb hadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
        · exfalso; omega
        · exact Or.inr ⟨rfl, (heqidx b (h - 2) hb hh2lt).mpr (by omega)⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      · rintro (⟨ec, -⟩ | ⟨-, ec⟩)
        · exact absurd ec (hneidx (h - 1) (j - 1) hhlt hjlt (by omega))
        · rw [heqidx b (h - 2) hb hh2lt] at ec
          subst ec
          exact hadjU (h - 1) (h - 2) hhlt hh2lt (Or.inr (Or.inl (by omega)))
    by_cases e2 : x = cycAt C x₀ (j - 1)
    · subst e2
      constructor
      · intro hadj
        rcases hadjD (j - 1) b hjlt hb hadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
        · exact Or.inl ⟨rfl, (heqidx b j hb hjjlt).mpr (by omega)⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      · rintro (⟨-, ec⟩ | ⟨ec, -⟩)
        · rw [heqidx b j hb hjjlt] at ec
          rw [ec]
          exact hadjU (j - 1) j hjlt hjjlt (Or.inl (by omega))
        · exact absurd ec (hneidx (j - 1) (h - 1) hjlt hhlt (by omega))
    · have hxint : x ∈ SPGT.interior F :=
        (PathBasics.mem_interior_iff_of_pathFrom hF').mpr ⟨hxF, e1, e2⟩
      refine iff_of_false ?_ ?_
      · exact hFCn x hxint b (by rw [Nat.mod_eq_of_lt hb]; omega)
          (by rw [Nat.mod_eq_of_lt hb]; omega)
      · rintro (⟨ec, -⟩ | ⟨ec, -⟩)
        · exact e2 ec
        · exact e1 ec
  have hdisjFW : ∀ x ∈ F, x ∉ arc C x₀ j (n - j + h - 1) := by
    intro x hxF hxW
    obtain ⟨b, hb, hxb, hbr⟩ := hWmem x hxW
    rcases hFmemC x hxF (by rw [hxb]; exact cycAt_mem hpos b) with e | e
    · rw [hxb, heqidx b (h - 1) hb (by omega)] at e; omega
    · rw [hxb, heqidx b (j - 1) hb (by omega)] at e; omega
  have hhole : IsHoleList G (F ++ arc C x₀ j (n - j + h - 1)) :=
    PathGlue.glue_hole hF' hW hdisjFW hcross (by rw [arc_length]; omega)
  have hBerge : Berge G := hG.1.1.1
  have hHeven : Even (F.length + (n - j + h - 1)) := by
    have hev := hBerge.1 _ hhole
    simpa only [holeLength, List.length_append, arc_length] using hev
  ---------------------------------------------------------------------------
  -- "the path p₁-⋯-p_h-⋯-p_i is even (by 2.2)", and its mirror image
  -- p_{i+1}-⋯-p_n.
  ---------------------------------------------------------------------------
  have hArcIdx : ∀ (a L : ℕ), a + L ≤ n → ∀ x ∈ arc C x₀ a L,
      ∃ b, a ≤ b ∧ b < a + L ∧ x = cycAt C x₀ b := by
    intro a L haL x hx
    obtain ⟨t, ht, rfl⟩ := (mem_arc_iff C x₀ a L x).mp hx
    exact ⟨a + t, by omega, by omega, rfl⟩
  have hArcY : ∀ (a L : ℕ), ∀ w ∈ arc C x₀ a L, w ∉ Y := by
    intro a L w hw hwY
    obtain ⟨t, ht, rfl⟩ := (mem_arc_iff C x₀ a L w).mp hw
    exact hYC _ hwY (cycAt_mem hpos _)
  -- the path `p₁-⋯-p_i`
  have hAexc : ∀ t, t < i → ∀ u, u < i →
      ¬ ((0 + t) % C.length = h - 1 ∧ (0 + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcase
    omega
  have hA := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ 0 i (by omega) (by omega) hAexc
  rw [show (0 : ℕ) + i - 1 = i - 1 from by omega] at hA
  have hAnoedge : ¬ ∃ u ∈ arc C x₀ 0 i, ∃ v ∈ arc C x₀ 0 i, EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    obtain ⟨b1, hb10, hb1i, rfl⟩ := hArcIdx 0 i (by omega) u hu
    obtain ⟨b2, hb20, hb2i, rfl⟩ := hArcIdx 0 i (by omega) v hv
    have k1 := (hYidx b1 (by omega)).mp hcu
    have k2 := (hYidx b2 (by omega)).mp hcv
    rcases hadjD b1 b2 (by omega) (by omega) hadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      omega
  have hAeven : Even (i - 1) := by
    rcases Nat.even_or_odd (i - 1) with he | ho
    · exact he
    exfalso
    have hconc := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti
      (arc C x₀ 0 i) (cycAt C x₀ 0) (cycAt C x₀ (i - 1)) hA (hArcY 0 i)
      (by rw [PathBasics.pathLength_eq, arc_length]; exact ho)
      ((hYidx 0 (by omega)).mpr (by omega)) ((hYidx (i - 1) (by omega)).mpr (by omega))
      hAnoedge
    obtain ⟨w, hwint, hwadj⟩ := hconc (cycAt C x₀ i) ((hYidx i (by omega)).mpr (by omega))
    obtain ⟨hwmem, hw1, hw2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hA).mp hwint
    obtain ⟨b, hb0, hbi, rfl⟩ := hArcIdx 0 i (by omega) w hwmem
    have hbne1 : b ≠ 0 := by rintro rfl; exact hw1 rfl
    have hbne2 : b ≠ i - 1 := by rintro rfl; exact hw2 rfl
    rcases hadjD i b (by omega) (by omega) hwadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      omega
  -- the path `p_{i+1}-⋯-p_n`
  have hBexc : ∀ t, t < n - i → ∀ u, u < n - i →
      ¬ ((i + t) % C.length = h - 1 ∧ (i + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcase
    omega
  have hB := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ i (n - i)
    (by omega) (by omega) hBexc
  rw [show i + (n - i) - 1 = n - 1 from by omega] at hB
  have hBnoedge : ¬ ∃ u ∈ arc C x₀ i (n - i), ∃ v ∈ arc C x₀ i (n - i), EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    obtain ⟨b1, hb10, hb1i, rfl⟩ := hArcIdx i (n - i) (by omega) u hu
    obtain ⟨b2, hb20, hb2i, rfl⟩ := hArcIdx i (n - i) (by omega) v hv
    have k1 := (hYidx b1 (by omega)).mp hcu
    have k2 := (hYidx b2 (by omega)).mp hcv
    rcases hadjD b1 b2 (by omega) (by omega) hadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      omega
  have hBeven : Even (n - i - 1) := by
    rcases Nat.even_or_odd (n - i - 1) with he | ho
    · exact he
    exfalso
    have hconc := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti
      (arc C x₀ i (n - i)) (cycAt C x₀ i) (cycAt C x₀ (n - 1)) hB (hArcY i (n - i))
      (by rw [PathBasics.pathLength_eq, arc_length]; exact ho)
      ((hYidx i (by omega)).mpr (by omega)) ((hYidx (n - 1) (by omega)).mpr (by omega))
      hBnoedge
    obtain ⟨w, hwint, hwadj⟩ := hconc (cycAt C x₀ (i - 1)) ((hYidx (i - 1) (by omega)).mpr (by omega))
    obtain ⟨hwmem, hw1, hw2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hB).mp hwint
    obtain ⟨b, hb0, hbi, rfl⟩ := hArcIdx i (n - i) (by omega) w hwmem
    have hbne1 : b ≠ i := by rintro rfl; exact hw1 rfl
    have hbne2 : b ≠ n - 1 := by rintro rfl; exact hw2 rfl
    rcases hadjD (i - 1) b (by omega) (by omega) hwadj with e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      omega
  ---------------------------------------------------------------------------
  -- "the path p_i-p_{i-1}-⋯-p_h-F-p_j-⋯-p_n is odd, and therefore has length 3
  --  by 13.6.  So F has length 1, and i = h+1 and n = j+1."
  ---------------------------------------------------------------------------
  have hsubW : ∀ x ∈ arc C x₀ j (n - j), x ∈ arc C x₀ j (n - j + h - 1) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_arc_iff C x₀ j (n - j) x).mp hx
    exact (mem_arc_iff C x₀ j (n - j + h - 1) _).mpr ⟨t, by omega, rfl⟩
  have hD3 := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ j (n - j)
    (by omega) (by omega) (fun t ht u hu => hWexc t (by omega) u (by omega))
  rw [show j + (n - j) - 1 = n - 1 from by omega] at hD3
  have hMcross : ∀ x ∈ F, ∀ y ∈ arc C x₀ j (n - j),
      (G.Adj x y ↔ (x = cycAt C x₀ (j - 1) ∧ y = cycAt C x₀ j)) := by
    intro x hxF y hy
    obtain ⟨c, hc1, hc2, rfl⟩ := hArcIdx j (n - j) (by omega) y hy
    rw [hcross x hxF _ (hsubW _ hy)]
    constructor
    · rintro (hl | ⟨-, hr⟩)
      · exact hl
      · exact absurd ((heqidx c (h - 2) (by omega) (by omega)).mp hr) (by omega)
    · exact fun hl => Or.inl hl
  have hM : IsPathFrom G (F ++ arc C x₀ j (n - j)) (cycAt C x₀ (h - 1)) (cycAt C x₀ (n - 1)) :=
    PathGlue.glue_path hF' hD3 (fun x hxF hx => hdisjFW x hxF (hsubW x hx)) hMcross
  have hRexc : ∀ t, t < i - h → ∀ u, u < i - h →
      ¬ ((h + t) % C.length = h - 1 ∧ (h + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcase
    omega
  have hR := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ h (i - h)
    (by omega) (by omega) hRexc
  rw [show h + (i - h) - 1 = i - 1 from by omega] at hR
  have hRrev : IsPathFrom G (arc C x₀ h (i - h)).reverse (cycAt C x₀ (i - 1)) (cycAt C x₀ h) :=
    PathBasics.isPathFrom_reverse hR
  have hDcross : ∀ x ∈ (arc C x₀ h (i - h)).reverse, ∀ y ∈ F ++ arc C x₀ j (n - j),
      (G.Adj x y ↔ (x = cycAt C x₀ h ∧ y = cycAt C x₀ (h - 1))) := by
    intro x hx y hy
    rw [List.mem_reverse] at hx
    obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx h (i - h) (by omega) x hx
    rw [List.mem_append] at hy
    rcases hy with hyF | hyA
    · by_cases e1 : y = cycAt C x₀ (h - 1)
      · subst e1
        constructor
        · intro hadj
          refine ⟨?_, rfl⟩
          rcases hadjD b (h - 1) (by omega) (by omega) hadj with
            e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
          · exact absurd e (by omega)
          · exact (heqidx b h (by omega) (by omega)).mpr (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
        · rintro ⟨ec, -⟩
          rw [heqidx b h (by omega) (by omega)] at ec
          rw [ec]
          exact hadjU h (h - 1) (by omega) (by omega) (Or.inr (Or.inl (by omega)))
      by_cases e2 : y = cycAt C x₀ (j - 1)
      · subst e2
        refine iff_of_false ?_ ?_
        · intro hadj
          rcases hadjD b (j - 1) (by omega) (by omega) hadj with
            e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
        · rintro ⟨-, ec⟩
          exact absurd ((heqidx (j - 1) (h - 1) (by omega) (by omega)).mp ec) (by omega)
      · have hyint : y ∈ SPGT.interior F :=
          (PathBasics.mem_interior_iff_of_pathFrom hF').mpr ⟨hyF, e1, e2⟩
        refine iff_of_false ?_ ?_
        · intro hadj
          exact hFCn y hyint b (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
            (by rw [Nat.mod_eq_of_lt (by omega)]; omega) hadj.symm
        · rintro ⟨-, ec⟩; exact e1 ec
    · obtain ⟨c, hc1, hc2, rfl⟩ := hArcIdx j (n - j) (by omega) y hyA
      refine iff_of_false ?_ ?_
      · intro hadj
        rcases hadjD b c (by omega) (by omega) hadj with
          e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
      · rintro ⟨-, ec⟩
        exact absurd ((heqidx c (h - 1) (by omega) (by omega)).mp ec) (by omega)
  have hDdisj : ∀ x ∈ (arc C x₀ h (i - h)).reverse, x ∉ F ++ arc C x₀ j (n - j) := by
    intro x hx hy
    rw [List.mem_reverse] at hx
    obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx h (i - h) (by omega) x hx
    rw [List.mem_append] at hy
    rcases hy with hyF | hyA
    · rcases hFmemC _ hyF (cycAt_mem hpos b) with e | e
      · exact absurd ((heqidx b (h - 1) (by omega) (by omega)).mp e) (by omega)
      · exact absurd ((heqidx b (j - 1) (by omega) (by omega)).mp e) (by omega)
    · obtain ⟨c, hc1, hc2, ec⟩ := hArcIdx j (n - j) (by omega) _ hyA
      exact absurd ((heqidx b c (by omega) (by omega)).mp ec) (by omega)
  have hDpath : IsPathFrom G ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j)))
      (cycAt C x₀ (i - 1)) (cycAt C x₀ (n - 1)) :=
    PathGlue.glue_path hRrev hM hDdisj hDcross
  have hDmem : ∀ x ∈ (arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j)),
      (∃ b, ((h ≤ b ∧ b < i) ∨ (j ≤ b ∧ b < n)) ∧ x = cycAt C x₀ b) ∨ x ∈ F := by
    intro x hx
    simp only [List.mem_append, List.mem_reverse] at hx
    rcases hx with h1 | h1 | h1
    · obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx h (i - h) (by omega) x h1
      exact Or.inl ⟨b, Or.inl ⟨by omega, by omega⟩, rfl⟩
    · exact Or.inr h1
    · obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx j (n - j) (by omega) x h1
      exact Or.inl ⟨b, Or.inr ⟨by omega, by omega⟩, rfl⟩
  have hDY : Y ⊆ {v : V | v ∈ ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j)))}ᶜ := by
    intro y hyY hyD
    rcases hDmem y hyD with ⟨b, -, rfl⟩ | hyF
    · exact hYC _ hyY (cycAt_mem hpos b)
    · exact hFY y hyF hyY
  have hDcompl : ∀ x ∈ ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j))),
      VertexComplete G x Y → (x = cycAt C x₀ (i - 1) ∨ x = cycAt C x₀ (n - 1)) := by
    intro x hx hxc
    rcases hDmem x hx with ⟨b, hbr, rfl⟩ | hxF
    · have hk := (hYidx b (by omega)).mp hxc
      rcases (show b = i - 1 ∨ b = n - 1 by omega) with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rw [e])
    · exact absurd hxc (hcon x hxF)
  have hDnoedge : ¬ ∃ u ∈ ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j))),
      ∃ v ∈ ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j))),
      EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    rcases hDcompl u hu hcu with rfl | rfl <;> rcases hDcompl v hv hcv with rfl | rfl
    · exact G.irrefl hadj
    · rcases hadjD (i - 1) (n - 1) (by omega) (by omega) hadj with
        e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
    · rcases hadjD (n - 1) (i - 1) (by omega) (by omega) hadj with
        e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
    · exact G.irrefl hadj
  have hDlen : ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j))).length
      = (i - h) + (F.length + (n - j)) := by
    simp only [List.length_append, List.length_reverse, arc_length]
  have hDodd : Odd (pathLength ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j)))) := by
    rw [PathBasics.pathLength_eq, hDlen, Nat.odd_iff]
    rw [Nat.even_iff] at hHeven hAeven
    omega
  have hDconc := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1
    ((arc C x₀ h (i - h)).reverse ++ (F ++ arc C x₀ j (n - j)))
    (cycAt C x₀ (i - 1)) (cycAt C x₀ (n - 1)) hDpath hDodd Y hDY hYanti
    ((hYidx (i - 1) (by omega)).mpr (by omega)) ((hYidx (n - 1) (by omega)).mpr (by omega))
  have hDstep : i = h + 1 ∧ F.length = 2 ∧ n = j + 1 := by
    rcases hDconc with hedge | ⟨hl3, -⟩
    · exact absurd hedge hDnoedge
    · rw [PathBasics.pathLength_eq, hDlen] at hl3
      refine ⟨by omega, by omega, by omega⟩
  ---------------------------------------------------------------------------
  -- "Similarly h = 2 and j = i + 2": the mirror path
  -- p_{i+1}-⋯-p_j-F-p_h-⋯-p_1 is odd, hence of length 3 by 13.6.
  ---------------------------------------------------------------------------
  have hsubW2 : ∀ x ∈ arc C x₀ 0 (h - 1), x ∈ arc C x₀ j (n - j + h - 1) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_arc_iff C x₀ 0 (h - 1) x).mp hx
    refine (mem_arc_iff C x₀ j (n - j + h - 1) _).mpr ⟨n - j + t, by omega, ?_⟩
    refine cycAt_congr ?_
    rw [show j + (n - j + t) = (0 + t) + C.length from by omega, Nat.add_mod_right]
  have hE1exc : ∀ t, t < j - 1 - i → ∀ u, u < j - 1 - i →
      ¬ ((i + t) % C.length = h - 1 ∧ (i + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcase
    omega
  have hE1 := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ i (j - 1 - i)
    (by omega) (by omega) hE1exc
  rw [show i + (j - 1 - i) - 1 = j - 2 from by omega] at hE1
  have hE3exc : ∀ t, t < h - 1 → ∀ u, u < h - 1 →
      ¬ ((0 + t) % C.length = h - 1 ∧ (0 + u) % C.length = j - 1) := by
    intro t ht u hu hcase
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcase
    omega
  have hE3 := arc_isPathFrom (G := G) hnodup hn4 hcycle hinduced x₀ 0 (h - 1)
    (by omega) (by omega) hE3exc
  rw [show (0 : ℕ) + (h - 1) - 1 = h - 2 from by omega] at hE3
  have hE3rev : IsPathFrom G (arc C x₀ 0 (h - 1)).reverse (cycAt C x₀ (h - 2)) (cycAt C x₀ 0) :=
    PathBasics.isPathFrom_reverse hE3
  have hFrev : IsPathFrom G F.reverse (cycAt C x₀ (j - 1)) (cycAt C x₀ (h - 1)) :=
    PathBasics.isPathFrom_reverse hF'
  have hM'cross : ∀ x ∈ F.reverse, ∀ y ∈ (arc C x₀ 0 (h - 1)).reverse,
      (G.Adj x y ↔ (x = cycAt C x₀ (h - 1) ∧ y = cycAt C x₀ (h - 2))) := by
    intro x hx y hy
    rw [List.mem_reverse] at hx hy
    obtain ⟨c, hc1, hc2, rfl⟩ := hArcIdx 0 (h - 1) (by omega) y hy
    rw [hcross x hx _ (hsubW2 _ hy)]
    constructor
    · rintro (⟨-, hr⟩ | hl)
      · exact absurd ((heqidx c j (by omega) (by omega)).mp hr) (by omega)
      · exact hl
    · exact fun hl => Or.inr hl
  have hM' : IsPathFrom G (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)
      (cycAt C x₀ (j - 1)) (cycAt C x₀ 0) :=
    PathGlue.glue_path hFrev hE3rev
      (fun x hx hy => hdisjFW x (List.mem_reverse.mp hx) (hsubW2 x (List.mem_reverse.mp hy)))
      hM'cross
  have hEcross : ∀ x ∈ arc C x₀ i (j - 1 - i), ∀ y ∈ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse),
      (G.Adj x y ↔ (x = cycAt C x₀ (j - 2) ∧ y = cycAt C x₀ (j - 1))) := by
    intro x hx y hy
    obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx i (j - 1 - i) (by omega) x hx
    rw [List.mem_append, List.mem_reverse, List.mem_reverse] at hy
    rcases hy with hyF | hyA
    · by_cases e2 : y = cycAt C x₀ (j - 1)
      · subst e2
        constructor
        · intro hadj
          refine ⟨?_, rfl⟩
          rcases hadjD b (j - 1) (by omega) (by omega) hadj with
            e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
          · exact (heqidx b (j - 2) (by omega) (by omega)).mpr (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
          · exact absurd e (by omega)
        · rintro ⟨ec, -⟩
          rw [heqidx b (j - 2) (by omega) (by omega)] at ec
          rw [ec]
          exact hadjU (j - 2) (j - 1) (by omega) (by omega) (Or.inl (by omega))
      by_cases e1 : y = cycAt C x₀ (h - 1)
      · subst e1
        refine iff_of_false ?_ ?_
        · intro hadj
          rcases hadjD b (h - 1) (by omega) (by omega) hadj with
            e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
        · rintro ⟨-, ec⟩
          exact absurd ((heqidx (h - 1) (j - 1) (by omega) (by omega)).mp ec) (by omega)
      · have hyint : y ∈ SPGT.interior F :=
          (PathBasics.mem_interior_iff_of_pathFrom hF').mpr ⟨hyF, e1, e2⟩
        refine iff_of_false ?_ ?_
        · intro hadj
          exact hFCn y hyint b (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
            (by rw [Nat.mod_eq_of_lt (by omega)]; omega) hadj.symm
        · rintro ⟨-, ec⟩; exact e2 ec
    · obtain ⟨c, hc1, hc2, rfl⟩ := hArcIdx 0 (h - 1) (by omega) y hyA
      refine iff_of_false ?_ ?_
      · intro hadj
        rcases hadjD b c (by omega) (by omega) hadj with
          e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
      · rintro ⟨-, ec⟩
        exact absurd ((heqidx c (j - 1) (by omega) (by omega)).mp ec) (by omega)
  have hEdisj : ∀ x ∈ arc C x₀ i (j - 1 - i), x ∉ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse) := by
    intro x hx hy
    obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx i (j - 1 - i) (by omega) x hx
    rw [List.mem_append, List.mem_reverse, List.mem_reverse] at hy
    rcases hy with hyF | hyA
    · rcases hFmemC _ hyF (cycAt_mem hpos b) with e | e
      · exact absurd ((heqidx b (h - 1) (by omega) (by omega)).mp e) (by omega)
      · exact absurd ((heqidx b (j - 1) (by omega) (by omega)).mp e) (by omega)
    · obtain ⟨c, hc1, hc2, ec⟩ := hArcIdx 0 (h - 1) (by omega) _ hyA
      exact absurd ((heqidx b c (by omega) (by omega)).mp ec) (by omega)
  have hEpath : IsPathFrom G
      (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse))
      (cycAt C x₀ i) (cycAt C x₀ 0) :=
    PathGlue.glue_path hE1 hM' hEdisj hEcross
  have hEmem : ∀ x ∈ (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)),
      (∃ b, ((i ≤ b ∧ b < j - 1) ∨ b < h - 1) ∧ x = cycAt C x₀ b) ∨ x ∈ F := by
    intro x hx
    simp only [List.mem_append, List.mem_reverse] at hx
    rcases hx with h1 | h1 | h1
    · obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx i (j - 1 - i) (by omega) x h1
      exact Or.inl ⟨b, Or.inl ⟨by omega, by omega⟩, rfl⟩
    · exact Or.inr h1
    · obtain ⟨b, hb1, hb2, rfl⟩ := hArcIdx 0 (h - 1) (by omega) x h1
      exact Or.inl ⟨b, Or.inr (by omega), rfl⟩
  have hEY : Y ⊆ {v : V | v ∈ (arc C x₀ i (j - 1 - i) ++
      (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse))}ᶜ := by
    intro y hyY hyE
    rcases hEmem y hyE with ⟨b, -, rfl⟩ | hyF
    · exact hYC _ hyY (cycAt_mem hpos b)
    · exact hFY y hyF hyY
  have hEcompl : ∀ x ∈ (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)),
      VertexComplete G x Y → (x = cycAt C x₀ i ∨ x = cycAt C x₀ 0) := by
    intro x hx hxc
    rcases hEmem x hx with ⟨b, hbr, rfl⟩ | hxF
    · have hk := (hYidx b (by omega)).mp hxc
      rcases (show b = i ∨ b = 0 by omega) with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rw [e])
    · exact absurd hxc (hcon x hxF)
  have hEnoedge : ¬ ∃ u ∈ (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)),
      ∃ v ∈ (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)),
      EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    rcases hEcompl u hu hcu with rfl | rfl <;> rcases hEcompl v hv hcv with rfl | rfl
    · exact G.irrefl hadj
    · rcases hadjD i 0 (by omega) (by omega) hadj with
        e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
    · rcases hadjD 0 i (by omega) (by omega) hadj with
        e | e | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;> omega
    · exact G.irrefl hadj
  have hElen : (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse)).length
      = (j - 1 - i) + (F.length + (h - 1)) := by
    simp only [List.length_append, List.length_reverse, arc_length]
  have hEodd : Odd (pathLength (arc C x₀ i (j - 1 - i) ++
      (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse))) := by
    rw [PathBasics.pathLength_eq, hElen, Nat.odd_iff]
    rw [Nat.even_iff] at hHeven hBeven
    omega
  have hEconc := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1
    (arc C x₀ i (j - 1 - i) ++ (F.reverse ++ (arc C x₀ 0 (h - 1)).reverse))
    (cycAt C x₀ i) (cycAt C x₀ 0) hEpath hEodd Y hEY hYanti
    ((hYidx i (by omega)).mpr (by omega)) ((hYidx 0 (by omega)).mpr (by omega))
  have hEstep : h = 2 ∧ F.length = 2 ∧ j = i + 2 := by
    rcases hEconc with hedge | ⟨hl3, -⟩
    · exact absurd hedge hEnoedge
    · rw [PathBasics.pathLength_eq, hElen] at hl3
      refine ⟨by omega, by omega, by omega⟩
  ---------------------------------------------------------------------------
  -- "and so n = 6.  Then p₂, p₅ are adjacent, so there is an antipath Q joining
  --  them with interior in Y.  But then in Ḡ the three paths p₁-p₄, p₅-Q-p₂,
  --  p₃-p₆ form a long prism, a contradiction."
  ---------------------------------------------------------------------------
  obtain ⟨hi_h, hF2, hn_j⟩ := hDstep
  obtain ⟨hh2, -, hj_i⟩ := hEstep
  have hFadj : G.Adj (cycAt C x₀ (h - 1)) (cycAt C x₀ (j - 1)) :=
    PathBasics.isPathFrom_ends_adj_of_length_one hF'
      (by rw [PathBasics.pathLength_eq]; omega)
  have hcadj : ∀ (s t : ℕ), s < C.length → t < C.length →
      (t ≠ s + 1) → (s ≠ t + 1) → ¬(s = 0 ∧ t = C.length - 1) → ¬(t = 0 ∧ s = C.length - 1) →
      ¬(s = h - 1 ∧ t = j - 1) → ¬(s = j - 1 ∧ t = h - 1) → s ≠ t →
      Gᶜ.Adj (cycAt C x₀ s) (cycAt C x₀ t) := by
    intro s t hs ht k1 k2 k3 k4 k5 k6 k7
    refine ⟨hneidx s t hs ht k7, ?_⟩
    intro hadj
    rcases hadjD s t hs ht hadj with e | e | e | e | e | e
    · exact k1 e
    · exact k2 e
    · exact k3 e
    · exact k4 e
    · exact k5 e
    · exact k6 e
  -- the antipath `Q` between `p₂` and `p₅` with interior in `Y`
  obtain ⟨Q, hQ, hQint⟩ := InducedPathExtraction.exists_antipath_interior_in (G := G) hYanti
    (u := cycAt C x₀ (h - 1)) (v := cycAt C x₀ (j - 1))
    (fun hm => hYC _ hm (cycAt_mem hpos _)) (fun hm => hYC _ hm (cycAt_mem hpos _))
    (by
      have hnc : ¬ VertexComplete G (cycAt C x₀ (h - 1)) Y := by
        intro hvc; have := (hYidx (h - 1) (by omega)).mp hvc; omega
      rw [VertexComplete] at hnc
      push Not at hnc
      exact hnc)
    (by
      have hnc : ¬ VertexComplete G (cycAt C x₀ (j - 1)) Y := by
        intro hvc; have := (hYidx (j - 1) (by omega)).mp hvc; omega
      rw [VertexComplete] at hnc
      push Not at hnc
      exact hnc)
  have hQmem3 : ∀ v ∈ Q, v = cycAt C x₀ (h - 1) ∨ v = cycAt C x₀ (j - 1) ∨ v ∈ Y := by
    intro v hv
    by_cases e1 : v = cycAt C x₀ (h - 1)
    · exact Or.inl e1
    by_cases e2 : v = cycAt C x₀ (j - 1)
    · exact Or.inr (Or.inl e2)
    · exact Or.inr (Or.inr
        (hQint v ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hv, e1, e2⟩)))
  have hYnotC : ∀ v ∈ Y, ∀ (k : ℕ), v ≠ cycAt C x₀ k :=
    fun v hv k he => hYC v hv (he ▸ cycAt_mem hpos k)
  have hYcnotadj : ∀ (k : ℕ), k < C.length → (k = n - 1 ∨ k = 0 ∨ k = i - 1 ∨ k = i) →
      ∀ v ∈ Y, ¬ Gᶜ.Adj (cycAt C x₀ k) v :=
    fun k hk hkc v hv hadj => hadj.2 ((hYidx k hk).mpr hkc v hv)
  -- `Q` has length `> 1`, since its ends are adjacent in `G`
  have hQpos : 1 ≤ pathLength Q := by
    by_contra hc
    have hQl1 : Q.length = 1 := by
      have := PathBasics.path_length_pos hQ.1
      rw [PathBasics.pathLength_eq] at hc
      omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hQl1
    have a1 := hQ.2.1
    have a2 := hQ.2.2
    rw [hx] at a1 a2
    exact hneidx (h - 1) (j - 1) (by omega) (by omega) (by omega)
      ((Option.some_injective _ a1).symm.trans (Option.some_injective _ a2))
  have hQlong : 1 < pathLength Q.reverse := by
    rw [PathBasics.pathLength_reverse]
    rcases Nat.lt_or_ge 1 (pathLength Q) with hl | hl
    · exact hl
    · exact absurd hFadj
        ((PathBasics.isPathFrom_ends_adj_of_length_one hQ (by omega)).2)
  -- the three paths of the prism in `Ḡ`
  have hq1 : IsPathFrom Gᶜ [cycAt C x₀ 0, cycAt C x₀ i] (cycAt C x₀ 0) (cycAt C x₀ i) :=
    ⟨PathBasics.isPathList_pair (hcadj 0 i (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)), by simp, by simp⟩
  have hq2 : IsPathFrom Gᶜ [cycAt C x₀ (i - 1), cycAt C x₀ (n - 1)]
      (cycAt C x₀ (i - 1)) (cycAt C x₀ (n - 1)) :=
    ⟨PathBasics.isPathList_pair (hcadj (i - 1) (n - 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)), by simp, by simp⟩
  have hq3 : IsPathFrom Gᶜ Q.reverse (cycAt C x₀ (j - 1)) (cycAt C x₀ (h - 1)) :=
    PathBasics.isPathFrom_reverse hQ
  have e12 : ∀ u ∈ [cycAt C x₀ 0, cycAt C x₀ i], ∀ v ∈ [cycAt C x₀ (i - 1), cycAt C x₀ (n - 1)],
      (Gᶜ.Adj u v ↔ (u = cycAt C x₀ 0 ∧ v = cycAt C x₀ (i - 1)) ∨
                    (u = cycAt C x₀ i ∧ v = cycAt C x₀ (n - 1))) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact iff_of_true (hcadj 0 (i - 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inl ⟨rfl, rfl⟩)
    · refine iff_of_false (fun hadj => hadj.2
        (hadjU 0 (n - 1) (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))) ?_
      rintro (⟨-, ec⟩ | ⟨ec, -⟩)
      · exact absurd ((heqidx (n - 1) (i - 1) (by omega) (by omega)).mp ec) (by omega)
      · exact absurd ((heqidx 0 i (by omega) (by omega)).mp ec) (by omega)
    · refine iff_of_false (fun hadj => hadj.2
        (hadjU i (i - 1) (by omega) (by omega) (Or.inr (Or.inl (by omega))))) ?_
      rintro (⟨ec, -⟩ | ⟨-, ec⟩)
      · exact absurd ((heqidx i 0 (by omega) (by omega)).mp ec) (by omega)
      · exact absurd ((heqidx (i - 1) (n - 1) (by omega) (by omega)).mp ec) (by omega)
    · exact iff_of_true (hcadj i (n - 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inr ⟨rfl, rfl⟩)
  have e13 : ∀ u ∈ [cycAt C x₀ 0, cycAt C x₀ i], ∀ v ∈ Q.reverse,
      (Gᶜ.Adj u v ↔ (u = cycAt C x₀ 0 ∧ v = cycAt C x₀ (j - 1)) ∨
                    (u = cycAt C x₀ i ∧ v = cycAt C x₀ (h - 1))) := by
    intro u hu v hv
    rw [List.mem_reverse] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rcases hQmem3 v hv with rfl | rfl | hvY
      · refine iff_of_false (fun hadj => hadj.2
          (hadjU 0 (h - 1) (by omega) (by omega) (Or.inl (by omega)))) ?_
        rintro (⟨-, ec⟩ | ⟨ec, -⟩)
        · exact absurd ((heqidx (h - 1) (j - 1) (by omega) (by omega)).mp ec) (by omega)
        · exact absurd ((heqidx 0 i (by omega) (by omega)).mp ec) (by omega)
      · exact iff_of_true (hcadj 0 (j - 1) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (hYcnotadj 0 (by omega) (by omega) v hvY) ?_
        rintro (⟨-, ec⟩ | ⟨-, ec⟩) <;> exact hYnotC v hvY _ ec
    · rcases hQmem3 v hv with rfl | rfl | hvY
      · exact iff_of_true (hcadj i (h - 1) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inr ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hadj => hadj.2
          (hadjU i (j - 1) (by omega) (by omega) (Or.inl (by omega)))) ?_
        rintro (⟨ec, -⟩ | ⟨-, ec⟩)
        · exact absurd ((heqidx i 0 (by omega) (by omega)).mp ec) (by omega)
        · exact absurd ((heqidx (j - 1) (h - 1) (by omega) (by omega)).mp ec) (by omega)
      · refine iff_of_false (hYcnotadj i (by omega) (by omega) v hvY) ?_
        rintro (⟨-, ec⟩ | ⟨-, ec⟩) <;> exact hYnotC v hvY _ ec
  have e23 : ∀ u ∈ [cycAt C x₀ (i - 1), cycAt C x₀ (n - 1)], ∀ v ∈ Q.reverse,
      (Gᶜ.Adj u v ↔ (u = cycAt C x₀ (i - 1) ∧ v = cycAt C x₀ (j - 1)) ∨
                    (u = cycAt C x₀ (n - 1) ∧ v = cycAt C x₀ (h - 1))) := by
    intro u hu v hv
    rw [List.mem_reverse] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rcases hQmem3 v hv with rfl | rfl | hvY
      · refine iff_of_false (fun hadj => hadj.2
          (hadjU (i - 1) (h - 1) (by omega) (by omega) (Or.inr (Or.inl (by omega))))) ?_
        rintro (⟨-, ec⟩ | ⟨ec, -⟩)
        · exact absurd ((heqidx (h - 1) (j - 1) (by omega) (by omega)).mp ec) (by omega)
        · exact absurd ((heqidx (i - 1) (n - 1) (by omega) (by omega)).mp ec) (by omega)
      · exact iff_of_true (hcadj (i - 1) (j - 1) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (hYcnotadj (i - 1) (by omega) (by omega) v hvY) ?_
        rintro (⟨-, ec⟩ | ⟨-, ec⟩) <;> exact hYnotC v hvY _ ec
    · rcases hQmem3 v hv with rfl | rfl | hvY
      · exact iff_of_true (hcadj (n - 1) (h - 1) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)) (Or.inr ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hadj => hadj.2
          (hadjU (n - 1) (j - 1) (by omega) (by omega) (Or.inr (Or.inl (by omega))))) ?_
        rintro (⟨ec, -⟩ | ⟨-, ec⟩)
        · exact absurd ((heqidx (n - 1) (i - 1) (by omega) (by omega)).mp ec) (by omega)
        · exact absurd ((heqidx (j - 1) (h - 1) (by omega) (by omega)).mp ec) (by omega)
      · refine iff_of_false (hYcnotadj (n - 1) (by omega) (by omega) v hvY) ?_
        rintro (⟨-, ec⟩ | ⟨-, ec⟩) <;> exact hYnotC v hvY _ ec
  exact hG.1.2.2 (PrismBasics.formPrism_mk
    (hcadj 0 (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hcadj 0 (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hcadj (i - 1) (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hcadj i (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hcadj i (h - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hcadj (n - 1) (h - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    (hneidx 0 i (by omega) (by omega) (by omega))
    (hneidx 0 (n - 1) (by omega) (by omega) (by omega))
    (hneidx 0 (h - 1) (by omega) (by omega) (by omega))
    (hneidx (i - 1) i (by omega) (by omega) (by omega))
    (hneidx (i - 1) (n - 1) (by omega) (by omega) (by omega))
    (hneidx (i - 1) (h - 1) (by omega) (by omega) (by omega))
    (hneidx (j - 1) i (by omega) (by omega) (by omega))
    (hneidx (j - 1) (n - 1) (by omega) (by omega) (by omega))
    (hneidx (j - 1) (h - 1) (by omega) (by omega) (by omega))
    hq1 hq2 hq3 e12 e13 e23 (Or.inr (Or.inr hQlong)))

end SPGT

end Workspace.Statements.S15
