import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentYCount
import Workspace.ProofLemmas.OddWheelAttachmentEndgame
import Workspace.ProofLemmas.Thm153Rotated
import Workspace.ProofLemmas.Thm162SetupBasics
import Workspace.ProofLemmas.Thm162ClaimFive
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# 16.2, the endgame: from *"From (4) we may assume that `X₁` has only one member"* to the end

PAPER (16.2, printed pp. 99–100).  `Workspace.ProofLemmas.OddWheelAttachmentEndgame.Setup`
records the index picture of that closing part (the base offset `b`, the rim reader `q`, the
path reader `f`, and the paper's `i = a+1`, `j = c+1`), and
`…OddWheelAttachmentEndgame.Contradiction` is the statement that this configuration is
impossible — the paragraph after claim (4), claim (5), and the closing paragraph.

`Workspace.ProofLemmas.OddWheelAttachmentEndgameSetup.endgame_of_contradiction` turns this into
`OddWheelAttachmentMain.Endgame`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm162Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentEndgame
open Workspace.ProofLemmas.Thm162SetupBasics

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V} {q f : ℕ → V} {b a c k : ℕ}


/-! ### The endgame -/

/-- **The endgame of 16.2.** -/
theorem endgame_contradiction (G : SimpleGraph V) : Contradiction G := by
  classical
  rintro C Y P q f b a c k hs
  have hn6 : 6 ≤ C.length := n6 hs
  have hp : 0 < C.length := by omega
  have hC : IsHoleList G C := holeC hs
  have hBerge : Berge G := hs.inF6.1.1.1
  have hYanti : AnticonnectedSet G Y := hs.wheel.2.1.2.1
  have hCY : ∀ w ∈ C, w ∉ Y := hs.wheel.2.1.2.2
  have hnEven : Even C.length := hBerge.1 C hC
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
  have hac := hs.ac
  have hSY : ∀ z ∈ fpath P k, z ∉ Y := by
    intro z hz; obtain ⟨t, h1, h2, rfl⟩ := (mem_fpath hs).mp hz; exact hs.fnotY t h1 h2
  have hSnc : ∀ z ∈ fpath P k, ¬ VertexComplete G z Y := by
    intro z hz; obtain ⟨t, h1, h2, rfl⟩ := (mem_fpath hs).mp hz; exact hs.fnotComplete t h1 h2
  have hq0 : q 0 = cyc C hp b := q_eq hs hp 0
  have hqa : q a = cyc C hp (b + a) := q_eq hs hp a
  have hqc : q c = cyc C hp (b + c) := q_eq hs hp c
  -- *"Since `p₁, p_i` have different wheel-parity, and so do `p₁, p_j` …"*
  have hπa : π (q 0) ≠ π (q a) := by
    intro he
    exact (hs.oppLst a hs.adjLstMin).2.2.2
      ((hπ (q 0) (q a) (q_mem hs hp 0) (q_mem hs hp a) (hs.oppLst a hs.adjLstMin).1).mpr he)
  have hπc : π (q 0) ≠ π (q c) := by
    intro he
    exact (hs.oppLst c hs.adjLstMax).2.2.2
      ((hπ (q 0) (q c) (q_mem hs hp 0) (q_mem hs hp c) (hs.oppLst c hs.adjLstMax).1).mpr he)
  -- *"From the hole `H₁` we deduce that `i, k` have the same parity …"*
  obtain ⟨h1even, h1edge, y₁, z₁, h1set, h1ne, h1adj⟩ :=
    OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep hs.alb hs.aub
      hSY hSnc (by rw [← hq0, ← hqa]; exact hπa) (hole_one hs hp)
  -- *"… and from the hole `H₂` that `j, k` have the same parity."*
  have hqn : q 0 = cyc C hp (b + c + (C.length - c)) := by
    rw [show b + c + (C.length - c) = b + C.length by omega, hq0]
    exact cyc_congr hp (by rw [Nat.add_mod_right])
  obtain ⟨h2even, h2edge, y₂, z₂, h2set, h2ne, h2adj⟩ :=
    OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep
      (show 1 ≤ C.length - c by omega) (show C.length - c + 2 ≤ C.length by omega)
      (fun z hz => hSY z (List.mem_reverse.mp hz))
      (fun z hz => hSnc z (List.mem_reverse.mp hz))
      (by rw [← hqc, ← hqn]; exact fun he => hπc he.symm) (hole_two hs hp)
  rw [fpath_length hs] at h1even
  rw [List.length_reverse, fpath_length hs] at h2even
  rw [Nat.even_iff] at h1even h2even hnEven
  -- *"(So either `p_i = p_j` or `p_i, p_j` are nonadjacent.)"*
  have hpar : a % 2 = c % 2 := by omega
  rcases Nat.lt_or_ge a c with hlt | hge
  · -- *"So `j > i`, and hence `j ≥ i + 2`."*
    have hac2 : a + 2 ≤ c := by omega
    -- *"Since `f_k` is adjacent to `p_i`, and `i < j` and `j − i` is even, it follows from (5)
    -- that `i = 2`, and similarly `f_k` has no neighbours in `{p_{i+2}, …, p_{n−1}}` and
    -- `j = n`.  So `f_k` has no neighbours in `{p₃, …, p_{n−1}}`, and therefore `p₂, pₙ` are
    -- its only neighbours, contradicting that there are nonadjacent vertices in `X` of
    -- opposite wheel-parity."*
    obtain ⟨h5a, h5b⟩ := Thm162ClaimFive.claim_five hs hac2
    have ha1 : a = 1 := by
      by_contra hne
      exact h5a a (by omega) (by omega) hs.adjLstMin
    have hcn : c = C.length - 1 := by
      by_contra hne
      exact h5b c (by omega) (by omega) hs.adjLstMax
    obtain ⟨d, hd1, hd2, hdadj⟩ := hs.midNbr
    by_cases hdc : d + 2 ≤ c
    · exact h5a d hd1 hdc hdadj
    · exact h5b d (by omega) hd2 hdadj
  · -- *"Suppose that `i = j`.  Then there are only two `Y`-complete edges in `C`, and therefore
    -- they are disjoint, and `p₁, p_i` are not `Y`-complete … contrary to 15.3 applied to `C`."*
    have haeq : c = a := by omega
    subst haeq
    have ha2 : 2 ≤ c := hs.clb
    have hfk : ∀ d : ℕ, d < C.length → G.Adj (f k) (q d) → d = c := by
      intro d hd hadj
      have := fk_adj_range hs hp hd hadj
      omega
    have hy₁c : VertexComplete G y₁ Y :=
      ((Set.ext_iff.mp h1set y₁).mpr (by simp)).2
    have hz₁c : VertexComplete G z₁ Y :=
      ((Set.ext_iff.mp h1set z₁).mpr (by simp)).2
    have hy₂c : VertexComplete G y₂ Y :=
      ((Set.ext_iff.mp h2set y₂).mpr (by simp)).2
    have hz₂c : VertexComplete G z₂ Y :=
      ((Set.ext_iff.mp h2set z₂).mpr (by simp)).2
    have hin1 : ∀ d : ℕ, d ≤ c → VertexComplete G (q d) Y → q d = y₁ ∨ q d = z₁ := by
      intro d hd hc'
      have hmem : q d ∈ (fpath P k ++ (arc C hp b (c + 1)).reverse) :=
        (mem_hole_one hs hp).mpr (Or.inr ⟨d, hd, rfl⟩)
      have h := (Set.ext_iff.mp h1set (q d)).mp ⟨hmem, hc'⟩
      simpa using h
    have hin2 : ∀ d : ℕ, c ≤ d → d ≤ C.length → VertexComplete G (q d) Y →
        q d = y₂ ∨ q d = z₂ := by
      intro d hd1 hd2 hc'
      have hmem : q d ∈ ((fpath P k).reverse ++ (arc C hp (b + c) (C.length - c + 1)).reverse) :=
        (mem_hole_two hs hp).mpr (Or.inr ⟨d, hd1, hd2, rfl⟩)
      have h := (Set.ext_iff.mp h2set (q d)).mp ⟨hmem, hc'⟩
      simpa using h
    have hYall : ∀ w : V, w ∈ C → VertexComplete G w Y →
        (w = y₁ ∨ w = z₁) ∨ (w = y₂ ∨ w = z₂) := by
      intro w hw hwc
      obtain ⟨d, hd, rfl⟩ := exists_q hs hp hw
      by_cases hda : d ≤ c
      · exact Or.inl (hin1 d hda hwc)
      · exact Or.inr (hin2 d (by omega) (by omega) hwc)
    have hkey : ∀ u v w' : V,
        (∀ x : V, x ∈ C → VertexComplete G x Y → x = u ∨ x = v ∨ x = w') → False := by
      intro u v w' hall
      obtain ⟨A, B, D, E, hA, hB, hD, hE, cA, cB, cD, cE, e1, e2, e3, e4, e5, e6⟩ :=
        four_yComplete hs.wheel
      exact not_four_in_three (hall A hA cA) (hall B hB cB) (hall D hD cD) (hall E hE cE)
        e1 e2 e3 e4 e5 e6
    have hqn0 : q C.length = q 0 := q_congr hs hp (by simp)
    have hq0nc : ¬ VertexComplete G (q 0) Y := by
      intro hc'
      have h1 := hin1 0 (by omega) hc'
      have h2 := hin2 C.length (by omega) (by omega) (by rw [hqn0]; exact hc')
      rw [hqn0] at h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact hkey (q 0) z₁ z₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q 0) z₁ y₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q 0) y₁ z₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q 0) y₁ y₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
    have hqanc : ¬ VertexComplete G (q c) Y := by
      intro hc'
      have h1 := hin1 c (by omega) hc'
      have h2 := hin2 c (by omega) (by omega) hc'
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact hkey (q c) z₁ z₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q c) z₁ y₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q c) y₁ z₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
      · exact hkey (q c) y₁ y₂ (fun x hx hxc => by have h' := hYall x hx hxc; tauto)
    -- the two `Y`-complete edges sit strictly inside the two gaps
    have hposA : ∀ w : V, (w = y₁ ∨ w = z₁) → ∃ d : ℕ, 1 ≤ d ∧ d + 1 ≤ c ∧ q d = w := by
      intro w hw
      have hmem2 : w ∈ (fpath P k ++ (arc C hp b (c + 1)).reverse) ∧ VertexComplete G w Y := by
        refine (Set.ext_iff.mp h1set w).mpr ?_
        rcases hw with rfl | rfl
        · simp
        · simp
      obtain ⟨hmem, hwc⟩ := hmem2
      rcases (mem_hole_one hs hp).mp hmem with ⟨t, ht1, ht2, rfl⟩ | ⟨d, hd, rfl⟩
      · exact absurd hwc (hs.fnotComplete t ht1 ht2)
      · refine ⟨d, ?_, ?_, rfl⟩
        · rcases Nat.eq_zero_or_pos d with rfl | h
          · exact absurd hwc hq0nc
          · exact h
        · by_contra hcon
          have hdc : d = c := by omega
          subst hdc
          exact absurd hwc hqanc
    have hposB : ∀ w : V, (w = y₂ ∨ w = z₂) →
        ∃ d : ℕ, c + 1 ≤ d ∧ d + 1 ≤ C.length ∧ q d = w := by
      intro w hw
      have hmem2 : w ∈ ((fpath P k).reverse ++ (arc C hp (b + c) (C.length - c + 1)).reverse) ∧
          VertexComplete G w Y := by
        refine (Set.ext_iff.mp h2set w).mpr ?_
        rcases hw with rfl | rfl
        · simp
        · simp
      obtain ⟨hmem, hwc⟩ := hmem2
      rcases (mem_hole_two hs hp).mp hmem with ⟨t, ht1, ht2, rfl⟩ | ⟨d, hd1, hd2, rfl⟩
      · exact absurd hwc (hs.fnotComplete t ht1 ht2)
      · refine ⟨d, ?_, ?_, rfl⟩
        · rcases Nat.lt_or_ge c d with h | h
          · omega
          · have hdc : d = c := by omega
            subst hdc
            exact absurd hwc hqanc
        · by_contra hcon
          have hdn : d = C.length := by omega
          subst hdn
          rw [hqn0] at hwc
          exact absurd hwc hq0nc
    obtain ⟨d₁, hd₁1, hd₁2, hd₁e⟩ := hposA y₁ (Or.inl rfl)
    obtain ⟨e₁, he₁1, he₁2, he₁e⟩ := hposA z₁ (Or.inr rfl)
    obtain ⟨d₂, hd₂1, hd₂2, hd₂e⟩ := hposB y₂ (Or.inl rfl)
    obtain ⟨e₂, he₂1, he₂2, he₂e⟩ := hposB z₂ (Or.inr rfl)
    have hcons1 : e₁ = d₁ + 1 ∨ d₁ = e₁ + 1 := by
      rcases q_adj hs hp (show d₁ < C.length by omega) (show e₁ < C.length by omega)
          (by rw [hd₁e, he₁e]; exact h1adj) with h | h
      · left; rw [h, Nat.mod_eq_of_lt (by omega)]
      · right; rw [h, Nat.mod_eq_of_lt (by omega)]
    have hcons2 : e₂ = d₂ + 1 ∨ d₂ = e₂ + 1 := by
      rcases q_adj hs hp (show d₂ < C.length by omega) (show e₂ < C.length by omega)
          (by rw [hd₂e, he₂e]; exact h2adj) with h | h
      · left
        by_cases hlt : d₂ + 1 < C.length
        · rw [h, Nat.mod_eq_of_lt hlt]
        · exfalso
          have hfull : d₂ + 1 = C.length := by omega
          rw [hfull, Nat.mod_self] at h
          omega
      · right
        by_cases hlt : e₂ + 1 < C.length
        · rw [h, Nat.mod_eq_of_lt hlt]
        · exfalso
          have hfull : e₂ + 1 = C.length := by omega
          rw [hfull, Nat.mod_self] at h
          omega
    obtain ⟨α, hα1, hα2, hαset⟩ :
        ∃ α : ℕ, 1 ≤ α ∧ α + 2 ≤ c ∧
          ∀ w : V, (w = y₁ ∨ w = z₁) ↔ (w = q α ∨ w = q (α + 1)) := by
      rcases hcons1 with rfl | rfl
      · exact ⟨d₁, hd₁1, by omega, by intro w; rw [← hd₁e, ← he₁e]; try tauto⟩
      · exact ⟨e₁, he₁1, by omega, by intro w; rw [← hd₁e, ← he₁e]; try tauto⟩
    obtain ⟨β, hβ1, hβ2, hβset⟩ :
        ∃ β : ℕ, c + 1 ≤ β ∧ β + 2 ≤ C.length ∧
          ∀ w : V, (w = y₂ ∨ w = z₂) ↔ (w = q β ∨ w = q (β + 1)) := by
      rcases hcons2 with rfl | rfl
      · exact ⟨d₂, hd₂1, by omega, by intro w; rw [← hd₂e, ← he₂e]; try tauto⟩
      · exact ⟨e₂, he₂1, by omega, by intro w; rw [← hd₂e, ← he₂e]; try tauto⟩
    -- the four cyclic positions, read from the base `b + α + 1`
    have E1 : cyc C hp (b + α + 1 + (C.length - 1)) = q α := by
      rw [q_eq hs hp α]
      exact cyc_congr hp (by rw [show b + α + 1 + (C.length - 1) = b + α + C.length by omega,
        Nat.add_mod_right])
    have E2 : cyc C hp (b + α + 1) = q (α + 1) := by
      rw [q_eq hs hp (α + 1), Nat.add_assoc]
    have E3 : cyc C hp (b + α + 1 + (β - α - 1)) = q β := by
      rw [q_eq hs hp β, show b + α + 1 + (β - α - 1) = b + β by omega]
    have E4 : cyc C hp (b + α + 1 + (β - α)) = q (β + 1) := by
      rw [q_eq hs hp (β + 1), show b + α + 1 + (β - α) = b + (β + 1) by omega]
    have E5 : cyc C hp (b + α + 1 + (c - α - 1)) = q c := by
      rw [q_eq hs hp c, show b + α + 1 + (c - α - 1) = b + c by omega]
    have E6 : cyc C hp (b + α + 1 + (C.length - α - 1)) = q 0 := by
      rw [q_eq hs hp 0]
      exact cyc_congr hp (by rw [show b + α + 1 + (C.length - α - 1) = b + C.length by omega,
        Nat.add_mod_right, Nat.add_zero])
    -- the path `p_i-f_k-⋯-f₁-p₁`, cut out of the hole `H₁`
    have hH1hole : IsHoleList G (fpath P k ++ (arc C hp b (c + 1)).reverse) := hole_one hs hp
    have hH1len : (fpath P k ++ (arc C hp b (c + 1)).reverse).length = k + c + 1 :=
      hole_one_length hs hp
    have hH1pos : 0 < (fpath P k ++ (arc C hp b (c + 1)).reverse).length := by omega
    have harclen : (arc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c) (k + 2)).length
        = k + 2 := arc_length hH1pos _ _
    have hF0 := arc_isPathFrom hH1hole hH1pos (a := k + c) (L := k + 2)
      (by omega) (by rw [hH1len]; omega)
    have hFfirst : cyc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c) = q 0 := by
      rw [cyc_eq hH1pos (by omega)]
      simpa using hole_one_getElem_q hs hp (s := c) (by omega) (by omega)
    have hFlast : cyc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c + (k + 2) - 1)
        = q c := by
      have hmod : (k + c + (k + 2) - 1) % (fpath P k ++ (arc C hp b (c + 1)).reverse).length
          = k % (fpath P k ++ (arc C hp b (c + 1)).reverse).length := by
        rw [hH1len, show k + c + (k + 2) - 1 = k + (k + c + 1) by omega, Nat.add_mod_right]
      rw [cyc_congr hH1pos hmod, cyc_eq hH1pos (by omega)]
      simpa using hole_one_getElem_q hs hp (s := 0) (by omega) (by omega)
    have hFmid : ∀ t : ℕ, 1 ≤ t → t ≤ k →
        cyc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c + t) = f t := by
      intro t h1 h2
      have hmod : (k + c + t) % (fpath P k ++ (arc C hp b (c + 1)).reverse).length
          = (t - 1) % (fpath P k ++ (arc C hp b (c + 1)).reverse).length := by
        rw [hH1len, show k + c + t = (t - 1) + (k + c + 1) * 1 by omega,
          Nat.add_mul_mod_self_left]
      rw [cyc_congr hH1pos hmod, cyc_eq hH1pos (by omega),
        hole_one_getElem_f hs hp (t := t - 1) (by omega) (by omega)]
      congr 1
      omega
    have hFmem : ∀ w : V,
        w ∈ arc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c) (k + 2) →
        w = q 0 ∨ (∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ f m = w) ∨ w = q c := by
      intro w hw
      obtain ⟨t, ht, hte⟩ := (mem_arc hH1pos).mp hw
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · left; rw [← hte]; exact hFfirst
      · by_cases htk : t ≤ k
        · exact Or.inr (Or.inl ⟨t, ht0, htk, by rw [← hte]; exact (hFmid t ht0 htk).symm⟩)
        · refine Or.inr (Or.inr ?_)
          rw [← hte]
          have htv : t = k + 1 := by omega
          subst htv
          have := hFlast
          rw [show k + c + (k + 2) - 1 = k + c + (k + 1) by omega] at this
          exact this
    have hFint : ∀ x : V,
        x ∈ SPGT.interior (arc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c) (k + 2))
        → ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ f m = x := by
      intro x hx
      obtain ⟨idx, hidx, hi1, hi2, hxe⟩ := PathBasics.exists_getElem_of_mem_interior
        (arc_isPathList hH1hole hH1pos (show 1 ≤ k + 2 by omega)
          (by rw [hH1len]; omega)) hx
      rw [arc_getElem] at hxe
      rw [harclen] at hidx hi2
      exact ⟨idx, by omega, by omega, by rw [← hxe]; exact (hFmid idx (by omega) (by omega)).symm⟩
    have hFrev : IsPathFrom G
        (arc (fpath P k ++ (arc C hp b (c + 1)).reverse) hH1pos (k + c) (k + 2)).reverse
        (q c) (q 0) := by
      have h := PathBasics.isPathFrom_reverse hF0
      rw [hFfirst, hFlast] at h
      exact h
    -- 15.3, applied to `C`
    have hfinal := Thm153Rotated.clean_path_hits_yComplete hs.inF6 hC hp hn6
      (fun y hy hyC => hCY y hyC hy) hYanti (b + α + 1)
      (h := c - α) (i := β - α) (j := C.length - α)
      (by omega) (by omega) (by omega) (by omega)
      (by
        intro w hw
        rw [E1, E2, E3, E4]
        constructor
        · intro hwc
          rcases hYall w hw hwc with hcase | hcase
          · have := (hαset w).mp hcase; tauto
          · have := (hβset w).mp hcase; tauto
        · rintro (rfl | rfl | rfl | rfl)
          · rcases (hαset (q α)).mpr (Or.inl rfl) with h | h
            · rw [h]; exact hy₁c
            · rw [h]; exact hz₁c
          · rcases (hαset (q (α + 1))).mpr (Or.inr rfl) with h | h
            · rw [h]; exact hy₁c
            · rw [h]; exact hz₁c
          · rcases (hβset (q β)).mpr (Or.inl rfl) with h | h
            · rw [h]; exact hy₂c
            · rw [h]; exact hz₂c
          · rcases (hβset (q (β + 1))).mpr (Or.inr rfl) with h | h
            · rw [h]; exact hy₂c
            · rw [h]; exact hz₂c)
      (by rw [E5, E6]; exact hFrev)
      (by
        intro w hw
        rw [List.mem_reverse] at hw
        rcases hFmem w hw with rfl | ⟨m, hm1, hm2, rfl⟩ | rfl
        · exact hCY (q 0) (q_mem hs hp 0)
        · exact hs.fnotY m hm1 hm2
        · exact hCY (q c) (q_mem hs hp c))
      (by
        rw [E5, E6]
        intro x hx w hw hwa hw0 hadj
        rw [PathBasics.mem_interior_reverse] at hx
        obtain ⟨m, hm1, hm2, rfl⟩ := hFint x hx
        by_cases hm : m = 1
        · subst hm
          exact hw0 ((hs.adjFst w hw).mp hadj)
        · by_cases hmk : m = k
          · subst hmk
            obtain ⟨d, hd, rfl⟩ := exists_q hs hp hw
            exact hwa (by rw [hfk d hd hadj])
          · exact hs.adjMid m (by omega) (by omega) w hw hadj)
    obtain ⟨w, hwF, hwc⟩ := hfinal
    rw [List.mem_reverse] at hwF
    rcases hFmem w hwF with rfl | ⟨m, hm1, hm2, rfl⟩ | rfl
    · exact hq0nc hwc
    · exact hs.fnotComplete m hm1 hm2 hwc
    · exact hqanc hwc

end Workspace.ProofLemmas.Thm162Endgame
