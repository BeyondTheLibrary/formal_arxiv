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
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# 16.2, the endgame: the reusable `OddWheelAttachmentEndgame.Setup` API

Lifted verbatim out of `Workspace.ProofLemmas.Thm162Endgame` so that
`Workspace.ProofLemmas.Thm162ClaimFive` can use it too (`Thm162Endgame` imports
`Thm162ClaimFive`, so the dependency had to be factored out to avoid an import cycle).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm162SetupBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentEndgame

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : List V} {Y : Set V} {P : List V} {q f : ℕ → V} {b a c k : ℕ}

/-! ### Reading the `Setup` -/

/-- `q t` is the rim vertex at cyclic position `b + t`. -/
theorem q_eq (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) (t : ℕ) :
    q t = cyc C hp (b + t) := by
  have h := hs.qdef t
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hp)] at h
  simp only [cyc]
  exact (Option.some_injective _ h).symm

/-- `f t` is the `t`-th vertex of `P`. -/
theorem f_eq (hs : Setup G C Y P q f b a c k) (t : ℕ) (ht : t < P.length) :
    P[t]'ht = f t := by
  have h := hs.fdef t ht
  rw [List.getElem?_eq_getElem ht] at h
  exact Option.some_injective _ h

/-- `f` is injective on the index range of `P`. -/
theorem f_inj (hs : Setup G C Y P q f b a c k) {s t : ℕ} (hsl : s < P.length) (htl : t < P.length)
    (h : f s = f t) : s = t := by
  have hnd : P.Nodup := PathBasics.path_nodup hs.path
  have : P[s]'hsl = P[t]'htl := by rw [f_eq hs s hsl, f_eq hs t htl]; exact h
  exact (List.Nodup.getElem_inj_iff hnd).mp this

/-- The path `f₁-⋯-f_k`, as a slice of `P`. -/
noncomputable def fpath (P : List V) (k : ℕ) : List V := (P.drop 1).take (k - 1 + 1)

theorem fpath_length (hs : Setup G C Y P q f b a c k) : (fpath P k).length = k := by
  have hk := hs.klb
  have hlen := hs.plen
  rw [fpath, PathBasics.length_slice P (show (1:ℕ) ≤ k by omega) (show k < P.length by omega)]
  omega

theorem fpath_isPathFrom (hs : Setup G C Y P q f b a c k) :
    IsPathFrom G (fpath P k) (f 1) (f k) := by
  have hk := hs.klb
  have hlen := hs.plen
  have h := PathBasics.isPathFrom_slice hs.path (show (1:ℕ) < k by omega)
    (show k < P.length by omega)
  rw [f_eq hs 1 (by omega), f_eq hs k (by omega)] at h
  exact h

theorem mem_fpath (hs : Setup G C Y P q f b a c k) {x : V} :
    x ∈ fpath P k ↔ ∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = x := by
  have hk := hs.klb
  have hlen := hs.plen
  rw [fpath, PathBasics.mem_slice_iff P (show (1:ℕ) ≤ k by omega) (show k < P.length by omega)]
  constructor
  · rintro ⟨t, ht, h1, h2, rfl⟩
    exact ⟨t, h1, h2, (f_eq hs t ht).symm⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, by omega, h1, h2, f_eq hs t (by omega)⟩

theorem holeC (hs : Setup G C Y P q f b a c k) : IsHoleList G C := hs.wheel.1.1

theorem n6 (hs : Setup G C Y P q f b a c k) : 6 ≤ C.length := hs.wheel.1.2

theorem q_mem (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) (t : ℕ) : q t ∈ C := by
  rw [q_eq hs hp t]; exact cyc_mem hp _

theorem q_congr (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {s t : ℕ}
    (h : s % C.length = t % C.length) : q s = q t := by
  rw [q_eq hs hp s, q_eq hs hp t]
  refine cyc_congr hp ?_
  exact Nat.ModEq.add_left b h

theorem q_inj (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {s t : ℕ}
    (hsn : s < C.length) (htn : t < C.length) (h : q s = q t) : s = t := by
  rw [q_eq hs hp s, q_eq hs hp t] at h
  have h' : s % C.length = t % C.length :=
    Nat.ModEq.add_left_cancel' b (cyc_inj (holeC hs) hp h)
  rwa [Nat.mod_eq_of_lt hsn, Nat.mod_eq_of_lt htn] at h'

/-- *"`X₁ = {p₁}`"*: `p₁` is the only rim neighbour of `f₁`. -/
theorem f1_adj_iff (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {d : ℕ}
    (hd : d < C.length) : G.Adj (f 1) (q d) ↔ d = 0 := by
  rw [hs.adjFst (q d) (q_mem hs hp d)]
  constructor
  · intro h; exact q_inj hs hp hd hp h
  · rintro rfl; rfl

/-- Every rim neighbour of `f_k` sits at a cyclic position between `a` and `c`. -/
theorem fk_adj_range (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {d : ℕ}
    (hd : d < C.length) (hadj : G.Adj (f k) (q d)) : a ≤ d ∧ d ≤ c := by
  constructor
  · by_contra hcon
    push_neg at hcon
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact hs.notAdjLstBase hadj
    · exact hs.minSpec d hd0 hcon hadj
  · by_contra hcon
    push_neg at hcon
    exact hs.maxSpec d hcon hd hadj

theorem f_ne (hs : Setup G C Y P q f b a c k) {s t : ℕ} (hsl : s < P.length) (htl : t < P.length)
    (h : s ≠ t) : f s ≠ f t := fun he => h (f_inj hs hsl htl he)

/-! ### The two holes `H₁` and `H₂` -/

/-- **`H₁ = p₁-f₁-⋯-f_k-p_i-p_{i−1}-⋯-p₁`.** -/
theorem hole_one (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) :
    IsHoleList G (fpath P k ++ (arc C hp b (a + 1)).reverse) := by
  have hk := hs.klb
  have hlen := hs.plen
  refine OddWheelAttachmentClaim4.hole_of_path_and_arc (holeC hs) hp hs.alb hs.aub
    (fpath_isPathFrom hs) (by rw [fpath_length hs]; exact hs.klb) ?_ ?_
  · intro z hz
    obtain ⟨t, h1, h2, rfl⟩ := (mem_fpath hs).mp hz
    exact hs.fnotC t h1 h2
  · intro z hz t ht
    obtain ⟨m, hm1, hm2, rfl⟩ := (mem_fpath hs).mp hz
    have haub := hs.aub
    have htn : t < C.length := by omega
    rw [← q_eq hs hp t]
    have h1k : (1 : ℕ) ≠ k := by omega
    by_cases hm : m = 1
    · subst hm
      rw [f1_adj_iff hs hp htn]
      constructor
      · intro h; exact Or.inl ⟨rfl, h⟩
      · rintro (⟨-, h⟩ | ⟨he, -⟩)
        · exact h
        · exact absurd (f_inj hs (by omega) (by omega) he) h1k
    · by_cases hmk : m = k
      · subst hmk
        constructor
        · intro hadj
          refine Or.inr ⟨rfl, ?_⟩
          by_contra hne
          rcases Nat.eq_zero_or_pos t with rfl | ht0
          · exact hs.notAdjLstBase hadj
          · exact hs.minSpec t ht0 (by omega) hadj
        · rintro (⟨he, -⟩ | ⟨-, rfl⟩)
          · exact absurd (f_inj hs (by omega) (by omega) he) (fun h => h1k h.symm)
          · exact hs.adjLstMin
      · constructor
        · intro hadj
          exact absurd hadj (hs.adjMid m (by omega) (by omega) _ (q_mem hs hp t))
        · rintro (⟨he, -⟩ | ⟨he, -⟩)
          · exact absurd (f_inj hs (by omega) (by omega) he) hm
          · exact absurd (f_inj hs (by omega) (by omega) he) hmk

/-- **`H₂ = p₁-f₁-⋯-f_k-p_j-p_{j+1}-⋯-pₙ-p₁`**, written from `f_k` round the other way. -/
theorem hole_two (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) :
    IsHoleList G ((fpath P k).reverse ++ (arc C hp (b + c) (C.length - c + 1)).reverse) := by
  have hk := hs.klb
  have hlen := hs.plen
  have hclb := hs.clb
  have hcub := hs.cub
  have hn := n6 hs
  refine OddWheelAttachmentClaim4.hole_of_path_and_arc (holeC hs) hp
    (show 1 ≤ C.length - c by omega) (show C.length - c + 2 ≤ C.length by omega)
    (PathBasics.isPathFrom_reverse (fpath_isPathFrom hs))
    (by rw [List.length_reverse, fpath_length hs]; exact hs.klb) ?_ ?_
  · intro z hz
    rw [List.mem_reverse] at hz
    obtain ⟨t, h1, h2, rfl⟩ := (mem_fpath hs).mp hz
    exact hs.fnotC t h1 h2
  · intro z hz t ht
    rw [List.mem_reverse] at hz
    obtain ⟨m, hm1, hm2, rfl⟩ := (mem_fpath hs).mp hz
    have hqe : cyc C hp (b + c + t) = q (c + t) := by
      rw [q_eq hs hp (c + t), ← Nat.add_assoc]
    rw [hqe]
    have h1k : (1 : ℕ) ≠ k := by omega
    by_cases hm : m = 1
    · subst hm
      constructor
      · intro hadj
        refine Or.inr ⟨rfl, ?_⟩
        by_contra hne
        have hlt : c + t < C.length := by omega
        have := (f1_adj_iff hs hp hlt).mp hadj
        omega
      · rintro (⟨he, -⟩ | ⟨-, rfl⟩)
        · exact absurd (f_inj hs (by omega) (by omega) he) h1k
        · have hct : c + (C.length - c) = C.length := by omega
          rw [hct, q_congr hs hp (show C.length % C.length = 0 % C.length by simp)]
          exact ((f1_adj_iff hs hp hp).mpr rfl)
    · by_cases hmk : m = k
      · subst hmk
        constructor
        · intro hadj
          refine Or.inl ⟨rfl, ?_⟩
          by_contra hne
          have ht0 : 0 < t := by omega
          by_cases hfull : c + t = C.length
          · rw [hfull, q_congr hs hp (show C.length % C.length = 0 % C.length by simp)] at hadj
            exact hs.notAdjLstBase hadj
          · exact hs.maxSpec (c + t) (by omega) (by omega) hadj
        · rintro (⟨-, rfl⟩ | ⟨he, -⟩)
          · rw [Nat.add_zero]; exact hs.adjLstMax
          · exact absurd (f_inj hs (by omega) (by omega) he) (fun h => h1k h.symm)
      · constructor
        · intro hadj
          exact absurd hadj (hs.adjMid m (by omega) (by omega) _ (q_mem hs hp (c + t)))
        · rintro (⟨he, -⟩ | ⟨he, -⟩)
          · exact absurd (f_inj hs (by omega) (by omega) he) hmk
          · exact absurd (f_inj hs (by omega) (by omega) he) hm

theorem mem_hole_one (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {x : V} :
    x ∈ (fpath P k ++ (arc C hp b (a + 1)).reverse) ↔
      (∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = x) ∨ (∃ d : ℕ, d ≤ a ∧ q d = x) := by
  rw [List.mem_append, List.mem_reverse, mem_fpath hs, mem_arc hp]
  constructor
  · rintro (h | ⟨t, ht, hte⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, by omega, by rw [q_eq hs hp t]; exact hte⟩
  · rintro (h | ⟨d, hd, hde⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, by omega, by rw [← q_eq hs hp d]; exact hde⟩

theorem mem_hole_two (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {x : V} :
    x ∈ ((fpath P k).reverse ++ (arc C hp (b + c) (C.length - c + 1)).reverse) ↔
      (∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ f t = x) ∨ (∃ d : ℕ, c ≤ d ∧ d ≤ C.length ∧ q d = x) := by
  have hcub := hs.cub
  rw [List.mem_append, List.mem_reverse, List.mem_reverse, mem_fpath hs, mem_arc hp]
  constructor
  · rintro (h | ⟨t, ht, hte⟩)
    · exact Or.inl h
    · refine Or.inr ⟨c + t, by omega, by omega, ?_⟩
      rw [q_eq hs hp (c + t), ← Nat.add_assoc]
      exact hte
  · rintro (h | ⟨d, hd1, hd2, hde⟩)
    · exact Or.inl h
    · refine Or.inr ⟨d - c, by omega, ?_⟩
      rw [show b + c + (d - c) = b + d by omega, ← q_eq hs hp d]
      exact hde

/-- Two rim vertices are adjacent exactly when their cyclic positions are consecutive. -/
theorem q_adj (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {d e : ℕ}
    (hd : d < C.length) (he : e < C.length) (hadj : G.Adj (q d) (q e)) :
    e = (d + 1) % C.length ∨ d = (e + 1) % C.length := by
  rw [q_eq hs hp d, q_eq hs hp e, cyc_adj (holeC hs) hp] at hadj
  rcases hadj with h | h
  · left
    have h1 : (b + e) ≡ (b + (d + 1)) [MOD C.length] := by rw [← Nat.add_assoc]; exact h
    have h2 : e ≡ d + 1 [MOD C.length] := Nat.ModEq.add_left_cancel' b h1
    rw [Nat.ModEq, Nat.mod_eq_of_lt he] at h2
    exact h2
  · right
    have h1 : (b + d) ≡ (b + (e + 1)) [MOD C.length] := by rw [← Nat.add_assoc]; exact h
    have h2 : d ≡ e + 1 [MOD C.length] := Nat.ModEq.add_left_cancel' b h1
    rw [Nat.ModEq, Nat.mod_eq_of_lt hd] at h2
    exact h2

/-- Every rim vertex is `q d` for a unique `d < n`. -/
theorem exists_q (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {w : V} (hw : w ∈ C) :
    ∃ d : ℕ, d < C.length ∧ q d = w := by
  obtain ⟨t, ht, hte⟩ := OddWheelAttachmentClaim4.exists_offset_cyc hp b hw
  exact ⟨t, ht, by rw [q_eq hs hp t]; exact hte⟩

/-- The wheel's two disjoint `Y`-complete edges give four pairwise distinct `Y`-complete
vertices of the rim. -/
theorem four_yComplete {G : SimpleGraph V} {C : List V} {Y : Set V} (hw : IsWheel G C Y) :
    ∃ A B D E : V, A ∈ C ∧ B ∈ C ∧ D ∈ C ∧ E ∈ C ∧
      VertexComplete G A Y ∧ VertexComplete G B Y ∧ VertexComplete G D Y ∧
      VertexComplete G E Y ∧
      A ≠ B ∧ A ≠ D ∧ A ≠ E ∧ B ≠ D ∧ B ≠ E ∧ D ≠ E := by
  obtain ⟨A, B, D, E, hA, hB, hD, hE, hAB, hDE, h1, h2, h3, h4⟩ := hw.2.2
  exact ⟨A, B, D, E, hA, hB, hD, hE, hAB.2.1, hAB.2.2, hDE.2.1, hDE.2.2,
    hAB.1.ne, h1, h2, h3, h4, hDE.1.ne⟩

/-- Four pairwise distinct vertices cannot all lie in a three-element set. -/
theorem not_four_in_three {A B D E u v w : V}
    (hA : A = u ∨ A = v ∨ A = w) (hB : B = u ∨ B = v ∨ B = w)
    (hD : D = u ∨ D = v ∨ D = w) (hE : E = u ∨ E = v ∨ E = w)
    (hAB : A ≠ B) (hAD : A ≠ D) (hAE : A ≠ E) (hBD : B ≠ D) (hBE : B ≠ E) (hDE : D ≠ E) :
    False := by
  rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;>
    rcases hD with rfl | rfl | rfl <;> rcases hE with rfl | rfl | rfl <;> simp_all

theorem hole_one_length (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) :
    (fpath P k ++ (arc C hp b (a + 1)).reverse).length = k + a + 1 := by
  rw [List.length_append, List.length_reverse, arc_length, fpath_length hs]
  omega

theorem hole_one_getElem_f (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {t : ℕ}
    (ht : t < k) (hlt : t < (fpath P k ++ (arc C hp b (a + 1)).reverse).length) :
    (fpath P k ++ (arc C hp b (a + 1)).reverse)[t]'hlt = f (t + 1) := by
  have hlen := hs.plen
  have hk := hs.klb
  have hft : t < (fpath P k).length := by rw [fpath_length hs]; exact ht
  rw [List.getElem_append_left hft]
  simp only [fpath] at hft ⊢
  rw [PathBasics.getElem_slice' P hft (show t + 1 < P.length by omega) (by omega)]
  exact f_eq hs (t + 1) _

theorem hole_one_getElem_q (hs : Setup G C Y P q f b a c k) (hp : 0 < C.length) {s : ℕ}
    (hsa : s ≤ a) (hlt : k + s < (fpath P k ++ (arc C hp b (a + 1)).reverse).length) :
    (fpath P k ++ (arc C hp b (a + 1)).reverse)[k + s]'hlt = q (a - s) := by
  have hfl : (fpath P k).length = k := fpath_length hs
  have hge : ¬ (k + s < (fpath P k).length) := by rw [hfl]; omega
  rw [List.getElem_append_right (by omega)]
  rw [List.getElem_reverse]
  rw [arc_getElem]
  rw [q_eq hs hp (a - s)]
  refine congrArg _ ?_
  rw [arc_length, hfl]
  omega

end Workspace.ProofLemmas.Thm162SetupBasics
