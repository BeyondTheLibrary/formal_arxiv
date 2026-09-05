import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm162ClaimFourHelpers
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# Abstract track arguments for 16.2, claim (4)

The two transition arcs cut from the rim are used only through their induced-path structure,
their two possible bridge edges, and the parity of the two holes obtained by closing them
through `f₁-⋯-fk`.  This file isolates those graph-theoretic arguments from cyclic-index
bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm162ClaimFourTracks

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem singleton_path (G : SimpleGraph V) (x : V) : IsPathFrom G [x] x x := by
  exact ⟨PathBasics.isPathList_singleton G x, rfl, rfl⟩

private theorem path_ends_ne {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length) : a ≠ b := by
  intro he
  have h0 : P[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hl : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hi := (List.Nodup.getElem_inj_iff hP.1.2.1).mp (h0.trans (he.trans hl.symm))
  omega

private theorem tail_head?_getElem {W : Type*} {l : List W} (h : 1 < l.length) :
    l.tail.head? = some (l[1]'h) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < l.tail.length by simp; omega)]
  simp

/-- If the head of a path is one end of its unique complete edge, the next path vertex is the
other end. -/
private theorem second_complete_of_pair {G : SimpleGraph V} {Y : Set V}
    {P : List V} {a b c d : V} (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length)
    (hset : {x : V | x ∈ P ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hadj : G.Adj c d) (ha : VertexComplete G a Y) :
    VertexComplete G (P[1]'(by omega)) Y := by
  have haP := (PathBasics.isPathFrom_ends_mem hP).1
  have hc : c ∈ P ∧ VertexComplete G c Y := by
    have hm : c ∈ {x : V | x ∈ P ∧ VertexComplete G x Y} := by
      rw [hset]
      simp
    exact hm
  have hd : d ∈ P ∧ VertexComplete G d Y := by
    have hm : d ∈ {x : V | x ∈ P ∧ VertexComplete G x Y} := by
      rw [hset]
      simp
    exact hm
  have hapair : a = c ∨ a = d := by
    have hm : a ∈ {x : V | x ∈ P ∧ VertexComplete G x Y} := ⟨haP, ha⟩
    rw [hset] at hm
    simpa using hm
  have h0 : P[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  rcases hapair with hac | had
  · obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hd.1
    have h0j : G.Adj (P[0]'(by omega)) (P[j]'hj) := by rw [h0, hac, hje]; exact hadj
    have hij := (PathBasics.path_adj_iff hP.1 (by omega) hj).mp h0j
    have hj1 : j = 1 := by rcases hij with h | h <;> omega
    have he : P[1]'(by omega) = d := by
      exact (HoleArithmetic.getElem_congr_idx P (by omega) hj hj1.symm).trans hje
    rw [he]
    exact hd.2
  · obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hc.1
    have h0j : G.Adj (P[0]'(by omega)) (P[j]'hj) := by rw [h0, had, hje]; exact hadj.symm
    have hij := (PathBasics.path_adj_iff hP.1 (by omega) hj).mp h0j
    have hj1 : j = 1 := by rcases hij with h | h <;> omega
    have he : P[1]'(by omega) = c := by
      exact (HoleArithmetic.getElem_congr_idx P (by omega) hj hj1.symm).trans hje
    rw [he]
    exact hc.2

private theorem penultimate_complete_of_pair {G : SimpleGraph V} {Y : Set V}
    {P : List V} {a b c d : V} (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length)
    (hset : {x : V | x ∈ P ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hadj : G.Adj c d) (hb : VertexComplete G b Y) :
    VertexComplete G (P[P.length - 2]'(by omega)) Y := by
  have hrev := second_complete_of_pair (PathBasics.isPathFrom_reverse hP) (by simpa using hP2)
    (show {x : V | x ∈ P.reverse ∧ VertexComplete G x Y} = {c, d} by
      ext x
      simpa using Set.ext_iff.mp hset x)
    hcd hadj hb
  simpa only [List.getElem_reverse, List.length_reverse] using hrev

private theorem length_two_of_complete_ends {G : SimpleGraph V} {Y : Set V}
    {P : List V} {a b c d : V} (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length)
    (hset : {x : V | x ∈ P ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hadj : G.Adj c d)
    (ha : VertexComplete G a Y) (hb : VertexComplete G b Y) : P.length = 2 := by
  have hab : a ≠ b := path_ends_ne hP hP2
  have ends : ∀ z : V, z = a ∨ z = b → z = c ∨ z = d := by
    intro z hz
    have hzP : z ∈ P := by
      rcases hz with rfl | rfl
      · exact (PathBasics.isPathFrom_ends_mem hP).1
      · exact (PathBasics.isPathFrom_ends_mem hP).2
    have hzC : VertexComplete G z Y := by rcases hz with rfl | rfl <;> assumption
    have hm : z ∈ {x : V | x ∈ P ∧ VertexComplete G x Y} := ⟨hzP, hzC⟩
    rw [hset] at hm
    simpa using hm
  have ha' := ends a (Or.inl rfl)
  have hb' := ends b (Or.inr rfl)
  have habadj : G.Adj a b := by
    rcases ha' with hac | had <;> rcases hb' with hbc | hbd
    · exact absurd (hac.trans hbc.symm) hab
    · simpa only [hac, hbd] using hadj
    · simpa only [had, hbc] using hadj.symm
    · exact absurd (had.trans hbd.symm) hab
  by_contra hn
  have h3 : 3 ≤ P.length := by omega
  exact PathBasics.path_ends_not_adj hP.1 h3 (by
    simpa only [PathBasics.getElem_zero_of_head? hP.2.1 (by omega),
      PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)] using habadj)

private theorem pathFrom_tail {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length) :
    IsPathFrom G P.tail (P[1]'(by omega)) b := by
  have ht : IsPathList G P.tail := by
    simpa only [List.drop_one] using PathBasics.isPathList_drop hP.1 (show 1 < P.length by omega)
  refine ⟨ht, ?_, ?_⟩
  · exact tail_head?_getElem (by omega)
  · rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show P.length - 1 < P.length by omega)]
    exact congrArg some (PathBasics.getElem_last_of_getLast? hP.2.2 (by omega))

private theorem pathFrom_dropLast {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hP2 : 2 ≤ P.length) :
    IsPathFrom G P.dropLast a (P[P.length - 2]'(by omega)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.dropLast_eq_take]
    exact PathBasics.isPathList_take hP.1 (by omega)
  · have h0 : P[0]'(by omega) = a :=
      PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have hh := PathBasics.head?_slice P (i := 0) (j := P.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : P.length - 2 - 0 + 1 = P.length - 1 := by omega
    rw [he] at hh
    simpa [h0] using hh
  · have hl := PathBasics.getLast?_slice P
      (i := 0) (j := P.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : P.length - 2 - 0 + 1 = P.length - 1 := by omega
    rw [he] at hl
    exact hl

private theorem exact_pair_of_two_members {W : Type*} {T : Set W} {c d u v : W}
    (hT : T = {c, d}) (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) : T = {u, v} := by
  rw [hT] at hu hv ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with h | h <;> simp_all [Set.pair_comm]

private theorem start_not_tail {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) : a ∉ P.tail := by
  cases P with
  | nil => intro _; exact hP.1.1 rfl
  | cons x xs =>
      have hx : x = a := by simpa using hP.2.1
      subst x
      exact (List.nodup_cons.mp hP.1.2.1).1

private theorem end_not_dropLast {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) : b ∉ P.dropLast := by
  have h := start_not_tail (PathBasics.isPathFrom_reverse hP)
  simpa only [List.tail_reverse, List.mem_reverse] using h

/-- The two same-side bridges force a long prism.  If only one were present, the two track
parities close it into an odd hole; if neither were present, 15.3 gives the paper's
`nobanister` contradiction. -/
theorem same_side_tracks_false {G : SimpleGraph V} (hG : InF6 G) {Y : Set V}
    (hYanti : AnticonnectedSet G Y)
    {S Q R : List V} {f₁ fk q₁ q₂ r₁ r₂ : V}
    (hS : IsPathFrom G S f₁ fk) (hS2 : 2 ≤ S.length)
    (hQ : IsPathFrom G Q q₁ q₂) (hQ2 : 2 ≤ Q.length)
    (hR : IsPathFrom G R r₁ r₂) (hR2 : 2 ≤ R.length)
    (hSQdisj : ∀ x ∈ S, x ∉ Q) (hSRdisj : ∀ x ∈ S, x ∉ R)
    (hQRdisj : ∀ x ∈ Q, x ∉ R)
    (hSQ : ∀ x ∈ S, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = f₁ ∧ y = q₁) ∨ (x = fk ∧ y = q₂)))
    (hSR : ∀ x ∈ S, ∀ y ∈ R,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁) ∨ (x = fk ∧ y = r₂)))
    (hQR : ∀ x ∈ Q, ∀ y ∈ R,
      (G.Adj x y ↔
        (x = q₁ ∧ y = r₁ ∧ G.Adj q₁ r₁) ∨
        (x = q₂ ∧ y = r₂ ∧ G.Adj q₂ r₂)))
    (hSY : ∀ x ∈ S, x ∉ Y) (hQY : ∀ x ∈ Q, x ∉ Y)
    (hRY : ∀ x ∈ R, x ∉ Y)
    (hSnc : ∀ x ∈ S, ¬ VertexComplete G x Y)
    {c d e g : V}
    (hQc : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hcdadj : G.Adj c d)
    (hRc : {x : V | x ∈ R ∧ VertexComplete G x Y} = {e, g})
    (heg : e ≠ g) (hegadj : G.Adj e g)
    (hQeven : Even (S.length + Q.length)) (hReven : Even (S.length + R.length))
    (hshort : Q.length = 2 → R.length = 2 → S.length = 2 →
      G.Adj q₁ r₁ → G.Adj q₂ r₂ → False) : False := by
  classical
  have hf₁S := (PathBasics.isPathFrom_ends_mem hS).1
  have hfkS := (PathBasics.isPathFrom_ends_mem hS).2
  have hq₁Q := (PathBasics.isPathFrom_ends_mem hQ).1
  have hq₂Q := (PathBasics.isPathFrom_ends_mem hQ).2
  have hr₁R := (PathBasics.isPathFrom_ends_mem hR).1
  have hr₂R := (PathBasics.isPathFrom_ends_mem hR).2
  have hf₁fk : f₁ ≠ fk := by
    intro he
    have h0 : S[0]'(by omega) = f₁ :=
      PathBasics.getElem_zero_of_head? hS.2.1 (by omega)
    have hl : S[S.length - 1]'(by omega) = fk :=
      PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)
    have hi := (List.Nodup.getElem_inj_iff hS.1.2.1).mp (h0.trans (he.trans hl.symm))
    omega
  have hbridge : G.Adj q₁ r₁ ∨ G.Adj q₂ r₂ := by
    by_contra hn
    push Not at hn
    have hanti : ∀ x ∈ Q, ∀ y ∈ R, ¬ G.Adj x y := by
      intro x hx y hy hxy
      rcases (hQR x hx y hy).mp hxy with h | h
      · exact hn.1 h.2.2
      · exact hn.2 h.2.2
    exact Thm162ClaimFourHelpers.no_banister hG hYanti hS hS2 hQ hQ2 hR hR2
      hSQdisj hSRdisj hQRdisj hSQ hSR hanti hSY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj

  have force_other : G.Adj q₁ r₁ → G.Adj q₂ r₂ := by
    intro h11
    by_contra h22
    let A : List V := [fk] ++ Q.reverse
    have hA : IsPathFrom G A fk q₁ := by
      dsimp only [A]
      refine PathGlue.glue_path (singleton_path G fk) (PathBasics.isPathFrom_reverse hQ) ?_ ?_
      · intro x hx hxQ
        have hxf : x = fk := by simpa using hx
        subst x
        exact hSQdisj fk hfkS (List.mem_reverse.mp hxQ)
      · intro x hx y hy
        have hxf : x = fk := by simpa using hx
        subst x
        rw [List.mem_reverse] at hy
        constructor
        · intro hadj
          rcases (hSQ fk hfkS y hy).mp hadj with ⟨he, -⟩ | ⟨-, he⟩
          · exact absurd he.symm hf₁fk
          · exact ⟨rfl, he⟩
        · rintro ⟨-, he⟩
          exact (hSQ fk hfkS y hy).mpr (Or.inr ⟨rfl, he⟩)
    have hARdisj : ∀ x ∈ A, x ∉ R := by
      intro x hx hxR
      rcases List.mem_append.mp hx with hx | hx
      · have hxf : x = fk := by simpa using hx
        subst x
        exact hSRdisj fk hfkS hxR
      · exact hQRdisj x (List.mem_reverse.mp hx) hxR
    have hAR : ∀ x ∈ A, ∀ y ∈ R,
        (G.Adj x y ↔ (x = q₁ ∧ y = r₁) ∨ (x = fk ∧ y = r₂)) := by
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · have hxf : x = fk := by simpa using hx
        subst x
        constructor
        · intro hadj
          rcases (hSR fk hfkS y hy).mp hadj with ⟨he, -⟩ | ⟨-, he⟩
          · exact absurd he.symm hf₁fk
          · exact Or.inr ⟨rfl, he⟩
        · rintro (⟨he, -⟩ | ⟨-, he⟩)
          · exact absurd he (by
              intro hfkq
              exact hSQdisj fk hfkS (by rw [he]; exact hq₁Q))
          · exact (hSR fk hfkS y hy).mpr (Or.inr ⟨rfl, he⟩)
      · have hxQ : x ∈ Q := List.mem_reverse.mp hx
        rw [hQR x hxQ y hy]
        constructor
        · rintro (h | h)
          · exact Or.inl ⟨h.1, h.2.1⟩
          · exact absurd h.2.2 h22
        · rintro (⟨hx1, hy1⟩ | ⟨hxf, -⟩)
          · exact Or.inl ⟨hx1, hy1, h11⟩
          · exfalso
            exact hSQdisj fk hfkS (by rw [← hxf]; exact hxQ)
    have hH : IsHoleList G (A ++ R) :=
      PathGlue.glue_hole hA hR hARdisj hAR (by simp only [A, List.length_append,
        List.length_singleton, List.length_reverse]; omega)
    have heven := hG.1.1.1.1 (A ++ R) hH
    simp only [SPGT.holeLength, A, List.length_append, List.length_singleton,
      List.length_reverse] at heven
    rw [Nat.even_iff] at hQeven hReven heven
    omega
  have force_first : G.Adj q₂ r₂ → G.Adj q₁ r₁ := by
    intro h22
    -- This is the same odd-hole calculation as `force_other`, with endpoint names exchanged.
    by_contra h11
    let A : List V := [f₁] ++ Q
    have hA : IsPathFrom G A f₁ q₂ := by
      dsimp only [A]
      refine PathGlue.glue_path (singleton_path G f₁) hQ ?_ ?_
      · intro x hx hxQ
        have hxf : x = f₁ := by simpa using hx
        subst x
        exact hSQdisj f₁ hf₁S hxQ
      · intro x hx y hy
        have hxf : x = f₁ := by simpa using hx
        subst x
        constructor
        · intro hadj
          rcases (hSQ f₁ hf₁S y hy).mp hadj with ⟨-, he⟩ | ⟨he, -⟩
          · exact ⟨rfl, he⟩
          · exact absurd he hf₁fk
        · rintro ⟨-, he⟩
          exact (hSQ f₁ hf₁S y hy).mpr (Or.inl ⟨rfl, he⟩)
    have hARdisj : ∀ x ∈ A, x ∉ R.reverse := by
      intro x hx hxR
      have hxR' := List.mem_reverse.mp hxR
      rcases List.mem_append.mp hx with hx | hx
      · have hxf : x = f₁ := by simpa using hx
        subst x
        exact hSRdisj f₁ hf₁S hxR'
      · exact hQRdisj x hx hxR'
    have hAR : ∀ x ∈ A, ∀ y ∈ R.reverse,
        (G.Adj x y ↔ (x = q₂ ∧ y = r₂) ∨ (x = f₁ ∧ y = r₁)) := by
      intro x hx y hy
      have hyR := List.mem_reverse.mp hy
      rcases List.mem_append.mp hx with hx | hx
      · have hxf : x = f₁ := by simpa using hx
        subst x
        constructor
        · intro hadj
          rcases (hSR f₁ hf₁S y hyR).mp hadj with ⟨-, he⟩ | ⟨he, -⟩
          · exact Or.inr ⟨rfl, he⟩
          · exact absurd he hf₁fk
        · rintro (⟨he, -⟩ | ⟨-, he⟩)
          · exfalso
            exact hSQdisj f₁ hf₁S (by rw [he]; exact hq₂Q)
          · exact (hSR f₁ hf₁S y hyR).mpr (Or.inl ⟨rfl, he⟩)
      · rw [hQR x hx y hyR]
        constructor
        · rintro (hh | hh)
          · exact absurd hh.2.2 h11
          · exact Or.inl ⟨hh.1, hh.2.1⟩
        · rintro (⟨hx2, hy2⟩ | ⟨hxf, -⟩)
          · exact Or.inr ⟨hx2, hy2, h22⟩
          · exfalso
            exact hSQdisj f₁ hf₁S (by rw [← hxf]; exact hx)
    have hH : IsHoleList G (A ++ R.reverse) :=
      PathGlue.glue_hole hA (PathBasics.isPathFrom_reverse hR) hARdisj hAR (by
        simp only [A, List.length_append, List.length_singleton, List.length_reverse]
        omega)
    have heven := hG.1.1.1.1 (A ++ R.reverse) hH
    simp only [SPGT.holeLength, A, List.length_append, List.length_singleton,
      List.length_reverse] at heven
    rw [Nat.even_iff] at hQeven hReven heven
    omega

  have h11 : G.Adj q₁ r₁ := by
    rcases hbridge with h11 | h22
    · exact h11
    · exact force_first h22
  have h22 : G.Adj q₂ r₂ := force_other h11
  have hqne : q₁ ≠ q₂ := by
    intro he
    have h0 : Q[0]'(by omega) = q₁ :=
      PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hl : Q[Q.length - 1]'(by omega) = q₂ :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
    have hi := (List.Nodup.getElem_inj_iff hQ.1.2.1).mp (h0.trans (he.trans hl.symm))
    omega
  have hrne : r₁ ≠ r₂ := by
    intro he
    have h0 : R[0]'(by omega) = r₁ :=
      PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
    have hl : R[R.length - 1]'(by omega) = r₂ :=
      PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
    have hi := (List.Nodup.getElem_inj_iff hR.1.2.1).mp (h0.trans (he.trans hl.symm))
    omega
  have hQRfull : ∀ x ∈ Q, ∀ y ∈ R,
      (G.Adj x y ↔ (x = q₁ ∧ y = r₁) ∨ (x = q₂ ∧ y = r₂)) := by
    intro x hx y hy
    rw [hQR x hx y hy]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.1⟩
    · rintro (h | h)
      · exact Or.inl ⟨h.1, h.2, h11⟩
      · exact Or.inr ⟨h.1, h.2, h22⟩
  have hform := PrismBasics.formPrism_of_data
    ((hSQ f₁ hf₁S q₁ hq₁Q).mpr (Or.inl ⟨rfl, rfl⟩))
    ((hSR f₁ hf₁S r₁ hr₁R).mpr (Or.inl ⟨rfl, rfl⟩)) h11
    ((hSQ fk hfkS q₂ hq₂Q).mpr (Or.inr ⟨rfl, rfl⟩))
    ((hSR fk hfkS r₂ hr₂R).mpr (Or.inr ⟨rfl, rfl⟩)) h22
    (fun he => hf₁fk he)
    (fun he => hSQdisj f₁ hf₁S (he ▸ hq₂Q))
    (fun he => hSRdisj f₁ hf₁S (he ▸ hr₂R))
    (fun he => hSQdisj fk hfkS (he.symm ▸ hq₁Q))
    hqne
    (fun he => hQRdisj q₁ hq₁Q (he ▸ hr₂R))
    (fun he => hSRdisj fk hfkS (by rw [← he]; exact hr₁R))
    (fun he => hQRdisj q₂ hq₂Q (by rw [← he]; exact hr₁R))
    hrne
    hS hQ hR hSQ hSR hQRfull
  have hlong : 1 < pathLength S ∨ 1 < pathLength Q ∨ 1 < pathLength R := by
    by_contra hn
    push Not at hn
    have hsL := PathBasics.pathLength_eq S
    have hqL := PathBasics.pathLength_eq Q
    have hrL := PathBasics.pathLength_eq R
    exact hshort (by omega) (by omega) (by omega) h11 h22
  exact hG.1.2.1 (PrismBasics.exists_isLongPrism_of_formPrism hform hlong)

/-- The crossed-bridge case, in the orientation in which `q₁r₂` is present.  The short
holes force both tracks to have odd edge length and `S` to have even vertex length.  Deleting
the complete outer ends gives the odd path used in 13.6; its forced length three reduces to
the four-vertex path used in 2.2. -/
theorem opposite_tracks_oriented_false {G : SimpleGraph V} (hG : InF6 G) {Y : Set V}
    (hYanti : AnticonnectedSet G Y)
    {S Q R : List V} {f₁ fk q₁ q₂ r₁ r₂ : V}
    (hS : IsPathFrom G S f₁ fk) (hS2 : 2 ≤ S.length)
    (hQ : IsPathFrom G Q q₁ q₂) (hQ2 : 2 ≤ Q.length)
    (hR : IsPathFrom G R r₁ r₂) (hR2 : 2 ≤ R.length)
    (hSQdisj : ∀ x ∈ S, x ∉ Q) (hSRdisj : ∀ x ∈ S, x ∉ R)
    (hQRdisj : ∀ x ∈ Q, x ∉ R)
    (hSQ : ∀ x ∈ S, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = f₁ ∧ y = q₁) ∨ (x = fk ∧ y = q₂)))
    (hSR : ∀ x ∈ S, ∀ y ∈ R,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁) ∨ (x = fk ∧ y = r₂)))
    (hQR : ∀ x ∈ Q, ∀ y ∈ R,
      (G.Adj x y ↔
        (x = q₁ ∧ y = r₂ ∧ G.Adj q₁ r₂) ∨
        (x = q₂ ∧ y = r₁ ∧ G.Adj q₂ r₁)))
    (hSY : ∀ x ∈ S, x ∉ Y) (hQY : ∀ x ∈ Q, x ∉ Y)
    (hRY : ∀ x ∈ R, x ∉ Y)
    (hSnc : ∀ x ∈ S, ¬ VertexComplete G x Y)
    {c d e g : V}
    (hQc : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hcdadj : G.Adj c d)
    (hRc : {x : V | x ∈ R ∧ VertexComplete G x Y} = {e, g})
    (heg : e ≠ g) (hegadj : G.Adj e g)
    (hQeven : Even (S.length + Q.length))
    (h12 : G.Adj q₁ r₂)
    (h12complete : G.Adj q₁ r₂ →
      VertexComplete G q₁ Y ∧ VertexComplete G r₂ Y)
    (h21complete : G.Adj q₂ r₁ →
      VertexComplete G q₂ Y ∧ VertexComplete G r₁ Y)
    (hshort : Q.length = 2 → R.length = 2 →
      G.Adj q₁ r₂ → G.Adj q₂ r₁ → False)
    (hfinal : S.length = 2 → (∀ w : V, VertexComplete G w Y →
      ∃ z ∈ ([f₁, fk] : List V), G.Adj w z) → False) : False := by
  classical
  have hf₁S := (PathBasics.isPathFrom_ends_mem hS).1
  have hfkS := (PathBasics.isPathFrom_ends_mem hS).2
  have hq₁Q := (PathBasics.isPathFrom_ends_mem hQ).1
  have hq₂Q := (PathBasics.isPathFrom_ends_mem hQ).2
  have hr₁R := (PathBasics.isPathFrom_ends_mem hR).1
  have hr₂R := (PathBasics.isPathFrom_ends_mem hR).2
  have hfne : f₁ ≠ fk := path_ends_ne hS hS2
  have hqne : q₁ ≠ q₂ := path_ends_ne hQ hQ2
  have hrne : r₁ ≠ r₂ := path_ends_ne hR hR2
  obtain ⟨hq₁c, hr₂c⟩ := h12complete h12
  have h21 : ¬ G.Adj q₂ r₁ := by
    intro h21
    obtain ⟨hq₂c, hr₁c⟩ := h21complete h21
    have hQlen : Q.length = 2 :=
      length_two_of_complete_ends hQ hQ2 hQc hcd hcdadj hq₁c hq₂c
    have hRlen : R.length = 2 :=
      length_two_of_complete_ends hR hR2 hRc heg hegadj hr₁c hr₂c
    exact hshort hQlen hRlen h12 h21
  have hq'c : VertexComplete G (Q[1]'(by omega)) Y :=
    second_complete_of_pair hQ hQ2 hQc hcd hcdadj hq₁c
  have hr'c : VertexComplete G (R[R.length - 2]'(by omega)) Y :=
    penultimate_complete_of_pair hR hR2 hRc heg hegadj hr₂c
  have hq₁notTail : q₁ ∉ Q.tail := start_not_tail hQ
  have hr₂notDrop : r₂ ∉ R.dropLast := end_not_dropLast hR

  -- The hole `r₂-fk-q₂-Q-q₁-r₂` makes `Q` have even vertex length.
  let AQ : List V := [r₂, fk]
  have hAQ : IsPathFrom G AQ r₂ fk := by
    refine ⟨PathBasics.isPathList_pair ?_, rfl, rfl⟩
    exact ((hSR fk hfkS r₂ hr₂R).mpr (Or.inr ⟨rfl, rfl⟩)).symm
  have hAQdisj : ∀ x ∈ AQ, x ∉ Q.reverse := by
    intro x hx hxQ
    have hxQ' := List.mem_reverse.mp hxQ
    simp only [AQ, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · exact hQRdisj x hxQ' (hx.symm ▸ hr₂R)
    · exact hSQdisj x (by rw [hx]; exact hfkS) hxQ'
  have hAQcross : ∀ x ∈ AQ, ∀ y ∈ Q.reverse,
      (G.Adj x y ↔ (x = fk ∧ y = q₂) ∨ (x = r₂ ∧ y = q₁)) := by
    intro x hx y hy
    have hyQ := List.mem_reverse.mp hy
    simp only [AQ, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hxr | hxf
    · subst x
      rw [SimpleGraph.adj_comm, hQR y hyQ r₂ hr₂R]
      constructor
      · rintro (hh | hh)
        · exact Or.inr ⟨rfl, hh.1⟩
        · exact absurd hh.2.2 h21
      · rintro (⟨he, -⟩ | ⟨-, he⟩)
        · exfalso
          exact hSRdisj fk hfkS (by rw [← he]; exact hr₂R)
        · exact Or.inl ⟨he, rfl, h12⟩
    · subst x
      rw [hSQ fk hfkS y hyQ]
      constructor
      · rintro (⟨he, -⟩ | ⟨-, he⟩)
        · exact absurd he.symm hfne
        · exact Or.inl ⟨rfl, he⟩
      · rintro (⟨-, he⟩ | ⟨he, -⟩)
        · exact Or.inr ⟨rfl, he⟩
        · exfalso
          exact hSRdisj fk hfkS (by rw [he]; exact hr₂R)
  have hHQ : IsHoleList G (AQ ++ Q.reverse) :=
    PathGlue.glue_hole hAQ (PathBasics.isPathFrom_reverse hQ) hAQdisj hAQcross
      (by simp only [AQ, List.length_cons, List.length_nil, List.length_reverse]; omega)
  have hQpar := hG.1.1.1.1 (AQ ++ Q.reverse) hHQ
  simp only [SPGT.holeLength, AQ, List.length_append, List.length_cons, List.length_nil,
    List.length_reverse] at hQpar
  rw [Nat.even_iff] at hQpar

  -- Symmetrically `q₁-f₁-r₁-R-r₂-q₁` makes `R` have even vertex length.
  let AR : List V := [q₁, f₁]
  have hAR : IsPathFrom G AR q₁ f₁ := by
    refine ⟨PathBasics.isPathList_pair ?_, rfl, rfl⟩
    exact ((hSQ f₁ hf₁S q₁ hq₁Q).mpr (Or.inl ⟨rfl, rfl⟩)).symm
  have hARdisj : ∀ x ∈ AR, x ∉ R := by
    intro x hx hxR
    simp only [AR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · exact hQRdisj x (by rw [hx]; exact hq₁Q) hxR
    · exact hSRdisj x (by rw [hx]; exact hf₁S) hxR
  have hARcross : ∀ x ∈ AR, ∀ y ∈ R,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁) ∨ (x = q₁ ∧ y = r₂)) := by
    intro x hx y hy
    simp only [AR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hxq | hxf
    · subst x
      rw [hQR q₁ hq₁Q y hy]
      constructor
      · rintro (hh | hh)
        · exact Or.inr ⟨rfl, hh.2.1⟩
        · exact absurd hh.2.2 h21
      · rintro (⟨he, -⟩ | ⟨-, he⟩)
        · exfalso
          exact hSQdisj f₁ hf₁S (he.symm ▸ hq₁Q)
        · exact Or.inl ⟨rfl, he, h12⟩
    · subst x
      rw [hSR f₁ hf₁S y hy]
      constructor
      · rintro (⟨-, he⟩ | ⟨he, -⟩)
        · exact Or.inl ⟨rfl, he⟩
        · exact absurd he hfne
      · rintro (⟨-, he⟩ | ⟨he, -⟩)
        · exact Or.inl ⟨rfl, he⟩
        · exfalso
          exact hSQdisj f₁ hf₁S (by rw [he]; exact hq₁Q)
  have hHR : IsHoleList G (AR ++ R) :=
    PathGlue.glue_hole hAR hR hARdisj hARcross
      (by simp only [AR, List.length_cons, List.length_nil]; omega)
  have hRpar := hG.1.1.1.1 (AR ++ R) hHR
  simp only [SPGT.holeLength, AR, List.length_append, List.length_cons, List.length_nil] at hRpar
  rw [Nat.even_iff] at hRpar hQeven
  have hSeven : Even S.length := by
    rw [Nat.even_iff]
    omega

  -- Delete `q₁` and `r₂`, then join the three remaining tracks.
  have hQt := pathFrom_tail hQ hQ2
  have hRd := pathFrom_dropLast hR hR2
  have hq'Tail : Q[1]'(by omega) ∈ Q.tail := (PathBasics.isPathFrom_ends_mem hQt).1
  have hr'Drop : R[R.length - 2]'(by omega) ∈ R.dropLast :=
    (PathBasics.isPathFrom_ends_mem hRd).2
  let U : List V := Q.tail ++ S.reverse
  have hUS : IsPathFrom G U (Q[1]'(by omega)) f₁ := by
    dsimp only [U]
    refine PathGlue.glue_path hQt (PathBasics.isPathFrom_reverse hS) ?_ ?_
    · intro x hxQ hxS
      exact hSQdisj x (List.mem_reverse.mp hxS) (List.mem_of_mem_tail hxQ)
    · intro x hxQ y hyS
      have hxQ' := List.mem_of_mem_tail hxQ
      have hyS' := List.mem_reverse.mp hyS
      rw [SimpleGraph.adj_comm, hSQ y hyS' x hxQ']
      constructor
      · rintro (⟨hy, hx⟩ | ⟨hy, hx⟩)
        · exfalso
          exact hq₁notTail (by rw [← hx]; exact hxQ)
        · exact ⟨hx, hy⟩
      · rintro ⟨hx, hy⟩
        exact Or.inr ⟨hy, hx⟩
  have hURdisj : ∀ x ∈ U, x ∉ R.dropLast := by
    intro x hx hxR
    rcases List.mem_append.mp hx with hxQ | hxS
    · exact hQRdisj x (List.mem_of_mem_tail hxQ) (List.mem_of_mem_dropLast hxR)
    · exact hSRdisj x (List.mem_reverse.mp hxS) (List.mem_of_mem_dropLast hxR)
  have hUR : ∀ x ∈ U, ∀ y ∈ R.dropLast,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁)) := by
    intro x hx y hy
    have hyR := List.mem_of_mem_dropLast hy
    rcases List.mem_append.mp hx with hxQ | hxS
    · have hxQ' := List.mem_of_mem_tail hxQ
      rw [hQR x hxQ' y hyR]
      constructor
      · rintro (hh | hh)
        · exfalso
          exact hr₂notDrop (by rw [← hh.2.1]; exact hy)
        · exact absurd hh.2.2 h21
      · rintro ⟨hxf, -⟩
        exfalso
        exact hSQdisj f₁ hf₁S (by rw [← hxf]; exact hxQ')
    · have hxS := List.mem_reverse.mp hxS
      rw [hSR x hxS y hyR]
      constructor
      · rintro (⟨hxf, hyr⟩ | ⟨-, hyr⟩)
        · exact ⟨hxf, hyr⟩
        · exfalso
          exact hr₂notDrop (by rw [← hyr]; exact hy)
      · rintro ⟨hxf, hyr⟩
        exact Or.inl ⟨hxf, hyr⟩
  let W : List V := U ++ R.dropLast
  have hW : IsPathFrom G W (Q[1]'(by omega)) (R[R.length - 2]'(by omega)) := by
    dsimp only [W]
    exact PathGlue.glue_path hUS hRd hURdisj hUR
  have hWlen : W.length = (Q.length - 1) + S.length + (R.length - 1) := by
    simp only [W, U, List.length_append, List.length_tail, List.length_reverse,
      List.length_dropLast]
  have hWodd : Odd (pathLength W) := by
    rw [PathBasics.pathLength_eq, hWlen, Nat.odd_iff]
    omega
  have hWY : ∀ x ∈ W, x ∉ Y := by
    intro x hx
    rcases List.mem_append.mp hx with hxU | hxR
    · rcases List.mem_append.mp hxU with hxQ | hxS
      · exact hQY x (List.mem_of_mem_tail hxQ)
      · exact hSY x (List.mem_reverse.mp hxS)
    · exact hRY x (List.mem_of_mem_dropLast hxR)
  have hQpair : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {q₁, Q[1]'(by omega)} :=
    exact_pair_of_two_members hQc ⟨hq₁Q, hq₁c⟩
      ⟨List.getElem_mem (by omega), hq'c⟩ (by
        intro he
        exact hq₁notTail (by rw [he]; exact hq'Tail))
  have hRpair : {x : V | x ∈ R ∧ VertexComplete G x Y} =
      {R[R.length - 2]'(by omega), r₂} :=
    exact_pair_of_two_members hRc
      ⟨List.getElem_mem (by omega), hr'c⟩ ⟨hr₂R, hr₂c⟩ (by
        intro he
        exact hr₂notDrop (by rw [← he]; exact hr'Drop))
  have hWends : ∀ x ∈ W, VertexComplete G x Y →
      x = Q[1]'(by omega) ∨ x = R[R.length - 2]'(by omega) := by
    intro x hx hxc
    rcases List.mem_append.mp hx with hxU | hxR
    · rcases List.mem_append.mp hxU with hxQ | hxS
      · have hm : x ∈ {z : V | z ∈ Q ∧ VertexComplete G z Y} :=
          ⟨List.mem_of_mem_tail hxQ, hxc⟩
        rw [hQpair] at hm
        have hp : x = q₁ ∨ x = Q[1]'(by omega) := by simpa using hm
        rcases hp with rfl | he
        · exact absurd hxQ hq₁notTail
        · exact Or.inl he
      · exact absurd hxc (hSnc x (List.mem_reverse.mp hxS))
    · have hm : x ∈ {z : V | z ∈ R ∧ VertexComplete G z Y} :=
        ⟨List.mem_of_mem_dropLast hxR, hxc⟩
      rw [hRpair] at hm
      have hp : x = R[R.length - 2]'(by omega) ∨ x = r₂ := by simpa using hm
      rcases hp with he | rfl
      · exact Or.inr he
      · exact absurd hxR hr₂notDrop
  have hXW : Y ⊆ {x : V | x ∈ W}ᶜ := fun y hy hyW => hWY y hyW hy
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1 W
      (Q[1]'(by omega)) (R[R.length - 2]'(by omega)) hW hWodd Y hXW hYanti hq'c hr'c with
    hedge | hlen3
  · obtain ⟨u, hu, v, hv, huv, huc, hvc⟩ := hedge
    rcases hWends u hu huc with huq | hur <;> rcases hWends v hv hvc with hvq | hvr
    · have hloop : G.Adj (Q[1]'(by omega)) (Q[1]'(by omega)) := by
        simpa [huq, hvq] using huv
      exact G.irrefl hloop
    · have hqQ : Q[1]'(by omega) ∈ Q := List.getElem_mem _
      have hrR : R[R.length - 2]'(by omega) ∈ R := List.getElem_mem _
      rcases (hQR _ hqQ _ hrR).mp (by simpa [huq, hvr] using huv) with hh | hh
      · exact hr₂notDrop (by rw [← hh.2.1]; exact hr'Drop)
      · exact h21 hh.2.2
    · have hqQ : Q[1]'(by omega) ∈ Q := List.getElem_mem _
      have hrR : R[R.length - 2]'(by omega) ∈ R := List.getElem_mem _
      rcases (hQR _ hqQ _ hrR).mp (by simpa [hur, hvq] using huv.symm) with hh | hh
      · exact hr₂notDrop (by rw [← hh.2.1]; exact hr'Drop)
      · exact h21 hh.2.2
    · have hloop : G.Adj (R[R.length - 2]'(by omega))
          (R[R.length - 2]'(by omega)) := by
        simpa [hur, hvr] using huv
      exact G.irrefl hloop
  have hW3 := hlen3.1
  rw [PathBasics.pathLength_eq, hWlen] at hW3
  have hQlen : Q.length = 2 := by omega
  have hRlen : R.length = 2 := by omega
  have hSlen : S.length = 2 := by omega
  have hSe : S = [f₁, fk] := by
    obtain ⟨a, b, hab⟩ := PathGlue.length_eq_two hSlen
    subst S
    have ha : a = f₁ := by simpa using hS.2.1
    have hb : b = fk := by simpa using hS.2.2
    simp [ha, hb]
  have hq2c : VertexComplete G q₂ Y := by
    have he : Q[1]'(by omega) = q₂ := by
      have hl := PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
      exact (HoleArithmetic.getElem_congr_idx Q (by omega) (by omega) (by omega)).trans hl
    rwa [← he]
  have hr1c : VertexComplete G r₁ Y := by
    have he : R[R.length - 2]'(by omega) = r₁ := by
      have h0 := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
      exact (HoleArithmetic.getElem_congr_idx R (by omega) (by omega) (by omega)).trans h0
    rwa [← he]

  -- The final four-vertex odd path is exactly the one to which the paper applies 2.2.
  let T : List V := [r₁, f₁, fk, q₂]
  have hr₁f₁ : G.Adj r₁ f₁ :=
    ((hSR f₁ hf₁S r₁ hr₁R).mpr (Or.inl ⟨rfl, rfl⟩)).symm
  have hf₁fk : G.Adj f₁ fk := PathBasics.isPathFrom_ends_adj_of_length_one hS (by
    rw [PathBasics.pathLength_eq, hSlen])
  have hfkq₂ : G.Adj fk q₂ := (hSQ fk hfkS q₂ hq₂Q).mpr (Or.inr ⟨rfl, rfl⟩)
  have hr₁fk : ¬ G.Adj r₁ fk := by
    intro ha
    rcases (hSR fk hfkS r₁ hr₁R).mp ha.symm with hh | hh
    · exact hfne hh.1.symm
    · exact hrne hh.2
  have hf₁q₂ : ¬ G.Adj f₁ q₂ := by
    intro ha
    rcases (hSQ f₁ hf₁S q₂ hq₂Q).mp ha with hh | hh
    · exact hqne hh.2.symm
    · exact hfne hh.1
  have hTpath : IsPathFrom G T r₁ q₂ := by
    refine ⟨PathGlue.isPathList_four ?_ hr₁f₁ hf₁fk hfkq₂ hr₁fk
      (fun ha => h21 ha.symm)
      hf₁q₂, rfl, rfl⟩
    dsimp only [T]
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, List.nodup_singleton _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (he | he | he)
      · exact hSRdisj f₁ hf₁S (by rw [← he]; exact hr₁R)
      · exact hSRdisj fk hfkS (by rw [← he]; exact hr₁R)
      · exact hQRdisj q₂ hq₂Q (by rw [← he]; exact hr₁R)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (he | he)
      · exact hfne he
      · exact hSQdisj f₁ hf₁S (by rw [he]; exact hq₂Q)
    · simp only [List.mem_singleton]
      intro he
      exact hSQdisj fk hfkS (by rw [he]; exact hq₂Q)
  have hTY : ∀ x ∈ T, x ∉ Y := by
    intro x hx
    simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact hRY r₁ hr₁R
    · rw [hx]; exact hSY f₁ hf₁S
    · rw [hx]; exact hSY fk hfkS
    · rw [hx]; exact hQY q₂ hq₂Q
  have hTnoedge : ¬ ∃ u ∈ T, ∃ v ∈ T, EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, huv⟩
    have ends : ∀ z ∈ T, VertexComplete G z Y → z = r₁ ∨ z = q₂ := by
      intro z hz hzc
      simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz | hz | hz
      · exact Or.inl hz
      · exact absurd (hz ▸ hzc) (hSnc f₁ hf₁S)
      · exact absurd (hz ▸ hzc) (hSnc fk hfkS)
      · exact Or.inr hz
    rcases ends u hu huv.2.1 with rfl | rfl <;> rcases ends v hv huv.2.2 with rfl | rfl
    · exact G.irrefl huv.1
    · exact h21 huv.1.symm
    · exact h21 huv.1
    · exact G.irrefl huv.1
  have hTresult := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hG.1.1.1 Y hYanti T r₁ q₂
    hTpath hTY (by simp only [T, pathLength]; exact ⟨1, rfl⟩) hr1c hq2c hTnoedge
  apply hfinal hSlen
  intro w hwc
  obtain ⟨z, hz, hwz⟩ := hTresult w hwc
  have hz' : z ∈ ([f₁, fk] : List V) := by simpa [T, SPGT.interior] using hz
  exact ⟨z, hz', hwz⟩

/-- The orientation-independent crossed-bridge argument.  If neither possible bridge exists,
the three tracks form the forbidden banister configuration.  Otherwise reverse the roles of
the two rim tracks, if necessary, and apply `opposite_tracks_oriented_false`. -/
theorem opposite_tracks_false {G : SimpleGraph V} (hG : InF6 G) {Y : Set V}
    (hYanti : AnticonnectedSet G Y)
    {S Q R : List V} {f₁ fk q₁ q₂ r₁ r₂ : V}
    (hS : IsPathFrom G S f₁ fk) (hS2 : 2 ≤ S.length)
    (hQ : IsPathFrom G Q q₁ q₂) (hQ2 : 2 ≤ Q.length)
    (hR : IsPathFrom G R r₁ r₂) (hR2 : 2 ≤ R.length)
    (hSQdisj : ∀ x ∈ S, x ∉ Q) (hSRdisj : ∀ x ∈ S, x ∉ R)
    (hQRdisj : ∀ x ∈ Q, x ∉ R)
    (hSQ : ∀ x ∈ S, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = f₁ ∧ y = q₁) ∨ (x = fk ∧ y = q₂)))
    (hSR : ∀ x ∈ S, ∀ y ∈ R,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁) ∨ (x = fk ∧ y = r₂)))
    (hQR : ∀ x ∈ Q, ∀ y ∈ R,
      (G.Adj x y ↔
        (x = q₁ ∧ y = r₂ ∧ G.Adj q₁ r₂) ∨
        (x = q₂ ∧ y = r₁ ∧ G.Adj q₂ r₁)))
    (hSY : ∀ x ∈ S, x ∉ Y) (hQY : ∀ x ∈ Q, x ∉ Y)
    (hRY : ∀ x ∈ R, x ∉ Y)
    (hSnc : ∀ x ∈ S, ¬ VertexComplete G x Y)
    {c d e g : V}
    (hQc : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hcdadj : G.Adj c d)
    (hRc : {x : V | x ∈ R ∧ VertexComplete G x Y} = {e, g})
    (heg : e ≠ g) (hegadj : G.Adj e g)
    (hQeven : Even (S.length + Q.length))
    (hReven : Even (S.length + R.length))
    (h12complete : G.Adj q₁ r₂ →
      VertexComplete G q₁ Y ∧ VertexComplete G r₂ Y)
    (h21complete : G.Adj q₂ r₁ →
      VertexComplete G q₂ Y ∧ VertexComplete G r₁ Y)
    (hshort : Q.length = 2 → R.length = 2 →
      G.Adj q₁ r₂ → G.Adj q₂ r₁ → False)
    (hfinal : S.length = 2 → (∀ w : V, VertexComplete G w Y →
      ∃ z ∈ ([f₁, fk] : List V), G.Adj w z) → False) : False := by
  classical
  by_cases h12 : G.Adj q₁ r₂
  · exact opposite_tracks_oriented_false hG hYanti hS hS2 hQ hQ2 hR hR2
      hSQdisj hSRdisj hQRdisj hSQ hSR hQR hSY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj hQeven h12 h12complete h21complete hshort hfinal
  by_cases h21 : G.Adj q₂ r₁
  · have hRQdisj : ∀ x ∈ R, x ∉ Q := by
      intro x hxR hxQ
      exact hQRdisj x hxQ hxR
    have hRQ : ∀ x ∈ R, ∀ y ∈ Q,
        (G.Adj x y ↔
          (x = r₁ ∧ y = q₂ ∧ G.Adj r₁ q₂) ∨
          (x = r₂ ∧ y = q₁ ∧ G.Adj r₂ q₁)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hQR y hy x hx]
      constructor
      · rintro (hh | hh)
        · exact Or.inr ⟨hh.2.1, hh.1, hh.2.2.symm⟩
        · exact Or.inl ⟨hh.2.1, hh.1, hh.2.2.symm⟩
      · rintro (hh | hh)
        · exact Or.inr ⟨hh.2.1, hh.1, hh.2.2.symm⟩
        · exact Or.inl ⟨hh.2.1, hh.1, hh.2.2.symm⟩
    exact opposite_tracks_oriented_false hG hYanti hS hS2 hR hR2 hQ hQ2
      hSRdisj hSQdisj hRQdisj hSR hSQ hRQ hSY hRY hQY hSnc
      hRc heg hegadj hQc hcd hcdadj hReven h21.symm
      (fun ha =>
        have hh := h21complete ha.symm
        ⟨hh.2, hh.1⟩)
      (fun ha =>
        have hh := h12complete ha.symm
        ⟨hh.2, hh.1⟩)
      (fun hRlen hQlen hrq hqr => hshort hQlen hRlen hqr.symm hrq.symm)
      hfinal
  · have hanti : ∀ x ∈ Q, ∀ y ∈ R, ¬ G.Adj x y := by
      intro x hx y hy hxy
      rcases (hQR x hx y hy).mp hxy with hh | hh
      · exact h12 hh.2.2
      · exact h21 hh.2.2
    exact Thm162ClaimFourHelpers.no_banister hG hYanti hS hS2 hQ hQ2 hR hR2
      hSQdisj hSRdisj hQRdisj hSQ hSR hanti hSY hQY hRY hSnc
      hQc hcd hcdadj hRc heg hegadj

end Workspace.ProofLemmas.Thm162ClaimFourTracks
