import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim10
import Workspace.ProofLemmas.Thm192Claim11
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S15.Thm_15_7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim12

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Two small tools used by the printed argument -/

/-- *"contrary to 15.7"*: a hole and an antihole, both of length `> 4`, cannot share three
distinct vertices. -/
private theorem three_common {G : SimpleGraph V} (hG : InF6 G) {C D : List V}
    (hC : IsHoleList G C) (hCl : 4 < holeLength C)
    (hD : IsAntiholeList G D) (hDl : 4 < holeLength D)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haC : a ∈ C) (hbC : b ∈ C) (hcC : c ∈ C)
    (haD : a ∈ D) (hbD : b ∈ D) (hcD : c ∈ D) : False := by
  have h := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hG C D hC hCl hD hDl
  have hsub : ({a, b, c} : Set V) ⊆ {w : V | w ∈ C} ∩ {w : V | w ∈ D} := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨haC, haD⟩
    · exact ⟨hbC, hbD⟩
    · exact ⟨hcC, hcD⟩
  have h3 : ({a, b, c} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- In an anticonnected set, a vertex with another vertex beside it has a **non**neighbour
inside the set (the first step of an antipath out of it). -/
private theorem exists_nonneighbour_of_anticonnected {G : SimpleGraph V} {S : Set V}
    (hS : AnticonnectedSet G S) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : v ≠ u) :
    ∃ w ∈ S, w ≠ u ∧ ¬ G.Adj u w := by
  have key : ∀ (a b : ↥S), (Gᶜ.induce S).Walk a b → (a : V) = u → (b : V) ≠ u →
      ∃ w ∈ S, w ≠ u ∧ ¬ G.Adj u w := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact absurd ha hb
    | @cons a' c' b' h q ih =>
        intro ha hb
        have h' : Gᶜ.Adj (a' : V) (c' : V) := h
        rw [ha] at h'
        have hcompl : u ≠ (c' : V) ∧ ¬ G.Adj u (c' : V) := by
          simpa [SimpleGraph.compl_adj] using h'
        exact ⟨(c' : V), c'.2, fun hc => hcompl.1 hc.symm, hcompl.2⟩
  exact (hS ⟨u, hu⟩ ⟨v, hv⟩).elim (fun p => key _ _ p rfl huv)

/-- Claim **(12)** of the printed proof: *"`y` is nonadjacent to all of
`q₁,…,q_{k−1}`."*

`hcex` (the minimum-counterexample hypothesis `¬ Concl192 G z A₀ x Y`) is a **pass-through**
here: the printed argument of (12) itself never makes the *"otherwise `(C,Y)` satisfies
19.2"* move — it uses (10), (11), 13.6 and 15.7 only.  But (10) and (11) each invoke claim
(4)'s second conjunct, which does need `hcex`, so (12) must supply it at those two call
sites. -/
theorem claim12 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (f₁ : V) (hf₁A : f₁ ∈ A) (hf₁adj : G.Adj (x 1) f₁)
    (hf₁uniq : ∀ a ∈ A, G.Adj (x 1) a → a = f₁)
    (hx2noP : ∀ w ∈ SPGT.interior P, ¬ G.Adj (x 2) w) (hff₁ : f ≠ f₁)
    (Q : List V) (hQ : IsPathFrom G Q f f₁) (hQA : ∀ w ∈ Q, w ∈ A)
    (hC₁ : IsHoleList G (z :: x 2 :: (Q ++ [x 1]))) :
    ∀ (i : ℕ) (hi : i + 1 < Q.length), ¬ G.Adj y (Q[i]'(by omega)) := by
  classical
  have hInF6 : InF6 G := hG.1
  have hInF5 : InF5 G := hG.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  -- `z` is adjacent to each `xⱼ`, and neither `z` nor any `xⱼ` nor any vertex of `Y`
  -- lies in `A₁`.
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hxA1 : ∀ j : ℕ, j ≤ 2 → x j ∉ wheelSystemA G z A₀ x 1 := fun j hj h =>
    Thm192Setup.wheelSystemA_no_z _ h (hzx j hj)
  have hzA1 : z ∉ wheelSystemA G z A₀ x 1 := by
    intro h
    refine Thm192Setup.wheelSystemA_no_complete _ h ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hzx 0 (by omega)
    · exact hzx 1 (by omega)
  have hYA1 : ∀ w ∈ Y, w ∉ wheelSystemA G z A₀ x 1 := by
    intro w hw h
    refine Thm192Setup.wheelSystemA_no_complete _ h ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact (hHyp.2.2.1 w hw).symm
    · exact (hHyp.2.2.2.1 w hw).symm
  obtain ⟨hyz', hyx0, hyx1, hyx2⟩ := hHyp.1 y hyY
  -- claims (10) and (11)
  obtain ⟨hx2x0, hx2x1⟩ := Thm192Claim10.claim10 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
    hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
  obtain ⟨hznotY0, hx2Y0, hx2ny⟩ := Thm192Claim11.claim11 G hG z A₀ hframe x hws Y hHyp ih y
    hyY hyz hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
    f₁ hf₁A hf₁adj hf₁uniq hx2noP hff₁ Q hQ hQA hC₁
  -- `Y₀` is nonempty and anticonnected, and `z` has a nonneighbour in it
  have hY0ne : (Y \ {y}).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    refine hznotY0 ?_
    intro w hw
    rw [hc] at hw
    exact absurd hw (Set.notMem_empty w)
  have hY0anti : AnticonnectedSet G (Y \ {y}) := by
    rcases hY0 with h | h
    · exact absurd h (Set.nonempty_iff_ne_empty.mp hY0ne)
    · exact h
  have hzNon : ∃ w ∈ Y \ {y}, ¬ G.Adj z w := by
    by_contra hc
    refine hznotY0 (fun w hw => ?_)
    by_contra hadj
    exact hc ⟨w, hw, hadj⟩
  have hyNon : ∃ w ∈ Y \ {y}, ¬ G.Adj y w := by
    obtain ⟨w, hw⟩ := hY0ne
    obtain ⟨v, hvY, hvy, hnadj⟩ :=
      exists_nonneighbour_of_anticonnected hHyp.2.1 hyY hw.1 (fun h => hw.2 h)
    exact ⟨v, ⟨hvY, by simpa using hvy⟩, hnadj⟩
  -- membership bookkeeping
  have hyA : y ∉ A := fun h => Thm192Setup.wheelSystemA_no_z _ (hAsub h) hyz.symm
  have hx2A : x 2 ∉ A := fun h => hxA1 2 (by omega) (hAsub h)
  have hx1A : x 1 ∉ A := fun h => hxA1 1 (by omega) (hAsub h)
  have hzAmem : z ∉ A := fun h => hzA1 (hAsub h)
  have hYA : ∀ w ∈ Y, w ∉ A := fun w hw h => hYA1 w hw (hAsub h)
  have hzAdjA : ∀ w ∈ A, ¬ G.Adj z w := fun w hw => Thm192Setup.wheelSystemA_no_z _ (hAsub hw)
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hQ0f : Q[0]'hQpos = f := PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlastf₁ : Q[Q.length - 1]'(by omega) = f₁ :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQnd : Q.Nodup := PathBasics.path_nodup hQ.1
  have hx2nex1 : x 2 ≠ x 1 := by
    intro h
    have := hws.2.1 2 (by omega) 1 (by omega) h
    omega
  -- suppose the claim fails, and take the least index
  intro i0 hi0 hadj0
  obtain ⟨i, hiQ, hyqi, hmin⟩ :
      ∃ i : ℕ, ∃ h : i + 1 < Q.length, G.Adj y (Q[i]'(Nat.lt_of_succ_lt h)) ∧
        ∀ j : ℕ, j < i → ∀ hj : j + 1 < Q.length,
          ¬ G.Adj y (Q[j]'(Nat.lt_of_succ_lt hj)) := by
    have hP' : ∃ i : ℕ, ∃ h : i + 1 < Q.length, G.Adj y (Q[i]'(Nat.lt_of_succ_lt h)) :=
      ⟨i0, hi0, hadj0⟩
    obtain ⟨h1, h2⟩ := Nat.find_spec hP'
    exact ⟨Nat.find hP', h1, h2, fun j hj hjq hadj => Nat.find_min hP' hj ⟨hjq, hadj⟩⟩
  have hilt : i < Q.length := by omega
  -- the stretch `S = q₁-⋯-qᵢ`
  set S : List V := (Q.drop 0).take (i - 0 + 1) with hSdef
  have hSlen : S.length = i - 0 + 1 := PathBasics.length_slice Q (Nat.zero_le i) hilt
  have hSlen' : S.length = i + 1 := by omega
  have hSpath : IsPathList G S :=
    PathBasics.isPathList_take (PathBasics.isPathList_drop hQ.1 (by omega)) (by omega)
  have hShead : S.head? = some f :=
    (PathBasics.head?_slice Q (Nat.zero_le i) hilt).trans (congrArg some hQ0f)
  have hSlast : S.getLast? = some (Q[i]'hilt) :=
    PathBasics.getLast?_slice Q (Nat.zero_le i) hilt
  have hS : IsPathFrom G S f (Q[i]'hilt) := ⟨hSpath, hShead, hSlast⟩
  have hSmem : ∀ w ∈ S, ∃ (k : ℕ) (hk : k < Q.length), k ≤ i ∧ Q[k]'hk = w := by
    intro w hw
    obtain ⟨k, hk, -, hki, hkw⟩ := (PathBasics.mem_slice_iff Q (Nat.zero_le i) hilt).mp hw
    exact ⟨k, hk, hki, hkw⟩
  have hSQ : ∀ w ∈ S, w ∈ Q := by
    intro w hw
    obtain ⟨k, hk, -, rfl⟩ := hSmem w hw
    exact List.getElem_mem hk
  have hSA : ∀ w ∈ S, w ∈ A := fun w hw => hQA w (hSQ w hw)
  have hyS : y ∉ S := fun h => hyA (hSA y h)
  have hzS : z ∉ S := fun h => hzAmem (hSA z h)
  have hx2S : x 2 ∉ S := fun h => hx2A (hSA _ h)
  have hx1S : x 1 ∉ S := fun h => hx1A (hSA _ h)
  -- the only neighbour of `y` in `S` is `qᵢ`
  have hyother : ∀ w ∈ S, w ≠ Q[i]'hilt → ¬ G.Adj y w := by
    intro w hw hwne
    obtain ⟨k, hk, hki, rfl⟩ := hSmem w hw
    have hkne : k ≠ i := by
      intro h
      exact hwne (HoleArithmetic.getElem_congr_idx Q hk hilt h)
    exact hmin k (by omega) (by omega)
  -- the only neighbour of `x₂` in `S` is `f`
  have hx2other : ∀ w ∈ S, w ≠ f → ¬ G.Adj (x 2) w := by
    intro w hw hwf hadj
    exact hwf (hfuniq w (hSA w hw) hadj)
  -- `x₁` has no neighbour at all in `S`
  have hx1other : ∀ w ∈ S, ¬ G.Adj (x 1) w := by
    intro w hw hadj
    obtain ⟨k, hk, hki, rfl⟩ := hSmem w hw
    have heq : Q[k]'hk = f₁ := hf₁uniq _ (hQA _ (List.getElem_mem hk)) hadj
    rw [← hQlastf₁] at heq
    have : k = Q.length - 1 := by
      by_contra hne
      exact PathBasics.path_ne_of_ne_index hQ.1 hk (by omega) hne heq
    omega
  -- the path `x₂-q₁-⋯-qᵢ-y`
  have hSy : IsPathFrom G (S ++ [y]) f y :=
    PathAttach.isPathFrom_concat hS hyqi hyS hyother
  have hx2Sy : x 2 ∉ S ++ [y] := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hx2S h
    · exact hyx2 (show x 2 = y by simpa using h).symm
  have hT : IsPathFrom G (x 2 :: (S ++ [y])) (x 2) y := by
    refine PathAttach.isPathFrom_cons hSy hfadj hx2Sy ?_
    intro w hw hwf
    rcases List.mem_append.mp hw with h | h
    · exact hx2other w h hwf
    · rw [List.mem_singleton] at h
      subst h
      exact hx2ny
  -- the hole `z-x₂-q₁-⋯-qᵢ-y-z`, whence `i` is even
  have hTlen : (x 2 :: (S ++ [y])).length = i + 3 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have hzT : z ∉ x 2 :: (S ++ [y]) := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact (hzx 2 (by omega)).ne h
    rcases List.mem_append.mp h with h | h
    · exact hzS h
    · exact hyz'.symm (by simpa using h)
  have hhole : IsHoleList G (z :: x 2 :: (S ++ [y])) := by
    refine PrismBasics.isHoleList_of_path_add_vertex hT ?_ (hzx 2 (by omega)) hyz.symm hzT ?_
    · have := PathBasics.pathLength_eq (x 2 :: (S ++ [y]))
      omega
    · intro w hw
      rw [PathBasics.mem_interior_iff_of_pathFrom hT] at hw
      obtain ⟨hwT, hw2, hwy⟩ := hw
      rcases List.mem_cons.mp hwT with h | h
      · exact absurd h hw2
      rcases List.mem_append.mp h with h | h
      · exact hzAdjA w (hSA w h)
      · exact absurd (by simpa using h) hwy
  have hieven : ∃ k : ℕ, i + 4 = k + k := by
    have heven : Even (holeLength (z :: x 2 :: (S ++ [y]))) := hBerge.1 _ hhole
    have hlen : holeLength (z :: x 2 :: (S ++ [y])) = i + 4 := by
      simp only [holeLength, List.length_cons, List.length_append, List.length_nil]
      omega
    rw [hlen] at heven
    exact heven
  -- the path `x₂-q₁-⋯-qᵢ-y-x₁`
  have hx1Sy : x 1 ∉ S ++ [y] := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hx1S h
    · exact hyx1 (show x 1 = y by simpa using h).symm
  have hU : IsPathFrom G (x 2 :: ((S ++ [y]) ++ [x 1])) (x 2) (x 1) := by
    refine PathAttach.isPathFrom_cons_concat hSy hfadj (hHyp.2.2.2.1 y hyY) hx2x1 hx2nex1
      hx2Sy hx1Sy ?_ ?_
    · intro w hw hwf
      rcases List.mem_append.mp hw with h | h
      · exact hx2other w h hwf
      · rw [List.mem_singleton] at h
        subst h
        exact hx2ny
    · intro w hw hwy
      rcases List.mem_append.mp hw with h | h
      · exact hx1other w h
      · exact absurd (by simpa using h) hwy
  have hUlenP : pathLength (x 2 :: ((S ++ [y]) ++ [x 1])) = i + 3 := by
    rw [PathAttach.pathLength_cons_append_singleton]
    simp only [List.length_append, List.length_singleton, hSlen']
  have hUmem : ∀ w ∈ x 2 :: ((S ++ [y]) ++ [x 1]),
      w = x 2 ∨ w ∈ S ∨ w = y ∨ w = x 1 := by
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · exact Or.inl h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
  -- 13.6 applied to that path and the anticonnected set `Y₀ ∪ {z}`
  have hXanti : AnticonnectedSet G ((Y \ {y}) ∪ {z}) := by
    obtain ⟨w, hwY0, hwz⟩ := hzNon
    refine ConnectedSetUnionAttach.connectedSet_union_singleton hY0anti ⟨w, hwY0, ?_⟩
    simp only [SimpleGraph.compl_adj]
    refine ⟨?_, hwz⟩
    intro h
    exact (hHyp.1 w hwY0.1).1 h.symm
  have hXP : ((Y \ {y}) ∪ {z}) ⊆ {v : V | v ∈ x 2 :: ((S ++ [y]) ++ [x 1])}ᶜ := by
    intro v hv hvmem
    have hvU := hUmem v hvmem
    rcases hv with hv | hv
    · obtain ⟨hvz, hv0, hv1, hv2⟩ := hHyp.1 v hv.1
      rcases hvU with h | h | h | h
      · exact hv2 h
      · exact hYA v hv.1 (hSA v h)
      · exact hv.2 (by simpa using h)
      · exact hv1 h
    · have hvz : v = z := by simpa using hv
      rcases hvU with h | h | h | h
      · rw [hvz] at h; exact (hzx 2 (by omega)).ne h
      · have hvA := hSA v h; rw [hvz] at hvA; exact hzAmem hvA
      · rw [hvz] at h; exact hyz' h.symm
      · rw [hvz] at h; exact (hzx 1 (by omega)).ne h
  have hx2X : VertexComplete G (x 2) ((Y \ {y}) ∪ {z}) := by
    intro q hq
    rcases hq with hq | hq
    · exact hx2Y0 q hq
    · rw [show q = z from by simpa using hq]
      exact (hzx 2 (by omega)).symm
  have hx1X : VertexComplete G (x 1) ((Y \ {y}) ∪ {z}) := by
    intro q hq
    rcases hq with hq | hq
    · exact hHyp.2.2.2.1 q hq.1
    · rw [show q = z from by simpa using hq]
      exact (hzx 1 (by omega)).symm
  have hodd : Odd (pathLength (x 2 :: ((S ++ [y]) ++ [x 1]))) := by
    obtain ⟨k, hk⟩ := hieven
    have hk2 : 2 ≤ k := by omega
    refine ⟨k - 1, ?_⟩
    rw [hUlenP]
    omega
  have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hInF5
    (x 2 :: ((S ++ [y]) ++ [x 1])) (x 2) (x 1) hU hodd ((Y \ {y}) ∪ {z}) hXP hXanti hx2X hx1X
  -- only the two ends of the path are `Y₀ ∪ {z}`-complete, so the first alternative fails
  have honly : ∀ w ∈ x 2 :: ((S ++ [y]) ++ [x 1]),
      VertexComplete G w ((Y \ {y}) ∪ {z}) → w = x 2 ∨ w = x 1 := by
    intro w hw hwc
    rcases hUmem w hw with h | h | h | h
    · exact Or.inl h
    · exact absurd (hwc z (Or.inr rfl)).symm (hzAdjA w (hSA w h))
    · exfalso
      obtain ⟨v, hvY0, hvadj⟩ := hyNon
      exact hvadj (h ▸ hwc v (Or.inl hvY0))
    · exact Or.inr h
  have hi3 : i + 3 = 3 := by
    rcases h136 with ⟨u, hu, v, hv, hedge⟩ | ⟨h3, -⟩
    · exfalso
      rcases honly u hu hedge.2.1 with rfl | rfl
      · rcases honly v hv hedge.2.2 with rfl | rfl
        · exact G.irrefl hedge.1
        · exact hx2x1 hedge.1
      · rcases honly v hv hedge.2.2 with rfl | rfl
        · exact hx2x1 hedge.1.symm
        · exact G.irrefl hedge.1
    · rw [hUlenP] at h3
      exact h3
  have hi0' : i = 0 := by omega
  -- so `y` is adjacent to `f`
  have hfy : G.Adj y f := by
    have := hyqi
    rw [show (Q[i]'hilt) = f from by rw [← hQ0f]; exact HoleArithmetic.getElem_congr_idx Q hilt hQpos hi0'] at this
    exact this
  -- bookkeeping for the two antiholes
  have hfyne : f ≠ y := hfy.symm.ne
  have hfY0mem : f ∉ Y \ {y} := fun h => hYA f h.1 hfA
  have hyY0mem : y ∉ Y \ {y} := fun h => h.2 rfl
  have hx2f : x 2 ≠ f := hfadj.ne
  have hx1f : x 1 ≠ f := fun h => hx1A (h ▸ hfA)
  have hx1nadjf : ¬ G.Adj (x 1) f := fun h => hff₁ (hf₁uniq f hfA h)
  have hzf : z ≠ f := fun h => hzAmem (h ▸ hfA)
  have hznadjf : ¬ G.Adj z f := hzAdjA f hfA
  have hQlen2 : 2 ≤ Q.length := by
    by_contra hc
    have h1 : Q.length = 1 := by omega
    refine hff₁ ?_
    rw [← hQ0f, ← hQlastf₁]
    exact HoleArithmetic.getElem_congr_idx Q hQpos (by omega) (by omega)
  have hC₁len : 4 < holeLength (z :: x 2 :: (Q ++ [x 1])) := by
    simp only [holeLength, List.length_cons, List.length_append, List.length_singleton]
    omega
  have hfC₁ : f ∈ z :: x 2 :: (Q ++ [x 1]) := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
    rw [← hQ0f]; exact List.getElem_mem hQpos
  have hx2C₁ : x 2 ∈ z :: x 2 :: (Q ++ [x 1]) := List.mem_cons_of_mem _ List.mem_cons_self
  have hx1C₁ : x 1 ∈ z :: x 2 :: (Q ++ [x 1]) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (by simp)))
  have hzC₁ : z ∈ z :: x 2 :: (Q ++ [x 1]) := List.mem_cons_self
  -- the two antihole cases of the printed proof
  by_cases hfY0 : VertexComplete G f (Y \ {y})
  · -- `f` is `Y₀`-complete: an antipath between `z` and `y` closes via `y-x₂-x₁-f-z`
    obtain ⟨R, hR, hRint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hY0anti
        (fun h => (hHyp.1 z h.1).1 rfl) hyY0mem hzNon hyNon
    have hRmem : ∀ w ∈ R, w = z ∨ w = y ∨ w ∈ Y \ {y} := by
      intro w hw
      by_cases h1 : w = z
      · exact Or.inl h1
      by_cases h2 : w = y
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr
          (hRint w ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hw, h1, h2⟩)))
    have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
    have hzyne : z ≠ y := fun h => hyz' h.symm
    have hRlen : 3 ≤ R.length := by
      by_contra hc
      rcases (by omega : R.length = 1 ∨ R.length = 2) with h | h
      · refine hzyne ?_
        have e0 : R[0]'(by omega) = z := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
        have e1 : R[R.length - 1]'(by omega) = y :=
          PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
        rw [← e0, ← e1]
        exact HoleArithmetic.getElem_congr_idx R _ _ (by omega)
      · have hadj : Gᶜ.Adj z y :=
          PathBasics.isPathFrom_ends_adj_of_length_one hR (by
            have := PathBasics.pathLength_eq R; omega)
        simp only [SimpleGraph.compl_adj] at hadj
        exact hadj.2 hyz.symm
    have hx2R : x 2 ∉ R := by
      intro h
      rcases hRmem _ h with h | h | h
      · exact (hzx 2 (by omega)).ne h.symm
      · exact hyx2 h.symm
      · exact (hHyp.1 _ h.1).2.2.2 rfl
    have hR₁ : IsPathFrom Gᶜ (R ++ [x 2]) z (x 2) := by
      refine PathAttach.isPathFrom_concat hR ?_ hx2R ?_
      · simp only [SimpleGraph.compl_adj]
        exact ⟨fun h => hyx2 h.symm, hx2ny⟩
      · intro w hw hwy
        rcases hRmem w hw with h | h | h
        · subst h
          simp only [SimpleGraph.compl_adj]
          intro hc
          exact hc.2 (hzx 2 (by omega)).symm
        · exact absurd h hwy
        · simp only [SimpleGraph.compl_adj]
          intro hc
          exact hc.2 (hx2Y0 w h)
    have hx1R₁ : x 1 ∉ R ++ [x 2] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · rcases hRmem _ h with h | h | h
        · exact (hzx 1 (by omega)).ne h.symm
        · exact hyx1 h.symm
        · exact (hHyp.1 _ h.1).2.2.1 rfl
      · exact hx2nex1 (show x 1 = x 2 by simpa using h).symm
    have hR₂ : IsPathFrom Gᶜ ((R ++ [x 2]) ++ [x 1]) z (x 1) := by
      refine PathAttach.isPathFrom_concat hR₁ ?_ hx1R₁ ?_
      · simp only [SimpleGraph.compl_adj]
        exact ⟨fun h => hx2nex1 h.symm, fun h => hx2x1 h.symm⟩
      · intro w hw hw2
        rcases List.mem_append.mp hw with h | h
        · rcases hRmem w h with h | h | h
          · subst h
            simp only [SimpleGraph.compl_adj]
            intro hc
            exact hc.2 (hzx 1 (by omega)).symm
          · subst h
            simp only [SimpleGraph.compl_adj]
            intro hc
            exact hc.2 (hHyp.2.2.2.1 w hyY)
          · simp only [SimpleGraph.compl_adj]
            intro hc
            exact hc.2 (hHyp.2.2.2.1 w h.1)
        · exact absurd (by simpa using h) hw2
    have hfR₂ : f ∉ (R ++ [x 2]) ++ [x 1] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases hRmem _ h with h | h | h
          · exact hzf h.symm
          · exact hfyne h
          · exact hfY0mem h
        · exact hx2f (show f = x 2 by simpa using h).symm
      · exact hx1f (show f = x 1 by simpa using h).symm
    have hD : IsAntiholeList G (f :: ((R ++ [x 2]) ++ [x 1])) := by
      refine PrismBasics.isAntiholeList_of_antipath_add_vertex hR₂ ?_ ?_ ?_ hfR₂ ?_
      · have := PathBasics.pathLength_eq ((R ++ [x 2]) ++ [x 1])
        simp only [List.length_append, List.length_singleton] at this ⊢
        omega
      · simp only [SimpleGraph.compl_adj]
        exact ⟨fun h => hzf h.symm, fun h => hznadjf h.symm⟩
      · simp only [SimpleGraph.compl_adj]
        exact ⟨fun h => hx1f h.symm, fun h => hx1nadjf h.symm⟩
      · intro w hw
        rw [PathBasics.mem_interior_iff_of_pathFrom hR₂] at hw
        obtain ⟨hwm, hwz, hw1⟩ := hw
        simp only [SimpleGraph.compl_adj]
        intro hc
        rcases List.mem_append.mp hwm with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases hRmem w h with h | h | h
            · exact hwz h
            · exact hc.2 (h ▸ hfy.symm)
            · exact hc.2 (hfY0 w h)
          · exact hc.2 ((by simpa using h : w = x 2) ▸ hfadj.symm)
        · exact hw1 (by simpa using h)
    refine three_common (a := z) (b := x 2) (c := x 1) hInF6 hC₁ hC₁len hD ?_
      ((hzx 2 (by omega)).ne) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [holeLength, List.length_cons, List.length_append, List.length_singleton]
      omega
    · exact (hzx 1 (by omega)).ne
    · exact hx2nex1
    · exact hzC₁
    · exact hx2C₁
    · exact hx1C₁
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
        (PathBasics.head_mem hR.2.1)))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp))
  · -- `f` is not `Y₀`-complete: an antipath between `f` and `y` closes via `y-x₂-x₁-f`
    have hfNon : ∃ w ∈ Y \ {y}, ¬ G.Adj f w := by
      by_contra hc
      refine hfY0 (fun w hw => ?_)
      by_contra hadj
      exact hc ⟨w, hw, hadj⟩
    obtain ⟨R, hR, hRint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hY0anti hfY0mem hyY0mem hfNon hyNon
    have hRmem : ∀ w ∈ R, w = f ∨ w = y ∨ w ∈ Y \ {y} := by
      intro w hw
      by_cases h1 : w = f
      · exact Or.inl h1
      by_cases h2 : w = y
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr
          (hRint w ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hw, h1, h2⟩)))
    have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
    have hRlen : 3 ≤ R.length := by
      by_contra hc
      rcases (by omega : R.length = 1 ∨ R.length = 2) with h | h
      · refine hfyne ?_
        have e0 : R[0]'(by omega) = f := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
        have e1 : R[R.length - 1]'(by omega) = y :=
          PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
        rw [← e0, ← e1]
        exact HoleArithmetic.getElem_congr_idx R _ _ (by omega)
      · have hadj : Gᶜ.Adj f y :=
          PathBasics.isPathFrom_ends_adj_of_length_one hR (by
            have := PathBasics.pathLength_eq R; omega)
        simp only [SimpleGraph.compl_adj] at hadj
        exact hadj.2 hfy.symm
    have hx2R : x 2 ∉ R := by
      intro h
      rcases hRmem _ h with h | h | h
      · exact hx2f h
      · exact hyx2 h.symm
      · exact (hHyp.1 _ h.1).2.2.2 rfl
    have hR₁ : IsPathFrom Gᶜ (R ++ [x 2]) f (x 2) := by
      refine PathAttach.isPathFrom_concat hR ?_ hx2R ?_
      · simp only [SimpleGraph.compl_adj]
        exact ⟨fun h => hyx2 h.symm, hx2ny⟩
      · intro w hw hwy
        rcases hRmem w hw with h | h | h
        · subst h
          simp only [SimpleGraph.compl_adj]
          intro hc
          exact hc.2 hfadj
        · exact absurd h hwy
        · simp only [SimpleGraph.compl_adj]
          intro hc
          exact hc.2 (hx2Y0 w h)
    have hx1R₁ : x 1 ∉ R ++ [x 2] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · rcases hRmem _ h with h | h | h
        · exact hx1f h
        · exact hyx1 h.symm
        · exact (hHyp.1 _ h.1).2.2.1 rfl
      · exact hx2nex1 (show x 1 = x 2 by simpa using h).symm
    have hD : IsAntiholeList G (x 1 :: (R ++ [x 2])) := by
      refine PrismBasics.isAntiholeList_of_antipath_add_vertex hR₁ ?_ ?_ ?_ hx1R₁ ?_
      · have := PathBasics.pathLength_eq (R ++ [x 2])
        simp only [List.length_append, List.length_singleton] at this ⊢
        omega
      · simp only [SimpleGraph.compl_adj]
        exact ⟨hx1f, hx1nadjf⟩
      · simp only [SimpleGraph.compl_adj]
        exact ⟨hx2nex1.symm, fun h => hx2x1 h.symm⟩
      · intro w hw
        rw [PathBasics.mem_interior_iff_of_pathFrom hR₁] at hw
        obtain ⟨hwm, hwf, hw2⟩ := hw
        simp only [SimpleGraph.compl_adj]
        intro hc
        rcases List.mem_append.mp hwm with h | h
        · rcases hRmem w h with h | h | h
          · exact hwf h
          · exact hc.2 (h ▸ hHyp.2.2.2.1 y hyY)
          · exact hc.2 (hHyp.2.2.2.1 w h.1)
        · exact hw2 (by simpa using h)
    refine three_common (a := x 1) (b := x 2) (c := f) hInF6 hC₁ hC₁len hD ?_
      hx2nex1.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [holeLength, List.length_cons, List.length_append, List.length_singleton]
      omega
    · exact hx1f
    · exact hx2f
    · exact hx1C₁
    · exact hx2C₁
    · exact hfC₁
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (PathBasics.head_mem hR.2.1))

end Workspace.ProofLemmas.Thm192Claim12
