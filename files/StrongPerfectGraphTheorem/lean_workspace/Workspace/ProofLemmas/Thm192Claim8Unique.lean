import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim3
import Workspace.ProofLemmas.Thm192Claim7
import Workspace.ProofLemmas.Thm192Claim8Basics
import Workspace.ProofLemmas.Thm192Claim8Path
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm134RegionAux
import Workspace.Statements.S17.Thm_17_3

/-!
# Claim (8) of 19.2: `f₁` is `x₂`'s only neighbour in `A`, and `f_k` is `x₁`'s

PAPER (printed p. 121):

> *"Now assume that `f₁` is not the unique neighbour of `x₂` in `A`.  From (3), `f₁` is the
> unique neighbour of `x₀` in `A`.  By (7), `f_k` is not the unique neighbour of `x₁` in
> `A`, and so from (3) it is the unique neighbour of `y` in `A`.  In particular `y` is not
> adjacent to `f₁`.  Both `x₀, z` have unique neighbours in `A ∪ {x₁} = F` say, namely
> `f₁, x₁` respectively.  Now `x₀, z` are both `{x₂,y}`-complete, and `f₁, x₁` are not.
> Since `F \ {x₁}` is connected, this contradicts 17.3.  So `f₁` is the unique neighbour of
> `x₂` in `A`.  Suppose that `f_k` is the unique neighbour of `y` in `A`.  Then both `z, y`
> have unique neighbours in `A ∪ {x₂}`, namely `x₂, f_k` respectively; and `z, y` are
> `{x₀,x₁}`-complete, and `x₂, f_k` are not.  Once again this contradicts 17.3.  So `f_k` is
> not the unique neighbour of `y` in `A`, and therefore it is the unique neighbour of `x₁`
> in `F`."*

Every *"from (3)"* here is the same move: deleting the endpoint of the path `f₁-⋯-f_k`
leaves a connected proper subset of `A`, so by claim (3) it must miss a neighbour of one of
`x₀, x₁, x₂, y`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8Unique

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two nonadjacent vertices form an anticonnected pair. -/
theorem anticonnected_pair {G : SimpleGraph V} {u v : V} (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    AnticonnectedSet G ({u, v} : Set V) := by
  have he : ({u, v} : Set V) = {v} ∪ {u} := by rw [Set.union_singleton]
  rw [AnticonnectedSet, he]
  exact ConnectedSetUnionAttach.connectedSet_union_singleton
    (Thm134RegionAux.connectedSet_singleton Gᶜ v) ⟨v, rfl, ⟨hne, huv⟩⟩

/-- Deleting the first vertex of a path leaves the stretch from its second vertex on. -/
theorem tail_eq {G : SimpleGraph V} {R : List V} {f₁ fk : V}
    (hR : IsPathFrom G R f₁ fk) (hlen : 2 ≤ R.length) :
    {w : V | w ∈ (R.drop 1).take (R.length - 1 - 1 + 1)} = {w : V | w ∈ R} \ {f₁} := by
  have hnd : R.Nodup := hR.1.2.1
  have h0 : R[0]'(by omega) = f₁ := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  rw [PathBasics.mem_slice_iff R (by omega) (show R.length - 1 < R.length by omega)]
  constructor
  · rintro ⟨k, hk, h1k, hkj, rfl⟩
    refine ⟨List.getElem_mem hk, ?_⟩
    intro he
    rw [← h0] at he
    have : k = 0 := (List.Nodup.getElem_inj_iff hnd).mp he
    omega
  · rintro ⟨hw, hne⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
    refine ⟨k, hk, ?_, by omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd h0 hne
    · omega

/-- Deleting the last vertex of a path leaves the stretch up to its penultimate vertex. -/
theorem init_eq {G : SimpleGraph V} {R : List V} {f₁ fk : V}
    (hR : IsPathFrom G R f₁ fk) (hlen : 2 ≤ R.length) :
    {w : V | w ∈ (R.drop 0).take (R.length - 2 - 0 + 1)} = {w : V | w ∈ R} \ {fk} := by
  have hnd : R.Nodup := hR.1.2.1
  have hl : R[R.length - 1]'(by omega) = fk :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  rw [PathBasics.mem_slice_iff R (by omega) (show R.length - 2 < R.length by omega)]
  constructor
  · rintro ⟨k, hk, h1k, hkj, rfl⟩
    refine ⟨List.getElem_mem hk, ?_⟩
    intro he
    rw [← hl] at he
    have : k = R.length - 1 := (List.Nodup.getElem_inj_iff hnd).mp he
    omega
  · rintro ⟨hw, hne⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
    refine ⟨k, hk, by omega, ?_, rfl⟩
    by_contra hcon
    exact hne (by rw [← hl]; exact HoleArithmetic.getElem_congr_idx R _ _ (by omega))


/-- The vertex set of a stretch of a path is connected (also when the stretch is a single
vertex). -/
theorem connected_slice {G : SimpleGraph V} {p : List V} (hp : IsPathList G p) {i j : ℕ}
    (hij : i ≤ j) (hj : j < p.length) :
    ConnectedSet G {w : V | w ∈ (p.drop i).take (j - i + 1)} := by
  rcases lt_or_eq_of_le hij with h | h
  · exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathFrom_slice hp h hj).1
  · have hset : {w : V | w ∈ (p.drop i).take (j - i + 1)} = {p[j]'hj} := by
      ext w
      rw [Set.mem_setOf_eq, PathBasics.mem_slice_iff p hij hj, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, hk, h1, h2, rfl⟩
        exact HoleArithmetic.getElem_congr_idx p _ _ (by omega)
      · rintro rfl
        exact ⟨j, hj, by omega, by omega, rfl⟩
    rw [hset]
    exact Thm134RegionAux.connectedSet_singleton G _


/-- The bookkeeping shared by every step of claim (8): `A` misses `z`, `x₀`, `x₁`, `x₂`, `y`,
and contains no `{x₀,x₁}`-complete vertex. -/
theorem unique_nbs (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (hx20 : G.Adj (x 2) (x 0)) (h2y : ¬ G.Adj (x 2) y)
    (R : List V) (f₁ fk : V) (hR : IsPathFrom G R f₁ fk) (hRA : {w : V | w ∈ R} = A)
    (h0f₁ : G.Adj (x 0) f₁) (h2f₁ : G.Adj (x 2) f₁) (h1fk : G.Adj (x 1) fk)
    (hyfk : G.Adj y fk) (hfne : f₁ ≠ fk) :
    (∀ a ∈ A, G.Adj (x 2) a → a = f₁) ∧ (∀ a ∈ A, G.Adj (x 1) a → a = fk) ∧
      (∃ a ∈ A, a ≠ fk ∧ G.Adj y a) := by
  classical
  -- standing bookkeeping
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hzA : ∀ g ∈ A, ¬ G.Adj z g := fun g hg => wheelSystemA_no_z g (hAsub hg)
  have hxA : ∀ j : ℕ, j ≤ 2 → x j ∉ A := fun j hj hm => hzA _ hm (hzx j hj)
  have hzAmem : z ∉ A := Thm192Claim8Basics.z_notMem hws hAsub
  have hyA : y ∉ A := fun hm => hzA _ hm hyz.symm
  have hnoc : ∀ g ∈ A, ¬ (G.Adj (x 0) g ∧ G.Adj (x 1) g) := by
    intro g hg hc
    exact Thm192Claim8Basics.no_X1_complete hAsub g hg ⟨hc.1.symm, hc.2.symm⟩
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro hadj
    refine hws.2.2.2.2.2.1 2 (by omega) (by omega) ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx20
    · exact hadj
  have hx01 : ¬ G.Adj (x 0) (x 1) := x0_not_adj_x1 hws
  have hxne : ∀ i j : ℕ, i ≤ 2 → j ≤ 2 → i ≠ j → x i ≠ x j := by
    intro i j hi hj hij he
    exact hij (hws.2.1 i hi j hj he)
  have hxz : ∀ j : ℕ, j ≤ 2 → x j ≠ z := fun j hj => (hws.2.2.1 j hj).2
  have hyne : y ≠ z ∧ y ≠ x 0 ∧ y ≠ x 1 ∧ y ≠ x 2 := hHyp.1 y hyY
  -- the two ends of the path
  have hf₁A : f₁ ∈ A := by rw [← hRA]; exact List.mem_of_mem_head? hR.2.1
  have hfkA : fk ∈ A := by rw [← hRA]; exact List.mem_of_mem_getLast? hR.2.2
  have hf₁ne : ∀ j : ℕ, j ≤ 2 → f₁ ≠ x j := fun j hj he => hxA j hj (he ▸ hf₁A)
  have hfkne : ∀ j : ℕ, j ≤ 2 → fk ≠ x j := fun j hj he => hxA j hj (he ▸ hfkA)
  have hzf₁ : ¬ G.Adj z f₁ := hzA _ hf₁A
  have hzfk : ¬ G.Adj z fk := hzA _ hfkA
  have h1f₁ : ¬ G.Adj (x 1) f₁ := fun h => hnoc f₁ hf₁A ⟨h0f₁, h⟩
  have h0fk : ¬ G.Adj (x 0) fk := fun h => hnoc fk hfkA ⟨h, h1fk⟩
  -- lengths and the two deletions
  have hpos : 0 < R.length := List.length_pos_iff.mpr hR.1.1
  have h0R : R[0]'hpos = f₁ := PathBasics.getElem_zero_of_head? hR.2.1 hpos
  have hlR : R[R.length - 1]'(by omega) = fk :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hpos
  have hlen : 2 ≤ R.length := by
    by_contra hcon
    have h1 : R.length = 1 := by omega
    refine hfne ?_
    rw [← h0R, ← hlR]
    exact (HoleArithmetic.getElem_congr_idx R _ _ (by omega)).symm
  have hconnTail : ConnectedSet G (A \ {f₁}) := by
    have := connected_slice hR.1 (i := 1) (j := R.length - 1) (by omega) (by omega)
    rwa [tail_eq hR hlen, hRA] at this
  have hconnInit : ConnectedSet G (A \ {fk}) := by
    have := connected_slice hR.1 (i := 0) (j := R.length - 2) (by omega) (by omega)
    rwa [init_eq hR hlen, hRA] at this
  -- the two "from (3)" deletions
  have L2 : ¬ ((∃ a ∈ A, a ≠ f₁ ∧ G.Adj (x 2) a) ∧ (∃ a ∈ A, a ≠ f₁ ∧ G.Adj (x 0) a)) := by
    rintro ⟨⟨a2, ha2, hne2, hadj2⟩, ⟨a0, ha0, hne0, hadj0⟩⟩
    have heq := Thm192Claim3.claim3 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin (A \ {f₁}) Set.diff_subset hconnTail ⟨a0, ⟨ha0, hne0⟩, hadj0⟩
      ⟨fk, ⟨hfkA, hfne.symm⟩, h1fk⟩ ⟨a2, ⟨ha2, hne2⟩, hadj2⟩ ⟨fk, ⟨hfkA, hfne.symm⟩, hyfk⟩
    have : f₁ ∈ A \ {f₁} := by rw [heq]; exact hf₁A
    exact this.2 rfl
  have L1 : ¬ ((∃ a ∈ A, a ≠ fk ∧ G.Adj (x 1) a) ∧ (∃ a ∈ A, a ≠ fk ∧ G.Adj y a)) := by
    rintro ⟨⟨a1, ha1, hne1, hadj1⟩, ⟨ay, hay, hney, hadjy⟩⟩
    have heq := Thm192Claim3.claim3 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin (A \ {fk}) Set.diff_subset hconnInit ⟨f₁, ⟨hf₁A, hfne⟩, h0f₁⟩
      ⟨a1, ⟨ha1, hne1⟩, hadj1⟩ ⟨f₁, ⟨hf₁A, hfne⟩, h2f₁⟩ ⟨ay, ⟨hay, hney⟩, hadjy⟩
    have : fk ∈ A \ {fk} := by rw [heq]; exact hfkA
    exact this.2 rfl
  -- claim (7) forbids `f₁` unique for `x₀` together with `f_k` unique for `x₁`
  have L7 : ¬ ((∀ a ∈ A, G.Adj (x 0) a → a = f₁) ∧ (∀ a ∈ A, G.Adj (x 1) a → a = fk)) := by
    rintro ⟨hu0, hu1⟩
    have hx0R : x 0 ∉ R := fun h => hxA 0 (by omega) (by rw [← hRA]; exact h)
    have hx1R : x 1 ∉ R := fun h => hxA 1 (by omega) (by rw [← hRA]; exact h)
    have hP : IsPathFrom G (x 0 :: (R ++ [x 1])) (x 0) (x 1) :=
      PathAttach.isPathFrom_cons_concat hR h0f₁ h1fk hx01
        (hxne 0 1 (by omega) (by omega) (by omega)) hx0R hx1R
        (fun w hw hwne hadj => hwne (hu0 w (by rw [← hRA]; exact hw) hadj))
        (fun w hw hwne hadj => hwne (hu1 w (by rw [← hRA]; exact hw) hadj))
    have hint : SPGT.interior (x 0 :: (R ++ [x 1])) = R := by
      simp [SPGT.interior]
    have hPint : ∀ w ∈ SPGT.interior (x 0 :: (R ++ [x 1])), w ∈ A := by
      intro w hw
      rw [hint] at hw
      rw [← hRA]; exact hw
    have hPlen : 3 ≤ (x 0 :: (R ++ [x 1])).length := by
      rw [PathAttach.length_cons_append_singleton]; omega
    have hAP : ∀ a ∈ A, a ∈ (x 0 :: (R ++ [x 1])) := by
      intro a ha
      rw [PathAttach.mem_cons_append_singleton]
      exact Or.inr (Or.inl (by rw [← hRA] at ha; exact ha))
    have hchoice := Thm192Claim8Basics.choiceOfPath G hG z A₀ hframe x hws Y hHyp ih y hyY
      hyz hY0 A hA hAmin _ hP hPint hPlen hAP
    refine Thm192Claim7.claim7 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      hcex _ hP hPint hPlen hchoice ⟨⟨f₁, ?_, h2f₁⟩, ⟨fk, ?_, hyfk⟩⟩
    · rw [hint]; rw [← hRA] at hf₁A; exact hf₁A
    · rw [hint]; rw [← hRA] at hfkA; exact hfkA
  -- **`f₁` is the unique neighbour of `x₂` in `A`.**
  have hu2 : ∀ a ∈ A, G.Adj (x 2) a → a = f₁ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a2, ha2, hadj2, hne2⟩ := hcon
    have hu0 : ∀ a ∈ A, G.Adj (x 0) a → a = f₁ := by
      intro a ha hadj
      by_contra hne
      exact L2 ⟨⟨a2, ha2, hne2, hadj2⟩, ⟨a, ha, hne, hadj⟩⟩
    have hnu1 : ∃ a ∈ A, a ≠ fk ∧ G.Adj (x 1) a := by
      by_contra hcon1
      push_neg at hcon1
      exact L7 ⟨hu0, fun a ha hadj => by
        by_contra hne
        exact hcon1 a ha hne hadj⟩
    have huy : ∀ a ∈ A, G.Adj y a → a = fk := by
      intro a ha hadj
      by_contra hne
      exact L1 ⟨hnu1, ⟨a, ha, hne, hadj⟩⟩
    have hyf₁ : ¬ G.Adj y f₁ := fun h => hfne (huy f₁ hf₁A h)
    -- 17.3 with `F = A ∪ {x₁}` and `Y = {x₂, y}`
    have hFconn : ConnectedSet G (A ∪ {x 1}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1 ⟨fk, hfkA, h1fk⟩
    have hFA : (A ∪ {x 1}) \ {x 1} = A := by
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hw | hw, hne⟩
        · exact hw
        · exact absurd hw hne
      · exact fun hw => ⟨Or.inl hw, fun he => hxA 1 (by omega) (he ▸ hw)⟩
    have hdisj : Disjoint (A ∪ {x 1}) ({x 2, y} : Set V) := by
      rw [Set.disjoint_left]
      rintro a ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases ha with ha | ha
      · rcases hb with rfl | rfl
        · exact hxA 2 (by omega) ha
        · exact hyA ha
      · have hax : a = x 1 := ha
        subst hax
        rcases hb with h | h
        · exact hxne 1 2 (by omega) (by omega) (by omega) h
        · exact hyne.2.2.1 h.symm
    have hanti : AnticonnectedSet G ({x 2, y} : Set V) :=
      anticonnected_pair (fun h => hyne.2.2.2 h.symm) h2y
    have hpath : IsPathList G [x 1, z, x 0, f₁] := by
      refine PathGlue.isPathList_four ?_ (hzx 1 (by omega)).symm (hzx 0 (by omega)) h0f₁
        (fun h => hx01 h.symm) (fun h => h1f₁ h) hzf₁
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or, not_false_eq_true, or_false]
      exact ⟨⟨hxz 1 (by omega), (hxne 0 1 (by omega) (by omega) (by omega)).symm,
        (hf₁ne 1 (by omega)).symm⟩, ⟨(hxz 0 (by omega)).symm, fun h => hzAmem (by rw [h]; exact hf₁A)⟩,
        (hf₁ne 0 (by omega)).symm⟩
    have hz₀ : z ∉ (A ∪ {x 1}) ∪ ({x 2, y} : Set V) := by
      rintro ((h | h) | h)
      · exact hzAmem h
      · exact hxz 1 (by omega) (by simpa using h.symm)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h
        · exact hxz 2 (by omega) h.symm
        · exact hyne.1 h.symm
    have hb₀ : x 0 ∉ (A ∪ {x 1}) ∪ ({x 2, y} : Set V) := by
      rintro ((h | h) | h)
      · exact hxA 0 (by omega) h
      · exact hxne 0 1 (by omega) (by omega) (by omega) (by simpa using h)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h
        · exact hxne 0 2 (by omega) (by omega) (by omega) h
        · exact hyne.2.1 h.symm
    have hzF : {f ∈ (A ∪ {x 1}) | G.Adj z f} = {x 1} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hf | hf, hadj⟩
        · exact absurd hadj (hzA f hf)
        · exact hf
      · rintro rfl
        exact ⟨Or.inr rfl, hzx 1 (by omega)⟩
    have hx0F : {f ∈ (A ∪ {x 1}) | G.Adj (x 0) f} = {f₁} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hf | hf, hadj⟩
        · exact hu0 f hf hadj
        · exact absurd (hf ▸ hadj) hx01
      · rintro rfl
        exact ⟨Or.inl hf₁A, h0f₁⟩
    obtain ⟨w, hw, hwanti⟩ := Workspace.Statements.S17.SPGT.thm_17_3 G hG (A ∪ {x 1})
      ({x 2, y} : Set V) hdisj hFconn hanti z (x 0) (x 1) f₁ hz₀ hb₀ (Or.inr rfl)
      (Or.inl hf₁A) hpath
      (by intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with h | h
          · rw [h]; exact hzx 2 (by omega)
          · rw [h]; exact hyz.symm)
      (by intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with h | h
          · rw [h]; exact hx20.symm
          · rw [h]; exact (hHyp.2.2.1 y hyY))
      (by intro hc; exact hx21 (hc (x 2) (by simp)).symm)
      (by intro hc; exact hyf₁ (hc y (by simp)).symm)
      hzF hx0F (by rw [hFA]; exact hA.2.1)
    rw [hFA] at hwanti
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hwanti f₁ hf₁A h2f₁
    · exact hwanti fk hfkA hyfk
  -- **`f_k` is not the unique neighbour of `y` in `A`.**
  have hnuy : ∃ a ∈ A, a ≠ fk ∧ G.Adj y a := by
    by_contra hcon
    push_neg at hcon
    have huy : ∀ a ∈ A, G.Adj y a → a = fk := by
      intro a ha hadj
      by_contra hne
      exact hcon a ha hne hadj
    have h2fk : ¬ G.Adj (x 2) fk := fun h => hfne (hu2 fk hfkA h).symm
    have hFconn : ConnectedSet G (A ∪ {x 2}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1 ⟨f₁, hf₁A, h2f₁⟩
    have hFA : (A ∪ {x 2}) \ {x 2} = A := by
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hw | hw, hne⟩
        · exact hw
        · exact absurd hw hne
      · exact fun hw => ⟨Or.inl hw, fun he => hxA 2 (by omega) (he ▸ hw)⟩
    have hdisj : Disjoint (A ∪ {x 2}) ({x 0, x 1} : Set V) := by
      rw [Set.disjoint_left]
      rintro a ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases ha with ha | ha
      · rcases hb with rfl | rfl
        · exact hxA 0 (by omega) ha
        · exact hxA 1 (by omega) ha
      · have hax : a = x 2 := ha
        subst hax
        rcases hb with h | h
        · exact hxne 2 0 (by omega) (by omega) (by omega) h
        · exact hxne 2 1 (by omega) (by omega) (by omega) h
    have hanti : AnticonnectedSet G ({x 0, x 1} : Set V) :=
      anticonnected_pair (hxne 0 1 (by omega) (by omega) (by omega)) hx01
    have hpath : IsPathList G [x 2, z, y, fk] := by
      refine PathGlue.isPathList_four ?_ (hzx 2 (by omega)).symm hyz.symm hyfk h2y h2fk
        (fun h => hzfk h)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or, not_false_eq_true, or_false]
      exact ⟨⟨hxz 2 (by omega), fun h => hyne.2.2.2 h.symm, (hfkne 2 (by omega)).symm⟩,
        ⟨fun h => hyne.1 h.symm, fun h => hzAmem (by rw [h]; exact hfkA)⟩,
        fun h => hyA (h ▸ hfkA)⟩
    have hz₀ : z ∉ (A ∪ {x 2}) ∪ ({x 0, x 1} : Set V) := by
      rintro ((h | h) | h)
      · exact hzAmem h
      · exact hxz 2 (by omega) (by simpa using h.symm)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h
        · exact hxz 0 (by omega) h.symm
        · exact hxz 1 (by omega) h.symm
    have hb₀ : y ∉ (A ∪ {x 2}) ∪ ({x 0, x 1} : Set V) := by
      rintro ((h | h) | h)
      · exact hyA h
      · exact hyne.2.2.2 (by simpa using h)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h
        · exact hyne.2.1 h
        · exact hyne.2.2.1 h
    have hzF : {f ∈ (A ∪ {x 2}) | G.Adj z f} = {x 2} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hf | hf, hadj⟩
        · exact absurd hadj (hzA f hf)
        · exact hf
      · rintro rfl
        exact ⟨Or.inr rfl, hzx 2 (by omega)⟩
    have hyF : {f ∈ (A ∪ {x 2}) | G.Adj y f} = {fk} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hf | hf, hadj⟩
        · exact huy f hf hadj
        · exact absurd (hf ▸ hadj) (fun h => h2y h.symm)
      · rintro rfl
        exact ⟨Or.inl hfkA, hyfk⟩
    obtain ⟨w, hw, hwanti⟩ := Workspace.Statements.S17.SPGT.thm_17_3 G hG (A ∪ {x 2})
      ({x 0, x 1} : Set V) hdisj hFconn hanti z y (x 2) fk hz₀ hb₀ (Or.inr rfl)
      (Or.inl hfkA) hpath
      (by intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact hzx 0 (by omega)
          · exact hzx 1 (by omega))
      (by intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact (hHyp.2.2.1 y hyY).symm
          · exact (hHyp.2.2.2.1 y hyY).symm)
      (by intro hc; exact hx21 (hc (x 1) (by simp)))
      (by intro hc; exact h0fk (hc (x 0) (by simp)).symm)
      hzF hyF (by rw [hFA]; exact hA.2.1)
    rw [hFA] at hwanti
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hwanti f₁ hf₁A h0f₁
    · exact hwanti fk hfkA h1fk
  refine ⟨hu2, ?_, hnuy⟩
  intro a ha hadj
  by_contra hne
  exact L1 ⟨⟨a, ha, hne, hadj⟩, hnuy⟩

end Workspace.ProofLemmas.Thm192Claim8Unique
