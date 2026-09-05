import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim9
import Workspace.ProofLemmas.Thm192Claim12
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S17.Thm_17_1

/-!
# The closing paragraph of the printed proof of 19.2

PAPER (printed p. 123):

> *To conclude, `A ∪ {x₂}` catches `{y,z,x₁}`, and so by 17.1, `y` is adjacent to
> `f₁ = q_k`.  Suppose that `x₀` is adjacent to one of `q₁,…,q_k`.  Then
> `{p₁,…,pₙ} ⊆ {q₁,…,q_k}` from the minimality of `A`, and so the neighbours of `y` in `C`
> are precisely `x₀, z, x₁, q_k = pₙ`, contrary to 2.3 applied to `C` and `y`.  So `x₀` is
> nonadjacent to all of `q₁,…,q_k`; but then `x₂-q₁-⋯-q_k-y-x₀` is an odd path of length
> `≥ 5`, its ends are `Y₀ ∪ {z}`-complete, and its internal vertices are not, contrary to
> 13.6.  Thus there is no such choice of `Y`.  This proves 19.2.*

The paragraph derives a contradiction outright, so the endgame lemma concludes `False`
from the whole accumulated context: the two extremal choices, claim (1)'s vertex `y`, the
path `P` and the choice made before claim (6), and the vertices `f`, `f₁` and the path `Q`
named by the interludes before claims (10) and (11).  Claims (2)–(12) are cited inside its
proof; they are not repeated in its hypotheses.

**`hcex`, the minimum-counterexample hypothesis.**  The closing paragraph does not cite claim
(4) directly, but the claims it *does* cite include (5), (6), (7), (8), (10), (11) and (12),
every one of which carries `(hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)` because its own
printed proof leans on the `hcex`-dependent conjuncts of claim (4) (*"The second is
immediate, for otherwise `(C,Y)` satisfies the theorem"*).  The whole paragraph is in any
case being run under the first line of the proof of 19.2, *"If possible, choose `Y` not
satisfying the theorem, with `|Y|` minimum"* — its conclusion `False` is exactly the
contradiction that refutes that choice.  So the standing assumption is carried explicitly as
`hcex`, in the same binder slot as in claims (4)–(12), and threaded through to those calls.
On the assembly side (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by
`by_contra` on the goal `Concl192 G z A₀ x Y` at the top of `core`, and is already an
explicit binder of the private wrapper `endgameAt`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closing paragraph of the printed proof of 19.2: *"To conclude, `A ∪ {x₂}` catches
`{y,z,x₁}` … Thus there is no such choice of `Y`.  This proves 19.2."* -/
theorem endgame (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
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
    False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hInF5 : InF5 G := hG.1.1
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) :=
    fun j hj => hws.2.2.2.2.2.2 j hj
  have hxA1 : ∀ j : ℕ, j ≤ 2 → x j ∉ wheelSystemA G z A₀ x 1 :=
    fun j hj h => Thm192Setup.wheelSystemA_no_z _ h (hzx j hj)
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
  have hyA : y ∉ A := fun h => hYA1 y hyY (hAsub h)
  have hzA : z ∉ A := fun h => hzA1 (hAsub h)
  have hx0A : x 0 ∉ A := fun h => hxA1 0 (by omega) (hAsub h)
  have hx1A : x 1 ∉ A := fun h => hxA1 1 (by omega) (hAsub h)
  have hx2A : x 2 ∉ A := fun h => hxA1 2 (by omega) (hAsub h)
  have hzAdjA : ∀ w ∈ A, ¬ G.Adj z w :=
    fun w hw => Thm192Setup.wheelSystemA_no_z _ (hAsub hw)
  have hx0ne1 : x 0 ≠ x 1 := by
    intro h
    have := hws.2.1 0 (by omega) 1 (by omega) h
    omega
  have hx2ne1 : x 2 ≠ x 1 := by
    intro h
    have := hws.2.1 2 (by omega) 1 (by omega) h
    omega
  have hx2ne0 : x 2 ≠ x 0 := by
    intro h
    have := hws.2.1 2 (by omega) 0 (by omega) h
    omega
  obtain ⟨hx2x0, hx2x1⟩ :=
    Workspace.ProofLemmas.Thm192Claim10.claim10 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
      hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
  obtain ⟨hznotY0, hx2Y0, hx2ny⟩ :=
    Workspace.ProofLemmas.Thm192Claim11.claim11 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
      hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
      f₁ hf₁A hf₁adj hf₁uniq hx2noP hff₁ Q hQ hQA hC₁
  have h12 := Workspace.ProofLemmas.Thm192Claim12.claim12 G hG z A₀ hframe x hws Y hHyp ih
    y hyY hyz hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj
    hfuniq f₁ hf₁A hf₁adj hf₁uniq hx2noP hff₁ Q hQ hQA hC₁

  -- The first sentence of the closing paragraph: 17.1 forces `y` to see `f₁`.
  have hyf₁ : G.Adj y f₁ := by
    by_contra hyf₁
    have hy1 : G.Adj y (x 1) := (hHyp.2.2.2.1 y hyY).symm
    let T : Set V := {y, z, x 1}
    let F : Set V := A ∪ {x 2}
    have htri : IsTriangle G T := by
      refine ⟨Set.ncard_eq_three.mpr ⟨y, z, x 1, hyz.ne, hyx1, (hzx 1 (by omega)).ne,
        rfl⟩, ?_⟩
      intro u hu v hv huv
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hyz
      · exact hy1
      · exact hyz.symm
      · exact (huv rfl).elim
      · exact hzx 1 (by omega)
      · exact hy1.symm
      · exact (hzx 1 (by omega)).symm
      · exact (huv rfl).elim
    have hFconn : ConnectedSet G F := by
      exact ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1 ⟨f, hfA, hfadj⟩
    have hFdisj : Disjoint F T := by
      rw [Set.disjoint_left]
      intro w hwF hwT
      rcases hwF with hwA | hw2
      · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hwT
        rcases hwT with rfl | rfl | rfl
        · exact hyA hwA
        · exact hzA hwA
        · exact hx1A hwA
      · have hw2' : w = x 2 := by simpa using hw2
        subst w
        simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hwT
        rcases hwT with h | h | h
        · exact hyx2 h.symm
        · exact (hzx 2 (by omega)).ne h.symm
        · exact hx2ne1 h
    have hcatch : Catches G F T := by
      refine ⟨htri, hFconn, hFdisj, ?_⟩
      intro w hw
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · obtain ⟨a, haA, hya⟩ := hA.2.2.2.2.2.2
        exact ⟨a, Or.inl haA, hya⟩
      · exact ⟨x 2, Or.inr rfl, hzx 2 (by omega)⟩
      · exact ⟨f₁, Or.inl hf₁A, hf₁adj⟩
    have hFT : F ⊆ Tᶜ := fun w hwF hwT => Set.disjoint_left.mp hFdisj hwF hwT
    rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFT hcatch with
        href | ⟨w, hwF, htwo⟩
    · obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hTeq, hRsub, href⟩ := href
      let R : Set V := {b₁, b₂, b₃}
      have hmatch : ∀ t ∈ T, ∃ r ∈ R, G.Adj t r := by
        intro t ht
        have ht' : t ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hTeq]; exact ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
        rcases ht' with rfl | rfl | rfl
        · refine ⟨b₁, by simp [R], ?_⟩
          exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
        · refine ⟨b₂, by simp [R], ?_⟩
          exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · refine ⟨b₃, by simp [R], ?_⟩
          exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have hx2R : x 2 ∈ R := by
        obtain ⟨r, hrR, hzr⟩ := hmatch z (by simp [T])
        have hrF : r ∈ F := hRsub (by simpa [R] using hrR)
        have hre : r = x 2 := by
          rcases hrF with hrA | hr2
          · exact (hzAdjA r hrA hzr).elim
          · simpa using hr2
        simpa [hre] using hrR
      have hf₁R : f₁ ∈ R := by
        obtain ⟨r, hrR, h1r⟩ := hmatch (x 1) (by simp [T])
        have hrF : r ∈ F := hRsub (by simpa [R] using hrR)
        have hre : r = f₁ := by
          rcases hrF with hrA | hr2
          · exact hf₁uniq r hrA h1r
          · have hre2 : r = x 2 := by simpa using hr2
            exact (hx2x1 (hre2 ▸ h1r.symm)).elim
        simpa [hre] using hrR
      have hx2f₁ : G.Adj (x 2) f₁ :=
        href.2.1.2 (x 2) (by simpa [R] using hx2R) f₁ (by simpa [R] using hf₁R)
          (fun h => hx2A (h.symm ▸ hf₁A))
      exact hff₁ (hfuniq f₁ hf₁A hx2f₁).symm
    · have hle : (G.neighborSet w ∩ T).ncard ≤ 1 := by
        apply (Set.ncard_le_one (Set.toFinite _)).2
        intro u hu v hv
        have hwu : G.Adj w u := by simpa only [SimpleGraph.mem_neighborSet] using hu.1
        have hwv : G.Adj w v := by simpa only [SimpleGraph.mem_neighborSet] using hv.1
        simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hwF with hwA | hw2
        · rcases hu.2 with rfl | rfl | rfl <;> rcases hv.2 with rfl | rfl | rfl
          <;> try rfl
          · exact (hzAdjA w hwA hwv.symm).elim
          · have hwf₁ := hf₁uniq w hwA hwv.symm
            exact (hyf₁ (hwf₁ ▸ hwu.symm)).elim
          · exact (hzAdjA w hwA hwu.symm).elim
          · exact (hzAdjA w hwA hwu.symm).elim
          · have hwf₁ := hf₁uniq w hwA hwu.symm
            exact (hyf₁ (hwf₁ ▸ hwv.symm)).elim
          · exact (hzAdjA w hwA hwv.symm).elim
        · have hwe : w = x 2 := by simpa using hw2
          subst w
          rcases hu.2 with rfl | rfl | rfl <;> rcases hv.2 with rfl | rfl | rfl
          <;> try rfl
          · exact (hx2ny hwu).elim
          · exact (hx2ny hwu).elim
          · exact (hx2ny hwv).elim
          · exact (hx2x1 hwv).elim
          · exact (hx2ny hwv).elim
          · exact (hx2x1 hwu).elim
      omega

  -- If `x₀` met `Q`, claim (9) would make the vertex set of `Q` equal to `A`.
  -- Claim (12) and 2.3 then give the contradiction in the printed proof.
  have hx0Q : ∀ w ∈ Q, ¬ G.Adj (x 0) w := by
    intro q hqQ hx0q
    let FQ : Set V := {w : V | w ∈ Q}
    have hFQsub : FQ ⊆ A := fun w hw => hQA w hw
    have hFQconn : ConnectedSet G FQ :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQ.1
    have hFQeq : FQ = A :=
      Workspace.ProofLemmas.Thm192Claim9.claim9 G hG z A₀ hframe x hws Y hHyp ih y hyY
        hyz hY0 A hA hAmin hcex FQ hFQsub hFQconn ⟨q, hqQ, hx0q⟩
        ⟨f₁, PathBasics.getLast_mem hQ.2.2, hf₁adj⟩
        ⟨f, PathBasics.head_mem hQ.2.1, hfadj⟩
    have hIntQ : ∀ w ∈ SPGT.interior P, w ∈ Q := by
      intro w hw
      have : w ∈ FQ := by rw [hFQeq]; exact hPint w hw
      exact this
    have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
    have hQlast : Q[Q.length - 1]'(by omega) = f₁ :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
    have hyQonly : ∀ w ∈ Q, G.Adj y w → w = f₁ := by
      intro w hw hadj
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
      by_cases hilast : i + 1 < Q.length
      · exact (h12 i hilast hadj).elim
      · rw [← hQlast]
        congr 1
        omega
    have hyPonly : ∀ w ∈ P, G.Adj y w → w = x 0 ∨ w = x 1 ∨ w = f₁ := by
      intro w hw hadj
      by_cases hw0 : w = x 0
      · exact Or.inl hw0
      by_cases hw1 : w = x 1
      · exact Or.inr (Or.inl hw1)
      exact Or.inr (Or.inr (hyQonly w
        (hIntQ w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hw0, hw1⟩)) hadj))
    have hx0nf₁ : ¬ G.Adj (x 0) f₁ := by
      intro h
      refine Thm192Setup.wheelSystemA_no_complete _ (hAsub hf₁A) ?_
      rw [Thm192Setup.wheelSystemX_one]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact h.symm
      · exact hf₁adj.symm
    have hE : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧
        EdgeComplete G ({y} : Set V) u v} = {s(x 1, f₁)} := by
      ext e
      constructor
      · rintro ⟨u, huP, v, hvP, rfl, huv, huY, hvY⟩
        have hyu : G.Adj y u := (huY y rfl).symm
        have hyv : G.Adj y v := (hvY y rfl).symm
        rcases hyPonly u huP hyu with rfl | rfl | rfl <;>
          rcases hyPonly v hvP hyv with rfl | rfl | rfl
        · exact (G.irrefl huv).elim
        · exact (Thm192Setup.x0_not_adj_x1 hws huv).elim
        · exact (hx0nf₁ huv).elim
        · exact (Thm192Setup.x0_not_adj_x1 hws huv.symm).elim
        · exact (G.irrefl huv).elim
        · exact rfl
        · exact (hx0nf₁ huv.symm).elim
        · exact Set.mem_singleton_iff.mpr Sym2.eq_swap
        · exact (G.irrefl huv).elim
      · intro he
        have heq : e = s(x 1, f₁) := by simpa using he
        subst e
        have hf₁P : f₁ ∈ P := by
          have hp : ∃ p ∈ SPGT.interior P, G.Adj (x 1) p := by
            have hpos : 0 < P.length := by omega
            let p := P[P.length - 2]'(by omega)
            have hpI : p ∈ SPGT.interior P :=
              PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
            have hpAdj : G.Adj (x 1) p := by
              have hadj := PathBasics.path_adj_succ hP.1
                (show P.length - 2 + 1 < P.length by omega)
              have hlast : P[P.length - 1]'(by omega) = x 1 :=
                PathBasics.getElem_last_of_getLast? hP.2.2 hpos
              have heq : P[P.length - 2 + 1]'(by omega) =
                  P[P.length - 1]'(by omega) := by
                congr 1
                omega
              rw [heq, hlast] at hadj
              exact hadj.symm
            exact ⟨p, hpI, hpAdj⟩
          obtain ⟨p, hpI, hpAdj⟩ := hp
          have peq : p = f₁ := hf₁uniq p (hPint p hpI) hpAdj
          rw [← peq]
          exact PathBasics.interior_subset hpI
        exact ⟨x 1, PathBasics.getLast_mem hP.2.2, f₁, hf₁P, rfl,
          hf₁adj, (fun w hw => by
            have : w = y := by simpa using hw
            subst w
            exact hHyp.2.2.2.1 y hyY), (fun w hw => by
            have : w = y := by simpa using hw
            subst w
            exact hyf₁.symm)⟩
    have hzP : z ∉ P := by
      intro hzP
      by_cases hz0 : z = x 0
      · exact (hzx 0 (by omega)).ne hz0
      by_cases hz1 : z = x 1
      · exact (hzx 1 (by omega)).ne hz1
      exact hzA (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hzP, hz0, hz1⟩))
    have hC : IsHoleList G (z :: P) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hP ?_ (hzx 0 (by omega))
        (hzx 1 (by omega)) hzP ?_
      · have := PathBasics.pathLength_eq P
        omega
      · intro w hw
        exact hzAdjA w (hPint w hw)
    have hCY : ∀ w ∈ z :: P, w ∉ ({y} : Set V) := by
      intro w hw hwy
      have wy : w = y := by simpa using hwy
      subst w
      rcases List.mem_cons.mp hw with h | h
      · exact hyz' h
      · exact hyA (hPint y ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
          ⟨h, hyx0, hyx1⟩))
    have hsingleAnti : AnticonnectedSet G ({y} : Set V) := by
      intro a b
      exact Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a
    have hrot : (z :: P).rotate 1 = P ++ [z] := by simp [List.rotate_cons_succ]
    have hpre : P <+: (z :: P).rotate 1 := by
      rw [hrot]
      exact ⟨[z], rfl⟩
    have hx0Y : VertexComplete G (x 0) ({y} : Set V) := by
      intro w hw
      have : w = y := by simpa using hw
      subst w
      exact hHyp.2.2.1 y hyY
    have hx1Y : VertexComplete G (x 1) ({y} : Set V) := by
      intro w hw
      have : w = y := by simpa using hw
      subst w
      exact hHyp.2.2.2.1 y hyY
    have hevenP : Even (pathLength P) := by
      obtain ⟨m, hm⟩ := hBerge.1 (z :: P) hC
      refine ⟨m - 1, ?_⟩
      rw [PathBasics.pathLength_eq]
      simp only [holeLength, List.length_cons] at hm
      omega
    have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge ({y} : Set V)
      hsingleAnti (z :: P) (Or.inr hC) hCY).1 P (x 0) (x 1)
        (Or.inr ⟨hC, 1, hpre⟩) hP hx0Y hx1Y
    rcases h23 with hpar | honly
    · rw [hE, Set.ncard_singleton] at hpar
      obtain ⟨m, hm⟩ := hevenP
      omega
    · have hzComplete : VertexComplete G z ({y} : Set V) := by
        intro w hw
        have : w = y := by simpa using hw
        subst w
        exact hyz.symm
      rcases honly z List.mem_cons_self hzComplete with h | h
      · exact (hzx 0 (by omega)).ne h
      · exact (hzx 1 (by omega)).ne h

  -- Claims (11) and (12) now give the final odd path forbidden by 13.6.
  have hY0ne : (Y \ {y}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    refine hznotY0 ?_
    intro w hw
    rw [h] at hw
    exact absurd hw (Set.notMem_empty w)
  have hY0anti : AnticonnectedSet G (Y \ {y}) := by
    rcases hY0 with h | h
    · exact absurd h (Set.nonempty_iff_ne_empty.mp hY0ne)
    · exact h
  have hzNon : ∃ w ∈ Y \ {y}, ¬ G.Adj z w := by
    by_contra h
    refine hznotY0 (fun w hw => ?_)
    by_contra hadj
    exact h ⟨w, hw, hadj⟩
  have hyNon : ∃ w ∈ Y \ {y}, ¬ G.Adj y w := by
    obtain ⟨w, hw⟩ := hY0ne
    have hwne : (w : V) ≠ y := fun h => hw.2 h
    have reach := hHyp.2.1 ⟨y, hyY⟩ ⟨w, hw.1⟩
    obtain ⟨walk⟩ := reach
    have first : ∀ (a b : ↑Y), (Gᶜ.induce Y).Walk a b → (a : V) = y → (b : V) ≠ y →
        ∃ v ∈ Y \ {y}, ¬ G.Adj y v := by
      intro a b walk
      induction walk with
      | nil => intro ha hb; exact (hb ha).elim
      | @cons a c b hac tail ih =>
          intro ha hb
          have he : Gᶜ.Adj y (c : V) := by simpa [ha] using hac
          simp only [SimpleGraph.compl_adj] at he
          exact ⟨c, ⟨c.2, fun h => he.1 h.symm⟩, he.2⟩
    exact first _ _ walk rfl hwne
  have hXanti : AnticonnectedSet G ((Y \ {y}) ∪ {z}) := by
    obtain ⟨w, hwY0, hwz⟩ := hzNon
    refine ConnectedSetUnionAttach.connectedSet_union_singleton hY0anti ⟨w, hwY0, ?_⟩
    simp only [SimpleGraph.compl_adj]
    exact ⟨fun h => (hHyp.1 w hwY0.1).1 h.symm, hwz⟩
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hQlast : Q[Q.length - 1]'(by omega) = f₁ :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQlen : 3 ≤ Q.length := by
    have heven : Even (holeLength (z :: x 2 :: (Q ++ [x 1]))) := hBerge.1 _ hC₁
    have hlen2 : 2 ≤ Q.length := by
      by_contra h
      have hlen1 : Q.length = 1 := by omega
      refine hff₁ ?_
      have hQ0 : Q[0]'hQpos = f := PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
      rw [← hQ0, ← hQlast]
      congr 1
      omega
    obtain ⟨m, hm⟩ := heven
    simp only [holeLength, List.length_cons, List.length_append, List.length_nil] at hm
    omega
  have hyQother : ∀ w ∈ Q, w ≠ f₁ → ¬ G.Adj y w := by
    intro w hwQ hwne hadj
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hwQ
    have hilast : i + 1 < Q.length := by
      by_contra h
      apply hwne
      rw [← hQlast]
      congr 1
      omega
    exact h12 i hilast hadj
  have hQy : IsPathFrom G (Q ++ [y]) f y :=
    PathAttach.isPathFrom_concat hQ hyf₁ (fun h => hyA (hQA y h)) hyQother
  have hx2Qy : x 2 ∉ Q ++ [y] := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hx2A (hQA _ h)
    · exact hyx2 (show x 2 = y by simpa using h).symm
  have hx2other : ∀ w ∈ Q ++ [y], w ≠ f → ¬ G.Adj (x 2) w := by
    intro w hw hwf hadj
    rcases List.mem_append.mp hw with hw | hw
    · exact hwf (hfuniq w (hQA w hw) hadj)
    · have hwy : w = y := by simpa using hw
      exact hx2ny (hwy ▸ hadj)
  have hT0 : IsPathFrom G (x 2 :: (Q ++ [y])) (x 2) y :=
    PathAttach.isPathFrom_cons hQy hfadj hx2Qy hx2other
  have hx0T0 : x 0 ∉ x 2 :: (Q ++ [y]) := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hx2ne0 h.symm
    rcases List.mem_append.mp h with h | h
    · exact hx0A (hQA _ h)
    · exact hyx0 (show x 0 = y by simpa using h).symm
  have hx0other : ∀ w ∈ x 2 :: (Q ++ [y]), w ≠ y → ¬ G.Adj (x 0) w := by
    intro w hw hwy hadj
    rcases List.mem_cons.mp hw with hw | hw
    · exact hx2x0 (hw ▸ hadj.symm)
    rcases List.mem_append.mp hw with hw | hw
    · exact hx0Q w hw hadj
    · exact hwy (by simpa using hw)
  have hT : IsPathFrom G ((x 2 :: (Q ++ [y])) ++ [x 0]) (x 2) (x 0) :=
    PathAttach.isPathFrom_concat hT0 (hHyp.2.2.1 y hyY) hx0T0 hx0other
  have hTlen : pathLength ((x 2 :: (Q ++ [y])) ++ [x 0]) = Q.length + 2 := by
    simp only [pathLength, List.length_append, List.length_cons, List.length_nil]
    omega
  have hTodd : Odd (pathLength ((x 2 :: (Q ++ [y])) ++ [x 0])) := by
    obtain ⟨m, hm⟩ := hBerge.1 _ hC₁
    refine ⟨m - 1, ?_⟩
    rw [hTlen]
    simp only [holeLength, List.length_cons, List.length_append, List.length_nil] at hm
    omega
  have hTmem : ∀ w ∈ (x 2 :: (Q ++ [y])) ++ [x 0],
      w = x 2 ∨ w ∈ Q ∨ w = y ∨ w = x 0 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_cons.mp hw with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hw)))
  have hXP : ((Y \ {y}) ∪ {z}) ⊆ {w : V | w ∈ (x 2 :: (Q ++ [y])) ++ [x 0]}ᶜ := by
    intro w hwX hwT
    rcases hTmem w hwT with h | h | h | h
    · subst w
      rcases hwX with hw | hw
      · exact (hHyp.1 (x 2) hw.1).2.2.2 rfl
      · have he : x 2 = z := by simpa using hw
        exact (hzx 2 (by omega)).ne he.symm
    · rcases hwX with hw | hw
      · exact hYA1 w hw.1 (hAsub (hQA w h))
      · have hwz : w = z := by simpa using hw
        rw [hwz] at h
        exact hzA (hQA z h)
    · subst w
      rcases hwX with hw | hw
      · exact hw.2 rfl
      · exact hyz' (by simpa using hw)
    · subst w
      rcases hwX with hw | hw
      · exact (hHyp.1 (x 0) hw.1).2.1 rfl
      · have he : x 0 = z := by simpa using hw
        exact (hzx 0 (by omega)).ne he.symm
  have hx2X : VertexComplete G (x 2) ((Y \ {y}) ∪ {z}) := by
    intro w hw
    rcases hw with hw | hw
    · exact hx2Y0 w hw
    · have : w = z := by simpa using hw
      subst w
      exact (hzx 2 (by omega)).symm
  have hx0X : VertexComplete G (x 0) ((Y \ {y}) ∪ {z}) := by
    intro w hw
    rcases hw with hw | hw
    · exact hHyp.2.2.1 w hw.1
    · have : w = z := by simpa using hw
      subst w
      exact (hzx 0 (by omega)).symm
  have honly : ∀ w ∈ (x 2 :: (Q ++ [y])) ++ [x 0],
      VertexComplete G w ((Y \ {y}) ∪ {z}) → w = x 2 ∨ w = x 0 := by
    intro w hw hwc
    rcases hTmem w hw with h | h | h | h
    · exact Or.inl h
    · exact (hzAdjA w (hQA w h) (hwc z (Or.inr rfl)).symm).elim
    · exfalso
      obtain ⟨v, hvY0, hyv⟩ := hyNon
      exact hyv (h ▸ hwc v (Or.inl hvY0))
    · exact Or.inr h
  have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hInF5
    ((x 2 :: (Q ++ [y])) ++ [x 0]) (x 2) (x 0) hT hTodd ((Y \ {y}) ∪ {z})
      hXP hXanti hx2X hx0X
  rcases h136 with ⟨u, hu, v, hv, hedge⟩ | ⟨hlen3, -⟩
  · rcases honly u hu hedge.2.1 with rfl | rfl <;>
      rcases honly v hv hedge.2.2 with rfl | rfl
    · exact G.irrefl hedge.1
    · exact hx2x0 hedge.1
    · exact hx2x0 hedge.1.symm
    · exact G.irrefl hedge.1
  · rw [hTlen] at hlen3
    omega

end Workspace.ProofLemmas.Thm192Endgame
