/-  Carve-out for statement 11.4 (`Workspace.Statements.S11.SPGT.thm_11_4`): step (1) of the
    printed proof.

    PAPER (printed p. 67):

      *"(1) `n ≥ 2`.*

      *For suppose `n = 1`.  Then `q₁` is adjacent to `a₀` and to `b₁`, and not to `b₀`, so by
      10.4, `q₁` has a neighbour in `R₂ \ b₂`.  Since `q₁` also has a neighbour in `F`, it can
      be linked onto the triangle `{b₀, b₁, b₂}`, via a path from `q₁` to `b₀` with interior in
      `F`, the path `q₁-b₁`, and the path from `q₁` to `b₂` with interior in `R₂`, contrary to
      2.4.  This proves (1)."*

    The theorem below is exactly the `n = 1` case: a single vertex `q` outside `V(S) ∪ F` with
    a neighbour in `F`, adjacent to the left-star `a₀` and to `b₁`, and non-adjacent to `b₀`
    and to `b₂`, yields a contradiction.

    HOW THE TWO CITED RESULTS ARE USED.

    * 10.4 is applied to the prism formed by the banister `a₀-R₀-b₀` and the step
      `a₁-R₁-b₁, a₂-R₂-b₂` (this is `PrismFromBanisterAndStep.formPrism_of_banister_and_step`),
      with `F := {q}` and the third rung of the prism taken to be `R₂`.  If `q` had no
      neighbour in `R₂` at all then `q` would have no attachment in the third rung, the
      attachment set `{a₀, b₁, …}` is not local (`a₀` lies only on the banister and `b₁` only
      on `R₁`), no vertex of `F` can be major because there is no even prism in `G` at all, and
      so 10.4 would force `F = {q}` to be nontrivial — absurd.  Hence `q` has a neighbour in
      `R₂`, and since `q` is not adjacent to `b₂` that neighbour lies in `R₂ \ b₂`.
    * 2.4 is applied to the triangle `{b₀, b₁, b₂}` with the three linking paths
      `P₀ ⊆ F ∪ {b₀}`, `P₁ = [b₁]` and `P₂ = R₂`; `q` has a neighbour in each, so 2.4 makes `q`
      adjacent to two of `b₀, b₁, b₂`, whereas it is adjacent only to `b₁`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm101LinkOntoTriangle
import Workspace.ProofLemmas.Thm114Aux
import Workspace.ProofLemmas.Thm121Case3RightDiagonal
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S10.Thm_10_4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm114ClaimOne

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Step (1) of the printed proof of 11.4**, in its contrapositive `n = 1` form.

There is no vertex `q` outside `V(S) ∪ F` with a neighbour in `F` which is adjacent to the
left-star `a₀` of a banister `a₀-R₀-b₀` (whose interior lies in `F`) and to the `B`-end `b₁`
of one rung of a step, but non-adjacent to the right-star `b₀` and to the `B`-end `b₂` of the
other rung. -/
theorem thm114_claim_one {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V), IsEvenPrism G a b P₁ P₂ P₃)
    (A C B F : Set V)
    (hFout : ∀ v ∈ F, v ∉ A ∪ B ∪ C)
    (hFconn : ConnectedSet G F)
    (hFanti : SPGT.Anticomplete G F (A ∪ B ∪ C))
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (hR₀F : ∀ w ∈ SPGT.interior R₀, w ∈ F)
    (hb₀Fnbr : ∃ f ∈ F, G.Adj b₀ f)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (q : V) (hqS : q ∉ A ∪ B ∪ C) (hqF : q ∉ F)
    (hqFnbr : ∃ f ∈ F, G.Adj q f)
    (ha₀q : G.Adj a₀ q) (hb₁q : G.Adj b₁ q)
    (hb₀q : ¬ G.Adj b₀ q) (hb₂q : ¬ G.Adj b₂ q) :
    False := by
  classical
  obtain ⟨hR₁, hR₂, hRdisj, hRcross⟩ := id hstep
  have ha₁A : a₁ ∈ A := hR₁.2.1
  have hb₁B : b₁ ∈ B := hR₁.2.2.1
  have ha₂A : a₂ ∈ A := hR₂.2.1
  have hb₂B : b₂ ∈ B := hR₂.2.2.1
  have hb₁R₁ : b₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hR₁.1).2
  have hb₂R₂ : b₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hR₂.1).2
  have hR₂S : ∀ x ∈ R₂, x ∈ A ∪ B ∪ C :=
    fun x hx => Thm114Aux.rung_mem_strip hR₂ x hx
  have ha₁b₁ : a₁ ≠ b₁ := by
    intro he
    exact hban.2.2.1.2.2 b₁ (Or.inl hb₁B) (he ▸ hban.2.2.1.2.1 a₁ ha₁A)
  have hqb₀ : q ≠ b₀ := by
    intro he
    exact hb₂q (by rw [he]; exact (hban.2.2.2.1.2.1 b₂ hb₂B).symm)
  have hqa₀ : q ≠ a₀ := ha₀q.ne.symm
  have hqR₀ : q ∉ R₀ := by
    intro hq
    by_cases ha : q = a₀
    · exact hqa₀ ha
    by_cases hb : q = b₀
    · exact hqb₀ hb
    exact hqF (hR₀F q ((PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hq, ha, hb⟩))
  have hqstairs : q ∉ staircaseVertices A C B R₀ := by
    rintro (hq | hq)
    · exact hqR₀ hq
    · exact hqS hq

  -- 10.4 supplies a neighbour of `q` on the second rung.
  obtain ⟨y₂, hy₂R₂, hqy₂⟩ :=
    Thm121Case3RightDiagonal.nbr_in_R2 G hG hK4 hprism A C B a₀ b₀ R₀ hban q
      hqstairs ha₀q.symm a₁ b₁ a₂ b₂ R₁ R₂ hstep b₁ hb₁R₁ ha₁b₁.symm hb₁q.symm

  -- A path from `q` to `b₀` with interior in `F`; deleting `q` gives the first
  -- of the three disjoint paths used to link `q` onto `{b₀,b₁,b₂}`.
  have hb₀F : b₀ ∉ F :=
    Thm114Aux.star_notMem_F hFanti (Or.inl (Or.inr hb₁B))
      (hban.2.2.2.1.2.1 b₁ hb₁B)
  obtain ⟨P, hP, hPint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hqF hb₀F hqFnbr hb₀Fnbr
  have hP3 : 3 ≤ P.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hP hqb₀ (fun h => hb₀q h.symm)
  have hP0 : IsPathFrom G (P.drop 1) (P[1]'(by omega)) b₀ := by
    refine ⟨PathBasics.isPathList_drop hP.1 (by omega), ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem (by omega)]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hP.2.2
  have hPzero : P[0]'(by omega) = q := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hqP0 : q ∉ P.drop 1 := by
    intro hmem
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hmem
    have hiP : 1 + i < P.length := by
      rw [List.length_drop] at hi
      omega
    have hget : (P.drop 1)[i]'hi = P[1 + i]'hiP := by
      simpa [Nat.add_comm] using (List.getElem_drop (l := P) (n := 1) hi)
    have heq : P[1 + i]'hiP = P[0]'(by omega) := by rw [← hget, hieq, hPzero]
    exact PathBasics.path_ne_of_ne_index hP.1 hiP (by omega) (by omega) heq
  have hP0sub : ∀ x ∈ P.drop 1, x ∈ F ∪ {b₀} := by
    intro x hx
    by_cases hxb : x = b₀
    · exact Or.inr hxb
    · refine Or.inl (hPint x ?_)
      exact (PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨List.mem_of_mem_drop hx, fun he => hqP0 (he ▸ hx), hxb⟩
  have hqP0nbr : ∃ x ∈ P.drop 1, G.Adj q x := by
    refine ⟨P[1]'(by omega), PathBasics.head_mem hP0.2.1, ?_⟩
    rw [← hPzero]
    exact PathBasics.path_adj_succ hP.1 (by omega)

  -- The suffix of `R₂` beginning at the chosen neighbour of `q` is the third path.
  obtain ⟨i₂, hi₂, hi₂y⟩ := List.mem_iff_getElem.mp hy₂R₂
  have hP2 : IsPathFrom G (R₂.drop i₂) (R₂[i₂]'hi₂) b₂ := by
    refine ⟨PathBasics.isPathList_drop hR₂.1.1 hi₂, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hi₂]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hR₂.1.2.2
  have hP2sub : ∀ x ∈ R₂.drop i₂, x ∈ R₂ := fun x hx => List.mem_of_mem_drop hx
  have hqP2nbr : ∃ x ∈ R₂.drop i₂, G.Adj q x := by
    refine ⟨R₂[i₂]'hi₂, PathBasics.head_mem hP2.2.1, ?_⟩
    rw [hi₂y]
    exact hqy₂

  have hb₀b₁ : G.Adj b₀ b₁ := hban.2.2.2.1.2.1 b₁ hb₁B
  have hb₀b₂ : G.Adj b₀ b₂ := hban.2.2.2.1.2.1 b₂ hb₂B
  have hb₁b₂ : G.Adj b₁ b₂ :=
    (hRcross b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
  have hlink : VertexCanBeLinkedOntoTriangle G q b₀ b₁ b₂ := by
    refine ⟨P.drop 1, [b₁], R₂.drop i₂,
      ⟨hP0.1, PathBasics.isPathList_singleton G b₁, hP2.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨Or.inr hP0.2.2, Or.inl rfl, Or.inr hP2.2.2⟩, ⟨?_, ?_, ?_⟩,
      ⟨hqP0nbr, ⟨b₁, by simp, hb₁q.symm⟩, hqP2nbr⟩⟩
    · intro x hx hx'
      simp only [List.mem_singleton] at hx'
      subst x
      rcases hP0sub b₁ hx with h | h
      · exact hFout b₁ h (Or.inl (Or.inr hb₁B))
      · exact hban.2.2.2.1.1 (h ▸ Or.inl (Or.inr hb₁B))
    · intro x hx hx'
      have hxS := hR₂S x (hP2sub x hx')
      rcases hP0sub x hx with h | h
      · exact hFout x h hxS
      · exact hban.2.2.2.1.1 (h ▸ hxS)
    · intro x hx hx'
      simp only [List.mem_singleton] at hx
      subst x
      exact hRdisj b₁ hb₁R₁ (hP2sub b₁ hx')
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      constructor
      · intro hadj
        rcases hP0sub x hx with h | h
        · exact absurd hadj (hFanti x h b₁ (Or.inl (Or.inr hb₁B)))
        · exact ⟨h, rfl⟩
      · rintro ⟨hx, -⟩
        rw [hx]
        exact hb₀b₁
    · intro x hx y hy
      have hyR₂ := hP2sub y hy
      constructor
      · intro hadj
        rcases hP0sub x hx with h | h
        · exact absurd hadj (hFanti x h y (hR₂S y hyR₂))
        · subst x
          refine ⟨rfl, ?_⟩
          rcases hR₂S y hyR₂ with (hyA | hyB) | hyC
          · exact absurd hadj (hban.2.2.2.1.2.2 y (Or.inl hyA))
          · exact hR₂.2.2.2.2.1 y hyR₂ hyB
          · exact absurd hadj (hban.2.2.2.1.2.2 y (Or.inr hyC))
      · rintro ⟨hx, hy⟩
        rw [hx, hy]
        exact hb₀b₂
    · intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst x
      have hyR₂ := hP2sub y hy
      constructor
      · intro hadj
        rcases (hRcross b₁ hb₁R₁ y hyR₂).mp hadj with h | h
        · exact absurd h.1.symm ha₁b₁
        · exact ⟨rfl, h.2⟩
      · rintro ⟨-, hy⟩
        rw [hy]
        exact hb₁b₂
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG q b₀ b₁ b₂ hlink with
    h | h | h
  · exact hb₀q h.1.symm
  · exact hb₀q h.1.symm
  · exact hb₂q h.2.symm

end Workspace.ProofLemmas.Thm114ClaimOne
