import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm182EdgeSetTake
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S13.Thm_13_7

/-!
# Small Roussel--Rubio consequences used in the proof of 18.5

This module contains only the exact balanced-pair consequence needed around the
three applications of 17.5 in 18.5.  It is deliberately independent of the
numbered declarations 17.2--17.5.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm185TripleRRSpecial

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parity consequence of 2.2--2.3 used in the first minimality step of
17.5.  The exceptional conclusion of 2.3 says that the two ends are the only
`X`-complete vertices of the ambient path.  If they are adjacent, the complete
edge set is a singleton; if they are nonadjacent, 2.2 contradicts the external
`X`-complete vertex which is anticomplete to the path. -/
theorem odd_complete_edges_of_complete_ends
    (G : SimpleGraph V) (hG : Berge G) (X : Set V) (hX : AnticonnectedSet G X)
    (p : List V) (p₁ pₙ : V) (hp : IsPathFrom G p p₁ pₙ)
    (hodd : Odd (pathLength p)) (hpX : ∀ w ∈ p, w ∉ X)
    (hp₁X : VertexComplete G p₁ X) (hpₙX : VertexComplete G pₙ X)
    (z : V) (hzX : VertexComplete G z X)
    (hzanti : VertexAnticomplete G z {w : V | w ∈ p}) :
    Odd {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
      e = s(u, v) ∧ EdgeComplete G X u v}.ncard := by
  classical
  let E : Set (Sym2 V) :=
    {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
      e = s(u, v) ∧ EdgeComplete G X u v}
  have hinfix : p <:+: p := (List.prefix_refl p).isInfix
  rcases (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hG X hX p
      (Or.inl hp.1) hpX).1 p p₁ pₙ (Or.inl ⟨hp.1, hinfix⟩) hp hp₁X hpₙX with
      hpar | honly
  · rw [Nat.odd_iff]
    change E.ncard % 2 = 1
    rw [hpar, Nat.odd_iff.mp hodd]
  · by_cases hadj : G.Adj p₁ pₙ
    · have hset : E = {s(p₁, pₙ)} := by
        ext e
        constructor
        · rintro ⟨u, hu, v, hv, rfl, hE⟩
          have hu' := honly u hu hE.2.1
          have hv' := honly v hv hE.2.2
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
          · exact False.elim (G.irrefl hE.1)
          · simp
          · simpa using Sym2.eq_swap (p₁, pₙ)
          · exact False.elim (G.irrefl hE.1)
        · intro he
          rw [Set.mem_singleton_iff] at he
          subst e
          exact ⟨p₁, (PathBasics.isPathFrom_ends_mem hp).1,
            pₙ, (PathBasics.isPathFrom_ends_mem hp).2,
            rfl, hadj, hp₁X, hpₙX⟩
      rw [show {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
          e = s(u, v) ∧ EdgeComplete G X u v} = E from rfl, hset]
      simp
    · have hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G X u v := by
        rintro ⟨u, hu, v, hv, hE⟩
        have hu' := honly u hu hE.2.1
        have hv' := honly v hv hE.2.2
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
        · exact G.irrefl hE.1
        · exact hadj hE.1
        · exact hadj hE.1.symm
        · exact G.irrefl hE.1
      obtain ⟨w, hw, hzw⟩ := _root_.Workspace.Statements.S02.SPGT.thm_2_2
        G hG X hX p p₁ pₙ hp hpX hodd hp₁X hpₙX hnoedge z hzX
      exact False.elim (hzanti w (PathBasics.interior_subset hw) hzw)

/-- If the total number of `X`-complete edges is even, then the last
`X`-complete vertex has even zero-based index.  Otherwise its initial segment
has odd length and the preceding lemma makes that same edge set odd. -/
theorem max_complete_index_even_of_even_edges
    (G : SimpleGraph V) (hG : Berge G) (X : Set V) (hX : AnticonnectedSet G X)
    (p : List V) (p₁ : V) (hp : IsPathList G p)
    (hhead : p.head? = some p₁) (hpX : ∀ w ∈ p, w ∉ X)
    (hp₁X : VertexComplete G p₁ X)
    (m : ℕ) (hm : m < p.length) (hmX : VertexComplete G (p[m]'hm) X)
    (hmax : ∀ (k : ℕ) (hk : k < p.length),
      VertexComplete G (p[k]'hk) X → k ≤ m)
    (z : V) (hzX : VertexComplete G z X)
    (hzanti : VertexAnticomplete G z {w : V | w ∈ p})
    (heven : Even {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
      e = s(u, v) ∧ EdgeComplete G X u v}.ncard) :
    Even m := by
  rcases Nat.even_or_odd m with hmEven | hmOdd
  · exact hmEven
  · have hmpos : 0 < m := by
      rw [Nat.odd_iff] at hmOdd
      omega
    let q : List V := p.take (m + 1)
    have hqFrom₀ := PathBasics.isPathFrom_slice hp hmpos hm
    have hqFrom : IsPathFrom G q p₁ (p[m]'hm) := by
      have hpos : 0 < p.length := by omega
      have hp₀ : p[0]'hpos = p₁ := PathBasics.getElem_zero_of_head? hhead hpos
      simpa [q, hp₀] using hqFrom₀
    have hqlen : q.length = m + 1 := by simp [q]; omega
    have hqodd : Odd (pathLength q) := by
      rw [PathBasics.pathLength_eq, hqlen]
      simpa using hmOdd
    have hqX : ∀ w ∈ q, w ∉ X :=
      fun w hw => hpX w (List.take_subset _ _ hw)
    have hzantiq : VertexAnticomplete G z {w : V | w ∈ q} := by
      intro w hw
      exact hzanti w (List.take_subset _ _ hw)
    have hqOddEdges := odd_complete_edges_of_complete_ends
      G hG X hX q p₁ (p[m]'hm) hqFrom hqodd hqX hp₁X hmX z hzX hzantiq
    have hEq := Thm182EdgeSetTake.xed_eq_take G X p m hm hmax
    have hqEvenEdges : Even {e : Sym2 V | ∃ u ∈ q, ∃ v ∈ q,
        e = s(u, v) ∧ EdgeComplete G X u v}.ncard := by
      rw [← hEq]
      exact heven
    exact False.elim ((Nat.not_odd_iff_even.mpr hqEvenEdges) hqOddEdges)

/-- A positive even path cannot have its two ends as the unique complete
vertices for two disjoint complete anticonnected sets when a common complete
vertex is anticomplete to the path.  Indeed, 13.7 reduces the path to three
vertices and supplies an odd antipath through one of the two sets; the common
vertex makes both relevant pairs balanced by 2.6. -/
theorem no_even_unique_ends (G : SimpleGraph V) (hG : InF5 G)
    (A B : Set V) (hAB : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAa : AnticonnectedSet G A) (hBa : AnticonnectedSet G B)
    (hcompl : Complete G A B)
    (P : List V) (a b : V) (hP : IsPathList G P)
    (heven : Even (pathLength P)) (hpos : 0 < pathLength P)
    (hhead : P.head? = some a) (hlast : P.getLast? = some b)
    (hout : ∀ w ∈ P, w ∉ A ∪ B)
    (hAuniq : ∀ w ∈ P, (VertexComplete G w A ↔ w = a))
    (hBuniq : ∀ w ∈ P, (VertexComplete G w B ↔ w = b))
    (z : V) (hzAB : z ∉ A ∪ B) (hzP : z ∉ P)
    (hzcomp : VertexComplete G z (A ∪ B))
    (hzanti : VertexAnticomplete G z {w : V | w ∈ P}) : False := by
  classical
  obtain ⟨hlen2, c, hshape, Q, R, hQ, hR, hxor⟩ :=
    _root_.Workspace.Statements.S13.SPGT.thm_13_7 G hG A B hAB hAne hBne
      hAa hBa hcompl P a b hP heven hpos hhead hlast hAuniq hBuniq
  let S : Set V := {w : V | w ∈ P}
  have hSA : Disjoint S A := by
    rw [Set.disjoint_left]
    intro w hwS hwA
    exact hout w hwS (Or.inl hwA)
  have hSB : Disjoint S B := by
    rw [Set.disjoint_left]
    intro w hwS hwB
    exact hout w hwS (Or.inr hwB)
  have hzSA : z ∉ S ∪ A := by
    rintro (hzS | hzA)
    · exact hzP hzS
    · exact hzAB (Or.inl hzA)
  have hzSB : z ∉ S ∪ B := by
    rintro (hzS | hzB)
    · exact hzP hzS
    · exact hzAB (Or.inr hzB)
  have hzA : VertexComplete G z A := fun x hx => hzcomp x (Or.inl hx)
  have hzB : VertexComplete G z B := fun x hx => hzcomp x (Or.inr hx)
  have hzS : VertexAnticomplete G z S := by simpa [S] using hzanti
  have hbalA : SPGT.Balanced G S A :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hG.1.1 S A hSA z hzSA hzA hzS
  have hbalB : SPGT.Balanced G S B :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hG.1.1 S B hSB z hzSB hzB hzS
  have haS : a ∈ S := PathBasics.head_mem hhead
  have hbS : b ∈ S := PathBasics.getLast_mem hlast
  have hcS : c ∈ S := by
    change c ∈ P
    rw [hshape]
    simp
  have hac : G.Adj a c := by
    rw [hshape] at hP
    simpa using PathBasics.path_adj_succ hP (i := 0) (by simp)
  have hcb : G.Adj c b := by
    rw [hshape] at hP
    simpa using PathBasics.path_adj_succ hP (i := 1) (by simp)
  rcases hxor with ⟨hQodd, hRnot⟩ | ⟨hRodd, hQnot⟩
  · exact hbalA.2 c b Q hcS hbS hcb hQ.1 hQ.2 hQodd
  · exact hbalB.2 a c R haS hcS hac hR.1 hR.2 hRodd

/-- Parity form of `no_even_unique_ends`: a positive path with unique complete
ends for the two sides has odd length. -/
theorem odd_of_unique_ends (G : SimpleGraph V) (hG : InF5 G)
    (A B : Set V) (hAB : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAa : AnticonnectedSet G A) (hBa : AnticonnectedSet G B)
    (hcompl : Complete G A B)
    (P : List V) (a b : V) (hP : IsPathList G P)
    (hpos : 0 < pathLength P)
    (hhead : P.head? = some a) (hlast : P.getLast? = some b)
    (hout : ∀ w ∈ P, w ∉ A ∪ B)
    (hAuniq : ∀ w ∈ P, (VertexComplete G w A ↔ w = a))
    (hBuniq : ∀ w ∈ P, (VertexComplete G w B ↔ w = b))
    (z : V) (hzAB : z ∉ A ∪ B) (hzP : z ∉ P)
    (hzcomp : VertexComplete G z (A ∪ B))
    (hzanti : VertexAnticomplete G z {w : V | w ∈ P}) :
    Odd (pathLength P) := by
  rcases Nat.even_or_odd (pathLength P) with heven | hodd
  · exact False.elim (no_even_unique_ends G hG A B hAB hAne hBne hAa hBa hcompl
      P a b hP heven hpos hhead hlast hout hAuniq hBuniq z hzAB hzP hzcomp hzanti)
  · exact hodd

end Workspace.ProofLemmas.Thm185TripleRRSpecial
