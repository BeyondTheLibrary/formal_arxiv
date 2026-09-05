/-  Proof attempt for statement 24.3 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 144).

    THE PAPER'S PROOF (paper/proofs/24_3.md, verbatim):

      "Proof.  Suppose such a vertex y exists.  By 24.2, n is odd, and therefore
       n >= 5.  Let Q be an antipath joining p_2, p_3 with interior in X.  Since Q can
       be completed to an antihole via p_3-p_n-p_2, it follows that Q has length 2, and
       so there exists x in X nonadjacent to p_2, p_3.  Since x is adjacent to p_n, we
       may choose i with 2 <= i <= n minimum such that x is adjacent to p_i.  Hence
       x-p_1-...-p_i-x is a hole of length >= 6, and y has three consecutive
       neighbours in it, contrary to G in F_11.  This proves 24.3."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "By 24.2, n is odd" is `thm_24_2` (proved) run contrapositively: if the path had
      odd *length* (= n-1) then some edge of it would be X-complete, but the only
      X-complete vertices of the path are its two ends (hypothesis `hint`), and those
      are non-adjacent because n >= 4.  So n-1 is even, n is odd, and with n >= 4 that
      gives n >= 5.
    * "Let Q be an antipath joining p_2, p_3 with interior in X" is
      `InducedPathExtraction.exists_antipath_interior_in`: p_2 and p_3 are not
      X-complete (they are interior vertices of the path), so each has a nonneighbour
      in X, and X is anticonnected.
    * "Since Q can be completed to an antihole via p_3-p_n-p_2, it follows that Q has
      length 2" is `PrismBasics.isHoleList_of_path_add_vertex` applied at `Gᶜ` with the
      extra vertex p_n: p_n is X-complete, hence G-adjacent to every interior vertex of
      Q, hence Gᶜ-nonadjacent to it, and p_n is Gᶜ-adjacent to p_2 and p_3 because on an
      induced path with n >= 5 the last vertex is G-nonadjacent to the second and third.
      `G in F_11` forces that antihole to have length 4, i.e. `pathLength Q = 2`.
    * "so there exists x in X nonadjacent to p_2, p_3": Q is then the three-vertex
      antipath p_2-x-p_3, and its only interior vertex x lies in X.
    * "we may choose i minimum" is `Nat.find` on `{k | x adjacent to p[k]}`, nonempty
      because p_n is X-complete.  Minimality gives i >= 4 (0-indexed: k >= 3), since x
      is nonadjacent to p_2 and p_3.
    * "x-p_1-...-p_i-x is a hole of length >= 6" is
      `PrismBasics.isHoleList_of_path_add_vertex` at `G`, closing the initial segment
      `p.take (k+1)` through x; there are no chords precisely by the minimality of k.
      Its length is k+2 >= 5, and Berge (from F_11) makes it even, hence >= 6.
    * "y has three consecutive neighbours in it, contrary to G in F_11" is the `F_10`
      clause of `InF11`: y is adjacent to x (y is X-complete), to p_1 and to p_2, and
      x, p_1, p_2 are the first three vertices of that hole.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleArc
import Workspace.Statements.S24.Thm_24_2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S24

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **24.3** (printed p. 144).

PAPER: *"Let `G ∈ F₁₁`.  Let `X ⊆ V(G)` be nonempty and anticonnected, and let
`p₁-⋯-pₙ` be a path of `G \ X` with `n ≥ 4`, such that `p₁, pₙ` are `X`-complete
and `p₂, …, pₙ₋₁` are not.  There is no vertex
`y ∈ V(G) \ (X ∪ {p₁, …, pₙ})` such that `y` is `X`-complete and adjacent to
`p₁, p₂`."*

Transcription notes.

* *"a path of `G \ X`"* is `IsPathList G p` together with `∀ w ∈ p, w ∉ X` (see
  `CONVENTIONS.md`: inducedness in `G \ X` and in `G` agree for vertex sets
  avoiding `X`).
* *"`n ≥ 4`"*, with `n` the number of vertices `p₁, …, pₙ`, is `4 ≤ p.length`.
* *"`p₂, …, pₙ₋₁` are not [`X`-complete]"* is exactly the statement about
  `SPGT.interior p`, the paper's `P*`.
* *"`y ∈ V(G) \ (X ∪ {p₁,…,pₙ})`"* is `y ∉ X ∧ y ∉ p`. -/
theorem thm_24_3 (G : SimpleGraph V) (hG : InF11 G)
    (X : Set V) (hXne : X.Nonempty) (hX : AnticonnectedSet G X)
    (p : List V) (p₁ p₂ pₙ : V)
    (hp : IsPathList G p) (hpX : ∀ w ∈ p, w ∉ X) (hn : 4 ≤ p.length)
    (hhead : p.head? = some p₁) (hsnd : p.tail.head? = some p₂)
    (hlast : p.getLast? = some pₙ)
    (hp₁X : VertexComplete G p₁ X) (hpₙX : VertexComplete G pₙ X)
    (hint : ∀ w ∈ SPGT.interior p, ¬ VertexComplete G w X) :
    ¬ ∃ y : V, y ∉ X ∧ y ∉ p ∧ VertexComplete G y X ∧ G.Adj y p₁ ∧ G.Adj y p₂ := by
  rintro ⟨y, hyX, hyp, hyXc, hyp₁, hyp₂⟩
  have hnd : p.Nodup := PathBasics.path_nodup hp
  have hpos : 0 < p.length := by omega
  have hadj : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
      (G.Adj (p[i]'hi) (p[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) :=
    fun i j hi hj => PathBasics.path_adj_iff hp hi hj
  have hgc : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length), i = j →
      (p[i]'hi) = (p[j]'hj) := by
    intro i j hi hj h
    subst h
    rfl
  have hP0 : (p[0]'hpos) = p₁ := PathBasics.getElem_zero_of_head? hhead hpos
  have hPn : (p[p.length - 1]'(by omega)) = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast hpos
  have hP1 : (p[1]'(by omega)) = p₂ := by
    have h := hsnd
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)] at h
    have h' : (p.tail[0]'(by simp; omega)) = p₂ := Option.some_inj.mp h
    rw [← h']
    simp [List.getElem_tail]
  -- the only `X`-complete vertices of the path are its two ends
  have hends : ∀ (k : ℕ) (hk : k < p.length), VertexComplete G (p[k]'hk) X →
      k = 0 ∨ k = p.length - 1 := by
    intro k hk hcomp
    by_contra hcon
    push Not at hcon
    exact hint _ (PathBasics.getElem_mem_interior hp hk (by omega) (by omega)) hcomp
  -- "By 24.2, `n` is odd, and therefore `n ≥ 5`."
  have hnotodd : ¬ Odd (pathLength p) := by
    intro hodd
    obtain ⟨a, hamem, b, hbmem, hab, haX, hbX⟩ :=
      _root_.Workspace.Statements.S24.SPGT.thm_24_2 G hG p p₁ pₙ ⟨hp, hhead, hlast⟩ hodd X hX
        hp₁X hpₙX
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hamem
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hbmem
    have hie := hends i hi (by rw [hia]; exact haX)
    have hje := hends j hj (by rw [hjb]; exact hbX)
    have hadjij : (i + 1 = j ∨ j + 1 = i) := by
      rw [← hadj i j hi hj, hia, hjb]
      exact hab
    omega
  have hodd5 : 5 ≤ p.length := by
    have hpe := PathBasics.pathLength_eq p
    rcases Nat.even_or_odd (pathLength p) with he | ho
    · rcases he with ⟨m, hm⟩
      omega
    · exact absurd ho hnotodd
  -- "Let `Q` be an antipath joining `p₂, p₃` with interior in `X`."
  have hp2int : (p[1]'(by omega)) ∈ SPGT.interior p :=
    PathBasics.getElem_mem_interior hp (by omega) (by omega) (by omega)
  have hp3int : (p[2]'(by omega)) ∈ SPGT.interior p :=
    PathBasics.getElem_mem_interior hp (by omega) (by omega) (by omega)
  have hp2nc : ∃ w ∈ X, ¬ G.Adj (p[1]'(by omega)) w := by
    by_contra hc
    push Not at hc
    exact hint _ hp2int hc
  have hp3nc : ∃ w ∈ X, ¬ G.Adj (p[2]'(by omega)) w := by
    by_contra hc
    push Not at hc
    exact hint _ hp3int hc
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hX
      (hpX _ (List.getElem_mem (by omega))) (hpX _ (List.getElem_mem (by omega))) hp2nc hp3nc
  have hQ' : IsPathFrom Gᶜ Q (p[1]'(by omega)) (p[2]'(by omega)) := hQ
  -- "Since `Q` can be completed to an antihole via `p₃-pₙ-p₂`, it follows that `Q` has length 2."
  have hQ12 : p[1]'(by omega) ≠ p[2]'(by omega) := by
    intro h
    have := hnd.getElem_inj_iff.mp h
    omega
  have hQlen1 : pathLength Q ≠ 1 := by
    intro h1
    refine (PathBasics.isPathFrom_ends_adj_of_length_one hQ' h1).2 ?_
    exact (hadj 1 2 (by omega) (by omega)).mpr (Or.inl rfl)
  have hQlen0 : pathLength Q ≠ 0 := by
    intro h0
    have hl1 : Q.length = 1 := by
      have := PathBasics.pathLength_eq Q
      have := PathBasics.path_length_pos hQ'.1
      omega
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hl1
    rw [hw] at hQ'
    have h2 : w = p[1]'(by omega) := by simpa using hQ'.2.1
    have h3 : w = p[2]'(by omega) := by simpa using hQ'.2.2
    exact hQ12 (h2.symm.trans h3)
  have hQ2 : 2 ≤ pathLength Q := by omega
  have hQmem : ∀ w ∈ Q, w = p[1]'(by omega) ∨ w = p[2]'(by omega) ∨ w ∈ X := by
    intro w hw
    by_cases h1 : w = p[1]'(by omega)
    · exact Or.inl h1
    by_cases h2 : w = p[2]'(by omega)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (hQint w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ').mpr ⟨hw, h1, h2⟩)))
  have hpnQ : pₙ ∉ Q := by
    intro hw
    rcases hQmem pₙ hw with h | h | h
    · rw [← hPn] at h
      have := hnd.getElem_inj_iff.mp h
      omega
    · rw [← hPn] at h
      have := hnd.getElem_inj_iff.mp h
      omega
    · exact hpX pₙ (by rw [← hPn]; exact List.getElem_mem _) h
  have hanti : IsHoleList Gᶜ (pₙ :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_vertex hQ' hQ2 ?_ ?_ hpnQ ?_
    · refine ⟨?_, ?_⟩
      · rw [← hPn]
        intro h
        have := hnd.getElem_inj_iff.mp h
        omega
      · rw [← hPn]
        intro h
        rw [hadj (p.length - 1) 1 (by omega) (by omega)] at h
        omega
    · refine ⟨?_, ?_⟩
      · rw [← hPn]
        intro h
        have := hnd.getElem_inj_iff.mp h
        omega
      · rw [← hPn]
        intro h
        rw [hadj (p.length - 1) 2 (by omega) (by omega)] at h
        omega
    · intro w hw h
      exact h.2 (hpₙX w (hQint w hw))
  have hQ2eq : pathLength Q = 2 := by
    have h4 := hG.2 (pₙ :: Q) hanti
    rw [PrismBasics.holeLength_cons pₙ (PathBasics.path_ne_nil hQ'.1)] at h4
    omega
  -- "so there exists `x ∈ X` nonadjacent to `p₂, p₃`"
  have hQ3 : Q.length = 3 := by
    have := PathBasics.pathLength_eq Q
    have := PathBasics.path_length_pos hQ'.1
    omega
  obtain ⟨a, x, b, hQeq⟩ := PrismBasics.length_eq_three hQ3
  subst hQeq
  have hxX : x ∈ X := hQint x (by simp [SPGT.interior])
  have hQa : a = p[1]'(by omega) := by simpa using hQ'.2.1
  have hQb : b = p[2]'(by omega) := by simpa using hQ'.2.2
  have hcadj1 : Gᶜ.Adj a x := (hQ'.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)
  have hcadj2 : Gᶜ.Adj b x := (hQ'.1.2.2 2 1 (by simp) (by simp)).mpr (Or.inr rfl)
  have hxa2 : ¬ G.Adj (p[1]'(by omega)) x := by rw [← hQa]; exact hcadj1.2
  have hxb3 : ¬ G.Adj (p[2]'(by omega)) x := by rw [← hQb]; exact hcadj2.2
  -- "Since `x` is adjacent to `pₙ`, we may choose `i` minimum with `x` adjacent to `pᵢ`."
  classical
  have hexk : ∃ k : ℕ, ∃ h : k < p.length, 1 ≤ k ∧ G.Adj x (p[k]'h) := by
    refine ⟨p.length - 1, by omega, by omega, ?_⟩
    rw [hPn]
    exact (hpₙX x hxX).symm
  obtain ⟨k, hk, hk1, hxk, hkmin⟩ :
      ∃ k : ℕ, ∃ h : k < p.length, 1 ≤ k ∧ G.Adj x (p[k]'h) ∧
        ∀ (m : ℕ) (hm : m < p.length), 1 ≤ m → G.Adj x (p[m]'hm) → k ≤ m := by
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec hexk
    exact ⟨Nat.find hexk, h1, h2, h3, fun m hm hm1 hm2 => Nat.find_min' hexk ⟨hm, hm1, hm2⟩⟩
  have hk3 : 3 ≤ k := by
    by_contra hc
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with h | h
    · exact hxa2 (by rw [← hgc k 1 hk (by omega) h]; exact hxk.symm)
    · exact hxb3 (by rw [← hgc k 2 hk (by omega) h]; exact hxk.symm)
  -- "Hence `x-p₁-⋯-pᵢ-x` is a hole of length `≥ 6`."
  have htakepath : IsPathList G (p.take (k + 1)) := PathBasics.isPathList_take hp (by omega)
  have htakelen : (p.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
  have htakeget : ∀ (t : ℕ) (ht : t < (p.take (k + 1)).length),
      ((p.take (k + 1))[t]'ht) = (p[t]'(by omega)) := fun t ht => List.getElem_take
  have htakehead : (p.take (k + 1)).head? = some (p[0]'hpos) := by
    rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
      List.getElem?_eq_getElem hpos]
  have htakelast : (p.take (k + 1)).getLast? = some (p[k]'hk) := by
    rw [List.getLast?_take, if_neg (by omega)]
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hk, Option.some_or]
  have htakefrom : IsPathFrom G (p.take (k + 1)) (p[0]'hpos) (p[k]'hk) :=
    ⟨htakepath, htakehead, htakelast⟩
  have hxtake : x ∉ p.take (k + 1) := fun h => hpX x (List.take_subset _ _ h) hxX
  have hhole : IsHoleList G (x :: p.take (k + 1)) := by
    refine PrismBasics.isHoleList_of_path_add_vertex htakefrom ?_ ?_ hxk hxtake ?_
    · rw [PathBasics.pathLength_eq, htakelen]
      omega
    · rw [hP0]
      exact (hp₁X x hxX).symm
    · intro w hw hadjxw
      rw [PathBasics.mem_interior_iff_of_pathFrom htakefrom] at hw
      obtain ⟨hwmem, hw0, hwk⟩ := hw
      obtain ⟨t, ht, htw⟩ := List.getElem_of_mem hwmem
      have htk : t < k + 1 := by rw [htakelen] at ht; omega
      have htv : (p[t]'(by omega)) = w := by rw [← htakeget t ht]; exact htw
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h1
        · exfalso
          apply hw0
          rw [← htw, htakeget t ht]
          exact hgc t 0 (by omega) hpos h0
        · exact h1
      have htne : t ≠ k := by
        intro h
        apply hwk
        rw [← htw, htakeget t ht]
        exact hgc t k (by omega) hk h
      have := hkmin t (by omega) ht1 (by rw [htv]; exact hadjxw)
      omega
  -- "and `y` has three consecutive neighbours in it, contrary to `G ∈ F₁₁`."
  have hlenhole : holeLength (x :: p.take (k + 1)) = k + 2 := by
    rw [holeLength, List.length_cons, htakelen]
  have hberge : Berge G := hG.1.1.1.1.1.1.1.1
  have hhole6 : 6 ≤ holeLength (x :: p.take (k + 1)) := by
    have heven := hberge.1 _ hhole
    rcases heven with ⟨m, hm⟩
    omega
  refine hG.1.2.1 (x :: p.take (k + 1)) hhole hhole6
    ⟨y, x, p₁, p₂, ⟨0, ?_⟩, hyXc x hxX, hyp₁, hyp₂⟩
  rw [List.rotate_zero]
  refine HoleArc.prefix_three (by rw [List.length_cons, htakelen]; omega) rfl ?_ ?_
  · simp only [List.getElem_cons_succ]
    rw [htakeget 0 (by omega), hP0]
  · simp only [List.getElem_cons_succ]
    rw [htakeget 1 (by omega), hP1]

end SPGT

end Workspace.Statements.S24
