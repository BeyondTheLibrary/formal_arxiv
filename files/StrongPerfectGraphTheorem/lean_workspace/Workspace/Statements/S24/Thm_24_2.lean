/-  Proof attempt for statement 24.2 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 143).

    THE PAPER'S PROOF (paper/proofs/24_2.md, verbatim):

      "Proof.  Suppose not; then from 13.6, P has length 3 (let its vertices be
       p_1, p_2, p_3, p_4 in order) and p_2, p_3 are joined by an antipath Q with
       interior in X.  But then p_2-Q-p_3-p_1-p_4-p_2 is an antihole of length > 4, a
       contradiction.  This proves 24.2."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "from 13.6" is `thm_13_6` (proved).  13.6 carries the published hypothesis
      `X subseteq V(G) \ V(P)`, which 24.2 does *not* state; it is derived here
      (`hXP`) rather than assumed: a vertex of `X` on `P` would be adjacent to both
      ends of `P`, and on an induced path the only vertex adjacent to both ends of a
      path with >= 2 vertices sits at index 1 and at index n-2 at once, forcing
      n = 3, i.e. `pathLength P = 2` -- contradicting `Odd (pathLength P)`.
    * "P has length 3 ... p_2, p_3 are joined by an antipath Q with interior in X" is
      the second alternative of 13.6; `P` is destructured as the literal
      `[p1, p2, p3, p4]` and `SPGT.interior [p1,p2,p3,p4] = [p2,p3]` is `rfl`.
    * "p_2-Q-p_3-p_1-p_4-p_2 is an antihole" is
      `PrismBasics.isHoleList_of_path_add_two_vertices` applied at `Gᶜ`, with the
      path `Q` (from p_2 to p_3) and the two extra vertices s = p_4 (attached at p_2)
      and t = p_1 (attached at p_3); the lemma produces `t :: s :: Q`, i.e. the cycle
      p_1-p_4-p_2-Q-p_3-p_1, which is the paper's cycle read from a different
      starting point.  The chords are absent exactly because p_1 and p_4 are the ends
      of P, hence `X`-complete, hence *G*-adjacent to every interior vertex of Q.
    * "of length > 4" : `Q` has odd length and cannot have length 1 (its ends p_2, p_3
      are adjacent in `G`), so its length is >= 3 and the antihole has length >= 6.
      `G in F_11` says every antihole has length 4 -- the contradiction.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S13.Thm_13_6

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


/-- **24.2** (printed p. 143), introduced by *"We begin with a further strengthening
of 13.6, as follows."*

PAPER: *"Let `G ∈ F₁₁`, and let `P` be a path in `G` with odd length.  Let
`X ⊆ V(G)` be anticonnected, such that both ends of `P` are `X`-complete.  Then
some edge of `P` is `X`-complete."*

Transcription notes.

* *"a path in `G` with odd length"* is `IsPathFrom G P u v` (which contains
  `IsPathList G P`, and names the two ends `u, v`) together with
  `Odd (pathLength P)`.
* *"`X ⊆ V(G)`"* is vacuous for a `Set V`; `X` is **not** assumed nonempty, nor
  disjoint from `V(P)` — the paper assumes neither.
* For *"some edge of `P` is `X`-complete"* see the module docstring. -/
theorem thm_24_2 (G : SimpleGraph V) (hG : InF11 G)
    (P : List V) (u v : V) (hP : IsPathFrom G P u v) (hodd : Odd (pathLength P))
    (X : Set V) (hX : AnticonnectedSet G X)
    (huX : VertexComplete G u X) (hvX : VertexComplete G v X) :
    ∃ a ∈ P, ∃ b ∈ P, EdgeComplete G X a b := by
  by_contra hcon
  have hpl : IsPathList G P := hP.1
  have hnd : P.Nodup := PathBasics.path_nodup hpl
  have hlenP : 2 ≤ P.length := by
    have h1 := PathBasics.pathLength_eq P
    have h2 := PathBasics.path_length_pos hpl
    rcases hodd with ⟨k, hk⟩
    omega
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hP0 : (P[0]'h0lt) = u := PathBasics.getElem_zero_of_head? hP.2.1 h0lt
  have hPn : (P[P.length - 1]'hnlt) = v := PathBasics.getElem_last_of_getLast? hP.2.2 h0lt
  have hadjP : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length),
      (G.Adj (P[i]'hi) (P[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) :=
    fun i j hi hj => PathBasics.path_adj_iff hpl hi hj
  -- 13.6 needs `X ∩ V(P) = ∅`; here that is a consequence, not a hypothesis.
  have hXP : X ⊆ {w : V | w ∈ P}ᶜ := by
    intro x hxX hxP
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxP
    have hux : G.Adj (P[0]'h0lt) (P[k]'hk) := by rw [hP0, hkx]; exact huX x hxX
    have hvx : G.Adj (P[P.length - 1]'hnlt) (P[k]'hk) := by rw [hPn, hkx]; exact hvX x hxX
    rw [hadjP 0 k h0lt hk] at hux
    rw [hadjP (P.length - 1) k hnlt hk] at hvx
    have hpe := PathBasics.pathLength_eq P
    rcases hodd with ⟨m, hm⟩
    omega
  -- "from 13.6"
  have hF5 : InF5 G := hG.1.1.1.1.1.1
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5 P u v hP hodd X hXP hX huX hvX
    with h1 | ⟨hlen3, c, d, hcd, Q, hQ, hQodd, hQint⟩
  · exact hcon h1
  -- "P has length 3 (let its vertices be p₁, p₂, p₃, p₄ in order)"
  have hP4 : P.length = 4 := by
    have := PathBasics.pathLength_eq P
    omega
  obtain ⟨p1, p2, p3, p4, hPeq⟩ := PrismBasics.length_eq_four hP4
  have hint4 : SPGT.interior P = [p2, p3] := by rw [hPeq]; rfl
  have hcp2 : p2 = c ∧ p3 = d := by
    have h : ([p2, p3] : List V) = [c, d] := by rw [← hint4, hcd]
    simpa using h
  obtain ⟨rfl, rfl⟩ := hcp2
  -- the six adjacency facts along `P = [p₁, p₂, p₃, p₄]`
  have hg : ∀ (i : ℕ) (hi : i < P.length), (P[i]'hi) = ([p1, p2, p3, p4] : List V)[i]'(by
      rw [hPeq] at hi; exact hi) := by
    intro i hi
    congr 1
  have e01 : G.Adj p1 p2 := by
    have := (hadjP 0 1 (by omega) (by omega)).mpr (Or.inl rfl)
    rw [hg 0 (by omega), hg 1 (by omega)] at this
    exact this
  have e12 : G.Adj p2 p3 := by
    have := (hadjP 1 2 (by omega) (by omega)).mpr (Or.inl rfl)
    rw [hg 1 (by omega), hg 2 (by omega)] at this
    exact this
  have e23 : G.Adj p3 p4 := by
    have := (hadjP 2 3 (by omega) (by omega)).mpr (Or.inl rfl)
    rw [hg 2 (by omega), hg 3 (by omega)] at this
    exact this
  have n02 : ¬ G.Adj p1 p3 := by
    intro h
    have : G.Adj (P[0]'(by omega)) (P[2]'(by omega)) := by
      rw [hg 0 (by omega), hg 2 (by omega)]; exact h
    rw [hadjP 0 2 (by omega) (by omega)] at this
    omega
  have n03 : ¬ G.Adj p1 p4 := by
    intro h
    have : G.Adj (P[0]'(by omega)) (P[3]'(by omega)) := by
      rw [hg 0 (by omega), hg 3 (by omega)]; exact h
    rw [hadjP 0 3 (by omega) (by omega)] at this
    omega
  have n13 : ¬ G.Adj p2 p4 := by
    intro h
    have : G.Adj (P[1]'(by omega)) (P[3]'(by omega)) := by
      rw [hg 1 (by omega), hg 3 (by omega)]; exact h
    rw [hadjP 1 3 (by omega) (by omega)] at this
    omega
  have hnd4 : ([p1, p2, p3, p4] : List V).Nodup := by rw [← hPeq]; exact hnd
  have d02 : p1 ≠ p3 := by rintro rfl; simp at hnd4
  have d03 : p1 ≠ p4 := by rintro rfl; simp at hnd4
  have d13 : p2 ≠ p4 := by rintro rfl; simp at hnd4
  have d01 : p1 ≠ p2 := by rintro rfl; simp at hnd4
  have d12 : p2 ≠ p3 := by rintro rfl; simp at hnd4
  have d23 : p3 ≠ p4 := by rintro rfl; simp at hnd4
  -- the ends of `P` are `p₁` and `p₄`
  have hu1 : u = p1 := by
    have h := hP.2.1
    rw [hPeq] at h
    simp at h
    exact h.symm
  have hv4 : v = p4 := by
    have h := hP.2.2
    rw [hPeq] at h
    simp at h
    exact h.symm
  have hp1c : VertexComplete G p1 X := by rw [← hu1]; exact huX
  have hp4c : VertexComplete G p4 X := by rw [← hv4]; exact hvX
  -- `Q` is an antipath from `p₂` to `p₃` of odd length `≥ 3`
  have hQ' : IsPathFrom Gᶜ Q p2 p3 := hQ
  have hQ1 : pathLength Q ≠ 1 := by
    intro h1
    exact (PathBasics.isPathFrom_ends_adj_of_length_one hQ' h1).2 e12
  have hQ3 : 3 ≤ pathLength Q := by
    rcases hQodd with ⟨m, hm⟩
    omega
  have hQmem : ∀ w ∈ Q, w = p2 ∨ w = p3 ∨ w ∈ X := by
    intro w hw
    by_cases hw2 : w = p2
    · exact Or.inl hw2
    by_cases hw3 : w = p3
    · exact Or.inr (Or.inl hw3)
    · exact Or.inr (Or.inr (hQint w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ').mpr ⟨hw, hw2, hw3⟩)))
  -- `p₁` and `p₄` lie outside `X` (each is `X`-complete) and outside `Q`
  have hp1X : p1 ∉ X := fun h => G.irrefl (hp1c p1 h)
  have hp4X : p4 ∉ X := fun h => G.irrefl (hp4c p4 h)
  have hp1Q : p1 ∉ Q := by
    intro hw
    rcases hQmem p1 hw with h | h | h
    · exact d01 h
    · exact d02 h
    · exact hp1X h
  have hp4Q : p4 ∉ Q := by
    intro hw
    rcases hQmem p4 hw with h | h | h
    · exact d13 h.symm
    · exact d23 h.symm
    · exact hp4X h
  -- "p₂-Q-p₃-p₁-p₄-p₂ is an antihole"
  have hhole : IsHoleList Gᶜ (p1 :: p4 :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hQ' (by omega)
      ⟨d13.symm, fun h => n13 h.symm⟩ ⟨d02, n02⟩ ⟨d03.symm, fun h => n03 h.symm⟩
      hp4Q hp1Q ?_ ?_ ?_ ?_
    · exact fun h => h.2 e23.symm
    · exact fun h => h.2 e01
    · intro x hx h
      exact h.2 (hp4c x (hQint x hx))
    · intro x hx h
      exact h.2 (hp1c x (hQint x hx))
  have hanti : IsAntiholeList G (p1 :: p4 :: Q) := hhole
  have h4 := hG.2 (p1 :: p4 :: Q) hanti
  rw [PrismBasics.holeLength_cons_cons p4 p1 (PathBasics.path_ne_nil hQ'.1)] at h4
  omega


end SPGT

end Workspace.Statements.S24
