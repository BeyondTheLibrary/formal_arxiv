/-  Proof attempt for statement 24.6 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 145).

    THE PAPER'S PROOF (paper/proofs/24_6.md, verbatim):

      "Proof.  Let C be the hole with vertices p_1, ..., p_{n+2} in order, and assume
       some z in V(G) \ V(C) is adjacent to p_{n+1}, p_{n+2}.  By 24.5, taking
       X = {p_{n+1}} and Y = {p_{n+2}} we deduce that z is adjacent to at least one of
       p_1, p_n.  Since G in F11 it follows that C has length 4.  This proves 24.6."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "Let C be the hole with vertices p_1, ..., p_{n+2} in order" is a *renumbering*:
      the paper puts the two adjacent neighbours of z at the end of the cyclic order.
      In Lean that is a rotation, done in `part1`: the two neighbours are `C[i]` and
      `C[(i+1) % C.length]` (adjacent vertices of a hole are cyclically consecutive),
      and `C.rotate (i + 2)` carries them to the last two positions.  `key` is the
      whole argument for a hole already in that position.
    * "taking X = {p_{n+1}} and Y = {p_{n+2}}" is `thm_24_5` applied to the two
      singletons, with the path `p_1-...-p_n` being `cyc.take (M - 2)`, the hole minus
      its last two vertices (`hole_take_isPathList`: dropping one vertex of the hole
      removes the wrap-around edge, so what is left is an induced path).  `p_1` is the
      unique `{p_{n+2}}`-complete vertex of that path and `p_n` the unique
      `{p_{n+1}}`-complete one, because on a hole each vertex has exactly two
      neighbours.
    * "we deduce that z is adjacent to at least one of p_1, p_n" is `hzend`, the
      contrapositive of 24.5's conclusion.  It immediately gives the second half of
      24.6's conclusion -- z has a *third* neighbour on C, namely p_1 or p_n.
    * "Since G in F11 it follows that C has length 4" is the `F_10` clause of `InF11`
      (printed p. 7: "for every hole C in G of length >= 6, no vertex of G has three
      consecutive neighbours in C"): z is adjacent to p_{n+1}, p_{n+2} and to one of
      p_1, p_n, and in each case those three are cyclically consecutive on C.  So C
      has length <= 5; and G is Berge (F11 <= F10 <= ... <= F3, whose first conjunct
      is `Berge`), so its holes have even length, hence exactly 4.
    * The closing sentence "In particular, G has no antipath of length 4" is deduced
      from the first half, exactly as the word "In particular" indicates.  For an
      antipath r0-r1-r2-r3-r4 the complement edges are the six non-consecutive pairs,
      and `[r3, r1, r4, r0]` is then a hole of G on which r2 has the two adjacent
      neighbours r4, r0 -- and no third neighbour, since r2 r1 and r2 r3 are edges of
      the antipath.  That contradicts the first half.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S24.Thm_24_5

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S24

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-! ### Small helpers -/

private theorem berge_of_inF11 {G : SimpleGraph V} (hG : InF11 G) : Berge G :=
  hG.1.1.1.1.1.1.1.1

private theorem anticonnected_singleton {G : SimpleGraph V} (x : V) :
    AnticonnectedSet G ({x} : Set V) := by
  intro a b
  have h : a = b := Subtype.ext (a.2.trans b.2.symm)
  rw [h]

/-- The first `m` vertices of a hole form an induced path, as long as at least one vertex of the
hole is left out (so that the wrap-around edge is not among them). -/
private theorem hole_take_isPathList {G : SimpleGraph V} {c : List V} (hc : IsHoleList G c)
    {m : ℕ} (hm2 : 2 ≤ m) (hm : m + 1 ≤ c.length) : IsPathList G (c.take m) := by
  obtain ⟨hlen4, hnd, hadj⟩ := hc
  refine ⟨?_, List.Nodup.sublist (List.take_sublist m c) hnd, ?_⟩
  · intro h
    have h0 : (c.take m).length = 0 := by rw [h]; rfl
    rw [List.length_take] at h0
    omega
  · intro i j hi hj
    have hilt : i < min m c.length := by rw [← List.length_take]; exact hi
    have hjlt : j < min m c.length := by rw [← List.length_take]; exact hj
    have hi' : i < c.length := by omega
    have hj' : j < c.length := by omega
    rw [List.getElem_take, List.getElem_take, hadj i j hi' hj']
    have e1 : (i + 1) % c.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    have e2 : (j + 1) % c.length = j + 1 := Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    omega

/-- Three named vertices at positions `0, 1, 2` of a list form a prefix of it. -/
private theorem prefix_three {l : List V} {x y z : V} (h : 3 ≤ l.length)
    (h0 : l[0]'(by omega) = x) (h1 : l[1]'(by omega) = y) (h2 : l[2]'(by omega) = z) :
    [x, y, z] <+: l := by
  subst h0
  subst h1
  subst h2
  match l, h with
  | (a :: b :: c :: t), _ => exact ⟨t, by simp⟩

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_24_6 (G : SimpleGraph V) (hG : InF11 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G) :
    (∀ C : List V, IsHoleList G C →
        ∀ z a b : V, z ∉ C → a ∈ C → b ∈ C →
          G.Adj z a → G.Adj z b → G.Adj a b →
            holeLength C = 4 ∧ ∃ c ∈ C, c ≠ a ∧ c ≠ b ∧ G.Adj z c) ∧
    (¬ ∃ q : List V, IsAntipathList G q ∧ pathLength q = 4) := by
  have hberge : Berge G := berge_of_inF11 hG
  -- THE MAIN CLAIM, for a hole whose last two vertices are the two adjacent neighbours of `z`.
  have key : ∀ (cyc : List V), IsHoleList G cyc → ∀ z u v : V, z ∉ cyc →
      (∀ h : cyc.length - 2 < cyc.length, (cyc[cyc.length - 2]'h) = u) →
      (∀ h : cyc.length - 1 < cyc.length, (cyc[cyc.length - 1]'h) = v) →
      G.Adj z u → G.Adj z v →
      holeLength cyc = 4 ∧ ∃ w ∈ cyc, w ≠ u ∧ w ≠ v ∧ G.Adj z w := by
    intro cyc hc z u v hzc hu hv hzu hzv
    have hM : 4 ≤ cyc.length := HoleBasics.hole_length_ge_four hc
    have hnd : cyc.Nodup := HoleBasics.hole_nodup hc
    have hadj := hc.2.2
    have hgc : ∀ (i j : ℕ) (hi : i < cyc.length) (hj : j < cyc.length), i = j →
        (cyc[i]'hi) = (cyc[j]'hj) := by
      intro i j hi hj h
      subst h
      rfl
    set M := cyc.length with hMdef
    have hu' : (cyc[M - 2]'(by omega)) = u := hu (by omega)
    have hv' : (cyc[M - 1]'(by omega)) = v := hv (by omega)
    -- the path `p₁-⋯-pₙ`, i.e. the hole minus its last two vertices
    have hppath : IsPathList G (cyc.take (M - 2)) := hole_take_isPathList hc (by omega) (by omega)
    have hplen : (cyc.take (M - 2)).length = M - 2 := by rw [List.length_take]; omega
    have hpget : ∀ (t : ℕ) (ht : t < (cyc.take (M - 2)).length),
        ((cyc.take (M - 2))[t]'ht) = (cyc[t]'(by omega)) := by
      intro t ht
      exact List.getElem_take
    have hpmem : ∀ w ∈ cyc.take (M - 2), ∃ (t : ℕ) (ht : t < cyc.length),
        t < M - 2 ∧ (cyc[t]'ht) = w := by
      intro w hw
      obtain ⟨t, htp, htw⟩ := List.getElem_of_mem hw
      have htm : t < M - 2 := hplen ▸ htp
      refine ⟨t, by omega, htm, ?_⟩
      rw [← hpget t htp]
      exact htw
    -- its two ends
    have hphead : (cyc.take (M - 2)).head? = some (cyc[0]'(by omega)) := by
      rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)]
    have hplast : (cyc.take (M - 2)).getLast? = some (cyc[M - 3]'(by omega)) := by
      rw [List.getLast?_take, if_neg (by omega)]
      have h3 : M - 2 - 1 = M - 3 := by omega
      rw [h3, List.getElem?_eq_getElem (by omega), Option.some_or]
    -- `u` and `v` are distinct, and distinct from every vertex of the path
    have hne_uv : u ≠ v := by
      rw [← hu', ← hv']
      intro h
      have := hnd.getElem_inj_iff.mp h
      omega
    have hpne : ∀ w ∈ cyc.take (M - 2), w ≠ u ∧ w ≠ v := by
      intro w hw
      obtain ⟨t, htlt, htm, htw⟩ := hpmem w hw
      constructor
      · rw [← htw, ← hu']
        intro h
        have := hnd.getElem_inj_iff.mp h
        omega
      · rw [← htw, ← hv']
        intro h
        have := hnd.getElem_inj_iff.mp h
        omega
    -- `z` is adjacent to at least one end of the path (this is 24.5)
    have hzend : G.Adj z (cyc[0]'(by omega)) ∨ G.Adj z (cyc[M - 3]'(by omega)) := by
      by_contra hcon
      push Not at hcon
      refine _root_.Workspace.Statements.S24.SPGT.thm_24_5 G hG hbsp ({v} : Set V) ({u} : Set V)
        (Set.disjoint_singleton.mpr (Ne.symm hne_uv)) (anticonnected_singleton v)
        (anticonnected_singleton u)
        (fun x hx y hy => by
          rw [show x = v from hx, show y = u from hy, ← hu', ← hv']
          exact ((hadj (M - 1) (M - 2) (by omega) (by omega)).mpr
            (Or.inr (by rw [Nat.mod_eq_of_lt (by omega)]; omega))))
        (cyc.take (M - 2)) (cyc[0]'(by omega)) (cyc[M - 3]'(by omega)) hppath ?_ (by omega)
        hphead hplast ?_ ?_ ⟨z, ?_, ?_, ?_, ?_, hcon.1, hcon.2⟩
      · -- vertices of the path avoid `X ∪ Y`
        intro w hw hmem
        rcases hmem with h | h
        · exact (hpne w hw).2 h
        · exact (hpne w hw).1 h
      · -- `p₁` is the unique `{v}`-complete vertex of the path
        intro w hw
        obtain ⟨t, htlt, htm, htw⟩ := hpmem w hw
        constructor
        · intro hcomp
          have hadjwv : G.Adj w v := hcomp v rfl
          rw [← htw, ← hv'] at hadjwv
          rw [hadj t (M - 1) (by omega) (by omega)] at hadjwv
          have e1 : (t + 1) % M = t + 1 := Nat.mod_eq_of_lt (by omega)
          have e2 : (M - 1 + 1) % M = 0 := by
            have : M - 1 + 1 = M := by omega
            rw [this, Nat.mod_self]
          rw [e1, e2] at hadjwv
          have ht0 : t = 0 := by omega
          rw [← htw]
          exact hgc _ _ _ _ ht0
        · intro he
          have ht0 : t = 0 := by
            rw [← htw] at he
            exact hnd.getElem_inj_iff.mp he
          intro x hx
          rw [show x = v from hx, ← htw, hgc t 0 htlt (by omega) ht0, ← hv']
          refine (hadj 0 (M - 1) (by omega) (by omega)).mpr (Or.inr ?_)
          have : M - 1 + 1 = M := by omega
          rw [this, Nat.mod_self]
      · -- `pₙ` is the unique `{u}`-complete vertex of the path
        intro w hw
        obtain ⟨t, htlt, htm, htw⟩ := hpmem w hw
        constructor
        · intro hcomp
          have hadjwu : G.Adj w u := hcomp u rfl
          rw [← htw, ← hu'] at hadjwu
          rw [hadj t (M - 2) (by omega) (by omega)] at hadjwu
          have e1 : (t + 1) % M = t + 1 := Nat.mod_eq_of_lt (by omega)
          have e2 : (M - 2 + 1) % M = M - 1 := by
            have h : M - 2 + 1 = M - 1 := by omega
            rw [h, Nat.mod_eq_of_lt (by omega)]
          rw [e1, e2] at hadjwu
          have ht0 : t = M - 3 := by omega
          rw [← htw]
          exact hgc _ _ _ _ ht0
        · intro he
          have ht0 : t = M - 3 := by
            rw [← htw] at he
            exact hnd.getElem_inj_iff.mp he
          intro x hx
          rw [show x = u from hx, ← htw, hgc t (M - 3) htlt (by omega) ht0, ← hu']
          refine (hadj (M - 3) (M - 2) (by omega) (by omega)).mpr (Or.inl ?_)
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
      · exact fun h => hzc (by rw [show z = v from h, ← hv']; exact List.getElem_mem _)
      · exact fun h => hzc (by rw [show z = u from h, ← hu']; exact List.getElem_mem _)
      · exact fun h => hzc (List.take_subset _ _ h)
      · intro x hx
        rcases hx with h | h
        · rw [show x = v from h]; exact hzv
        · rw [show x = u from h]; exact hzu
    -- the conclusion
    have hp₁mem : (cyc[0]'(by omega)) ∈ cyc := List.getElem_mem _
    have hpₙmem : (cyc[M - 3]'(by omega)) ∈ cyc := List.getElem_mem _
    have hp₁ne : (cyc[0]'(by omega)) ≠ u ∧ (cyc[0]'(by omega)) ≠ v := by
      constructor
      · rw [← hu']; intro h; have := hnd.getElem_inj_iff.mp h; omega
      · rw [← hv']; intro h; have := hnd.getElem_inj_iff.mp h; omega
    have hpₙne : (cyc[M - 3]'(by omega)) ≠ u ∧ (cyc[M - 3]'(by omega)) ≠ v := by
      constructor
      · rw [← hu']; intro h; have := hnd.getElem_inj_iff.mp h; omega
      · rw [← hv']; intro h; have := hnd.getElem_inj_iff.mp h; omega
    refine ⟨?_, ?_⟩
    · -- "Since `G ∈ F₁₁` it follows that `C` has length 4."
      by_contra hM4
      have hHL : holeLength cyc = M := rfl
      have hM6 : 6 ≤ M := by
        have heven : Even (holeLength cyc) := hberge.1 cyc hc
        rw [hHL] at heven hM4
        obtain ⟨k, hk⟩ := heven
        omega
      have hgc : ∀ (i j : ℕ) (hi : i < cyc.length) (hj : j < cyc.length), i = j →
          (cyc[i]'hi) = (cyc[j]'hj) := by
        intro i j hi hj h
        subst h
        rfl
      have hF10 := hG.1.2.1
      rcases hzend with hz1 | hz2
      · refine hF10 (cyc.rotate (M - 2)) (HoleBasics.isHoleList_rotate hc (M - 2)) ?_
          ⟨z, u, v, (cyc[0]'(by omega)), ⟨0, ?_⟩, hzu, hzv, hz1⟩
        · rw [HoleBasics.holeLength_rotate, hHL]; omega
        · rw [List.rotate_zero]
          refine prefix_three (by rw [List.length_rotate]; omega) ?_ ?_ ?_
          · simp only [List.getElem_rotate]
            exact (hgc _ _ _ _ (by
              rw [Nat.mod_eq_of_lt (show 0 + (M - 2) < cyc.length by omega)]; omega)).trans hu'
          · simp only [List.getElem_rotate]
            exact (hgc _ _ _ _ (by
              rw [Nat.mod_eq_of_lt (show 1 + (M - 2) < cyc.length by omega)]; omega)).trans hv'
          · simp only [List.getElem_rotate]
            exact hgc _ _ _ _ (by
              rw [show 2 + (M - 2) = cyc.length by omega, Nat.mod_self])
      · refine hF10 (cyc.rotate (M - 3)) (HoleBasics.isHoleList_rotate hc (M - 3)) ?_
          ⟨z, (cyc[M - 3]'(by omega)), u, v, ⟨0, ?_⟩, hz2, hzu, hzv⟩
        · rw [HoleBasics.holeLength_rotate, hHL]; omega
        · rw [List.rotate_zero]
          refine prefix_three (by rw [List.length_rotate]; omega) ?_ ?_ ?_
          · simp only [List.getElem_rotate]
            exact hgc _ _ _ _ (by
              rw [Nat.mod_eq_of_lt (show 0 + (M - 3) < cyc.length by omega)]; omega)
          · simp only [List.getElem_rotate]
            exact (hgc _ _ _ _ (by
              rw [Nat.mod_eq_of_lt (show 1 + (M - 3) < cyc.length by omega)]; omega)).trans hu'
          · simp only [List.getElem_rotate]
            exact (hgc _ _ _ _ (by
              rw [Nat.mod_eq_of_lt (show 2 + (M - 3) < cyc.length by omega)]; omega)).trans hv'
    · rcases hzend with hz1 | hz2
      · exact ⟨_, hp₁mem, hp₁ne.1, hp₁ne.2, hz1⟩
      · exact ⟨_, hpₙmem, hpₙne.1, hpₙne.2, hz2⟩
  -- FIRST CONCLUSION: rotate the hole so that the two adjacent neighbours of `z` are last.
  have part1 : ∀ C : List V, IsHoleList G C →
      ∀ z a b : V, z ∉ C → a ∈ C → b ∈ C →
        G.Adj z a → G.Adj z b → G.Adj a b →
          holeLength C = 4 ∧ ∃ c ∈ C, c ≠ a ∧ c ≠ b ∧ G.Adj z c := by
    intro C hC z a b hzC haC hbC hza hzb hab
    have hM : 4 ≤ C.length := HoleBasics.hole_length_ge_four hC
    have hgc : ∀ (s t : ℕ) (hs : s < C.length) (ht : t < C.length), s = t →
        (C[s]'hs) = (C[t]'ht) := by
      intro s t hs ht h
      subst h
      rfl
    -- the rotation step, for a pair given by an index and its cyclic successor
    have rot : ∀ (u v : V) (i : ℕ) (hi : i < C.length),
        (C[i]'hi) = u →
        (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega))) = v →
        G.Adj z u → G.Adj z v →
        holeLength C = 4 ∧ ∃ w ∈ C, w ≠ u ∧ w ≠ v ∧ G.Adj z w := by
      intro u v i hi hiu hiv hzu hzv
      have hres := key (C.rotate (i + 2)) (HoleBasics.isHoleList_rotate hC (i + 2)) z u v
        (fun h => hzC (List.mem_rotate.mp h))
        (by
          intro h
          simp only [List.getElem_rotate, List.length_rotate]
          exact (hgc _ _ _ _ (by
            rw [show C.length - 2 + (i + 2) = C.length + i by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt hi])).trans hiu)
        (by
          intro h
          simp only [List.getElem_rotate, List.length_rotate]
          exact (hgc _ _ _ _ (by
            rw [show C.length - 1 + (i + 2) = C.length + (i + 1) by omega,
              Nat.add_mod_left])).trans hiv)
        hzu hzv
      obtain ⟨hlen4, w, hwmem, hwu, hwv, hwadj⟩ := hres
      refine ⟨?_, w, List.mem_rotate.mp hwmem, hwu, hwv, hwadj⟩
      rw [← HoleBasics.holeLength_rotate C (i + 2)]
      exact hlen4
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem haC
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hbC
    have hcase : (j = (i + 1) % C.length ∨ i = (j + 1) % C.length) := by
      rw [← hC.2.2 i j hi hj, hia, hjb]
      exact hab
    rcases hcase with h | h
    · exact rot a b i hi hia ((hgc _ _ _ _ h.symm).trans hjb) hza hzb
    · obtain ⟨hlen4, w, hwmem, hwb, hwa, hwadj⟩ :=
        rot b a j hj hjb ((hgc _ _ _ _ h.symm).trans hia) hzb hza
      exact ⟨hlen4, w, hwmem, hwa, hwb, hwadj⟩
  refine ⟨part1, ?_⟩
  -- SECOND CONCLUSION: "In particular, `G` has no antipath of length 4."
  rintro ⟨q, hq, hqlen⟩
  have hq5 : q.length = 5 := by
    have h1 := PathBasics.pathLength_eq q
    have h2 : 0 < q.length := PathBasics.path_length_pos (hq : IsPathList Gᶜ q)
    omega
  obtain ⟨r0, r1, r2, r3, r4, hqe⟩ := PrismBasics.length_eq_five hq5
  subst hqe
  have hnd5 : ([r0, r1, r2, r3, r4] : List V).Nodup := hq.2.1
  -- the four non-edges of `G`: the consecutive pairs of the antipath
  have n01 : ¬ G.Adj r0 r1 := ((hq.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)).2
  have n12 : ¬ G.Adj r1 r2 := ((hq.2.2 1 2 (by simp) (by simp)).mpr (Or.inl rfl)).2
  have n23 : ¬ G.Adj r2 r3 := ((hq.2.2 2 3 (by simp) (by simp)).mpr (Or.inl rfl)).2
  have n34 : ¬ G.Adj r3 r4 := ((hq.2.2 3 4 (by simp) (by simp)).mpr (Or.inl rfl)).2
  -- the six edges of `G`: the non-consecutive pairs
  have d02 : r0 ≠ r2 := by rintro rfl; simp at hnd5
  have d03 : r0 ≠ r3 := by rintro rfl; simp at hnd5
  have d04 : r0 ≠ r4 := by rintro rfl; simp at hnd5
  have d13 : r1 ≠ r3 := by rintro rfl; simp at hnd5
  have d14 : r1 ≠ r4 := by rintro rfl; simp at hnd5
  have d24 : r2 ≠ r4 := by rintro rfl; simp at hnd5
  have d01 : r0 ≠ r1 := by rintro rfl; simp at hnd5
  have d12 : r1 ≠ r2 := by rintro rfl; simp at hnd5
  have d23 : r2 ≠ r3 := by rintro rfl; simp at hnd5
  have d34 : r3 ≠ r4 := by rintro rfl; simp at hnd5
  have e02 : G.Adj r0 r2 := by
    by_contra h
    have hc : Gᶜ.Adj r0 r2 := ⟨d02, h⟩
    have := (hq.2.2 0 2 (by simp) (by simp)).mp hc
    omega
  have e03 : G.Adj r0 r3 := by
    by_contra h
    have hc : Gᶜ.Adj r0 r3 := ⟨d03, h⟩
    have := (hq.2.2 0 3 (by simp) (by simp)).mp hc
    omega
  have e04 : G.Adj r0 r4 := by
    by_contra h
    have hc : Gᶜ.Adj r0 r4 := ⟨d04, h⟩
    have := (hq.2.2 0 4 (by simp) (by simp)).mp hc
    omega
  have e13 : G.Adj r1 r3 := by
    by_contra h
    have hc : Gᶜ.Adj r1 r3 := ⟨d13, h⟩
    have := (hq.2.2 1 3 (by simp) (by simp)).mp hc
    omega
  have e14 : G.Adj r1 r4 := by
    by_contra h
    have hc : Gᶜ.Adj r1 r4 := ⟨d14, h⟩
    have := (hq.2.2 1 4 (by simp) (by simp)).mp hc
    omega
  have e24 : G.Adj r2 r4 := by
    by_contra h
    have hc : Gᶜ.Adj r2 r4 := ⟨d24, h⟩
    have := (hq.2.2 2 4 (by simp) (by simp)).mp hc
    omega
  -- `r₃-r₁-r₄-r₀-r₃` is a hole of `G` of length 4
  have hpath : IsPathFrom G [r4, r0] r4 r0 :=
    ⟨PathBasics.isPathList_pair e04.symm, by simp, by simp⟩
  have hhole : IsHoleList G [r3, r1, r4, r0] := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hpath (by simp [pathLength])
      e14 e03.symm e13 (by simp [d14, Ne.symm d01]) (by simp [d34, Ne.symm d03])
      (fun h => n01 h.symm) n34 ?_ ?_
    · intro x hx
      simp [SPGT.interior] at hx
    · intro x hx
      simp [SPGT.interior] at hx
  have hr2 : r2 ∉ ([r3, r1, r4, r0] : List V) := by
    simp [d23, Ne.symm d12, d24, Ne.symm d02]
  obtain ⟨-, w, hwmem, hw4, hw0, hwadj⟩ :=
    part1 [r3, r1, r4, r0] hhole r2 r4 r0 hr2 (by simp) (by simp) e24 e02.symm e04.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
  rcases hwmem with h | h | h | h
  · exact n23 (by rw [← h]; exact hwadj)
  · exact n12 (by rw [← h]; exact hwadj.symm)
  · exact hw4 h
  · exact hw0 h

end SPGT

end Workspace.Statements.S24
