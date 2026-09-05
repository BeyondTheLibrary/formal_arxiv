/-  Proof attempt 1 for statement 4.1 (`Workspace.Statements.S04.SPGT.thm_4_1`).

    THE PAPER'S PROOF (perfect.pdf printed p. 14, `paper/proofs/4_1.md`):

      "By taking complements if necessary we may assume that for some a₁ ∈ A, {a₁} is a
       component of A.  Let N be the set of vertices of G adjacent to a₁; so N ⊆ B.
       Assume first that N is not anticonnected.  Then (V(G) \ N, N) is a skew partition
       of G, and it is easy to check that it is balanced, as required.  So we may assume
       that N is anticonnected.  Consequently N is a subset of some anticomponent of B,
       say B₁.  Choose b₂ ∈ B \ B₁.  Then N' = N ∪ {b₂} is not anticonnected, and so
       (V(G) \ N', N') is a skew partition of G, and once again it is easily checked to
       be balanced."

    Map onto the Lean proof below.

    * "By taking complements if necessary"  =  `key` is proved once and applied to `G`
      (first disjunct of `hone`) and to `Gᶜ` (second disjunct), using
      `ClassLemmas.isSkewPartition_compl`, `ClassLemmas.admitsBalancedSkewPartition_compl`
      and `HoleBasics.berge_compl`.  `IsAnticomponent G B B'` is *by definition*
      `IsComponent Gᶜ B B'`, so the second disjunct really is the first one for `Gᶜ`.
    * "so N ⊆ B"  =  `hNB` (a neighbour of `a₁` inside `A` would make `{a₁, x}` a
      connected subset of `A` strictly containing the component `{a₁}`).
    * "N is not anticonnected ⟹ (V(G)\N, N) is a skew partition"  =  `finish_star`
      with `B' = N`.
    * "N anticonnected ⟹ N ⊆ B₁ an anticomponent, choose b₂ ∈ B \ B₁"  — the only use
      the paper makes of `B₁` is that `b₂ ∈ B \ B₁` is complete to `B₁ ⊇ N`, so the
      anticomponent is bypassed and the vertex is produced directly: if *every* vertex
      of `B \ N` had a non-neighbour in `N` then `N` anticonnected would make the whole
      of `B` anticonnected (`anticonnected_of_attached`), contradicting the skew
      partition.  This is exactly the maximality of `B₁` the paper appeals to.
    * "it is easy to check that it is balanced" (both times)  =  `balanced_star`,
      the only substantial part.  `a₁` is complete to `N` and anticomplete to
      `V(G) \ N`, so an odd path between nonadjacent vertices of `N` with interior off
      `N` closes through `a₁` into an odd hole (`no_odd_path_star`, run in `G` for the
      first clause of `Balanced` and in `Gᶜ` for the second).  For `B' = N ∪ {b₂}` the
      two ends of such a path must still lie in `N` (`b₂` is complete to `N`), and an
      antipath whose interior meets `b₂` is forced to have exactly three vertices,
      hence even length.

    GAP FILLED.  The printed sentence "Then N' = N ∪ {b₂} is not anticonnected" needs
    `N ≠ ∅`; a vertex `a₁` isolated in `G` makes `N = ∅` and `N'` a singleton, which is
    anticonnected.  That degenerate case is disposed of separately (`finish_edge`):
    `B` is not anticonnected, so it contains two adjacent vertices `x, y`, and
    `(V(G) \ {x,y}, {x,y})` is then a skew partition (`a₁` is isolated) which is
    balanced for trivial reasons (`balanced_of_edge`).  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas

-- The frozen statement's `variable` line carries `[Fintype V] [DecidableEq V]`, neither of
-- which this proof consumes.  The linter's suggested fix would change the elaborated
-- signature (and be rejected by `rollback_check`), so the linter is switched off instead.
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S04

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

namespace SPGT

/-! ### Infrastructure

None of this is in the paper; it is the bookkeeping the phrase "it is easy to check"
stands for.  `succ_mod_eq` and `glue_hole` are copied from the proof of 2.6
(`ProofAttempts/thm_2_6/Attempt_2.lean`) and belong in `Workspace/ProofLemmas/` once
lifted. -/

section Helpers

variable {V : Type*}

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- If `P` and `R` are vertex-disjoint paths and the only edges of `G` between `V(P)`
and `V(R)` are the two joining the last vertex of `P` to the first of `R` and the first
of `P` to the last of `R`, then `P ++ R` is a hole. -/
private theorem glue_hole {G : SimpleGraph V} {P R : List V} {u₀ u₁ w₀ w₁ : V}
    (hP : IsPathFrom G P u₀ u₁) (hR : IsPathFrom G R w₀ w₁)
    (hdisj : ∀ x ∈ P, x ∉ R)
    (hcross : ∀ x ∈ P, ∀ y ∈ R, (G.Adj x y ↔ (x = u₁ ∧ y = w₀) ∨ (x = u₀ ∧ y = w₁)))
    (hlen : 4 ≤ P.length + R.length) :
    IsHoleList G (P ++ R) := by
  obtain ⟨hPl, hPh, hPt⟩ := hP
  obtain ⟨hRl, hRh, hRt⟩ := hR
  have hm : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hPl
  have hn : 0 < R.length := Workspace.ProofLemmas.PathBasics.path_length_pos hRl
  have hP0 : P[0]'hm = u₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPh hm
  have hPm : P[P.length - 1]'(by omega) = u₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPt hm
  have hR0 : R[0]'hn = w₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hRh hn
  have hRn : R[R.length - 1]'(by omega) = w₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hRt hn
  have hPnd : P.Nodup := hPl.2.1
  have hRnd : R.Nodup := hRl.2.1
  have cross : ∀ (i j : ℕ) (hiP : i < P.length) (hjP : P.length ≤ j)
      (hi : i < (P ++ R).length) (hj : j < (P ++ R).length),
      (G.Adj ((P ++ R)[i]'hi) ((P ++ R)[j]'hj) ↔
        (j = (i + 1) % (P ++ R).length ∨ i = (j + 1) % (P ++ R).length)) := by
    intro i j hiP hjP hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    have hjR : j - P.length < R.length := by omega
    rw [List.getElem_append_left hiP, List.getElem_append_right hjP,
      hcross (P[i]'hiP) (List.getElem_mem hiP) (R[j - P.length]'hjR) (List.getElem_mem hjR)]
    have e1 : (P[i]'hiP = u₁) ↔ i = P.length - 1 := by
      rw [← hPm]; exact hPnd.getElem_inj_iff
    have e2 : (P[i]'hiP = u₀) ↔ i = 0 := by
      rw [← hP0]; exact hPnd.getElem_inj_iff
    have e3 : (R[j - P.length]'hjR = w₀) ↔ j - P.length = 0 := by
      rw [← hR0]; exact hRnd.getElem_inj_iff
    have e4 : (R[j - P.length]'hjR = w₁) ↔ j - P.length = R.length - 1 := by
      rw [← hRn]; exact hRnd.getElem_inj_iff
    rw [e1, e2, e3, e4]
    simp only [List.length_append]
    rw [succ_mod_eq hiL, succ_mod_eq hjL]
    split_ifs <;> omega
  refine ⟨by simpa using hlen, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hPnd, hRnd, fun a ha b hb => by rintro rfl; exact hdisj a ha hb⟩
  · intro i j hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    rcases lt_or_ge i P.length with hiP | hiP
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [List.getElem_append_left hiP, List.getElem_append_left hjP,
          Workspace.ProofLemmas.PathBasics.path_adj_iff hPl hiP hjP]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega
      · exact cross i j hiP hjP hi hj
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [SimpleGraph.adj_comm, cross j i hjP hiP hj hi]
        constructor <;> (intro h; tauto)
      · have hiR : i - P.length < R.length := by omega
        have hjR : j - P.length < R.length := by omega
        rw [List.getElem_append_right hiP, List.getElem_append_right hjP,
          Workspace.ProofLemmas.PathBasics.path_adj_iff hRl hiR hjR]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega

/-- **The "easy check".**  `Nw` is the neighbourhood of `w`.  An odd path whose two ends
are nonadjacent neighbours of `w` and whose interior avoids the neighbourhood of `w`
closes up through `w` into an odd hole. -/
private theorem no_odd_path_star {H : SimpleGraph V}
    (hHberge : ∀ c : List V, IsHoleList H c → Even (holeLength c))
    (w : V) (Nw : Set V) (hNw : ∀ x : V, x ∈ Nw ↔ H.Adj w x)
    (u v : V) (p : List V) (hu : u ∈ Nw) (hv : v ∈ Nw) (hnadj : ¬ H.Adj u v)
    (hp : IsPathFrom H p u v)
    (hint : ∀ x ∈ Workspace.Types.Core.SPGT.interior p, x ∉ Nw) :
    ¬ Odd (pathLength p) := by
  intro hodd
  rw [Nat.odd_iff] at hodd
  have hne1 : pathLength p ≠ 1 := fun h =>
    hnadj (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hp h)
  have hplen : 4 ≤ p.length := by
    have h := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hp.1
    omega
  -- a vertex of the path lying in `Nw` must be one of the two ends
  have hend : ∀ (i : ℕ) (hi : i < p.length), (p[i]'hi) ∈ Nw → (i = 0 ∨ i = p.length - 1) := by
    intro i hi hmem
    by_contra hcon
    push Not at hcon
    exact hint _
      (Workspace.ProofLemmas.PathBasics.getElem_mem_interior hp.1 hi (by omega) (by omega)) hmem
  have hwu : w ≠ u := by rintro rfl; exact ((hNw w).mp hu).ne rfl
  have hwv : w ≠ v := by rintro rfl; exact ((hNw w).mp hv).ne rfl
  -- `w` is not a vertex of the path
  have hwp : w ∉ p := by
    intro hmem
    have hwint : w ∈ Workspace.Types.Core.SPGT.interior p :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hmem, hwu, hwv⟩
    obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hp.1 hwint
    have hm1 : (p[k - 1]'(by omega)) ∈ Nw := by
      refine (hNw _).mpr ?_
      rw [← hkw]
      exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hp.1 hk
        (show k - 1 < p.length by omega)).mpr (Or.inr (by omega))
    have hm2 : (p[k + 1]'(by omega)) ∈ Nw := by
      refine (hNw _).mpr ?_
      rw [← hkw]
      exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hp.1 hk
        (show k + 1 < p.length by omega)).mpr (Or.inl rfl)
    have h1 := hend (k - 1) (by omega) hm1
    have h2 := hend (k + 1) (by omega) hm2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  -- `w` is adjacent to exactly the two ends
  have hadjw : ∀ x ∈ p, (H.Adj x w ↔ (x = v ∨ x = u)) := by
    intro x hx
    constructor
    · intro hxw
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
      have hiN : (p[i]'hi) ∈ Nw := by rw [hix]; exact (hNw x).mpr hxw.symm
      have hpos : 0 < p.length := by omega
      rcases hend i hi hiN with h | h
      · subst h
        right
        rw [← hix]
        exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hpos
      · subst h
        left
        rw [← hix]
        exact Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    · rintro (rfl | rfl)
      · exact ((hNw x).mp hv).symm
      · exact ((hNw x).mp hu).symm
  have hsing : IsPathFrom H [w] w w :=
    ⟨Workspace.ProofLemmas.PathBasics.isPathList_singleton H w, by simp, by simp⟩
  have hhole : IsHoleList H (p ++ [w]) := by
    refine glue_hole hp hsing ?_ ?_ ?_
    · intro x hx hx'
      rw [List.mem_singleton] at hx'
      subst hx'
      exact hwp hx
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [hadjw x hx]
      constructor
      · rintro (h | h)
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨h, rfl⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
    · simp only [List.length_singleton]; omega
  have hev : Even ((p ++ [w]).length) := hHberge _ hhole
  simp only [List.length_append, List.length_singleton] at hev
  rw [Nat.even_iff] at hev
  rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hodd
  omega

/-! #### Connectivity bookkeeping -/

private theorem eq_of_reachable_isolated {W : Type*} {H : SimpleGraph W} {a b : W}
    (hiso : ∀ z, ¬ H.Adj a z) (h : H.Reachable a b) : a = b := by
  obtain ⟨wk⟩ := h
  cases wk with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- A set containing two distinct vertices one of which has no neighbour inside it is
not connected. -/
private theorem not_connectedSet_of_isolated {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) (hiso : ∀ z ∈ X, ¬ G.Adj x z) :
    ¬ ConnectedSet G X := by
  intro h
  have h' : (⟨x, hx⟩ : ↥X) = ⟨y, hy⟩ :=
    eq_of_reachable_isolated (fun z hz => hiso z.1 z.2 hz) (h ⟨x, hx⟩ ⟨y, hy⟩)
  exact hxy (congrArg Subtype.val h')

/-- Two adjacent vertices form a connected set. -/
private theorem connectedSet_pair {G : SimpleGraph V} {a b : V} (hab : G.Adj a b) :
    ConnectedSet G ({a, b} : Set V) := by
  have hkey : ∀ (z : V) (hz : z ∈ ({a, b} : Set V)),
      (G.induce ({a, b} : Set V)).Reachable ⟨z, hz⟩ ⟨a, by simp⟩ := by
    intro z hz
    rcases (show z = a ∨ z = b from hz) with h | h
    · subst h; exact SimpleGraph.Reachable.refl _
    · subst h
      exact SimpleGraph.Adj.reachable
        (show (G.induce ({a, z} : Set V)).Adj ⟨z, hz⟩ ⟨a, by simp⟩ from hab.symm)
  intro u v
  exact (hkey u.1 u.2).trans (hkey v.1 v.2).symm

private def inclHom (G : SimpleGraph V) {X Y : Set V} (hXY : X ⊆ Y) :
    G.induce X →g G.induce Y where
  toFun u := ⟨u.1, hXY u.2⟩
  map_rel' := fun hab => hab

private theorem reachable_of_subset (G : SimpleGraph V) {X Y : Set V} (hXY : X ⊆ Y)
    {a b : ↥X} (hab : (G.induce X).Reachable a b) :
    (G.induce Y).Reachable ⟨a.1, hXY a.2⟩ ⟨b.1, hXY b.2⟩ :=
  hab.map (inclHom G hXY)

/-- If `N` is a nonempty anticonnected subset of `B` and every vertex of `B \ N` has a
non-neighbour in `N`, then `B` is anticonnected.  (This is the maximality of the
anticomponent `B₁` that the paper appeals to.) -/
private theorem anticonnected_of_attached {G : SimpleGraph V} {N B : Set V}
    (hN : AnticonnectedSet G N) (n₀ : V) (hn₀ : n₀ ∈ N) (hNB : N ⊆ B)
    (hatt : ∀ b ∈ B, b ∉ N → ∃ n ∈ N, Gᶜ.Adj b n) : AnticonnectedSet G B := by
  have hreach : ∀ (z : V) (hz : z ∈ B),
      (Gᶜ.induce B).Reachable ⟨z, hz⟩ ⟨n₀, hNB hn₀⟩ := by
    intro z hz
    by_cases hzN : z ∈ N
    · exact reachable_of_subset Gᶜ hNB (a := ⟨z, hzN⟩) (b := ⟨n₀, hn₀⟩) (hN _ _)
    · obtain ⟨n, hn, hadj⟩ := hatt z hz hzN
      have h1 : (Gᶜ.induce B).Adj ⟨z, hz⟩ ⟨n, hNB hn⟩ := hadj
      exact h1.reachable.trans
        (reachable_of_subset Gᶜ hNB (a := ⟨n, hn⟩) (b := ⟨n₀, hn₀⟩) (hN _ _))
  intro u v
  exact (hreach u.1 u.2).trans (hreach v.1 v.2).symm

/-! #### The two "easily checked" balanced pairs -/

/-- `(V(G) \ {x,y}, {x,y})` is balanced whenever `x` and `y` are adjacent.  (Used only
for the degenerate case `N = ∅`.) -/
private theorem balanced_of_edge {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    Workspace.Types.Core.SPGT.Balanced G (({x, y} : Set V)ᶜ) ({x, y} : Set V) := by
  constructor
  · intro u v p hu hv hnadj hp _ hodd
    have hu' : u = x ∨ u = y := hu
    have hv' : v = x ∨ v = y := hv
    have huv : u = v := by
      rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
      · rw [h1, h2]
      · exact absurd (by rw [h1, h2]; exact hxy) hnadj
      · exact absurd (by rw [h1, h2]; exact hxy.symm) hnadj
      · rw [h1, h2]
    subst huv
    rw [Nat.odd_iff] at hodd
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hp (by omega) rfl
  · intro u v p _ _ hadj hp hint hodd
    rw [Nat.odd_iff] at hodd
    have hne1 : pathLength p ≠ 1 := by
      intro h
      exact ((SimpleGraph.compl_adj G u v).mp
        (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hp h)).2 hadj
    have hplen : 4 ≤ p.length := by
      have h := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hp.1
      omega
    have h1 : (p[1]'(by omega)) ∈ Workspace.Types.Core.SPGT.interior p :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hp.1 (by omega) (by omega) (by omega)
    have h2 : (p[2]'(by omega)) ∈ Workspace.Types.Core.SPGT.interior p :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hp.1 (by omega) (by omega) (by omega)
    have hadj12 : Gᶜ.Adj (p[1]'(by omega)) (p[2]'(by omega)) :=
      (Workspace.ProofLemmas.PathBasics.path_adj_iff hp.1 (by omega) (by omega)).mpr
        (Or.inl rfl)
    have hne12 : (p[1]'(by omega)) ≠ (p[2]'(by omega)) := hadj12.ne
    have hb1 := hint _ h1
    have hb2 := hint _ h2
    rcases (show (p[1]'(by omega)) = x ∨ (p[1]'(by omega)) = y from hb1) with e1 | e1 <;>
      rcases (show (p[2]'(by omega)) = x ∨ (p[2]'(by omega)) = y from hb2) with e2 | e2
    · exact hne12 (e1.trans e2.symm)
    · exact ((SimpleGraph.compl_adj G _ _).mp hadj12).2 (e1 ▸ e2 ▸ hxy)
    · exact ((SimpleGraph.compl_adj G _ _).mp hadj12).2 (e1 ▸ e2 ▸ hxy.symm)
    · exact hne12 (e1.trans e2.symm)

/-- The heart of 4.1: for `N` the neighbourhood of `a₁` and any `B'` with `N ⊆ B'`,
`a₁ ∉ B'` and `B' \ N` a single vertex complete to `N`, the pair `(V(G) \ B', B')` is
balanced. -/
private theorem balanced_star {G : SimpleGraph V} (hG : Berge G) (a₁ : V) (N B' : Set V)
    (hN : ∀ x : V, x ∈ N ↔ G.Adj a₁ x) (hNB' : N ⊆ B') (ha₁ : a₁ ∉ B')
    (hB : ∀ w ∈ B', w ∉ N → (VertexComplete G w N ∧ ∀ z ∈ B', z ≠ w → z ∈ N)) :
    Workspace.Types.Core.SPGT.Balanced G (B'ᶜ) B' := by
  constructor
  · -- no odd path between nonadjacent vertices of `B'` with interior outside `B'`
    intro u v p hu hv hnadj hp hint hodd
    have hodd' : Odd (pathLength p) := hodd
    rw [Nat.odd_iff] at hodd
    have huv : u ≠ v :=
      Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hp (by omega)
    have huN : u ∈ N := by
      by_contra hcon
      obtain ⟨hcomp, hall⟩ := hB u hu hcon
      exact hnadj (hcomp v (hall v hv (Ne.symm huv)))
    have hvN : v ∈ N := by
      by_contra hcon
      obtain ⟨hcomp, hall⟩ := hB v hv hcon
      exact hnadj (hcomp u (hall u hu huv)).symm
    exact no_odd_path_star hG.1 a₁ N hN u v p huN hvN hnadj hp
      (fun x hx hxN => hint x hx (hNB' hxN)) hodd'
  · -- no odd antipath between adjacent vertices outside `B'` with interior in `B'`
    intro u v p hu hv hadj hp hint hodd
    have hodd' : Odd (pathLength p) := hodd
    rw [Nat.odd_iff] at hodd
    have hp' : IsPathFrom Gᶜ p u v := Workspace.ProofLemmas.PathBasics.isAntipathFrom_iff.mp hp
    have hnadjc : ¬ Gᶜ.Adj u v := fun h => ((SimpleGraph.compl_adj G u v).mp h).2 hadj
    have hune : u ≠ a₁ := by
      intro h; subst h; exact hv (hNB' ((hN v).mpr hadj))
    have hvne : v ≠ a₁ := by
      intro h; subst h; exact hu (hNB' ((hN u).mpr hadj.symm))
    have huNc : Gᶜ.Adj a₁ u :=
      (SimpleGraph.compl_adj G a₁ u).mpr ⟨Ne.symm hune, fun h => hu (hNB' ((hN u).mpr h))⟩
    have hvNc : Gᶜ.Adj a₁ v :=
      (SimpleGraph.compl_adj G a₁ v).mpr ⟨Ne.symm hvne, fun h => hv (hNB' ((hN v).mpr h))⟩
    by_cases hcase : ∀ x ∈ Workspace.Types.Core.SPGT.interior p, x ∈ N
    · refine no_odd_path_star (H := Gᶜ) hG.2 a₁ {z : V | Gᶜ.Adj a₁ z}
        (fun _ => Iff.rfl) u v p huNc hvNc hnadjc hp' ?_ hodd'
      intro x hx hxc
      exact ((SimpleGraph.compl_adj G a₁ x).mp hxc).2 ((hN x).mp (hcase x hx))
    · push Not at hcase
      obtain ⟨w, hwint, hwN⟩ := hcase
      obtain ⟨hcomp, hall⟩ := hB w (hint w hwint) hwN
      have hne1 : pathLength p ≠ 1 := fun h =>
        hnadjc (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hp' h)
      have hplen : 4 ≤ p.length := by
        have h := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hp'.1
        omega
      obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
        Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hp'.1 hwint
      have hnotint : ∀ (i : ℕ) (hi : i < p.length), Gᶜ.Adj w (p[i]'hi) →
          (i = 0 ∨ i = p.length - 1) := by
        intro i hi hadji
        by_contra hcon
        push Not at hcon
        have hmem : (p[i]'hi) ∈ Workspace.Types.Core.SPGT.interior p :=
          Workspace.ProofLemmas.PathBasics.getElem_mem_interior hp'.1 hi (by omega) (by omega)
        have hzN : (p[i]'hi) ∈ N := hall _ (hint _ hmem) hadji.ne'
        exact ((SimpleGraph.compl_adj G w _).mp hadji).2 (hcomp _ hzN)
      have hadj1 : Gᶜ.Adj w (p[k - 1]'(by omega)) := by
        rw [← hkw]
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hp'.1 hk
          (show k - 1 < p.length by omega)).mpr (Or.inr (by omega))
      have hadj2 : Gᶜ.Adj w (p[k + 1]'(by omega)) := by
        rw [← hkw]
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hp'.1 hk
          (show k + 1 < p.length by omega)).mpr (Or.inl rfl)
      have h1 := hnotint (k - 1) (by omega) hadj1
      have h2 := hnotint (k + 1) (by omega) hadj2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

/-! #### Assembling the skew partition -/

private theorem finish_star {G : SimpleGraph V} (hG : Berge G) (A B : Set V)
    (hdisj : Disjoint A B) (a₁ a' : V) (ha₁ : a₁ ∈ A) (ha' : a' ∈ A) (hne : a' ≠ a₁)
    (N B' : Set V) (hN : ∀ x : V, x ∈ N ↔ G.Adj a₁ x) (hNB' : N ⊆ B') (hB'B : B' ⊆ B)
    (hB : ∀ w ∈ B', w ∉ N → (VertexComplete G w N ∧ ∀ z ∈ B', z ≠ w → z ∈ N))
    (hnac : ¬ AnticonnectedSet G B') :
    AdmitsBalancedSkewPartition G := by
  have ha₁B' : a₁ ∉ B' := fun h => (Set.disjoint_left.mp hdisj ha₁) (hB'B h)
  have ha'B' : a' ∉ B' := fun h => (Set.disjoint_left.mp hdisj ha') (hB'B h)
  refine ⟨B'ᶜ, B', ⟨⟨?_, ?_, ?_, hnac⟩, balanced_star hG a₁ N B' hN hNB' ha₁B' hB⟩⟩
  · exact Set.compl_union_self B'
  · exact disjoint_compl_left
  · refine not_connectedSet_of_isolated (X := B'ᶜ) ha₁B' ha'B' (Ne.symm hne) ?_
    intro z hz hadjz
    exact hz (hNB' ((hN z).mpr hadjz))

private theorem finish_edge {G : SimpleGraph V} (A B : Set V) (hdisj : Disjoint A B)
    (a₁ a' : V) (ha₁ : a₁ ∈ A) (ha' : a' ∈ A) (hne : a' ≠ a₁)
    (hiso : ∀ z : V, ¬ G.Adj a₁ z) (x y : V) (hx : x ∈ B) (hy : y ∈ B) (hxy : G.Adj x y) :
    AdmitsBalancedSkewPartition G := by
  have hmem : ∀ c : V, c ∈ A → c ∉ ({x, y} : Set V) := by
    intro c hc hcm
    rcases (show c = x ∨ c = y from hcm) with rfl | rfl
    · exact (Set.disjoint_left.mp hdisj hc) hx
    · exact (Set.disjoint_left.mp hdisj hc) hy
  refine ⟨({x, y} : Set V)ᶜ, ({x, y} : Set V), ⟨⟨?_, ?_, ?_, ?_⟩, balanced_of_edge hxy⟩⟩
  · exact Set.compl_union_self _
  · exact disjoint_compl_left
  · exact not_connectedSet_of_isolated (X := ({x, y} : Set V)ᶜ) (hmem a₁ ha₁) (hmem a' ha')
      (Ne.symm hne) (fun z _ => hiso z)
  · refine not_connectedSet_of_isolated (G := Gᶜ) (X := ({x, y} : Set V))
      (show x ∈ ({x, y} : Set V) by simp) (show y ∈ ({x, y} : Set V) by simp) hxy.ne ?_
    intro z hz hadjz
    rcases (show z = x ∨ z = y from hz) with rfl | rfl
    · exact hadjz.ne rfl
    · exact ((SimpleGraph.compl_adj G x z).mp hadjz).2 hxy

/-! #### The half of 4.1 that is proved directly (the other half is its complement) -/

private theorem key {G : SimpleGraph V} (hG : Berge G) (A B : Set V)
    (hAB : IsSkewPartition G A B) (a₁ : V) (hcomp : IsComponent G A ({a₁} : Set V)) :
    AdmitsBalancedSkewPartition G := by
  obtain ⟨hunion, hdisj, hAnc, hBnac⟩ := hAB
  have ha₁A : a₁ ∈ A := hcomp.1 rfl
  -- `N` is the set of neighbours of `a₁`
  have hN : ∀ x : V, x ∈ {z : V | G.Adj a₁ z} ↔ G.Adj a₁ x := fun _ => Iff.rfl
  -- "so N ⊆ B"
  have hNB : {z : V | G.Adj a₁ z} ⊆ B := by
    intro z hz
    have hadjz : G.Adj a₁ z := hz
    have hzA : z ∉ A := by
      intro hzA
      have heq : ({a₁, z} : Set V) = ({a₁} : Set V) :=
        hcomp.2.2 ({a₁, z} : Set V) (fun c hc => Or.inl hc)
          (by
            intro c hc
            rcases (show c = a₁ ∨ c = z from hc) with rfl | rfl
            · exact ha₁A
            · exact hzA)
          (connectedSet_pair hadjz)
      have : z ∈ ({a₁} : Set V) := heq ▸ (show z ∈ ({a₁, z} : Set V) from Or.inr rfl)
      exact hadjz.ne' this
    have hmem : z ∈ A ∪ B := by rw [hunion]; trivial
    rcases hmem with h | h
    · exact absurd h hzA
    · exact h
  -- `A` has a vertex other than `a₁`, since `A` is not connected
  obtain ⟨a', ha'A, ha'ne⟩ : ∃ a' : V, a' ∈ A ∧ a' ≠ a₁ := by
    by_contra hcon
    push Not at hcon
    refine hAnc ?_
    intro u v
    have : u = v := Subtype.ext ((hcon u.1 u.2).trans (hcon v.1 v.2).symm)
    rw [this]
  by_cases hNempty : ∀ z : V, ¬ G.Adj a₁ z
  · -- degenerate case, not in the paper: `a₁` is isolated, so `N = ∅`
    rw [AnticonnectedSet, ConnectedSet, SimpleGraph.Preconnected] at hBnac
    push Not at hBnac
    obtain ⟨u₀, v₀, huv⟩ := hBnac
    have hsub : u₀ ≠ v₀ := by
      intro h; rw [h] at huv; exact huv (SimpleGraph.Reachable.refl _)
    have hne : (u₀ : V) ≠ (v₀ : V) := fun h => hsub (Subtype.ext h)
    have hadj : G.Adj (u₀ : V) (v₀ : V) := by
      by_contra hcon
      exact huv (SimpleGraph.Adj.reachable
        (show (Gᶜ.induce B).Adj u₀ v₀ from (SimpleGraph.compl_adj G _ _).mpr ⟨hne, hcon⟩))
    exact finish_edge A B hdisj a₁ a' ha₁A ha'A ha'ne hNempty (u₀ : V) (v₀ : V) u₀.2 v₀.2 hadj
  · push Not at hNempty
    obtain ⟨n₀, hn₀⟩ := hNempty
    have hn₀N : n₀ ∈ {z : V | G.Adj a₁ z} := hn₀
    by_cases hNanti : AnticonnectedSet G {z : V | G.Adj a₁ z}
    · -- "N is anticonnected": produce `b₂` (the paper's `b₂ ∈ B \ B₁`)
      obtain ⟨b₂, hb₂B, hb₂N, hb₂comp⟩ :
          ∃ b₂ : V, b₂ ∈ B ∧ b₂ ∉ {z : V | G.Adj a₁ z} ∧
            ∀ n ∈ {z : V | G.Adj a₁ z}, G.Adj b₂ n := by
        by_contra hcon
        push Not at hcon
        refine hBnac (anticonnected_of_attached hNanti n₀ hn₀N hNB ?_)
        intro b hb hbN
        obtain ⟨n, hn, hnadj⟩ := hcon b hb hbN
        exact ⟨n, hn, (SimpleGraph.compl_adj G b n).mpr ⟨by rintro rfl; exact hbN hn, hnadj⟩⟩
      refine finish_star hG A B hdisj a₁ a' ha₁A ha'A ha'ne
        {z : V | G.Adj a₁ z} ({z : V | G.Adj a₁ z} ∪ {b₂}) hN Set.subset_union_left ?_ ?_ ?_
      · intro z hz
        rcases hz with h | h
        · exact hNB h
        · rw [show z = b₂ from h]; exact hb₂B
      · intro w hw hwN
        have hwb : w = b₂ := by
          rcases hw with h | h
          · exact absurd h hwN
          · exact h
        subst hwb
        exact ⟨hb₂comp, by
          intro z hz hzw
          rcases hz with h | h
          · exact h
          · exact absurd (show z = w from h) hzw⟩
      · refine not_connectedSet_of_isolated (G := Gᶜ)
          (X := ({z : V | G.Adj a₁ z} ∪ {b₂})) (Or.inr rfl) (Or.inl hn₀N) ?_ ?_
        · intro h; exact hb₂N (h ▸ hn₀N)
        · intro z hz hadjz
          rcases hz with h | h
          · exact ((SimpleGraph.compl_adj G b₂ z).mp hadjz).2 (hb₂comp z h)
          · exact hadjz.ne (show b₂ = z from (show z = b₂ from h).symm)
    · -- "N is not anticonnected": the partition is `(V(G) \ N, N)`
      exact finish_star hG A B hdisj a₁ a' ha₁A ha'A ha'ne
        {z : V | G.Adj a₁ z} {z : V | G.Adj a₁ z} hN (subset_refl _) hNB
        (fun w hw hwN => absurd hw hwN) hNanti

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **4.1** (printed p. 14)

PAPER: *"Let `G` be Berge, and suppose that `G` admits a skew partition `(A,B)` such that
either some component of `A` or some anticomponent of `B` has only one vertex.  Then `G`
admits a balanced skew partition."*

Transcription notes.

* *"`G` admits a skew partition `(A,B)` such that …"* is rendered by naming the witnessing
  partition: `(A,B)` is a skew partition of `G` satisfying the stated side condition.
* *"has only one vertex"* is `∃ a, A' = {a}`, i.e. the set is a singleton.
* The two alternatives appear in the order printed. -/
theorem thm_4_1 (G : SimpleGraph V) (hG : Berge G) (A B : Set V)
    (hAB : IsSkewPartition G A B)
    (hone : (∃ A' : Set V, IsComponent G A A' ∧ ∃ a : V, A' = {a}) ∨
            (∃ B' : Set V, IsAnticomponent G B B' ∧ ∃ b : V, B' = {b})) :
    AdmitsBalancedSkewPartition G := by
  rcases hone with ⟨A', hA', a, rfl⟩ | ⟨B', hB', b, rfl⟩
  · exact key hG A B hAB a hA'
  · -- "By taking complements if necessary": this is the first case for `Gᶜ`
    refine Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp
      (key (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) B A ?_ b hB')
    exact Workspace.ProofLemmas.ClassLemmas.isSkewPartition_compl.mpr hAB


end SPGT

end Workspace.Statements.S04
