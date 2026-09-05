import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OddWheelArc
import Workspace.ProofLemmas.OddWheelSpan
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.BalancedNoLeap
import Workspace.ProofLemmas.CycleTwoChordsAppearance
import Workspace.ProofLemmas.OddWheelClaimOneNoCore
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S15.Thm_15_5

/-!
# The endgame of the NO branch of claim (1) of 16.1

PAPER (16.1, printed p. 97), the last four sentences of the proof of claim (1):

> *"Both these paths have length ≥ 2; suppose they both have length 2.  Then `n = 6`, and the
> only `Y' ∪ {v}`-complete vertices in `C` are `p₁, p₄`, contrary to 15.5.  So one of the paths
> has length > 2, and from the symmetry we may assume that `j ≥ 4`.  Hence the hole
> `H = v-p₁-⋯-p_j-v` has length ≥ 6, and the only `Y'`-complete vertices in it are `p_i,
> p_{i+1}`.  By 2.10, `Y'` contains a hat or a leap.  But `p_{k+1}` has no neighbour in this
> hole, so the pair `(V(H), Y')` is balanced by 2.6, and hence there is no leap.  So there is a
> hat; that is, there exists `y ∈ Y'` with no neighbours in `H` except `p_i, p_{i+1}`.  From the
> minimality of `Y'` it follows that `Y' = {y}`.  But then `G|(V(C) ∪ {v,y})` is the line graph
> of a bipartite subdivision of `K₄`, a contradiction."*

Index dictionary: `n = C.length`, `D t` is the rim vertex at cyclic position `k + t`, the
paper's `p_a` is `D (a-1)`, its `j` is `L + 1`, its `i` is `s + 1`, its `k` is `c + 1`.

The paper's *"from the symmetry we may assume that `j ≥ 4`"* is a genuine gap: the *minimality*
of `Y'` is stated for the arc `p₁-⋯-p_j`, and is **not** symmetric under exchanging the two arcs.
It is filled here by splitting on `L`:

* `4 ≤ L` — the paper's case, verbatim: take the hat in `H = v-p₁-⋯-p_j-v`;
* `L = 2` and `c = L + 1` — the vertices `p₁` and `p_{j+1}` are the only `Y' ∪ {v}`-complete
  vertices of the rim and the arc between them is odd, contrary to 15.5.  (When `n = 6` this is
  literally the paper's own `n = 6` case.)
* `L = 2` and `c ≥ L + 3` — take the hat in the OTHER hole `H' = v-p_{j+1}-⋯-p_n-v`, which then
  has length `n - 2 ≥ 6`, and recover *"`y` has no neighbour on `p₁-⋯-p_j` except `p_i,
  p_{i+1}`"* from 2.3 applied to `C` with hub `{y}` (the rim carries an even number of
  `{y}`-complete edges, because it carries at least four `{y}`-complete vertices, and all of
  them but the one on `p₁-⋯-p_j` are accounted for).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelClaimOneNoEnd

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.OddWheelArc

variable {V : Type*}

/-! ## The hat -/

/-- PAPER: *"the only `Y'`-complete vertices in it are `p_i, p_{i+1}`.  By 2.10, `Y'` contains a
hat or a leap.  But `p_{k+1}` has no neighbour in this hole, so the pair `(V(H), Y')` is
balanced by 2.6, and hence there is no leap.  So there is a hat; that is, there exists `y ∈ Y'`
with no neighbours in `H` except `p_i, p_{i+1}`."*

Stated for an arbitrary base offset `k`, so that it can be applied to either of the two holes
`v-p₁-⋯-p_j-v` and `v-p_{j+1}-⋯-p_n-v`. -/
theorem hat_of_hole [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hvC : v ∉ C) (hvY' : v ∉ Y') (hvZ : ¬ VertexComplete G v Y')
    (hCY' : ∀ w ∈ C, w ∉ Y') (hY'anti : AnticonnectedSet G Y')
    (hL4 : 4 ≤ L) (hLeven : Even L) (hL2 : L + 2 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hs : s + 1 < L)
    (hcomp : ∀ t, t ≤ L → (VertexComplete G (D t) Y' ↔ (t = s ∨ t = s + 1)))
    (w : V) (hw : VertexComplete G w Y') (hwY' : w ∉ Y')
    (hwnH : w ∉ bigHole C k L v)
    (hwH : ∀ z ∈ bigHole C k L v, ¬ G.Adj w z) :
    ∃ y ∈ Y', (∀ t, t ≤ L → (G.Adj y (D t) ↔ (t = s ∨ t = s + 1))) ∧ ¬ G.Adj y v := by
  have hH : IsHoleList G (bigHole C k L v) :=
    bigHole_isHole hC hn hD hnn (by omega) hL2 hvC hvD
  have hmem : ∀ z : V, z ∈ bigHole C k L v ↔ ((∃ t, t ≤ L ∧ z = D t) ∨ z = v) :=
    fun z => bigHole_mem_iff (v := v) hC hn hD hnn (by omega)
  have hHY' : ∀ z ∈ bigHole C k L v, z ∉ Y' := by
    intro z hz
    rcases (hmem z).mp hz with ⟨t, ht, rfl⟩ | rfl
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
  have hHlen : (bigHole C k L v).length = L + 2 := bigHole_length (v := v) (by omega)
  have hsmem : D s ∈ bigHole C k L v := (hmem _).mpr (Or.inl ⟨s, by omega, rfl⟩)
  have hs1mem : D (s + 1) ∈ bigHole C k L v := (hmem _).mpr (Or.inl ⟨s + 1, by omega, rfl⟩)
  have hadjss : G.Adj (D s) (D (s + 1)) :=
    (rim_adj hC hn hD hnn (by omega) (by omega)).mpr (Or.inl rfl)
  have honlyH : ∀ z ∈ bigHole C k L v, VertexComplete G z Y' → (z = D s ∨ z = D (s + 1)) := by
    intro z hz hcz
    rcases (hmem z).mp hz with ⟨t, ht, rfl⟩ | rfl
    · rcases (hcomp t ht).mp hcz with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · exact absurd hcz hvZ
  rcases Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y' hY'anti (bigHole C k L v) hH hHY'
      (by rw [holeLength, hHlen]; omega) (D s) (D (s + 1)) hsmem hs1mem hadjss
      ((hcomp s (by omega)).mpr (Or.inl rfl)) ((hcomp (s + 1) (by omega)).mpr (Or.inr rfl))
      honlyH with ⟨y, hyY', hhat⟩ | ⟨a, ha, b, hb, hleap⟩
  · -- the hat
    obtain ⟨-, -, -, -, hya, hyb, hyother⟩ := hhat
    refine ⟨y, hyY', ?_, ?_⟩
    · intro t ht
      constructor
      · intro hadj
        by_contra hcon
        push_neg at hcon
        exact hyother (D t) ((hmem _).mpr (Or.inl ⟨t, ht, rfl⟩))
          (fun hh => hcon.1 (rim_inj hC hn hD hnn (by omega) (by omega) hh))
          (fun hh => hcon.2 (rim_inj hC hn hD hnn (by omega) (by omega) hh)) hadj
      · rintro (h | h)
        · rw [h]; exact hya
        · rw [h]; exact hyb
    · refine hyother v ((hmem _).mpr (Or.inr rfl)) ?_ ?_
      · intro hh; exact hvC (by rw [hh]; exact rim_mem hn hD s)
      · intro hh; exact hvC (by rw [hh]; exact rim_mem hn hD (s + 1))
  · -- no leap: `(V(H), Y')` is balanced by 2.6
    exfalso
    have hbal : SPGT.Balanced G {z : V | z ∈ bigHole C k L v} Y' :=
      Workspace.Statements.S02.SPGT.thm_2_6 G hBerge {z : V | z ∈ bigHole C k L v} Y'
        (Set.disjoint_left.mpr (fun x hx hx' => hHY' x hx hx')) w
        (by
          simp only [Set.mem_union, Set.mem_setOf_eq]
          rintro (h | h)
          · exact hwnH h
          · exact hwY' h)
        hw (fun x hx => hwH x hx)
    have hHeven : Even (bigHole C k L v).length := by
      rw [hHlen, Nat.even_iff]
      rw [Nat.even_iff] at hLeven
      omega
    rcases hleap with h | h
    · exact BalancedNoLeap.not_leap_of_balanced hH hHeven hHY' hbal ha hb h
    · exact BalancedNoLeap.not_leap_of_balanced hH hHeven hHY' hbal ha hb h

/-! ## From the hat to the contradiction -/

private theorem anticonnected_singleton {G : SimpleGraph V} (c : V) :
    AnticonnectedSet G ({c} : Set V) := by
  intro u v
  have huv : u = v := Subtype.ext (u.2.trans v.2.symm)
  subst huv
  exact SimpleGraph.Reachable.refl u

private theorem arcCount_zero_of {G : SimpleGraph V} {Z : Set V} {C : List V} {k : ℕ} :
    ∀ m : ℕ, (∀ t, t < m → ¬ WheelParity.CycEdge G Z C (k + t)) →
      arcCount G Z C k m = 0 := by
  intro m
  induction m with
  | zero => intro _; exact arcCount_zero Z k
  | succ m ih =>
      intro h
      have e1 : arcCount G Z C k (m + 1) = arcCount G Z C k m + arcCount G Z C (k + m) 1 :=
        arcCount_split Z k m 1
      rw [e1, ih (fun t ht => h t (by omega)), arcCount_one_neg (h m (by omega))]

/-- PAPER: *"So there is a hat; that is, there exists `y ∈ Y'` with no neighbours in `H` except
`p_i, p_{i+1}`."*

This is the conclusion of the paper's case analysis *"Both these paths have length ≥ 2; suppose
they both have length 2 … So one of the paths has length > 2, and from the symmetry we may
assume that `j ≥ 4`."*, run against the configuration `no_config` has produced.  The three
cases are the ones listed in the module docstring.

-/
private theorem exists_hat [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s c : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length) (hnn : C.length = n) (hneven : Even n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t))
    (hvC : v ∉ C) (hvY' : v ∉ Y') (hvZ : ¬ VertexComplete G v Y')
    (hCY' : ∀ w ∈ C, w ∉ Y') (hY'anti : AnticonnectedSet G Y')
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hseven : Even s) (hsL : s + 1 < L)
    (hcodd : ¬ Even c) (hcL : L + 1 ≤ c) (hcn : c + 1 ≤ n - 2)
    (hvfull : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1)))
    (hcomplete : ∀ t, t < n →
      (VertexComplete G (D t) Y' ↔ (t = s ∨ t = s + 1 ∨ t = c ∨ t = c + 1))) :
    ∃ y ∈ Y', (∀ t, t ≤ L → (G.Adj y (D t) ↔ (t = s ∨ t = s + 1))) ∧ ¬ G.Adj y v := by
  have hBerge : Berge G := hG.1.1.1
  rcases lt_or_ge L 4 with hLlt | hL4
  · -- The two-edge first arc.  Its exceptional short case is disposed of by 15.5.
    have hL : L = 2 := by
      rw [Nat.even_iff] at hLeven
      omega
    have hs : s = 0 := by
      rw [Nat.even_iff] at hseven
      omega
    subst L
    subst s
    by_cases hc3 : c = 3
    · subst c
      exfalso
      let W : Set V := Y' ∪ {v}
      have hWanti : AnticonnectedSet G W :=
        KiteTailBasics.anticonnectedSet_union_singleton hY'anti hvZ
      have hWC : ∀ z ∈ W, z ∉ C := by
        intro z hzw hz
        rcases hzw with hzY | hzv
        · exact hCY' z hz hzY
        · rw [Set.mem_singleton_iff] at hzv
          exact hvC (hzv ▸ hz)
      let P : List V := arc C k 0 3
      have hP : IsPathFrom G P (D 0) (D 3) := by
        exact arc_isPathFrom' hC hn hD hnn (by omega) (by omega)
      have hPlen : pathLength P = 3 := by
        rw [PathBasics.pathLength_eq, arc_length C k 0 3 (by omega)]
      have honlyW : ∀ t, t < n → VertexComplete G (D t) W → (t = 0 ∨ t = 3) := by
        intro t ht htW
        have htY : VertexComplete G (D t) Y' := fun y hy => htW y (Or.inl hy)
        have htv : G.Adj v (D t) := (htW v (Or.inr rfl)).symm
        have h1 := (hcomplete t ht).mp htY
        have h2 := (hvfull t ht).mp htv
        omega
      have hD0W : VertexComplete G (D 0) W := by
        apply OddWheelSpan.vertexComplete_union.mpr
        refine ⟨(hcomplete 0 (by omega)).mpr (Or.inl rfl), ?_⟩
        exact ((hvfull 0 (by omega)).mpr (Or.inl rfl)).symm
      have hD3W : VertexComplete G (D 3) W := by
        apply OddWheelSpan.vertexComplete_union.mpr
        refine ⟨(hcomplete 3 (by omega)).mpr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
        exact ((hvfull 3 (by omega)).mpr (Or.inr (Or.inr (Or.inl rfl)))).symm
      have hint : ∀ z ∈ SPGT.interior P, ¬ VertexComplete G z W := by
        intro z hz hzW
        have hz' := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hz
        obtain ⟨t, ht0, ht3, rfl⟩ :=
          (arc_mem_iff hC hn hD hnn (show 0 ≤ 3 by omega) (by omega)).mp hz'.1
        rcases honlyW t (by omega) hzW with rfl | rfl
        · exact hz'.2.1 rfl
        · exact hz'.2.2 rfl
      have hPpre : ∃ r : ℕ, P <+: C.rotate r ∨ P.reverse <+: C.rotate r := by
        refine ⟨k, Or.inl ?_⟩
        simpa [P, arc] using (List.take_prefix (3 - 0 + 1) (C.rotate k))
      have hEven := Workspace.Statements.S15.SPGT.thm_15_5 G hG C hC W hWC hWanti
        P (D 0) (D 3) hP hPpre (by rw [hPlen]; omega) hD0W hD3W hint
      rw [hPlen, Nat.even_iff] at hEven
      omega
    · -- Use the complementary long hole, then recover the missing first-arc adjacency by 2.3.
      have hc5 : 5 ≤ c := by
        rw [Nat.even_iff] at hcodd
        omega
      have hn8 : 8 ≤ n := by omega
      let D' : ℕ → V := fun t => D (3 + t)
      have hD' : ∀ t : ℕ, C[((k + 3) + t) % C.length]? = some (D' t) := by
        intro t
        simpa [D', show k + 3 + t = k + (3 + t) by omega] using hD (3 + t)
      have hL'even : Even (n - 4) := by
        rw [Nat.even_iff] at hneven ⊢
        omega
      have hvD' : ∀ t, t ≤ n - 4 →
          (G.Adj v (D' t) ↔ (t = 0 ∨ t = n - 4)) := by
        intro t ht
        change G.Adj v (D (3 + t)) ↔ _
        rw [hvfull (3 + t) (by omega)]
        omega
      have hcomp' : ∀ t, t ≤ n - 4 →
          (VertexComplete G (D' t) Y' ↔ (t = c - 3 ∨ t = c - 3 + 1)) := by
        intro t ht
        change VertexComplete G (D (3 + t)) Y' ↔ _
        rw [hcomplete (3 + t) (by omega)]
        omega
      have hD1Y : VertexComplete G (D 1) Y' :=
        (hcomplete 1 (by omega)).mpr (Or.inr (Or.inl rfl))
      have hD1notY : D 1 ∉ Y' := hCY' _ (rim_mem hn hD 1)
      have hotherMem : ∀ z : V, z ∈ bigHole C (k + 3) (n - 4) v ↔
          ((∃ t, t ≤ n - 4 ∧ z = D' t) ∨ z = v) :=
        fun z => bigHole_mem_iff (v := v) hC hn hD' hnn (by omega)
      have hD1notH : D 1 ∉ bigHole C (k + 3) (n - 4) v := by
        intro hmem
        rcases (hotherMem (D 1)).mp hmem with ⟨t, ht, heq⟩ | heq
        · have : 1 = 3 + t :=
            rim_inj hC hn hD hnn (by omega) (by omega) (by simpa [D'] using heq)
          omega
        · exact hvC (by rw [← heq]; exact rim_mem hn hD 1)
      have hD1anti : ∀ z ∈ bigHole C (k + 3) (n - 4) v, ¬ G.Adj (D 1) z := by
        intro z hz
        rcases (hotherMem z).mp hz with ⟨t, ht, rfl⟩ | rfl
        · change ¬ G.Adj (D 1) (D (3 + t))
          rw [rim_adj hC hn hD hnn (by omega) (by omega)]
          omega
        · intro hadj
          have hv1 := (hvfull 1 (by omega)).mp hadj.symm
          omega
      obtain ⟨y, hyY', hyOther, hyv⟩ :=
        hat_of_hole (D := D') (k := k + 3) (n := n) (L := n - 4) (s := c - 3)
          hBerge hC hn hD' hnn hvC hvY' hvZ hCY' hY'anti (by omega) hL'even
          (by omega) hvD' (by omega) hcomp' (D 1) hD1Y hD1notY hD1notH hD1anti
      have hy0 : G.Adj y (D 0) :=
        ((hcomplete 0 (by omega)).mpr (Or.inl rfl) y hyY').symm
      have hy1 : G.Adj y (D 1) :=
        ((hcomplete 1 (by omega)).mpr (Or.inr (Or.inl rfl)) y hyY').symm
      have hyc : G.Adj y (D c) := by
        have h := (hyOther (c - 3) (by omega)).mpr (Or.inl rfl)
        change G.Adj y (D (3 + (c - 3))) at h
        convert h using 1 <;> congr <;> omega
      have hy2 : ¬ G.Adj y (D 2) := by
        intro hy2adj
        let Q : List V := arc C k 2 c
        have hQ : IsPathFrom G Q (D 2) (D c) :=
          arc_isPathFrom' hC hn hD hnn (by omega) (by omega)
        have hQlen : pathLength Q = c - 2 := by
          rw [PathBasics.pathLength_eq, arc_length C k 2 c (by omega)]
          omega
        have hCy : ∀ z ∈ C, z ∉ ({y} : Set V) := by
          intro z hz
          simp only [Set.mem_singleton_iff]
          intro hzy
          exact hCY' y (hzy ▸ hz) hyY'
        have honlyQ : ∀ t, 2 ≤ t → t ≤ c →
            VertexComplete G (D t) ({y} : Set V) → (t = 2 ∨ t = c) := by
          intro t ht2 htc htcomp
          by_cases ht : t = 2
          · exact Or.inl ht
          · have ht3 : 3 ≤ t := by omega
            have hadj : G.Adj y (D' (t - 3)) := by
              have := htcomp y rfl
              simpa [D', show 3 + (t - 3) = t by omega] using this.symm
            rcases (hyOther (t - 3) (by omega)).mp hadj with h | h
            · exact Or.inr (by omega)
            · exfalso; omega
        have hnoedge : ∀ a ∈ Q, ∀ b ∈ Q, ¬ EdgeComplete G ({y} : Set V) a b := by
          intro a ha b hb hE
          obtain ⟨ta, hta2, htac, rfl⟩ :=
            (arc_mem_iff hC hn hD hnn (show 2 ≤ c by omega) (by omega)).mp ha
          obtain ⟨tb, htb2, htbc, rfl⟩ :=
            (arc_mem_iff hC hn hD hnn (show 2 ≤ c by omega) (by omega)).mp hb
          have ha' := honlyQ ta hta2 htac hE.2.1
          have hb' := honlyQ tb htb2 htbc hE.2.2
          have hadj := (rim_adj hC hn hD hnn (by omega) (by omega)).mp hE.1
          omega
        have hQpre : ∃ r : ℕ, Q <+: C.rotate r := by
          refine ⟨k + 2, ?_⟩
          simpa [Q, arc] using (List.take_prefix (c - 2 + 1) (C.rotate (k + 2)))
        have hD2comp : VertexComplete G (D 2) ({y} : Set V) := by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          exact hz ▸ hy2adj.symm
        have hDccomp : VertexComplete G (D c) ({y} : Set V) := by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          exact hz ▸ hyc.symm
        rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge ({y} : Set V)
            (anticonnected_singleton y) C (Or.inr hC) hCy).1 Q (D 2) (D c)
            (Or.inr ⟨hC, hQpre⟩) hQ hD2comp hDccomp with hpar | honly
        · have hz : {e : Sym2 V | ∃ a ∈ Q, ∃ b ∈ Q,
              e = s(a, b) ∧ EdgeComplete G ({y} : Set V) a b}.ncard = 0 :=
            OddWheelClaimOneNoCore.yEdges_empty hnoedge
          rw [hz, hQlen] at hpar
          rw [Nat.even_iff] at hcodd
          omega
        · have hD0comp : VertexComplete G (D 0) ({y} : Set V) := by
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            exact hz ▸ hy0.symm
          rcases honly (D 0) (rim_mem hn hD 0) hD0comp with h | h
          · exact (rim_ne hC hn hD hnn (by omega) (by omega) (by omega)) h
          · exact (rim_ne hC hn hD hnn (by omega) (by omega) (by omega)) h
      refine ⟨y, hyY', ?_, hyv⟩
      intro t ht
      constructor
      · intro hadj
        rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hadj hy2
      · rintro (rfl | rfl)
        · exact hy0
        · exact hy1
  · -- This is the long first hole used verbatim in the printed proof.
    have hvD0 : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)) := by
      intro t ht
      rw [hvfull t (by omega)]
      omega
    have hcomp0 : ∀ t, t ≤ L →
        (VertexComplete G (D t) Y' ↔ (t = s ∨ t = s + 1)) := by
      intro t ht
      rw [hcomplete t (by omega)]
      omega
    have hc1Y : VertexComplete G (D (c + 1)) Y' :=
      (hcomplete (c + 1) (by omega)).mpr (Or.inr (Or.inr (Or.inr rfl)))
    have hc1notY : D (c + 1) ∉ Y' := hCY' _ (rim_mem hn hD (c + 1))
    have hmem : ∀ z : V, z ∈ bigHole C k L v ↔
        ((∃ t, t ≤ L ∧ z = D t) ∨ z = v) :=
      fun z => bigHole_mem_iff (v := v) hC hn hD hnn (by omega)
    have hc1notH : D (c + 1) ∉ bigHole C k L v := by
      intro hz
      rcases (hmem (D (c + 1))).mp hz with ⟨t, ht, heq⟩ | heq
      · have := rim_inj hC hn hD hnn (by omega) (by omega) heq
        omega
      · exact hvC (by rw [← heq]; exact rim_mem hn hD (c + 1))
    have hc1anti : ∀ z ∈ bigHole C k L v, ¬ G.Adj (D (c + 1)) z := by
      intro z hz
      rcases (hmem z).mp hz with ⟨t, ht, rfl⟩ | rfl
      · rw [rim_adj hC hn hD hnn (by omega) (by omega)]
        omega
      · intro hadj
        have hv := (hvfull (c + 1) (by omega)).mp hadj.symm
        omega
    exact hat_of_hole hBerge hC hn hD hnn hvC hvY' hvZ hCY' hY'anti hL4 hLeven
      (by omega) hvD0 hsL hcomp0 (D (c + 1)) hc1Y hc1notY hc1notH hc1anti

/-! ## The NO branch of claim (1), completed -/

/-- **The NO branch of claim (1) of 16.1.**

PAPER: *"This proves that `v` has no neighbour in `{p_{j+2},…,p_{n−1}}`. …"* down to the end of
the proof of claim (1).  The configuration analysis is
`OddWheelClaimOneNoCore.no_config`; what is added here is the final paragraph transcribed in the
module docstring.

`hmin` is the minimality of `Y'` produced by `OddWheelArc.exists_minimal` (*"Choose `Y' ⊆ Y`
minimal such that `Y'` is anticonnected and there are an odd number of `Y'`-complete edges in
`P`"*). -/
theorem branch_no [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y Y' : Set V} {v : V} {D : ℕ → V} {k n L s : ℕ}
    (hw : IsWheel G C Y)
    (hC : IsHoleList G C) (hn : 0 < C.length) (hn6 : 6 ≤ n) (hneven : Even n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hvC : v ∉ C) (hvY : v ∉ Y)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hY'Y : Y' ⊆ Y) (hY'anti : AnticonnectedSet G Y') (hvY' : v ∉ Y')
    (hvZ : ¬ VertexComplete G v Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hmin : ∀ Z : Set V, Z ⊆ Y' → AnticonnectedSet G Z →
      Odd (arcCount G Z C k L) → ¬ VertexComplete G v Z → Z = Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hfar : ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y')
    (hno : ∀ t, L + 2 ≤ t → t ≤ n - 2 → ¬ G.Adj v (D t)) :
    False := by
  have hBerge : Berge G := hG.1.1.1
  -- *"This proves that `v` has no neighbour in `{p_{j+2},…,p_{n−1}}` … So `m = k+1`."*
  obtain ⟨c, hcodd, hcL, hcn, hvfull, hcomplete⟩ :=
    OddWheelClaimOneNoCore.no_config hG hC hn hnn hneven hD hvC hL1 hLeven hn4 hvD hY'anti hvY'
      hvZ hCY' hseven hsL hcs hcs1 honly hfar hno
  -- *"So there is a hat; that is, there exists `y ∈ Y'` with no neighbours in `H` except
  -- `p_i, p_{i+1}`."*
  obtain ⟨y, hyY', hyarc, hyv⟩ :=
    exists_hat hG hC hn hnn hneven hD hvC hvY' hvZ hCY' hY'anti hL1 hLeven hn4 hseven hsL
      hcodd hcL hcn hvfull hcomplete
  -- the arc `p₁-⋯-p_j` carries exactly one `{y}`-complete edge, namely `p_i p_{i+1}`
  have hedge : ∀ j, j < L → (WheelParity.CycEdge G ({y} : Set V) C (k + j) ↔ j = s) := by
    intro j hj
    have hb : C[(k + j + 1) % C.length]? = some (D (j + 1)) := by
      have h4 := hD (j + 1)
      rwa [show k + (j + 1) = k + j + 1 from by omega] at h4
    rw [cycEdge_iff' (hD j) hb]
    constructor
    · intro hE
      have h1 : G.Adj (D j) y := hE.2.1 y rfl
      have h2 : G.Adj (D (j + 1)) y := hE.2.2 y rfl
      rcases (hyarc j (by omega)).mp h1.symm with h | h
      · exact h
      · exfalso
        rcases (hyarc (j + 1) (by omega)).mp h2.symm with h' | h' <;> omega
    · rintro rfl
      refine ⟨(rim_adj hC hn hD hnn (show j < n by omega) (show j + 1 < n by omega)).mpr
        (Or.inl rfl), ?_, ?_⟩
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((hyarc j (by omega)).mpr (Or.inl rfl)).symm
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((hyarc (j + 1) (by omega)).mpr (Or.inr rfl)).symm
  have harc : Odd (arcCount G ({y} : Set V) C k L) := by
    have e1 : arcCount G ({y} : Set V) C k L
        = arcCount G ({y} : Set V) C k s + arcCount G ({y} : Set V) C (k + s) (L - s) := by
      have h4 := arcCount_split (G := G) (C := C) ({y} : Set V) k s (L - s)
      rwa [show s + (L - s) = L from by omega] at h4
    have e2 : arcCount G ({y} : Set V) C (k + s) (L - s)
        = arcCount G ({y} : Set V) C (k + s) 1
          + arcCount G ({y} : Set V) C (k + s + 1) (L - s - 1) := by
      have h4 := arcCount_split (G := G) (C := C) ({y} : Set V) (k + s) 1 (L - s - 1)
      rwa [show 1 + (L - s - 1) = L - s from by omega] at h4
    have z1 : arcCount G ({y} : Set V) C k s = 0 :=
      arcCount_zero_of s (fun t ht => by rw [hedge t (by omega)]; omega)
    have z2 : arcCount G ({y} : Set V) C (k + s + 1) (L - s - 1) = 0 := by
      refine arcCount_zero_of (k := k + s + 1) (L - s - 1) (fun t ht => ?_)
      rw [show k + s + 1 + t = k + (s + 1 + t) from by omega, hedge (s + 1 + t) (by omega)]
      omega
    have o1 : arcCount G ({y} : Set V) C (k + s) 1 = 1 :=
      arcCount_one_pos ((hedge s (by omega)).mpr rfl)
    rw [e1, e2, z1, z2, o1]
    norm_num
  -- *"From the minimality of `Y'` it follows that `Y' = {y}`."*
  have hYy : Y' = ({y} : Set V) :=
    (hmin ({y} : Set V) (Set.singleton_subset_iff.mpr hyY') (anticonnected_singleton y) harc
      (fun hvc => hyv (hvc y rfl).symm)).symm
  -- the neighbours of `y` on the whole rim
  have hyfull : ∀ t, t < n → (G.Adj y (D t) ↔ (t = s ∨ t = s + 1 ∨ t = c ∨ t = c + 1)) := by
    intro t ht
    rw [← hcomplete t ht, hYy]
    constructor
    · intro h z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h.symm
    · intro h
      exact (h y rfl).symm
  -- *"But then `G|(V(C) ∪ {v,y})` is the line graph of a bipartite subdivision of `K₄`."*
  exact CycleTwoChordsAppearance.no_two_hub_rim hG hC hn hnn hD hvC
    (fun h => hCY' y h (hYy ▸ rfl)) (fun h => hyv h.symm)
    (Nat.even_iff.mp hneven) (Nat.even_iff.mp hLeven) (Nat.even_iff.mp hseven)
    (Nat.not_even_iff.mp hcodd) hsL hcL hcn hvfull hyfull

end Workspace.ProofLemmas.OddWheelClaimOneNoEnd
