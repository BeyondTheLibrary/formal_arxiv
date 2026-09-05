import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm186Setup
import Workspace.ProofLemmas.Thm186Claim1
import Workspace.ProofLemmas.Thm186FSizeTwo
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.SubpathIsSlice
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.Thm183EdgeCount
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentClaim2
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S18.Thm_18_3
import Workspace.Statements.S18.Thm_18_4

/-!
# 18.6, claim (2)

PAPER (`paper/proofs/18_6.md`, published page 114):

> *"(2) There do not exist `a, b` with `1 < a < b ≤ n` such that `p_a` is an attachment of `F`
> and `p_b` is `Y`-complete.*
>
> *For suppose that such `a, b` exist.  From (1), there is an `X`-complete vertex in `F`; and
> from the minimality of `F`, there is a path `p_a-f₁-⋯-f_k` such that `F = {f₁, …, f_k}` and
> `f_k` is the unique `X`-complete vertex in `F`.  Let `W₁` be the set of attachments of
> `F \ {f_k}` in `P`, and `W₂` the set of attachments of `F \ {f₁}` in `P`.  From the minimality
> of `F`, for `i = 1, 2` there is a subpath `p_{a_i}-⋯-p_{b_i}` of `P` (`= P_i` say), such that
> no internal vertex of `P_i` is `Y`-complete, and `W_i ⊆ V(P_i)`, and either `b₂ = n` or
> `a₂ = b₂ = 1`.*
>
> *First assume that `b₂ = n`.  Choose `P₁, P₂` minimal; then `p_{a₁}` is a neighbour of `f₁`,
> and `p₁-⋯-p_{a₁}-f₁-⋯-f_k` is a path `P'` say.  Suppose that there is a `Y`-complete vertex in
> `P'` different from `p₁`.  Then `P'` has length `≥ 4`, and `(X,Y,P')` is a pseudowheel,
> contrary to the optimality of `(X,Y,P)`.  So there are no `Y`-complete vertices in `P'`.  But
> also there are none in `{p_{a₁+1}, …, p_{b₁-1}}` and none in `{p_{a₂+1}, …, p_{b₂-1}}`, so all
> the `Y`-complete vertices of `P` belong to `{p_{b₁}, …, p_{a₂}}`, except for `p₁`.  By 18.4
> there are an odd number, at least `3`, of `Y`-complete edges in this path.  From the minimality
> of `F`, `f₁-⋯-f_k-p_{a₂}-p_{a₂-1}-⋯-p_{b₁}-f₁` is a hole, which therefore also contains an odd
> number `≥ 3` of `Y`-complete edges.  But this contradicts 2.3.*
>
> *So we may assume that `a₂ = b₂ = 1`, and that `p₁ ∈ W₂`, and therefore `b₁ > 1`.  From the
> minimality of `F` there are no edges between `F \ {f₁}` and `V(P \ p₁)`.  Choose `P₁` minimal.
> So `p_{b₁}` is adjacent to `f₁`, and either `a₁ = 1` or `p_{a₁}` is adjacent to `f₁`.  Suppose
> first that an odd number of edges of the path `p₁-⋯-p_{a₁}` are `Y`-complete.  Hence `p₁` has
> no neighbours in `F \ {f_k}`, and so `f₁-⋯-f_k-p₁-⋯-p_{a₁}-f₁` is a hole.  It contains an odd
> number of `Y`-complete edges, and at least three `Y`-complete vertices, because `p₁` is
> `Y`-complete and `p₂` is not, a contradiction to 2.3.  So there are an even number of
> `Y`-complete edges in the path `p₁-⋯-p_{a₁}`, and therefore an odd number in `p_{b₁}-⋯-p_n`,
> since there are an odd number in `P`, and none in `P₁`.  Therefore there are an odd number in
> the path `f_k-⋯-f₁-p_{b₁}-⋯-p_n` (`= R` say).  But an edge of `p_{b₁}-⋯-p_n` is `Y`-complete
> and `p_n` is not, so `b₂ ≤ n − 2`; and since `k ≥ 2`, it follows that `R` has length `≥ 4`.
> Also, at least two vertices of `R` are `Y`-complete, and its ends are not `Y`-complete, and its
> ends are its only `X`-complete vertices.  This contradicts 18.3.  So there is no such `F`.
> This proves (2)."*

Cited results: claim (1), 18.3, 18.4, 2.3, and the optimality clause of `OptimalPseudowheel`.

Index convention: the paper's `p_a` is `P[a-1]` (0-indexed), so *"`1 < a < b ≤ n`"* becomes
`0 < a < b < P.length` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm186Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm186Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Greatest index below `n` satisfying `Q`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ n : ℕ, (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  classical
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- Every stretch of a list is an infix. -/
private theorem slice_infix (p : List V) (i m : ℕ) : (p.drop i).take m <:+: p := by
  refine ⟨p.take i, (p.drop i).drop m, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- A one-vertex stretch is an infix. -/
private theorem singleton_infix {W : Type*} {l : List W} {x : W} (h : x ∈ l) : [x] <:+: l := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem h
  exact ⟨s, t, by rw [hst]; simp⟩

/-- Rewriting a dependent list index. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h
  rfl

/-- Positional `Y`-edge counts commute with taking an initial segment. -/
private theorem yEdgeIdx_take_ncard (G : SimpleGraph V) (Y : Set V) (p : List V)
    {a : ℕ} (ha : a < p.length) :
    (Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (p.take (a + 1))).ncard =
      {k : ℕ | k ∈ Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y p ∧ k < a}.ncard := by
  classical
  let A := Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (p.take (a + 1))
  let B := {k : ℕ | k ∈ Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y p ∧ k < a}
  refine Set.ncard_congr (s := A) (t := B) (fun k _ => k) ?_ ?_ ?_
  · intro k hk
    change k ∈ A at hk
    change k ∈ B
    rcases hk with ⟨hk, hkY, hk1Y⟩
    have htake : (p.take (a + 1)).length = a + 1 := by simp; omega
    have hkP : k + 1 < p.length := by rw [htake] at hk; omega
    refine ⟨⟨hkP, ?_, ?_⟩, by rw [htake] at hk; omega⟩
    · simpa only [List.getElem_take] using hkY
    · simpa only [List.getElem_take] using hk1Y
  · intro k l hk hl he
    change k = l at he
    exact he
  · intro k hk
    change k ∈ B at hk
    rcases hk with ⟨⟨hk, hkY, hk1Y⟩, hka⟩
    have htake : (p.take (a + 1)).length = a + 1 := by simp; omega
    have hkTake : k + 1 < (p.take (a + 1)).length := by rw [htake]; omega
    refine ⟨k, ⟨hkTake, ?_, ?_⟩, rfl⟩
    · simpa only [List.getElem_take] using hkY
    · simpa only [List.getElem_take] using hk1Y

/-- Positional `Y`-edge counts commute with dropping an initial segment, up to translating
the index. -/
private theorem yEdgeIdx_drop_ncard (G : SimpleGraph V) (Y : Set V) (p : List V)
    {b : ℕ} (hb : b < p.length) :
    (Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (p.drop b)).ncard =
      {k : ℕ | k ∈ Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y p ∧ b ≤ k}.ncard := by
  classical
  let A := Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (p.drop b)
  let B := {k : ℕ | k ∈ Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y p ∧ b ≤ k}
  refine Set.ncard_congr (s := A) (t := B) (fun k _ => b + k) ?_ ?_ ?_
  · intro k hk
    change k ∈ A at hk
    change b + k ∈ B
    rcases hk with ⟨hk, hkY, hk1Y⟩
    have hkP : b + k + 1 < p.length := by simp only [List.length_drop] at hk; omega
    refine ⟨⟨hkP, ?_, ?_⟩, by omega⟩
    · simpa only [List.getElem_drop] using hkY
    · simpa only [List.getElem_drop] using hk1Y
  · intro k l hk hl he
    change b + k = b + l at he
    omega
  · intro j hj
    change j ∈ B at hj
    rcases hj with ⟨⟨hj, hjY, hj1Y⟩, hbj⟩
    let k := j - b
    have hkeq : b + k = j := by dsimp [k]; omega
    have hkDrop : k + 1 < (p.drop b).length := by simp only [List.length_drop]; omega
    refine ⟨k, ⟨hkDrop, ?_, ?_⟩, hkeq⟩
    · simpa only [List.getElem_drop, hkeq] using hjY
    · have heq1 : b + (k + 1) = j + 1 := by omega
      simpa only [List.getElem_drop, heq1] using hj1Y

/-- The second entry of a list, read off its tail. -/
private theorem tail_head?_getElem {W : Type*} {l : List W} (h : 1 < l.length) :
    l.tail.head? = some (l[1]'h) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < l.tail.length by simp; omega)]
  simp

/-- A slice with possibly equal endpoints, packaged with its named ends. -/
private theorem isPathFrom_slice_le {G : SimpleGraph V} {p : List V} (h : IsPathList G p)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) := by
  refine ⟨?_, PathBasics.head?_slice p hij hj, PathBasics.getLast?_slice p hij hj⟩
  rcases eq_or_lt_of_le hij with he | hlt
  · have hlen : ((p.drop i).take (j - i + 1)).length = 1 := by
      rw [PathBasics.length_slice p hij hj]
      omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx]
    exact PathBasics.isPathList_singleton G x
  · exact PathBasics.isPathList_slice h hlt hj

/-- Removing the first and last vertices from a hole leaves the long arc between their
neighbours. -/
private theorem isPathList_hole_interior {G : SimpleGraph V} {q : List V}
    (hq : IsHoleList G q) :
    IsPathList G ((q.drop 1).take (q.length - 2)) := by
  have hn : 4 ≤ q.length := hq.1
  have hMlen : ((q.drop 1).take (q.length - 2)).length = q.length - 2 := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    rw [hnil] at hMlen
    simp at hMlen
    omega
  · exact List.Nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hq.2.1
  · intro s t hs ht
    have hs2 : s < q.length - 2 := by omega
    have ht2 : t < q.length - 2 := by omega
    have es : ((q.drop 1).take (q.length - 2))[s]'hs = q[1 + s]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
    have et : ((q.drop 1).take (q.length - 2))[t]'ht = q[1 + t]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
    rw [es, et, hq.2.2 (1 + s) (1 + t) (by omega) (by omega),
      Nat.mod_eq_of_lt (show 1 + s + 1 < q.length by omega),
      Nat.mod_eq_of_lt (show 1 + t + 1 < q.length by omega)]
    omega

/-- A leap at an edge of an even hole cannot have a common neighbour which is anticomplete
to the hole: the long arc between the two leap vertices, closed through that common
neighbour, is an odd hole. -/
private theorem leap_common_neighbor_contra {G : SimpleGraph V} (hBerge : Berge G)
    {c : List V} (hc : IsHoleList G c) {u v a b x : V}
    (hleap : IsLeapForHole G c u v a b) (hxC : x ∉ c)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hxanti : ∀ z ∈ c, ¬ G.Adj x z) : False := by
  classical
  obtain ⟨-, i, hhead, hlast, hlp⟩ := hleap
  let p : List V := c.rotate i
  have hp : IsHoleList G p := by
    simpa [p] using HoleBasics.isHoleList_rotate hc i
  have hpEven : Even p.length := by
    rw [show p.length = c.length by simp [p]]
    exact hBerge.1 c hc
  have hpc : ∀ z : V, z ∈ p ↔ z ∈ c := fun z => by simp [p]
  have hxP : x ∉ p := fun h => hxC ((hpc x).mp h)
  have hpos : 0 < p.length := by have := hp.1; omega
  have huP : u ∈ p := by
    have hp' : p.getLast? = some u := by simpa [p] using hlast
    exact PathBasics.getLast_mem hp'
  have hvP : v ∈ p := by
    have hp' : p.head? = some v := by simpa [p] using hhead
    exact PathBasics.head_mem hp'
  obtain ⟨hdelPath0, -, hab_ne, hab_nadj', hAd, hBd⟩ := hlp
  have hdelPath : IsPathList (G.deleteEdges {s(u, v)}) p := by
    simpa [p] using hdelPath0
  have hn4p : 4 ≤ p.length := hp.1
  have hAdp : ∀ (k : ℕ) (hk : k < p.length),
      ((G.deleteEdges {s(u, v)}).Adj a (p[k]'hk) ↔
        (k = 0 ∨ k = 1 ∨ k = p.length - 1)) := by
    simpa [p] using hAd
  have hBdp : ∀ (k : ℕ) (hk : k < p.length),
      ((G.deleteEdges {s(u, v)}).Adj b (p[k]'hk) ↔
        (k = 0 ∨ k = p.length - 2 ∨ k = p.length - 1)) := by
    simpa [p] using hBd
  have hanot : a ∉ p := by
    intro haP
    have ha0 : (G.deleteEdges {s(u, v)}).Adj a (p[0]'hpos) :=
      (hAdp 0 hpos).mpr (Or.inl rfl)
    obtain ⟨k, hk, hka⟩ := List.getElem_of_mem haP
    have h0 : (G.deleteEdges {s(u, v)}).Adj (p[k]'hk) (p[0]'hpos) := by
      rw [hka]
      exact ha0
    have hk1 : k = 1 := by
      rcases (PathBasics.path_adj_iff hdelPath hk hpos).mp h0 with h | h <;> omega
    have haa : (G.deleteEdges {s(u, v)}).Adj a a := by
      have ha1 := (hAdp k hk).mpr (Or.inr (Or.inl hk1))
      simpa [hka] using ha1
    exact (G.deleteEdges {s(u, v)}).irrefl haa
  have hbnot : b ∉ p := by
    intro hbP
    have hb0 : (G.deleteEdges {s(u, v)}).Adj b (p[0]'hpos) :=
      (hBdp 0 hpos).mpr (Or.inl rfl)
    have hbLast : (G.deleteEdges {s(u, v)}).Adj b (p[p.length - 1]'(by omega)) :=
      (hBdp (p.length - 1) (by omega)).mpr (Or.inr (Or.inr rfl))
    obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hbP
    have h0 : (G.deleteEdges {s(u, v)}).Adj (p[k]'hk) (p[0]'hpos) := by
      rw [hkb]
      exact hb0
    have hk1 : k = 1 := by
      rcases (PathBasics.path_adj_iff hdelPath hk hpos).mp h0 with h | h <;> omega
    have hlastAdj : (G.deleteEdges {s(u, v)}).Adj (p[k]'hk)
        (p[p.length - 1]'(by omega)) := by
      rw [hkb]
      exact hbLast
    rcases (PathBasics.path_adj_iff hdelPath hk (by omega)).mp hlastAdj with h | h <;> omega
  have htrans : ∀ z ∈ p, ∀ w : V, w ∉ p →
      ((G.deleteEdges {s(u, v)}).Adj w z ↔ G.Adj w z) := by
    intro z hz w hw
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hw (h1 ▸ huP)
    · exact hw (h1 ▸ hvP)
  have hab_nadj : ¬ G.Adj a b := by
    intro hab
    apply hab_nadj'
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hab, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hanot (h1 ▸ huP)
    · exact hanot (h1 ▸ hvP)
  have hAg : ∀ (k : ℕ) (hk : k < p.length),
      (G.Adj a (p[k]'hk) ↔ (k = 0 ∨ k = 1 ∨ k = p.length - 1)) := by
    intro k hk
    rw [← htrans (p[k]'hk) (List.getElem_mem hk) a hanot]
    exact hAdp k hk
  have hBg : ∀ (k : ℕ) (hk : k < p.length),
      (G.Adj b (p[k]'hk) ↔ (k = 0 ∨ k = p.length - 2 ∨ k = p.length - 1)) := by
    intro k hk
    rw [← htrans (p[k]'hk) (List.getElem_mem hk) b hbnot]
    exact hBdp k hk
  let M : List V := (p.drop 1).take (p.length - 2)
  have hMlen : M.length = p.length - 2 := by simp [M]; omega
  have hn4 : 4 ≤ p.length := hp.1
  have hidx : p.length - 2 - 1 + 1 = p.length - 2 := by omega
  have hMpath : IsPathList G M := by simpa [M] using isPathList_hole_interior hp
  have hMfrom : IsPathFrom G M (p[1]'(by omega)) (p[p.length - 2]'(by omega)) := by
    refine ⟨hMpath, ?_, ?_⟩
    · have h := PathBasics.head?_slice p (i := 1) (j := p.length - 2) (by omega) (by omega)
      rw [hidx] at h
      simpa [M] using h
    · have h := PathBasics.getLast?_slice p (i := 1) (j := p.length - 2)
          (by omega) (by omega)
      rw [hidx] at h
      simpa [M] using h
  have hMmem : ∀ z : V, z ∈ M ↔
      ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ k ≤ p.length - 2 ∧ p[k]'hk = z := by
    intro z
    have h := PathBasics.mem_slice_iff p (i := 1) (j := p.length - 2) (x := z)
      (by omega) (by omega)
    rw [hidx] at h
    simpa [M] using h
  have hMC : ∀ z ∈ M, z ∈ c := by
    intro z hz
    obtain ⟨k, hk, -, -, rfl⟩ := (hMmem z).mp hz
    exact (hpc _).mp (List.getElem_mem hk)
  have hadja : G.Adj a (p[1]'(by omega)) := (hAg 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hadjb : G.Adj b (p[p.length - 2]'(by omega)) :=
    (hBg (p.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
  have haM : a ∉ M := fun h => hanot ((hpc a).mpr (hMC a h))
  have hbM : b ∉ M := fun h => hbnot ((hpc b).mpr (hMC b h))
  have hsother : ∀ z ∈ M, z ≠ p[1]'(by omega) → ¬ G.Adj a z := by
    intro z hz hz1 haz
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem z).mp hz
    have hcases := (hAg k hk).mp haz
    have hkEq : k = 1 := by omega
    exact hz1 (hp.2.1.getElem_inj_iff.mpr hkEq)
  have htother : ∀ z ∈ M, z ≠ p[p.length - 2]'(by omega) → ¬ G.Adj b z := by
    intro z hz hz1 hbz
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem z).mp hz
    have hcases := (hBg k hk).mp hbz
    have hkEq : k = p.length - 2 := by omega
    exact hz1 (hp.2.1.getElem_inj_iff.mpr hkEq)
  let L : List V := a :: (M ++ [b])
  have hL : IsPathFrom G L a b := by
    simpa [L] using PathAttach.isPathFrom_cons_concat hMfrom hadja hadjb hab_nadj hab_ne
      haM hbM hsother htother
  have hLlen : L.length = p.length := by
    have hplen : pathLength L = p.length - 1 := by
      simp only [L, PathAttach.pathLength_cons_append_singleton, hMlen]
      omega
    have := PathBasics.length_eq_pathLength_add_one hL.1
    omega
  have hxL : x ∉ L := by
    intro hx
    change x ∈ a :: (M ++ [b]) at hx
    rcases PathAttach.mem_cons_append_singleton.mp hx with h | h | h
    · exact hxa.ne h
    · exact hxC (hMC x h)
    · exact hxb.ne h
  have hxPath : IsPathFrom G [x] x x :=
    ⟨PathBasics.isPathList_singleton G x, rfl, rfl⟩
  have hHole : IsHoleList G (L ++ [x]) := by
    refine PathGlue.glue_hole hL hxPath ?_ ?_ (by simp [hLlen]; omega)
    · intro z hz hzx
      simp only [List.mem_singleton] at hzx
      subst z
      exact hxL hz
    · intro z hz y hy
      simp only [List.mem_singleton] at hy
      subst y
      constructor
      · intro hzx
        change z ∈ a :: (M ++ [b]) at hz
        rcases PathAttach.mem_cons_append_singleton.mp hz with h | h | h
        · exact Or.inr ⟨h, rfl⟩
        · exact absurd hzx (fun hadj => hxanti z (hMC z h) hadj.symm)
        · exact Or.inl ⟨h, rfl⟩
      · rintro (⟨hz, -⟩ | ⟨hz, -⟩)
        · subst z; exact hxb.symm
        · subst z; exact hxa.symm
  have hEvenNew : Even (holeLength (L ++ [x])) := hBerge.1 _ hHole
  obtain ⟨r, hr⟩ := hpEven
  obtain ⟨s, hs⟩ := hEvenNew
  simp only [holeLength, List.length_append, List.length_singleton, hLlen] at hs
  omega

/-- Two disjoint capped edges of a long hole, joined outside the hole by an induced path,
form a long prism. -/
private theorem two_caps_contra {G : SimpleGraph V} (hG : InF7 G)
    {C : List V} (hC : IsHoleList G C) (hC6 : 6 ≤ C.length)
    {u v c d g₁ g₂ : V} {S : List V}
    (huC : u ∈ C) (hvC : v ∈ C) (huv : G.Adj u v)
    (hcC : c ∈ C) (hdC : d ∈ C) (hcd : G.Adj c d)
    (huc : u ≠ c) (hud : u ≠ d) (hvc : v ≠ c) (hvd : v ≠ d)
    (hS : IsPathFrom G S g₁ g₂) (hg : g₁ ≠ g₂)
    (hSC : ∀ z ∈ S, z ∉ C)
    (hcross : ∀ z ∈ S, ∀ w ∈ C, G.Adj z w ↔
      ((z = g₁ ∧ (w = u ∨ w = v)) ∨ (z = g₂ ∧ (w = c ∨ w = d)))) : False := by
  classical
  open Workspace.ProofLemmas.OddWheelAttachmentArcs in
    obtain ⟨D, hD, hDlen, hDmem, hpos, hone, hD0, hD1⟩ :=
      exists_reorient hC huC hvC huv
  have hposD : 0 < D.length := hpos
  have hcyc0 :
      Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD 0 = u := by
    rw [Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc_eq hposD hpos]
    exact hD0
  have hcyc1 :
      Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD 1 = v := by
    rw [Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc_eq hposD hone]
    exact hD1
  have hD6 : 6 ≤ D.length := by omega
  obtain ⟨sc, hsc, hscc⟩ :=
    Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc_surj hposD ((hDmem c).mpr hcC)
  obtain ⟨sd, hsd, hsdd⟩ :=
    Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc_surj hposD ((hDmem d).mpr hdC)
  have hsc0 : sc ≠ 0 := fun he => huc (by rw [← hscc, he, hcyc0])
  have hsc1 : sc ≠ 1 := fun he => hvc (by rw [← hscc, he, hcyc1])
  have hsd0 : sd ≠ 0 := fun he => hud (by rw [← hsdd, he, hcyc0])
  have hsd1 : sd ≠ 1 := fun he => hvd (by rw [← hsdd, he, hcyc1])
  have hidx := Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc_adj_index hD hposD hsc hsd
    (by rw [hscc, hsdd]; exact hcd)
  have hkey : ∀ (c' d' : V) (s t : ℕ), s < D.length → t < D.length →
      Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD s = c' →
      Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD t = d' →
      t = s + 1 → 2 ≤ s → s + 2 ≤ D.length →
      (c' = c ∨ c' = d) → (d' = c ∨ d' = d) → c' ≠ d' → False := by
    intro c' d' s t hs ht hc' hd' hst hs2 hslen hc'cd hd'cd hc'd'
    have hprism := Workspace.ProofLemmas.OddWheelAttachmentClaim2.long_prism
      hD hposD hD6 hs2 hslen hS hg
      (by intro z hz hzD; exact hSC z hz ((hDmem z).mp hzD))
      (by
        intro z hz w hw
        have hwC : w ∈ C := (hDmem w).mp hw
        rw [hcyc0, hcyc1, show
          Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD s = c' from hc',
          show Workspace.ProofLemmas.OddWheelAttachmentArcs.cyc D hposD (s + 1) = d' from
            (hst ▸ hd')]
        constructor
        · intro hzw
          rcases (hcross z hz w hwC).mp hzw with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h.1, ?_⟩
            rcases h.2 with hwc | hwd <;> aesop
        · rintro (h | h)
          · exact (hcross z hz w hwC).mpr (Or.inl h)
          · refine (hcross z hz w hwC).mpr (Or.inr ⟨h.1, ?_⟩)
            rcases h.2 with hwc' | hwd' <;> aesop)
    obtain ⟨A, B, P₁, P₂, P₃, hprism'⟩ := hprism
    exact hG.1.1.2.1 ⟨A, B, P₁, P₂, P₃, hprism'⟩
  have hcdne : c ≠ d := hcd.ne
  rcases hidx with e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hkey c d sc sd hsc hsd hscc hsdd e (by omega) (by omega)
      (Or.inl rfl) (Or.inr rfl) hcdne
  · exact hkey d c sd sc hsd hsc hsdd hscc e (by omega) (by omega)
      (Or.inr rfl) (Or.inl rfl) hcdne.symm
  · exact hsc0 e1
  · exact hsd0 e1

/-- The structural data produced by the first half of the printed claim-(2) argument.  Keeping
this package in an opaque declaration prevents the dependent list-index proof from being
reduced again in each of the two parity cases. -/
private structure Frame (G : SimpleGraph V) (X Y : Set V) (P : List V) (F : Set V)
    (a b : ℕ) (halen : a < P.length) where
  Q : List V
  hQl : IsPathList G Q
  hQlen3 : 3 ≤ Q.length
  hQfrom : IsPathFrom G Q (P[a]'halen) (Q[Q.length - 1]'(by omega))
  htailF : ∀ z : V, z ∈ Q.tail ↔ z ∈ F
  hFmem : ∀ z : V, z ∈ F ↔
    ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ Q[i]'hi = z
  hfkX : VertexComplete G (Q[Q.length - 1]'(by omega)) X
  huniqueX : ∀ z ∈ F, VertexComplete G z X → z = Q[Q.length - 1]'(by omega)
  α : ℕ
  β : ℕ
  a₂ : ℕ
  b₂ : ℕ
  hαlt : α < P.length
  hβlt : β < P.length
  ha₂lt : a₂ < P.length
  hb₂lt : b₂ < P.length
  hαa : α ≤ a
  haβ : a ≤ β
  hβb : β ≤ b
  hαatt : P[α]'hαlt ∈
    attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P}
  hβatt : P[β]'hβlt ∈
    attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P}
  hW₁range : ∀ (j : ℕ) (hj : j < P.length),
    P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
      α ≤ j ∧ j ≤ β
  hαβnoY : ∀ (j : ℕ) (hj : j < P.length), α < j → j < β →
    ¬ VertexComplete G (P[j]'hj) Y
  hP₂noY : ∀ (j : ℕ) (hj : j < P.length), a₂ < j → j < b₂ →
    ¬ VertexComplete G (P[j]'hj) Y
  hP₂ends : (a₂ = 0 ∧ b₂ = 0) ∨ b₂ = P.length - 1
  hW₂range : ∀ (j : ℕ) (hj : j < P.length),
    P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} →
      a₂ ≤ j ∧ j ≤ b₂

/-- The opaque structural half of claim (2). -/
private theorem exists_frame (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b)
    (haatt : (P[a]'halen) ∈ attachments G F {w : V | w ∈ P})
    (hbY : VertexComplete G (P[b]'hblen) Y) :
    ∃ fr : Frame G X Y P F a b halen, True := by
  classical
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY0⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hBerge : Berge G := hG.1.1.1.1
  have hq₁ : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
  have hqn : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have hXuniq : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
    intro v hv
    rw [← hq₁, ← hqn]
    exact hXuniq0 v hv
  have hp₁Y : VertexComplete G p₁ Y := by rw [← hq₁]; exact hq₁Y
  have hpₙY : ¬ VertexComplete G pₙ Y := by rw [← hqn]; exact hqₙY0
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have h1lt : 1 < P.length := by omega
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hFP : ∀ f ∈ F, f ∉ P := fun f hf => (hmin.1.1 f hf).2
  have hFXY : ∀ f ∈ F, f ∉ X ∪ Y := fun f hf => (hmin.1.1 f hf).1
  have hFY : ∀ f ∈ F, ¬ VertexComplete G f Y := hmin.1.2.2
  have hFconn : ConnectedSet G F := hmin.1.2.1
  have hPY : ∀ w ∈ P, w ∉ Y := fun w hw => (hPXY w hw).2
  have hFcard : 2 ≤ F.ncard :=
    Thm186FSizeTwo.two_le_ncard_of_counterexample G hG X Y P p₁ pₙ hopt hhead hlast F
      hmin.1 hmin.2.1
  -- Claim (1) supplies the target at the far end of the path through `F`.
  obtain ⟨fX, hfXF, hfXX⟩ :=
    Thm186Claim1.claim1 G hG X Y P p₁ pₙ hopt hhead hlast F hmin
  obtain ⟨-, fₐ, hfₐF, hafₐ⟩ := haatt
  have hUconn : ConnectedSet G (F ∪ {P[a]'halen}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hFconn ⟨fₐ, hfₐF, hafₐ⟩
  obtain ⟨T, hTfrom, hTin⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hUconn
      (show P[a]'halen ∈ F ∪ {P[a]'halen} from Or.inr rfl)
      (show fX ∈ F ∪ {P[a]'halen} from Or.inl hfXF)
  have hTl : IsPathList G T := hTfrom.1
  have hTpos : 0 < T.length := PathBasics.path_length_pos hTl
  have hT0 : T[0]'hTpos = P[a]'halen :=
    PathBasics.getElem_zero_of_head? hTfrom.2.1 hTpos
  have hTlast : T[T.length - 1]'(by omega) = fX :=
    PathBasics.getElem_last_of_getLast? hTfrom.2.2 hTpos
  have hTaF : P[a]'halen ∉ F := fun h => hFP _ h (List.getElem_mem halen)
  have hTlen2 : 2 ≤ T.length := by
    by_contra h
    have he : (0 : ℕ) = T.length - 1 := by omega
    exact hTaF (by rw [← hT0, gidx T he hTpos (by omega), hTlast]; exact hfXF)
  have hexK : ∃ k, ∃ hk : k < T.length, 0 < k ∧ VertexComplete G (T[k]'hk) X := by
    refine ⟨T.length - 1, by omega, by omega, ?_⟩
    rw [hTlast]
    exact hfXX
  obtain ⟨hklen, hkpos, hkX⟩ := Nat.find_spec hexK
  set k : ℕ := Nat.find hexK with hkdef
  have hkmin : ∀ (i : ℕ) (hi : i < T.length), 0 < i → i < k →
      ¬ VertexComplete G (T[i]'hi) X := by
    intro i hi hi0 hik hiX
    exact Nat.find_min hexK hik ⟨hi, hi0, hiX⟩
  set Q : List V := T.take (k + 1) with hQdef
  have hQlen : Q.length = k + 1 := by rw [hQdef, List.length_take]; omega
  have hQl : IsPathList G Q := by
    rw [hQdef]
    exact PathBasics.isPathList_take hTl (by omega)
  have hQfrom : IsPathFrom G Q (P[a]'halen) (T[k]'hklen) := by
    refine ⟨hQl, ?_, ?_⟩
    · rw [hQdef, List.head?_take, if_neg (by omega)]
      exact hTfrom.2.1
    · rw [hQdef, List.getLast?_take, if_neg (by omega)]
      simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hklen, Option.some_or]
  have hQtailPath : IsPathList G Q.tail := by
    simpa only [List.drop_one] using PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
  have hQtailConn : ConnectedSet G {z : V | z ∈ Q.tail} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQtailPath
  have hQtailSub : {z : V | z ∈ Q.tail} ⊆ F := by
    intro z hz
    have hzT : z ∈ T := by
      have hzQ : z ∈ Q := List.mem_of_mem_tail hz
      rw [hQdef] at hzQ
      exact List.mem_of_mem_take hzQ
    rcases hTin z hzT with hzF | hza
    · exact hzF
    · have hza' : z = P[a]'halen := by simpa using hza
      obtain ⟨l, hQlcons⟩ := List.head?_eq_some_iff.mp hQfrom.2.1
      have hQnd := PathBasics.path_nodup hQl
      rw [hQlcons, List.nodup_cons] at hQnd
      exfalso
      apply hQnd.1
      simpa [hQlcons, hza'] using hz
  have hQlastMem : T[k]'hklen ∈ Q.tail := by
    rw [hQdef]
    have hktail : k - 1 < (T.take (k + 1)).tail.length := by simp; omega
    have he : (T.take (k + 1)).tail[k - 1]'hktail = T[k]'hklen := by
      simp only [List.getElem_tail, List.getElem_take]
      exact gidx T (by omega) (by omega) hklen
    rw [← he]
    exact List.getElem_mem hktail
  have hQ1lt : 1 < Q.length := by rw [hQlen]; omega
  have hQfirstMem : Q[1]'hQ1lt ∈ Q.tail := by
    have hzero : 0 < Q.tail.length := by simp; omega
    have he : Q.tail[0]'hzero = Q[1]'hQ1lt := by simp
    rw [← he]
    exact List.getElem_mem hzero
  have hQa1 : G.Adj (P[a]'halen) (Q[1]'hQ1lt) := by
    have hadj := PathBasics.path_adj_succ hQl (show 0 + 1 < Q.length by omega)
    have hzero : Q[0]'(by omega) = P[a]'halen :=
      PathBasics.getElem_zero_of_head? hQfrom.2.1 (by omega)
    rw [hzero] at hadj
    exact hadj
  have hAdmTail : Adm G X Y P {z : V | z ∈ Q.tail} := by
    refine ⟨?_, hQtailConn, ?_⟩
    · intro z hz
      exact hmin.1.1 z (hQtailSub hz)
    · intro z hz
      exact hFY z (hQtailSub hz)
  have hTailEq : F = {z : V | z ∈ Q.tail} := by
    apply Set.Subset.antisymm ?_ hQtailSub
    by_contra hnot
    have hproper : {z : V | z ∈ Q.tail} ⊂ F :=
      (Set.ssubset_iff_subset_ne).2 ⟨hQtailSub, fun he => hnot (by rw [he])⟩
    have hcardlt : {z : V | z ∈ Q.tail}.ncard < F.ncard :=
      Set.ncard_lt_ncard hproper (Set.toFinite F)
    obtain ⟨R, hRl, hRinf, hRatt, hRint, hRend⟩ :=
      hmin.2.2 _ hAdmTail hcardlt
    have haattTail : (P[a]'halen) ∈
        attachments G {z : V | z ∈ Q.tail} {z : V | z ∈ P} :=
      ⟨List.getElem_mem halen, Q[1]'hQ1lt, hQfirstMem, hQa1⟩
    have haR : P[a]'halen ∈ R := hRatt _ haattTail
    have hkTailX : VertexComplete G (T[k]'hklen) X := hkX
    rcases hRend ⟨T[k]'hklen, hQlastMem, hkTailX⟩ with hsingle | hlastR
    · have haeq : P[a]'halen = p₁ := by
        have : P[a]'halen ∈ ({p₁} : Set V) := by rw [← hsingle]; exact haR
        simpa using this
      rw [← hp0] at haeq
      have := (List.Nodup.getElem_inj_iff hnd).mp haeq
      omega
    · have hRsub : ∀ z ∈ R, z ∈ P := by
        obtain ⟨s, t, hst⟩ := hRinf
        intro z hz
        rw [← hst]
        simp [hz]
      obtain ⟨r, hrle, hmemR, hor⟩ :=
        SubpathIsSlice.exists_index_of_subpath hP hRl hRsub
      have hidx : ∀ (t : ℕ) (ht : t < P.length), P[t]'ht ∈ R →
          r ≤ t ∧ t < r + R.length := by
        intro t ht htR
        obtain ⟨j, hj, h1, h2, h3⟩ := (hmemR _).mp htR
        have hjt : j = t := (List.Nodup.getElem_inj_iff hnd).mp h3
        subst hjt
        exact ⟨h1, h2⟩
      obtain ⟨hra, har⟩ := hidx a halen haR
      have hpnR : P[P.length - 1]'hnlt ∈ R := by rw [hpn]; exact hlastR
      obtain ⟨hrn, hnr⟩ := hidx (P.length - 1) hnlt hpnR
      have hrend : r + R.length = P.length := by omega
      have hRq : r + R.length - 1 - r + 1 = R.length := by omega
      have hrb : r < b := lt_of_le_of_lt hra hab
      have hbn : b ≠ P.length - 1 := by
        intro he
        apply hpₙY
        rw [← hpn]
        rw [gidx P he hblen hnlt] at hbY
        exact hbY
      have hbend : b < r + R.length - 1 := by omega
      have hbintSlice : P[b]'hblen ∈
          SPGT.interior ((P.drop r).take R.length) := by
        have h := PathBasics.mem_interior_slice_iff (p := P) hP
          (i := r) (j := r + R.length - 1) (by omega) (by omega)
          (x := P[b]'hblen)
        rw [hRq] at h
        exact h.mpr ⟨b, hblen, hrb, hbend, rfl⟩
      apply hRint (P[b]'hblen)
      · rcases hor with he | he
        · rw [he]
          exact hbintSlice
        · rw [← PathBasics.mem_interior_reverse, he]
          exact hbintSlice
      · exact hbY
  have hQtailF : ∀ z, z ∈ Q.tail ↔ z ∈ F := by
    intro z
    simp only [hTailEq, Set.mem_setOf_eq]
  have hQlen3 : 3 ≤ Q.length := by
    have hcard : F.ncard ≤ Q.tail.length := by
      rw [hTailEq, ← List.coe_toFinset, Set.ncard_coe_finset]
      exact List.toFinset_card_le _
    simp only [List.length_tail] at hcard
    omega
  have hk_last : k = Q.length - 1 := by rw [hQlen]; omega
  have hQlastEq : Q[Q.length - 1]'(by omega) = T[k]'hklen := by
    have hkQ : k < Q.length := by omega
    calc
      Q[Q.length - 1]'(by omega) = Q[k]'hkQ := gidx Q hk_last.symm (by omega) hkQ
      _ = T[k]'hklen := by simpa [Q]
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ Q[i]'hi = z := by
    intro z
    rw [hTailEq]
    constructor
    · intro hz
      obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
      have hj' : j + 1 < Q.length := by
        simp only [List.length_tail] at hj
        omega
      refine ⟨j + 1, hj', by omega, ?_⟩
      rw [← hjz]
      simp
    · rintro ⟨i, hi, hi1, rfl⟩
      have hj : i - 1 < Q.tail.length := by simp; omega
      have he : Q.tail[i - 1]'hj = Q[i]'hi := by
        simp only [List.getElem_tail]
        exact gidx Q (by omega) (by omega) hi
      rw [← he]
      exact List.getElem_mem hj
  have hfkF : Q[Q.length - 1]'(by omega) ∈ F :=
    (hFmem _).mpr ⟨Q.length - 1, by omega, by omega, rfl⟩
  have hf1F : Q[1]'hQ1lt ∈ F := (hFmem _).mpr ⟨1, hQ1lt, le_rfl, rfl⟩
  have hfkX : VertexComplete G (Q[Q.length - 1]'(by omega)) X := by
    rw [hQlastEq]
    exact hkX
  have huniqueX : ∀ z ∈ F, VertexComplete G z X →
      z = Q[Q.length - 1]'(by omega) := by
    intro z hzF hzX
    obtain ⟨i, hi, hi1, rfl⟩ := (hFmem z).mp hzF
    have : ¬ i < k := by
      intro hik
      have hQiT : Q[i]'hi = T[i]'(by omega) := by simpa [Q]
      exact hkmin i (by omega) (by omega) hik (by rw [hQiT] at hzX; exact hzX)
    have hieq : i = Q.length - 1 := by rw [hQlen]; omega
    exact gidx Q hieq hi (by omega)
  have hf1fk : Q[1]'hQ1lt ≠ Q[Q.length - 1]'(by omega) :=
    PathBasics.path_ne_of_ne_index hQl hQ1lt (by omega) (by omega)
  -- The two proper connected sets used in the paper are `F \ {f_k}` and `F \ {f₁}`.
  set F₁ : Set V := {z : V | z ∈ SPGT.interior Q} with hF₁def
  set F₂ : Set V := {z : V | z ∈ Q.drop 2} with hF₂def
  have hF₁sub : F₁ ⊆ F := by
    intro z hz
    rw [hF₁def] at hz
    exact hQtailSub (List.mem_of_mem_dropLast hz)
  have hF₂sub : F₂ ⊆ F := by
    intro z hz
    rw [hF₂def] at hz
    have hzTail : z ∈ Q.tail := by
      change z ∈ Q.drop 2 at hz
      have hdrop : Q.drop 2 = Q.tail.tail := by
        cases Q with
        | nil => rfl
        | cons x l => cases l <;> rfl
      have hz' : z ∈ Q.tail.tail := by rw [← hdrop]; exact hz
      exact List.mem_of_mem_tail hz'
    exact hQtailSub hzTail
  have hF₁conn : ConnectedSet G F₁ := by
    rw [hF₁def]
    exact MinimalConnectedIsPath.connectedSet_interior hQfrom
  have hF₂path : IsPathList G (Q.drop 2) := PathBasics.isPathList_drop hQl (by omega)
  have hF₂conn : ConnectedSet G F₂ := by
    rw [hF₂def]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hF₂path
  have hfkF₂ : Q[Q.length - 1]'(by omega) ∈ F₂ := by
    rw [hF₂def]
    have hi : Q.length - 1 - 2 < (Q.drop 2).length := by simp; omega
    have hiQ : 2 + (Q.length - 1 - 2) < Q.length := by
      simp only [List.length_drop] at hi
      omega
    have he : (Q.drop 2)[Q.length - 1 - 2]'hi = Q[Q.length - 1]'(by omega) := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) hiQ (by omega)
    rw [← he]
    exact List.getElem_mem hi
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m → Q[m]'hm ∈ F₂ := by
    intro m hm hm2
    rw [hF₂def]
    have hi : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hi = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hi
  have hf1F₁ : Q[1]'hQ1lt ∈ F₁ := by
    rw [hF₁def]
    exact PathBasics.getElem_mem_interior hQl hQ1lt (by omega) (by omega)
  have hfknotF₁ : Q[Q.length - 1]'(by omega) ∉ F₁ := by
    intro hz
    rw [hF₁def] at hz
    obtain ⟨i, hi, hi1, hi2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQl hz
    have hieq : i = Q.length - 1 := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp he
    omega
  have hf1notF₂ : Q[1]'hQ1lt ∉ F₂ := by
    intro hz
    rw [hF₂def] at hz
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hz
    have hiQ : 2 + i < Q.length := by
      simp only [List.length_drop] at hi
      omega
    have heq : Q[2 + i]'hiQ = Q[1]'hQ1lt := by simpa using he
    have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp heq
    omega
  have hF₁proper : F₁ ⊂ F :=
    (Set.ssubset_iff_subset_ne).2 ⟨hF₁sub, fun he => hfknotF₁ (by rw [he]; exact hfkF)⟩
  have hF₂proper : F₂ ⊂ F :=
    (Set.ssubset_iff_subset_ne).2 ⟨hF₂sub, fun he => hf1notF₂ (by rw [he]; exact hf1F)⟩
  have hAdm₁ : Adm G X Y P F₁ :=
    ⟨fun z hz => hmin.1.1 z (hF₁sub hz), hF₁conn,
      fun z hz => hFY z (hF₁sub hz)⟩
  have hAdm₂ : Adm G X Y P F₂ :=
    ⟨fun z hz => hmin.1.1 z (hF₂sub hz), hF₂conn,
      fun z hz => hFY z (hF₂sub hz)⟩
  obtain ⟨P₁, hP₁, hP₁inf, hP₁att, hP₁int, hP₁end⟩ :=
    hmin.2.2 F₁ hAdm₁ (Set.ncard_lt_ncard hF₁proper (Set.toFinite F))
  obtain ⟨P₂, hP₂, hP₂inf, hP₂att, hP₂int, hP₂end⟩ :=
    hmin.2.2 F₂ hAdm₂ (Set.ncard_lt_ncard hF₂proper (Set.toFinite F))
  have hP₁sub : ∀ z ∈ P₁, z ∈ P := by
    obtain ⟨s, t, hst⟩ := hP₁inf
    intro z hz
    rw [← hst]
    simp [hz]
  have hP₂sub : ∀ z ∈ P₂, z ∈ P := by
    obtain ⟨s, t, hst⟩ := hP₂inf
    intro z hz
    rw [← hst]
    simp [hz]
  obtain ⟨a₁, ha₁le, hmemP₁, horP₁⟩ :=
    SubpathIsSlice.exists_index_of_subpath hP hP₁ hP₁sub
  obtain ⟨a₂, ha₂le, hmemP₂, horP₂⟩ :=
    SubpathIsSlice.exists_index_of_subpath hP hP₂ hP₂sub
  have hP₁ne : P₁ ≠ [] := PathBasics.path_ne_nil hP₁
  have hP₂ne : P₂ ≠ [] := PathBasics.path_ne_nil hP₂
  have hP₁pos : 0 < P₁.length := PathBasics.path_length_pos hP₁
  have hP₂pos : 0 < P₂.length := PathBasics.path_length_pos hP₂
  set b₁ : ℕ := a₁ + P₁.length - 1 with hb₁def
  set b₂ : ℕ := a₂ + P₂.length - 1 with hb₂def
  have ha₁lt : a₁ < P.length := by omega
  have hb₁lt : b₁ < P.length := by omega
  have ha₂lt : a₂ < P.length := by omega
  have hb₂lt : b₂ < P.length := by omega
  have hb₁span : b₁ - a₁ + 1 = P₁.length := by simp [b₁]; omega
  have hb₂span : b₂ - a₂ + 1 = P₂.length := by simp [b₂]; omega
  have hP₁range : ∀ (j : ℕ) (hj : j < P.length), P[j]'hj ∈ P₁ ↔
      a₁ ≤ j ∧ j ≤ b₁ := by
    intro j hj
    rw [hmemP₁]
    constructor
    · rintro ⟨i, hi, h1, h2, he⟩
      have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp he
      subst hij
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨j, hj, h1, by omega, rfl⟩
  have hP₂range : ∀ (j : ℕ) (hj : j < P.length), P[j]'hj ∈ P₂ ↔
      a₂ ≤ j ∧ j ≤ b₂ := by
    intro j hj
    rw [hmemP₂]
    constructor
    · rintro ⟨i, hi, h1, h2, he⟩
      have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp he
      subst hij
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨j, hj, h1, by omega, rfl⟩
  have haatt₁ : P[a]'halen ∈ attachments G F₁ {z : V | z ∈ P} :=
    ⟨List.getElem_mem halen, Q[1]'hQ1lt, hf1F₁, hQa1⟩
  have haP₁ : P[a]'halen ∈ P₁ := hP₁att _ haatt₁
  have ha₁a : a₁ ≤ a := (hP₁range a halen).mp haP₁ |>.1
  have hab₁ : a ≤ b₁ := (hP₁range a halen).mp haP₁ |>.2
  have hP₁noY : ∀ (j : ℕ) (hj : j < P.length), a₁ < j → j < b₁ →
      ¬ VertexComplete G (P[j]'hj) Y := by
    intro j hj h1 h2 hjY
    apply hP₁int (P[j]'hj) _ hjY
    rcases horP₁ with he | he
    · rw [he, ← hb₁span]
      exact (PathBasics.mem_interior_slice_iff hP (by omega) hb₁lt).mpr
        ⟨j, hj, h1, h2, rfl⟩
    · rw [← PathBasics.mem_interior_reverse, he, ← hb₁span]
      exact (PathBasics.mem_interior_slice_iff hP (by omega) hb₁lt).mpr
        ⟨j, hj, h1, h2, rfl⟩
  have hP₂noY : ∀ (j : ℕ) (hj : j < P.length), a₂ < j → j < b₂ →
      ¬ VertexComplete G (P[j]'hj) Y := by
    intro j hj h1 h2 hjY
    apply hP₂int (P[j]'hj) _ hjY
    rcases horP₂ with he | he
    · rw [he, ← hb₂span]
      exact (PathBasics.mem_interior_slice_iff hP (by omega) hb₂lt).mpr
        ⟨j, hj, h1, h2, rfl⟩
    · rw [← PathBasics.mem_interior_reverse, he, ← hb₂span]
      exact (PathBasics.mem_interior_slice_iff hP (by omega) hb₂lt).mpr
        ⟨j, hj, h1, h2, rfl⟩
  have hP₂ends : (a₂ = 0 ∧ b₂ = 0) ∨ b₂ = P.length - 1 := by
    rcases hP₂end ⟨Q[Q.length - 1]'(by omega), hfkF₂, hfkX⟩ with hs | hn
    · left
      have hsetmem : ∀ z ∈ P₂, z = p₁ := by
        intro z hz
        have : z ∈ ({p₁} : Set V) := by rw [← hs]; exact hz
        simpa using this
      have haeq : P[a₂]'ha₂lt = p₁ :=
        hsetmem _ ((hP₂range a₂ ha₂lt).mpr ⟨le_rfl, by omega⟩)
      have hbeq : P[b₂]'hb₂lt = p₁ :=
        hsetmem _ ((hP₂range b₂ hb₂lt).mpr ⟨by omega, le_rfl⟩)
      rw [← hp0] at haeq hbeq
      exact ⟨(List.Nodup.getElem_inj_iff hnd).mp haeq,
        (List.Nodup.getElem_inj_iff hnd).mp hbeq⟩
    · right
      have hpnP₂ : P[P.length - 1]'hnlt ∈ P₂ := by rw [hpn]; exact hn
      exact (hP₂range _ hnlt).mp hpnP₂ |>.2 |> fun h => by omega
  -- Tighten `P₁` to the first and last actual attachments of `F₁`.
  have hW₁ex : ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G F₁ {z : V | z ∈ P} := ⟨a, halen, haatt₁⟩
  obtain ⟨hαlt, hαatt⟩ := Nat.find_spec hW₁ex
  set α : ℕ := Nat.find hW₁ex with hαdef
  have hαmin : ∀ (j : ℕ) (hj : j < P.length), j < α →
      P[j]'hj ∉ attachments G F₁ {z : V | z ∈ P} := by
    intro j hj hjα hatt
    exact Nat.find_min hW₁ex hjα ⟨hj, hatt⟩
  obtain ⟨β, hβltP, hβQ, hβmax⟩ :=
    exists_greatest
      (Q := fun j => ∃ hj : j < P.length,
        P[j]'hj ∈ attachments G F₁ {z : V | z ∈ P})
      P.length ⟨α, hαlt, hαlt, hαatt⟩
  obtain ⟨hβlt, hβatt⟩ := hβQ
  have hαa : α ≤ a := by
    by_contra hlt
    exact hαmin a halen (by omega) haatt₁
  have haβ : a ≤ β := hβmax a halen ⟨halen, haatt₁⟩
  have hαβ : α ≤ β := le_trans hαa haβ
  have hαP₁ : P[α]'hαlt ∈ P₁ := hP₁att _ hαatt
  have hβP₁ : P[β]'hβlt ∈ P₁ := hP₁att _ hβatt
  have ha₁α : a₁ ≤ α := (hP₁range α hαlt).mp hαP₁ |>.1
  have hβb₁ : β ≤ b₁ := (hP₁range β hβlt).mp hβP₁ |>.2
  have hW₁range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G F₁ {z : V | z ∈ P} → α ≤ j ∧ j ≤ β := by
    intro j hj hatt
    constructor
    · by_contra hlt
      exact hαmin j hj (by omega) hatt
    · exact hβmax j hj ⟨hj, hatt⟩
  have hαβnoY : ∀ (j : ℕ) (hj : j < P.length), α < j → j < β →
      ¬ VertexComplete G (P[j]'hj) Y := by
    intro j hj hαj hjβ
    exact hP₁noY j hj (by omega) (by omega)
  have hβb : β ≤ b := by
    by_contra hlt
    exact hαβnoY b hblen (lt_of_le_of_lt hαa hab) (by omega) hbY
  have hQfrom' : IsPathFrom G Q (P[a]'halen) (Q[Q.length - 1]'(by omega)) := by
    rw [hQlastEq]
    exact hQfrom
  let fr : Frame G X Y P F a b halen :=
    { Q := Q
      hQl := hQl
      hQlen3 := hQlen3
      hQfrom := hQfrom'
      htailF := hQtailF
      hFmem := hFmem
      hfkX := hfkX
      huniqueX := huniqueX
      α := α
      β := β
      a₂ := a₂
      b₂ := b₂
      hαlt := hαlt
      hβlt := hβlt
      ha₂lt := ha₂lt
      hb₂lt := hb₂lt
      hαa := hαa
      haβ := haβ
      hβb := hβb
      hαatt := by simpa [F₁] using hαatt
      hβatt := by simpa [F₁] using hβatt
      hW₁range := by
        intro j hj hatt
        exact hW₁range j hj (by simpa [F₁] using hatt)
      hαβnoY := hαβnoY
      hP₂noY := hP₂noY
      hP₂ends := hP₂ends
      hW₂range := by
        intro j hj hatt
        exact (hP₂range j hj).mp (hP₂att _ (by simpa [F₂] using hatt)) }
  exact ⟨fr, trivial⟩
  /-
  -- If every attachment of `F₂` starts at or after `p_b` (in particular if `W₂` is
  -- empty), the left endpoint of the tight `P₁` is joined to `f₁`.  Replacing the tail of
  -- `P` after that endpoint by `F` then invokes optimality and clears all `Y`-complete
  -- vertices to its left.
  have hleft_of_F₂_after :
      (∀ (j : ℕ) (hj : j < P.length),
        P[j]'hj ∈ attachments G F₂ {z : V | z ∈ P} → b ≤ j) →
      G.Adj (P[α]'hαlt) (Q[1]'hQ1lt) ∧
        ∀ (j : ℕ) (hj : j < P.length), 0 < j → j ≤ α →
          ¬ VertexComplete G (P[j]'hj) Y := by
    obsolete
    /- intro hF₂after
    have hαf₁ : G.Adj (P[α]'hαlt) (Q[1]'hQ1lt) := by
      obtain ⟨-, z, hzF₁, hαz⟩ := hαatt
      obtain ⟨m, hm, hm1, hm2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQl
        (by simpa [F₁] using hzF₁)
      have hmle : m ≤ Q.length - 2 := by omega
      have hm_eq : m = 1 := by
        by_contra hne
        have hm2' : 2 ≤ m := by omega
        have hzF₂ : z ∈ F₂ := by
          rw [← he]
          exact hF₂idx m hm hm2'
        have hatt₂ : P[α]'hαlt ∈ attachments G F₂ {z : V | z ∈ P} :=
          ⟨List.getElem_mem hαlt, z, hzF₂, hαz⟩
        have := hF₂after α hαlt hatt₂
        omega
      subst hm_eq
      rw [he]
      exact hαz
    have hTailFrom : IsPathFrom G Q.tail (Q[1]'hQ1lt)
        (Q[Q.length - 1]'(by omega)) := by
      refine ⟨hQtailPath, tail_head?_getElem hQ1lt, ?_⟩
      rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
    have hLfrom : IsPathFrom G ((P.drop 0).take (α - 0 + 1))
        (P[0]'h0lt) (P[α]'hαlt) := isPathFrom_slice_le hP (Nat.zero_le α) hαlt
    have hmemL : ∀ x : V, x ∈ (P.drop 0).take (α - 0 + 1) ↔
        ∃ (i : ℕ) (hi : i < P.length), i ≤ α ∧ P[i]'hi = x := by
      intro x
      rw [PathBasics.mem_slice_iff P (Nat.zero_le α) hαlt]
      constructor
      · rintro ⟨i, hi, -, hiα, rfl⟩
        exact ⟨i, hi, hiα, rfl⟩
      · rintro ⟨i, hi, hiα, rfl⟩
        exact ⟨i, hi, Nat.zero_le i, hiα, rfl⟩
    have hmemTail : ∀ x : V, x ∈ Q.tail ↔
        ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = x := by
      intro x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hm : i + 1 < Q.length := by simp only [List.length_tail] at hi; omega
        refine ⟨i + 1, hm, by omega, ?_⟩
        simp
      · rintro ⟨m, hm, hm1, rfl⟩
        have hi : m - 1 < Q.tail.length := by simp; omega
        have he : Q.tail[m - 1]'hi = Q[m]'hm := by
          simp only [List.getElem_tail]
          exact gidx Q (by omega) (by omega) hm
        rw [← he]
        exact List.getElem_mem hi
    have hP'from0 : IsPathFrom G
        ((P.drop 0).take (α - 0 + 1) ++ Q.tail)
        (P[0]'h0lt) (Q[Q.length - 1]'(by omega)) := by
      refine PathGlue.glue_path hLfrom hTailFrom ?_ ?_
      · intro x hx hxt
        exact hFP x (hQtailSub hxt) (by
          obtain ⟨i, hi, -, rfl⟩ := (hmemL x).mp hx
          exact List.getElem_mem hi)
      · intro x hx y hy
        obtain ⟨i, hi, hiα, rfl⟩ := (hmemL x).mp hx
        obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail y).mp hy
        constructor
        · intro hadj
          have hmF : Q[m]'hm ∈ F := (hFmem _).mpr ⟨m, hm, hm1, rfl⟩
          by_cases hmlast : m = Q.length - 1
          · have hmF₂ : Q[m]'hm ∈ F₂ := by
              exact hF₂idx m hm (by omega)
            have hatt₂ : P[i]'hi ∈ attachments G F₂ {z : V | z ∈ P} :=
              ⟨List.getElem_mem hi, _, hmF₂, hadj⟩
            have := hF₂after i hi hatt₂
            omega
          · have hmInt : Q[m]'hm ∈ F₁ := by
              rw [hF₁def]
              exact PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
            have hatt₁ : P[i]'hi ∈ attachments G F₁ {z : V | z ∈ P} :=
              ⟨List.getElem_mem hi, _, hmInt, hadj⟩
            have hirange := hW₁range i hi hatt₁
            have hiαeq : i = α := by omega
            subst hiαeq
            have mmeq : m = 1 := by
              by_contra hmne
              have hmF₂ : Q[m]'hm ∈ F₂ := hF₂idx m hm (by omega)
              have hatt₂ : P[α]'hαlt ∈ attachments G F₂ {z : V | z ∈ P} :=
                ⟨List.getElem_mem hαlt, _, hmF₂, hadj⟩
              have := hF₂after α hαlt hatt₂
              omega
            subst mmeq
            exact ⟨rfl, rfl⟩
        · rintro ⟨hiαeq, hm1eq⟩
          have hiEq : i = α := (List.Nodup.getElem_inj_iff hnd).mp hiαeq
          have hmEq : m = 1 :=
            (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm1eq
          subst hiEq
          subst hmEq
          exact hαf₁
    set P' : List V := (P.drop 0).take (α - 0 + 1) ++ Q.tail with hP'def
    have hP'from : IsPathFrom G P' p₁ (Q[Q.length - 1]'(by omega)) := by
      rw [← hp0]
      exact hP'from0
    have hP'l : IsPathList G P' := hP'from.1
    have hmemP' : ∀ x : V, x ∈ P' ↔
        ((∃ (i : ℕ) (hi : i < P.length), i ≤ α ∧ P[i]'hi = x) ∨ x ∈ Q.tail) := by
      intro x
      rw [hP'def, List.mem_append, hmemL]
    have hP'Y : ∀ w ∈ P', VertexComplete G w Y → w = p₁ := by
      intro w hw hwY
      by_contra hwne
      have hwF : w ∉ F := fun h => hFY w h hwY
      obtain ⟨j, hj, hjα, rfl⟩ : ∃ (j : ℕ) (hj : j < P.length),
          j ≤ α ∧ P[j]'hj = w := by
        rcases (hmemP' w).mp hw with h | h
        · exact h
        · exact absurd (hQtailSub h) hwF
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hwne (by rw [← hp0])
      have hj1 : j ≠ 1 := by
        rintro rfl
        exact hq₂Y (by rw [← hp1]; exact hwY)
      have hP'len : P'.length = α + 1 + (Q.length - 1) := by
        rw [hP'def, List.length_append, PathBasics.length_slice P (Nat.zero_le α) hαlt]
        simp
      have hP'5 : 5 ≤ P'.length := by omega
      have hP'1lt : 1 < P'.length := by omega
      have hP'2 : P'[1]'hP'1lt = q₂ := by
        have hP'0 : P'[0]'(by omega) = p₁ :=
          PathBasics.getElem_zero_of_head? hP'from.2.1 (by omega)
        have hadj01 := PathBasics.path_adj_succ hP'l (show 0 + 1 < P'.length by omega)
        rw [hP'0] at hadj01
        have hq₂P' : q₂ ∈ P' := by
          apply (hmemP' q₂).mpr
          left
          exact ⟨1, h1lt, by omega, hp1⟩
        obtain ⟨t, ht, htq⟩ := List.getElem_of_mem hq₂P'
        have hp₁P' : p₁ ∈ P' := PathBasics.head_mem hP'from.2.1
        obtain ⟨s, hs, hsp⟩ := List.getElem_of_mem hp₁P'
        have hs0 : s = 0 := by
          have hhead0 : P'[0]'(by omega) = p₁ := hP'0
          rw [← hsp] at hhead0
          exact (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP'l)).mp hhead0.symm
        have hadj : G.Adj p₁ q₂ := by
          rw [← hp0, ← hp1]
          exact PathBasics.path_adj_succ hP (show 0 + 1 < P.length by omega)
        have htidx := (PathBasics.path_adj_iff hP'l hs ht).mp (by rw [hsp, htq]; exact hadj)
        have ht1 : t = 1 := by omega
        exact (gidx P' ht1.symm hP'1lt ht).trans htq
      have hout : ∀ v ∈ P', v ∉ X ∧ v ∉ Y := by
        intro v hv
        rcases (hmemP' v).mp hv with ⟨i, hi, -, rfl⟩ | htail
        · exact hPXY _ (List.getElem_mem hi)
        · exact ⟨fun hx => hFXY _ (hQtailSub htail) (Set.mem_union_left _ hx),
            fun hy => hFXY _ (hQtailSub htail) (Set.mem_union_right _ hy)⟩
      have hXc : ∀ v ∈ P', VertexComplete G v X ↔
          (v = p₁ ∨ v = Q[Q.length - 1]'(by omega)) := by
        intro v hv
        rcases (hmemP' v).mp hv with ⟨i, hi, hiα, rfl⟩ | htail
        · constructor
          · intro hvX
            rcases (hXuniq _ (List.getElem_mem hi)).mp hvX with h | h
            · exact Or.inl h
            · exfalso
              have hiLast : i = P.length - 1 := by
                rw [← hpn] at h
                exact (List.Nodup.getElem_inj_iff hnd).mp h
              omega
          · rintro (h | h)
            · exact (hXuniq _ (List.getElem_mem hi)).mpr (Or.inl h)
            · exfalso
              exact hFP _ hfkF (by rw [← h]; exact List.getElem_mem hi)
        · constructor
          · intro hvX
            exact Or.inr (huniqueX v (hQtailSub htail) hvX)
          · rintro (rfl | rfl)
            · exfalso
              exact hFP _ (hQtailSub htail) (PathBasics.head_mem hhead)
            · exact hfkX
      have hpw : IsPseudowheel G X Y P' :=
        PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl hP'from
          (tail_head?_getElem hP'1lt |>.trans (congrArg some hP'2)) hout hP'5 hXc hp₁Y
          ⟨P[j]'hj, hw, hwne, hwY⟩
          hq₂Y (hFY _ hfkF)
      have hsubset : {v : V | v ∈ P' ∧ VertexComplete G v Y} ⊆
          {v : V | v ∈ P ∧ VertexComplete G v Y} := by
        rintro v ⟨hv, hvY⟩
        refine ⟨?_, hvY⟩
        rcases (hmemP' v).mp hv with ⟨i, hi, -, rfl⟩ | htail
        · exact List.getElem_mem hi
        · exact absurd hvY (hFY _ (hQtailSub htail))
      have hbnot : P[b]'hblen ∉ {v : V | v ∈ P' ∧ VertexComplete G v Y} := by
        rintro ⟨hbP', -⟩
        rcases (hmemP' _).mp hbP' with ⟨i, hi, hiα, hieq⟩ | htail
        · have hib : i = b := (List.Nodup.getElem_inj_iff hnd).mp hieq
          omega
        · exact hFP _ (hQtailSub htail) (List.getElem_mem hblen)
      exact hopt.2.1 ⟨X, Y, P', hpw,
        Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset hsubset).mpr
            ⟨P[b]'hblen, ⟨List.getElem_mem hblen, hbY⟩, hbnot⟩)
          (Set.toFinite _)⟩
    refine ⟨hαf₁, ?_⟩
    intro j hj hj0 hjα hjY
    exact (by
      have hmem : P[j]'hj ∈ P' := (hmemP' _).mpr (Or.inl ⟨j, hj, hjα, rfl⟩)
      have he := hP'Y _ hmem hjY
      rw [← hp0] at he
      have := (List.Nodup.getElem_inj_iff hnd).mp he
      omega)
    -/
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  have hoddP : Odd (HoleYEdgeParity.yEdges G Y P).ncard := h184.1.1
  have hthreeP : 3 ≤ (HoleYEdgeParity.yEdges G Y P).ncard := h184.1.2
  rcases hP₂ends with hzero | hlast₂
  · obsolete
  · have hbn : b ≠ P.length - 1 := by
      intro he
      apply hpₙY
      rw [← hpn]
      rw [gidx P he hblen hnlt] at hbY
      exact hbY
    have hblast : b < P.length - 1 := by omega
    have hba₂ : b ≤ a₂ := by
      by_contra hlt
      exact hP₂noY b hblen (by omega) (by omega) hbY
    have hF₂after : ∀ (j : ℕ) (hj : j < P.length),
        P[j]'hj ∈ attachments G F₂ {z : V | z ∈ P} → b ≤ j := by
      intro j hj hatt
      have hjP₂ := hP₂att _ hatt
      have hjrange := (hP₂range j hj).mp hjP₂
      omega
    obtain ⟨hαf₁, hleftY⟩ := hleft_of_F₂_after hF₂after
    by_cases hW₂ex : ∃ j, ∃ hj : j < P.length,
        P[j]'hj ∈ attachments G F₂ {z : V | z ∈ P}
    · obsolete
      /- obtain ⟨hγlt, hγatt⟩ := Nat.find_spec hW₂ex
      set γ : ℕ := Nat.find hW₂ex with hγdef
      have hγmin : ∀ (j : ℕ) (hj : j < P.length), j < γ →
          P[j]'hj ∉ attachments G F₂ {z : V | z ∈ P} := by
        intro j hj hjγ hatt
        exact Nat.find_min hW₂ex hjγ ⟨hj, hatt⟩
      have ha₂γ : a₂ ≤ γ := by
        have hmem := hP₂att _ hγatt
        exact (hP₂range γ hγlt).mp hmem |>.1
      have hβγle : β ≤ γ := by omega
      have hβγ : β < γ := by
        rcases eq_or_lt_of_le hβγle with heq | hlt
        · exfalso
          have hYloc0 : ∀ (j : ℕ) (hj : j < P.length),
              VertexComplete G (P[j]'hj) Y → j = 0 ∨ j = β := by
            intro j hj hjY
            by_cases hj0 : j = 0
            · exact Or.inl hj0
            right
            by_cases hjβ : j < β
            · rcases le_or_gt j α with hjα | hαj
              · exact absurd hjY (hleftY j hj (by omega) hjα)
              · exact absurd hjY (hαβnoY j hj hαj hjβ)
            · by_cases hβj : β < j
              · have hjlast : j < P.length - 1 := by
                  by_contra hn
                  have hjEq : j = P.length - 1 := by omega
                  apply hpₙY
                  rw [← hpn]
                  rw [gidx P hjEq hj hnlt] at hjY
                  exact hjY
                exact absurd hjY (hP₂noY j hj (by omega) (by omega))
              · omega
          have hempty : HoleYEdgeParity.yEdges G Y P = ∅ := by
            ext e
            simp only [Set.mem_empty_iff_false, iff_false]
            rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
            have hiLoc := hYloc0 i hi huY
            have hjLoc := hYloc0 j hj hvY
            have hadjIdx := (PathBasics.path_adj_iff hP hi hj).mp huv
            rcases hiLoc with hiLoc | hiLoc
            · rcases hjLoc with hjLoc | hjLoc
              · have hij : i = j := by omega
                exact G.irrefl _ ((gidx P hij hi hj) ▸ huv)
              · omega
            · rcases hjLoc with hjLoc | hjLoc
              · omega
              · have hij : i = j := by omega
                exact G.irrefl _ ((gidx P hij hi hj) ▸ huv)
          rw [hempty, Set.ncard_empty] at hthreeP
          omega
        · exact hlt
      have hβf₁ : G.Adj (P[β]'hβlt) (Q[1]'hQ1lt) := by
        obtain ⟨-, z, hzF₁, hβz⟩ := hβatt
        obtain ⟨m, hm, hm1, hm2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQl
          (by simpa [F₁] using hzF₁)
        have hmEq : m = 1 := by
          by_contra hne
          have hmF₂ : Q[m]'hm ∈ F₂ := hF₂idx m hm (by omega)
          have hatt₂ : P[β]'hβlt ∈ attachments G F₂ {z : V | z ∈ P} :=
            ⟨List.getElem_mem hβlt, _, hmF₂, by rw [he]; exact hβz⟩
          by_contra hnot
          exact hγmin β hβlt hβγ hatt₂
        subst hmEq
        rw [he]
        exact hβz
      have hγfk : G.Adj (P[γ]'hγlt) (Q[Q.length - 1]'(by omega)) := by
        obtain ⟨-, z, hzF₂, hγz⟩ := hγatt
        obtain ⟨m, hm, hm1, he⟩ := (hFmem z).mp (hF₂sub hzF₂)
        have hm2 : 2 ≤ m := by
          by_contra hlt
          have hmEq : m = 1 := by omega
          subst hmEq
          exact hf1notF₂ (by rw [he]; exact hzF₂)
        have hmEq : m = Q.length - 1 := by
          by_contra hne
          have hmF₁ : Q[m]'hm ∈ F₁ := by
            rw [hF₁def]
            exact PathBasics.getElem_mem_interior hQl hm (by omega) (by omega)
          have hatt₁ : P[γ]'hγlt ∈ attachments G F₁ {z : V | z ∈ P} :=
            ⟨List.getElem_mem hγlt, _, hmF₁, by rw [he]; exact hγz⟩
          have := hW₁range γ hγlt hatt₁
          omega
        have he' : z = Q[Q.length - 1]'(by omega) := by
          rw [← he]
          exact gidx Q hmEq hm (by omega)
        rw [he'] at hγz
        exact hγz
      have hTailFrom : IsPathFrom G Q.tail (Q[1]'hQ1lt)
          (Q[Q.length - 1]'(by omega)) := by
        refine ⟨hQtailPath, tail_head?_getElem hQ1lt, ?_⟩
        rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
      set S : List V := (P.drop β).take (γ - β + 1) with hSdef
      have hSfrom : IsPathFrom G S (P[β]'hβlt) (P[γ]'hγlt) := by
        rw [hSdef]
        exact PathBasics.isPathFrom_slice hP hβγ hγlt
      have hSrev : IsPathFrom G S.reverse (P[γ]'hγlt) (P[β]'hβlt) :=
        PathBasics.isPathFrom_reverse hSfrom
      have hmemS : ∀ x : V, x ∈ S.reverse ↔
          ∃ (j : ℕ) (hj : j < P.length), β ≤ j ∧ j ≤ γ ∧ P[j]'hj = x := by
        intro x
        rw [List.mem_reverse, hSdef, PathBasics.mem_slice_iff P (le_of_lt hβγ) hγlt]
      have hmemTail : ∀ x : V, x ∈ Q.tail ↔
          ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = x := by
        intro x
        constructor
        · intro hx
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          have hm : i + 1 < Q.length := by simp only [List.length_tail] at hi; omega
          exact ⟨i + 1, hm, by omega, by simp⟩
        · rintro ⟨m, hm, hm1, rfl⟩
          have hi : m - 1 < Q.tail.length := by simp; omega
          have he : Q.tail[m - 1]'hi = Q[m]'hm := by
            simp only [List.getElem_tail]
            exact gidx Q (by omega) (by omega) hm
          rw [← he]
          exact List.getElem_mem hi
      have hHole : IsHoleList G (Q.tail ++ S.reverse) := by
        refine PathGlue.glue_hole hTailFrom hSrev ?_ ?_ ?_
        · intro x hx hxs
          obtain ⟨j, hj, -, -, rfl⟩ := (hmemS x).mp hxs
          exact hFP _ (hQtailSub hx) (List.getElem_mem hj)
        · intro x hx y hy
          obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail x).mp hx
          obtain ⟨j, hj, hβj, hjγ, rfl⟩ := (hmemS y).mp hy
          constructor
          · intro hadj
            rcases eq_or_lt_of_le hm1 with hmone | hmgt
            · subst hmone
              have hatt : P[j]'hj ∈ attachments G F₁ {z : V | z ∈ P} :=
                ⟨List.getElem_mem hj, _, hf1F₁, hadj.symm⟩
              have hjle := (hW₁range j hj hatt).2
              have hjeq : j = β := by omega
              subst hjeq
              exact Or.inr ⟨rfl, rfl⟩
            · by_cases hmlast : m = Q.length - 1
              · subst hmlast
                have hatt : P[j]'hj ∈ attachments G F₂ {z : V | z ∈ P} :=
                  ⟨List.getElem_mem hj, _, hfkF₂, hadj.symm⟩
                have hjge : γ ≤ j := by
                  by_contra hlt
                  exact hγmin j hj (by omega) hatt
                have hjeq : j = γ := by omega
                subst hjeq
                exact Or.inl ⟨rfl, rfl⟩
              · have hmF₁ : Q[m]'hm ∈ F₁ := by
                  rw [hF₁def]
                  exact PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
                have hatt₁ : P[j]'hj ∈ attachments G F₁ {z : V | z ∈ P} :=
                  ⟨List.getElem_mem hj, _, hmF₁, hadj.symm⟩
                have hjle := (hW₁range j hj hatt₁).2
                omega
          · rintro (⟨hm, hj⟩ | ⟨hm, hj⟩)
            · have hmEq : m = Q.length - 1 :=
                (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm
              have hjEq : j = γ := (List.Nodup.getElem_inj_iff hnd).mp hj
              subst hmEq
              subst hjEq
              exact hγfk.symm
            · have hmEq : m = 1 :=
                (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm
              have hjEq : j = β := (List.Nodup.getElem_inj_iff hnd).mp hj
              subst hmEq
              subst hjEq
              exact hβf₁.symm
        · rw [hSdef, List.length_reverse, PathBasics.length_slice P (le_of_lt hβγ) hγlt]
          simp
          omega
      have hYloc : ∀ (j : ℕ) (hj : j < P.length),
          VertexComplete G (P[j]'hj) Y → j = 0 ∨ (β ≤ j ∧ j ≤ γ) := by
        intro j hj hjY
        by_cases hj0 : j = 0
        · exact Or.inl hj0
        right
        constructor
        · by_contra hlt
          rcases le_or_gt j α with hjα | hαj
          · exact absurd hjY (hleftY j hj (by omega) hjα)
          · exact absurd hjY (hαβnoY j hj hαj (by omega))
        · by_contra hlt
          have hjlast : j < P.length - 1 := by
            by_contra hn
            have hjEq : j = P.length - 1 := by omega
            apply hpₙY
            rw [← hpn]
            rw [gidx P hjEq hj hnlt] at hjY
            exact hjY
          exact hP₂noY j hj (by omega) (by omega) hjY
      have hHY : ∀ w ∈ Q.tail ++ S.reverse, w ∉ Y := by
        intro w hw
        rw [List.mem_append] at hw
        rcases hw with hw | hw
        · exact fun h => hFXY _ (hQtailSub hw) (Set.mem_union_right _ h)
        · obtain ⟨j, hj, -, -, rfl⟩ := (hmemS w).mp hw
          exact hPY _ (List.getElem_mem hj)
      have hyeq : HoleYEdgeParity.yEdges G Y (Q.tail ++ S.reverse) =
          HoleYEdgeParity.yEdges G Y P := by
        have hto : ∀ w ∈ Q.tail ++ S.reverse, VertexComplete G w Y → w ∈ P := by
          intro w hw hwY
          rw [List.mem_append] at hw
          rcases hw with hw | hw
          · exact absurd hwY (hFY _ (hQtailSub hw))
          · obtain ⟨j, hj, -, -, rfl⟩ := (hmemS w).mp hw
            exact List.getElem_mem hj
        have hfrom : ∀ (i : ℕ) (hi : i < P.length), VertexComplete G (P[i]'hi) Y →
            ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[i]'hi) (P[j]'hj) →
              VertexComplete G (P[j]'hj) Y → P[i]'hi ∈ Q.tail ++ S.reverse := by
          intro i hi hiY j hj hij hjY
          rcases hYloc i hi hiY with hi0 | hir
          · subst hi0
            have hidx := (PathBasics.path_adj_iff hP hi hj).mp hij
            have hj1 : j = 1 := by omega
            subst hj1
            exact absurd hjY (by rw [hp1]; exact hq₂Y)
          · rw [List.mem_append]
            exact Or.inr ((hmemS _).mpr ⟨i, hi, hir.1, hir.2, rfl⟩)
        ext e
        constructor
        · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
          exact ⟨u, hto u hu huY, v, hto v hv hvY, rfl, huv, huY, hvY⟩
        · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
          exact ⟨_, hfrom i hi huY j hj huv hvY, _, hfrom j hj hvY i hi huv.symm huY,
            rfl, huv, huY, hvY⟩
      exact HoleYEdgeParity.not_odd_ge_three_yEdges' hBerge hYanti hHole hHY
        (by rw [hyeq]; exact hoddP) (by rw [hyeq]; exact hthreeP)
      -/
    · obsolete
  -/

/-- The single-edge exceptional case in the printed parity argument.  The hole through
`p₀,F,p_α` has the `X`-complete edge `p₀f_k`; 2.10 gives either a clean cap, which
together with the triangle at `p_αp_βf₁` makes a long prism, or a leap, which closes
through the other `X`-complete end `p_n` to make an odd hole. -/
private theorem zero_exception_contra (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b) (hbY : VertexComplete G (P[b]'hblen) Y)
    (fr : Frame G X Y P F a b halen)
    (hzero : fr.a₂ = 0 ∧ fr.b₂ = 0)
    (hW₂ex : ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P})
    (hαY : VertexComplete G (P[fr.α]'fr.hαlt) Y)
    (hβY : VertexComplete G (P[fr.β]'fr.hβlt) Y)
    (hstep : fr.β = fr.α + 1) : False := by
  classical
  let Q : List V := fr.Q
  let α : ℕ := fr.α
  let β : ℕ := fr.β
  have hQl : IsPathList G Q := fr.hQl
  have hQlen3 : 3 ≤ Q.length := fr.hQlen3
  have hαlt : α < P.length := fr.hαlt
  have hβlt : β < P.length := fr.hβlt
  have hαa : α ≤ a := fr.hαa
  have hβb : β ≤ b := fr.hβb
  have hstep' : β = α + 1 := by simpa [α, β] using hstep
  have hαY' : VertexComplete G (P[α]'hαlt) Y := by simpa [α] using hαY
  have hβY' : VertexComplete G (P[β]'hβlt) Y := by simpa [β] using hβY
  have hW₁range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
        α ≤ j ∧ j ≤ β := by
    simpa [Q, α, β] using fr.hW₁range
  have hW₂range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} →
        j = 0 := by
    intro j hj hatt
    have hr := fr.hW₂range j hj (by simpa [Q] using hatt)
    omega
  have htailF : ∀ z : V, z ∈ Q.tail ↔ z ∈ F := by simpa [Q] using fr.htailF
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = z := by
    simpa [Q] using fr.hFmem
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hPnd : P.Nodup := PathBasics.path_nodup hP
  have hQnd : Q.Nodup := PathBasics.path_nodup hQl
  have hBerge : Berge G := hG.1.1.1.1
  have h0lt : 0 < P.length := by omega
  have h1lt : 1 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hq₁ : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
  have hqₙ : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have hp0X : VertexComplete G (P[0]'h0lt) X := by
    rw [hp0, ← hq₁]
    exact (hXuniq0 q₁ (PathBasics.head_mem hPfrom.2.1)).mpr (Or.inl rfl)
  have hpnX : VertexComplete G (P[P.length - 1]'hnlt) X := by
    rw [hpn, ← hqₙ]
    exact (hXuniq0 qₙ (PathBasics.getLast_mem hPfrom.2.2)).mpr (Or.inr rfl)
  have hXuniq : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
    intro v hv
    rw [← hq₁, ← hqₙ]
    exact hXuniq0 v hv
  have hFP : ∀ z ∈ F, z ∉ P := fun z hz => (hmin.1.1 z hz).2
  have hFXY : ∀ z ∈ F, z ∉ X ∪ Y := fun z hz => (hmin.1.1 z hz).1
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m → Q[m]'hm ∈ Q.drop 2 := by
    intro m hm hm2
    have hi : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hi = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hi
  have hαtwo : 2 ≤ α := by
    have hα0 : α ≠ 0 := by
      intro he
      have hβ1 : β = 1 := by omega
      apply hq₂Y
      rw [← hp1]
      rw [gidx P hβ1 hβlt h1lt] at hβY'
      exact hβY'
    have hα1 : α ≠ 1 := by
      intro he
      apply hq₂Y
      rw [← hp1]
      rw [gidx P he hαlt h1lt] at hαY'
      exact hαY'
    omega
  have hblast : b < P.length - 1 := by
    have hpₙY : ¬ VertexComplete G pₙ Y := by rw [← hqₙ]; exact hqₙY
    by_contra hb
    have he : b = P.length - 1 := by omega
    apply hpₙY
    rw [← hpn]
    rw [gidx P he hblen hnlt] at hbY
    exact hbY
  have hf1Int : Q[1]'(by omega) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQl (by omega) (by omega) (by omega)
  have hAttF1 : ∀ (j : ℕ) (hj : j < P.length), 0 < j →
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
      G.Adj (P[j]'hj) (Q[1]'(by omega)) := by
    intro j hj hj0 hatt
    obtain ⟨-, z, hz, hjz⟩ := hatt
    obtain ⟨m, hm, hm1, hm2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQl hz
    have hmEq : m = 1 := by
      by_contra hne
      have hatt₂ : P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hj, Q[m]'hm, hF₂idx m hm (by omega), by rw [he]; exact hjz⟩
      have := hW₂range j hj hatt₂
      omega
    have he' : Q[1]'(by omega) = z := (gidx Q hmEq.symm (by omega) hm).trans he
    rw [he']
    exact hjz
  have hαf1 : G.Adj (P[α]'hαlt) (Q[1]'(by omega)) :=
    hAttF1 α hαlt (by omega) (by simpa [Q, α] using fr.hαatt)
  have hβf1 : G.Adj (P[β]'hβlt) (Q[1]'(by omega)) :=
    hAttF1 β hβlt (by omega) (by simpa [Q, β] using fr.hβatt)
  have hp0fk : G.Adj (P[0]'h0lt) (Q[Q.length - 1]'(by omega)) := by
    obtain ⟨j, hj, hatt⟩ := hW₂ex
    have hj0 : j = 0 := hW₂range j hj (by simpa [Q] using hatt)
    obtain ⟨-, z, hz, hjz⟩ := hatt
    have hzQ : z ∈ Q.drop 2 := by simpa [Q] using hz
    obtain ⟨r, hr, hre⟩ := List.getElem_of_mem hzQ
    have hm : 2 + r < Q.length := by simp only [List.length_drop] at hr; omega
    have hzEq : Q[2 + r]'hm = z := by simpa using hre
    have hmLast : 2 + r = Q.length - 1 := by
      by_contra hne
      have hInt : Q[2 + r]'hm ∈ SPGT.interior Q :=
        PathBasics.getElem_mem_interior hQl hm (by omega) (by omega)
      have hatt₁ : P[j]'hj ∈
          attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hj, Q[2 + r]'hm, hInt, by rw [hzEq]; exact hjz⟩
      have hrange := hW₁range j hj hatt₁
      omega
    have hpj : P[j]'hj = P[0]'h0lt := gidx P hj0 hj h0lt
    have hqz : Q[Q.length - 1]'(by omega) = z :=
      (gidx Q hmLast.symm (by omega) hm).trans hzEq
    rw [← hpj, hqz]
    exact hjz
  have hPrefix : IsPathFrom G (P.take (α + 1)) (P[0]'h0lt) (P[α]'hαlt) := by
    simpa using PathBasics.isPathFrom_slice hP (show 0 < α by omega) hαlt
  have hTail : IsPathFrom G Q.tail (Q[1]'(by omega)) (Q[Q.length - 1]'(by omega)) := by
    have ht : IsPathList G Q.tail := by
      simpa only [List.drop_one] using PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
    refine ⟨ht, tail_head?_getElem (by omega), ?_⟩
    rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
  have hmemPrefix : ∀ z : V, z ∈ P.take (α + 1) ↔
      ∃ (j : ℕ) (hj : j < P.length), j ≤ α ∧ P[j]'hj = z := by
    intro z
    have h := PathBasics.mem_slice_iff P (i := 0) (j := α) (Nat.zero_le α) hαlt (x := z)
    simpa using h
  have hmemTail : ∀ z : V, z ∈ Q.tail ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = z := by
    intro z
    rw [htailF, hFmem]
  let C : List V := P.take (α + 1) ++ Q.tail
  have hC : IsHoleList G C := by
    dsimp [C]
    refine PathGlue.glue_hole hPrefix hTail ?_ ?_ (by simp; omega)
    · intro z hzP hzQ
      obtain ⟨j, hj, -, rfl⟩ := (hmemPrefix z).mp hzP
      exact hFP _ ((htailF _).mp hzQ) (List.getElem_mem hj)
    · intro z hzP w hzQ
      obtain ⟨j, hj, hjα, rfl⟩ := (hmemPrefix z).mp hzP
      obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail w).mp hzQ
      constructor
      · intro hadj
        rcases eq_or_lt_of_le hm1 with rfl | hm2
        · have hatt₁ : P[j]'hj ∈
              attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hj, Q[1]'hm, hf1Int, hadj⟩
          have hjEq : j = α := by have := hW₁range j hj hatt₁; omega
          exact Or.inl ⟨gidx P hjEq hj hαlt, rfl⟩
        · have hatt₂ : P[j]'hj ∈
              attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hj, Q[m]'hm, hF₂idx m hm hm2, hadj⟩
          have hjEq : j = 0 := hW₂range j hj hatt₂
          have hmEq : m = Q.length - 1 := by
            by_contra hne
            have hInt : Q[m]'hm ∈ SPGT.interior Q :=
              PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
            have hatt₁ : P[j]'hj ∈
                attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hj, Q[m]'hm, hInt, hadj⟩
            have := hW₁range j hj hatt₁
            omega
          exact Or.inr ⟨gidx P hjEq hj h0lt, gidx Q hmEq hm (by omega)⟩
      · rintro (⟨hjEq, hmEq⟩ | ⟨hjEq, hmEq⟩)
        · have hj' : j = α := hPnd.getElem_inj_iff.mp hjEq
          have hm' : m = 1 := hQnd.getElem_inj_iff.mp hmEq
          subst j; subst m
          exact hαf1
        · have hj' : j = 0 := hPnd.getElem_inj_iff.mp hjEq
          have hm' : m = Q.length - 1 := hQnd.getElem_inj_iff.mp hmEq
          subst j; subst m
          exact hp0fk
  have hClen : C.length = α + 1 + (Q.length - 1) := by simp [C]; omega
  have hC5 : 5 ≤ C.length := by omega
  have hC6 : 6 ≤ C.length := by
    have heven : Even (holeLength C) := hBerge.1 C hC
    obtain ⟨r, hr⟩ := heven
    simp only [holeLength] at hr
    omega
  have hmemC : ∀ z : V, z ∈ C ↔
      ((∃ (j : ℕ) (hj : j < P.length), j ≤ α ∧ P[j]'hj = z) ∨ z ∈ Q.tail) := by
    intro z
    simp only [C, List.mem_append, hmemPrefix]
  have hCX : ∀ z ∈ C, z ∉ X := by
    intro z hzC hzX
    rcases (hmemC z).mp hzC with ⟨j, hj, -, rfl⟩ | hzQ
    · exact (hPXY _ (List.getElem_mem hj)).1 hzX
    · exact hFXY z ((htailF z).mp hzQ) (Set.mem_union_left _ hzX)
  have hp0C : P[0]'h0lt ∈ C := (hmemC _).mpr (Or.inl ⟨0, h0lt, by omega, rfl⟩)
  have hfkC : Q[Q.length - 1]'(by omega) ∈ C := (hmemC _).mpr (Or.inr (by
    apply (hmemTail _).mpr
    exact ⟨Q.length - 1, by omega, by omega, rfl⟩))
  have hOnlyX : ∀ z ∈ C, VertexComplete G z X →
      z = P[0]'h0lt ∨ z = Q[Q.length - 1]'(by omega) := by
    intro z hzC hzX
    rcases (hmemC z).mp hzC with ⟨j, hj, hjα, rfl⟩ | hzQ
    · rcases (hXuniq _ (List.getElem_mem hj)).mp hzX with he | he
      · left
        rw [hp0] at ⊢
        exact he
      · exfalso
        rw [← hpn] at he
        have hjlast := hPnd.getElem_inj_iff.mp he
        omega
    · right
      exact fr.huniqueX z ((htailF z).mp hzQ) hzX
  have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge X hXanti C hC hCX
    (by simpa only [holeLength] using hC5) (P[0]'h0lt) (Q[Q.length - 1]'(by omega))
    hp0C hfkC hp0fk hp0X (by simpa [Q] using fr.hfkX) hOnlyX
  rcases h210 with hhat | hleap
  · obtain ⟨hh, hhX, hhat⟩ := hhat
    have hmemDrop : ∀ z : V, z ∈ P.drop β ↔
        ∃ (j : ℕ) (hj : j < P.length), β ≤ j ∧ P[j]'hj = z := by
      intro z
      constructor
      · intro hz
        obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hz
        have hj : β + r < P.length := by simp only [List.length_drop] at hr; omega
        exact ⟨β + r, hj, by omega, by simp⟩
      · rintro ⟨j, hj, hβj, rfl⟩
        have hr : j - β < (P.drop β).length := by simp; omega
        have he : (P.drop β)[j - β]'hr = P[j]'hj := by
          simp only [List.getElem_drop]
          exact gidx P (by omega) (by omega) hj
        rw [← he]
        exact List.getElem_mem hr
    have hβdrop : P[β]'hβlt ∈ P.drop β :=
      (hmemDrop _).mpr ⟨β, hβlt, le_rfl, rfl⟩
    have hpndrop : P[P.length - 1]'hnlt ∈ P.drop β :=
      (hmemDrop _).mpr ⟨P.length - 1, hnlt, by omega, rfl⟩
    have hdropPath : IsPathList G (P.drop β) := PathBasics.isPathList_drop hP hβlt
    have hdropConn : ConnectedSet G {z : V | z ∈ P.drop β} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hdropPath
    have hUconn : ConnectedSet G ({z : V | z ∈ P.drop β} ∪ {hh}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hdropConn
        ⟨P[P.length - 1]'hnlt, hpndrop, (hpnX hh hhX).symm⟩
    obtain ⟨S, hS, hSin⟩ :=
      InducedPathExtraction.exists_isPathFrom_of_connected hUconn
        (show hh ∈ {z : V | z ∈ P.drop β} ∪ {hh} from Or.inr rfl)
        (show P[β]'hβlt ∈ {z : V | z ∈ P.drop β} ∪ {hh} from Or.inl hβdrop)
    have hhpβ : hh ≠ P[β]'hβlt := by
      intro he
      exact (hPXY _ (List.getElem_mem hβlt)).1 (he ▸ hhX)
    have hSC : ∀ z ∈ S, z ∉ C := by
      intro z hzS hzC
      rcases hSin z hzS with hzDrop | hzH
      · obtain ⟨j, hj, hβj, rfl⟩ := (hmemDrop z).mp hzDrop
        rcases (hmemC _).mp hzC with ⟨i, hi, hiα, he⟩ | hzQ
        · have hij : i = j := hPnd.getElem_inj_iff.mp he
          omega
        · exact hFP _ ((htailF _).mp hzQ) (List.getElem_mem hj)
      · have hzEq : z = hh := by simpa using hzH
        subst z
        exact hCX hh hzC hhX
    have hcross : ∀ z ∈ S, ∀ w ∈ C, G.Adj z w ↔
        ((z = hh ∧ (w = P[0]'h0lt ∨ w = Q[Q.length - 1]'(by omega))) ∨
          (z = P[β]'hβlt ∧ (w = P[α]'hαlt ∨ w = Q[1]'(by omega)))) := by
      intro z hzS w hwC
      rcases hSin z hzS with hzDrop | hzH
      · obtain ⟨j, hj, hβj, rfl⟩ := (hmemDrop z).mp hzDrop
        have hjNotH : P[j]'hj ≠ hh := by
          intro he
          exact (hPXY _ (List.getElem_mem hj)).1 (he ▸ hhX)
        constructor
        · intro hadj
          right
          rcases (hmemC w).mp hwC with ⟨i, hi, hiα, rfl⟩ | hwQ
          · have hidx := (PathBasics.path_adj_iff hP hj hi).mp hadj
            have hjEq : j = β := by omega
            have hiEq : i = α := by omega
            exact ⟨gidx P hjEq hj hβlt, Or.inl (gidx P hiEq hi hαlt)⟩
          · obtain ⟨m, hm, hm1, he⟩ := (hmemTail w).mp hwQ
            have hmEq : m = 1 := by
              by_contra hmne
              have hatt₂ : P[j]'hj ∈
                  attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
                ⟨List.getElem_mem hj, Q[m]'hm, hF₂idx m hm (by omega),
                  by rw [he]; exact hadj⟩
              have := hW₂range j hj hatt₂
              omega
            have hatt₁ : P[j]'hj ∈
                attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hj, Q[m]'hm,
                PathBasics.getElem_mem_interior hQl hm (by omega) (by omega),
                by rw [he]; exact hadj⟩
            have hjEq : j = β := by have := hW₁range j hj hatt₁; omega
            exact ⟨gidx P hjEq hj hβlt,
              Or.inr (he.symm.trans (gidx Q hmEq hm (by omega)))⟩
        · rintro (⟨hzH, -⟩ | ⟨hzβ, hw⟩)
          · exact absurd hzH hjNotH
          · have hjEq : j = β := hPnd.getElem_inj_iff.mp hzβ
            subst j
            rcases hw with hwα | hwf1
            · rw [hwα]
              exact (PathBasics.path_adj_iff hP hβlt hαlt).mpr (Or.inr (by omega))
            · rw [hwf1]
              exact hβf1
      · have hzEq : z = hh := by simpa using hzH
        subst z
        have hhatOnly := hhat.2.2.2.2.2.2
        constructor
        · intro hhw
          left
          refine ⟨rfl, ?_⟩
          by_cases hw0 : w = P[0]'h0lt
          · exact Or.inl hw0
          by_cases hwfk : w = Q[Q.length - 1]'(by omega)
          · exact Or.inr hwfk
          exact (hhatOnly w hwC hw0 hwfk hhw).elim
        · rintro (⟨-, hw⟩ | ⟨hhEq, -⟩)
          · rcases hw with rfl | rfl
            · exact hhat.2.2.2.2.1
            · exact hhat.2.2.2.2.2.1
          · exact absurd hhEq hhpβ
    have hαC : P[α]'hαlt ∈ C :=
      (hmemC _).mpr (Or.inl ⟨α, hαlt, le_rfl, rfl⟩)
    have hf1C : Q[1]'(by omega) ∈ C := (hmemC _).mpr (Or.inr (by
      apply (hmemTail _).mpr
      exact ⟨1, by omega, by omega, rfl⟩))
    have hp0neα : P[0]'h0lt ≠ P[α]'hαlt :=
      fun he => (by have := hPnd.getElem_inj_iff.mp he; omega)
    have hp0nef1 : P[0]'h0lt ≠ Q[1]'(by omega) := fun he =>
      hFP _ ((htailF _).mp ((hmemTail _).mpr ⟨1, by omega, by omega, rfl⟩))
        (by rw [← he]; exact List.getElem_mem h0lt)
    have hfkneα : Q[Q.length - 1]'(by omega) ≠ P[α]'hαlt := fun he =>
      hFP _ ((htailF _).mp ((hmemTail _).mpr
        ⟨Q.length - 1, by omega, by omega, rfl⟩))
        (by rw [he]; exact List.getElem_mem hαlt)
    have hfknef1 : Q[Q.length - 1]'(by omega) ≠ Q[1]'(by omega) := fun he => by
      have := hQnd.getElem_inj_iff.mp he
      omega
    exact two_caps_contra hG hC hC6 hp0C hfkC hp0fk hαC hf1C hαf1
      hp0neα hp0nef1 hfkneα hfknef1 hS hhpβ hSC hcross
  · obtain ⟨aa, haaX, bb, hbbX, hleap | hleap⟩ := hleap
    all_goals
      have hpnC : P[P.length - 1]'hnlt ∉ C := by
        intro hzC
        rcases (hmemC _).mp hzC with ⟨j, hj, hjα, he⟩ | hzQ
        · have hjlast : j = P.length - 1 := hPnd.getElem_inj_iff.mp he
          omega
        · exact hFP _ ((htailF _).mp hzQ) (List.getElem_mem hnlt)
      have hpnAnti : ∀ z ∈ C, ¬ G.Adj (P[P.length - 1]'hnlt) z := by
        intro z hzC hadj
        rcases (hmemC z).mp hzC with ⟨j, hj, hjα, rfl⟩ | hzQ
        · have hidx := (PathBasics.path_adj_iff hP hnlt hj).mp hadj
          omega
        · obtain ⟨m, hm, hm1, he⟩ := (hFmem z).mp ((htailF z).mp hzQ)
          by_cases hmOne : m = 1
          · have hatt₁ : P[P.length - 1]'hnlt ∈
                attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hnlt, Q[m]'hm,
                PathBasics.getElem_mem_interior hQl hm (by omega) (by omega),
                by rw [he]; exact hadj⟩
            have hr := hW₁range (P.length - 1) hnlt hatt₁
            omega
          · have hatt₂ : P[P.length - 1]'hnlt ∈
                attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hnlt, Q[m]'hm, hF₂idx m hm (by omega), by rw [he]; exact hadj⟩
            have := hW₂range (P.length - 1) hnlt hatt₂
            omega
      exact leap_common_neighbor_contra hBerge hC hleap hpnC
        (hpnX aa haaX) (hpnX bb hbbX) hpnAnti

/-- The optimality step common to both cases of claim (2): if all attachments of
`F \ {f₁}` occur at or after the assumed `Y`-complete vertex, then the tight left endpoint is
joined to `f₁`, and no noninitial vertex before that endpoint is `Y`-complete. -/
private theorem left_clear (G : SimpleGraph V) (X Y : Set V) (P : List V) (p₁ pₙ : V)
    (hopt : OptimalPseudowheel G X Y P) (hhead : P.head? = some p₁)
    (hlast : P.getLast? = some pₙ) (F : Set V)
    (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b) (hbY : VertexComplete G (P[b]'hblen) Y)
    (fr : Frame G X Y P F a b halen)
    (hF₂after : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P} → b ≤ j) :
    G.Adj (P[fr.α]'fr.hαlt) (fr.Q[1]'(by have := fr.hQlen3; omega)) ∧
      ∀ (j : ℕ) (hj : j < P.length), 0 < j → j ≤ fr.α →
        ¬ VertexComplete G (P[j]'hj) Y := by
  classical
  revert hF₂after
  rcases fr with ⟨Q, hQl, hQlen3, hQfrom, htailF, hFmem, hfkX, huniqueX,
    α, β, a₂, b₂, hαlt, hβlt, ha₂lt, hb₂lt, hαa, haβ, hβb,
    hαatt, hβatt, hW₁range, hαβnoY, hP₂noY, hP₂ends, hW₂range⟩
  intro hAfter
  have hAfter' : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} → b ≤ j := by
    simpa using hAfter
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hq₁ : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
  have hqn : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have h0lt : 0 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have h1lt : 1 < P.length := by omega
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hXuniq : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
    intro v hv
    rw [← hq₁, ← hqn]
    exact hXuniq0 v hv
  have hp₁Y : VertexComplete G p₁ Y := by rw [← hq₁]; exact hq₁Y
  have hFP : ∀ z ∈ F, z ∉ P := fun z hz => (hmin.1.1 z hz).2
  have hFXY : ∀ z ∈ F, z ∉ X ∪ Y := fun z hz => (hmin.1.1 z hz).1
  have hFY : ∀ z ∈ F, ¬ VertexComplete G z Y := hmin.1.2.2
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m → Q[m]'hm ∈
      {z : V | z ∈ Q.drop 2} := by
    intro m hm hm2
    have hi : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hi = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hi
  have hf1F : Q[1]'(by omega) ∈ F :=
    (hFmem _).mpr ⟨1, by omega, le_rfl, rfl⟩
  have hfkF : Q[Q.length - 1]'(by omega) ∈ F :=
    (hFmem _).mpr ⟨Q.length - 1, by omega, by omega, rfl⟩
  have hf1F₁ : Q[1]'(by omega) ∈ {z : V | z ∈ SPGT.interior Q} :=
    PathBasics.getElem_mem_interior hQl (by omega) (by omega) (by omega)
  have hαf1 : G.Adj (P[α]'hαlt) (Q[1]'(by omega)) := by
    obtain ⟨-, z, hzF₁, hαz⟩ := hαatt
    obtain ⟨m, hm, hm1, hm2, he⟩ :=
      PathBasics.exists_getElem_of_mem_interior hQl hzF₁
    have hmEq : m = 1 := by
      by_contra hne
      have hmF₂ := hF₂idx m hm (by omega)
      have hatt₂ : P[α]'hαlt ∈
          attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hαlt, Q[m]'hm, hmF₂, by rw [he]; exact hαz⟩
      have := hAfter' α hαlt hatt₂
      omega
    have he' : Q[1]'(by omega) = z := by
      exact (gidx Q hmEq.symm (by omega) hm).trans he
    rw [he']
    exact hαz
  have hTailFrom : IsPathFrom G Q.tail (Q[1]'(by omega))
      (Q[Q.length - 1]'(by omega)) := by
    have htailPath : IsPathList G Q.tail := by
      simpa only [List.drop_one] using PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
    refine ⟨htailPath, tail_head?_getElem (by omega), ?_⟩
    rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
  have hLfrom : IsPathFrom G ((P.drop 0).take (α - 0 + 1))
      (P[0]'h0lt) (P[α]'hαlt) := isPathFrom_slice_le hP (Nat.zero_le α) hαlt
  have hmemL : ∀ x : V, x ∈ (P.drop 0).take (α - 0 + 1) ↔
      ∃ (i : ℕ) (hi : i < P.length), i ≤ α ∧ P[i]'hi = x := by
    intro x
    rw [PathBasics.mem_slice_iff P (Nat.zero_le α) hαlt]
    constructor
    · rintro ⟨i, hi, -, hiα, rfl⟩
      exact ⟨i, hi, hiα, rfl⟩
    · rintro ⟨i, hi, hiα, rfl⟩
      exact ⟨i, hi, Nat.zero_le i, hiα, rfl⟩
  have hmemTail : ∀ x : V, x ∈ Q.tail ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hm : i + 1 < Q.length := by simp only [List.length_tail] at hi; omega
      exact ⟨i + 1, hm, by omega, by simp⟩
    · rintro ⟨m, hm, hm1, rfl⟩
      have hi : m - 1 < Q.tail.length := by simp; omega
      have he : Q.tail[m - 1]'hi = Q[m]'hm := by
        simp only [List.getElem_tail]
        exact gidx Q (by omega) (by omega) hm
      rw [← he]
      exact List.getElem_mem hi
  have hP'from0 : IsPathFrom G ((P.drop 0).take (α - 0 + 1) ++ Q.tail)
      (P[0]'h0lt) (Q[Q.length - 1]'(by omega)) := by
    refine PathGlue.glue_path hLfrom hTailFrom ?_ ?_
    · intro x hx hxt
      obtain ⟨i, hi, -, rfl⟩ := (hmemL x).mp hx
      exact hFP _ ((htailF _).mp hxt) (List.getElem_mem hi)
    · intro x hx y hy
      obtain ⟨i, hi, hiα, rfl⟩ := (hmemL x).mp hx
      obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail y).mp hy
      constructor
      · intro hadj
        by_cases hmlast : m = Q.length - 1
        · have hatt₂ : P[i]'hi ∈
              attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hi, Q[m]'hm, hF₂idx m hm (by omega), hadj⟩
          have := hAfter' i hi hatt₂
          omega
        · have hmF₁ : Q[m]'hm ∈ {z : V | z ∈ SPGT.interior Q} :=
            PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
          have hatt₁ : P[i]'hi ∈
              attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hi, Q[m]'hm, hmF₁, hadj⟩
          have hir := hW₁range i hi hatt₁
          have hiEq : i = α := by omega
          have hmEq : m = 1 := by
            by_contra hmne
            have hatt₂ : P[i]'hi ∈
                attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hi, Q[m]'hm, hF₂idx m hm (by omega), hadj⟩
            have := hAfter' i hi hatt₂
            omega
          exact ⟨gidx P hiEq hi hαlt, gidx Q hmEq hm (by omega)⟩
      · rintro ⟨he1, he2⟩
        have hiEq : i = α := (List.Nodup.getElem_inj_iff hnd).mp he1
        have hmEq : m = 1 :=
          (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp he2
        subst hiEq
        subst hmEq
        exact hαf1
  set P' : List V := (P.drop 0).take (α - 0 + 1) ++ Q.tail with hP'def
  have hP'from : IsPathFrom G P' p₁ (Q[Q.length - 1]'(by omega)) := by
    rw [← hp0]
    exact hP'from0
  have hP'l : IsPathList G P' := hP'from.1
  have hmemP' : ∀ x : V, x ∈ P' ↔
      ((∃ (i : ℕ) (hi : i < P.length), i ≤ α ∧ P[i]'hi = x) ∨ x ∈ Q.tail) := by
    intro x
    rw [hP'def, List.mem_append, hmemL]
  have hP'Y : ∀ w ∈ P', VertexComplete G w Y → w = p₁ := by
    intro w hw hwY
    by_contra hwne
    obtain ⟨j, hj, hjα, rfl⟩ :
        ∃ (j : ℕ) (hj : j < P.length), j ≤ α ∧ P[j]'hj = w := by
      rcases (hmemP' w).mp hw with h | h
      · exact h
      · exact absurd hwY (hFY _ ((htailF _).mp h))
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hwne (by rw [← hp0])
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact hq₂Y (by rw [← hp1]; exact hwY)
    have hP'len : P'.length = α + 1 + (Q.length - 1) := by
      rw [hP'def, List.length_append, PathBasics.length_slice P (Nat.zero_le α) hαlt]
      simp
    have hP'5 : 5 ≤ P'.length := by omega
    have hP'1lt : 1 < P'.length := by omega
    set p₂' : V := P'[1]'hP'1lt with hp₂'def
    have hp₂'head : P'.tail.head? = some p₂' := by
      rw [hp₂'def]
      exact tail_head?_getElem hP'1lt
    have hp₂'Y : ¬ VertexComplete G p₂' Y := by
      intro hpY
      have hpMem : p₂' ∈ P' := by rw [hp₂'def]; exact List.getElem_mem _
      rcases (hmemP' _).mp hpMem with ⟨i, hi, hiα, hieq⟩ | htail
      · have hP'0 : P'[0]'(by omega) = p₁ :=
          PathBasics.getElem_zero_of_head? hP'from.2.1 (by omega)
        have hadj0 : G.Adj p₁ p₂' := by
          rw [← hP'0, hp₂'def]
          exact PathBasics.path_adj_succ hP'l (show 0 + 1 < P'.length by omega)
        have hadjP : G.Adj (P[0]'h0lt) (P[i]'hi) := by rw [hp0, hieq]; exact hadj0
        have hiIdx := (PathBasics.path_adj_iff hP h0lt hi).mp hadjP
        have hiEq : i = 1 := by omega
        subst hiEq
        apply hq₂Y
        rw [← hieq] at hpY
        rw [hp1] at hpY
        exact hpY
      · exact hFY _ ((htailF _).mp htail) hpY
    have hout : ∀ v ∈ P', v ∉ X ∧ v ∉ Y := by
      intro v hv
      rcases (hmemP' v).mp hv with ⟨i, hi, -, rfl⟩ | htail
      · exact hPXY _ (List.getElem_mem hi)
      · exact ⟨fun hx => hFXY _ ((htailF _).mp htail) (Set.mem_union_left _ hx),
          fun hy => hFXY _ ((htailF _).mp htail) (Set.mem_union_right _ hy)⟩
    have hXc : ∀ v ∈ P', VertexComplete G v X ↔
        (v = p₁ ∨ v = Q[Q.length - 1]'(by omega)) := by
      intro v hv
      rcases (hmemP' v).mp hv with ⟨i, hi, hiα, rfl⟩ | htail
      · constructor
        · intro hvX
          rcases (hXuniq _ (List.getElem_mem hi)).mp hvX with he | he
          · exact Or.inl he
          · exfalso
            have hin : i = P.length - 1 := by
              have hpN : P[P.length - 1]'(by omega) = pₙ :=
                PathBasics.getElem_last_of_getLast? hlast (by omega)
              rw [← hpN] at he
              exact (List.Nodup.getElem_inj_iff hnd).mp he
            omega
        · rintro (he | he)
          · exact (hXuniq _ (List.getElem_mem hi)).mpr (Or.inl he)
          · exfalso
            exact hFP _ hfkF (by rw [← he]; exact List.getElem_mem hi)
      · constructor
        · intro hvX
          exact Or.inr (huniqueX v ((htailF _).mp htail) hvX)
        · rintro (rfl | rfl)
          · exfalso
            exact hFP _ ((htailF _).mp htail) (PathBasics.head_mem hhead)
          · exact hfkX
    have hpw : IsPseudowheel G X Y P' :=
      PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl hP'from
        hp₂'head hout hP'5 hXc hp₁Y ⟨P[j]'hj, hw, hwne, hwY⟩ hp₂'Y (hFY _ hfkF)
    have hsubset : {v : V | v ∈ P' ∧ VertexComplete G v Y} ⊆
        {v : V | v ∈ P ∧ VertexComplete G v Y} := by
      rintro v ⟨hv, hvY⟩
      refine ⟨?_, hvY⟩
      rcases (hmemP' v).mp hv with ⟨i, hi, -, rfl⟩ | htail
      · exact List.getElem_mem hi
      · exact absurd hvY (hFY _ ((htailF _).mp htail))
    have hbnot : P[b]'hblen ∉ {v : V | v ∈ P' ∧ VertexComplete G v Y} := by
      rintro ⟨hbP', -⟩
      rcases (hmemP' _).mp hbP' with ⟨i, hi, hiα, hieq⟩ | htail
      · have hib : i = b := (List.Nodup.getElem_inj_iff hnd).mp hieq
        omega
      · exact hFP _ ((htailF _).mp htail) (List.getElem_mem hblen)
    exact hopt.2.1 ⟨X, Y, P', hpw,
      Set.ncard_lt_ncard
        ((Set.ssubset_iff_of_subset hsubset).mpr
          ⟨P[b]'hblen, ⟨List.getElem_mem hblen, hbY⟩, hbnot⟩)
        (Set.toFinite _)⟩
  refine ⟨hαf1, ?_⟩
  intro j hj hj0 hjα hjY
  have hmem : P[j]'hj ∈ P' := (hmemP' _).mpr (Or.inl ⟨j, hj, hjα, rfl⟩)
  have he := hP'Y _ hmem hjY
  rw [← hp0] at he
  have := (List.Nodup.getElem_inj_iff hnd).mp he
  omega

/-- The `b₂ = n` case when `F \ {f₁}` has an actual attachment.  The first such
attachment and the last attachment of `F \ {f_k}` close the path through `F` into the hole
used in the printed proof. -/
private theorem last_nonempty_contra (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b) (hbY : VertexComplete G (P[b]'hblen) Y)
    (fr : Frame G X Y P F a b halen) (hlast₂ : fr.b₂ = P.length - 1)
    (hW₂ex : ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P}) : False := by
  classical
  let Q : List V := fr.Q
  let α : ℕ := fr.α
  let β : ℕ := fr.β
  let a₂ : ℕ := fr.a₂
  let b₂ : ℕ := fr.b₂
  have hQl : IsPathList G Q := fr.hQl
  have hQlen3 : 3 ≤ Q.length := fr.hQlen3
  have hαlt : α < P.length := fr.hαlt
  have hβlt : β < P.length := fr.hβlt
  have ha₂lt : a₂ < P.length := fr.ha₂lt
  have hb₂lt : b₂ < P.length := fr.hb₂lt
  have hαa : α ≤ a := fr.hαa
  have haβ : a ≤ β := fr.haβ
  have hβb : β ≤ b := fr.hβb
  have hβatt : P[β]'hβlt ∈
      attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} := by
    simpa [Q, β] using fr.hβatt
  have hW₁range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
        α ≤ j ∧ j ≤ β := by
    simpa [Q, α, β] using fr.hW₁range
  have hαβnoY : ∀ (j : ℕ) (hj : j < P.length), α < j → j < β →
      ¬ VertexComplete G (P[j]'hj) Y := by
    simpa [α, β] using fr.hαβnoY
  have hP₂noY : ∀ (j : ℕ) (hj : j < P.length), a₂ < j → j < b₂ →
      ¬ VertexComplete G (P[j]'hj) Y := by
    simpa [a₂, b₂] using fr.hP₂noY
  have hW₂range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} →
        a₂ ≤ j ∧ j ≤ b₂ := by
    simpa [Q, a₂, b₂] using fr.hW₂range
  have htailF : ∀ z : V, z ∈ Q.tail ↔ z ∈ F := by
    simpa [Q] using fr.htailF
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ Q[i]'hi = z := by
    simpa [Q] using fr.hFmem
  have hfkF : Q[Q.length - 1]'(by omega) ∈ F :=
    (hFmem _).mpr ⟨Q.length - 1, by omega, by omega, rfl⟩
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hBerge : Berge G := hG.1.1.1.1
  have hqn : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have hpₙY : ¬ VertexComplete G pₙ Y := by rw [← hqn]; exact hqₙY
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have h1lt : 1 < P.length := by omega
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hFP : ∀ z ∈ F, z ∉ P := fun z hz => (hmin.1.1 z hz).2
  have hFXY : ∀ z ∈ F, z ∉ X ∪ Y := fun z hz => (hmin.1.1 z hz).1
  have hFY : ∀ z ∈ F, ¬ VertexComplete G z Y := hmin.1.2.2
  have hPY : ∀ z ∈ P, z ∉ Y := fun z hz => (hPXY z hz).2
  have hQtailSub : ∀ z : V, z ∈ Q.tail → z ∈ F := by
    intro z hz
    exact (htailF z).mp hz
  have hF₂sub : ∀ z : V, z ∈ Q.drop 2 → z ∈ F := by
    intro z hz
    apply hQtailSub z
    have he : Q.drop 2 = Q.tail.tail := by
      cases Q with
      | nil => rfl
      | cons x l => cases l <;> rfl
    rw [he] at hz
    exact List.mem_of_mem_tail hz
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m →
      Q[m]'hm ∈ {z : V | z ∈ Q.drop 2} := by
    intro m hm hm2
    have hi : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hi = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hi
  have hf1F₁ : Q[1]'(by omega) ∈ {z : V | z ∈ SPGT.interior Q} :=
    PathBasics.getElem_mem_interior hQl (by omega) (by omega) (by omega)
  have hfkF₂ : Q[Q.length - 1]'(by omega) ∈ {z : V | z ∈ Q.drop 2} :=
    hF₂idx _ (by omega) (by omega)
  have hf1notF₂ : Q[1]'(by omega) ∉ {z : V | z ∈ Q.drop 2} := by
    intro hz
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hz
    have hiQ : 2 + i < Q.length := by simp only [List.length_drop] at hi; omega
    have heq : Q[2 + i]'hiQ = Q[1]'(by omega) := by simpa using he
    have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp heq
    omega
  have hbn : b ≠ P.length - 1 := by
    intro he
    apply hpₙY
    rw [← hpn]
    rw [gidx P he hblen hnlt] at hbY
    exact hbY
  have hblast : b < P.length - 1 := by omega
  have hba₂ : b ≤ a₂ := by
    by_contra hlt
    have hb₂last : b₂ = P.length - 1 := by simpa [b₂] using hlast₂
    exact hP₂noY b hblen (by omega) (by omega) hbY
  have hF₂after : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} → b ≤ j := by
    intro j hj hatt
    have hjrange := hW₂range j hj hatt
    omega
  obtain ⟨hαf1, hleftY⟩ := left_clear G X Y P p₁ pₙ hopt hhead hlast F hmin
    a b halen hblen ha0 hab hbY fr (by simpa [Q] using hF₂after)
  have hleftY' : ∀ (j : ℕ) (hj : j < P.length), 0 < j → j ≤ α →
      ¬ VertexComplete G (P[j]'hj) Y := by
    simpa [α] using hleftY
  obtain ⟨hγlt, hγatt⟩ := Nat.find_spec hW₂ex
  let γ : ℕ := Nat.find hW₂ex
  have hγmin : ∀ (j : ℕ) (hj : j < P.length), j < γ →
      P[j]'hj ∉ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} := by
    intro j hj hjγ hatt
    exact Nat.find_min hW₂ex hjγ ⟨hj, hatt⟩
  have ha₂γ : a₂ ≤ γ := (hW₂range γ hγlt hγatt).1
  have hβγle : β ≤ γ := by omega
  have hβγ : β < γ := by
    rcases eq_or_lt_of_le hβγle with heq | hlt
    · exfalso
      have hYloc0 : ∀ (j : ℕ) (hj : j < P.length),
          VertexComplete G (P[j]'hj) Y → j = 0 ∨ j = β := by
        intro j hj hjY
        by_cases hj0 : j = 0
        · exact Or.inl hj0
        right
        by_cases hjβ : j < β
        · rcases le_or_gt j α with hjα | hαj
          · exact absurd hjY (hleftY' j hj (by omega) hjα)
          · exact absurd hjY (hαβnoY j hj hαj hjβ)
        · by_cases hβj : β < j
          · have hjlast : j < P.length - 1 := by
              by_contra hn
              have hjEq : j = P.length - 1 := by omega
              apply hpₙY
              rw [← hpn]
              rw [gidx P hjEq hj hnlt] at hjY
              exact hjY
            have hb₂last : b₂ = P.length - 1 := by simpa [b₂] using hlast₂
            exact absurd hjY (hP₂noY j hj (by omega) (by omega))
          · omega
      have hempty : HoleYEdgeParity.yEdges G Y P = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
        have hiLoc := hYloc0 i hi huY
        have hjLoc := hYloc0 j hj hvY
        have hadjIdx := (PathBasics.path_adj_iff hP hi hj).mp huv
        rcases hiLoc with hiLoc | hiLoc <;> rcases hjLoc with hjLoc | hjLoc
        · have hij : i = j := by omega
          exact (G.ne_of_adj huv) (gidx P hij hi hj)
        · omega
        · omega
        · have hij : i = j := by omega
          exact (G.ne_of_adj huv) (gidx P hij hi hj)
      have hthreeP : 3 ≤ (HoleYEdgeParity.yEdges G Y P).ncard :=
        (_root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1).1.2
      have hzero : (HoleYEdgeParity.yEdges G Y P).ncard = 0 := by
        rw [hempty, Set.ncard_empty]
      omega
    · exact hlt
  have hβf1 : G.Adj (P[β]'hβlt) (Q[1]'(by omega)) := by
    obtain ⟨-, z, hzF₁, hβz⟩ := hβatt
    obtain ⟨m, hm, hm1, hm2, he⟩ :=
      PathBasics.exists_getElem_of_mem_interior hQl hzF₁
    have hmEq : m = 1 := by
      by_contra hne
      have hmF₂ := hF₂idx m hm (by omega)
      have hatt₂ : P[β]'hβlt ∈
          attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hβlt, Q[m]'hm, hmF₂, by rw [he]; exact hβz⟩
      exact (hγmin β hβlt hβγ hatt₂).elim
    have he' : Q[1]'(by omega) = z := (gidx Q hmEq.symm (by omega) hm).trans he
    rw [he']
    exact hβz
  have hγfk : G.Adj (P[γ]'hγlt) (Q[Q.length - 1]'(by omega)) := by
    obtain ⟨-, z, hzF₂, hγz⟩ := hγatt
    obtain ⟨m, hm, hm1, he⟩ := (hFmem z).mp (hF₂sub z hzF₂)
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hmEq : m = 1 := by omega
      subst hmEq
      exact hf1notF₂ (by rw [he]; exact hzF₂)
    have hmEq : m = Q.length - 1 := by
      by_contra hne
      have hmF₁ : Q[m]'hm ∈ {z : V | z ∈ SPGT.interior Q} :=
        PathBasics.getElem_mem_interior hQl hm (by omega) (by omega)
      have hatt₁ : P[γ]'hγlt ∈
          attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hγlt, Q[m]'hm, hmF₁, by rw [he]; exact hγz⟩
      have := hW₁range γ hγlt hatt₁
      omega
    have he' : z = Q[Q.length - 1]'(by omega) := by
      rw [← he]
      exact gidx Q hmEq hm (by omega)
    rw [he'] at hγz
    exact hγz
  have hTailFrom : IsPathFrom G Q.tail (Q[1]'(by omega))
      (Q[Q.length - 1]'(by omega)) := by
    have ht : IsPathList G Q.tail := by
      simpa only [List.drop_one] using PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
    refine ⟨ht, tail_head?_getElem (by omega), ?_⟩
    rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
  let S : List V := (P.drop β).take (γ - β + 1)
  have hSfrom : IsPathFrom G S (P[β]'hβlt) (P[γ]'hγlt) := by
    dsimp [S]
    exact PathBasics.isPathFrom_slice hP hβγ hγlt
  have hSrev : IsPathFrom G S.reverse (P[γ]'hγlt) (P[β]'hβlt) :=
    PathBasics.isPathFrom_reverse hSfrom
  have hmemS : ∀ x : V, x ∈ S.reverse ↔
      ∃ (j : ℕ) (hj : j < P.length), β ≤ j ∧ j ≤ γ ∧ P[j]'hj = x := by
    intro x
    rw [List.mem_reverse]
    dsimp [S]
    rw [PathBasics.mem_slice_iff P (le_of_lt hβγ) hγlt]
  have hmemTail : ∀ x : V, x ∈ Q.tail ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hm : i + 1 < Q.length := by simp only [List.length_tail] at hi; omega
      exact ⟨i + 1, hm, by omega, by simp⟩
    · rintro ⟨m, hm, hm1, rfl⟩
      have hi : m - 1 < Q.tail.length := by simp; omega
      have he : Q.tail[m - 1]'hi = Q[m]'hm := by
        simp only [List.getElem_tail]
        exact gidx Q (by omega) (by omega) hm
      rw [← he]
      exact List.getElem_mem hi
  have hHole : IsHoleList G (Q.tail ++ S.reverse) := by
    refine PathGlue.glue_hole hTailFrom hSrev ?_ ?_ ?_
    · intro x hx hxs
      obtain ⟨j, hj, -, -, rfl⟩ := (hmemS x).mp hxs
      exact hFP _ (hQtailSub _ hx) (List.getElem_mem hj)
    · intro x hx y hy
      obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail x).mp hx
      obtain ⟨j, hj, hβj, hjγ, rfl⟩ := (hmemS y).mp hy
      constructor
      · intro hadj
        rcases eq_or_lt_of_le hm1 with hmone | hmgt
        · subst hmone
          have hatt : P[j]'hj ∈
              attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hj, _, hf1F₁, hadj.symm⟩
          have hjle := (hW₁range j hj hatt).2
          have hjeq : j = β := by omega
          subst hjeq
          exact Or.inr ⟨rfl, rfl⟩
        · by_cases hmlast : m = Q.length - 1
          · subst hmlast
            have hatt : P[j]'hj ∈
                attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hj, _, hfkF₂, hadj.symm⟩
            have hjge : γ ≤ j := by
              by_contra hlt
              exact hγmin j hj (by omega) hatt
            have hjeq : j = γ := by omega
            subst hjeq
            exact Or.inl ⟨rfl, rfl⟩
          · have hmF₁ : Q[m]'hm ∈ {z : V | z ∈ SPGT.interior Q} :=
              PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
            have hatt₁ : P[j]'hj ∈
                attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hj, _, hmF₁, hadj.symm⟩
            have hjle := (hW₁range j hj hatt₁).2
            have hmF₂ := hF₂idx m hm (by omega)
            have hatt₂ : P[j]'hj ∈
                attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
              ⟨List.getElem_mem hj, _, hmF₂, hadj.symm⟩
            exact (hγmin j hj (by omega) hatt₂).elim
      · rintro (⟨hm', hj'⟩ | ⟨hm', hj'⟩)
        · have hmEq : m = Q.length - 1 :=
            (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm'
          have hjEq : j = γ := (List.Nodup.getElem_inj_iff hnd).mp hj'
          subst hmEq
          subst hjEq
          exact hγfk.symm
        · have hmEq : m = 1 :=
            (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm'
          have hjEq : j = β := (List.Nodup.getElem_inj_iff hnd).mp hj'
          subst hmEq
          subst hjEq
          exact hβf1.symm
    · dsimp [S]
      rw [List.length_reverse, PathBasics.length_slice P (le_of_lt hβγ) hγlt]
      simp
      omega
  have hYloc : ∀ (j : ℕ) (hj : j < P.length),
      VertexComplete G (P[j]'hj) Y → j = 0 ∨ (β ≤ j ∧ j ≤ γ) := by
    intro j hj hjY
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    right
    constructor
    · by_contra hlt
      rcases le_or_gt j α with hjα | hαj
      · exact absurd hjY (hleftY' j hj (by omega) hjα)
      · exact absurd hjY (hαβnoY j hj hαj (by omega))
    · by_contra hlt
      have hjlast : j < P.length - 1 := by
        by_contra hn
        have hjEq : j = P.length - 1 := by omega
        apply hpₙY
        rw [← hpn]
        rw [gidx P hjEq hj hnlt] at hjY
        exact hjY
      have hb₂last : b₂ = P.length - 1 := by simpa [b₂] using hlast₂
      exact hP₂noY j hj (by omega) (by omega) hjY
  have hHY : ∀ w ∈ Q.tail ++ S.reverse, w ∉ Y := by
    intro w hw
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact fun h => hFXY _ (hQtailSub _ hw) (Set.mem_union_right _ h)
    · obtain ⟨j, hj, -, -, rfl⟩ := (hmemS w).mp hw
      exact hPY _ (List.getElem_mem hj)
  have hyeq : HoleYEdgeParity.yEdges G Y (Q.tail ++ S.reverse) =
      HoleYEdgeParity.yEdges G Y P := by
    have hto : ∀ w ∈ Q.tail ++ S.reverse, VertexComplete G w Y → w ∈ P := by
      intro w hw hwY
      rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact absurd hwY (hFY _ (hQtailSub _ hw))
      · obtain ⟨j, hj, -, -, rfl⟩ := (hmemS w).mp hw
        exact List.getElem_mem hj
    have hfrom : ∀ (i : ℕ) (hi : i < P.length), VertexComplete G (P[i]'hi) Y →
        ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[i]'hi) (P[j]'hj) →
          VertexComplete G (P[j]'hj) Y → P[i]'hi ∈ Q.tail ++ S.reverse := by
      intro i hi hiY j hj hij hjY
      rcases hYloc i hi hiY with hi0 | hir
      · subst hi0
        have hidx := (PathBasics.path_adj_iff hP hi hj).mp hij
        have hj1 : j = 1 := by omega
        subst hj1
        exact absurd hjY (by rw [hp1]; exact hq₂Y)
      · rw [List.mem_append]
        exact Or.inr ((hmemS _).mpr ⟨i, hi, hir.1, hir.2, rfl⟩)
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      exact ⟨u, hto u hu huY, v, hto v hv hvY, rfl, huv, huY, hvY⟩
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      exact ⟨_, hfrom i hi huY j hj huv hvY, _, hfrom j hj hvY i hi huv.symm huY,
        rfl, huv, huY, hvY⟩
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  exact HoleYEdgeParity.not_odd_ge_three_yEdges' hBerge hYanti hHole hHY
    (by rw [hyeq]; exact h184.1.1) (by rw [hyeq]; exact h184.1.2)

/-- The path `f_k-⋯-f₁-p_β-⋯-p_n` contradicts 18.3 whenever no vertex of its
`P`-suffix attaches to `F \ {f₁}` and that suffix has an odd number of `Y`-complete edges. -/
private theorem suffix_path_contra (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (ha0 : 0 < a)
    (fr : Frame G X Y P F a b halen)
    (hNoF₂ : ∀ (j : ℕ) (hj : j < P.length), fr.β ≤ j →
      P[j]'hj ∉ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P})
    (hoddSuffix : Odd (HoleYEdgeParity.yEdges G Y (P.drop fr.β)).ncard) : False := by
  classical
  let Q : List V := fr.Q
  let β : ℕ := fr.β
  have hQl : IsPathList G Q := fr.hQl
  have hQlen3 : 3 ≤ Q.length := fr.hQlen3
  have hβlt : β < P.length := fr.hβlt
  have hβpos : 0 < β := by have := fr.haβ; omega
  have hβatt : P[β]'hβlt ∈
      attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} := by
    simpa [Q, β] using fr.hβatt
  have hW₁range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
        fr.α ≤ j ∧ j ≤ β := by
    simpa [Q, β] using fr.hW₁range
  have hNoF₂' : ∀ (j : ℕ) (hj : j < P.length), β ≤ j →
      P[j]'hj ∉ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} := by
    simpa [Q, β] using hNoF₂
  have hoddSuffix' : Odd (HoleYEdgeParity.yEdges G Y (P.drop β)).ncard := by
    simpa [β] using hoddSuffix
  have htailF : ∀ z : V, z ∈ Q.tail ↔ z ∈ F := by
    simpa [Q] using fr.htailF
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ Q[i]'hi = z := by
    simpa [Q] using fr.hFmem
  have hfkF' : Q[Q.length - 1]'(by omega) ∈ F :=
    (hFmem _).mpr ⟨Q.length - 1, by omega, by omega, rfl⟩
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hq1 : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
  have hqn : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have hpₙY : ¬ VertexComplete G pₙ Y := by rw [← hqn]; exact hqₙY
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hXuniq : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
    intro v hv
    rw [← hq1, ← hqn]
    exact hXuniq0 v hv
  have hFP : ∀ z ∈ F, z ∉ P := fun z hz => (hmin.1.1 z hz).2
  have hFXY : ∀ z ∈ F, z ∉ X ∪ Y := fun z hz => (hmin.1.1 z hz).1
  have hFY : ∀ z ∈ F, ¬ VertexComplete G z Y := hmin.1.2.2
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m →
      Q[m]'hm ∈ {z : V | z ∈ Q.drop 2} := by
    intro m hm hm2
    have hi : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hi = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hi
  have hf1F₁ : Q[1]'(by omega) ∈ {z : V | z ∈ SPGT.interior Q} :=
    PathBasics.getElem_mem_interior hQl (by omega) (by omega) (by omega)
  have hβf1 : G.Adj (P[β]'hβlt) (Q[1]'(by omega)) := by
    obtain ⟨-, z, hzF₁, hβz⟩ := hβatt
    obtain ⟨m, hm, hm1, hm2, he⟩ :=
      PathBasics.exists_getElem_of_mem_interior hQl hzF₁
    have hmEq : m = 1 := by
      by_contra hne
      have hatt₂ : P[β]'hβlt ∈
          attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hβlt, Q[m]'hm, hF₂idx m hm (by omega), by rw [he]; exact hβz⟩
      exact (hNoF₂' β hβlt le_rfl hatt₂).elim
    have he' : Q[1]'(by omega) = z := (gidx Q hmEq.symm (by omega) hm).trans he
    rw [he']
    exact hβz
  have hTailFrom : IsPathFrom G Q.tail (Q[1]'(by omega))
      (Q[Q.length - 1]'(by omega)) := by
    have ht : IsPathList G Q.tail := by
      simpa only [List.drop_one] using PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
    refine ⟨ht, tail_head?_getElem (by omega), ?_⟩
    rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
  have hTailRev : IsPathFrom G Q.tail.reverse (Q[Q.length - 1]'(by omega))
      (Q[1]'(by omega)) := PathBasics.isPathFrom_reverse hTailFrom
  have hDropFrom : IsPathFrom G (P.drop β) (P[β]'hβlt) pₙ := by
    refine ⟨PathBasics.isPathList_drop hP hβlt, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hβlt]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hlast
  have hmemTail : ∀ x : V, x ∈ Q.tail.reverse ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = x := by
    intro x
    rw [List.mem_reverse]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hm : i + 1 < Q.length := by simp only [List.length_tail] at hi; omega
      exact ⟨i + 1, hm, by omega, by simp⟩
    · rintro ⟨m, hm, hm1, rfl⟩
      have hi : m - 1 < Q.tail.length := by simp; omega
      have he : Q.tail[m - 1]'hi = Q[m]'hm := by
        simp only [List.getElem_tail]
        exact gidx Q (by omega) (by omega) hm
      rw [← he]
      exact List.getElem_mem hi
  have hmemDrop : ∀ x : V, x ∈ P.drop β ↔
      ∃ (j : ℕ) (hj : j < P.length), β ≤ j ∧ P[j]'hj = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hj : β + i < P.length := by simp only [List.length_drop] at hi; omega
      exact ⟨β + i, hj, by omega, by simp⟩
    · rintro ⟨j, hj, hβj, rfl⟩
      have hi : j - β < (P.drop β).length := by simp; omega
      have he : (P.drop β)[j - β]'hi = P[j]'hj := by
        simp only [List.getElem_drop]
        exact gidx P (by omega) (by omega) hj
      rw [← he]
      exact List.getElem_mem hi
  let R : List V := Q.tail.reverse ++ P.drop β
  have hRfrom : IsPathFrom G R (Q[Q.length - 1]'(by omega)) pₙ := by
    dsimp [R]
    refine PathGlue.glue_path hTailRev hDropFrom ?_ ?_
    · intro x hx hxp
      obtain ⟨j, hj, -, rfl⟩ := (hmemDrop x).mp hxp
      exact hFP _ ((htailF _).mp (by simpa using hx)) (List.getElem_mem hj)
    · intro x hx y hy
      obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail x).mp hx
      obtain ⟨j, hj, hβj, rfl⟩ := (hmemDrop y).mp hy
      constructor
      · intro hadj
        rcases eq_or_lt_of_le hm1 with hmone | hmgt
        · subst hmone
          have hatt₁ : P[j]'hj ∈
              attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hj, _, hf1F₁, hadj.symm⟩
          have hjle := (hW₁range j hj hatt₁).2
          have hjeq : j = β := by omega
          subst hjeq
          exact ⟨rfl, rfl⟩
        · have hatt₂ : P[j]'hj ∈
              attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
            ⟨List.getElem_mem hj, _, hF₂idx m hm (by omega), hadj.symm⟩
          exact (hNoF₂' j hj hβj hatt₂).elim
      · rintro ⟨hm', hj'⟩
        have hmEq : m = 1 :=
          (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hQl)).mp hm'
        have hjEq : j = β := (List.Nodup.getElem_inj_iff hnd).mp hj'
        subst hmEq
        subst hjEq
        exact hβf1.symm
  have hRXY : ∀ w ∈ R, w ∉ X ∪ Y := by
    intro w hw
    change w ∈ Q.tail.reverse ++ P.drop β at hw
    rcases List.mem_append.mp hw with hw | hw
    · have hwF : w ∈ F := (htailF _).mp (by simpa using hw)
      exact hFXY w hwF
    · obtain ⟨j, hj, -, rfl⟩ := (hmemDrop w).mp hw
      rintro (hx | hy)
      · exact (hPXY _ (List.getElem_mem hj)).1 hx
      · exact (hPXY _ (List.getElem_mem hj)).2 hy
  have hRX : ∀ w ∈ R, VertexComplete G w X ↔
      (w = Q[Q.length - 1]'(by omega) ∨ w = pₙ) := by
    intro w hw
    change w ∈ Q.tail.reverse ++ P.drop β at hw
    rcases List.mem_append.mp hw with hw | hw
    · have hwF : w ∈ F := (htailF _).mp (by simpa using hw)
      constructor
      · intro hwX
        exact Or.inl (fr.huniqueX w hwF hwX)
      · rintro (rfl | rfl)
        · exact fr.hfkX
        · exfalso
          exact hFP _ hwF (by rw [← hpn]; exact List.getElem_mem hnlt)
    · obtain ⟨j, hj, hβj, rfl⟩ := (hmemDrop w).mp hw
      constructor
      · intro hwX
        rcases (hXuniq _ (List.getElem_mem hj)).mp hwX with he | he
        · rw [← PathBasics.getElem_zero_of_head? hhead h0lt] at he
          have hj0 := (List.Nodup.getElem_inj_iff hnd).mp he
          omega
        · exact Or.inr he
      · rintro (he | he)
        · exfalso
          exact hFP _ hfkF' (by rw [← he]; exact List.getElem_mem hj)
        · exact (hXuniq _ (List.getElem_mem hj)).mpr (Or.inr he)
  have hyeq : HoleYEdgeParity.yEdges G Y R =
      HoleYEdgeParity.yEdges G Y (P.drop β) := by
    have hto : ∀ w ∈ R, VertexComplete G w Y → w ∈ P.drop β := by
      intro w hw hwY
      change w ∈ Q.tail.reverse ++ P.drop β at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact absurd hwY (hFY _ ((htailF _).mp (by simpa using hw)))
      · exact hw
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      exact ⟨u, hto u hu huY, v, hto v hv hvY, rfl, huv, huY, hvY⟩
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      exact ⟨u, by change u ∈ Q.tail.reverse ++ P.drop β; simp [hu],
        v, by change v ∈ Q.tail.reverse ++ P.drop β; simp [hv],
        rfl, huv, huY, hvY⟩
  have hoddR : Odd (HoleYEdgeParity.yEdges G Y R).ncard := by
    rw [hyeq]
    exact hoddSuffix'
  obtain ⟨e, he⟩ : (HoleYEdgeParity.yEdges G Y (P.drop β)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [Nat.odd_iff] at hoddSuffix'; omega)
  obtain ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩ := he
  obtain ⟨i, hi, hβi, hiu⟩ := (hmemDrop u).mp hu
  obtain ⟨j, hj, hβj, hjv⟩ := (hmemDrop v).mp hv
  have hidx := (PathBasics.path_adj_iff hP hi hj).mp (by rw [hiu, hjv]; exact huv)
  have hinlast : i ≠ P.length - 1 := by
    intro heq
    apply hpₙY
    rw [← hpn, ← gidx P heq hi hnlt, hiu]
    exact huY
  have hjnlast : j ≠ P.length - 1 := by
    intro heq
    apply hpₙY
    rw [← hpn, ← gidx P heq hj hnlt, hjv]
    exact hvY
  have hR5 : 5 ≤ R.length := by
    change 5 ≤ (Q.tail.reverse ++ P.drop β).length
    simp only [List.length_append, List.length_reverse, List.length_tail, List.length_drop]
    omega
  have huR : u ∈ R := by
    change u ∈ Q.tail.reverse ++ P.drop β
    exact List.mem_append_right _ hu
  have hvR : v ∈ R := by
    change v ∈ Q.tail.reverse ++ P.drop β
    exact List.mem_append_right _ hv
  have htwoY : 2 ≤ {w : V | w ∈ R ∧ VertexComplete G w Y}.ncard :=
    (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨u, ⟨huR, huY⟩, v, ⟨hvR, hvY⟩, G.ne_of_adj huv⟩
  have h183 := _root_.Workspace.Statements.S18.SPGT.thm_18_3 G hG X Y hXY hXne hYne
    hXanti hYanti hcompl R (Q[Q.length - 1]'(by omega)) pₙ hRfrom.1 hRXY hR5
    hRfrom.2.1 hRfrom.2.2 hRX
  have hpar := (h183.2 htwoY).2
  have hendempty : {w : V | (w = Q[Q.length - 1]'(by omega) ∨ w = pₙ) ∧
      VertexComplete G w Y} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl | rfl, hwY⟩
    · exact hFY _ ((htailF _).mp (by
          have hi : Q.length - 1 - 1 < Q.tail.length := by simp; omega
          have he : Q.tail[Q.length - 1 - 1]'hi = Q[Q.length - 1]'(by omega) := by
            simp only [List.getElem_tail]
            exact gidx Q (by omega) (by omega) (by omega)
          rw [← he]
          exact List.getElem_mem hi)) hwY
    · exact hpₙY hwY
  rw [hendempty, Set.ncard_empty] at hpar
  change (HoleYEdgeParity.yEdges G Y R).ncard % 2 = 0 at hpar
  rw [Nat.odd_iff] at hoddR
  omega

/-- The `a₂=b₂=0` case with a genuine attachment.  The left part has even
`Y`-complete-edge count by 2.3.  Unless the one edge between the two tight endpoints is
itself `Y`-complete, the odd total count therefore lies in the right suffix and 18.3 applies;
the remaining one-edge exception is `zero_exception_contra`. -/
private theorem zero_nonempty_contra (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b) (hbY : VertexComplete G (P[b]'hblen) Y)
    (fr : Frame G X Y P F a b halen) (hzero : fr.a₂ = 0 ∧ fr.b₂ = 0)
    (hW₂ex : ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P}) : False := by
  classical
  let Q : List V := fr.Q
  let α : ℕ := fr.α
  let β : ℕ := fr.β
  have hQl : IsPathList G Q := fr.hQl
  have hQlen3 : 3 ≤ Q.length := fr.hQlen3
  have hαlt : α < P.length := fr.hαlt
  have hβlt : β < P.length := fr.hβlt
  have hαa : α ≤ a := fr.hαa
  have haβ : a ≤ β := fr.haβ
  have hβb : β ≤ b := fr.hβb
  have hαβ : α ≤ β := by omega
  have hαβnoY : ∀ (j : ℕ) (hj : j < P.length), α < j → j < β →
      ¬ VertexComplete G (P[j]'hj) Y := by simpa [α, β] using fr.hαβnoY
  have hW₁range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
        α ≤ j ∧ j ≤ β := by
    simpa [Q, α, β] using fr.hW₁range
  have hW₂range : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} → j = 0 := by
    intro j hj hatt
    have := fr.hW₂range j hj (by simpa [Q] using hatt)
    omega
  have htailF : ∀ z : V, z ∈ Q.tail ↔ z ∈ F := by simpa [Q] using fr.htailF
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = z := by
    simpa [Q] using fr.hFmem
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hPnd : P.Nodup := PathBasics.path_nodup hP
  have hQnd : Q.Nodup := PathBasics.path_nodup hQl
  have hBerge : Berge G := hG.1.1.1.1
  have h0lt : 0 < P.length := by omega
  have h1lt : 1 < P.length := by omega
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hp0Y : VertexComplete G (P[0]'h0lt) Y := by
    have hq₁ : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
    have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
    rw [hp0, ← hq₁]
    exact hq₁Y
  have hFP : ∀ z ∈ F, z ∉ P := fun z hz => (hmin.1.1 z hz).2
  have hFXY : ∀ z ∈ F, z ∉ X ∪ Y := fun z hz => (hmin.1.1 z hz).1
  have hFY : ∀ z ∈ F, ¬ VertexComplete G z Y := hmin.1.2.2
  have hF₂idx : ∀ (m : ℕ) (hm : m < Q.length), 2 ≤ m → Q[m]'hm ∈ Q.drop 2 := by
    intro m hm hm2
    have hr : m - 2 < (Q.drop 2).length := by simp; omega
    have he : (Q.drop 2)[m - 2]'hr = Q[m]'hm := by
      simp only [List.getElem_drop]
      exact gidx Q (by omega) (by omega) hm
    rw [← he]
    exact List.getElem_mem hr
  have hf1Int : Q[1]'(by omega) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQl (by omega) (by omega) (by omega)
  have hAttF1 : ∀ (j : ℕ) (hj : j < P.length), 0 < j →
      P[j]'hj ∈ attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} →
      G.Adj (P[j]'hj) (Q[1]'(by omega)) := by
    intro j hj hj0 hatt
    obtain ⟨-, z, hz, hjz⟩ := hatt
    obtain ⟨m, hm, hm1, hm2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQl hz
    have hmEq : m = 1 := by
      by_contra hne
      have hatt₂ : P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hj, Q[m]'hm, hF₂idx m hm (by omega), by rw [he]; exact hjz⟩
      have := hW₂range j hj hatt₂
      omega
    rw [(gidx Q hmEq.symm (by omega) hm).trans he]
    exact hjz
  have hαf1_of_pos (hαpos : 0 < α) : G.Adj (P[α]'hαlt) (Q[1]'(by omega)) :=
    hAttF1 α hαlt hαpos (by simpa [Q, α] using fr.hαatt)
  have hp0fk_of_pos (hαpos : 0 < α) :
      G.Adj (P[0]'h0lt) (Q[Q.length - 1]'(by omega)) := by
    obtain ⟨j, hj, hatt⟩ := hW₂ex
    have hj0 : j = 0 := hW₂range j hj (by simpa [Q] using hatt)
    obtain ⟨-, z, hz, hjz⟩ := hatt
    have hzQ : z ∈ Q.drop 2 := by simpa [Q] using hz
    obtain ⟨r, hr, hre⟩ := List.getElem_of_mem hzQ
    have hm : 2 + r < Q.length := by simp only [List.length_drop] at hr; omega
    have hzEq : Q[2 + r]'hm = z := by simpa using hre
    have hmLast : 2 + r = Q.length - 1 := by
      by_contra hne
      have hInt : Q[2 + r]'hm ∈ SPGT.interior Q :=
        PathBasics.getElem_mem_interior hQl hm (by omega) (by omega)
      have hatt₁ : P[j]'hj ∈
          attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
        ⟨List.getElem_mem hj, Q[2 + r]'hm, hInt, by rw [hzEq]; exact hjz⟩
      have := hW₁range j hj hatt₁
      omega
    rw [← gidx P hj0 hj h0lt, (gidx Q hmLast.symm (by omega) hm).trans hzEq]
    exact hjz
  let E := Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y P
  let Eleft : Set ℕ := {k | k ∈ E ∧ k < α}
  let Eright : Set ℕ := {k | k ∈ E ∧ β ≤ k}
  have hleftEven : Even Eleft.ncard := by
    by_cases hα2 : 2 ≤ α
    · have hPrefix : IsPathFrom G (P.take (α + 1)) (P[0]'h0lt) (P[α]'hαlt) := by
        simpa using PathBasics.isPathFrom_slice hP (show 0 < α by omega) hαlt
      have hαf1 : G.Adj (P[α]'hαlt) (Q[1]'(by omega)) := hαf1_of_pos (by omega)
      have hp0fk : G.Adj (P[0]'h0lt) (Q[Q.length - 1]'(by omega)) :=
        hp0fk_of_pos (by omega)
      have hTail : IsPathFrom G Q.tail (Q[1]'(by omega)) (Q[Q.length - 1]'(by omega)) := by
        have ht : IsPathList G Q.tail := by
          simpa only [List.drop_one] using
            PathBasics.isPathList_drop hQl (show 1 < Q.length by omega)
        refine ⟨ht, tail_head?_getElem (by omega), ?_⟩
        rw [List.getLast?_tail, if_neg (by omega), List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega)]
      have hmemPrefix : ∀ z : V, z ∈ P.take (α + 1) ↔
          ∃ (j : ℕ) (hj : j < P.length), j ≤ α ∧ P[j]'hj = z := by
        intro z
        have h := PathBasics.mem_slice_iff P (i := 0) (j := α) (Nat.zero_le α) hαlt (x := z)
        simpa using h
      have hmemTail : ∀ z : V, z ∈ Q.tail ↔
          ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ Q[m]'hm = z := by
        intro z
        rw [htailF, hFmem]
      let C : List V := P.take (α + 1) ++ Q.tail
      have hC : IsHoleList G C := by
        dsimp [C]
        refine PathGlue.glue_hole hPrefix hTail ?_ ?_ (by simp; omega)
        · intro z hzP hzQ
          obtain ⟨j, hj, -, rfl⟩ := (hmemPrefix z).mp hzP
          exact hFP _ ((htailF _).mp hzQ) (List.getElem_mem hj)
        · intro z hzP w hzQ
          obtain ⟨j, hj, hjα, rfl⟩ := (hmemPrefix z).mp hzP
          obtain ⟨m, hm, hm1, rfl⟩ := (hmemTail w).mp hzQ
          constructor
          · intro hadj
            rcases eq_or_lt_of_le hm1 with rfl | hm2
            · have hatt₁ : P[j]'hj ∈
                  attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
                ⟨List.getElem_mem hj, Q[1]'hm, hf1Int, hadj⟩
              have hjEq : j = α := by have := hW₁range j hj hatt₁; omega
              exact Or.inl ⟨gidx P hjEq hj hαlt, rfl⟩
            · have hatt₂ : P[j]'hj ∈
                  attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} :=
                ⟨List.getElem_mem hj, Q[m]'hm, hF₂idx m hm hm2, hadj⟩
              have hjEq : j = 0 := hW₂range j hj hatt₂
              have hmEq : m = Q.length - 1 := by
                by_contra hne
                have hInt : Q[m]'hm ∈ SPGT.interior Q :=
                  PathBasics.getElem_mem_interior hQl hm hm1 (by omega)
                have hatt₁ : P[j]'hj ∈
                    attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} :=
                  ⟨List.getElem_mem hj, Q[m]'hm, hInt, hadj⟩
                have := hW₁range j hj hatt₁
                omega
              exact Or.inr ⟨gidx P hjEq hj h0lt, gidx Q hmEq hm (by omega)⟩
          · rintro (⟨hjEq, hmEq⟩ | ⟨hjEq, hmEq⟩)
            · have hj' : j = α := hPnd.getElem_inj_iff.mp hjEq
              have hm' : m = 1 := hQnd.getElem_inj_iff.mp hmEq
              subst j; subst m
              exact hαf1
            · have hj' : j = 0 := hPnd.getElem_inj_iff.mp hjEq
              have hm' : m = Q.length - 1 := hQnd.getElem_inj_iff.mp hmEq
              subst j; subst m
              exact hp0fk
      have hCY : ∀ z ∈ C, z ∉ Y := by
        intro z hzC hzY
        rcases List.mem_append.mp hzC with hzP | hzQ
        · exact (hPXY z (List.mem_of_mem_take hzP)).2 hzY
        · exact hFXY z ((htailF z).mp hzQ) (Set.mem_union_right _ hzY)
      have hyeq : HoleYEdgeParity.yEdges G Y C =
          HoleYEdgeParity.yEdges G Y (P.take (α + 1)) := by
        ext e
        constructor
        · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
          have hup : u ∈ P.take (α + 1) := by
            rcases List.mem_append.mp hu with hu | hu
            · exact hu
            · exact absurd huY (hFY u ((htailF u).mp hu))
          have hvp : v ∈ P.take (α + 1) := by
            rcases List.mem_append.mp hv with hv | hv
            · exact hv
            · exact absurd hvY (hFY v ((htailF v).mp hv))
          exact ⟨u, hup, v, hvp, rfl, huv, huY, hvY⟩
        · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
          exact ⟨u, by exact List.mem_append_left _ hu, v, by exact List.mem_append_left _ hv,
            rfl, huv, huY, hvY⟩
      have hPrefixPath : IsPathList G (P.take (α + 1)) := hPrefix.1
      have hleftEq :
          (Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (P.take (α + 1))).ncard =
            Eleft.ncard := by
        simpa [E, Eleft] using yEdgeIdx_take_ncard G Y P hαlt
      by_contra hnotEven
      have hoddLeft : Odd Eleft.ncard := Nat.not_even_iff_odd.mp hnotEven
      have hoddPrefix : Odd (HoleYEdgeParity.yEdges G Y (P.take (α + 1))).ncard := by
        rw [Workspace.ProofLemmas.Thm183EdgeCount.yEdges_ncard_eq_index_ncard hPrefixPath,
          hleftEq]
        exact hoddLeft
      have hoddC : Odd (HoleYEdgeParity.yEdges G Y C).ncard := by rw [hyeq]; exact hoddPrefix
      have hidxNonempty :
          (Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (P.take (α + 1))).Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero
        rw [hleftEq]
        intro hz
        rw [hz] at hoddLeft
        exact Nat.not_odd_zero hoddLeft
      obtain ⟨k, hk, hkY, hk1Y⟩ := hidxNonempty
      have htakeLen : (P.take (α + 1)).length = α + 1 := by simp; omega
      have hk0 : k ≠ 0 := by
        intro he
        subst k
        apply hq₂Y
        rw [← hp1]
        simpa only [List.getElem_take] using hk1Y
      have hkP : k + 1 < P.length := by rw [htakeLen] at hk; omega
      have hkP0 : k < P.length := by omega
      have hkY' : VertexComplete G (P[k]'hkP0) Y := by
        simpa only [List.getElem_take] using hkY
      have hk1Y' : VertexComplete G (P[k + 1]'hkP) Y := by
        simpa only [List.getElem_take] using hk1Y
      have hkC : P[k]'hkP0 ∈ C := by
        change P[k]'hkP0 ∈ P.take (α + 1) ++ Q.tail
        apply List.mem_append_left
        apply (hmemPrefix _).mpr
        exact ⟨k, hkP0, by rw [htakeLen] at hk; omega, rfl⟩
      have hk1C : P[k + 1]'hkP ∈ C := by
        change P[k + 1]'hkP ∈ P.take (α + 1) ++ Q.tail
        apply List.mem_append_left
        apply (hmemPrefix _).mpr
        exact ⟨k + 1, hkP, by rw [htakeLen] at hk; omega, rfl⟩
      have hp0C : P[0]'h0lt ∈ C := by
        change P[0]'h0lt ∈ P.take (α + 1) ++ Q.tail
        apply List.mem_append_left
        exact (hmemPrefix _).mpr ⟨0, h0lt, by omega, rfl⟩
      have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti C
        (Or.inr hC) hCY).2 hC
      rcases h23 with heven | ⟨c, d, hset, -, -⟩
      · exact hnotEven (by
          rw [← hleftEq,
            ← Workspace.ProofLemmas.Thm183EdgeCount.yEdges_ncard_eq_index_ncard hPrefixPath,
            ← hyeq]
          exact heven)
      · have hp0pair : P[0]'h0lt ∈ ({c, d} : Set V) := by
          rw [← hset]
          exact ⟨hp0C, hp0Y⟩
        have hkpair : P[k]'hkP0 ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hkC, hkY'⟩
        have hk1pair : P[k + 1]'hkP ∈ ({c, d} : Set V) := by
          rw [← hset]; exact ⟨hk1C, hk1Y'⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp0pair hkpair hk1pair
        have h0k : P[0]'h0lt ≠ P[k]'hkP0 := fun he => by
          have := hPnd.getElem_inj_iff.mp he; omega
        have h0k1 : P[0]'h0lt ≠ P[k + 1]'hkP := fun he => by
          have := hPnd.getElem_inj_iff.mp he; omega
        have hkk1 : P[k]'hkP0 ≠ P[k + 1]'hkP := fun he => by
          have := hPnd.getElem_inj_iff.mp he; omega
        rcases hp0pair with h | h <;> rcases hkpair with h' | h' <;>
          rcases hk1pair with h'' | h''
        · exact h0k (h.trans h'.symm)
        · exact h0k (h.trans h'.symm)
        · exact h0k1 (h.trans h''.symm)
        · exact hkk1 (h'.trans h''.symm)
        · exact hkk1 (h'.trans h''.symm)
        · exact h0k1 (h.trans h''.symm)
        · exact h0k (h.trans h'.symm)
        · exact h0k (h.trans h'.symm)
    · have hEmpty : Eleft = ∅ := by
        ext k
        simp only [Eleft, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hk, hkY, hk1Y⟩, hkα⟩
        have hk0 : k = 0 := by omega
        subst k
        apply hq₂Y
        rw [← hp1]
        exact hk1Y
      rw [hEmpty, Set.ncard_empty]
      exact Even.zero
  by_cases hException :
      β = α + 1 ∧ VertexComplete G (P[α]'hαlt) Y ∧
        VertexComplete G (P[β]'hβlt) Y
  · exact zero_exception_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b halen hblen
      ha0 hab hbY fr hzero hW₂ex hException.2.1 hException.2.2
      (by simpa [α, β] using hException.1)
  have hcover : E = Eleft ∪ Eright := by
    ext k
    constructor
    · intro hk
      by_cases hkα : k < α
      · exact Or.inl ⟨hk, hkα⟩
      by_cases hβk : β ≤ k
      · exact Or.inr ⟨hk, hβk⟩
      exfalso
      rcases hk with ⟨hklen, hkY, hk1Y⟩
      have hkEq : k = α := by
        by_contra hne
        exact hαβnoY k (by omega) (by omega) (by omega) hkY
      have hstep : β = α + 1 := by
        by_contra hne
        have hk1lt : k + 1 < β := by omega
        exact hαβnoY (k + 1) hklen (by omega) hk1lt hk1Y
      apply hException
      refine ⟨hstep, ?_, ?_⟩
      · simpa only [gidx P hkEq (by omega) hαlt] using hkY
      · have he : k + 1 = β := by omega
        simpa only [gidx P he hklen hβlt] using hk1Y
    · rintro (hk | hk)
      · exact hk.1
      · exact hk.1
  have hdisj : Disjoint Eleft Eright := by
    rw [Set.disjoint_left]
    rintro k ⟨-, hkα⟩ ⟨-, hβk⟩
    omega
  have hEfinite : E.Finite :=
    Set.Finite.subset (Set.finite_Iio P.length) (by
      rintro k ⟨hk, -, -⟩
      exact (show k < P.length by omega))
  have hleftFinite : Eleft.Finite := hEfinite.subset (fun _ h => h.1)
  have hrightFinite : Eright.Finite := hEfinite.subset (fun _ h => h.1)
  have hcard : E.ncard = Eleft.ncard + Eright.ncard := by
    rw [hcover, Set.ncard_union_eq hdisj hleftFinite hrightFinite]
  have hoddE : Odd E.ncard := by
    have h184 := (_root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1).1.1
    change Odd (HoleYEdgeParity.yEdges G Y P).ncard at h184
    rw [Workspace.ProofLemmas.Thm183EdgeCount.yEdges_ncard_eq_index_ncard hP] at h184
    simpa [E] using h184
  have hoddRight : Odd Eright.ncard := by
    rw [Nat.odd_iff] at hoddE ⊢
    rw [Nat.even_iff] at hleftEven
    omega
  have hoddDropIdx : Odd
      (Workspace.ProofLemmas.Thm183EdgeCount.YEdgeIdx G Y (P.drop β)).ncard := by
    rw [yEdgeIdx_drop_ncard G Y P hβlt]
    simpa [E, Eright] using hoddRight
  have hoddSuffix : Odd (HoleYEdgeParity.yEdges G Y (P.drop β)).ncard := by
    rw [Workspace.ProofLemmas.Thm183EdgeCount.yEdges_ncard_eq_index_ncard
      (PathBasics.isPathList_drop hP hβlt)]
    exact hoddDropIdx
  have hNoF₂ : ∀ (j : ℕ) (hj : j < P.length), fr.β ≤ j →
      P[j]'hj ∉ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P} := by
    intro j hj hβj hatt
    have hj0 := hW₂range j hj (by simpa [Q] using hatt)
    omega
  exact suffix_path_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b halen ha0
    fr hNoF₂ (by simpa [β] using hoddSuffix)

/-- If `F \ {f₁}` has no attachment at all, optimality moves every `Y`-complete edge into
the suffix beginning at the last attachment of `F \ {f_k}`; `suffix_path_contra` then applies.
This is the empty-attachment case omitted from the corresponding sentence in the paper. -/
private theorem empty_F₂_contra (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (a b : ℕ) (halen : a < P.length) (hblen : b < P.length)
    (ha0 : 0 < a) (hab : a < b) (hbY : VertexComplete G (P[b]'hblen) Y)
    (fr : Frame G X Y P F a b halen)
    (hW₂none : ¬ ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P}) : False := by
  classical
  let Q : List V := fr.Q
  let α : ℕ := fr.α
  let β : ℕ := fr.β
  have hαlt : α < P.length := fr.hαlt
  have hβlt : β < P.length := fr.hβlt
  have hαβnoY : ∀ (j : ℕ) (hj : j < P.length), α < j → j < β →
      ¬ VertexComplete G (P[j]'hj) Y := by
    simpa [α, β] using fr.hαβnoY
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have h1lt : 1 < P.length := by omega
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hF₂after : ∀ (j : ℕ) (hj : j < P.length),
      P[j]'hj ∈ attachments G {z : V | z ∈ Q.drop 2} {z : V | z ∈ P} → b ≤ j := by
    intro j hj hatt
    exact (hW₂none ⟨j, hj, by simpa [Q] using hatt⟩).elim
  obtain ⟨hαf1, hleftY⟩ := left_clear G X Y P p₁ pₙ hopt hhead hlast F hmin
    a b halen hblen ha0 hab hbY fr (by simpa [Q] using hF₂after)
  have hleftY' : ∀ (j : ℕ) (hj : j < P.length), 0 < j → j ≤ α →
      ¬ VertexComplete G (P[j]'hj) Y := by
    simpa [α] using hleftY
  have hYloc : ∀ (j : ℕ) (hj : j < P.length),
      VertexComplete G (P[j]'hj) Y → j = 0 ∨ β ≤ j := by
    intro j hj hjY
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    right
    by_contra hjβ
    rcases le_or_gt j α with hjα | hαj
    · exact hleftY' j hj (by omega) hjα hjY
    · exact hαβnoY j hj hαj (by omega) hjY
  have hmemDrop : ∀ (j : ℕ) (hj : j < P.length), β ≤ j → P[j]'hj ∈ P.drop β := by
    intro j hj hβj
    have hi : j - β < (P.drop β).length := by simp; omega
    have he : (P.drop β)[j - β]'hi = P[j]'hj := by
      simp only [List.getElem_drop]
      exact gidx P (by omega) (by omega) hj
    rw [← he]
    exact List.getElem_mem hi
  have hyeq : HoleYEdgeParity.yEdges G Y P =
      HoleYEdgeParity.yEdges G Y (P.drop β) := by
    have hinto : ∀ (i : ℕ) (hi : i < P.length), VertexComplete G (P[i]'hi) Y →
        ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[i]'hi) (P[j]'hj) →
          VertexComplete G (P[j]'hj) Y → P[i]'hi ∈ P.drop β := by
      intro i hi hiY j hj hij hjY
      rcases hYloc i hi hiY with hi0 | hβi
      · subst hi0
        have hidx := (PathBasics.path_adj_iff hP hi hj).mp hij
        have hj1 : j = 1 := by omega
        subst hj1
        exact absurd hjY (by rw [hp1]; exact hq₂Y)
      · exact hmemDrop i hi hβi
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      exact ⟨_, hinto i hi huY j hj huv hvY, _, hinto j hj hvY i hi huv.symm huY,
        rfl, huv, huY, hvY⟩
    · rintro ⟨u, hu, v, hv, rfl, huv, huY, hvY⟩
      exact ⟨u, List.mem_of_mem_drop hu, v, List.mem_of_mem_drop hv, rfl, huv, huY, hvY⟩
  have hoddSuffix : Odd (HoleYEdgeParity.yEdges G Y (P.drop β)).ncard := by
    rw [← hyeq]
    exact (_root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1).1.1
  have hNoF₂ : ∀ (j : ℕ) (hj : j < P.length), fr.β ≤ j →
      P[j]'hj ∉ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P} := by
    intro j hj hβj hatt
    exact hW₂none ⟨j, hj, hatt⟩
  exact suffix_path_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b halen ha0
    fr hNoF₂ (by simpa [β] using hoddSuffix)

/-- **18.6, claim (2)**: *"There do not exist `a, b` with `1 < a < b ≤ n` such that `p_a` is an
attachment of `F` and `p_b` is `Y`-complete."* -/
theorem claim2 (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F) :
    ¬ ∃ (a b : ℕ) (ha : a < P.length) (hb : b < P.length),
        0 < a ∧ a < b ∧ (P[a]'ha) ∈ attachments G F {w : V | w ∈ P} ∧
        VertexComplete G (P[b]'hb) Y := by
  classical
  rintro ⟨a, b, halen, hblen, ha0, hab, haatt, hbY⟩
  obtain ⟨fr, -⟩ := exists_frame G hG X Y P p₁ pₙ hopt hhead hlast F hmin
    a b halen hblen ha0 hab haatt hbY
  by_cases hW₂ex : ∃ j, ∃ hj : j < P.length,
      P[j]'hj ∈ attachments G {z : V | z ∈ fr.Q.drop 2} {z : V | z ∈ P}
  · rcases fr.hP₂ends with hzero | hlast₂
    · exact zero_nonempty_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b
        halen hblen ha0 hab hbY fr hzero hW₂ex
    · exact last_nonempty_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b
        halen hblen ha0 hab hbY fr hlast₂ hW₂ex
  · exact empty_F₂_contra G hG X Y P p₁ pₙ hopt hhead hlast F hmin a b halen
      hblen ha0 hab hbY fr hW₂ex

#print axioms leap_common_neighbor_contra
#print axioms two_caps_contra
#print axioms exists_frame
#print axioms zero_exception_contra
#print axioms left_clear
#print axioms last_nonempty_contra
#print axioms suffix_path_contra
#print axioms zero_nonempty_contra
#print axioms empty_F₂_contra
#print axioms claim2

end Workspace.ProofLemmas.Thm186Claim2
