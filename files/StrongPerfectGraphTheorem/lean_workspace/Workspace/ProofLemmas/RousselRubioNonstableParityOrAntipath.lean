import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.RousselRubioParityBase

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace RRNonstableAux


open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*}

/-- **First exit from a deleted vertex.**  If `a` and `b` are reachable inside `S` and both
differ from `u`, then either they are reachable inside `S \ {u}`, or `a` reaches (inside
`S \ {u}`) a vertex `w` adjacent to `u`. -/
private theorem exists_exit {K : SimpleGraph V} {S : Set V} {u : V} :
    ∀ (a b : ↥S) (W : (K.induce S).Walk a b) (hau : (a : V) ≠ u) (hbu : (b : V) ≠ u),
      (K.induce (S \ {u})).Reachable ⟨(a : V), ⟨a.2, hau⟩⟩ ⟨(b : V), ⟨b.2, hbu⟩⟩ ∨
      ∃ w : V, ∃ hw : w ∈ S \ {u}, K.Adj w u ∧
        (K.induce (S \ {u})).Reachable ⟨(a : V), ⟨a.2, hau⟩⟩ ⟨w, hw⟩ := by
  intro a b W
  induction W with
  | nil =>
      intro hau hbu
      left
      exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih =>
      intro hau hbu
      by_cases hyu : (y : V) = u
      · right
        refine ⟨(x : V), ⟨x.2, hau⟩, ?_, SimpleGraph.Reachable.refl _⟩
        have : K.Adj (x : V) (y : V) := hxy
        rw [hyu] at this
        exact this
      · rcases ih hyu hbu with h | ⟨w, hw, hwu, hreach⟩
        · left
          refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) h
          show K.Adj (x : V) (y : V)
          exact hxy
        · right
          refine ⟨w, hw, hwu, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hreach⟩
          show K.Adj (x : V) (y : V)
          exact hxy

/-! ### Reachability inside a vertex set, packaged without subtype proofs -/

/-- `x` reaches `y` inside `S`. -/
private def ReachIn (K : SimpleGraph V) (S : Set V) (x y : V) : Prop :=
  ∃ (hx : x ∈ S) (hy : y ∈ S), (K.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem reachIn_refl {K : SimpleGraph V} {S : Set V} {x : V} (hx : x ∈ S) :
    ReachIn K S x x := ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

private theorem reachIn_trans {K : SimpleGraph V} {S : Set V} {x y z : V}
    (h₁ : ReachIn K S x y) (h₂ : ReachIn K S y z) : ReachIn K S x z := by
  obtain ⟨hx, hy, h₁⟩ := h₁
  obtain ⟨hy', hz, h₂⟩ := h₂
  exact ⟨hx, hz, h₁.trans h₂⟩

private theorem reachIn_symm {K : SimpleGraph V} {S : Set V} {x y : V}
    (h : ReachIn K S x y) : ReachIn K S y x := by
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hy, hx, h.symm⟩

private theorem reachIn_of_adj {K : SimpleGraph V} {S : Set V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (h : K.Adj x y) : ReachIn K S x y :=
  ⟨hx, hy, SimpleGraph.Adj.reachable h⟩

private theorem reachIn_of_preconnected {K : SimpleGraph V} {S : Set V}
    (h : (K.induce S).Preconnected) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ReachIn K S x y := ⟨hx, hy, h ⟨x, hx⟩ ⟨y, hy⟩⟩

private theorem preconnected_of_reachIn {K : SimpleGraph V} {S : Set V}
    (h : ∀ x ∈ S, ∀ y ∈ S, ReachIn K S x y) : (K.induce S).Preconnected := by
  intro a b
  obtain ⟨ha, hb, hr⟩ := h (a : V) a.2 (b : V) b.2
  exact hr

private theorem exists_exit' {K : SimpleGraph V} {S : Set V} {u : V} {a b : V}
    (hau : a ≠ u) (hbu : b ≠ u) (h : ReachIn K S a b) :
    ReachIn K (S \ {u}) a b ∨
      ∃ w : V, w ∈ S ∧ w ≠ u ∧ K.Adj w u ∧ ReachIn K (S \ {u}) a w := by
  obtain ⟨ha, hb, hr⟩ := h
  rcases exists_exit ⟨a, ha⟩ ⟨b, hb⟩ hr.some hau hbu with h | ⟨w, hw, hwu, hreach⟩
  · exact Or.inl ⟨⟨ha, hau⟩, ⟨hb, hbu⟩, h⟩
  · exact Or.inr ⟨w, hw.1, hw.2, hwu, ⟨⟨ha, hau⟩, hw, hreach⟩⟩

/-! ### Longest antipaths inside `T` -/

/-- The plan's "longest antipath inside `T`". -/
private def LongestAntipathIn (G : SimpleGraph V) (T : Set V) (Q : List V) (u v : V) : Prop :=
  IsAntipathFrom G Q u v ∧ (∀ x ∈ Q, x ∈ T) ∧
    ∀ (R : List V) (c d : V), IsAntipathFrom G R c d → (∀ x ∈ R, x ∈ T) →
      pathLength R ≤ pathLength Q

private theorem exists_longest_antipath [Fintype V] (G : SimpleGraph V) (T : Set V)
    (hT : T.Nonempty) : ∃ (Q : List V) (u v : V), LongestAntipathIn G T Q u v := by
  classical
  set Lset : Set ℕ :=
    {n | ∃ (R : List V) (c d : V), IsAntipathFrom G R c d ∧ (∀ x ∈ R, x ∈ T) ∧
      pathLength R = n} with hLdef
  obtain ⟨t, ht⟩ := hT
  have hne : Lset.Nonempty := by
    refine ⟨0, [t], t, t, ?_, ?_, rfl⟩
    · exact ⟨PathBasics.isPathList_singleton Gᶜ t, rfl, rfl⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ ht
  have hbdd : BddAbove Lset := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨R, c, d, hR, hRT, rfl⟩
    have hnd : R.Nodup := PathBasics.path_nodup hR.1
    have := hnd.length_le_card
    simp only [pathLength]
    omega
  obtain ⟨Q, u, v, hQ, hQT, hQlen⟩ := Nat.sSup_mem hne hbdd
  refine ⟨Q, u, v, hQ, hQT, ?_⟩
  intro R c d hR hRT
  rw [hQlen]
  exact le_csSup hbdd ⟨R, c, d, hR, hRT, rfl⟩

/-- A walk inside `S` starting in a set `C` that is closed under `S`-neighbours stays in `C`. -/
private theorem reach_closed {K : SimpleGraph V} {S C : Set V}
    (hclosed : ∀ x ∈ C, ∀ y ∈ S, K.Adj x y → y ∈ C) :
    ∀ (a b : ↥S) (W : (K.induce S).Walk a b) (ha : (a : V) ∈ C),
      ∃ hb : (b : V) ∈ C, (K.induce C).Reachable ⟨(a : V), ha⟩ ⟨(b : V), hb⟩ := by
  intro a b W
  induction W with
  | nil => intro ha; exact ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons x y z hxy p ih =>
      intro ha
      have hyC : (y : V) ∈ C := hclosed _ ha _ y.2 hxy
      obtain ⟨hb, hr⟩ := ih hyC
      refine ⟨hb, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hr⟩
      show K.Adj (x : V) (y : V)
      exact hxy

private theorem reachIn_closed {K : SimpleGraph V} {S C : Set V}
    (hclosed : ∀ x ∈ C, ∀ y ∈ S, K.Adj x y → y ∈ C) {x y : V} (hx : x ∈ C)
    (h : ReachIn K S x y) : ReachIn K C x y := by
  obtain ⟨hxS, hyS, hr⟩ := h
  obtain ⟨hyC, hrC⟩ := reach_closed hclosed ⟨x, hxS⟩ ⟨y, hyS⟩ hr.some hx
  exact ⟨hx, hyC, hrC⟩

/-! ### Step 5.1: deleting the first end of a longest antipath -/

private theorem endpoint_deletion_anticonnected [Fintype V] {G : SimpleGraph V} {T : Set V}
    (hT : AnticonnectedSet G T) {Q : List V} {u v : V}
    (hQ : LongestAntipathIn G T Q u v) (hk : 2 ≤ pathLength Q) :
    AnticonnectedSet G (T \ {u}) := by
  classical
  obtain ⟨hQp, hQT, hQmax⟩ := hQ
  have hnd : Q.Nodup := PathBasics.path_nodup hQp.1
  have hpos : 0 < Q.length := PathBasics.path_length_pos hQp.1
  have hlen : 3 ≤ Q.length := by
    have := PathBasics.pathLength_eq Q
    omega
  have hu0 : Q[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hQp.2.1 hpos
  have hmemT : ∀ (i : ℕ) (hi : i < Q.length), (Q[i]'hi) ∈ T := fun i hi =>
    hQT _ (List.getElem_mem hi)
  have hneu : ∀ (i : ℕ) (hi : i < Q.length), i ≠ 0 → (Q[i]'hi) ≠ u := by
    intro i hi hi0 he
    exact hi0 (hnd.getElem_inj_iff.mp (he.trans hu0.symm))
  set q1 : V := Q[1]'(by omega) with hq1def
  have hq1T : q1 ∈ T := hmemT 1 (by omega)
  have hq1u : q1 ≠ u := hneu 1 (by omega) (by omega)
  have hq1mem : q1 ∈ T \ {u} := ⟨hq1T, hq1u⟩
  -- reachability along `Q` from `q1` forwards, avoiding `u`
  have chain : ∀ (i : ℕ) (hi : i + 1 < Q.length),
      ReachIn Gᶜ (T \ {u}) q1 (Q[i + 1]'hi) := by
    intro i
    induction i with
    | zero => intro hi; exact reachIn_refl hq1mem
    | succ n ih =>
        intro hi
        have hn : n + 1 < Q.length := by omega
        refine reachIn_trans (ih hn) (reachIn_of_adj ?_ ?_ ?_)
        · exact ⟨hmemT _ hn, hneu _ hn (by omega)⟩
        · exact ⟨hmemT _ hi, hneu _ hi (by omega)⟩
        · exact PathBasics.path_adj_succ hQp.1 hi
  -- every vertex of `T` other than `u` reaches `q1` avoiding `u`
  have main : ∀ a ∈ T, a ≠ u → ReachIn Gᶜ (T \ {u}) a q1 := by
    intro a haT hau
    by_contra hcon
    have hreachT : ReachIn Gᶜ T a q1 := reachIn_of_preconnected hT haT hq1T
    rcases exists_exit' hau hq1u hreachT with h | ⟨w, hwT, hwu, hwadj, hwreach⟩
    · exact hcon h
    have hwmem : w ∈ T \ {u} := ⟨hwT, hwu⟩
    have hforbid : ∀ (i : ℕ) (hi : i < Q.length), i ≠ 0 → ¬ Gᶜ.Adj w (Q[i]'hi) := by
      intro i hi hi0 hadj
      obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
      have hx : ReachIn Gᶜ (T \ {u}) w (Q[n + 1]'hi) :=
        reachIn_of_adj hwmem ⟨hmemT _ hi, hneu _ hi (by omega)⟩ hadj
      exact hcon (reachIn_trans hwreach (reachIn_trans hx (reachIn_symm (chain n hi))))
    have hwnotQ : w ∉ Q := by
      intro hmem
      obtain ⟨i, hi, hie⟩ : ∃ (i : ℕ) (hi : i < Q.length), Q[i]'hi = w := by
        obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
        exact ⟨i, hi, hie⟩
      by_cases hi0 : i = 0
      · subst hi0
        exact hwu (hie ▸ hu0)
      · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
        exact hcon (reachIn_trans hwreach (reachIn_symm (hie ▸ chain n hi)))
    have hother : ∀ x ∈ Q, x ≠ u → ¬ Gᶜ.Adj w x := by
      intro x hx hxu
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hx
      subst hie
      exact hforbid i hi (by
        intro h0
        subst h0
        exact hxu hu0)
    have hnew : IsPathFrom Gᶜ (w :: Q) w v :=
      PathAttach.isPathFrom_cons hQp hwadj hwnotQ hother
    have hnewT : ∀ x ∈ (w :: Q), x ∈ T := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hwT
      · exact hQT x h
    have hle := hQmax (w :: Q) w v hnew hnewT
    rw [PathBasics.pathLength_cons] at hle
    have := PathBasics.pathLength_eq Q
    omega
  refine preconnected_of_reachIn ?_
  intro x hx y hy
  exact reachIn_trans (main x hx.1 hx.2) (reachIn_symm (main y hy.1 hy.2))

/-! ### Step 5.5: deleting both ends of a longest odd antipath -/

private theorem reverse_longest [Fintype V] {G : SimpleGraph V} {T : Set V} {Q : List V}
    {u v : V} (hQ : LongestAntipathIn G T Q u v) :
    LongestAntipathIn G T Q.reverse v u := by
  obtain ⟨hQp, hQT, hQmax⟩ := hQ
  refine ⟨PathBasics.isAntipathFrom_reverse hQp, ?_, ?_⟩
  · intro x hx
    exact hQT x (List.mem_reverse.mp hx)
  · intro R c d hR hRT
    rw [PathBasics.pathLength_reverse]
    exact hQmax R c d hR hRT

private theorem both_ends_deletion_anticonnected [Fintype V] {G : SimpleGraph V}
    (hG : Berge G) {T : Set V} (hT : AnticonnectedSet G T) {Q : List V} {u v : V}
    (hQ : LongestAntipathIn G T Q u v) (hodd : Odd (pathLength Q))
    (hk3 : 3 ≤ pathLength Q) :
    AnticonnectedSet G (T \ {u, v}) := by
  classical
  have hQ' := hQ
  obtain ⟨hQp, hQT, hQmax⟩ := hQ
  have hnd : Q.Nodup := PathBasics.path_nodup hQp.1
  have hpos : 0 < Q.length := PathBasics.path_length_pos hQp.1
  have hQlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  have hlen4 : 4 ≤ Q.length := by omega
  have hu0 : Q[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hQp.2.1 hpos
  have hvl : Q[Q.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hQp.2.2 hpos
  have hmemT : ∀ (i : ℕ) (hi : i < Q.length), (Q[i]'hi) ∈ T := fun i hi =>
    hQT _ (List.getElem_mem hi)
  have hneu : ∀ (i : ℕ) (hi : i < Q.length), i ≠ 0 → (Q[i]'hi) ≠ u := by
    intro i hi hi0 he
    exact hi0 (hnd.getElem_inj_iff.mp (he.trans hu0.symm))
  have hnev : ∀ (i : ℕ) (hi : i < Q.length), i ≠ Q.length - 1 → (Q[i]'hi) ≠ v := by
    intro i hi hi0 he
    exact hi0 (hnd.getElem_inj_iff.mp (he.trans hvl.symm))
  set W : Set V := T \ {u, v} with hWdef
  have hWsub : W ⊆ T := fun x hx => hx.1
  have huW : u ∉ W := fun h => h.2 (Or.inl rfl)
  have hvW : v ∉ W := fun h => h.2 (Or.inr rfl)
  -- interior vertices of `Q` live in `W`
  have hintW : ∀ (i : ℕ) (hi : i < Q.length), 1 ≤ i → i + 1 < Q.length →
      (Q[i]'hi) ∈ W := by
    intro i hi h1 h2
    exact ⟨hmemT i hi, by
      rintro (h | h)
      · exact hneu i hi (by omega) h
      · exact hnev i hi (by omega) h⟩
  set q1 : V := Q[1]'(by omega) with hq1def
  have hq1W : q1 ∈ W := hintW 1 (by omega) le_rfl (by omega)
  have hq1u : q1 ≠ u := hneu 1 (by omega) (by omega)
  have hq1v : q1 ≠ v := hnev 1 (by omega) (by omega)
  -- reachability along the interior of `Q`, avoiding both ends
  have chainW : ∀ (n : ℕ) (hn : n + 1 + 1 < Q.length),
      ReachIn Gᶜ W q1 (Q[n + 1]'(by omega)) := by
    intro n
    induction n with
    | zero => intro hn; exact reachIn_refl hq1W
    | succ m ih =>
        intro hn
        refine reachIn_trans (ih (by omega)) (reachIn_of_adj ?_ ?_ ?_)
        · exact hintW (m + 1) (by omega) (by omega) (by omega)
        · exact hintW (m + 2) (by omega) (by omega) (by omega)
        · exact PathBasics.path_adj_succ hQp.1 (show m + 1 + 1 < Q.length by omega)
  have hintReach : ∀ x ∈ SPGT.interior Q, ReachIn Gᶜ W q1 x := by
    intro x hx
    obtain ⟨n, hn, h1, h2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQp.1 hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := chainW m (by omega)
    rwa [he] at this
  have hintMemW : ∀ x ∈ SPGT.interior Q, x ∈ W := by
    intro x hx
    obtain ⟨n, hn, h1, h2, he⟩ := PathBasics.exists_getElem_of_mem_interior hQp.1 hx
    exact he ▸ hintW n hn h1 (by omega)
  -- the two one-end deletions
  have hTu : AnticonnectedSet G (T \ {u}) := endpoint_deletion_anticonnected hT hQ' (by omega)
  have hTv : AnticonnectedSet G (T \ {v}) :=
    endpoint_deletion_anticonnected hT (reverse_longest hQ')
      (by rw [PathBasics.pathLength_reverse]; omega)
  have hWeqU : (T \ {u}) \ {v} = W := by
    ext x; simp only [hWdef, Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  have hWeqV : (T \ {v}) \ {u} = W := by
    ext x; simp only [hWdef, Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  by_contra hcon
  have hex : ∃ a ∈ W, ¬ ReachIn Gᶜ W a q1 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hcon (preconnected_of_reachIn (fun x hx y hy =>
      reachIn_trans (hall x hx) (reachIn_symm (hall y hy))))
  obtain ⟨a, haW, hane⟩ := hex
  set C : Set V := {x | x ∈ W ∧ ReachIn Gᶜ W x a} with hCdef
  have hCW : C ⊆ W := fun x hx => hx.1
  have hCclosed : ∀ x ∈ C, ∀ y ∈ W, Gᶜ.Adj x y → y ∈ C := by
    intro x hx y hy hadj
    exact ⟨hy, reachIn_trans (reachIn_of_adj hy hx.1 hadj.symm) hx.2⟩
  have haC : a ∈ C := ⟨haW, reachIn_refl haW⟩
  have hCconn : ConnectedSet Gᶜ C := by
    refine preconnected_of_reachIn ?_
    intro x hx y hy
    refine reachIn_closed hCclosed hx ?_
    exact reachIn_trans hx.2 (reachIn_symm hy.2)
  have hintQnotC : ∀ x ∈ SPGT.interior Q, x ∉ C := by
    intro x hx hxC
    exact hane (reachIn_symm (reachIn_trans (hintReach x hx) hxC.2))
  have huC : u ∉ C := fun h => huW (hCW h)
  have hvC : v ∉ C := fun h => hvW (hCW h)
  -- `C` has a neighbour of `u` and a neighbour of `v` in `Gᶜ`
  have hu_nbr : ∃ f ∈ C, Gᶜ.Adj u f := by
    have haTv : a ∈ T \ {v} := ⟨(hWsub haW), fun h => haW.2 (Or.inr h)⟩
    have hq1Tv : q1 ∈ T \ {v} := ⟨hWsub hq1W, hq1v⟩
    have hreach : ReachIn Gᶜ (T \ {v}) a q1 := reachIn_of_preconnected hTv haTv hq1Tv
    rcases exists_exit' (u := u) (fun h => haW.2 (Or.inl h)) hq1u hreach with h | ⟨w, hwT, hwu, hwadj, hwreach⟩
    · rw [hWeqV] at h; exact absurd h hane
    · rw [hWeqV] at hwreach
      refine ⟨w, ⟨?_, reachIn_symm hwreach⟩, hwadj.symm⟩
      obtain ⟨_, hy, _⟩ := hwreach
      exact hy
  have hv_nbr : ∃ f ∈ C, Gᶜ.Adj v f := by
    have haTu : a ∈ T \ {u} := ⟨(hWsub haW), fun h => haW.2 (Or.inl h)⟩
    have hq1Tu : q1 ∈ T \ {u} := ⟨hWsub hq1W, hq1u⟩
    have hreach : ReachIn Gᶜ (T \ {u}) a q1 := reachIn_of_preconnected hTu haTu hq1Tu
    rcases exists_exit' (u := v) (fun h => haW.2 (Or.inr h)) hq1v hreach with h | ⟨w, hwT, hwu, hwadj, hwreach⟩
    · rw [hWeqU] at h; exact absurd h hane
    · rw [hWeqU] at hwreach
      refine ⟨w, ⟨?_, reachIn_symm hwreach⟩, hwadj.symm⟩
      obtain ⟨_, hy, _⟩ := hwreach
      exact hy
  -- the second path from `u` to `v`, with interior in `C`
  have huv : u ≠ v := PathBasics.isPathFrom_ends_ne hQp (by omega)
  have huvnadj : ¬ Gᶜ.Adj u v := by
    have := PathBasics.path_ends_not_adj hQp.1 (by omega)
    rwa [hu0, hvl] at this
  obtain ⟨R, hR, hRint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in (G := Gᶜ) hCconn huC hvC hu_nbr hv_nbr
  have hR3 : 3 ≤ R.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hR huv huvnadj
  have hdisj : ∀ x ∈ SPGT.interior Q, x ∉ SPGT.interior R := by
    intro x hx hxR
    exact hintQnotC x hx (hRint x hxR)
  have hanti : ∀ x ∈ SPGT.interior Q, ∀ y ∈ SPGT.interior R, ¬ Gᶜ.Adj x y := by
    intro x hx y hy hadj
    exact hintQnotC x hx (hCclosed y (hRint y hy) x (hintMemW x hx) hadj.symm)
  obtain ⟨hhole, hholelen⟩ :=
    TwoPathsHole.odd_hole_of_two_paths (G := Gᶜ) hQp hR (by omega) hR3 hdisj hanti
  set c : List V := Q ++ (SPGT.interior R).reverse with hcdef
  have hclen : c.length = pathLength Q + pathLength R := hholelen
  have hRlen : pathLength R = R.length - 1 := rfl
  have hRge : 2 ≤ pathLength R := by rw [hRlen]; omega
  have hcT : ∀ x ∈ c, x ∈ T := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hQT x h
    · exact hWsub (hCW (hRint x (List.mem_reverse.mp h)))
  rcases Nat.even_or_odd (pathLength Q + pathLength R) with hev | hoddsum
  · -- even total length: delete a vertex and contradict maximality of `Q`
    have hRodd : Odd (pathLength R) := by
      rcases hodd with ⟨t, ht⟩
      rcases Nat.even_or_odd (pathLength R) with h | h
      · exfalso
        obtain ⟨t2, ht2⟩ := h
        obtain ⟨t3, ht3⟩ := hev
        omega
      · exact h
    have hR3' : 3 ≤ pathLength R := by
      obtain ⟨t, ht⟩ := hRodd
      omega
    have h5 : 5 ≤ c.length := by omega
    have htail := HoleMinusVertexPath.isPathFrom_tail hhole h5
    have htaillen := HoleMinusVertexPath.pathLength_tail hhole h5
    have hle := hQmax c.tail _ _ htail (by
      intro x hx
      exact hcT x (List.mem_of_mem_tail hx))
    omega
  · refine (Nat.not_even_iff_odd.mpr ?_) (hG.2 c hhole)
    rw [hholelen]
    exact hoddsum

/-! ### The positional complete-edge index set -/

/-- `I(G,S,P)` of the plan's shared notation. -/
private def EIdx (G : SimpleGraph V) (S : Set V) (P : List V) : Set ℕ :=
  {i | i + 1 < P.length ∧ ∃ a b : V, P[i]? = some a ∧ P[i + 1]? = some b ∧
    EdgeComplete G S a b}

private theorem EIdx_lt {G : SimpleGraph V} {S : Set V} {P : List V} {i : ℕ}
    (h : i ∈ EIdx G S P) : i + 1 < P.length := h.1

private theorem mem_EIdx_iff {G : SimpleGraph V} {S : Set V} {P : List V} {i : ℕ}
    (hP : IsPathList G P) (hi : i + 1 < P.length) :
    i ∈ EIdx G S P ↔
      (VertexComplete G (P[i]'(by omega)) S ∧ VertexComplete G (P[i + 1]'hi) S) := by
  constructor
  · rintro ⟨-, a, b, ha, hb, hab⟩
    rw [List.getElem?_eq_getElem (show i < P.length by omega)] at ha
    rw [List.getElem?_eq_getElem hi] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    exact ⟨hab.2.1, hab.2.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hi, _, _, ?_, ?_, ?_, h1, h2⟩
    · exact List.getElem?_eq_getElem (show i < P.length by omega)
    · exact List.getElem?_eq_getElem hi
    · exact PathBasics.path_adj_succ hP hi

private theorem EIdx_mono {G : SimpleGraph V} {S S' : Set V} {P : List V}
    (h : S ⊆ S') : EIdx G S' P ⊆ EIdx G S P := by
  rintro i ⟨hi, a, b, ha, hb, hadj, h1, h2⟩
  exact ⟨hi, a, b, ha, hb, hadj, fun x hx => h1 x (h hx), fun x hx => h2 x (h hx)⟩

private theorem EIdx_finite {G : SimpleGraph V} {S : Set V} {P : List V} :
    (EIdx G S P).Finite :=
  Set.Finite.subset (Set.finite_Iio P.length) (fun i hi => by
    have := EIdx_lt hi; simp only [Set.mem_Iio]; omega)

/-! ### The four ambient-complement cycles used by Section 5 -/

section Cycles

variable {G : SimpleGraph V} {T : Set V} {Q : List V} {u v : V}

private theorem ends_mem (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T) :
    u ∈ T ∧ v ∈ T := by
  obtain ⟨hu, hv⟩ := PathBasics.isPathFrom_ends_mem hQp
  exact ⟨hQT u hu, hQT v hv⟩

private theorem interior_mem (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T)
    {x : V} (hx : x ∈ SPGT.interior Q) : x ∈ T ∧ x ≠ u ∧ x ≠ v := by
  obtain ⟨h1, h2, h3⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQp).mp hx
  exact ⟨hQT x h1, h2, h3⟩

/-- The cycle `a-u-q₁-⋯-q_{k-1}-v-b-a` of the ambient complement, of length `k+3`. -/
private theorem hole_aQb {a b : V}
    (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T) (hk : 1 ≤ pathLength Q)
    (haT : a ∉ T) (hbT : b ∉ T)
    (hau : ¬ G.Adj a u) (hbv : ¬ G.Adj b v)
    (haC : ∀ t ∈ T, t ≠ u → G.Adj a t) (hbC : ∀ t ∈ T, t ≠ v → G.Adj b t)
    (hab : ¬ G.Adj a b) (hne : a ≠ b) :
    IsHoleList Gᶜ (b :: a :: Q) ∧ holeLength (b :: a :: Q) = pathLength Q + 3 := by
  obtain ⟨huT, hvT⟩ := ends_mem hQp hQT
  have huv : u ≠ v := PathBasics.isPathFrom_ends_ne hQp hk
  have hanu : a ≠ u := fun h => haT (h ▸ huT)
  have hbnv : b ≠ v := fun h => hbT (h ▸ hvT)
  have hQlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  refine ⟨PrismBasics.isHoleList_of_path_add_two_vertices hQp hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · exact ⟨hanu, hau⟩
  · exact ⟨hbnv, hbv⟩
  · exact ⟨hne, hab⟩
  · exact fun h => haT (hQT a h)
  · exact fun h => hbT (hQT b h)
  · intro hcon
    exact hcon.2 (haC v hvT huv.symm)
  · intro hcon
    exact hcon.2 (hbC u huT huv)
  · intro x hx hcon
    obtain ⟨hxT, hxu, hxv⟩ := interior_mem hQp hQT hx
    exact hcon.2 (haC x hxT hxu)
  · intro x hx hcon
    obtain ⟨hxT, hxu, hxv⟩ := interior_mem hQp hQT hx
    exact hcon.2 (hbC x hxT hxv)
  · simp only [holeLength, List.length_cons]
    omega

/-- The antipath `a-u-q₁-⋯-q_{k-1}-v-b`, of length `k+2`. -/
private theorem path_aQb {a b : V}
    (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T) (hk : 1 ≤ pathLength Q)
    (haT : a ∉ T) (hbT : b ∉ T)
    (hau : ¬ G.Adj a u) (hbv : ¬ G.Adj b v)
    (haC : ∀ t ∈ T, t ≠ u → G.Adj a t) (hbC : ∀ t ∈ T, t ≠ v → G.Adj b t)
    (hab : G.Adj a b) :
    IsAntipathFrom G (a :: (Q ++ [b])) a b ∧
      SPGT.interior (a :: (Q ++ [b])) = Q ∧
      pathLength (a :: (Q ++ [b])) = pathLength Q + 2 := by
  obtain ⟨huT, hvT⟩ := ends_mem hQp hQT
  have huv : u ≠ v := PathBasics.isPathFrom_ends_ne hQp hk
  have hanu : a ≠ u := fun h => haT (h ▸ huT)
  have hbnv : b ≠ v := fun h => hbT (h ▸ hvT)
  have hQlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  have hmain : IsPathFrom Gᶜ (a :: (Q ++ [b])) a b := by
    refine PathAttach.isPathFrom_cons_concat hQp ⟨hanu, hau⟩ ⟨hbnv, hbv⟩ ?_ hab.ne
      (fun h => haT (hQT a h)) (fun h => hbT (hQT b h)) ?_ ?_
    · intro hcon
      exact hcon.2 hab
    · intro x hx hxu hcon
      exact hcon.2 (haC x (hQT x hx) hxu)
    · intro x hx hxv hcon
      exact hcon.2 (hbC x (hQT x hx) hxv)
  refine ⟨hmain, ?_, ?_⟩
  · simp [SPGT.interior]
  · simp only [pathLength, List.length_cons, List.length_append, List.length_nil]
    omega

/-- The cycle `w-u-q₁-⋯-q_{k-1}-v-w`, of length `k+2`. -/
private theorem hole_wQ {w : V}
    (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T) (hk : 2 ≤ pathLength Q)
    (hwT : w ∉ T) (hwu : ¬ G.Adj w u) (hwv : ¬ G.Adj w v)
    (hwC : ∀ t ∈ T, t ≠ u → t ≠ v → G.Adj w t) :
    IsHoleList Gᶜ (w :: Q) ∧ holeLength (w :: Q) = pathLength Q + 2 := by
  obtain ⟨huT, hvT⟩ := ends_mem hQp hQT
  have hQlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  refine ⟨PrismBasics.isHoleList_of_path_add_vertex hQp hk ?_ ?_ ?_ ?_, ?_⟩
  · exact ⟨fun h => hwT (h ▸ huT), hwu⟩
  · exact ⟨fun h => hwT (h ▸ hvT), hwv⟩
  · exact fun h => hwT (hQT w h)
  · intro x hx hcon
    obtain ⟨hxT, hxu, hxv⟩ := interior_mem hQp hQT hx
    exact hcon.2 (hwC x hxT hxu hxv)
  · simp only [holeLength, List.length_cons]
    omega

/-- The cycle `w-a-u-q₁-⋯-q_{k-1}-v-b-w`, of length `k+4`. -/
private theorem hole_w_aQb {a b w : V}
    (hpath : IsAntipathFrom G (a :: (Q ++ [b])) a b)
    (hint : SPGT.interior (a :: (Q ++ [b])) = Q)
    (hplen : pathLength (a :: (Q ++ [b])) = pathLength Q + 2)
    (hk : 0 < pathLength Q) (hQT : ∀ x ∈ Q, x ∈ T)
    (hwa : ¬ G.Adj w a) (hwb : ¬ G.Adj w b) (hwnea : w ≠ a) (hwneb : w ≠ b)
    (hwQ : w ∉ Q) (hwC : VertexComplete G w T) :
    IsHoleList Gᶜ (w :: (a :: (Q ++ [b]))) ∧
      holeLength (w :: (a :: (Q ++ [b]))) = pathLength Q + 4 := by
  have hQlen : Q.length = pathLength Q + 1 := by
    have := PathBasics.length_eq_pathLength_add_one hpath.1
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega
  refine ⟨PrismBasics.isHoleList_of_path_add_vertex hpath (by omega) ?_ ?_ ?_ ?_, ?_⟩
  · exact ⟨hwnea, hwa⟩
  · exact ⟨hwneb, hwb⟩
  · intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hwnea h
    · rcases List.mem_append.mp h with h' | h'
      · exact hwQ h'
      · exact hwneb (List.mem_singleton.mp h')
  · intro x hx hcon
    rw [hint] at hx
    exact hcon.2 (hwC x (hQT x hx))
  · simp only [holeLength, List.length_cons, List.length_append, List.length_nil]
    omega

/-- The cycle `w-a-u-q₁-⋯-q_{k-1}-v-b-z-w`, of length `k+5`. -/
private theorem hole_two_aQb {a b w z : V}
    (hpath : IsAntipathFrom G (a :: (Q ++ [b])) a b)
    (hint : SPGT.interior (a :: (Q ++ [b])) = Q)
    (hk : 0 < pathLength Q) (hQT : ∀ x ∈ Q, x ∈ T)
    (hwa : ¬ G.Adj w a) (hwnea : w ≠ a)
    (hzb : ¬ G.Adj z b) (hzneb : z ≠ b)
    (hwz : ¬ G.Adj w z) (hwnez : w ≠ z)
    (hwb : G.Adj w b) (hza : G.Adj z a)
    (hwQ : w ∉ Q) (hzQ : z ∉ Q)
    (hwC : VertexComplete G w T) (hzC : VertexComplete G z T) :
    IsHoleList Gᶜ (z :: w :: (a :: (Q ++ [b]))) ∧
      holeLength (z :: w :: (a :: (Q ++ [b]))) = pathLength Q + 5 := by
  have hQlen : Q.length = pathLength Q + 1 := by
    simp only [pathLength] at hk ⊢; omega
  have hcount : (a :: (Q ++ [b])).length = Q.length + 2 := by simp
  have hplen1 : 1 ≤ pathLength (a :: (Q ++ [b])) := by
    simp only [pathLength, hcount]; omega
  refine ⟨PrismBasics.isHoleList_of_path_add_two_vertices hpath hplen1
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · exact ⟨hwnea, hwa⟩
  · exact ⟨hzneb, hzb⟩
  · exact ⟨hwnez, hwz⟩
  · intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hwnea h
    · rcases List.mem_append.mp h with h' | h'
      · exact hwQ h'
      · exact hwb.ne (List.mem_singleton.mp h')
  · intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hza.ne h
    · rcases List.mem_append.mp h with h' | h'
      · exact hzQ h'
      · exact hzneb (List.mem_singleton.mp h')
  · intro hcon; exact hcon.2 hwb
  · intro hcon; exact hcon.2 hza
  · intro x hx hcon
    rw [hint] at hx
    exact hcon.2 (hwC x (hQT x hx))
  · intro x hx hcon
    rw [hint] at hx
    exact hcon.2 (hzC x (hQT x hx))
  · simp only [holeLength, List.length_cons, List.length_append, List.length_nil]
    omega

end Cycles

/-! ### Completeness bookkeeping -/

private theorem complete_of_adj {G : SimpleGraph V} {T : Set V} {w t : V}
    (hcomp : VertexComplete G w (T \ {t})) (hadj : G.Adj w t) : VertexComplete G w T := by
  intro x hx
  by_cases hxt : x = t
  · exact hxt ▸ hadj
  · exact hcomp x ⟨hx, hxt⟩

private theorem misses_of_not_complete {G : SimpleGraph V} {T : Set V} {w t : V}
    (hcomp : VertexComplete G w (T \ {t})) (hnot : ¬ VertexComplete G w T) : ¬ G.Adj w t :=
  fun h => hnot (complete_of_adj hcomp h)

private theorem complete_sdiff {G : SimpleGraph V} {T : Set V} {w t : V}
    (hcomp : VertexComplete G w (T \ {t})) : ∀ x ∈ T, x ≠ t → G.Adj w x :=
  fun x hx hxt => hcomp x ⟨hx, hxt⟩

private theorem complete_pair_sdiff {G : SimpleGraph V} {T : Set V} {w t₁ t₂ : V}
    (hcomp : VertexComplete G w (T \ {t₁, t₂})) :
    ∀ x ∈ T, x ≠ t₁ → x ≠ t₂ → G.Adj w x :=
  fun x hx h1 h2 => hcomp x ⟨hx, by simp [h1, h2]⟩

private theorem complete_of_pair {G : SimpleGraph V} {T : Set V} {w t₁ t₂ : V}
    (hcomp : VertexComplete G w (T \ {t₁, t₂})) (h : G.Adj w t₂) :
    ∀ x ∈ T, x ≠ t₁ → G.Adj w x := by
  intro x hx hx1
  by_cases hx2 : x = t₂
  · exact hx2 ▸ h
  · exact hcomp x ⟨hx, by simp [hx1, hx2]⟩

private theorem complete_of_pair' {G : SimpleGraph V} {T : Set V} {w t₁ t₂ : V}
    (hcomp : VertexComplete G w (T \ {t₁, t₂})) (h : G.Adj w t₁) :
    ∀ x ∈ T, x ≠ t₂ → G.Adj w x := by
  intro x hx hx2
  by_cases hx1 : x = t₁
  · exact hx1 ▸ h
  · exact hcomp x ⟨hx, by simp [hx1, hx2]⟩

private theorem vc_sdiff_of {G : SimpleGraph V} {T : Set V} {w t : V}
    (h : ∀ x ∈ T, x ≠ t → G.Adj w x) : VertexComplete G w (T \ {t}) :=
  fun x hx => h x hx.1 hx.2

/-- Step 5.6(1)/(3): a `T \ {u,v}`-complete vertex outside `T` cannot miss both ends of an
odd longest antipath. -/
private theorem claimC {G : SimpleGraph V} (hG : Berge G) {T : Set V} {Q : List V} {u v : V}
    (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T)
    (hk2 : 2 ≤ pathLength Q) (hkodd : Odd (pathLength Q))
    {w : V} (hwT : w ∉ T) (hwS : VertexComplete G w (T \ {u, v}))
    (hwu : ¬ G.Adj w u) (hwv : ¬ G.Adj w v) : False := by
  obtain ⟨hhole, hlen⟩ :=
    hole_wQ hQp hQT hk2 hwT hwu hwv (complete_pair_sdiff hwS)
  have heven := hG.2 _ hhole
  rw [hlen] at heven
  obtain ⟨t1, ht1⟩ := hkodd
  obtain ⟨t2, ht2⟩ := heven
  omega

/-! ### Step 5.3 and 5.4: the longest antipath has odd length -/

private theorem step54 {G : SimpleGraph V} (hG : Berge G) {T : Set V}
    {P : List V} {r s : V} (hP : IsPathFrom G P r s) (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoInt : ∀ z ∈ SPGT.interior P, ¬ VertexComplete G z T)
    {Q : List V} {u v : V} (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T)
    (hk2 : 2 ≤ pathLength Q) (hkeven : Even (pathLength Q))
    {i j : ℕ} (hiA : i ∈ EIdx G (T \ {u}) P) (hjB : j ∈ EIdx G (T \ {v}) P)
    (horder : i + 1 < j) : False := by
  have hPl : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  have hilt : i + 1 < P.length := EIdx_lt hiA
  have hjlt : j + 1 < P.length := EIdx_lt hjB
  obtain ⟨hca0, hca1⟩ := (mem_EIdx_iff hP.1 hilt).mp hiA
  obtain ⟨hcb0, hcb1⟩ := (mem_EIdx_iff hP.1 hjlt).mp hjB
  have huT : u ∈ T := (ends_mem hQp hQT).1
  have hvT : v ∈ T := (ends_mem hQp hQT).2
  -- the four selected path vertices
  have hb0 : i < P.length := by omega
  have hb1 : i + 1 < P.length := hilt
  have hb2 : j < P.length := by omega
  have hb3 : j + 1 < P.length := hjlt
  have hPnot : ∀ (l : ℕ) (hl : l < P.length), (P[l]'hl) ∉ T := fun l hl =>
    hPT _ (List.getElem_mem hl)
  have hPint : ∀ (l : ℕ) (hl : l < P.length), 1 ≤ l → l + 2 ≤ P.length →
      ¬ VertexComplete G (P[l]'hl) T := fun l hl h1 h2 =>
    hnoInt _ (PathBasics.getElem_mem_interior hP.1 hl h1 h2)
  have hgap : ∀ (l l' : ℕ) (hl : l < P.length) (hl' : l' < P.length),
      l + 1 ≠ l' → l' + 1 ≠ l → ¬ G.Adj (P[l]'hl) (P[l']'hl') := fun l l' hl hl' h1 h2 =>
    PathBasics.path_not_adj_of_gap hP.1 hl hl' h1 h2
  have hPne : ∀ (l l' : ℕ) (hl : l < P.length) (hl' : l' < P.length), l ≠ l' →
      (P[l]'hl) ≠ (P[l']'hl') := fun l l' hl hl' h =>
    PathBasics.path_ne_of_ne_index hP.1 hl hl' h
  -- the generic `k+3` odd-hole contradiction
  have kill : ∀ a b : V, a ∉ T → b ∉ T → ¬ G.Adj a u → ¬ G.Adj b v →
      (∀ t ∈ T, t ≠ u → G.Adj a t) → (∀ t ∈ T, t ≠ v → G.Adj b t) →
      ¬ G.Adj a b → a ≠ b → False := by
    intro a b haT hbT hau hbv haC hbC hab hne
    obtain ⟨hhole, hlen⟩ :=
      hole_aQb hQp hQT (by omega) haT hbT hau hbv haC hbC hab hne
    have heven := hG.2 _ hhole
    rw [hlen] at heven
    obtain ⟨t1, ht1⟩ := hkeven
    obtain ⟨t2, ht2⟩ := heven
    omega
  -- `P[i+1]` misses `u`, `P[j]` misses `v`
  have hmissA1 : ¬ G.Adj (P[i + 1]'hb1) u :=
    misses_of_not_complete hca1 (hPint (i + 1) hb1 (by omega) (by omega))
  have hmissB0 : ¬ G.Adj (P[j]'hb2) v :=
    misses_of_not_complete hcb0 (hPint j hb2 (by omega) (by omega))
  by_cases hadj : G.Adj (P[i + 1]'hb1) (P[j]'hb2)
  · -- consecutive, so `j = i + 2`
    have hji : j = i + 2 := by
      have := (PathBasics.path_adj_iff hP.1 hb1 hb2).mp hadj
      omega
    subst hji
    -- the left end of the first edge must be `p₀`
    have hi0 : i = 0 := by
      by_contra hi0
      have hmissA0 : ¬ G.Adj (P[i]'hb0) u :=
        misses_of_not_complete hca0 (hPint i hb0 (by omega) (by omega))
      exact kill (P[i]'hb0) (P[i + 2]'hb2) (hPnot _ hb0) (hPnot _ hb2) hmissA0 hmissB0
        (complete_sdiff hca0) (complete_sdiff hcb0)
        (hgap i (i + 2) hb0 hb2 (by omega) (by omega)) (hPne i (i + 2) hb0 hb2 (by omega))
    subst hi0
    -- the right end of the second edge must be `pₘ`
    have hjm : (2 : ℕ) + 1 + 1 = P.length := by
      by_contra hjm
      have hmissB1 : ¬ G.Adj (P[2 + 1]'hb3) v :=
        misses_of_not_complete hcb1 (hPint (2 + 1) hb3 (by omega) (by omega))
      exact kill (P[0 + 1]'hb1) (P[2 + 1]'hb3) (hPnot _ hb1) (hPnot _ hb3) hmissA1 hmissB1
        (complete_sdiff hca1) (complete_sdiff hcb1)
        (hgap (0 + 1) (2 + 1) hb1 hb3 (by omega) (by omega))
        (hPne (0 + 1) (2 + 1) hb1 hb3 (by omega))
    -- `P` has exactly four vertices; build the final `k+5` odd hole
    have hlen4 : P.length = 4 := by omega
    have hr0 : (P[0]'(by omega)) = r :=
      PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have hs3 : (P[3]'(by omega)) = s := by
      have := PathBasics.getElem_last_of_getLast? hP.2.2 (show 0 < P.length by omega)
      rw [← this]
      congr 1
      omega
    have hQrev : IsAntipathFrom G Q.reverse v u := PathBasics.isAntipathFrom_reverse hQp
    have hQrevT : ∀ x ∈ Q.reverse, x ∈ T := fun x hx => hQT x (List.mem_reverse.mp hx)
    have hrevlen : pathLength Q.reverse = pathLength Q := PathBasics.pathLength_reverse Q
    have hadj21 : G.Adj (P[2]'hb2) (P[0 + 1]'hb1) :=
      (PathBasics.path_adj_succ hP.1 (show 0 + 1 + 1 < P.length by omega)).symm
    obtain ⟨hpath, hint, hplen⟩ :=
      path_aQb hQrev hQrevT (by omega) (hPnot _ hb2) (hPnot _ hb1) hmissB0 hmissA1
        (complete_sdiff hcb0) (complete_sdiff hca1) hadj21
    obtain ⟨hhole, hlen⟩ :=
      hole_two_aQb (T := T) hpath hint (by omega) hQrevT
        (hgap 0 2 (by omega) hb2 (by omega) (by omega)) (hPne 0 2 (by omega) hb2 (by omega))
        (hgap 3 (0 + 1) (by omega) hb1 (by omega) (by omega))
        (hPne 3 (0 + 1) (by omega) hb1 (by omega))
        (hgap 0 3 (by omega) (by omega) (by omega) (by omega))
        (hPne 0 3 (by omega) (by omega) (by omega))
        (PathBasics.path_adj_succ hP.1 (show 0 + 1 < P.length by omega))
        ((PathBasics.path_adj_succ hP.1 (show 2 + 1 < P.length by omega)).symm)
        (fun h => hPnot 0 (by omega) (hQrevT _ h))
        (fun h => hPnot 3 (by omega) (hQrevT _ h))
        (by rw [hr0]; exact hr) (by rw [hs3]; exact hs)
    have heven := hG.2 _ hhole
    rw [hlen, hrevlen] at heven
    obtain ⟨t1, ht1⟩ := hkeven
    obtain ⟨t2, ht2⟩ := heven
    omega
  · exact kill (P[i + 1]'hb1) (P[j]'hb2) (hPnot _ hb1) (hPnot _ hb2) hmissA1 hmissB0
      (complete_sdiff hca1) (complete_sdiff hcb0) hadj (hPne (i + 1) j hb1 hb2 (by omega))

/-! ### Steps 5.6 and 5.7: the third edge, its location, and the antipath -/

private theorem step57 {G : SimpleGraph V} (hG : Berge G) {T : Set V}
    {P : List V} {r s : V} (hP : IsPathFrom G P r s) (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    {Q : List V} {u v : V} (hQp : IsAntipathFrom G Q u v) (hQT : ∀ x ∈ Q, x ∈ T)
    (hk3 : 3 ≤ pathLength Q) (hkodd : Odd (pathLength Q))
    {l : ℕ} (hl : l ∈ EIdx G (T \ {u, v}) P)
    (hmissU : ¬ G.Adj (P[l]'(by have := EIdx_lt hl; omega)) u)
    (hmissV : ¬ G.Adj (P[l + 1]'(EIdx_lt hl)) v) :
    pathLength P = 3 ∧
      ∃ c d : V, SPGT.interior P = [c, d] ∧
        ∃ R : List V, IsAntipathFrom G R c d ∧ Odd (pathLength R) ∧
          ∀ w ∈ SPGT.interior R, w ∈ T := by
  have hPl : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  have hllt : l + 1 < P.length := EIdx_lt hl
  have hbl : l < P.length := by omega
  obtain ⟨hcA, hcB⟩ := (mem_EIdx_iff hP.1 hllt).mp hl
  have huT : u ∈ T := (ends_mem hQp hQT).1
  have hvT : v ∈ T := (ends_mem hQp hQT).2
  have hPnot : ∀ (n : ℕ) (hn : n < P.length), (P[n]'hn) ∉ T := fun n hn =>
    hPT _ (List.getElem_mem hn)
  have hgap : ∀ (n n' : ℕ) (hn : n < P.length) (hn' : n' < P.length),
      n + 1 ≠ n' → n' + 1 ≠ n → ¬ G.Adj (P[n]'hn) (P[n']'hn') := fun n n' hn hn' h1 h2 =>
    PathBasics.path_not_adj_of_gap hP.1 hn hn' h1 h2
  have hPne : ∀ (n n' : ℕ) (hn : n < P.length) (hn' : n' < P.length), n ≠ n' →
      (P[n]'hn) ≠ (P[n']'hn') := fun n n' hn hn' h =>
    PathBasics.path_ne_of_ne_index hP.1 hn hn' h
  have hr0 : (P[0]'(by omega)) = r :=
    PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hsl : (P[P.length - 1]'(by omega)) = s :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  -- Claim C: an `S`-complete vertex outside `T` cannot miss both ends of `Q`
  have claimC : ∀ w : V, w ∉ T → VertexComplete G w (T \ {u, v}) →
      ¬ G.Adj w u → ¬ G.Adj w v → False := by
    intro w hwT hwS hwu hwv
    obtain ⟨hhole, hlen⟩ :=
      hole_wQ hQp hQT (by omega) hwT hwu hwv (complete_pair_sdiff hwS)
    have heven := hG.2 _ hhole
    rw [hlen] at heven
    obtain ⟨t1, ht1⟩ := hkodd
    obtain ⟨t2, ht2⟩ := heven
    omega
  have hseeV : G.Adj (P[l]'hbl) v := by
    by_contra h
    exact claimC _ (hPnot _ hbl) hcA hmissU h
  have hseeU : G.Adj (P[l + 1]'hllt) u := by
    by_contra h
    exact claimC _ (hPnot _ hllt) hcB h hmissV
  have hcompA : ∀ t ∈ T, t ≠ u → G.Adj (P[l]'hbl) t := complete_of_pair hcA hseeV
  have hcompB : ∀ t ∈ T, t ≠ v → G.Adj (P[l + 1]'hllt) t := by
    intro t ht htv
    by_cases htu : t = u
    · exact htu ▸ hseeU
    · exact hcB t ⟨ht, by simp [htu, htv]⟩
  have hadjAB : G.Adj (P[l]'hbl) (P[l + 1]'hllt) := PathBasics.path_adj_succ hP.1 hllt
  have hQrev : IsAntipathFrom G Q.reverse v u := PathBasics.isAntipathFrom_reverse hQp
  have hQrevT : ∀ x ∈ Q.reverse, x ∈ T := fun x hx => hQT x (List.mem_reverse.mp hx)
  have hrevlen : pathLength Q.reverse = pathLength Q := PathBasics.pathLength_reverse Q
  -- the forward antipath `P[l] - u - ⋯ - v - P[l+1]`
  obtain ⟨hpathF, hintF, hplenF⟩ :=
    path_aQb hQp hQT (by omega) (hPnot _ hbl) (hPnot _ hllt) hmissU hmissV
      hcompA hcompB hadjAB
  -- (a) the third edge starts at `p₁`
  have hl1 : l = 1 := by
    by_contra hl1
    rcases Nat.lt_or_ge l 1 with hlt | hge
    · -- `l = 0`: then `P[0] = r` is `T`-complete, contradicting `hmissU`
      have : l = 0 := by omega
      subst this
      exact hmissU (by rw [hr0]; exact hr u huT)
    · have hl2 : 2 ≤ l := by omega
      obtain ⟨hhole, hlen⟩ :=
        hole_w_aQb (T := T) hpathF hintF hplenF (by omega) hQT
          (hgap 0 l (by omega) hbl (by omega) (by omega))
          (hgap 0 (l + 1) (by omega) hllt (by omega) (by omega))
          (hPne 0 l (by omega) hbl (by omega)) (hPne 0 (l + 1) (by omega) hllt (by omega))
          (fun h => hPnot 0 (by omega) (hQT _ h)) (by rw [hr0]; exact hr)
      have heven := hG.2 _ hhole
      rw [hlen] at heven
      obtain ⟨t1, ht1⟩ := hkodd
      obtain ⟨t2, ht2⟩ := heven
      omega
  -- (b) the third edge ends at `p_{m-1}`
  have hlm : l + 1 + 1 = P.length - 1 := by
    by_contra hlm
    rcases Nat.lt_or_ge (l + 1 + 1) (P.length - 1) with hlt | hge
    · -- the mirrored `k+4` hole through `pₘ`
      have hadjBA : G.Adj (P[l + 1]'hllt) (P[l]'hbl) := hadjAB.symm
      obtain ⟨hpathB, hintB, hplenB⟩ :=
        path_aQb hQrev hQrevT (by omega) (hPnot _ hllt) (hPnot _ hbl) hmissV hmissU
          hcompB hcompA hadjBA
      obtain ⟨hhole, hlen⟩ :=
        hole_w_aQb (T := T) hpathB hintB hplenB (by omega) hQrevT
          (hgap (P.length - 1) (l + 1) (by omega) hllt (by omega) (by omega))
          (hgap (P.length - 1) l (by omega) hbl (by omega) (by omega))
          (hPne (P.length - 1) (l + 1) (by omega) hllt (by omega))
          (hPne (P.length - 1) l (by omega) hbl (by omega))
          (fun h => hPnot (P.length - 1) (by omega) (hQrevT _ h))
          (by rw [hsl]; exact hs)
      have heven := hG.2 _ hhole
      rw [hlen, hrevlen] at heven
      obtain ⟨t1, ht1⟩ := hkodd
      obtain ⟨t2, ht2⟩ := heven
      omega
    · -- `l + 2 = P.length` forces `P[l+1] = s`, which is `T`-complete
      have : l + 1 = P.length - 1 := by omega
      refine hmissV ?_
      have hval : (P[l + 1]'hllt) = s := by rw [← hsl]; congr 1
      rw [hval]
      exact hs v hvT
  subst hl1
  have hlen4 : P.length = 4 := by omega
  have hm3 : pathLength P = 3 := by omega
  -- the interior of `P` is exactly the two internal vertices
  have hint2 : SPGT.interior P = [P[1]'(by omega), P[2]'(by omega)] := by
    have hlen : (SPGT.interior P).length = 2 := by
      rw [PathBasics.interior_length]; omega
    refine List.ext_getElem (by simp [hlen]) ?_
    intro n hn hn'
    rw [hlen] at hn
    have hstep : ∀ (t : ℕ) (ht : t < (SPGT.interior P).length),
        (SPGT.interior P)[t]'ht = P[t + 1]'(by rw [PathBasics.interior_length] at ht; omega) := by
      intro t ht
      show (P.tail.dropLast)[t]'ht = _
      rw [List.getElem_dropLast, List.getElem_tail]
    interval_cases n
    · rw [hstep 0 (by omega)]; simp
    · rw [hstep 1 (by omega)]; simp
  refine ⟨hm3, P[1]'(by omega), P[2]'(by omega), hint2,
    P[1]'(by omega) :: (Q ++ [P[1 + 1]'hllt]), ?_, ?_, ?_⟩
  · exact hpathF
  · rw [hplenF]
    obtain ⟨t1, ht1⟩ := hkodd
    exact ⟨t1 + 1, by omega⟩
  · rw [hintF]; exact hQT

/-! ### Assembly of the nonstable case -/

private theorem mainAux [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (T : Set V) (hTne : T.Nonempty) (hTanti : AnticonnectedSet G T)
    (hTnonstable : ¬ Set.Pairwise T (fun x y ↦ ¬ G.Adj x y))
    (P : List V) (r s : V) (hP : IsPathFrom G P r s)
    (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoInternalComplete : ∀ z ∈ SPGT.interior P, ¬ VertexComplete G z T)
    (hnoLeap : ¬ (
      Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b))
    (hproper : ∀ S : Set V, S ⊂ T → AnticonnectedSet G S →
      ((EIdx G S P).ncard % 2 = pathLength P % 2) ∨
      (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ S, ∃ b ∈ S, IsLeapForPath G P a b) ∨
      (pathLength P = 3 ∧
        ∃ c d : V, SPGT.interior P = [c, d] ∧
          ∃ R : List V, IsAntipathFrom G R c d ∧ Odd (pathLength R) ∧
            ∀ w ∈ SPGT.interior R, w ∈ S)) :
    ((EIdx G T P).ncard % 2 = pathLength P % 2) ∨
    (pathLength P = 3 ∧
      ∃ c d : V, SPGT.interior P = [c, d] ∧
        ∃ R : List V, IsAntipathFrom G R c d ∧ Odd (pathLength R) ∧
          ∀ w ∈ SPGT.interior R, w ∈ T) := by
  classical
  have hPl : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  by_cases hsmall : pathLength P ≤ 2
  · exact Or.inl (RousselRubioParityBase G T P r s hP hPT hr hs (Or.inr hsmall))
  have hm3 : 3 ≤ pathLength P := by omega
  obtain ⟨Q, u, v, hQlong⟩ := exists_longest_antipath G T hTne
  have hQp : IsAntipathFrom G Q u v := hQlong.1
  have hQT : ∀ x ∈ Q, x ∈ T := hQlong.2.1
  have hQmax := hQlong.2.2
  have huT : u ∈ T := (ends_mem hQp hQT).1
  have hvT : v ∈ T := (ends_mem hQp hQT).2
  -- `T` is not stable, so the longest antipath has length at least two
  have hk2 : 2 ≤ pathLength Q := by
    obtain ⟨x, hx, y, hy, hxy, hadj⟩ : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ G.Adj x y := by
      by_contra hcon
      refine hTnonstable ?_
      intro a ha b hb hab hadj
      exact hcon ⟨a, ha, b, hb, hab, hadj⟩
    obtain ⟨p, hp, hpmem⟩ :=
      InducedPathExtraction.exists_isPathFrom_of_connected (G := Gᶜ) hTanti hx hy
    have hnadj : ¬ Gᶜ.Adj x y := fun h => h.2 hadj
    have h3 : 3 ≤ p.length :=
      MinimalConnectedIsPath.three_le_length_of_not_adj hp hxy hnadj
    have hle := hQmax p x y hp hpmem
    have hpl := PathBasics.length_eq_pathLength_add_one hp.1
    omega
  have huv : u ≠ v := PathBasics.isPathFrom_ends_ne hQp (by omega)
  have hTu_ss : T \ {u} ⊂ T := ⟨Set.diff_subset, fun hcon => (hcon huT).2 rfl⟩
  have hTv_ss : T \ {v} ⊂ T := ⟨Set.diff_subset, fun hcon => (hcon hvT).2 rfl⟩
  have hTu_anti : AnticonnectedSet G (T \ {u}) :=
    endpoint_deletion_anticonnected hTanti hQlong hk2
  have hTv_anti : AnticonnectedSet G (T \ {v}) :=
    endpoint_deletion_anticonnected hTanti (reverse_longest hQlong)
      (by rw [PathBasics.pathLength_reverse]; exact hk2)
  -- every exceptional outcome on a proper subset is an outcome for `T`
  have lift : ∀ S : Set V, S ⊆ T → S ⊂ T → AnticonnectedSet G S →
      ((EIdx G S P).ncard % 2 = pathLength P % 2) ∨
      (pathLength P = 3 ∧
        ∃ c d : V, SPGT.interior P = [c, d] ∧
          ∃ R : List V, IsAntipathFrom G R c d ∧ Odd (pathLength R) ∧
            ∀ w ∈ SPGT.interior R, w ∈ T) := by
    intro S hsub hss hanti
    rcases hproper S hss hanti with h | h | h
    · exact Or.inl h
    · obtain ⟨h1, h2, a, ha, b, hb, hlp⟩ := h
      exact absurd ⟨h1, h2, a, hsub ha, b, hsub hb, hlp⟩ hnoLeap
    · obtain ⟨h1, c, d, hcd, R, hR, hRodd, hRint⟩ := h
      exact Or.inr ⟨h1, c, d, hcd, R, hR, hRodd, fun w hw => hsub (hRint w hw)⟩
  rcases lift (T \ {u}) Set.diff_subset hTu_ss hTu_anti with hAp | hright
  swap
  · exact Or.inr hright
  rcases lift (T \ {v}) Set.diff_subset hTv_ss hTv_anti with hBp | hright
  swap
  · exact Or.inr hright
  -- Step 5.2: the two families have disjoint vertex supports
  have hunion : ∀ w : V, VertexComplete G w (T \ {u}) → VertexComplete G w (T \ {v}) →
      VertexComplete G w T := by
    intro w h1 h2 t ht
    by_cases htu : t = u
    · exact h2 t ⟨ht, by simp only [Set.mem_singleton_iff, htu]; exact huv⟩
    · exact h1 t ⟨ht, htu⟩
  have hnotBoth : ∀ (n : ℕ) (hn : n < P.length), 1 ≤ n → n + 2 ≤ P.length →
      VertexComplete G (P[n]'hn) (T \ {u}) → VertexComplete G (P[n]'hn) (T \ {v}) →
      False := by
    intro n hn h1 h2 hc1 hc2
    exact hnoInternalComplete _ (PathBasics.getElem_mem_interior hP.1 hn h1 h2)
      (hunion _ hc1 hc2)
  have vcc : ∀ (n n' : ℕ) (hn : n < P.length) (hn' : n' < P.length) (S : Set V),
      n = n' → VertexComplete G (P[n]'hn) S → VertexComplete G (P[n']'hn') S := by
    intro n n' hn hn' S h hc
    subst h
    exact hc
  have hsep : ∀ i ∈ EIdx G (T \ {u}) P, ∀ j ∈ EIdx G (T \ {v}) P,
      i + 1 < j ∨ j + 1 < i := by
    intro i hi j hj
    have hilt : i + 1 < P.length := EIdx_lt hi
    have hjlt : j + 1 < P.length := EIdx_lt hj
    obtain ⟨hia, hib⟩ := (mem_EIdx_iff hP.1 hilt).mp hi
    obtain ⟨hja, hjb⟩ := (mem_EIdx_iff hP.1 hjlt).mp hj
    have hne1 : i ≠ j := by
      intro heq
      by_cases hi0 : i = 0
      · refine hnotBoth 1 (by omega) (by omega) (by omega) ?_ ?_
        · exact vcc (i + 1) 1 hilt (by omega) _ (by omega) hib
        · exact vcc (j + 1) 1 hjlt (by omega) _ (by omega) hjb
      · refine hnotBoth i (by omega) (by omega) (by omega) hia ?_
        exact vcc j i (by omega) (by omega) _ (by omega) hja
    have hne2 : i ≠ j + 1 := by
      intro heq
      refine hnotBoth (j + 1) (by omega) (by omega) (by omega) ?_ hjb
      exact vcc i (j + 1) (by omega) (by omega) _ heq hia
    have hne3 : i + 1 ≠ j := by
      intro heq
      refine hnotBoth j (by omega) (by omega) (by omega) ?_ hja
      exact vcc (i + 1) j hilt (by omega) _ heq hib
    omega
  have hdisj : Disjoint (EIdx G (T \ {u}) P) (EIdx G (T \ {v}) P) := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    rcases hsep i hiA i hiB with h | h <;> omega
  have hTsub : EIdx G T P ⊆ ∅ := by
    intro i hi
    have h1 : i ∈ EIdx G (T \ {u}) P := EIdx_mono Set.diff_subset hi
    have h2 : i ∈ EIdx G (T \ {v}) P := EIdx_mono Set.diff_subset hi
    rcases hsep i h1 i h2 with h | h <;> omega
  have hTempty : (EIdx G T P).ncard = 0 :=
    (Set.ncard_eq_zero EIdx_finite).mpr (Set.subset_empty_iff.mp hTsub)
  by_cases hmeven : pathLength P % 2 = 0
  · left; rw [hTempty]; omega
  have hmodd : pathLength P % 2 = 1 := by omega
  have hAodd : (EIdx G (T \ {u}) P).ncard % 2 = 1 := by rw [hAp]; exact hmodd
  have hBodd : (EIdx G (T \ {v}) P).ncard % 2 = 1 := by rw [hBp]; exact hmodd
  have hAne : (EIdx G (T \ {u}) P).Nonempty := by
    rcases Set.eq_empty_or_nonempty (EIdx G (T \ {u}) P) with h | h
    · rw [h] at hAodd; simp at hAodd
    · exact h
  have hBne : (EIdx G (T \ {v}) P).Nonempty := by
    rcases Set.eq_empty_or_nonempty (EIdx G (T \ {v}) P) with h | h
    · rw [h] at hBodd; simp at hBodd
    · exact h
  obtain ⟨i0, hi0⟩ := hAne
  obtain ⟨j0, hj0⟩ := hBne
  -- Step 5.4: the longest antipath has odd length
  have hkodd : Odd (pathLength Q) := by
    rcases Nat.even_or_odd (pathLength Q) with hev | hod
    · exfalso
      rcases hsep i0 hi0 j0 hj0 with hord | hord
      · exact step54 hG hP hPT hr hs hnoInternalComplete hQp hQT hk2 hev hi0 hj0 hord
      · exact step54 hG hP hPT hr hs hnoInternalComplete
          (PathBasics.isAntipathFrom_reverse hQp)
          (fun x hx => hQT x (List.mem_reverse.mp hx))
          (by rw [PathBasics.pathLength_reverse]; exact hk2)
          (by rw [PathBasics.pathLength_reverse]; exact hev) hj0 hi0 hord
    · exact hod
  have hk3 : 3 ≤ pathLength Q := by obtain ⟨t, ht⟩ := hkodd; omega
  -- Step 5.5: delete both ends
  have hS_anti : AnticonnectedSet G (T \ {u, v}) :=
    both_ends_deletion_anticonnected hG hTanti hQlong hkodd hk3
  have hS_ss : T \ {u, v} ⊂ T :=
    ⟨Set.diff_subset, fun hcon => (hcon huT).2 (Set.mem_insert u {v})⟩
  rcases lift (T \ {u, v}) Set.diff_subset hS_ss hS_anti with hSp | hright
  swap
  · exact Or.inr hright
  -- Step 5.6: a third complete edge outside both families
  have hsub1 : T \ {u, v} ⊆ T \ {u} := by
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp h)))⟩
  have hsub2 : T \ {u, v} ⊆ T \ {v} := by
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (Set.mem_insert_iff.mpr (Or.inr h))⟩
  have hUsub : EIdx G (T \ {u}) P ∪ EIdx G (T \ {v}) P ⊆ EIdx G (T \ {u, v}) P :=
    Set.union_subset (EIdx_mono hsub1) (EIdx_mono hsub2)
  have hnotsub : ¬ (EIdx G (T \ {u, v}) P ⊆
      EIdx G (T \ {u}) P ∪ EIdx G (T \ {v}) P) := by
    intro hsub
    have heq : EIdx G (T \ {u, v}) P = EIdx G (T \ {u}) P ∪ EIdx G (T \ {v}) P :=
      Set.Subset.antisymm hsub hUsub
    rw [heq, Set.ncard_union_eq hdisj EIdx_finite EIdx_finite] at hSp
    omega
  obtain ⟨l, hlS, hlAB⟩ := Set.not_subset.mp hnotsub
  have hlA : l ∉ EIdx G (T \ {u}) P := fun h => hlAB (Or.inl h)
  have hlB : l ∉ EIdx G (T \ {v}) P := fun h => hlAB (Or.inr h)
  have hllt : l + 1 < P.length := EIdx_lt hlS
  have hbl : l < P.length := by omega
  obtain ⟨hcA, hcB⟩ := (mem_EIdx_iff hP.1 hllt).mp hlS
  have hPnotT : ∀ (n : ℕ) (hn : n < P.length), (P[n]'hn) ∉ T := fun n hn =>
    hPT _ (List.getElem_mem hn)
  right
  by_cases hαu : G.Adj (P[l]'hbl) u
  · -- `P[l]` sees `u`; then `P[l+1]` misses `u`, sees `v`, and `P[l]` misses `v`
    have hβu : ¬ G.Adj (P[l + 1]'hllt) u := by
      intro h
      exact hlB ((mem_EIdx_iff hP.1 hllt).mpr
        ⟨vc_sdiff_of (complete_of_pair' hcA hαu), vc_sdiff_of (complete_of_pair' hcB h)⟩)
    have hβv : G.Adj (P[l + 1]'hllt) v := by
      by_contra h
      exact claimC hG hQp hQT hk2 hkodd (hPnotT _ hllt) hcB hβu h
    have hαv : ¬ G.Adj (P[l]'hbl) v := by
      intro h
      exact hlA ((mem_EIdx_iff hP.1 hllt).mpr
        ⟨vc_sdiff_of (complete_of_pair hcA h), vc_sdiff_of (complete_of_pair hcB hβv)⟩)
    have hpc : ({v, u} : Set V) = {u, v} := Set.pair_comm v u
    have hlS' : l ∈ EIdx G (T \ {v, u}) P := by rw [hpc]; exact hlS
    exact step57 hG hP hPT hr hs (PathBasics.isAntipathFrom_reverse hQp)
      (fun x hx => hQT x (List.mem_reverse.mp hx))
      (by rw [PathBasics.pathLength_reverse]; exact hk3)
      (by rw [PathBasics.pathLength_reverse]; exact hkodd) hlS' hαv hβu
  · -- `P[l]` misses `u`; then it sees `v`, and `P[l+1]` misses `v`
    have hαv : G.Adj (P[l]'hbl) v := by
      by_contra h
      exact claimC hG hQp hQT hk2 hkodd (hPnotT _ hbl) hcA hαu h
    have hβv : ¬ G.Adj (P[l + 1]'hllt) v := by
      intro h
      exact hlA ((mem_EIdx_iff hP.1 hllt).mpr
        ⟨vc_sdiff_of (complete_of_pair hcA hαv), vc_sdiff_of (complete_of_pair hcB h)⟩)
    exact step57 hG hP hPT hr hs hQp hQT hk3 hkodd hlS hαu hβv


end RRNonstableAux

open RRNonstableAux

/-- The nonstable-set branch of the strengthened Roussel--Rubio induction:
proper anticonnected subsets satisfying the full parity trichotomy force either
the complete-edge parity conclusion or the exceptional length-three odd
antipath. -/
theorem RousselRubioNonstableParityOrAntipath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (T : Set V) (hTne : T.Nonempty) (hTanti : AnticonnectedSet G T)
    (hTnonstable :
      ¬ Set.Pairwise T (fun x y ↦ ¬ G.Adj x y))
    (P : List V) (r s : V) (hP : IsPathFrom G P r s)
    (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoInternalComplete :
      ∀ z ∈ SPGT.interior P, ¬ VertexComplete G z T)
    (hnoLeap : ¬ (
      Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b))
    (hproper : ∀ S : Set V, S ⊂ T → AnticonnectedSet G S →
      (({i : ℕ | i + 1 < P.length ∧
          ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
            EdgeComplete G S u v} : Set ℕ).ncard % 2 =
        pathLength P % 2) ∨
      (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ S, ∃ b ∈ S, IsLeapForPath G P a b) ∨
      (pathLength P = 3 ∧
        ∃ c d : V, SPGT.interior P = [c, d] ∧
          ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
            ∀ w ∈ SPGT.interior Q, w ∈ S)) :
    (({i : ℕ | i + 1 < P.length ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ).ncard % 2 =
      pathLength P % 2) ∨
    (pathLength P = 3 ∧
      ∃ c d : V, SPGT.interior P = [c, d] ∧
        ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
          ∀ w ∈ SPGT.interior Q, w ∈ T) := by
  exact mainAux G hG T hTne hTanti hTnonstable P r s hP hPT hr hs hnoInternalComplete
    hnoLeap hproper

end Workspace.ProofLemmas
