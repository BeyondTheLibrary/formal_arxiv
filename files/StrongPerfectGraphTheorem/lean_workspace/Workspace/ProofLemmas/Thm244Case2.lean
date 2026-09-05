import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.TriangleCatching
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArc
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.Thm244Parity
import Workspace.ProofLemmas.ReflectionAntihole
import Workspace.Statements.S17.Thm_17_1

/-!
# 24.4, second case of the trichotomy

Refutation of the second of the three shapes of `Thm244Shapes`, following the printed proof of
**24.4** (Chudnovsky–Robertson–Seymour–Thomas, printed p. 144) sentence by sentence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Types.Thm244Case2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm244Shapes

/-! ## Generic bookkeeping -/

section Helpers

variable {V : Type*}

private theorem getElem_congr {α : Type*} (l : List α) {a b : ℕ} (h : a = b)
    (ha : a < l.length) (hb : b < l.length) : l[a]'ha = l[b]'hb := by
  subst h; rfl

private theorem ncard_triple {x y z : V} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    ({x, y, z} : Set V).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by simp [h1, h2]), Set.ncard_pair h3]

/-- A path whose two named ends coincide is a single vertex. -/
private theorem path_self_singleton {G : SimpleGraph V} {p : List V} {x : V}
    (h : IsPathFrom G p x x) : p = [x] := by
  have hpos : 0 < p.length := PathBasics.path_length_pos h.1
  have hnd := PathBasics.path_nodup h.1
  have hlen : p.length = 1 := by
    by_contra hc
    have h2 : 0 < p.length - 1 := by omega
    have e0 : p[0]'hpos = x := PathBasics.getElem_zero_of_head? h.2.1 hpos
    have e1 : p[p.length - 1]'(by omega) = x := PathBasics.getElem_last_of_getLast? h.2.2 hpos
    have := hnd.getElem_inj_iff.mp (e0.trans e1.symm)
    omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
  have : a = x := by simpa using h.2.1
  rw [this]

/-- The empty set is connected. -/
private theorem connectedSet_empty {G : SimpleGraph V} : ConnectedSet G (∅ : Set V) := by
  intro a
  exact a.2.elim

/-- A path minus its last vertex is a connected set. -/
private theorem connectedSet_leg {G : SimpleGraph V} {p : List V} {x y : V}
    (h : IsPathFrom G p x y) : ConnectedSet G {w : V | w ∈ p ∧ w ≠ y} := by
  have hnd := PathBasics.path_nodup h.1
  have hne := PathBasics.path_ne_nil h.1
  have hpos : 0 < p.length := PathBasics.path_length_pos h.1
  have hlast : p.getLast hne = y := by
    have h2 := h.2.2
    rw [List.getLast?_eq_some_getLast hne] at h2
    exact Option.some_injective _ h2
  have hset : {w : V | w ∈ p ∧ w ≠ y} = {w : V | w ∈ p.take (p.length - 1)} := by
    ext w
    simp only [Set.mem_setOf_eq]
    rw [← List.dropLast_eq_take, PathBasics.mem_dropLast_iff hnd hne, hlast]
  rw [hset]
  rcases Nat.lt_or_ge p.length 2 with hlt | hge
  · have he : p.length - 1 = 0 := by omega
    rw [he]
    simpa using (connectedSet_empty (G := G))
  · exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_take h.1 (by omega))

/-- Attaching a possibly-empty connected set to a connected set. -/
private theorem connected_attach {G : SimpleGraph V} {W S : Set V}
    (hW : ConnectedSet G W) (hS : ConnectedSet G S)
    (hlink : S.Nonempty → ∃ p ∈ W, ∃ q ∈ S, G.Adj p q) : ConnectedSet G (W ∪ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hW
  · exact ConnectedSetUnionAttach.connectedSet_union hW hS (Or.inr (hlink hne))

/-- The last-but-one vertex of a nondegenerate path. -/
private theorem exists_pred_neighbour {G : SimpleGraph V} {p : List V} {x y : V}
    (h : IsPathFrom G p x y) (hxy : x ≠ y) : ∃ w, w ∈ p ∧ w ≠ y ∧ G.Adj y w := by
  have hpos : 0 < p.length := PathBasics.path_length_pos h.1
  have h2 : 2 ≤ p.length := by
    by_contra hc
    have hl : p.length = 1 := by omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
    have e1 : a = x := by simpa using h.2.1
    have e2 : a = y := by simpa using h.2.2
    exact hxy (e1.symm.trans e2)
  have hlast : p[p.length - 1]'(by omega) = y := PathBasics.getElem_last_of_getLast? h.2.2 hpos
  have hadj : G.Adj (p[p.length - 2]'(by omega)) (p[p.length - 1]'(by omega)) := by
    have := PathBasics.path_adj_succ h.1 (i := p.length - 2) (by omega)
    rwa [getElem_congr p (show p.length - 2 + 1 = p.length - 1 by omega) (by omega) (by omega)]
      at this
  refine ⟨p[p.length - 2]'(by omega), List.getElem_mem _, ?_, ?_⟩
  · rw [← hlast]
    intro hcon
    have := (PathBasics.path_nodup h.1).getElem_inj_iff.mp hcon
    omega
  · rw [← hlast]; exact hadj.symm

/-- A path minus its last vertex is nonempty only if the path is nondegenerate. -/
private theorem leg_nonempty {G : SimpleGraph V} {p : List V} {x y : V}
    (h : IsPathFrom G p x y) (hne : {w : V | w ∈ p ∧ w ≠ y}.Nonempty) : x ≠ y := by
  intro hxy
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hwp, hwy⟩ := hw
  rw [hxy] at h
  rw [path_self_singleton h] at hwp
  exact hwy (by simpa using hwp)

/-- Three vertices, two of which are joined to the first, form a connected set. -/
private theorem connectedSet_triple {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) : ConnectedSet G ({x, y, z} : Set V) := by
  have hchain : List.IsChain G.Adj [y, x, z] := by
    refine List.isChain_iff_getElem.mpr ?_
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi_bound : i ≤ 1 := by omega
    interval_cases i
    · simpa using hxy.symm
    · simpa using hxz
  have hset : ({x, y, z} : Set V) = {w : V | w ∈ [y, x, z]} := by
    ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      List.mem_cons, List.not_mem_nil, or_false]; tauto
  rw [hset]
  exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain hchain

/-- The tail of a path, as a slice (so that `PathBasics.mem_slice_iff` decodes membership). -/
private theorem isPathFrom_tailSlice {G : SimpleGraph V} {p : List V} {x y : V}
    (h : IsPathFrom G p x y) (h3 : 3 ≤ p.length) :
    IsPathFrom G ((p.drop 1).take (p.length - 1 - 1 + 1)) (p[1]'(by omega)) y := by
  have hpos : 0 < p.length := by omega
  have hlast : p[p.length - 1]'(by omega) = y := PathBasics.getElem_last_of_getLast? h.2.2 hpos
  have := PathBasics.isPathFrom_slice h.1 (i := 1) (j := p.length - 1) (by omega) (by omega)
  rwa [hlast] at this

end Helpers

/-! ## Closing an antipath into an antihole -/

section Antiholes

variable {V : Type*}

/-- *"… can be completed to an antihole via `z`"*: a single `X`-complete vertex non-adjacent to
both ends closes an antipath with interior in `X` into an antihole. -/
private theorem antihole_witness {G : SimpleGraph V} {Xs : Set V} {p q z : V}
    (hadjpq : G.Adj p q) (hzX : VertexComplete G z Xs)
    (hzp : ¬ G.Adj z p) (hzq : ¬ G.Adj z q) (hznep : z ≠ p) (hzneq : z ≠ q)
    {Q : List V} (hQ : IsAntipathFrom G Q p q) (hQint : ∀ w ∈ SPGT.interior Q, w ∈ Xs) :
    ∃ c : List V, IsAntiholeList G c ∧ holeLength c = pathLength Q + 2 := by
  have hQ3 : 3 ≤ Q.length := AntiholeCompletion.three_le_length_of_antipath hQ hadjpq
  have hznotX : z ∉ Xs := fun hh => G.irrefl (hzX z hh)
  have hznotQ : z ∉ Q := by
    intro hz
    exact hznotX (hQint z ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hz, hznep, hzneq⟩))
  have hRpath : IsPathFrom Gᶜ [z] z z := ⟨PathBasics.isPathList_singleton Gᶜ z, rfl, rfl⟩
  have hdisj : ∀ x ∈ Q, x ∉ [z] := by
    intro x hx hmem
    have hxz : x = z := by simpa using hmem
    exact hznotQ (hxz ▸ hx)
  have hcross : ∀ x ∈ Q, ∀ y ∈ [z], (Gᶜ.Adj x y ↔ (x = q ∧ y = z) ∨ (x = p ∧ y = z)) := by
    intro x hx y hy
    have hyz : y = z := by simpa using hy
    subst hyz
    constructor
    · intro hadjxz
      by_cases hxu : x = p
      · exact Or.inr ⟨hxu, rfl⟩
      by_cases hxv : x = q
      · exact Or.inl ⟨hxv, rfl⟩
      exact absurd (hzX x (hQint x
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩))).symm hadjxz.2
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact ⟨fun hh => hzneq hh.symm, fun hh => hzq hh.symm⟩
      · exact ⟨fun hh => hznep hh.symm, fun hh => hzp hh.symm⟩
  refine ⟨Q ++ [z], PathGlue.glue_hole hQ hRpath hdisj hcross
    (by simp only [List.length_singleton]; omega), ?_⟩
  simp only [holeLength, List.length_append, List.length_singleton]
  have := PathBasics.pathLength_eq Q
  omega

/-- *"Since `Q ∪ R` is an antihole …"*: two antipaths with the same ends, one with interior in
`Ys` and one with interior in `Xs`, where `Xs` is complete to `Ys`, close into an antihole. -/
private theorem antihole_two_antipaths {G : SimpleGraph V} {Xs Ys : Set V}
    (hXY : Disjoint Xs Ys) (hcompl : Complete G Xs Ys)
    {p q : V} (hadjpq : G.Adj p q)
    (hpX : p ∉ Xs) (hqX : q ∉ Xs) {Q R : List V}
    (hQ : IsAntipathFrom G Q p q) (hQint : ∀ w ∈ SPGT.interior Q, w ∈ Ys)
    (hR : IsAntipathFrom G R p q) (hRint : ∀ w ∈ SPGT.interior R, w ∈ Xs) :
    ∃ c : List V, IsAntiholeList G c ∧ holeLength c = pathLength Q + pathLength R := by
  have hQ3 : 3 ≤ Q.length := AntiholeCompletion.three_le_length_of_antipath hQ hadjpq
  have hR3 : 3 ≤ R.length := AntiholeCompletion.three_le_length_of_antipath hR hadjpq
  have hRpos : 0 < R.length := by omega
  have hR1lt : 1 < R.length := by omega
  have hRm2 : R.length - 2 < R.length := by omega
  have hRm1 : R.length - 1 < R.length := by omega
  have hR0 : R[0]'hRpos = p := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRL : R[R.length - 1]'hRm1 = q := PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  have hIpath : IsPathFrom Gᶜ (SPGT.interior R) (R[1]'hR1lt) (R[R.length - 2]'hRm2) :=
    PathGlue.isPathFrom_interior hR.1 hR3
  have hIrev : IsPathFrom Gᶜ (SPGT.interior R).reverse (R[R.length - 2]'hRm2) (R[1]'hR1lt) :=
    PathBasics.isPathFrom_reverse hIpath
  have hIeq : SPGT.interior R = (R.drop 1).take ((R.length - 2) - 1 + 1) := by
    rw [PathBasics.interior_eq_drop_take]; congr 1; omega
  have hImem : ∀ y : V, y ∈ SPGT.interior R ↔
      ∃ (k : ℕ) (hk : k < R.length), 1 ≤ k ∧ k ≤ R.length - 2 ∧ (R[k]'hk) = y := by
    intro y
    rw [hIeq]
    exact PathBasics.mem_slice_iff R (by omega) hRm2
  have hdisj : ∀ x ∈ Q, x ∉ (SPGT.interior R).reverse := by
    intro x hx hmem
    have hxX : x ∈ Xs := hRint x (List.mem_reverse.mp hmem)
    by_cases hxu : x = p
    · exact hpX (hxu ▸ hxX)
    by_cases hxv : x = q
    · exact hqX (hxv ▸ hxX)
    exact (Set.disjoint_left.mp hXY hxX)
      (hQint x ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩))
  have hcross : ∀ x ∈ Q, ∀ y ∈ (SPGT.interior R).reverse,
      (Gᶜ.Adj x y ↔ (x = q ∧ y = R[R.length - 2]'hRm2) ∨ (x = p ∧ y = R[1]'hR1lt)) := by
    intro x hx y hy
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hImem y).mp (List.mem_reverse.mp hy)
    have hkX : (R[k]'hk) ∈ Xs := hRint _ ((hImem _).mpr ⟨k, hk, hk1, hk2, rfl⟩)
    have hinjR : ∀ (m : ℕ) (hm : m < R.length), ((R[k]'hk) = (R[m]'hm) ↔ k = m) := by
      intro m hm
      exact List.Nodup.getElem_inj_iff hRnd
    have huv : p ≠ q := hadjpq.ne
    have hadju : Gᶜ.Adj p (R[k]'hk) ↔ k = 1 := by
      rw [← hR0, PathBasics.path_adj_iff hR.1 hRpos hk]; omega
    have hadjv : Gᶜ.Adj q (R[k]'hk) ↔ k = R.length - 2 := by
      rw [← hRL, PathBasics.path_adj_iff hR.1 hRm1 hk]; omega
    have hik1 : ((R[k]'hk) = (R[1]'hR1lt)) ↔ k = 1 := hinjR 1 hR1lt
    have hikm : ((R[k]'hk) = (R[R.length - 2]'hRm2)) ↔ k = R.length - 2 := hinjR _ hRm2
    by_cases hxu : x = p
    · rw [hxu, hadju, hikm, hik1]
      constructor
      · intro hh; exact Or.inr ⟨rfl, hh⟩
      · rintro (⟨hh, -⟩ | ⟨-, hh⟩)
        · exact absurd hh huv
        · exact hh
    by_cases hxv : x = q
    · rw [hxv, hadjv, hikm, hik1]
      constructor
      · intro hh; exact Or.inl ⟨rfl, hh⟩
      · rintro (⟨-, hh⟩ | ⟨hh, -⟩)
        · exact hh
        · exact absurd hh.symm huv
    · have hxY : x ∈ Ys := hQint x ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩)
      refine iff_of_false (fun hcon => hcon.2 (hcompl _ hkX x hxY).symm) ?_
      rintro (⟨hh, -⟩ | ⟨hh, -⟩)
      · exact hxv hh
      · exact hxu hh
  have hlen : 4 ≤ Q.length + (SPGT.interior R).reverse.length := by
    rw [List.length_reverse, PathBasics.interior_length]
    omega
  refine ⟨Q ++ (SPGT.interior R).reverse, PathGlue.glue_hole hQ hIrev hdisj hcross hlen, ?_⟩
  simp only [holeLength, List.length_append, List.length_reverse, PathBasics.interior_length]
  have h1 := PathBasics.pathLength_eq Q
  have h2 := PathBasics.pathLength_eq R
  omega

/-- *"let `xᵢ` be the middle vertex of `Qᵢ`"*: an antipath of length `2` with interior in `Xs`
has a single interior vertex, which lies in `Xs` and is nonadjacent to both ends. -/
private theorem middle_of_antipath {G : SimpleGraph V} {Q : List V} {p q : V} {Xs : Set V}
    (hQ : IsAntipathFrom G Q p q) (hQint : ∀ z ∈ SPGT.interior Q, z ∈ Xs)
    (h2 : pathLength Q = 2) :
    ∃ x : V, x ∈ Xs ∧ ¬ G.Adj p x ∧ ¬ G.Adj q x := by
  have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hlen : Q.length = 3 := by
    have := PathBasics.pathLength_eq Q
    omega
  obtain ⟨e, x, f, hEq⟩ := PrismBasics.length_eq_three hlen
  rw [hEq] at hQ hQint
  have he : e = p := by simpa using hQ.2.1
  have hf : f = q := by simpa using hQ.2.2
  have hxX : x ∈ Xs := hQint x (by rw [PathBasics.interior_eq]; simp)
  have hadj0 : Gᶜ.Adj e x := by
    have := PathBasics.path_adj_succ hQ.1 (i := 0) (by simp)
    simpa using this
  have hadj1 : Gᶜ.Adj x f := by
    have := PathBasics.path_adj_succ hQ.1 (i := 1) (by simp)
    simpa using this
  refine ⟨x, hxX, ?_, ?_⟩
  · rw [← he]; exact hadj0.2
  · rw [← hf]; exact fun hc => hadj1.2 hc.symm

end Antiholes

/-! ## The two branches of the printed argument -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"If `P₁, P₂, P₃` all have length 0, then the union of `Q₁, Q₂, Q₃` is an antihole of
length `> 4`, a contradiction."* -/
private theorem degenerate_case (G : SimpleGraph V) (hG : InF11 G) (X : Fin 3 → Set V)
    (hXd : ∀ i j : Fin 3, i ≠ j → Disjoint (X i) (X j))
    (hXa : ∀ i : Fin 3, AnticonnectedSet G (X i))
    (hXc : ∀ i j : Fin 3, i ≠ j → Complete G (X i) (X j))
    (v u : Fin 3 → V) (P : Fin 3 → List V)
    (hP : ∀ i : Fin 3, IsPathFrom G (P i) (v i) (u i))
    (hPX : ∀ i : Fin 3, ∀ w ∈ P i, ∀ l : Fin 3, w ∉ X l)
    (hvc : ∀ i : Fin 3, VertexComplete G (v i) (X i))
    (huniq : ∀ i j : Fin 3, ∀ w ∈ P i, VertexComplete G w (X j) → w = v j)
    (hPne : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, x ≠ y)
    (hPadj : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, (G.Adj x y ↔ (x = u i ∧ y = u j)))
    (hdeg : ∀ i : Fin 3, v i = u i) : False := by
  have huP : ∀ i : Fin 3, u i ∈ P i := fun i => (PathBasics.isPathFrom_ends_mem (hP i)).2
  have hvP : ∀ i : Fin 3, v i ∈ P i := fun i => (PathBasics.isPathFrom_ends_mem (hP i)).1
  have hunX : ∀ i l : Fin 3, u i ∉ X l := fun i l => hPX i _ (huP i) l
  have huadj : ∀ i j : Fin 3, i ≠ j → G.Adj (u i) (u j) :=
    fun i j h => (hPadj i j h _ (huP i) _ (huP j)).mpr ⟨rfl, rfl⟩
  have hune : ∀ i j : Fin 3, i ≠ j → u i ≠ u j := fun i j h => hPne i j h _ (huP i) _ (huP j)
  have hunev : ∀ i j : Fin 3, i ≠ j → u i ≠ v j := fun i j h => hPne i j h _ (huP i) _ (hvP j)
  have hnotc : ∀ i j : Fin 3, ∀ w ∈ P i, w ≠ v j → ∃ x ∈ X j, ¬ G.Adj w x := by
    intro i j w hw hwne
    by_contra hcon
    push_neg at hcon
    exact hwne (huniq i j w hw hcon)
  have hQex : ∀ i j k : Fin 3, u j ≠ v i → u k ≠ v i →
      ∃ q : List V, IsAntipathFrom G q (u j) (u k) ∧ ∀ z ∈ SPGT.interior q, z ∈ X i := by
    intro i j k hj hk
    exact InducedPathExtraction.exists_antipath_interior_in (hXa i) (hunX j i) (hunX k i)
      (hnotc j i _ (huP j) hj) (hnotc k i _ (huP k) hk)
  obtain ⟨Q0, hQ0, hQ0int⟩ := hQex 0 1 2 (hunev 1 0 (by decide)) (hunev 2 0 (by decide))
  obtain ⟨Q1, hQ1, hQ1int⟩ := hQex 1 2 0 (hunev 2 1 (by decide)) (hunev 0 1 (by decide))
  obtain ⟨Q2, hQ2, hQ2int⟩ := hQex 2 0 1 (hunev 0 2 (by decide)) (hunev 1 2 (by decide))
  have h0len : 3 ≤ Q0.length :=
    AntiholeCompletion.three_le_length_of_antipath hQ0 (huadj 1 2 (by decide))
  have h1len : 3 ≤ Q1.length :=
    AntiholeCompletion.three_le_length_of_antipath hQ1 (huadj 2 0 (by decide))
  have h2len : 3 ≤ Q2.length :=
    AntiholeCompletion.three_le_length_of_antipath hQ2 (huadj 0 1 (by decide))
  have hQ2mem : ∀ z ∈ Q2, z = u 0 ∨ z = u 1 ∨ z ∈ X 2 := by
    intro z hz
    by_cases h1 : z = u 0
    · exact Or.inl h1
    by_cases h2 : z = u 1
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQ2int z ((PathBasics.mem_interior_iff_of_pathFrom hQ2).mpr ⟨hz, h1, h2⟩)))
  -- Delete the last vertex `u 0` from `Q1`, then glue on `Q2`.
  obtain ⟨D, hD, hDlen, hDmem⟩ :=
    Thm244Parity.chop (PathBasics.isAntipathFrom_iff.mp hQ1) (by omega)
  have hDdec : ∀ x ∈ D, x = u 2 ∨ x ∈ X 1 := by
    intro x hx
    obtain ⟨k, hk, hkm, rfl⟩ := (hDmem x).mp hx
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl (PathBasics.getElem_zero_of_head? hQ1.2.1 hk)
    · exact Or.inr (hQ1int _ (PathBasics.getElem_mem_interior hQ1.1 hk hk0 (by omega)))
  have hQ1last : Q1[Q1.length - 1]'(by omega) = u 0 :=
    PathBasics.getElem_last_of_getLast? hQ1.2.2 (by omega)
  have hglue : IsPathFrom Gᶜ (D ++ Q2) (u 2) (u 1) := by
    refine PathGlue.glue_path hD (PathBasics.isAntipathFrom_iff.mp hQ2) ?_ ?_
    · intro x hx hxq
      rcases hDdec x hx with rfl | hxX
      · rcases hQ2mem _ hxq with h | h | h
        · exact hune 2 0 (by decide) h
        · exact hune 2 1 (by decide) h
        · exact hunX 2 2 h
      · rcases hQ2mem x hxq with h | h | h
        · exact hunX 0 1 (h ▸ hxX)
        · exact hunX 1 1 (h ▸ hxX)
        · exact (Set.disjoint_left.mp (hXd 1 2 (by decide)) hxX) h
    · intro x hx y hy
      obtain ⟨k, hk, hkm, rfl⟩ := (hDmem x).mp hx
      have hkey : ((Q1[k]'hk) = Q1[Q1.length - 2]'(by omega)) ↔ k = Q1.length - 2 :=
        (PathBasics.path_nodup hQ1.1).getElem_inj_iff
      rcases hQ2mem y hy with rfl | rfl | hyX
      · rw [← hQ1last, PathBasics.path_adj_iff hQ1.1 hk (by omega), hkey]
        simp only [and_true]
        omega
      · refine iff_of_false ?_ (fun hc => hune 1 0 (by decide) hc.2)
        intro hadj
        have hne1 : ¬ G.Adj (Q1[k]'hk) (u 1) := hadj.2
        rcases hDdec _ hx with h | h
        · exact hne1 (by rw [h]; exact huadj 2 1 (by decide))
        · have hx1 : G.Adj (Q1[k]'hk) (v 1) := (hvc 1 _ h).symm
          rw [hdeg 1] at hx1
          exact hne1 hx1
      · refine iff_of_false ?_ (fun hc => hunX 0 2 (hc.2 ▸ hyX))
        intro hadj
        rcases hDdec _ hx with h | h
        · exact hadj.2 (by rw [h, ← hdeg 2]; exact hvc 2 y hyX)
        · exact hadj.2 (hXc 1 2 (by decide) _ h y hyX)
  have hgluemem : ∀ z ∈ D ++ Q2, z = u 2 ∨ z ∈ X 1 ∨ z = u 0 ∨ z = u 1 ∨ z ∈ X 2 := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · rcases hDdec z h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases hQ2mem z h with h' | h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  have hglueint : ∀ z ∈ SPGT.interior (D ++ Q2), z ∈ ((X 1 ∪ {u 0}) ∪ X 2) := by
    intro z hz
    rw [PathBasics.mem_interior_iff_of_pathFrom hglue] at hz
    obtain ⟨hzm, hz2, hz1⟩ := hz
    rcases hgluemem z hzm with h | h | h | h | h
    · exact absurd h hz2
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact absurd h hz1
    · exact Or.inr h
  have hQ0rev : IsAntipathFrom G Q0.reverse (u 2) (u 1) := PathBasics.isAntipathFrom_reverse hQ0
  have hQ0revint : ∀ z ∈ SPGT.interior Q0.reverse, z ∈ X 0 :=
    fun z hz => hQ0int z (PathBasics.mem_interior_reverse.mp hz)
  obtain ⟨cyc, hcyc, hcyclen⟩ :=
    antihole_two_antipaths (G := G) (Xs := (X 1 ∪ {u 0}) ∪ X 2) (Ys := X 0)
      (by
        rw [Set.disjoint_left]
        rintro x ((hx | hx) | hx)
        · exact fun hx0 => (Set.disjoint_left.mp (hXd 1 0 (by decide)) hx) hx0
        · have : x = u 0 := hx
          exact fun hx0 => hunX 0 0 (this ▸ hx0)
        · exact fun hx0 => (Set.disjoint_left.mp (hXd 2 0 (by decide)) hx) hx0)
      (by
        rintro x ((hx | hx) | hx) y hy
        · exact hXc 1 0 (by decide) x hx y hy
        · have hxu : x = u 0 := hx
          rw [hxu, ← hdeg 0]
          exact hvc 0 y hy
        · exact hXc 2 0 (by decide) x hx y hy)
      (huadj 2 1 (by decide))
      (by
        rintro ((hx | hx) | hx)
        · exact hunX 2 1 hx
        · exact hune 2 0 (by decide) hx
        · exact hunX 2 2 hx)
      (by
        rintro ((hx | hx) | hx)
        · exact hunX 1 1 hx
        · exact hune 1 0 (by decide) hx
        · exact hunX 1 2 hx)
      hQ0rev hQ0revint (PathBasics.isAntipathFrom_iff.mpr hglue) hglueint
  have h4 := hG.2 cyc hcyc
  rw [hcyclen, PathBasics.pathLength_reverse] at h4
  simp only [PathBasics.pathLength_eq, List.length_append, hDlen] at h4
  omega

/-- The main body of the printed argument, once the paper's *"we may assume that `P₁` has
length `> 0`"* has fixed an index `a` with `v a ≠ u a`; `b` and `c` are the other two. -/
private theorem core_case (G : SimpleGraph V) (hG : InF11 G) (X : Fin 3 → Set V)
    (hXd : ∀ i j : Fin 3, i ≠ j → Disjoint (X i) (X j))
    (hXa : ∀ i : Fin 3, AnticonnectedSet G (X i))
    (hXc : ∀ i j : Fin 3, i ≠ j → Complete G (X i) (X j))
    (v u : Fin 3 → V) (P : Fin 3 → List V)
    (hP : ∀ i : Fin 3, IsPathFrom G (P i) (v i) (u i))
    (hPX : ∀ i : Fin 3, ∀ w ∈ P i, ∀ l : Fin 3, w ∉ X l)
    (hvc : ∀ i : Fin 3, VertexComplete G (v i) (X i))
    (huniq : ∀ i j : Fin 3, ∀ w ∈ P i, VertexComplete G w (X j) → w = v j)
    (hPne : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, x ≠ y)
    (hPadj : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, (G.Adj x y ↔ (x = u i ∧ y = u j)))
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hva : v a ≠ u a) : False := by
  have huP : ∀ i : Fin 3, u i ∈ P i := fun i => (PathBasics.isPathFrom_ends_mem (hP i)).2
  have hvP : ∀ i : Fin 3, v i ∈ P i := fun i => (PathBasics.isPathFrom_ends_mem (hP i)).1
  have hunX : ∀ i l : Fin 3, u i ∉ X l := fun i l => hPX i _ (huP i) l
  have huadj : ∀ i j : Fin 3, i ≠ j → G.Adj (u i) (u j) :=
    fun i j h => (hPadj i j h _ (huP i) _ (huP j)).mpr ⟨rfl, rfl⟩
  have hune : ∀ i j : Fin 3, i ≠ j → u i ≠ u j := fun i j h => hPne i j h _ (huP i) _ (huP j)
  have hunev : ∀ i j : Fin 3, i ≠ j → u i ≠ v j := fun i j h => hPne i j h _ (huP i) _ (hvP j)
  have hnotc : ∀ i j : Fin 3, ∀ w ∈ P i, w ≠ v j → ∃ x ∈ X j, ¬ G.Adj w x := by
    intro i j w hw hwne
    by_contra hcon
    push_neg at hcon
    exact hwne (huniq i j w hw hcon)
  have hQex : ∀ i j k : Fin 3, u j ≠ v i → u k ≠ v i →
      ∃ q : List V, IsAntipathFrom G q (u j) (u k) ∧ ∀ z ∈ SPGT.interior q, z ∈ X i := by
    intro i j k hj hk
    exact InducedPathExtraction.exists_antipath_interior_in (hXa i) (hunX j i) (hunX k i)
      (hnotc j i _ (huP j) hj) (hnotc k i _ (huP k) hk)
  -- `Q₁, Q₂, Q₃` of the printed proof
  obtain ⟨Qa, hQa, hQaint⟩ := hQex a b c (hunev b a (Ne.symm hab)) (hunev c a (Ne.symm hac))
  obtain ⟨Qb, hQb, hQbint⟩ := hQex b c a (hunev c b (Ne.symm hbc)) (hunev a b hab)
  obtain ⟨Qc, hQc, hQcint⟩ := hQex c a b (hunev a c hac) (hunev b c hbc)
  -- the two auxiliary antipaths of the printed proof, both with interior in `X₁`
  obtain ⟨Ra, hRa, hRaint⟩ := hQex a c a (hunev c a (Ne.symm hac)) (Ne.symm hva)
  obtain ⟨Rb, hRb, hRbint⟩ := hQex a a b (Ne.symm hva) (hunev b a (Ne.symm hab))
  have hQalen : 3 ≤ Qa.length :=
    AntiholeCompletion.three_le_length_of_antipath hQa (huadj b c hbc)
  have hQblen : 3 ≤ Qb.length :=
    AntiholeCompletion.three_le_length_of_antipath hQb (huadj c a (Ne.symm hac))
  have hQclen : 3 ≤ Qc.length :=
    AntiholeCompletion.three_le_length_of_antipath hQc (huadj a b hab)
  have hRalen : 3 ≤ Ra.length :=
    AntiholeCompletion.three_le_length_of_antipath hRa (huadj c a (Ne.symm hac))
  have hRblen : 3 ≤ Rb.length :=
    AntiholeCompletion.three_le_length_of_antipath hRb (huadj a b hab)
  -- *"Since `v₁-u₂-Q₁-u₃-v₁` is an antihole, `Q₁` has length 2."*
  have hnadjb : ¬ G.Adj (v a) (u b) :=
    fun hcon => hva ((hPadj a b hab _ (hvP a) _ (huP b)).mp hcon).1
  have hnadjc : ¬ G.Adj (v a) (u c) :=
    fun hcon => hva ((hPadj a c hac _ (hvP a) _ (huP c)).mp hcon).1
  obtain ⟨ca, hca, hcalen⟩ := antihole_witness (huadj b c hbc) (hvc a) hnadjb hnadjc
    (hPne a b hab _ (hvP a) _ (huP b)) (hPne a c hac _ (hvP a) _ (huP c)) hQa hQaint
  have hQa2 : pathLength Qa = 2 := by
    have h4 := hG.2 ca hca
    rw [hcalen] at h4
    omega
  -- *"… their union with `Q₂` is an antihole; so `Q₂` has length 2, and similarly so does `Q₃`."*
  obtain ⟨cb, hcb, hcblen⟩ := antihole_two_antipaths (G := G) (Xs := X a) (Ys := X b)
    (hXd a b hab) (hXc a b hab) (huadj c a (Ne.symm hac)) (hunX c a) (hunX a a)
    hQb hQbint hRa hRaint
  have hQb2 : pathLength Qb = 2 := by
    have h4 := hG.2 cb hcb
    rw [hcblen] at h4
    simp only [PathBasics.pathLength_eq] at h4 ⊢
    omega
  obtain ⟨cc, hcc, hcclen⟩ := antihole_two_antipaths (G := G) (Xs := X a) (Ys := X c)
    (hXd a c hac) (hXc a c hac) (huadj a b hab) (hunX a a) (hunX b a)
    hQc hQcint hRb hRbint
  have hQc2 : pathLength Qc = 2 := by
    have h4 := hG.2 cc hcc
    rw [hcclen] at h4
    simp only [PathBasics.pathLength_eq] at h4 ⊢
    omega
  -- *"For `i = 1,2,3` let `xᵢ` be the middle vertex of `Qᵢ`."*
  obtain ⟨xa, hxaX, hxab, hxac⟩ := middle_of_antipath hQa hQaint hQa2
  obtain ⟨xb, hxbX, hxbc, hxba⟩ := middle_of_antipath hQb hQbint hQb2
  obtain ⟨xc, hxcX, hxca, hxcb⟩ := middle_of_antipath hQc hQcint hQc2
  -- the triangle `{u₁,u₂,u₃}`
  have hAtri : IsTriangle G ({u a, u b, u c} : Set V) := by
    refine ⟨ncard_triple (hune a b hab) (hune a c hac) (hune b c hbc), ?_⟩
    intro y hy z hz hyz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hyz
        | exact huadj a b hab
        | exact huadj a c hac
        | exact huadj b a (Ne.symm hab)
        | exact huadj b c hbc
        | exact huadj c a (Ne.symm hac)
        | exact huadj c b (Ne.symm hbc)
  -- *"`V(P₁\u₁) ∪ V(P₂\u₂) ∪ V(P₃\u₃) ∪ {x₁,x₂,x₃}` is connected"*
  obtain ⟨Fp, hFpconn, hFpmem⟩ :
      ∃ Fp : Set V, ConnectedSet G Fp ∧ ∀ w : V, w ∈ Fp ↔
        ((w = xa ∨ w = xb ∨ w = xc) ∨ (w ∈ P a ∧ w ≠ u a) ∨ (w ∈ P b ∧ w ≠ u b) ∨
          (w ∈ P c ∧ w ≠ u c)) := by
    refine ⟨((({xa, xb, xc} : Set V) ∪ {w : V | w ∈ P a ∧ w ≠ u a}) ∪
      {w : V | w ∈ P b ∧ w ≠ u b}) ∪ {w : V | w ∈ P c ∧ w ≠ u c}, ?_, ?_⟩
    · refine connected_attach (connected_attach
        (connected_attach ?_ (connectedSet_leg (hP a)) ?_) (connectedSet_leg (hP b)) ?_)
        (connectedSet_leg (hP c)) ?_
      · exact connectedSet_triple (hXc a b hab xa hxaX xb hxbX) (hXc a c hac xa hxaX xc hxcX)
      · intro _
        exact ⟨xa, by simp, v a, ⟨hvP a, hva⟩, (hvc a xa hxaX).symm⟩
      · intro hne
        exact ⟨xb, by simp, v b, ⟨hvP b, leg_nonempty (hP b) hne⟩, (hvc b xb hxbX).symm⟩
      · intro hne
        exact ⟨xc, by simp, v c, ⟨hvP c, leg_nonempty (hP c) hne⟩, (hvc c xc hxcX).symm⟩
    · intro w
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      tauto
  -- *"… and catches the triangle `{u₁,u₂,u₃}`"*
  have hdisjFA : ∀ w ∈ Fp, w ∉ ({u a, u b, u c} : Set V) := by
    intro w hw hwA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwA
    rcases (hFpmem w).mp hw with (rfl | rfl | rfl) | ⟨hwP, hwu⟩ | ⟨hwP, hwu⟩ | ⟨hwP, hwu⟩
    · rcases hwA with h | h | h
      · exact hunX a a (h ▸ hxaX)
      · exact hunX b a (h ▸ hxaX)
      · exact hunX c a (h ▸ hxaX)
    · rcases hwA with h | h | h
      · exact hunX a b (h ▸ hxbX)
      · exact hunX b b (h ▸ hxbX)
      · exact hunX c b (h ▸ hxbX)
    · rcases hwA with h | h | h
      · exact hunX a c (h ▸ hxcX)
      · exact hunX b c (h ▸ hxcX)
      · exact hunX c c (h ▸ hxcX)
    · rcases hwA with h | h | h
      · exact hwu h
      · exact hPne a b hab _ hwP _ (huP b) h
      · exact hPne a c hac _ hwP _ (huP c) h
    · rcases hwA with h | h | h
      · exact hPne b a (Ne.symm hab) _ hwP _ (huP a) h
      · exact hwu h
      · exact hPne b c hbc _ hwP _ (huP c) h
    · rcases hwA with h | h | h
      · exact hPne c a (Ne.symm hac) _ hwP _ (huP a) h
      · exact hPne c b (Ne.symm hbc) _ hwP _ (huP b) h
      · exact hwu h
  have hcatchAdj : ∀ z ∈ ({u a, u b, u c} : Set V), ∃ f ∈ Fp, G.Adj z f := by
    have key : ∀ (i : Fin 3) (xi : V), xi ∈ X i → xi ∈ Fp →
        (∀ w : V, w ∈ P i → w ≠ u i → w ∈ Fp) → ∃ f ∈ Fp, G.Adj (u i) f := by
      intro i xi hxi hxiFp hleg
      by_cases hd : v i = u i
      · refine ⟨xi, hxiFp, ?_⟩
        have h := hvc i xi hxi
        rwa [hd] at h
      · obtain ⟨w, hwP, hwu, hadj⟩ := exists_pred_neighbour (hP i) hd
        exact ⟨w, hleg w hwP hwu, hadj⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact key a xa hxaX ((hFpmem xa).mpr (Or.inl (Or.inl rfl)))
        (fun w hw hwu => (hFpmem w).mpr (Or.inr (Or.inl ⟨hw, hwu⟩)))
    · exact key b xb hxbX ((hFpmem xb).mpr (Or.inl (Or.inr (Or.inl rfl))))
        (fun w hw hwu => (hFpmem w).mpr (Or.inr (Or.inr (Or.inl ⟨hw, hwu⟩))))
    · exact key c xc hxcX ((hFpmem xc).mpr (Or.inl (Or.inr (Or.inr rfl))))
        (fun w hw hwu => (hFpmem w).mpr (Or.inr (Or.inr (Or.inr ⟨hw, hwu⟩))))
  -- *"… and none of its vertices have two neighbours in the triangle"*
  have hncard : ∀ f ∈ Fp, (G.neighborSet f ∩ ({u a, u b, u c} : Set V)).ncard ≤ 1 := by
    have bound : ∀ (f z : V),
        (G.neighborSet f ∩ ({u a, u b, u c} : Set V)) ⊆ ({z} : Set V) →
        (G.neighborSet f ∩ ({u a, u b, u c} : Set V)).ncard ≤ 1 := by
      intro f z hsub
      have := Set.ncard_le_ncard hsub (Set.finite_singleton z)
      rwa [Set.ncard_singleton] at this
    intro f hf
    rcases (hFpmem f).mp hf with (rfl | rfl | rfl) | ⟨hwP, hwu⟩ | ⟨hwP, hwu⟩ | ⟨hwP, hwu⟩
    · refine bound f (u a) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact rfl
      · exact absurd hy1'.symm hxab
      · exact absurd hy1'.symm hxac
    · refine bound f (u b) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact absurd hy1'.symm hxba
      · exact rfl
      · exact absurd hy1'.symm hxbc
    · refine bound f (u c) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact absurd hy1'.symm hxca
      · exact absurd hy1'.symm hxcb
      · exact rfl
    · refine bound f (u a) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact rfl
      · exact absurd ((hPadj a b hab _ hwP _ (huP b)).mp hy1').1 hwu
      · exact absurd ((hPadj a c hac _ hwP _ (huP c)).mp hy1').1 hwu
    · refine bound f (u b) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact absurd ((hPadj b a (Ne.symm hab) _ hwP _ (huP a)).mp hy1').1 hwu
      · exact rfl
      · exact absurd ((hPadj b c hbc _ hwP _ (huP c)).mp hy1').1 hwu
    · refine bound f (u c) ?_
      rintro y ⟨hy1, hy2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
      have hy1' : G.Adj f y := hy1
      rcases hy2 with rfl | rfl | rfl
      · exact absurd ((hPadj c a (Ne.symm hac) _ hwP _ (huP a)).mp hy1').1 hwu
      · exact absurd ((hPadj c b (Ne.symm hbc) _ hwP _ (huP b)).mp hy1').1 hwu
      · exact rfl
  -- *"This is contrary to 17.1."*
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG.1.1.1.1
      ({u a, u b, u c} : Set V) hAtri Fp (fun w hw => hdisjFA w hw)
      ⟨hAtri, hFpconn, Set.disjoint_left.mpr hdisjFA, hcatchAdj⟩ with
    ⟨a₁, a₂, a₃, b₁, b₂, b₃, -, -, href⟩ | ⟨f, hf, hf2⟩
  · -- *"it contains no reflection of the triangle since there is no antihole of length 6"*
    have hanti := ReflectionAntihole.isAntiholeList_of_reflection href
    have h6 := hG.2 _ hanti
    simp only [holeLength, List.length_cons, List.length_nil] at h6
    omega
  · have := hncard f hf
    omega

/-- **Refutation of the second case of the trichotomy in the proof of 24.4** (printed p. 144).

*"Now suppose the second holds, and for `i = 1,2,3` let `uᵢ, vᵢ, Pᵢ` be as in the second
case. … This is contrary to 17.1."* -/
theorem case2_refute (G : SimpleGraph V) (hG : InF11 G)
    (X : Fin 3 → Set V)
    (hXdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (X i) (X j))
    (hXne : ∀ i : Fin 3, (X i).Nonempty)
    (hXanti : ∀ i : Fin 3, AnticonnectedSet G (X i))
    (hXcomp : ∀ i j : Fin 3, i ≠ j → Complete G (X i) (X j))
    (F : Set V) (hFX : ∀ w ∈ F, ∀ i : Fin 3, w ∉ X i)
    (v u : Fin 3 → V) (P : Fin 3 → List V)
    (hshape : TriangleLegs G F (fun l => {w : V | VertexComplete G w (X l)}) v u P) :
    False := by
  obtain ⟨hvN, huniqN, hP, hPF, hPne, hPadj⟩ := hshape
  have hvc : ∀ i : Fin 3, VertexComplete G (v i) (X i) := fun i => hvN i
  have huniq : ∀ i j : Fin 3, ∀ w ∈ P i, VertexComplete G w (X j) → w = v j :=
    fun i j w hw hcomp => huniqN j w (hPF i w hw) hcomp
  have hPX : ∀ i : Fin 3, ∀ w ∈ P i, ∀ l : Fin 3, w ∉ X l :=
    fun i w hw l => hFX w (hPF i w hw) l
  by_cases hall : ∀ i : Fin 3, v i = u i
  · exact degenerate_case G hG X hXdisj hXanti hXcomp v u P hP hPX hvc huniq hPne hPadj hall
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    have hd : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
    exact core_case G hG X hXdisj hXanti hXcomp v u P hP hPX hvc huniq hPne hPadj
      i (i + 1) (i + 2) (hd i).1 (hd i).2.1 (hd i).2.2 hi

end Main

end Workspace.Types.Thm244Case2
