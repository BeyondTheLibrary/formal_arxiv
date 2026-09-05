import Workspace.ProofLemmas.TwoConnectedDisjointPaths
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Connectivity58Skeleton

/-!
# Splitting a vertex, and the two disjoint paths of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"(To see this, divide `u` into two adjacent vertices,
one incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)"*

The paper splits `u`; here we do the dual bookkeeping, which needs only one new vertex.  Delete
from `J` every edge at `u` except the two chosen ones, and add one new vertex joined to the two
ends `a`, `b` of the prescribed edge.  In the resulting graph no single vertex is a cutvertex,
so `TwoConnectedDisjointPaths.exists_two_tracks` gives two tracks from `u` to the new vertex
meeting only at their ends.  Removing the new vertex leaves exactly the two vertex-disjoint
paths the paper asks for: one leaving `u` along the first chosen edge and ending at one of
`a`, `b`, the other leaving along the second and ending at the other.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.TwoConnectedSplitVertex

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.TwoConnectedDisjointPaths

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The auxiliary graph. -/
def splitGraph (J : SimpleGraph U) (u x y a b : U) : SimpleGraph (Option U) where
  Adj P R :=
    match P, R with
    | some p, some r => J.Adj p r ∧ (p = u → r = x ∨ r = y) ∧ (r = u → p = x ∨ p = y)
    | some p, none   => p = a ∨ p = b
    | none, some r   => r = a ∨ r = b
    | none, none     => False
  symm := by
    rintro (_ | p) (_ | r) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    rintro (_ | p) h
    · exact h
    · exact h.1.ne rfl

theorem splitGraph_adj_some {J : SimpleGraph U} {u x y a b p r : U} :
    (splitGraph J u x y a b).Adj (some p) (some r) ↔
      J.Adj p r ∧ (p = u → r = x ∨ r = y) ∧ (r = u → p = x ∨ p = y) := Iff.rfl

theorem splitGraph_adj_none {J : SimpleGraph U} {u x y a b r : U} :
    (splitGraph J u x y a b).Adj none (some r) ↔ (r = a ∨ r = b) := Iff.rfl

theorem splitGraph_adj_none' {J : SimpleGraph U} {u x y a b p : U} :
    (splitGraph J u x y a b).Adj (some p) none ↔ (p = a ∨ p = b) := Iff.rfl

variable {J : SimpleGraph U}

/-- Every vertex of the auxiliary graph has two distinct neighbours. -/
theorem split_hdeg (hJ : IsKConnected J 3) {u x y a b : U}
    (hux : J.Adj u x) (huy : J.Adj u y) (hxy : x ≠ y) (hab : J.Adj a b) :
    ∀ X Y : Option U, ∃ p, (splitGraph J u x y a b).Adj X p ∧ p ≠ Y := by
  have hxu : x ≠ u := hux.ne'
  have hyu : y ≠ u := huy.ne'
  rintro (_ | p) Y
  · rcases Y with _ | t
    · exact ⟨some a, Or.inl rfl, by simp⟩
    · by_cases ht : t = a
      · exact ⟨some b, Or.inr rfl, by
          simp only [ne_eq, Option.some.injEq]
          rw [ht]; exact hab.ne'⟩
      · exact ⟨some a, Or.inl rfl, by
          simp only [ne_eq, Option.some.injEq]
          exact fun hh => ht hh.symm⟩
  · by_cases hpu : p = u
    · subst hpu
      have hAx : (splitGraph J p x y a b).Adj (some p) (some x) :=
        ⟨hux, fun _ => Or.inl rfl, fun hh => absurd hh hxu⟩
      have hAy : (splitGraph J p x y a b).Adj (some p) (some y) :=
        ⟨huy, fun _ => Or.inr rfl, fun hh => absurd hh hyu⟩
      rcases Y with _ | t
      · exact ⟨some x, hAx, by simp⟩
      · by_cases ht : t = x
        · exact ⟨some y, hAy, by
            simp only [ne_eq, Option.some.injEq]
            rw [ht]; exact fun hh => hxy hh.symm⟩
        · exact ⟨some x, hAx, by
            simp only [ne_eq, Option.some.injEq]
            exact fun hh => ht hh.symm⟩
    · obtain ⟨r, hpr, hru, hrt⟩ :=
        Connectivity58Skeleton.exists_third_neighbor hJ p u
          (match Y with | none => u | some t => t)
      refine ⟨some r, ⟨hpr, fun hh => absurd hh hpu, fun hh => absurd hh hru⟩, ?_⟩
      rcases Y with _ | t
      · simp
      · simp only [ne_eq, Option.some.injEq]
        exact hrt

/-- Deleting one vertex of the auxiliary graph leaves the rest connected. -/
theorem split_nocut (hJ : IsKConnected J 3) {u x y a b : U}
    (hux : J.Adj u x) (huy : J.Adj u y) (hxy : x ≠ y)
    (hab : J.Adj a b) (hau : a ≠ u) (hbu : b ≠ u) :
    NoCutvertex (splitGraph J u x y a b) := by
  classical
  intro Z Pv Rv hPZ hRZ
  set Γ := splitGraph J u x y a b with hΓ
  set X : Set (Option U) := ({Z}ᶜ : Set (Option U)) with hX
  obtain ⟨w, hZw, hZw'⟩ : ∃ w : U, (∀ p : U, p ≠ w → some p ≠ Z) ∧
      (∀ p : U, p = w → p ≠ u → some p = Z) := by
    rcases Z with _ | t
    · exact ⟨u, fun p _ => by simp, fun p hp hpu => absurd hp hpu⟩
    · exact ⟨t, fun p hp => by simpa using hp, fun p hp _ => by rw [hp]⟩
  have hmemX : ∀ p : U, p ≠ w → some p ∈ X := fun p hp => hZw p hp
  -- reachability inside `J` with `u` and `w` removed
  have key : ∀ p r : U, p ≠ u → p ≠ w → r ≠ u → r ≠ w → RchIn Γ X (some p) (some r) := by
    intro p r hpu hpw hru hrw
    have hcard : ({u, w} : Set U).ncard < 3 := by
      have h1 := Set.ncard_insert_le u ({w} : Set U)
      have h2 := Set.ncard_singleton w
      omega
    have hconn := hJ.2 ({u, w} : Set U) hcard
    have hpm : p ∈ ({u, w} : Set U)ᶜ := by rintro (h | h); exacts [hpu h, hpw h]
    have hrm : r ∈ ({u, w} : Set U)ᶜ := by rintro (h | h); exacts [hru h, hrw h]
    obtain ⟨wk⟩ := hconn.preconnected ⟨p, hpm⟩ ⟨r, hrm⟩
    refine rchIn_of_walk (K := (J.induce (({u, w} : Set U)ᶜ))) (fun z => some z.val)
      (fun z => hmemX z.val (fun hh => z.2 (Or.inr hh))) ?_ wk
    intro z z' hzz'
    refine RchIn.of_adj (hmemX z.val (fun hh => z.2 (Or.inr hh)))
      (hmemX z'.val (fun hh => z'.2 (Or.inr hh))) ?_
    exact ⟨hzz', fun hh => absurd hh (fun hh2 => z.2 (Or.inl hh2)),
      fun hh => absurd hh (fun hh2 => z'.2 (Or.inl hh2))⟩
  -- an anchor: one of the two ends of the prescribed edge survives
  obtain ⟨c₀, hc₀ab, hc₀w⟩ : ∃ c₀ : U, (c₀ = a ∨ c₀ = b) ∧ c₀ ≠ w := by
    by_cases hh : a = w
    · exact ⟨b, Or.inr rfl, fun hh2 => hab.ne (hh.trans hh2.symm)⟩
    · exact ⟨a, Or.inl rfl, hh⟩
  have hc₀u : c₀ ≠ u := by rcases hc₀ab with rfl | rfl; exacts [hau, hbu]
  have conn : ∀ V : Option U, V ≠ Z → RchIn Γ X V (some c₀) := by
    rintro (_ | p) hV
    · refine RchIn.of_adj hV (hmemX c₀ hc₀w) ?_
      exact hc₀ab
    · by_cases hpu : p = u
      · subst hpu
        obtain ⟨x', hx'xy, hx'w⟩ : ∃ x' : U, (x' = x ∨ x' = y) ∧ x' ≠ w := by
          by_cases hh : x = w
          · exact ⟨y, Or.inr rfl, fun hh2 => hxy (hh.trans hh2.symm)⟩
          · exact ⟨x, Or.inl rfl, hh⟩
        have hx'u : x' ≠ p := by rcases hx'xy with rfl | rfl; exacts [hux.ne', huy.ne']
        have hadj : Γ.Adj (some p) (some x') := by
          rcases hx'xy with rfl | rfl
          · exact ⟨hux, fun _ => Or.inl rfl, fun hh => absurd hh hx'u⟩
          · exact ⟨huy, fun _ => Or.inr rfl, fun hh => absurd hh hx'u⟩
        exact (RchIn.of_adj hV (hmemX x' hx'w) hadj).trans (key x' c₀ hx'u hx'w hc₀u hc₀w)
      · have hpw : p ≠ w := fun hh => hV (hZw' p hh hpu)
        exact key p c₀ hpu hpw hc₀u hc₀w
  exact (conn Pv hPZ).trans (conn Rv hRZ).symm


/-- Reading a track of the auxiliary graph from `u` to the new vertex back as a track of `J`
out of `u`. -/
private theorem decode {u x y a b : U} {Pp : List (Option U)}
    (hau : a ≠ u) (hbu : b ≠ u)
    (hP : IsTrackFrom (splitGraph J u x y a b) Pp (some u) none) :
    ∃ (t : List U) (t1 e : U),
      IsTrackFrom J t u e ∧ 2 ≤ t.length ∧ (e = a ∨ e = b) ∧ (t1 = x ∨ t1 = y) ∧
      t[1]? = some t1 ∧ 3 ≤ Pp.length ∧ Pp[1]? = some (some t1) ∧
      Pp[Pp.length - 2]? = some (some e) ∧
      (∀ z : U, z ∈ t → some z ∈ Pp) := by
  classical
  set Γ := splitGraph J u x y a b with hΓ
  have hnd : Pp.Nodup := hP.1.2.1
  have hne : 0 < Pp.length := List.length_pos_of_ne_nil hP.1.1
  have hP0 : Pp[0]'hne = some u := SubdivisionCounting.track_head hP hne
  have hPl : Pp[Pp.length - 1]'(by omega) = none := by
    have h' := hP.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : Pp.length - 1 < Pp.length)] at h'
    exact Option.some_injective _ h'
  have hlen2 : 2 ≤ Pp.length := by
    by_contra hc
    have : (0 : ℕ) = Pp.length - 1 := by omega
    rw [SubdivisionCounting.getElem_eq_of_index_eq Pp this hne (by omega), hPl] at hP0
    exact absurd hP0.symm (by simp)
  have hlen3 : 3 ≤ Pp.length := by
    by_contra hc
    have hh := hP.1.2.2 0 (by omega)
    rw [hP0, SubdivisionCounting.getElem_eq_of_index_eq Pp
      (show (1:ℕ) = Pp.length - 1 by omega) (by omega) (by omega), hPl] at hh
    rcases hh with h | h
    · exact hau h.symm
    · exact hbu h.symm
  -- no `none` before the last position
  have hnone : ∀ (k : ℕ) (hk : k < Pp.length - 1), Pp[k]'(by omega) ≠ none := by
    intro k hk hc
    have := hnd.getElem_inj_iff (hi := (by omega : k < Pp.length))
      (hj := (by omega : Pp.length - 1 < Pp.length)) |>.mp (by rw [hc, hPl])
    omega
  have hnotnone : ∀ o ∈ Pp.dropLast, o ≠ none := by
    intro o ho
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ho
    rw [List.length_dropLast] at hk
    rw [List.getElem_dropLast]
    exact hnone k (by omega)
  have htlen0 : (Pp.dropLast.map (fun o : Option U => o.getD u)).length = Pp.length - 1 := by
    simp
  have htget0 : ∀ (k : ℕ) (hk : k < (Pp.dropLast.map (fun o : Option U => o.getD u)).length),
      (Pp.dropLast.map (fun o : Option U => o.getD u))[k]'hk
        = (Pp[k]'(by omega)).getD u := by
    intro k hk
    rw [List.getElem_map, List.getElem_dropLast]
  set t : List U := Pp.dropLast.map (fun o : Option U => o.getD u) with htdef
  have htlen : t.length = Pp.length - 1 := htlen0
  have hsome : ∀ (k : ℕ) (hk : k < t.length),
      Pp[k]'(by omega) = some (t[k]'hk) := by
    intro k hk
    rw [htget0 k hk]
    have h2 := hnone k (by omega)
    cases hh : Pp[k]'(by omega : k < Pp.length) with
    | none => exact absurd hh h2
    | some v => rfl
  have htnd : t.Nodup := by
    rw [htdef]
    refine List.Nodup.map_on ?_ (List.Nodup.sublist (List.dropLast_sublist _) hnd)
    intro o ho o' ho' heq
    cases o with
    | none => exact absurd rfl (hnotnone _ ho)
    | some v =>
      cases o' with
      | none => exact absurd rfl (hnotnone _ ho')
      | some v' => simpa using heq
  have htadj : ∀ (k : ℕ) (hk : k + 1 < t.length),
      J.Adj (t[k]'(by omega)) (t[k+1]'hk) := by
    intro k hk
    have hh := hP.1.2.2 k (by omega)
    rw [hsome k (by omega), hsome (k+1) hk] at hh
    exact hh.1
  have ht0 : t[0]'(by omega) = u := by
    have := hsome 0 (by omega)
    rw [hP0] at this
    exact (Option.some_injective _ this).symm
  set e : U := t[t.length - 1]'(by omega) with hedef
  have htrack : IsTrackFrom J t u e := by
    refine ⟨⟨by intro hc; rw [hc] at htlen; simp at htlen; omega, htnd, htadj⟩, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < t.length), ht0]
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega : t.length - 1 < t.length)]
  have hPe : Pp[Pp.length - 2]'(by omega) = some e := by
    rw [hedef]
    have := hsome (t.length - 1) (by omega)
    rw [SubdivisionCounting.getElem_eq_of_index_eq Pp
      (show Pp.length - 2 = t.length - 1 by omega) (by omega) (by omega)]
    exact this
  have hea : e = a ∨ e = b := by
    have hh := hP.1.2.2 (Pp.length - 2) (by omega)
    rw [hPe, SubdivisionCounting.getElem_eq_of_index_eq Pp
      (show Pp.length - 2 + 1 = Pp.length - 1 by omega) (by omega) (by omega), hPl] at hh
    exact hh
  set t1 : U := t[1]'(by omega) with ht1def
  have hP1 : Pp[1]'(by omega) = some t1 := hsome 1 (by omega)
  have ht1 : t1 = x ∨ t1 = y := by
    have hh := hP.1.2.2 0 (by omega)
    rw [hP0, hP1] at hh
    exact hh.2.1 rfl
  refine ⟨t, t1, e, htrack, by omega, hea, ht1, ?_, hlen3, ?_, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem (by omega : 1 < t.length)]
  · rw [List.getElem?_eq_getElem (by omega : 1 < Pp.length), hP1]
  · rw [List.getElem?_eq_getElem (by omega : Pp.length - 2 < Pp.length), hPe]
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [← hsome k hk]
    exact List.getElem_mem _


/-- **The two vertex-disjoint paths of 5.8 (6).**  In a 3-connected graph, a vertex `u` with two
distinct neighbours `x`, `y` and an edge `ab` avoiding `u` admit two tracks out of `u`, one
starting along `ux` and one along `uy`, meeting only at `u`, and ending at `a` and `b` in one
order or the other. -/
theorem exists_split_tracks (hJ : IsKConnected J 3) {u x y a b : U}
    (hux : J.Adj u x) (huy : J.Adj u y) (hxy : x ≠ y)
    (hab : J.Adj a b) (hau : a ≠ u) (hbu : b ≠ u) :
    ∃ (tA tB : List U) (a' b' : U),
      ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
      IsTrackFrom J tA u a' ∧ IsTrackFrom J tB u b' ∧
      2 ≤ tA.length ∧ 2 ≤ tB.length ∧
      (∀ z ∈ tA, z ∈ tB → z = u) ∧
      ((tA[1]? = some x ∧ tB[1]? = some y) ∨ (tA[1]? = some y ∧ tB[1]? = some x)) := by
  classical
  obtain ⟨Pp, Rr, hPt, hRt, hdisj⟩ :=
    exists_two_tracks (split_nocut hJ hux huy hxy hab hau hbu)
      (split_hdeg hJ hux huy hxy hab) (u := (some u : Option U)) (v := (none : Option U))
      (by simp)
  obtain ⟨tA, tA1, eA, hA, hA2, heA, htA1, hAget, -, -, -, hAsub⟩ := decode hau hbu hPt
  obtain ⟨tB, tB1, eB, hB, hB2, heB, htB1, hBget, -, -, -, hBsub⟩ := decode hau hbu hRt
  have hmeet : ∀ z ∈ tA, z ∈ tB → z = u := by
    intro z hz hz'
    rcases hdisj (some z) (hAsub z hz) (hBsub z hz') with hh | hh
    · exact Option.some_injective _ hh
    · exact absurd hh (by simp)
  have hA0 : tA[0]'(by omega) = u := SubdivisionCounting.track_head hA (by omega)
  have hB0 : tB[0]'(by omega) = u := SubdivisionCounting.track_head hB (by omega)
  have hA1v : tA[1]'(by omega) = tA1 := by
    rw [List.getElem?_eq_getElem (by omega : 1 < tA.length)] at hAget
    exact Option.some_injective _ hAget
  have hB1v : tB[1]'(by omega) = tB1 := by
    rw [List.getElem?_eq_getElem (by omega : 1 < tB.length)] at hBget
    exact Option.some_injective _ hBget
  have hA1mem : tA1 ∈ tA := hA1v ▸ List.getElem_mem _
  have hB1mem : tB1 ∈ tB := hB1v ▸ List.getElem_mem _
  have hAemem : eA ∈ tA := by
    have := hA.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : tA.length - 1 < tA.length)] at this
    exact (Option.some_injective _ this) ▸ List.getElem_mem _
  have hBemem : eB ∈ tB := by
    have := hB.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : tB.length - 1 < tB.length)] at this
    exact (Option.some_injective _ this) ▸ List.getElem_mem _
  have hne1 : tA1 ≠ tB1 := by
    intro hh
    have hu : tA1 = u := hmeet tA1 hA1mem (hh ▸ hB1mem)
    have : (1 : ℕ) = 0 :=
      hA.1.2.1.getElem_inj_iff (hi := (by omega : 1 < tA.length))
        (hj := (by omega : 0 < tA.length)) |>.mp (by rw [hA1v, hA0, hu])
    omega
  have hnee : eA ≠ eB := by
    intro hh
    have hu : eA = u := hmeet eA hAemem (hh ▸ hBemem)
    rcases heA with h | h
    · exact hau (h ▸ hu)
    · exact hbu (h ▸ hu)
  have hpair : (eA = a ∧ eB = b) ∨ (eA = b ∧ eB = a) := by
    rcases heA with h | h <;> rcases heB with h' | h'
    · exact absurd (h.trans h'.symm) hnee
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
    · exact absurd (h.trans h'.symm) hnee
  refine ⟨tA, tB, eA, eB, hpair, hA, hB, hA2, hB2, hmeet, ?_⟩
  rcases htA1 with h | h <;> rcases htB1 with h' | h'
  · exact absurd (h.trans h'.symm) hne1
  · exact Or.inl ⟨by rw [hAget, h], by rw [hBget, h']⟩
  · exact Or.inr ⟨by rw [hAget, h], by rw [hBget, h']⟩
  · exact absurd (h.trans h'.symm) hne1


end Workspace.ProofLemmas.TwoConnectedSplitVertex
