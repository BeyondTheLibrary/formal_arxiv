import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.StriationCompl
import Workspace.Statements.S09.Thm_9_1

/-!
# Shared striation tools for the proof of 9.6

The proof of claim (3) and the closing paragraph both use the same consequence of 9.1.
For every strip `S i` and antistrip `T j`, some twist contains that pair.  Hence, if one
`T j`-antirung has length greater than one, every `S i`-rung has length one.  The complement
gives the symmetric statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm96StriationTools

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

def leftPart (R : Set V × Set V × Set V) : Set V := R.1
def middlePart (R : Set V × Set V × Set V) : Set V := R.2.1
def rightPart (R : Set V × Set V × Set V) : Set V := R.2.2

theorem stripVertices_eq (R : Set V × Set V × Set V) :
    stripVertices R = leftPart R ∪ rightPart R ∪ middlePart R := by
  obtain ⟨A, C, B⟩ := R
  rfl

theorem left_subset_stripVertices (R : Set V × Set V × Set V) :
    leftPart R ⊆ stripVertices R := by
  obtain ⟨A, C, B⟩ := R
  exact fun _ h => Or.inl (Or.inl h)

theorem right_subset_stripVertices (R : Set V × Set V × Set V) :
    rightPart R ⊆ stripVertices R := by
  obtain ⟨A, C, B⟩ := R
  exact fun _ h => Or.inl (Or.inr h)

theorem middle_subset_stripVertices (R : Set V × Set V × Set V) :
    middlePart R ⊆ stripVertices R := by
  obtain ⟨A, C, B⟩ := R
  exact fun _ h => Or.inr h

theorem left_nonempty {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (hR : IsStrip G R) : (leftPart R).Nonempty := by
  obtain ⟨A, C, B⟩ := R
  exact hR.2.2.2.1

theorem right_nonempty {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (hR : IsStrip G R) : (rightPart R).Nonempty := by
  obtain ⟨A, C, B⟩ := R
  exact hR.2.2.2.2.1

theorem left_right_disjoint {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (hR : IsStrip G R) : Disjoint (leftPart R) (rightPart R) := by
  obtain ⟨A, C, B⟩ := R
  exact hR.1

/-- Every strip contains a distinct left and right end. -/
theorem two_le_strip_ncard [Finite V] {G : SimpleGraph V}
    {R : Set V × Set V × Set V} (hR : IsStrip G R) :
    2 ≤ (stripVertices R).ncard := by
  obtain ⟨x, hx⟩ := left_nonempty hR
  obtain ⟨y, hy⟩ := right_nonempty hR
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Set.disjoint_left.mp (left_right_disjoint hR) hx hy
  have hsub : ({x, y} : Set V) ⊆ stripVertices R := by
    intro z hz
    rcases hz with h | h
    · exact left_subset_stripVertices R (h ▸ hx)
    · exact right_subset_stripVertices R (h ▸ hy)
  rw [← Set.ncard_pair hxy]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- Every vertex of a strip lies on a rung. -/
theorem exists_rung_through {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (hR : IsStrip G R) {v : V} (hv : v ∈ stripVertices R) :
    ∃ p : List V, IsSRung G R p ∧ v ∈ p := by
  obtain ⟨A, C, B⟩ := R
  exact hR.2.2.2.2.2 v hv

/-- Every strip has a rung. -/
theorem exists_rung {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (hR : IsStrip G R) : ∃ p : List V, IsSRung G R p := by
  obtain ⟨a, ha⟩ := left_nonempty hR
  obtain ⟨p, hp, -⟩ := exists_rung_through hR (left_subset_stripVertices R ha)
  exact ⟨p, hp⟩

/-- The vertex set of a rung is connected and is contained in its strip. -/
theorem rung_connected_subset {G : SimpleGraph V} {R : Set V × Set V × Set V}
    {p : List V} (hp : IsSRung G R p) :
    ConnectedSet G {v : V | v ∈ p} ∧ {v : V | v ∈ p} ⊆ stripVertices R := by
  obtain ⟨A, C, B⟩ := R
  obtain ⟨a, b, hab, ha, hb, htail, hdrop, hint⟩ := hp
  refine ⟨InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hab.1, ?_⟩
  intro v hv
  by_cases hva : v = a
  · exact Or.inl (Or.inl (hva ▸ ha))
  by_cases hvb : v = b
  · exact Or.inl (Or.inr (hvb ▸ hb))
  · exact Or.inr (hint v ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hab).2
      ⟨hv, hva, hvb⟩))

/-- If every rung of a strip has length one, its middle set is empty. -/
theorem middle_eq_empty_of_rungs_one {G : SimpleGraph V}
    {R : Set V × Set V × Set V} (hR : IsStrip G R)
    (hone : ∀ p : List V, IsSRung G R p → pathLength p = 1) :
    middlePart R = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro z hz
  obtain ⟨p, hp, hzp⟩ := exists_rung_through hR (middle_subset_stripVertices R hz)
  obtain ⟨A, C, B⟩ := R
  obtain ⟨a, b, hab, ha, hb, htail, hdrop, hint⟩ := hp
  have hzint : z ∈ SPGT.interior p := by
    refine (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hab).2 ⟨hzp, ?_, ?_⟩
    · intro h; subst h; exact (Set.disjoint_left.mp hR.2.1 ha) hz
    · intro h; subst h; exact (Set.disjoint_left.mp hR.2.2.1 hb) hz
  have hlen := Workspace.ProofLemmas.PathBasics.interior_length p
  have hpone := hone p ⟨a, b, hab, ha, hb, htail, hdrop, hint⟩
  simp only [pathLength] at hpone
  have hplen : p.length = 2 := by omega
  rw [hplen] at hlen
  have : (SPGT.interior p).length = 0 := by omega
  rw [List.length_eq_zero_iff.mp this] at hzint
  simpa using hzint

/-- A twist is unchanged when the two strips are exchanged. -/
theorem isTwist_swap {G : SimpleGraph V} {S₁ S₂ T₁ T₂ : Set V × Set V × Set V}
    (h : IsTwist G S₁ S₂ T₁ T₂) : IsTwist G S₂ S₁ T₁ T₂ := by
  simp only [IsTwist, AgreeOn] at h ⊢
  tauto

/-- The row-twist axiom, without an ordering condition on the two row indices. -/
theorem exists_twist_of_ne {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {i i' : Fin m} (hii : i ≠ i') :
    ∃ j j' : Fin n, j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j') := by
  rcases lt_trichotomy i i' with h | h | h
  · exact hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' h
  · exact absurd h hii
  · obtain ⟨j, j', hjj, ht⟩ := hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i' i h
    exact ⟨j, j', hjj, isTwist_swap ht⟩

private theorem twist_partner_abstract {n : ℕ} (Ag Ds : Fin n → Prop)
    (hcover : ∀ k, Ag k ∨ Ds k) {c d : Fin n} (hcd : c ≠ d)
    (htw : (Ag c ∧ Ds d) ∨ (Ag d ∧ Ds c)) (j : Fin n) :
    ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
  have main : ∀ c d : Fin n, c ≠ d → Ag c → Ds d →
      ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
    intro c d hcd hc hd
    by_cases hjd : j = d
    · refine ⟨c, ?_, Or.inr ⟨hc, by rw [hjd]; exact hd⟩⟩
      rw [hjd]
      exact hcd.symm
    · rcases hcover j with hj | hj
      · exact ⟨d, hjd, Or.inl ⟨hj, hd⟩⟩
      · by_cases hjc : j = c
        · exact ⟨d, hjd, Or.inl ⟨by rw [hjc]; exact hc, hd⟩⟩
        · exact ⟨c, hjc, Or.inr ⟨hc, hj⟩⟩
  rcases htw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact main c d hcd h1 h2
  · exact main d c hcd.symm h1 h2

/-- Once a pair of strips has one twist, every antistrip has a twist partner for that pair. -/
theorem twist_partner {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {i i' : Fin m} (hii : i ≠ i') (j : Fin n) :
    ∃ j' : Fin n, j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j') := by
  let Ag : Fin n → Prop := fun k => AgreeOn G (S i) (S i') (T k)
  let Ds : Fin n → Prop := fun k =>
    (ParallelStripAntistrip G (S i) (T k) ∧ CoParallel G (S i') (T k)) ∨
    (CoParallel G (S i) (T k) ∧ ParallelStripAntistrip G (S i') (T k))
  have hcover : ∀ k, Ag k ∨ Ds k := by
    intro k
    rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i k with hi | hi <;>
      rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i' k with hi' | hi'
    · exact Or.inl (Or.inl ⟨hi, hi'⟩)
    · exact Or.inr (Or.inl ⟨hi, hi'⟩)
    · exact Or.inr (Or.inr ⟨hi, hi'⟩)
    · exact Or.inl (Or.inr ⟨hi, hi'⟩)
  obtain ⟨c, d, hcd, htw⟩ := exists_twist_of_ne hL hii
  have htw' : (Ag c ∧ Ds d) ∨ (Ag d ∧ Ds c) := by
    simpa only [Ag, Ds, IsTwist] using htw
  obtain ⟨j', hjj, hjtw⟩ := twist_partner_abstract Ag Ds hcover hcd htw' j
  exact ⟨j', hjj, by simpa only [Ag, Ds, IsTwist] using hjtw⟩

/-- Every strip-antistrip corner belongs to a twist. -/
theorem exists_twist_at_corner {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) (i : Fin m) (j : Fin n) :
    ∃ i' : Fin m, ∃ j' : Fin n,
      i ≠ i' ∧ j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j') := by
  have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  have h0 : 0 < m := by omega
  have h1 : 1 < m := by omega
  obtain ⟨i', hii⟩ : ∃ i' : Fin m, i ≠ i' := by
    by_cases h : i = ⟨0, h0⟩
    · exact ⟨⟨1, h1⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, h0⟩, h⟩
  obtain ⟨j', hjj, htw⟩ := twist_partner hL hii j
  exact ⟨i', j', hii, hjj, htw⟩

/-- PAPER (9.6, claim (3), using 9.1): if one antirung is not a single edge, every rung is. -/
theorem all_rungs_one_of_long_antirung
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hL : IsStriation G S T) {j : Fin n} {Q : List V}
    (hQ : IsSRung Gᶜ (T j) Q) (hQlong : pathLength Q ≠ 1) :
    ∀ (i : Fin m) (P : List V), IsSRung G (S i) P → pathLength P = 1 := by
  intro i P hP
  obtain ⟨i', j', hii, hjj, htw⟩ := exists_twist_at_corner hL i j
  obtain ⟨P', hP'⟩ := exists_rung (hL.1 i')
  obtain ⟨Q', hQ'⟩ := exists_rung (hL.2.1 j')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    Workspace.ProofLemmas.KnotFromTwist.exists_knot_of_twist hL hii hjj htw hP hP' hQ hQ'
  rcases (_root_.Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot).2 with h | h
  · rcases eP₁ with rfl | rfl
    · exact h.1
    · simpa only [Workspace.ProofLemmas.PathBasics.pathLength_reverse] using h.1
  · have hQ₁one : pathLength Q₁ = 1 := h.1
    rcases eQ₁ with rfl | rfl
    · exact absurd hQ₁one hQlong
    · rw [Workspace.ProofLemmas.PathBasics.pathLength_reverse] at hQ₁one
      exact absurd hQ₁one hQlong

/-- The complement of `all_rungs_one_of_long_antirung`. -/
theorem all_antirungs_one_of_long_rung
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hL : IsStriation G S T) {i : Fin m} {P : List V}
    (hP : IsSRung G (S i) P) (hPlong : pathLength P ≠ 1) :
    ∀ (j : Fin n) (Q : List V), IsSRung Gᶜ (T j) Q → pathLength Q = 1 := by
  have hGc : Berge Gᶜ := Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hLc : IsStriation Gᶜ T S := Workspace.ProofLemmas.StriationCompl.isStriation_compl hL
  intro j Q hQ
  have hP' : IsSRung (Gᶜ)ᶜ (S i) P := by
    rwa [compl_compl]
  exact all_rungs_one_of_long_antirung hGc hLc hP' hPlong j Q hQ

/-- A two-vertex strip has no middle vertex, so each of its odd rungs is one edge. -/
theorem rung_one_of_strip_ncard_two [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S₀ : Set V × Set V × Set V}
    (hS : IsStrip G S₀) (hcard : (stripVertices S₀).ncard = 2)
    (hodd : ∀ p : List V, IsSRung G S₀ p → Odd (pathLength p))
    {p : List V} (hp : IsSRung G S₀ p) : pathLength p = 1 := by
  obtain ⟨A, C, B⟩ := S₀
  obtain ⟨hAB, hAC, hBC, ⟨x, hx⟩, ⟨y, hy⟩, -⟩ := hS
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Set.disjoint_left.mp hAB hx hy
  have hpair : ({x, y} : Set V) ⊆ A ∪ B ∪ C := by
    intro z hz
    rcases hz with h | h
    · exact Or.inl (Or.inl (h ▸ hx))
    · exact Or.inl (Or.inr (h ▸ hy))
  have hcard' : (A ∪ B ∪ C).ncard = 2 := by
    simpa only [stripVertices] using hcard
  have hwhole : A ∪ B ∪ C = ({x, y} : Set V) :=
    (Set.eq_of_subset_of_ncard_le hpair
      (le_of_eq (by rw [hcard', Set.ncard_pair hxy])) (Set.toFinite _)).symm
  have hCempty : C = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun z hz => ?_)
    have hzpair : z ∈ ({x, y} : Set V) := by
      rw [← hwhole]
      exact Or.inr hz
    rcases hzpair with hzx | hzy
    · subst z
      exact Set.disjoint_left.mp hAC hx hz
    · subst z
      exact Set.disjoint_left.mp hBC hy hz
  obtain ⟨a, b, hpab, ha, hb, htail, hdrop, hint⟩ := hp
  have hinterior : (SPGT.interior p).length = 0 := by
    rcases hq : SPGT.interior p with _ | ⟨w, ws⟩
    · simp
    · exfalso
      have hw : w ∈ SPGT.interior p := by rw [hq]; simp
      have hwC := hint w hw
      rw [hCempty] at hwC
      exact hwC
  have hpodd := hodd p ⟨a, b, hpab, ha, hb, htail, hdrop, hint⟩
  rw [Workspace.ProofLemmas.PathBasics.interior_length] at hinterior
  have hplen := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hpab.1
  rw [Nat.odd_iff] at hpodd
  omega

/-- PAPER (9.6, closing paragraph): a middle vertex of an antistrip is complete to every
vertex of each strip.  The antirung through the middle vertex is long, so 9.1 makes all
rungs single edges. -/
theorem middle_vertex_complete_strip
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hL : IsStriation G S T) (i : Fin m) (j : Fin n)
    {z : V} (hz : z ∈ middlePart (T j)) :
    ∀ v ∈ stripVertices (S i), G.Adj z v := by
  obtain ⟨Q, hQ, hzQ⟩ := exists_rung_through (hL.2.1 j)
    (middle_subset_stripVertices _ hz)
  obtain ⟨c, d, hQcd, hc, hd, hQtail, hQdrop, hQint⟩ := hQ
  have hzc : z ≠ c := by
    intro h
    subst c
    obtain ⟨X, Z, Y⟩ := T j
    exact Set.disjoint_left.mp (hL.2.1 j).2.1 hc hz
  have hzd : z ≠ d := by
    intro h
    subst d
    obtain ⟨X, Z, Y⟩ := T j
    exact Set.disjoint_left.mp (hL.2.1 j).2.2.1 hd hz
  have hzint : z ∈ SPGT.interior Q :=
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQcd).mpr
      ⟨hzQ, hzc, hzd⟩
  have hQlong : pathLength Q ≠ 1 := by
    intro hone
    have hpos := List.length_pos_of_mem hzint
    rw [Workspace.ProofLemmas.PathBasics.interior_length] at hpos
    have hlen := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hQcd.1
    omega
  have hSedge := all_rungs_one_of_long_antirung hG hL
    ⟨c, d, hQcd, hc, hd, hQtail, hQdrop, hQint⟩ hQlong
  intro v hv
  obtain ⟨P, hP, hvP⟩ := exists_rung_through (hL.1 i) hv
  obtain ⟨a, b, hPab, ha, hb, hPtail, hPdrop, hPint⟩ := hP
  have hPone := hSedge i P ⟨a, b, hPab, ha, hb, hPtail, hPdrop, hPint⟩
  have hPlen : P.length = 2 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hPone
    omega
  obtain ⟨x, y, hPxy⟩ := Workspace.ProofLemmas.PrismBasics.length_eq_two hPlen
  have hxa : x = a := by rw [hPxy] at hPab; simpa using hPab.2.1
  have hyb : y = b := by rw [hPxy] at hPab; simpa using hPab.2.2
  rw [hPxy, hxa, hyb] at hvP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvP
  rcases hvP with hva | hvb
  · subst v
    rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i j with hp | hcpar
    · exact (hp.1.1 a ha z (Set.mem_union_right _ hz)).symm
    · exact (hcpar.1.1 a ha z (Set.mem_union_right _ hz)).symm
  · subst v
    rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i j with hp | hcpar
    · exact (hp.1.2 b hb z (Set.mem_union_right _ hz)).symm
    · exact (hcpar.1.2 b hb z (Set.mem_union_right _ hz)).symm

end Workspace.ProofLemmas.Thm96StriationTools
