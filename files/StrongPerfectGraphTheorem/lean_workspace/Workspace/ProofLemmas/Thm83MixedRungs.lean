import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# The implicit step in the printed proof of 8.3

The paper prints no argument for the bold sentence; the route recorded in the frozen module's
own docstring is followed here, in its contrapositive form.  See the report for the step-by-step
correspondence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm83MixedRungs

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

section Aux

variable {W : Type*}

theorem subsingleton_setOf_mem_of_length_one {l : List W} (h : l.length = 1) :
    {z : W | z ∈ l}.Subsingleton := by
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  have : i = 0 := by omega
  have : j = 0 := by omega
  simp_all

theorem length_one_of_subsingleton_setOf_mem {l : List W} (hne : l ≠ []) (hnd : l.Nodup)
    (hs : {z : W | z ∈ l}.Subsingleton) : l.length = 1 := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hne
  by_contra hcon
  have h2 : 2 ≤ l.length := by omega
  have h0 : l[0]'(by omega) ∈ l := List.getElem_mem _
  have h1 : l[1]'(by omega) ∈ l := List.getElem_mem _
  have := hs h0 h1
  have := hnd.getElem_inj_iff.mp this
  omega

theorem trackEdges_pair (x y : W) : trackEdges [x, y] = ({s(x, y)} : Set (Sym2 W)) := by
  ext e
  simp only [trackEdges, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

theorem trackEdges_subset_edgeSet {H : SimpleGraph W} {q : List W}
    (hq : IsTrackList H q) : trackEdges q ⊆ H.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact hq.2.2 i hi

theorem length_le_two_of_trackEdges_subsingleton {H : SimpleGraph W} {q : List W}
    (hq : IsTrackList H q) (hs : (trackEdges q).Subsingleton) : q.length ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ q.length := by omega
  have h1 : s(q[0]'(by omega), q[1]'(by omega)) ∈ trackEdges q := ⟨0, by omega, rfl⟩
  have h2 : s(q[1]'(by omega), q[2]'(by omega)) ∈ trackEdges q := ⟨1, by omega, rfl⟩
  have he := hs h1 h2
  rcases Sym2.eq_iff.mp he with ⟨e1, -⟩ | ⟨e1, -⟩
  · exact absurd (hq.2.1.getElem_inj_iff.mp e1) (by omega)
  · exact absurd (hq.2.1.getElem_inj_iff.mp e1) (by omega)

theorem eq_pair_of_length_two {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hlen : q.length = 2) : q = [a, b] := by
  have h0 := SubdivisionCounting.track_head hq (by omega)
  have h1 := SubdivisionCounting.track_last hq hlen
  refine List.ext_getElem (by simp [hlen]) ?_
  intro i hi hi'
  simp only [List.length_cons, List.length_nil] at hi'
  interval_cases i
  · simpa using h0
  · simpa using h1

theorem two_le_length_of_trackFrom_ne {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hab : a ≠ b) : 2 ≤ q.length := by
  by_contra hcon
  have hne : q ≠ [] := hq.1.1
  have hpos : 0 < q.length := List.length_pos_of_ne_nil hne
  have hlen : q.length = 1 := by omega
  have h0 : q[0]'(by omega) = a := SubdivisionCounting.track_head hq (by omega)
  have hlast : q.getLast? = some (q[0]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, show q.length - 1 = 0 from by omega,
      List.getElem?_eq_getElem (by omega)]
  rw [hq.2.2] at hlast
  exact hab (h0 ▸ (Option.some_injective _ hlast).symm ▸ rfl)

theorem trackInterior_eq_nil_of_length_le_two {q : List W} (h : q.length ≤ 2) :
    trackInterior q = [] := by
  have : (trackInterior q).length = 0 := by
    simp only [trackInterior, List.length_dropLast, List.length_tail]
    omega
  exact List.eq_nil_of_length_eq_zero this

theorem three_le_length_of_mem_trackInterior {q : List W} {w : W}
    (h : w ∈ trackInterior q) : 3 ≤ q.length := by
  rw [SubdivisionCounting.mem_trackInterior_iff] at h
  obtain ⟨j, hj, -⟩ := h
  omega

end Aux

section Core

/-- The rung/branch dictionary in the form the proof of 8.3 needs: the branch `B u v` is a
single edge exactly when the rung `R u v` has length `0`. -/
theorem dict {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V) (hForms : FormsLineGraph G J S N R H) :
    ∃ (ι : U → W) (B : U → U → List W),
      Function.Injective ι ∧ Set.range ι = branchVertices H ∧
      (∀ u v : U, J.Adj u v → IsBranch H (B u v) ∧ IsTrackFrom H (B u v) (ι u) (ι v)) ∧
      (∀ u v : U, J.Adj u v → (pathLength (R u v) = 0 ↔ B u v = [ι u, ι v])) ∧
      (∀ q : List W, IsBranch H q →
        ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (B u v)) := by
  classical
  obtain ⟨φ⟩ := hForms.2.2
  obtain ⟨ι, B, hιinj, hrange, hbranch, himg, hsurj⟩ :=
    Thm84BranchRungDictionaryAt.branchRungDictionaryAt G J hJ S N hSN H R hForms φ
  refine ⟨ι, B, hιinj, hrange, hbranch, ?_, hsurj⟩
  intro u v huv
  obtain ⟨-, s, t, hpath, -, -, -⟩ := hForms.1 u v huv
  have hRne : R u v ≠ [] := hpath.1.1
  have hRnd : (R u v).Nodup := hpath.1.2.1
  have hιne : ι u ≠ ι v := fun h => huv.ne (hιinj h)
  have htrack : IsTrackList H (B u v) := (hbranch u v huv).2.1
  have h2le : 2 ≤ (B u v).length := two_le_length_of_trackFrom_ne (hbranch u v huv).2 hιne
  have hsub := himg u v huv
  constructor
  · intro hzero
    have hlen1 : (R u v).length = 1 := by
      have hp : 0 < (R u v).length := List.length_pos_of_ne_nil hRne
      simp only [pathLength] at hzero
      omega
    have hRsub : {z : V | z ∈ R u v}.Subsingleton := subsingleton_setOf_mem_of_length_one hlen1
    have hEsub : (trackEdges (B u v)).Subsingleton := by
      intro e₁ h₁ e₂ h₂
      have he₁ : e₁ ∈ H.edgeSet := trackEdges_subset_edgeSet htrack h₁
      have he₂ : e₂ ∈ H.edgeSet := trackEdges_subset_edgeSet htrack h₂
      have hm₁ : (↑(φ ⟨e₁, he₁⟩) : V) ∈ {z : V | z ∈ R u v} := by
        rw [← hsub]; exact ⟨e₁, he₁, h₁, rfl⟩
      have hm₂ : (↑(φ ⟨e₂, he₂⟩) : V) ∈ {z : V | z ∈ R u v} := by
        rw [← hsub]; exact ⟨e₂, he₂, h₂, rfl⟩
      exact congrArg Subtype.val (φ.injective (Subtype.ext (hRsub hm₁ hm₂)))
    have hle := length_le_two_of_trackEdges_subsingleton htrack hEsub
    exact eq_pair_of_length_two (hbranch u v huv).2 (by omega)
  · intro hpair
    have hE : trackEdges (B u v) = ({s(ι u, ι v)} : Set (Sym2 W)) := by
      rw [hpair]; exact trackEdges_pair _ _
    have hRsub : {z : V | z ∈ R u v}.Subsingleton := by
      rw [← hsub]
      rintro x ⟨e₁, he₁, hm₁, rfl⟩ y ⟨e₂, he₂, hm₂, rfl⟩
      rw [hE, Set.mem_singleton_iff] at hm₁ hm₂
      subst hm₁
      subst hm₂
      rfl
    have := length_one_of_subsingleton_setOf_mem hRne hRnd hRsub
    simp only [pathLength, this]

/-- A rung of length `0` makes its branch a single edge, hence an edge of `H` between the two
branch-vertices attached to the ends of the corresponding edge of `J`. -/
theorem zero_rung_to_adj {V U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {R : U → U → List V} {ι : U → W} {B : U → U → List W}
    (hbranch : ∀ u v : U, J.Adj u v → IsBranch H (B u v) ∧ IsTrackFrom H (B u v) (ι u) (ι v))
    (hdict : ∀ u v : U, J.Adj u v → (pathLength (R u v) = 0 ↔ B u v = [ι u, ι v]))
    {u v : U} (huv : J.Adj u v) (h : pathLength (R u v) = 0) : H.Adj (ι u) (ι v) := by
  have hpair := (hdict u v huv).mp h
  have htl : IsTrackList H (B u v) := (hbranch u v huv).2.1
  rw [hpair] at htl
  simpa using htl.2.2 0 (by simp)

/-- Conversely, an edge of `H` joining two branch-vertices is a branch of `H`, hence carries a
rung of length `0`. -/
theorem edge_to_zero_rung {V U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {R : U → U → List V} {ι : U → W} {B : U → U → List W}
    (hbranch : ∀ u v : U, J.Adj u v → IsBranch H (B u v) ∧ IsTrackFrom H (B u v) (ι u) (ι v))
    (hdict : ∀ u v : U, J.Adj u v → (pathLength (R u v) = 0 ↔ B u v = [ι u, ι v]))
    (hsurj : ∀ q : List W, IsBranch H q →
      ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (B u v))
    (hιinj : Function.Injective ι)
    {x y : W} (hxy : H.Adj x y) (hx : x ∈ branchVertices H) (hy : y ∈ branchVertices H) :
    ∃ p q : U, J.Adj p q ∧ pathLength (R p q) = 0 ∧ s(ι p, ι q) = s(x, y) := by
  have hne : x ≠ y := hxy.ne
  have htrackxy : IsTrackFrom H [x, y] x y := by
    refine ⟨⟨by simp, by simp [hne], ?_⟩, rfl, rfl⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    simpa using hxy
  have hbr : IsBranch H [x, y] := by
    refine Thm82BranchDelta.isBranch_of_ends_branch htrackxy hne ?_ hx hy
    intro w hw
    simp [trackInterior] at hw
  obtain ⟨p, q, hpq, hEeq⟩ := hsurj [x, y] hbr
  have hE : trackEdges (B p q) = ({s(x, y)} : Set (Sym2 W)) := by
    rw [← hEeq, trackEdges_pair]
  have hsub : (trackEdges (B p q)).Subsingleton := by
    rw [hE]; exact Set.subsingleton_singleton
  have hle := length_le_two_of_trackEdges_subsingleton (hbranch p q hpq).2.1 hsub
  have hιne : ι p ≠ ι q := fun h => hpq.ne (hιinj h)
  have h2 := two_le_length_of_trackFrom_ne (hbranch p q hpq).2 hιne
  have hpair : B p q = [ι p, ι q] := eq_pair_of_length_two (hbranch p q hpq).2 (by omega)
  refine ⟨p, q, hpq, (hdict p q hpq).mpr hpair, ?_⟩
  rw [hpair, trackEdges_pair] at hE
  exact Set.singleton_eq_singleton_iff.mp hE

end Core

theorem thm83MixedRungs {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    {n n' : ℕ} {H : SimpleGraph (Fin n)} {H' : SimpleGraph (Fin n')}
    {Rn Rd : U → U → List V}
    (hforms : FormsLineGraph G J S N Rn H) (hnondeg : NondegenerateAppearance J H)
    (hforms' : FormsLineGraph G J S N Rd H') (hdeg : DegenerateAppearance J H') :
    ∃ u v : U, J.Adj u v ∧ pathLength (Rd u v) = 0 ∧ 1 ≤ pathLength (Rn u v) := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hzero : ∀ u v : U, J.Adj u v → pathLength (Rd u v) = 0 → pathLength (Rn u v) = 0 := by
    intro u v huv h
    have := hcontra u v huv h
    omega
  obtain ⟨ι, B, hιinj, hrange, hbranch, hdictH, hsurj⟩ := dict G J hJ S N hSN H Rn hforms
  obtain ⟨ι', B', hι'inj, hrange', hbranch', hdictH', hsurj'⟩ := dict G J hJ S N hSN H' Rd hforms'
  apply hnondeg
  rcases hdeg with ⟨hK4, hdegK4⟩ | ⟨hnK4, hK33J, hK33H'⟩
  ------------------------------------------------------------------
  -- `J = K₄`: four branches of `H'` forming a four-cycle are single edges.
  ------------------------------------------------------------------
  · left
    refine ⟨hK4, ?_⟩
    obtain ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hbvsub⟩ := hdegK4
    have hab1 : a ≠ b := by intro h; rw [h] at hnd; simp at hnd
    have hac1 : a ≠ c := by intro h; rw [h] at hnd; simp at hnd
    have had1 : a ≠ d := by intro h; rw [h] at hnd; simp at hnd
    have hbc1 : b ≠ c := by intro h; rw [h] at hnd; simp at hnd
    have hbd1 : b ≠ d := by intro h; rw [h] at hnd; simp at hnd
    have hcd1 : c ≠ d := by intro h; rw [h] at hnd; simp at hnd
    -- the four branch-vertices of `H'` are exactly `a, b, c, d`
    have hcardU : Fintype.card U = 4 := by
      obtain ⟨e⟩ := hK4
      simpa using Fintype.card_congr e.toEquiv
    have hncard4 : ({a, b, c, d} : Set (Fin n')).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab1, hac1, had1]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [hbc1, hbd1]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [hcd1]) (Set.toFinite _),
        Set.ncard_singleton]
    have hrangeEq : Set.range ι' = ({a, b, c, d} : Set (Fin n')) := by
      refine Set.eq_of_subset_of_ncard_le (hrange' ▸ hbvsub) ?_ (Set.toFinite _)
      rw [hncard4, Set.ncard_range_of_injective hι'inj, Nat.card_eq_fintype_card, hcardU]
    have hbv' : ∀ z ∈ ({a, b, c, d} : Set (Fin n')), z ∈ branchVertices H' := by
      intro z hz
      rw [← hrange', hrangeEq]
      exact hz
    obtain ⟨ua, hua⟩ : a ∈ Set.range ι' := by rw [hrangeEq]; simp
    obtain ⟨ub, hub⟩ : b ∈ Set.range ι' := by rw [hrangeEq]; simp
    obtain ⟨uc, huc⟩ : c ∈ Set.range ι' := by rw [hrangeEq]; simp
    obtain ⟨ud, hud⟩ : d ∈ Set.range ι' := by rw [hrangeEq]; simp
    -- transporting a four-cycle edge of `H'` to an edge of `H`
    have step : ∀ x y : Fin n', H'.Adj x y → ∀ ux uy : U, ι' ux = x → ι' uy = y →
        x ∈ branchVertices H' → y ∈ branchVertices H' → H.Adj (ι ux) (ι uy) := by
      intro x y hxy ux uy hux huy hxb hyb
      obtain ⟨p, q, hpq, hzeroD, hs⟩ :=
        edge_to_zero_rung hbranch' hdictH' hsurj' hι'inj hxy hxb hyb
      have hHadj : H.Adj (ι p) (ι q) :=
        zero_rung_to_adj hbranch hdictH hpq (hzero p q hpq hzeroD)
      rw [← hux, ← huy] at hs
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← hι'inj h1, ← hι'inj h2]; exact hHadj
      · rw [← hι'inj h1, ← hι'inj h2]; exact hHadj.symm
    have hA := step a b hab ua ub hua hub (hbv' a (by simp)) (hbv' b (by simp))
    have hB := step b c hbc ub uc hub huc (hbv' b (by simp)) (hbv' c (by simp))
    have hC := step c d hcd uc ud huc hud (hbv' c (by simp)) (hbv' d (by simp))
    have hD := step d a hda ud ua hud hua (hbv' d (by simp)) (hbv' a (by simp))
    -- the four images are distinct, and they exhaust the branch-vertices of `H`
    have huab : ua ≠ ub := fun h => hab1 (by rw [← hua, ← hub, h])
    have huac : ua ≠ uc := fun h => hac1 (by rw [← hua, ← huc, h])
    have huad : ua ≠ ud := fun h => had1 (by rw [← hua, ← hud, h])
    have hubc : ub ≠ uc := fun h => hbc1 (by rw [← hub, ← huc, h])
    have hubd : ub ≠ ud := fun h => hbd1 (by rw [← hub, ← hud, h])
    have hucd : uc ≠ ud := fun h => hcd1 (by rw [← huc, ← hud, h])
    refine ⟨ι ua, ι ub, ι uc, ι ud, ?_, hA, hB, hC, hD, ?_⟩
    · simp [hιinj.eq_iff, huab, huac, huad, hubc, hubd, hucd]
    · intro w hw
      rw [← hrange] at hw
      obtain ⟨u, rfl⟩ := hw
      have hmem : ι' u ∈ ({a, b, c, d} : Set (Fin n')) := by
        rw [← hrangeEq]; exact ⟨u, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hmem with h | h | h | h
      · exact Or.inl (by rw [hι'inj (h.trans hua.symm)])
      · exact Or.inr (Or.inl (by rw [hι'inj (h.trans hub.symm)]))
      · exact Or.inr (Or.inr (Or.inl (by rw [hι'inj (h.trans huc.symm)])))
      · exact Or.inr (Or.inr (Or.inr (by rw [hι'inj (h.trans hud.symm)])))
  ------------------------------------------------------------------
  -- `J = H' = K₃,₃`: *all* branches of `H'` are single edges.
  ------------------------------------------------------------------
  · right
    refine ⟨hnK4, hK33J, ?_⟩
    obtain ⟨eJ⟩ := hK33J
    obtain ⟨eH'⟩ := hK33H'
    have hcard : Fintype.card U = Fintype.card (Fin n') := by
      rw [Fintype.card_congr eJ.toEquiv, Fintype.card_congr eH'.toEquiv]
    have hbij : Function.Bijective ι' :=
      (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, hcard⟩
    have hbvuniv : branchVertices H' = (Set.univ : Set (Fin n')) := by
      rw [← hrange', hbij.2.range_eq]
    -- every `Rd`-rung has length `0`, hence so does every `Rn`-rung
    have hallD : ∀ p q : U, J.Adj p q → pathLength (Rd p q) = 0 := by
      intro p q hpq
      have hlen : (B' p q).length ≤ 2 := by
        by_contra hc
        have h3 : 0 + 2 < (B' p q).length := by omega
        exact (hbranch' p q hpq).1.2.1 _
          (SubdivisionCounting.mem_trackInterior_getElem (B' p q) 0 h3)
          (hbvuniv ▸ Set.mem_univ _)
      have hιne : ι' p ≠ ι' q := fun h => hpq.ne (hι'inj h)
      have h2 := two_le_length_of_trackFrom_ne (hbranch' p q hpq).2 hιne
      exact (hdictH' p q hpq).mpr (eq_pair_of_length_two (hbranch' p q hpq).2 (by omega))
    have hallN : ∀ p q : U, J.Adj p q → pathLength (Rn p q) = 0 :=
      fun p q hpq => hzero p q hpq (hallD p q hpq)
    -- hence `ι : J ≃g H`, so `H ≅ J ≅ K₃,₃`
    obtain ⟨ι₀, T, hι₀inj, htrack0, hlen0, hrev0, hdisj0, hnew0, hcover0, hedges0⟩ :=
      hforms.2.1.1
    have hdegJ : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ
    have hrange0 : Set.range ι₀ = branchVertices H :=
      Set.Subset.antisymm
        (SubdivisionCounting.range_subset_branchVertices hι₀inj htrack0 hlen0 hdisj0 hnew0 hdegJ)
        (SubdivisionCounting.branchVertices_subset_range htrack0 hrev0 hdisj0 hcover0 hedges0)
    have hTshort : ∀ p q : U, J.Adj p q → (T p q).length ≤ 2 := by
      intro p q hpq
      have hι₀ne : ι₀ p ≠ ι₀ q := fun h => hpq.ne (hι₀inj h)
      have hbr : IsBranch H (T p q) := by
        refine Thm82BranchDelta.isBranch_of_ends_branch (htrack0 p q hpq) hι₀ne ?_ ?_ ?_
        · intro w hw
          rw [← hrange0]
          exact hnew0 p q hpq w hw
        · rw [← hrange0]; exact ⟨p, rfl⟩
        · rw [← hrange0]; exact ⟨q, rfl⟩
      obtain ⟨x, y, hxy, hEq⟩ := hsurj (T p q) hbr
      have hBpair : B x y = [ι x, ι y] := (hdictH x y hxy).mp (hallN x y hxy)
      have hsub : (trackEdges (T p q)).Subsingleton := by
        rw [hEq, hBpair, trackEdges_pair]; exact Set.subsingleton_singleton
      exact length_le_two_of_trackEdges_subsingleton (htrack0 p q hpq).1 hsub
    have hιsurj : Function.Surjective ι := by
      intro w
      rcases hcover0 w with ⟨u, rfl⟩ | ⟨p, q, hpq, hw⟩
      · have hmem : ι₀ u ∈ Set.range ι := by rw [hrange, ← hrange0]; exact ⟨u, rfl⟩
        exact hmem
      · exfalso
        have h1 := three_le_length_of_mem_trackInterior hw
        have h2 := hTshort p q hpq
        omega
    have hadj_iff : ∀ x y : U, H.Adj (ι x) (ι y) ↔ J.Adj x y := by
      intro x y
      constructor
      · intro h
        obtain ⟨p, q, hpq, -, hs⟩ :=
          edge_to_zero_rung hbranch hdictH hsurj hιinj h
            (by rw [← hrange]; exact ⟨x, rfl⟩) (by rw [← hrange]; exact ⟨y, rfl⟩)
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← hιinj h1, ← hιinj h2]; exact hpq
        · rw [← hιinj h2, ← hιinj h1]; exact hpq.symm
      · intro h
        exact zero_rung_to_adj hbranch hdictH h (hallN x y h)
    have eqv : J ≃g H :=
      { toEquiv := Equiv.ofBijective ι ⟨hιinj, hιsurj⟩
        map_rel_iff' := @fun x y => hadj_iff x y }
    exact ⟨eqv.symm.trans eJ⟩

end Workspace.ProofLemmas.Thm83MixedRungs
