import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand
import Workspace.ProofLemmas.TwoConnectedSplitVertex
import Workspace.ProofLemmas.Thm58StarBranchParityTrack
import Workspace.ProofLemmas.Connectivity58Concat
import Workspace.ProofLemmas.TrackSlice

/-!
# The cycle `C₂` of 5.8 (6) in the host graph

PAPER (proof of 5.8 (6), printed p. 28): *"Let `A` be the neighbours of `p₁` in `N_u` and
`B = N_u \ A`.  In `H` there is a cycle `C₂` using the branch between `v₁` and `v₂`, and using
an edge in `A` and an edge in `B`.  (To see this, divide `u` into two adjacent vertices, one
incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)"*

The cycle is presented here as a pair of tracks with the same two ends: the branch (up to
orientation, so `Q` is the branch read in one direction or the other) and a second track `D`
meeting it only at those ends and running through the star vertex `c` between the prescribed
`A`-neighbour and the prescribed `B`-neighbour.  `Connectivity58CycleBuild.baseCycle` glues the
two tracks into the cycle, and `Thm58StarBranchMixedHoleCycle.exists_hole` reads its rung in
`G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHoleTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- **The cycle `C₂` of 5.8 (6).**  PAPER, proof of 5.8 (6), printed p. 28: *"In `H` there is a cycle `C₂` using the
branch between `v₁` and `v₂`, and using an edge in `A` and an edge in `B`.  (To see this,
divide `u` into two adjacent vertices, one incident with the edges in `A` and the other with
those in `B`, and use Menger's theorem to deduce that there are two vertex-disjoint paths
between these two vertices and `{v₁,v₂}`.)"*

Here `u` is the star vertex `c`, the chosen edge of `A` is `c xA` and the chosen edge of `B` is
`c xB`, and `v₁`, `v₂` are the two ends of the branch `q`.  The cycle `C₂` is returned as the
branch `Q` (that is `q`, read in whichever direction makes the `A`-edge the one on the `v₁`
side) together with the complementary track `D`, which runs from `v₁` to `v₂` through `c`,
arriving along the `A`-edge and leaving along the `B`-edge, and which meets the branch only at
`v₁` and `v₂`. -/
theorem exists_mixed_track (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {xA xB : Fin n} (hAedge : s(c, xA) ∈ H.edgeSet) (hBedge : s(c, xB) ∈ H.edgeSet)
    (hxAB : xA ≠ xB) :
    ∃ (Q D : List (Fin n)) (w₁ w₂ : Fin n) (j : ℕ),
      IsTrackFrom H Q w₁ w₂ ∧ 2 ≤ Q.length ∧ trackEdges Q = trackEdges q ∧
      IsTrackFrom H D w₁ w₂ ∧ 3 ≤ D.length ∧ (∀ z ∈ trackInterior D, z ∉ Q) ∧
      1 ≤ j ∧ j + 1 < D.length ∧
      D[j]? = some c ∧ D[j - 1]? = some xA ∧ D[j + 1]? = some xB := by
  classical
  have hJ3 : IsKConnected J 3 := h.ready.2.1
  have hsubd : IsSubdivision J H := h.ready.2.2.1.1
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsubd
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlen, hrev, hdisjint, hnew⟩
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ3
  have hq2 : 2 ≤ q.length := branch_two_le_length h
  obtain ⟨a, b, hab, hqE⟩ :=
    BranchClassification.exists_trackEdges_eq_of_isBranch hι htrack hlen hrev hdisjint hnew
      hcover hedges hdeg h.branch hq2
  -- every vertex of the subdividing track of `ab` lies on the branch
  have hmemq : ∀ z : Fin n, z ∈ T a b → z ∈ q := by
    intro z hz
    obtain ⟨i, hi, hiz⟩ := List.getElem_of_mem hz
    by_cases hlt : i + 1 < (T a b).length
    · refine Thm58StarBranchParityTrack.mem_of_mem_edge (t := q)
        (g := s((T a b)[i], (T a b)[i + 1])) (by rw [hqE]; exact ⟨i, hlt, rfl⟩) ?_
      rw [← hiz]; exact Sym2.mem_mk_left _ _
    · have h2 : 2 ≤ (T a b).length := two_le_track_length hS hab
      refine Thm58StarBranchParityTrack.mem_of_mem_edge (t := q)
        (g := s((T a b)[i - 1]'(by omega), (T a b)[i - 1 + 1]'(by omega)))
        (by rw [hqE]; exact ⟨i - 1, by omega, rfl⟩) ?_
      rw [← hiz, SubdivisionCounting.getElem_eq_of_index_eq (T a b)
        (show i - 1 + 1 = i by omega) (by omega) hi]
      exact Sym2.mem_mk_right _ _
  have hlen0 : 0 < (T a b).length := by
    have := two_le_track_length hS hab; omega
  have hιa : ι a ∈ T a b := by
    rw [← SubdivisionCounting.track_head (htrack a b hab) hlen0]; exact List.getElem_mem _
  have hιb : ι b ∈ T a b := by
    rw [← DegenerateK4Tracks.track_getLast (htrack a b hab) hlen0]; exact List.getElem_mem _
  -- the star vertex is the image of a skeleton vertex, distinct from the two branch ends
  obtain ⟨u, hu⟩ : ∃ u : Fin m, ι u = c :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges h.star
  subst hu
  have hau : a ≠ u := by rintro rfl; exact hcq (hmemq _ hιa)
  have hbu : b ≠ u := by rintro rfl; exact hcq (hmemq _ hιb)
  -- the two prescribed edges at the star vertex lie on two subdividing tracks
  obtain ⟨x', hux', hAT⟩ :=
    SubdivisionTrackExpansion.edge_at_embedded_vertex hS hedges hAedge (Sym2.mem_mk_left _ _)
  obtain ⟨y', huy', hBT⟩ :=
    SubdivisionTrackExpansion.edge_at_embedded_vertex hS hedges hBedge (Sym2.mem_mk_left _ _)
  have second : ∀ (z : Fin m) (w : Fin n) (huz : J.Adj u z),
      s(ι u, w) ∈ trackEdges (T u z) →
      w = (T u z)[1]'(by have := two_le_track_length hS huz; omega) := by
    intro z w huz hT
    have hTz : IsTrackFrom H (T u z) (ι u) (ι z) := htrack u z huz
    have h2 : 2 ≤ (T u z).length := two_le_track_length hS huz
    have h0 : (T u z)[0]'(by omega) = ι u :=
      SubdivisionCounting.track_head hTz (by omega)
    have heq := edge_at_head hTz.1 hT h2 (by rw [h0]; exact Sym2.mem_mk_left _ _)
    rw [h0] at heq
    rcases Sym2.eq_iff.mp heq with ⟨-, hh⟩ | ⟨hh, -⟩
    · exact hh
    · exfalso
      have := (hTz.1.2.1.getElem_inj_iff (hi := (by omega : (0 : ℕ) < (T u z).length))
        (hj := (by omega : (1 : ℕ) < (T u z).length))).mp (h0.trans hh)
      omega
  have hxA1 := second x' xA hux' hAT
  have hxB1 := second y' xB huy' hBT
  have hx'y' : x' ≠ y' := by
    rintro rfl
    exact hxAB (hxA1.trans hxB1.symm)
  -- Menger for the split vertex
  obtain ⟨tA0, tB0, a', b', hends, htA0, htB0, hlA0, hlB0, hmeet0, hstart0⟩ :=
    TwoConnectedSplitVertex.exists_split_tracks hJ3 hux' huy' hx'y' hab hau hbu
  have hswapE : ∀ z w : Fin m, J.Adj z w → trackEdges (T w z) = trackEdges (T z w) := by
    intro z w hzw
    rw [hrev z w hzw, SubdivisionCounting.trackEdges_reverse]
  obtain ⟨sA, sB, eA, eB, hEAB, hsA, hsB, hlenA, hlenB, hmeetAB, hsA1, hsB1, hqE', heAu,
      heBu⟩ :
      ∃ (sA sB : List (Fin m)) (eA eB : Fin m),
        J.Adj eA eB ∧ IsTrackFrom J sA u eA ∧ IsTrackFrom J sB u eB ∧
        2 ≤ sA.length ∧ 2 ≤ sB.length ∧ (∀ z ∈ sA, z ∈ sB → z = u) ∧
        sA[1]? = some x' ∧ sB[1]? = some y' ∧ trackEdges (T eA eB) = trackEdges q ∧
        eA ≠ u ∧ eB ≠ u := by
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hstart0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨tA0, tB0, a', b', hab, htA0, htB0, hlA0, hlB0, hmeet0, h1, h2, hqE.symm, hau, hbu⟩
    · exact ⟨tB0, tA0, b', a', hab.symm, htB0, htA0, hlB0, hlA0,
        fun z hz hz' => hmeet0 z hz' hz, h2, h1, (hswapE _ _ hab).trans hqE.symm, hbu, hau⟩
    · exact ⟨tA0, tB0, a', b', hab.symm, htA0, htB0, hlA0, hlB0, hmeet0, h1, h2,
        (hswapE b' a' hab).trans hqE.symm, hbu, hau⟩
    · exact ⟨tB0, tA0, b', a', hab, htB0, htA0, hlB0, hlA0,
        fun z hz hz' => hmeet0 z hz' hz, h2, h1, hqE.symm, hau, hbu⟩
  have hchA : List.IsChain J.Adj sA := List.isChain_iff_getElem.mpr hsA.1.2.2
  have hchB : List.IsChain J.Adj sB := List.isChain_iff_getElem.mpr hsB.1.2.2
  have heAsA : eA ∈ sA := List.mem_of_mem_getLast? (by rw [hsA.2.2]; rfl)
  have heBsB : eB ∈ sB := List.mem_of_mem_getLast? (by rw [hsB.2.2]; rfl)
  have heBnA : eB ∉ sA := fun hh => heBu (hmeetAB _ hh heBsB)
  have heAnB : eA ∉ sB := fun hh => heAu (hmeetAB _ heAsA hh)
  -- the two skeleton tracks share no edge, and neither uses the branch edge
  have hnoedgeAB : ∀ e ∈ trackEdges sA, e ∉ trackEdges sB := by
    rintro e ⟨i, hi, rfl⟩ he'
    have h1 : sA[i] = u := hmeetAB _ (List.getElem_mem _)
      (Thm58StarBranchParityTrack.mem_of_mem_edge he' (Sym2.mem_mk_left _ _))
    have h2 : sA[i + 1] = u := hmeetAB _ (List.getElem_mem _)
      (Thm58StarBranchParityTrack.mem_of_mem_edge he' (Sym2.mem_mk_right _ _))
    have := (hsA.1.2.1.getElem_inj_iff (hi := (by omega : i < sA.length))
      (hj := hi)).mp (h1.trans h2.symm)
    omega
  have hpairedge : ∀ (s : List (Fin m)), eB ∉ s ∨ eA ∉ s →
      ∀ e ∈ trackEdges s, e ∉ trackEdges [eA, eB] := by
    rintro l hl e he ⟨i, hi, hEq⟩
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [show ([eA, eB][0]'(by simp)) = eA from rfl, show ([eA, eB][1]'(by simp)) = eB from rfl]
      at hEq
    subst hEq
    rcases hl with hl | hl
    · exact hl (Thm58StarBranchParityTrack.mem_of_mem_edge he (Sym2.mem_mk_right _ _))
    · exact hl (Thm58StarBranchParityTrack.mem_of_mem_edge he (Sym2.mem_mk_left _ _))
  have hchPair : List.IsChain J.Adj [eA, eB] := by
    refine List.isChain_iff_getElem.mpr ?_
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    exact hEAB
  have hQpair : expandTracks ι T [eA, eB] = T eA eB := expandTracks_pair hS hEAB
  -- expand to the host graph
  have hLA : IsTrackFrom H (expandTracks ι T sA) (ι u) (ι eA) :=
    SubdivisionTrackExpansion.expandTracks_isTrackFrom hS hsA
  have hLB : IsTrackFrom H (expandTracks ι T sB) (ι u) (ι eB) :=
    SubdivisionTrackExpansion.expandTracks_isTrackFrom hS hsB
  have hLAr : IsTrackFrom H (expandTracks ι T sA).reverse (ι eA) (ι u) :=
    TrackSlice.isTrackFrom_reverse hLA
  have hlenLA : 2 ≤ (expandTracks ι T sA).length :=
    two_le_expandTracks_length hS hchA hlenA
  have hlenLB : 2 ≤ (expandTracks ι T sB).length :=
    two_le_expandTracks_length hS hchB hlenB
  have hmeetLL : ∀ w ∈ (expandTracks ι T sA).reverse, w ∈ expandTracks ι T sB → w = ι u := by
    intro w hw hw'
    obtain ⟨z, hz, hz', rfl⟩ :=
      expandTracks_meet hS hchA hchB hnoedgeAB w (List.mem_reverse.mp hw) hw'
    rw [hmeetAB z hz hz']
  have hD : IsTrackFrom H ((expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail)
      (ι eA) (ι eB) := Connectivity58Concat.isTrackFrom_append hLAr hLB hmeetLL
  have hpairA : ∀ w ∈ expandTracks ι T sA, w ∈ T eA eB → w = ι eA := by
    intro w hw hw'
    rw [← hQpair] at hw'
    obtain ⟨z, hz, hz', rfl⟩ :=
      expandTracks_meet hS hchA hchPair (hpairedge sA (Or.inl heBnA)) w hw hw'
    rcases List.mem_pair.mp hz' with rfl | rfl
    · rfl
    · exact absurd hz heBnA
  have hpairB : ∀ w ∈ expandTracks ι T sB, w ∈ T eA eB → w = ι eB := by
    intro w hw hw'
    rw [← hQpair] at hw'
    obtain ⟨z, hz, hz', rfl⟩ :=
      expandTracks_meet hS hchB hchPair (hpairedge sB (Or.inr heAnB)) w hw hw'
    rcases List.mem_pair.mp hz' with rfl | rfl
    · exact absurd hz heAnB
    · rfl
  -- the second vertices of the two expanded tracks are the two prescribed neighbours
  obtain ⟨restA, hAeq⟩ : ∃ rest, sA = u :: x' :: rest := by
    match sA, hlenA, hsA.2.1, hsA1 with
    | z :: w :: rest, _, hh, h1 =>
      refine ⟨rest, ?_⟩
      have hz : z = u := Option.some_injective _ hh
      have hw : w = x' := Option.some_injective _ h1
      rw [hz, hw]
  obtain ⟨restB, hBeq⟩ : ∃ rest, sB = u :: y' :: rest := by
    match sB, hlenB, hsB.2.1, hsB1 with
    | z :: w :: rest, _, hh, h1 =>
      refine ⟨rest, ?_⟩
      have hz : z = u := Option.some_injective _ hh
      have hw : w = y' := Option.some_injective _ h1
      rw [hz, hw]
  have hchA2 : List.IsChain J.Adj (u :: x' :: restA) := hAeq ▸ hchA
  have hchB2 : List.IsChain J.Adj (u :: y' :: restB) := hBeq ▸ hchB
  have hLA1 : (expandTracks ι T sA)[1]? = some xA := by
    rw [hAeq, expandTracks_second hS hux' hchA2.tail,
      hxA1, List.getElem?_eq_getElem (by have := two_le_track_length hS hux'; omega)]
  have hLB1 : (expandTracks ι T sB)[1]? = some xB := by
    rw [hBeq, expandTracks_second hS huy' hchB2.tail,
      hxB1, List.getElem?_eq_getElem (by have := two_le_track_length hS huy'; omega)]
  -- assemble
  refine ⟨T eA eB, (expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail, ι eA, ι eB,
    (expandTracks ι T sA).length - 1, htrack eA eB hEAB, two_le_track_length hS hEAB, hqE',
    hD, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [Connectivity58Concat.length_append, List.length_reverse]; omega
  · intro z hz hzQ
    have hzD := mem_of_mem_trackInterior hz
    rcases List.mem_append.mp hzD with hh | hh
    · exact ne_head_of_mem_trackInterior hD.1.2.1 hD.2.1 hz
        (hpairA z (List.mem_reverse.mp hh) hzQ)
    · exact ne_getLast_of_mem_trackInterior hD.1.2.1 hD.2.2 hz
        (hpairB z (List.mem_of_mem_tail hh) hzQ)
  · rw [Connectivity58Concat.length_append, List.length_reverse]; omega
  · have hb : (expandTracks ι T sA).length - 1 <
        ((expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail).length := by
      rw [Connectivity58Concat.length_append, List.length_reverse]; omega
    rw [List.getElem?_eq_getElem hb,
      Connectivity58Concat.append_getElem_left _ _ _ (by rw [List.length_reverse]; omega) hb,
      List.getElem_reverse,
      SubdivisionCounting.getElem_eq_of_index_eq (expandTracks ι T sA)
        (show (expandTracks ι T sA).length - 1 - ((expandTracks ι T sA).length - 1) = 0
          by omega) (by omega) (by omega),
      SubdivisionCounting.track_head hLA (by omega)]
  · have hb : (expandTracks ι T sA).length - 1 - 1 <
        ((expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail).length := by
      rw [Connectivity58Concat.length_append, List.length_reverse]; omega
    rw [List.getElem?_eq_getElem hb,
      Connectivity58Concat.append_getElem_left _ _ _ (by rw [List.length_reverse]; omega) hb,
      List.getElem_reverse,
      SubdivisionCounting.getElem_eq_of_index_eq (expandTracks ι T sA)
        (show (expandTracks ι T sA).length - 1 - ((expandTracks ι T sA).length - 1 - 1) = 1
          by omega) (by omega) (by omega)]
    rw [← List.getElem?_eq_getElem (l := expandTracks ι T sA) (i := 1) (by omega)] at *
    exact hLA1
  · have hb : (expandTracks ι T sA).length - 1 + 1 <
        ((expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail).length := by
      rw [Connectivity58Concat.length_append, List.length_reverse]; omega
    have hidx : (expandTracks ι T sA).reverse.length - 1 + 1
        = (expandTracks ι T sA).length - 1 + 1 := by rw [List.length_reverse]
    rw [List.getElem?_eq_getElem hb, ← SubdivisionCounting.getElem_eq_of_index_eq
        ((expandTracks ι T sA).reverse ++ (expandTracks ι T sB).tail) hidx (by omega) hb,
      Connectivity58Concat.append_getElem_right hLAr hLB 1 (by omega) (by omega)]
    rw [← List.getElem?_eq_getElem (l := expandTracks ι T sB) (i := 1) (by omega)] at *
    exact hLB1


end Workspace.ProofLemmas.Thm58StarBranchMixedHoleTrack
