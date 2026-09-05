import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.RungReplacementDelete
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.PathBasics

/-!
# The residual appearance after deleting a branch

Continuing `Workspace.ProofLemmas.RungReplacementDelete`, this module records the two facts
about the residual appearance that the add-track step of 7.5 consumes:

* PAPER (printed p. 37, the content of *"`N′bᵢ = (Nbᵢ \ {rᵢ}) ∪ {r′ᵢ}`"* before the new rung is
  attached): deleting the branch removes exactly `rᵢ` from the clique at `bᵢ`, because `rᵢ` is
  the only vertex the clique `N_{bᵢ}` has on the old rung;
* the two ends of the deleted branch are **nonadjacent** in the residual graph, which is what
  lets a new track be added between them.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementResidual

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.RungReplacementDelete

variable {V W U : Type*}

/-- **The residual endpoint clique.**  `N_b` loses exactly the vertex `r` it had on the old
rung. -/
theorem nset_resGraph
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (q : List W)
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q)
    (φ₀ : (resGraph H q).lineGraph ≃g G.induce (K \ rungOf G H K φ q))
    (hlab : ∀ (f : Sym2 (resVerts q)) (hf : f ∈ (resGraph H q).edgeSet),
      (↑(φ₀ ⟨f, hf⟩) : V)
        = (↑(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩) : V))
    (b : W) (hb : b ∉ trackInterior q) (r : V)
    (hr : NSet G H K φ b ∩ rungOf G H K φ q = {r}) :
    NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀ ⟨b, hb⟩ = NSet G H K φ b \ {r} := by
  have hrmem : r ∈ NSet G H K φ b ∩ rungOf G H K φ q := by rw [hr]; rfl
  ext x
  constructor
  · rintro ⟨f, hf, ⟨-, hbf⟩, rfl⟩
    have hmap := (mem_resGraph_edgeSet f).mp hf
    have hbe : b ∈ Sym2.map Subtype.val f := Sym2.mem_map.mpr ⟨⟨b, hb⟩, hbf, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ⟨Sym2.map Subtype.val f, hmap.1, ⟨hmap.1, hbe⟩, hlab f hf⟩
    · intro hcon
      have hnr := (resLabel_mem G H K φ q hf).2
      rw [hlab f hf] at hcon
      exact hnr (hcon ▸ hrmem.2)
  · rintro ⟨⟨e, he, ⟨-, hbe⟩, rfl⟩, hxr⟩
    have henot : e ∉ trackEdges q := by
      intro hcon
      refine hxr ?_
      have : (↑(φ ⟨e, he⟩) : V) ∈ NSet G H K φ b ∩ rungOf G H K φ q :=
        ⟨⟨e, he, ⟨he, hbe⟩, rfl⟩, ⟨e, he, hcon, rfl⟩⟩
      rw [hr] at this
      exact this
    obtain ⟨f, hfval⟩ := exists_sym2_lift (q := q) e (hclosed e he henot)
    have hf : f ∈ (resGraph H q).edgeSet := by
      rw [mem_resGraph_edgeSet, hfval]; exact ⟨he, henot⟩
    have hbf : (⟨b, hb⟩ : resVerts q) ∈ f := by
      have : b ∈ Sym2.map Subtype.val f := hfval ▸ hbe
      obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.mp this
      have : w = ⟨b, hb⟩ := Subtype.ext hwv
      rwa [this] at hw
    refine ⟨f, hf, ⟨hf, hbf⟩, ?_⟩
    rw [hlab f hf,
      show (⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩ : H.edgeSet)
        = ⟨e, he⟩ from Subtype.ext hfval]

/-- **The two ends of the deleted branch are nonadjacent in the residual graph.**

If the branch has length one, its only edge is deleted; if it is longer, its ends are already
nonadjacent in `H` by `Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds`. -/
theorem not_resGraph_adj_ends [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q) :
    ¬ (resGraph H q).Adj ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ := by
  rintro ⟨hadj, hnot⟩
  rcases Nat.lt_or_ge q.length 3 with hlt | hge
  · have hlen : q.length = 2 := by omega
    have h0 : q[0]'(by omega) = b₁ :=
      Workspace.ProofLemmas.SubdivisionCounting.track_head hqf (by omega)
    have h1 : q[1]'(by omega) = b₂ :=
      Workspace.ProofLemmas.SubdivisionCounting.track_last hqf hlen
    exact hnot ⟨0, by omega, by rw [h0, h1]⟩
  · have hlen : 2 ≤ trackLength q := by simp only [trackLength]; omega
    exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H hsub q b₁ b₂
      hq hqf hlen).2.2.2 hadj


/-- Every vertex of a track is one of its two ends or an internal vertex. -/
theorem mem_track_cases {H : SimpleGraph W} {q : List W} {b₁ b₂ w : W}
    (hqf : IsTrackFrom H q b₁ b₂) (hq2 : 2 ≤ q.length) (hw : w ∈ q) :
    w = b₁ ∨ w = b₂ ∨ w ∈ trackInterior q := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
  have h0 : q[0]'(by omega) = b₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hqf (by omega)
  have hL : q[q.length - 1]'(by omega) = b₂ := by
    have h' := hqf.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact Or.inl h0
  · rcases Nat.lt_or_ge j (q.length - 1) with hlt | hge
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      exact Or.inr (Or.inr
        (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q k (by omega)))
    · refine Or.inr (Or.inl ?_)
      rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show j = q.length - 1 by omega) hj (by omega)]
      exact hL

/-- **A clique away from the deleted branch is unchanged.** -/
theorem nset_resGraph_of_notMem
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (q : List W)
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q)
    (φ₀ : (resGraph H q).lineGraph ≃g G.induce (K \ rungOf G H K φ q))
    (hlab : ∀ (f : Sym2 (resVerts q)) (hf : f ∈ (resGraph H q).edgeSet),
      (↑(φ₀ ⟨f, hf⟩) : V)
        = (↑(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩) : V))
    (c : W) (hc : c ∉ q) (hc' : c ∉ trackInterior q) :
    NSet G (resGraph H q) (K \ rungOf G H K φ q) φ₀ ⟨c, hc'⟩ = NSet G H K φ c := by
  ext x
  constructor
  · rintro ⟨f, hf, ⟨-, hcf⟩, rfl⟩
    have hmap := (mem_resGraph_edgeSet f).mp hf
    exact ⟨Sym2.map Subtype.val f, hmap.1,
      ⟨hmap.1, Sym2.mem_map.mpr ⟨⟨c, hc'⟩, hcf, rfl⟩⟩, hlab f hf⟩
  · rintro ⟨e, he, ⟨-, hce⟩, rfl⟩
    have henot : e ∉ trackEdges q := fun hcon =>
      hc (Workspace.ProofLemmas.RungReplacementBranchFacts.mem_list_of_mem_trackEdges hcon hce)
    obtain ⟨f, hfval⟩ := exists_sym2_lift (q := q) e (hclosed e he henot)
    have hf : f ∈ (resGraph H q).edgeSet := by
      rw [mem_resGraph_edgeSet, hfval]; exact ⟨he, henot⟩
    have hcf : (⟨c, hc'⟩ : resVerts q) ∈ f := by
      have hmem : c ∈ Sym2.map Subtype.val f := hfval ▸ hce
      obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.mp hmem
      have hweq : w = ⟨c, hc'⟩ := Subtype.ext hwv
      rwa [hweq] at hw
    refine ⟨f, hf, ⟨hf, hcf⟩, ?_⟩
    rw [hlab f hf,
      show (⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩ : H.edgeSet)
        = ⟨e, he⟩ from Subtype.ext hfval]

/-- **The rung of a retained track is unchanged.** -/
theorem rung_resGraph
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (q : List W) (b : W) (hb : b ∉ trackInterior q)
    (φ₀ : (resGraph H q).lineGraph ≃g G.induce (K \ rungOf G H K φ q))
    (hlab : ∀ (f : Sym2 (resVerts q)) (hf : f ∈ (resGraph H q).edgeSet),
      (↑(φ₀ ⟨f, hf⟩) : V)
        = (↑(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩) : V))
    (p : List W) (hpin : ∀ w ∈ p, w ∉ trackInterior q)
    (hpE : ∀ (i : ℕ) (hi : i + 1 < p.length),
      s(p[i]'(by omega), p[i + 1]'hi) ∈ H.edgeSet)
    (hpq : ∀ (i : ℕ) (hi : i + 1 < p.length),
      s(p[i]'(by omega), p[i + 1]'hi) ∉ trackEdges q) :
    {x : V | ∃ (f : Sym2 (resVerts q)) (hf : f ∈ (resGraph H q).edgeSet),
        f ∈ trackEdges (p.map (resEmb q b hb)) ∧ x = (↑(φ₀ ⟨f, hf⟩) : V)}
      = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet), e ∈ trackEdges p ∧
        x = (↑(φ ⟨e, he⟩) : V)} := by
  have hkey : ∀ (i : ℕ) (hi : i + 1 < p.length),
      Sym2.map Subtype.val (Sym2.map (resEmb q b hb) s(p[i]'(by omega), p[i + 1]'hi))
        = s(p[i]'(by omega), p[i + 1]'hi) := by
    intro i hi
    rw [Sym2.map_map]
    show s(_, _) = _
    rw [Function.comp_apply, Function.comp_apply,
      resEmb_of_notMem q b hb (hpin _ (List.getElem_mem _)),
      resEmb_of_notMem q b hb (hpin _ (List.getElem_mem _))]
  have hlift : ∀ (i : ℕ) (hi : i + 1 < p.length),
      Sym2.map (resEmb q b hb) s(p[i]'(by omega), p[i + 1]'hi) ∈ (resGraph H q).edgeSet := by
    intro i hi
    rw [mem_resGraph_edgeSet, hkey i hi]
    exact ⟨hpE i hi, hpq i hi⟩
  ext x
  constructor
  · rintro ⟨f, hf, hfm, rfl⟩
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at hfm
    obtain ⟨e, ⟨i, hi, rfl⟩, rfl⟩ := hfm
    refine ⟨s(p[i]'(by omega), p[i + 1]'hi), hpE i hi, ⟨i, hi, rfl⟩, ?_⟩
    rw [hlab _ hf,
      show (⟨Sym2.map Subtype.val (Sym2.map (resEmb q b hb)
          s(p[i]'(by omega), p[i + 1]'hi)), _⟩ : H.edgeSet)
        = ⟨s(p[i]'(by omega), p[i + 1]'hi), hpE i hi⟩ from Subtype.ext (hkey i hi)]
  · rintro ⟨e, he, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨Sym2.map (resEmb q b hb) s(p[i]'(by omega), p[i + 1]'hi), hlift i hi, ?_, ?_⟩
    · rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
      exact ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    · rw [hlab _ (hlift i hi),
        show (⟨Sym2.map Subtype.val (Sym2.map (resEmb q b hb)
            s(p[i]'(by omega), p[i + 1]'hi)), _⟩ : H.edgeSet)
          = ⟨s(p[i]'(by omega), p[i + 1]'hi), he⟩ from Subtype.ext (hkey i hi)]

/-- The length dictionary: a path whose vertex set is the rung of a track `q` has exactly
`trackLength q` vertices.  (Same statement as
`Workspace.ProofLemmas.RungReplacementRungLength.rung_length_eq_trackLength`, repeated here
because that module sits above this one in the import graph.) -/
theorem rung_length_eq_trackLength {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (hlen : 1 ≤ trackLength q) (R : List V) (hR : IsPathList G R)
    (hRset : {x : V | x ∈ R} = rungOf G H K φ q) : R.length = trackLength q := by
  classical
  have hset : rungOf G H K φ q = {x : V | x ∈ TrackToRungPath.trackRung φ q hq} := by
    have hlen' : (TrackToRungPath.trackRung φ q hq).length = q.length - 1 := by
      rw [TrackToRungPath.trackRung_length]; rfl
    ext x
    constructor
    · rintro ⟨e, he, ⟨i, hi, rfl⟩, rfl⟩
      have hidx : i < (TrackToRungPath.trackRung φ q hq).length := by rw [hlen']; omega
      rw [← TrackToRungPath.trackRung_getElem φ q hq i hidx hi he]
      exact List.getElem_mem _
    · intro hx
      obtain ⟨i, hidx, hxi⟩ := List.mem_iff_getElem.mp hx
      have hi : i + 1 < q.length := by rw [hlen'] at hidx; omega
      have he : s(q[i]'(by omega), q[i + 1]'hi) ∈ H.edgeSet :=
        TrackToRungPath.trackEdge_mem_edgeSet hq i hi
      exact ⟨_, he, ⟨i, hi, rfl⟩, by
        rw [← hxi]; exact TrackToRungPath.trackRung_getElem φ q hq i hidx hi he⟩
  have hnd : (TrackToRungPath.trackRung φ q hq).Nodup :=
    (TrackToRungPath.trackRung_isPathList φ q hq hlen).2.1
  have hcard := congrArg Set.ncard (hRset.trans hset)
  have h1 : {x : V | x ∈ R}.ncard = R.length := by
    have : {x : V | x ∈ R} = (↑R.toFinset : Set V) := by ext y; simp
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hR.2.1]
  have h2 : {x : V | x ∈ TrackToRungPath.trackRung φ q hq}.ncard
      = (TrackToRungPath.trackRung φ q hq).length := by
    have : {x : V | x ∈ TrackToRungPath.trackRung φ q hq}
        = (↑(TrackToRungPath.trackRung φ q hq).toFinset : Set V) := by ext y; simp
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  rw [h1, h2, TrackToRungPath.trackRung_length] at hcard
  exact hcard

end Workspace.ProofLemmas.RungReplacementResidual
