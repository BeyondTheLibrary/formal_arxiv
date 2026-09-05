import Workspace.ProofLemmas.Connectivity58Skeleton
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.RungReplacementMaximality

/-!
# The return track of the cycle of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`."*

A cycle of `H` through a branch is the branch together with a second track joining the same two
ends and meeting the branch only there.  This file produces that second track — the *return
track* — from the skeleton statement `Connectivity58Skeleton.exists_avoiding_track`: expand the
skeleton track through the subdivision.  The two facts that make the expansion behave are that
the skeleton track avoids the vertex of `J` under `u`, and that it does not use the skeleton
edge of the branch itself.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Connectivity58Cycle

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCompose

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
variable {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

/-- Expanding a list of skeleton vertices never shortens it. -/
theorem expandTracks_length_ge (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → p.length ≤ (expandTracks ι T p).length := by
  intro p
  induction p with
  | nil => intro _; simp [expandTracks]
  | cons x t ih =>
    cases t with
    | nil => intro _; simp [expandTracks]
    | cons y rest =>
      intro hch
      have hxy : J.Adj x y := hch.rel_head
      have h2 := two_le_track_length hS hxy
      have := ih hch.tail
      rw [expandTracks_cons_cons]
      simp only [List.length_append, List.length_dropLast, List.length_cons] at *
      omega

/-- Every skeleton vertex of a list survives into its expansion. -/
theorem mem_expandTracks_of_mem (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → ∀ x ∈ p, ι x ∈ expandTracks ι T p := by
  intro p
  induction p with
  | nil => intro _ x hx; simp at hx
  | cons z t ih =>
    cases t with
    | nil =>
      intro _ x hx
      have : x = z := by simpa using hx
      subst this
      simp [expandTracks]
    | cons y rest =>
      intro hch x hx
      have hzy : J.Adj z y := hch.rel_head
      rw [expandTracks_cons_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine List.mem_append_left _ ?_
        have h2 := two_le_track_length hS hzy
        have h0 : (T x y)[0]'(by omega) = ι x :=
          SubdivisionCounting.track_head (hS.track x y hzy) (by omega)
        have hmem : (T x y).dropLast[0]'(by simp; omega) = ι x := by
          rw [List.getElem_dropLast]
          exact h0
        exact hmem ▸ List.getElem_mem _
      · exact List.mem_append_right _ (ih hch.tail x hx')

/-- **The return track.**  In a subdivision of a 3-connected graph, a branch `q` with ends
`v₁`, `v₂` and a branch-vertex `c` off `q` admit a second track from `v₁` to `v₂` which avoids
`c`, meets `q` only at `v₁` and `v₂`, uses no edge of `q`, and carries a further branch-vertex.
Together with `q` this is the cycle of 5.8 (6). -/
theorem exists_return_track (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) {v₁ v₂ : W}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) {c : W} (hc : c ∈ branchVertices H) (hcq : c ∉ q) :
    ∃ D : List W, IsTrackFrom H D v₁ v₂ ∧ c ∉ D ∧
      (∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂) ∧
      (∀ e ∈ trackEdges D, e ∉ trackEdges q) ∧
      (∃ z ∈ D, z ∈ branchVertices H ∧ z ≠ v₁ ∧ z ≠ v₂) := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlen, hrev, hdisjint, hnew⟩
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨a₀, b₀, hab₀, hqE₀, hends⟩ :=
    BranchClassification.exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisjint hnew
      hcover hedges hdeg hq hq2 hqe hbv₁ hbv₂
  -- normalise the orientation
  obtain ⟨a, b, hab, hqE, hv₁, hv₂⟩ :
      ∃ a b : U, J.Adj a b ∧ trackEdges q = trackEdges (T a b) ∧ v₁ = ι a ∧ v₂ = ι b := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a₀, b₀, hab₀, hqE₀, h1, h2⟩
    · refine ⟨b₀, a₀, hab₀.symm, ?_, h1, h2⟩
      rw [hqE₀, hrev a₀ b₀ hab₀, SubdivisionCounting.trackEdges_reverse]
  subst hv₁; subst hv₂
  have hqT : q = T a b :=
    RungReplacementMaximality.eq_of_trackEdges_subset hqe (htrack a b hab) (by rw [hqE])
  -- the star vertex is an old vertex
  have hbrange : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  obtain ⟨u, rfl⟩ := hbrange hc
  have hmemT : ∀ x y : U, J.Adj x y → ι x ∈ T x y := by
    intro x y hxy
    have h2 := two_le_track_length hS hxy
    have h0 : (T x y)[0]'(by omega) = ι x :=
      SubdivisionCounting.track_head (hS.track x y hxy) (by omega)
    exact h0 ▸ List.getElem_mem _
  have hua : u ≠ a := by
    rintro rfl
    exact hcq (by rw [hqT]; exact hmemT u b hab)
  have hub : u ≠ b := by
    rintro rfl
    refine hcq ?_
    rw [hqT]
    have := hmemT u a hab.symm
    rw [hrev a u hab] at this
    simpa using this
  obtain ⟨t, ht, hut, hedge, ht3⟩ :=
    Connectivity58Skeleton.exists_avoiding_track hJ hab hua hub
  have hch : List.IsChain J.Adj t := List.isChain_iff_getElem.mpr ht.1.2.2
  set D : List W := expandTracks ι T t with hDdef
  have hDfrom : IsTrackFrom H D (ι a) (ι b) :=
    SubdivisionTrackExpansion.expandTracks_isTrackFrom hS ht
  have hD3 : 3 ≤ D.length := le_trans ht3 (expandTracks_length_ge hS t hch)
  have hDnd : D.Nodup := hDfrom.1.2.1
  have hD0 : D[0]'(by omega) = ι a := SubdivisionCounting.track_head hDfrom (by omega)
  have hDlast : D[D.length - 1]'(by omega) = ι b := by
    have h' := hDfrom.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega : D.length - 1 < D.length)]
      at h'
    exact Option.some_injective _ h'
  -- the return track meets the branch only at its two ends
  have hmeetq : ∀ z ∈ D, z ∈ q → z = ι a ∨ z = ι b := by
    have hab2 : IsTrackFrom J [a, b] a b := by
      refine ⟨⟨by simp, by simp [hab.ne], ?_⟩, rfl, rfl⟩
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst this
      simpa using hab
    have hexp : expandTracks ι T [a, b] = T a b := by
      show (T a b).dropLast ++ expandTracks ι T [b] = T a b
      rw [expandTracks_singleton]
      exact List.dropLast_append_getLast? (ι b) (track_getLast? hS hab)
    have hmeet := SubdivisionTrackExpansion.expandTracks_meet_only_ends hS ht hab2
      (by intro z hz hz2; simpa using hz2) (Or.inl hedge)
    intro z hz hzq
    exact hmeet z hz (by rw [hexp, ← hqT]; exact hzq)
  refine ⟨D, hDfrom, ?_, hmeetq, ?_, ?_⟩
  · intro hmem
    rcases mem_expandTracks hS t hch _ hmem with ⟨x, hx, hxe⟩ | ⟨x, y, -, -, hxy, hint⟩
    · exact hut (hι hxe ▸ hx)
    · exact hnew x y hxy _ hint ⟨u, rfl⟩
  · -- uses no edge of the branch
    rintro e ⟨i, hi, rfl⟩ heq
    obtain ⟨hxq, hyq⟩ := BranchClassification.mem_of_mem_trackEdges heq
    have hxD : D[i]'(by omega) ∈ D := List.getElem_mem _
    have hyD : D[i + 1]'hi ∈ D := List.getElem_mem _
    have hadj : H.Adj (D[i]'(by omega)) (D[i + 1]'hi) := hDfrom.1.2.2 i hi
    have hx := hmeetq _ hxD hxq
    have hy := hmeetq _ hyD hyq
    have hne : D[i]'(by omega) ≠ D[i + 1]'hi := hadj.ne
    have hiaib : ι a ≠ ι b := fun hh => hab.ne (hι hh)
    rcases hx with hx | hx
    · have hi0 : i = 0 := by
        have := hDnd.getElem_inj_iff (hi := (by omega : i < D.length))
          (hj := (by omega : 0 < D.length))
        exact this.mp (by rw [hx, hD0])
      have hyb : D[i + 1]'hi = ι b := by
        rcases hy with hy | hy
        · exact absurd (hx.trans hy.symm) hne
        · exact hy
      have hil : i + 1 = D.length - 1 := by
        have := hDnd.getElem_inj_iff (hi := hi)
          (hj := (by omega : D.length - 1 < D.length))
        exact this.mp (by rw [hyb, hDlast])
      omega
    · have hil : i = D.length - 1 := by
        have := hDnd.getElem_inj_iff (hi := (by omega : i < D.length))
          (hj := (by omega : D.length - 1 < D.length))
        exact this.mp (by rw [hx, hDlast])
      omega
  · -- a third branch vertex on the return track
    have ht0 : t[0]'(by omega) = a := SubdivisionCounting.track_head ht (by omega)
    have htl : t[t.length - 1]'(by omega) = b := by
      have h' := ht.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : t.length - 1 < t.length)] at h'
      exact Option.some_injective _ h'
    have htnd : t.Nodup := ht.1.2.1
    refine ⟨ι (t[1]'(by omega)), mem_expandTracks_of_mem hS t hch _ (List.getElem_mem _), ?_,
      ?_, ?_⟩
    · exact SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
        ⟨t[1]'(by omega), rfl⟩
    · intro hh
      have : t[1]'(by omega) = t[0]'(by omega) := by rw [ht0]; exact hι hh
      have := htnd.getElem_inj_iff (hi := (by omega : 1 < t.length))
        (hj := (by omega : 0 < t.length)) |>.mp this
      omega
    · intro hh
      have : t[1]'(by omega) = t[t.length - 1]'(by omega) := by rw [htl]; exact hι hh
      have := htnd.getElem_inj_iff (hi := (by omega : 1 < t.length))
        (hj := (by omega : t.length - 1 < t.length)) |>.mp this
      omega

end Workspace.ProofLemmas.Connectivity58Cycle
