import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# 8.5, claims (2) and (3): shared reading of the branch outcome of 5.8

When 5.8 returns its branch outcome it hands back a branch `q` of `H` with ends `b₁, b₂`, the
list `Rline` of the vertices of `G` carried by `q`, and the two vertices `r₁ ∈ N(b₁) ∩ Rline`,
`r₂ ∈ N(b₂) ∩ Rline`.  The lemmas here translate that data back into the language of the strip
system: `b₁` and `b₂` are the branch vertices `ι a₁`, `ι a₂` of two *adjacent* vertices of `J`,
`Rline` is the rung of the strip `S_{a₁a₂}`, and `r₁` is its end in `N_{a₁}`.

This is the content of the paper's sentence *"The branch containing `x'` does not meet `x`, so
`D` is the branch between `u` and `v`"* (proof of 8.5, claim (2), printed p. 42), and it is what
lets claims (2) and (3) name the vertex `d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm85Claim3Common

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]

/-- A rung meets `N_c` in at most one vertex, for each of the two ends `c` of its edge.  This
is the uniqueness clause of `IsUVRung` (printed p. 39, *"`s` is the unique vertex of `R` in
`N_u`"*). -/
theorem rung_mem_N_unique {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V}
    {N : U → Set V} {u v : U} {R : List V} (hR : IsUVRung G J S N u v R) {c : U}
    (hc : c = u ∨ c = v) {z z' : V} (hz : z ∈ R) (hz' : z' ∈ R)
    (hzN : z ∈ N c) (hz'N : z' ∈ N c) : z = z' := by
  obtain ⟨-, s, t, -, -, hs, ht⟩ := hR
  rcases hc with rfl | rfl
  · rw [(hs z hz).mp hzN, (hs z' hz').mp hz'N]
  · rw [(ht z hz).mp hzN, (ht z' hz').mp hz'N]

/-- **A strip at `a` whose rung end is not the exceptional vertex `r` is active.**

If `p ∈ F` is complete to all of the line-graph clique at `ι a` except possibly `r`, then for
every neighbour `w` of `a` in `J` whose rung end is not `r`, the strip `S_{aw}` meets the
attachment set of `F`. -/
theorem active_of_rung_end_ne
    (G : SimpleGraph V) (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (iota : U → W) (E : U → U → Sym2 W)
    (hEedge : ∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet)
    (hincident : ∀ u : U,
      incidentEdges H (iota u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v})
    (hEphi : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
      IsPathFrom G (Rchoice u v) s t → (↑(phi ⟨E u v, he⟩) : V) = s)
    (F : Set V) (p : V) (hpF : p ∈ F) (a : U) (r : V)
    (hcomplete : ∀ x ∈ {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H (iota a) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r}, G.Adj p x)
    (w : U) (haw : J.Adj a w)
    (hne : (↑(phi ⟨E a w, hEedge a w haw⟩) : V) ≠ r) :
    (attachments G F (stripSystemVertices J S) ∩ S a w).Nonempty := by
  obtain ⟨-, s, t, hpath, hRsub, -, -⟩ := hForms.1 a w haw
  have hsR : s ∈ Rchoice a w := List.mem_of_mem_head? hpath.2.1
  have hsS : s ∈ S a w := hRsub s hsR
  have himg : (↑(phi ⟨E a w, hEedge a w haw⟩) : V) = s :=
    hEphi a w haw (hEedge a w haw) s t hpath
  have hinc : E a w ∈ incidentEdges H (iota a) := by
    rw [hincident a]; exact ⟨w, haw, rfl⟩
  have hadj : G.Adj p s := by
    rw [← himg]
    refine hcomplete _ ⟨⟨E a w, hEedge a w haw, hinc, rfl⟩, ?_⟩
    simpa using hne
  exact ⟨s, ⟨StripSystemBasics.strip_subset_vertices haw hsS, p, hpF, hadj.symm⟩, hsS⟩

/-- The two ends of a branch of `H` are different.  (A branch has at least two vertices, and a
track has no repeated vertex.) -/
theorem branch_ends_ne
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (b1 b2 : W) (q : List W) (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2) :
    b1 ≠ b2 := by
  obtain ⟨iota0, T, hiota0, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hForms.2.1.1
  have hdeg : ∀ a : U, 3 ≤ (J.neighborSet a).ncard := fun a =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  have hnbr : ∀ w : W, ∃ z : W, H.Adj w z := by
    intro w
    rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
    · obtain ⟨z, hz⟩ : (J.neighborSet a).Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _)]
        have := hdeg a
        omega
      have hlen2 : 2 ≤ (T a z).length := by
        have := hlen a z hz
        simp only [trackLength] at this
        omega
      refine ⟨(T a z)[1]'(by omega), ?_⟩
      have hadj := (htrack a z hz).1.2.2 0 (by omega)
      rw [SubdivisionCounting.track_head (htrack a z hz) (by omega)] at hadj
      exact hadj
    · rw [SubdivisionCounting.mem_trackInterior_iff] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      exact ⟨(T a b)[j + 2]'(by omega), (htrack a b hab).1.2.2 (j + 1) (by omega)⟩
  have hq2 :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.two_le_length_of_isBranch hnbr hq
  intro heq
  have hhead : q[0]'(by omega) = b1 :=
    SubdivisionCounting.track_head hqfrom (by omega)
  have hlast : q[q.length - 1]'(by omega) = b2 := by
    have h := hqfrom.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have he : q[0]'(by omega) = q[q.length - 1]'(by omega) := by rw [hhead, hlast, heq]
  have hi := hq.1.2.1.getElem_inj_iff.mp he
  omega

/-- **A vertex of the line-graph clique at `ι a` is the end of a rung at `a`.**  Every member
of `N(ι a)` is the image of an edge of `H` incident with `ι a`, hence of an edge `E a w` for a
neighbour `w` of `a` in `J`, hence the end in `N_a` of the chosen `aw`-rung. -/
theorem mem_Nc_decode
    (G : SimpleGraph V) (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (iota : U → W) (E : U → U → Sym2 W)
    (hincident : ∀ u : U,
      incidentEdges H (iota u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v})
    (hEphi : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
      IsPathFrom G (Rchoice u v) s t → (↑(phi ⟨E u v, he⟩) : V) = s)
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (aa : U) (r : V) (hr : r ∈ Nc (iota aa)) :
    ∃ w : U, J.Adj aa w ∧ r ∈ N aa ∧ r ∈ S aa w := by
  rw [hNc (iota aa), hincident aa] at hr
  obtain ⟨e, he, ⟨w, haw, rfl⟩, hre⟩ := hr
  obtain ⟨-, s, t, hpath, hsub, hs, -⟩ := hForms.1 aa w haw
  have hsR : s ∈ Rchoice aa w := List.mem_of_mem_head? hpath.2.1
  have hrs : r = s := by rw [hre]; exact hEphi aa w haw he s t hpath
  subst hrs
  exact ⟨w, haw, (hs r hsR).mpr rfl, hsub r hsR⟩

/-- **Reading the branch outcome of 5.8 back in the strip system.**

The branch `q` returned by 5.8 joins two branch vertices of `H`, so its ends are `ι a₁` and
`ι a₂` for two vertices `a₁, a₂` of `J`; the vertices of `G` it carries are exactly those of a
rung, so `a₁a₂` is an edge of `J` and `Rline` is an `a₁a₂`-rung; and `r₁`, `r₂` are its ends in
`N_{a₁}`, `N_{a₂}`. -/
theorem branch_ends_dictionary
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (iota : U → W) (E : U → U → Sym2 W)
    (hrange : Set.range iota = branchVertices H)
    (hEedge : ∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet)
    (hincident : ∀ u : U,
      incidentEdges H (iota u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v})
    (hEphi : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
      IsPathFrom G (Rchoice u v) s t → (↑(phi ⟨E u v, he⟩) : V) = s)
    (b1 b2 : W) (q : List W) (Rline : List V) (r1 r2 : V)
    (hb1 : b1 ∈ branchVertices H) (hb2 : b2 ∈ branchVertices H)
    (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2)
    (hRimage : {x : V | x ∈ Rline} =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (hr1 : Nc b1 ∩ {x : V | x ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {x : V | x ∈ Rline} = {r2}) :
    ∃ a1 a2 : U, J.Adj a1 a2 ∧ iota a1 = b1 ∧ iota a2 = b2 ∧
      r1 ∈ N a1 ∧ r2 ∈ N a2 ∧
      (∀ z ∈ Rline, z ∈ S a1 a2) ∧
      (∀ z ∈ Rline, z ∈ N a1 → z = r1) := by
  classical
  obtain ⟨iotaB, B, -, -, -, hBrung, hBsurj⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.branchRungDictionaryAt
      G J hJ S N hSN H Rchoice hForms phi
  obtain ⟨a, b, hab, hqB⟩ := hBsurj q hq
  have hRlineEq : {x : V | x ∈ Rline} = {x : V | x ∈ Rchoice a b} := by
    rw [hRimage, ← hBrung a b hab, hqB]
  have hRlineS : ∀ z ∈ Rline, z ∈ S a b := by
    intro z hz
    obtain ⟨-, -, -, -, hsub, -, -⟩ := hForms.1 a b hab
    exact hsub z (by
      have : z ∈ {x : V | x ∈ Rline} := hz
      rw [hRlineEq] at this
      exact this)
  have hr1R : r1 ∈ Rline :=
    (show r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} by rw [hr1]; simp).2
  have hr2R : r2 ∈ Rline :=
    (show r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} by rw [hr2]; simp).2
  have hr1Nc : r1 ∈ Nc b1 :=
    (show r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} by rw [hr1]; simp).1
  have hr2Nc : r2 ∈ Nc b2 :=
    (show r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} by rw [hr2]; simp).1
  obtain ⟨a1, ha1⟩ : b1 ∈ Set.range iota := by rw [hrange]; exact hb1
  obtain ⟨a2, ha2⟩ : b2 ∈ Set.range iota := by rw [hrange]; exact hb2
  have hbne : b1 ≠ b2 := branch_ends_ne G J hJ S N H Rchoice hForms b1 b2 q hq hqfrom
  have ha12 : a1 ≠ a2 := by
    intro h; exact hbne (by rw [← ha1, ← ha2, h])
  -- decode `r₁` as the end of a rung at `a₁`
  obtain ⟨w0, haw0, hr1N, hr1S⟩ :=
    mem_Nc_decode G J S N H Rchoice hForms phi iota E hincident hEphi Nc hNc a1 r1
      (by rw [ha1]; exact hr1Nc)
  obtain ⟨w0', haw0', hr2N, hr2S⟩ :=
    mem_Nc_decode G J S N H Rchoice hForms phi iota E hincident hEphi Nc hNc a2 r2
      (by rw [ha2]; exact hr2Nc)
  have he1 : s(a, b) = s(a1, w0) :=
    StripSystemBasics.edge_eq_of_mem_strips hSN hab haw0 (hRlineS r1 hr1R) hr1S
  have he2 : s(a, b) = s(a2, w0') :=
    StripSystemBasics.edge_eq_of_mem_strips hSN hab haw0' (hRlineS r2 hr2R) hr2S
  have hw0 : w0 = a2 := by
    have h := he1.symm.trans he2
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 ha12
    · exact h2
  subst hw0
  refine ⟨a1, w0, haw0, ha1, ha2, hr1N, hr2N, ?_, ?_⟩
  · intro z hz
    have hzab : z ∈ S a b := hRlineS z hz
    rcases Sym2.eq_iff.mp he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hzab
    · have heq : S a b = S a1 w0 := by
        rw [h1, h2]
        exact StripSystemBasics.strip_symm hSN haw0.symm
      rw [← heq]; exact hzab
  · intro z hz hzN
    have hzR : z ∈ Rchoice a b := by
      have : z ∈ {x : V | x ∈ Rline} := hz
      rw [hRlineEq] at this
      exact this
    have hr1Rc : r1 ∈ Rchoice a b := by
      have : r1 ∈ {x : V | x ∈ Rline} := hr1R
      rw [hRlineEq] at this
      exact this
    have hmem : a1 = a ∨ a1 = b := by
      rcases Sym2.eq_iff.mp he1 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    exact rung_mem_N_unique (hForms.1 a b hab) hmem hzR hr1Rc hzN hr1N

/-- **The last three subcases of 5.8.2 all make both ends of the path complete to their
cliques.**  Either the first subcase 5.8.2.a holds verbatim, or `p₁` is complete to
`N(b₁) \ {r₁}` and `p₂` is complete to `N(b₂) \ {r₂}`.  (In 5.8.2.c the two ends coincide and
the completeness is stated for the union; `r₁ ∈ N(b₂)` would put `r₁` in
`N(b₂) ∩ Rline = {r₂}`, which is how the two exceptional vertices are separated.) -/
theorem first_case_or_both_ends
    (G : SimpleGraph V) (J : SimpleGraph U) (Rchoice : U → U → List V)
    (Nc : W → Set V) (P : List V) (p1 p2 : V) (b1 b2 : W) (Rline : List V) (r1 r2 : V)
    (hr1 : Nc b1 ∩ {x : V | x ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {x : V | x ∈ Rline} = {r2})
    (hcases :
      ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∃ x ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          y ≠ r1 → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
          (x = p2 ∧ y ∈ {z : V | z ∈ Rline} \ {r1}))) ∨
      ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨ (x = p2 ∧ y ∈ Nc b2 \ {r2}) ∨
          (x = p1 ∧ y = r1) ∨ (x = p2 ∧ y = r2)) ∧
        (Even (pathLength P) ↔ Even (pathLength Rline))) ∨
      (p1 = p2 ∧
        (∀ x ∈ (Nc b1 ∪ Nc b2) \ {r1, r2}, G.Adj p1 x) ∧
        (∀ y ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          G.Adj p1 y → y ∈ Nc b1 ∪ Nc b2 ∪ {z : V | z ∈ Rline}) ∧
        Even (pathLength Rline)) ∨
      (r1 = r2 ∧
        (∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          y ≠ r1 → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨ (x = p2 ∧ y ∈ Nc b2 \ {r2})) ∧
        Even (pathLength P))) :
    ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
      (∃ x ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 x) ∧
      (∀ x ∈ P, ∀ y ∈
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
        y ≠ r1 → G.Adj x y →
        (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
        (x = p2 ∧ y ∈ {z : V | z ∈ Rline} \ {r1}))) ∨
    ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧ (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x)) := by
  rcases hcases with hfirst | hsecond | hthird | hfourth
  · exact Or.inl hfirst
  · exact Or.inr ⟨hsecond.1, hsecond.2.1⟩
  · refine Or.inr ⟨?_, ?_⟩
    · intro x hx
      apply hthird.2.1 x
      refine ⟨Or.inl hx.1, ?_⟩
      intro hpair
      rcases hpair with h | h
      · exact hx.2 h
      · have hxR : x ∈ Rline := by rw [show x = r2 from h]; exact
          (show r2 ∈ Nc b2 ∩ {y : V | y ∈ Rline} by rw [hr2]; simp).2
        have hxI : x ∈ Nc b1 ∩ {z : V | z ∈ Rline} := ⟨hx.1, hxR⟩
        rw [hr1] at hxI
        exact hx.2 (by simpa using hxI)
    · intro x hx
      rw [← hthird.1]
      apply hthird.2.1 x
      refine ⟨Or.inr hx.1, ?_⟩
      intro hpair
      rcases hpair with h | h
      · have hxR : x ∈ Rline := by rw [show x = r1 from h]; exact
          (show r1 ∈ Nc b1 ∩ {y : V | y ∈ Rline} by rw [hr1]; simp).2
        have hxI : x ∈ Nc b2 ∩ {z : V | z ∈ Rline} := ⟨hx.1, hxR⟩
        rw [hr2] at hxI
        exact hx.2 (by simpa using hxI)
      · exact hx.2 h
  · exact Or.inr ⟨hfourth.2.1, hfourth.2.2.1⟩

/-- **The path returned by 5.8 is the whole of the minimal set `F`.**

If one end of the path has a neighbour in the strip `S_{a₁w}` and the other end has a
neighbour in the strip `S_{a₁a₂}` which is not in `N_{a₁}`, then those two attachments of the
path are not local: they lie in different strips, and the only vertex of `J` whose
neighbourhood could contain both is `a₂`, which the first attachment avoids.  The minimality of
`F` therefore forces the vertex set of the path to be all of `F`. -/
theorem path_eq_F_of_two_attachments
    (G : SimpleGraph V) (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N)
    (F : Set V)
    (hFmin : ∀ F1 : Set V, F1 ⊆ F → ConnectedSet G F1 →
      ¬ LocalForStripSystem J S N (attachments G F1 (stripSystemVertices J S)) → F1 = F)
    (P : List V) (hP : IsPathList G P) (hPF : ∀ z ∈ P, z ∈ F)
    (a1 a2 w : U) (haw : J.Adj a1 w) (ha12 : J.Adj a1 a2) (hwa2 : w ≠ a2) (ha1ne2 : a1 ≠ a2)
    (p1 p2 y1 x0 : V) (hp1P : p1 ∈ P) (hp2P : p2 ∈ P)
    (hy1S : y1 ∈ S a1 w) (hx0S : x0 ∈ S a1 a2) (hx0notN : x0 ∉ N a1)
    (hy1adj : G.Adj p1 y1) (hx0adj : G.Adj p2 x0) :
    {z : V | z ∈ P} = F := by
  have hy1att : y1 ∈ attachments G {z : V | z ∈ P} (stripSystemVertices J S) :=
    ⟨StripSystemBasics.strip_subset_vertices haw hy1S, p1, hp1P, hy1adj.symm⟩
  have hx0att : x0 ∈ attachments G {z : V | z ∈ P} (stripSystemVertices J S) :=
    ⟨StripSystemBasics.strip_subset_vertices ha12 hx0S, p2, hp2P, hx0adj.symm⟩
  have hnotlocal : ¬ LocalForStripSystem J S N
      (attachments G {z : V | z ∈ P} (stripSystemVertices J S)) := by
    rintro (⟨c, hc⟩ | ⟨c, d, hcd, hsub⟩)
    · have hy1v : y1 ∈ N c := hc hy1att
      have hx0v : x0 ∈ N c := hc hx0att
      have hca2 : c = a2 := by
        by_contra hcon
        have hca1 : c ≠ a1 := by rintro rfl; exact hx0notN hx0v
        have h0 : x0 ∈ S a1 a2 ∩ N c := ⟨hx0S, hx0v⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN ha12 hca1 hcon] at h0
        exact h0
      subst hca2
      have h0 : y1 ∈ S a1 w ∩ N c := ⟨hy1S, hy1v⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN haw (Ne.symm ha1ne2)
        (Ne.symm hwa2)] at h0
      exact h0
    · have h1 : s(c, d) = s(a1, w) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hcd haw (hsub hy1att) hy1S
      have h2 : s(c, d) = s(a1, a2) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hcd ha12 (hsub hx0att) hx0S
      rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨-, h4⟩ | ⟨h3, -⟩
      · exact hwa2 h4
      · exact ha1ne2 h3
  exact hFmin {z : V | z ∈ P} (fun z hz => hPF z hz)
    (Workspace.ProofLemmas.KiteTailBasics.connectedSet_of_isPathList hP) hnotlocal

end Workspace.ProofLemmas.Thm85Claim3Common
