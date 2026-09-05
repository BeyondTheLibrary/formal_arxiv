import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.RungReplacementDelete
import Workspace.ProofLemmas.RungReplacementAddTrack
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.RungReplacementDegrees
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.RungReplacementMaximality
import Workspace.ProofLemmas.RungReplacementResidual
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.TrackSlice

/-!
# The structural half of the rung replacement of 7.5, isolated

PAPER (proof of 7.5, claim (2), printed p. 37):

> *"So if in `L(H)` we replace `Rb₁b₂` by `R′` we obtain another appearance of `J` in `G`, say
> `L(H′)`, where `H′` is obtained from `H` by replacing the branch `Bb₁b₂` by some new branch
> `B′` joining the same two vertices."*

The rest of the rung-replacement machinery — the residual appearance
(`Workspace.ProofLemmas.RungReplacementDelete`), the labelled add-track step
(`Workspace.ProofLemmas.RungReplacementAddTrack`) and the clique dictionary
(`Workspace.ProofLemmas.RungReplacementLabels`) — is proved.  What is stated without proof here
is the purely structural content of the sentence above, in four pieces:

1. the surgery produces a **subdivision of `J`** again;
2. it produces a **bipartite** graph, provided the new track has the same parity as the old
   branch (this is the paper's standing assumption that `H′` is again a bipartite subdivision);
3. the new track is a **branch** of the new graph;
4. every other branch of `H` is still a **branch** of the new graph, with the same ends.

All four are the same fact from four angles: the presentation of `H` as a subdivision of `J`
carries over verbatim once the track attached to the edge `b₁b₂` of `J` is replaced by the new
one.  A Lean proof has to build the replacement presentation and re-verify the eight clauses of
`Workspace.Types.Tracks.IsSubdivision`, and for (3) and (4) has to re-verify maximality of the
tracks as subgraphs.  That work is not done here.

Every statement below is about the concrete surgery: `H` with the branch `q` deleted
(`resGraph H q`) and one new track added (`IsBranchExtension`).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementSurgeryGaps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.RungReplacementDelete
open Workspace.ProofLemmas.RungReplacementAddTrack

variable {U W Z : Type*}

/-- **GAP (paper 7.5, printed p. 37).**  PAPER: *"`H′` is obtained from `H` by replacing the
branch `Bb₁b₂` by some new branch `B′` joining the same two vertices"* — in particular `H′` is
again a subdivision of `J`.

Take the presentation of `H` as a subdivision of `J`, and replace the two orientations of the
track attached to the edge of `J` whose ends are `b₁` and `b₂` by the new track `q'` and its
reverse; map every other track through `rho`.  Coverage holds because every deleted vertex was
internal to precisely that track. -/
theorem subdivision_of_replacement [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q') :
    IsSubdivision J D := by
  classical
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisj, hnew0, hcover, hedges⟩ := id hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hends := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub q b₁ b₂ hq hqf (by simp only [trackLength]; omega)
  -- The branch `q` is one of the subdividing tracks, oriented so that `b₁ = ι a`, `b₂ = ι b`.
  have hchoice : ∃ a b : U, J.Adj a b ∧ trackEdges q = trackEdges (T a b) ∧
      b₁ = ι a ∧ b₂ = ι b := by
    obtain ⟨a, b, hab, hE, h | h⟩ :=
      Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
        hι htrack hlenT hrev hdisj hnew0 hcover hedges hdeg hq hq2 hqf hends.1 hends.2
    · exact ⟨a, b, hab, hE, h.1, h.2⟩
    · refine ⟨b, a, hab.symm, ?_, h.1, h.2⟩
      rw [hrev a b hab, SubdivisionCounting.trackEdges_reverse]
      exact hE
  obtain ⟨a, b, hab, hEq, hb1eq, hb2eq⟩ := hchoice
  have hqT : q = T a b := by
    refine Workspace.ProofLemmas.RungReplacementMaximality.eq_of_trackEdges_subset hqf ?_
      (le_of_eq hEq)
    rw [hb1eq, hb2eq]; exact htrack a b hab
  -- the retained part of `H`, mapped into `Z`
  set ρ : W → Z := fun w => rho (resEmb q b₁ hb₁ w) with hρdef
  have hρe : ∀ (w : W) (h : w ∉ trackInterior q), ρ w = rho ⟨w, h⟩ := by
    intro w h; simp only [hρdef, resEmb_of_notMem q b₁ hb₁ h]
  have hρinj : ∀ x y : W, x ∉ trackInterior q → y ∉ trackInterior q → ρ x = ρ y → x = y := by
    intro x y hx hy hxy
    rw [hρe x hx, hρe y hy] at hxy
    exact Subtype.ext_iff.mp (hext.inj hxy)
  have hrange : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlenT hdisj hnew0 hdeg
  have hnotint : ∀ u : U, ι u ∉ trackInterior q := fun u h => hq.2.1 _ h (hrange ⟨u, rfl⟩)
  have hclosed := Workspace.ProofLemmas.RungReplacementBranchFacts.edges_off_branch_avoid_interior
    hJ hsub hq hq2
  have holdAdj : ∀ x y : W, H.Adj x y → s(x, y) ∉ trackEdges q → D.Adj (ρ x) (ρ y) := by
    intro x y hxy hne
    have hx : x ∉ trackInterior q := hclosed _ hxy hne x (by simp)
    have hy : y ∉ trackInterior q := hclosed _ hxy hne y (by simp)
    rw [hρe x hx, hρe y hy]
    exact hext.oldAdj _ _ ⟨hxy, hne⟩
  -- vertices and edges of the other tracks avoid the deleted branch
  have hmemq : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → ∀ w ∈ T u v, w ∉ trackInterior q := by
    intro u v huv hne w hw hwi
    exact hdisj a b u v hab huv (Ne.symm hne) w (hqT ▸ hwi) hw
  have hedgeq : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) →
      ∀ e ∈ trackEdges (T u v), e ∉ trackEdges q := by
    intro u v huv hne e he hq'
    exact hne (SubdivisionCounting.trackEdges_disjoint hι htrack hlenT hdisj u v a b huv hab e he
      (hqT ▸ hq'))
  -- the replacement family of tracks
  set R : U → U → List Z := fun u v =>
    if u = a ∧ v = b then q' else if u = b ∧ v = a then q'.reverse else (T u v).map ρ with hRdef
  have hne_ab : a ≠ b := hab.ne
  have hR : R a b = q' := by simp [hRdef]
  have hRr : R b a = q'.reverse := by simp [hRdef, hne_ab, hne_ab.symm]
  have hRo : ∀ u v : U, s(u, v) ≠ s(a, b) → R u v = (T u v).map ρ := by
    intro u v hne
    have h1 : ¬ (u = a ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
    have h2 : ¬ (u = b ∧ v = a) := by rintro ⟨rfl, rfl⟩; exact hne (Sym2.eq_swap)
    simp [hRdef, h1, h2]
  have hab_cases : ∀ u v : U, s(u, v) = s(a, b) → (u = a ∧ v = b) ∨ (u = b ∧ v = a) :=
    fun u v h => Sym2.eq_iff.mp h
  have hRab_int : ∀ u v : U, s(u, v) = s(a, b) → ∀ z ∈ trackInterior (R u v),
      z ∈ trackInterior q' := by
    intro u v h z hz
    rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [hR] at hz
    · rw [hRr, TrackSlice.trackInterior_reverse, List.mem_reverse] at hz; exact hz
  have hRab_mem : ∀ u v : U, s(u, v) = s(a, b) → ∀ z ∈ R u v, z ∈ q' := by
    intro u v h z hz
    rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [hR] at hz
    · rw [hRr, List.mem_reverse] at hz; exact hz
  have hRab_edges : ∀ u v : U, s(u, v) = s(a, b) → trackEdges (R u v) = trackEdges q' := by
    intro u v h
    rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hR]
    · rw [hRr, SubdivisionCounting.trackEdges_reverse]
  have hTab_int : ∀ u v : U, J.Adj u v → s(u, v) = s(a, b) →
      ∀ w ∈ trackInterior (T u v), w ∈ trackInterior q := by
    intro u v huv h w hw
    rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hqT]; exact hw
    · rw [hrev v u huv.symm, TrackSlice.trackInterior_reverse, List.mem_reverse] at hw
      rw [hqT]; exact hw
  have hTab_edges : ∀ u v : U, J.Adj u v → s(u, v) = s(a, b) →
      trackEdges (T u v) = trackEdges q := by
    intro u v huv h
    rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hqT]
    · rw [hrev v u huv.symm, SubdivisionCounting.trackEdges_reverse, hqT]
  -- `ρ` sends the interior of another track off the new track
  have hoff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → ∀ w ∈ trackInterior (T u v),
      ρ w ∉ q' := by
    intro u v huv hne w hw
    have hwq : w ∉ trackInterior q :=
      hmemq u v huv hne w (List.tail_subset _ (List.dropLast_subset _ hw)) 
    rw [hρe w hwq]
    refine Workspace.ProofLemmas.RungReplacementDegrees.rho_notMem_track
      (w₀ := ⟨w, hwq⟩) hext (fun h => ?_) (fun h => ?_)
    · exact hnew0 u v huv w hw ⟨a, by rw [← hb1eq]; exact (Subtype.ext_iff.mp h).symm⟩
    · exact hnew0 u v huv w hw ⟨b, by rw [← hb2eq]; exact (Subtype.ext_iff.mp h).symm⟩
  -- tracks of `H` other than the deleted branch survive
  have hmaptrack : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) →
      IsTrackFrom D ((T u v).map ρ) (ρ (ι u)) (ρ (ι v)) := by
    intro u v huv hne
    have h := htrack u v huv
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro hn; exact h.1.1 (List.map_eq_nil_iff.mp hn)
    · refine h.1.2.1.map_on ?_
      intro x hx y hy hxy
      exact hρinj x y (hmemq u v huv hne x hx) (hmemq u v huv hne y hy) hxy
    · intro i hi
      have hi' : i + 1 < (T u v).length := by simpa using hi
      simp only [List.getElem_map]
      refine holdAdj _ _ (h.1.2.2 i hi') ?_
      exact hedgeq u v huv hne _ ⟨i, hi', rfl⟩
    · simp only [List.head?_map, h.2.1, Option.map_some]
    · simp only [List.getLast?_map, h.2.2, Option.map_some]
  -- the two orientations of the new track are tracks from `ρ (ι a)` to `ρ (ι b)`
  have htrack_ab : IsTrackFrom D q' (ρ (ι a)) (ρ (ι b)) := by
    rw [← hb1eq, ← hb2eq, hρe b₁ hb₁, hρe b₂ hb₂]
    exact hext.track
  refine ⟨fun u => ρ (ι u), R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    exact hι (hρinj _ _ (hnotint u) (hnotint v) h)
  · intro u v huv
    by_cases h : s(u, v) = s(a, b)
    · rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hR]; exact htrack_ab
      · rw [hRr]; exact TrackSlice.isTrackFrom_reverse htrack_ab
    · rw [hRo u v h]; exact hmaptrack u v huv h
  · intro u v huv
    by_cases h : s(u, v) = s(a, b)
    · rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hR]; have := hext.length; simp only [trackLength]; omega
      · rw [hRr]; have := hext.length; simp only [trackLength, List.length_reverse]; omega
    · rw [hRo u v h]
      simpa only [trackLength, List.length_map] using hlenT u v huv
  · intro u v huv
    by_cases h : s(u, v) = s(a, b)
    · rcases hab_cases u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hR, hRr]
      · rw [hR, hRr, List.reverse_reverse]
    · have h' : s(v, u) ≠ s(a, b) := fun hc => h (Sym2.eq_swap.trans hc)
      rw [hRo u v h, hRo v u h', hrev u v huv, List.map_reverse]
  · intro u v u' v' huv hu'v' hne z hz hz'
    by_cases h : s(u, v) = s(a, b)
    · -- the new track's interior consists of brand new vertices
      have hzq' : z ∈ trackInterior q' := hRab_int u v h z hz
      have h' : s(u', v') ≠ s(a, b) := fun hc => hne (h.trans hc.symm)
      rw [hRo u' v' h'] at hz'
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hz'
      exact hext.newInterior z hzq' ⟨resEmb q b₁ hb₁ w, hw⟩
    · rw [hRo u v h, SubdivisionCounting.trackInterior_map] at hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hwq : w ∉ trackInterior q :=
        hmemq u v huv h w (List.tail_subset _ (List.dropLast_subset _ hw))
      by_cases h' : s(u', v') = s(a, b)
      · exact hoff u v huv h w hw (hRab_mem u' v' h' _ hz')
      · rw [hRo u' v' h'] at hz'
        obtain ⟨w', hw', he⟩ := List.mem_map.mp hz'
        have : w = w' := hρinj _ _ hwq (hmemq u' v' hu'v' h' w' hw') he.symm
        exact hdisj u v u' v' huv hu'v' hne w hw (this ▸ hw')
  · intro u v huv z hz ⟨u', hu'⟩
    by_cases h : s(u, v) = s(a, b)
    · exact hext.newInterior z (hRab_int u v h z hz) ⟨resEmb q b₁ hb₁ (ι u'), hu'⟩
    · rw [hRo u v h, SubdivisionCounting.trackInterior_map] at hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hwq : w ∉ trackInterior q :=
        hmemq u v huv h w (List.tail_subset _ (List.dropLast_subset _ hw))
      have : ι u' = w := hρinj _ _ (hnotint u') hwq hu'
      exact hnew0 u v huv w hw ⟨u', this⟩
  · intro z
    rcases hext.cover z with ⟨w₀, rfl⟩ | hz
    · have hz : rho w₀ = ρ (w₀ : W) := by
        rw [hρe (w₀ : W) w₀.2]
      rcases hcover (w₀ : W) with ⟨u, hu⟩ | ⟨u, v, huv, hw⟩
      · exact Or.inl ⟨u, by rw [hz, hu]⟩
      · by_cases h : s(u, v) = s(a, b)
        · exact absurd (hTab_int u v huv h _ hw) w₀.2
        · refine Or.inr ⟨u, v, huv, ?_⟩
          rw [hRo u v h, SubdivisionCounting.trackInterior_map, hz]
          exact List.mem_map.mpr ⟨(w₀ : W), hw, rfl⟩
    · exact Or.inr ⟨a, b, hab, by rw [hR]; exact hz⟩
  · have hmapcomp : ∀ f : Sym2 (resVerts q), Sym2.map ρ (Sym2.map Subtype.val f) =
        Sym2.map rho f := by
      intro f
      induction f using Sym2.ind with
      | _ x y => simp only [Sym2.map_mk]; rw [hρe x.val x.2, hρe y.val y.2]
    ext e
    rw [hext.edges]
    simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro (⟨f, hf, rfl⟩ | he)
      · obtain ⟨hf1, hf2⟩ := (mem_resGraph_edgeSet f).mp hf
        rw [hedges] at hf1
        simp only [Set.mem_iUnion] at hf1
        obtain ⟨u, v, huv, hf1⟩ := hf1
        have h : s(u, v) ≠ s(a, b) := by
          intro hc; exact hf2 (by rw [← hTab_edges u v huv hc]; exact hf1)
        refine ⟨u, v, huv, ?_⟩
        rw [hRo u v h, SubdivisionCounting.trackEdges_map]
        exact ⟨_, hf1, hmapcomp f⟩
      · exact ⟨a, b, hab, by rw [hR]; exact he⟩
    · rintro ⟨u, v, huv, he⟩
      by_cases h : s(u, v) = s(a, b)
      · exact Or.inr (by rw [← hRab_edges u v h]; exact he)
      · rw [hRo u v h, SubdivisionCounting.trackEdges_map] at he
        obtain ⟨g, hg, rfl⟩ := he
        have hgv : ∀ w ∈ g, w ∉ trackInterior q := by
          intro w hw
          exact hmemq u v huv h w
            (Workspace.ProofLemmas.RungReplacementBranchFacts.mem_list_of_mem_trackEdges hg hw)
        obtain ⟨f, hf⟩ := exists_sym2_lift g hgv
        refine Or.inl ⟨f, ?_, ?_⟩
        · refine (mem_resGraph_edgeSet f).mpr ⟨?_, ?_⟩
          · rw [hf, hedges]
            exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨huv, hg⟩⟩⟩
          · rw [hf]; exact hedgeq u v huv h g hg
        · rw [← hmapcomp f, hf]

/-- **GAP (paper 7.5, printed p. 37).**  The new graph is bipartite.

`IsAppearance` demands a *bipartite* subdivision, and replacing one track shifts the length of
every cycle of `H` through that track by `trackLength q' - trackLength q`.  Restrict a
two-colouring of `H` to the retained vertices and colour the new internal vertices alternately
starting from the colour of `b₁`; the parity hypothesis makes the constraint at `b₂` hold. -/
theorem bipartite_of_replacement [Fintype U] [Fintype W]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    (hbip : H.IsBipartite)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    (hpar : Even (trackLength q') ↔ Even (trackLength q)) :
    D.IsBipartite := by
  classical
  obtain ⟨C⟩ := hbip
  have hlen' := hext.length
  have hnd' : q'.Nodup := hext.track.1.2.1
  -- `swap` exchanges the two colours.
  let swap : Fin 2 → Fin 2 := fun x => if x = 0 then 1 else 0
  have hswap_ne : ∀ x : Fin 2, swap x ≠ x := by decide
  have hswap_swap : ∀ x : Fin 2, swap (swap x) = x := by decide
  have hne_swap : ∀ x y : Fin 2, x ≠ y → y = swap x := by decide
  -- `alt x j` is the colour reached after `j` steps starting from `x`.
  let alt : Fin 2 → ℕ → Fin 2 := fun x j => if j % 2 = 0 then x else swap x
  have halt_zero : ∀ x : Fin 2, alt x 0 = x := by intro x; simp [alt]
  have halt_step : ∀ (x : Fin 2) (j : ℕ), swap (alt x j) = alt x (j + 1) := by
    intro x j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · simp only [alt, if_pos h, if_neg (by omega : ¬ (j + 1) % 2 = 0)]
    · simp only [alt, if_neg (by omega : ¬ j % 2 = 0), if_pos (by omega : (j + 1) % 2 = 0)]
      exact hswap_swap x
  have halt_ne : ∀ (x : Fin 2) (j : ℕ), alt x j ≠ alt x (j + 1) := by
    intro x j
    rw [← halt_step x j]
    exact fun hc => hswap_ne _ hc.symm
  have halt_congr : ∀ (x : Fin 2) (j k : ℕ), j % 2 = k % 2 → alt x j = alt x k := by
    intro x j k h
    simp only [alt, h]
  -- Colours alternate along any track of `H`.
  have halong : ∀ (t : List W), IsTrackList H t → ∀ (j : ℕ) (hj : j < t.length),
      C (t[j]'hj) = alt (C (t[0]'(by omega))) j := by
    intro t ht j
    induction j with
    | zero => intro hj; rw [halt_zero]
    | succ k ih =>
      intro hj
      have hk : k < t.length := by omega
      have hadj : H.Adj (t[k]'hk) (t[k + 1]'hj) := ht.2.2 k hj
      rw [hne_swap _ _ (C.valid hadj), ih hk, halt_step]
  -- The two ends of the deleted branch get colours differing by `trackLength q`.
  have hq0 : q[0]'(by omega) = b₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hqf (by omega)
  have hqL : q[q.length - 1]'(by omega) = b₂ := by
    have h' := hqf.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  have hCb₂ : C b₂ = alt (C b₁) (trackLength q) := by
    have := halong q hq.1 (q.length - 1) (by omega)
    rw [hqL, hq0] at this
    rw [this]
    rfl
  -- The same difference, expressed with the length of the new track.
  have hpar' : trackLength q' % 2 = trackLength q % 2 := by
    have h1 := hpar
    simp only [Nat.even_iff] at h1
    omega
  have hCb₂' : C b₂ = alt (C b₁) (q'.length - 1) := by
    rw [hCb₂]
    exact (halt_congr (C b₁) (trackLength q) (q'.length - 1) (by
      simp only [trackLength] at hpar' ⊢; omega))
  -- The colouring of the new graph.
  let col : Z → Fin 2 := fun z =>
    if h : ∃ w : resVerts q, rho w = z then C (Classical.choose h).val
    else alt (C b₁) (q'.idxOf z)
  have hcol_rho : ∀ w : resVerts q, col (rho w) = C w.val := by
    intro w
    have h : ∃ w' : resVerts q, rho w' = rho w := ⟨w, rfl⟩
    show (if h' : ∃ w' : resVerts q, rho w' = rho w then C (Classical.choose h').val
      else alt (C b₁) (q'.idxOf (rho w))) = C w.val
    rw [dif_pos h]
    exact congrArg C (congrArg Subtype.val (hext.inj (Classical.choose_spec h)))
  have hq'0 : q'[0]'(by omega) = rho ⟨b₁, hb₁⟩ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  have hq'L : q'[q'.length - 1]'(by omega) = rho ⟨b₂, hb₂⟩ := by
    have h' := hext.track.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  have hcol_new : ∀ (j : ℕ) (hj : j < q'.length), col (q'[j]'hj) = alt (C b₁) j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [hq'0, hcol_rho, halt_zero]
    · rcases Nat.lt_or_ge j (q'.length - 1) with hlt | hge
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hint : q'[k + 1]'hj ∈ trackInterior q' :=
          Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q' k (by omega)
        have hnr : ¬ ∃ w : resVerts q, rho w = q'[k + 1]'hj := by
          rintro ⟨w, hw⟩
          exact hext.newInterior _ hint ⟨w, hw⟩
        show (if h' : ∃ w : resVerts q, rho w = q'[k + 1]'hj then C (Classical.choose h').val
          else alt (C b₁) (q'.idxOf (q'[k + 1]'hj))) = alt (C b₁) (k + 1)
        rw [dif_neg hnr, hnd'.idxOf_getElem (k + 1) hj]
      · have hjeq : j = q'.length - 1 := by omega
        subst hjeq
        rw [hq'L, hcol_rho]
        exact hCb₂'
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro a b hab
  have hedge : s(a, b) ∈ D.edgeSet := hab
  rw [hext.edges] at hedge
  rcases hedge with ⟨e₀, he₀, heq⟩ | ⟨j, hj, heq⟩
  · induction e₀ using Sym2.ind with
    | _ x y =>
      have hxy : (resGraph H q).Adj x y := he₀
      have heq' : s(rho x, rho y) = s(a, b) := heq
      rcases Sym2.eq_iff.mp heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hcol_rho, hcol_rho]
        exact C.valid hxy.1
      · rw [← h1, ← h2, hcol_rho, hcol_rho]
        exact C.valid hxy.1.symm
  · have heq' : s(q'[j]'(by omega), q'[j + 1]'hj) = s(a, b) := heq.symm
    rcases Sym2.eq_iff.mp heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, hcol_new j (by omega), hcol_new (j + 1) hj]
      exact halt_ne _ _
    · rw [← h1, ← h2, hcol_new j (by omega), hcol_new (j + 1) hj]
      exact (halt_ne _ _).symm

/-- The two ends of the deleted branch are still branch-vertices after the surgery: each of
them loses its neighbour on the old branch and gains one on the new one. -/
theorem branchVertex_ends [Fintype U] [Fintype W] [Finite Z]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q') :
    rho ⟨b₁, hb₁⟩ ∈ branchVertices D ∧ rho ⟨b₂, hb₂⟩ ∈ branchVertices D := by
  have hq'2 := hext.length
  have hnd : q.Nodup := hq.1.2.1
  have hnd' : q'.Nodup := hext.track.1.2.1
  have hclosed := Workspace.ProofLemmas.RungReplacementBranchFacts.edges_off_branch_avoid_interior hJ hsub hq hq2
  have hnadj := Workspace.ProofLemmas.RungReplacementResidual.not_resGraph_adj_ends
    hJ hsub hq hqf hq2 hb₁ hb₂
  have hends := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub q b₁ b₂ hq hqf (by simp only [trackLength]; omega)
  have hq0 : q[0]'(by omega) = b₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hqf (by omega)
  have hqL : q[q.length - 1]'(by omega) = b₂ := by
    have h' := hqf.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  have hq'0 : q'[0]'(by omega) = rho ⟨b₁, hb₁⟩ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  have hq'L : q'[q'.length - 1]'(by omega) = rho ⟨b₂, hb₂⟩ := by
    have h' := hext.track.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  -- the unique old-branch neighbour of each end
  have huniq₁ : ∀ y : W, H.Adj b₁ y → s(b₁, y) ∈ trackEdges q → y = q[1]'(by omega) := by
    intro y hy ⟨i, hi, hie⟩
    rcases Sym2.eq_iff.mp hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (0 : ℕ) = i := hnd.getElem_inj_iff.mp (by rw [hq0]; exact h1)
      subst this
      exact h2
    · exfalso
      have : (0 : ℕ) = i + 1 := hnd.getElem_inj_iff.mp (by rw [hq0]; exact h1)
      omega
  have huniq₂ : ∀ y : W, H.Adj b₂ y → s(b₂, y) ∈ trackEdges q →
      y = q[q.length - 2]'(by omega) := by
    intro y hy ⟨i, hi, hie⟩
    rcases Sym2.eq_iff.mp hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have : q.length - 1 = i := hnd.getElem_inj_iff.mp (by rw [hqL]; exact h1)
      omega
    · have hidx : q.length - 1 = i + 1 := hnd.getElem_inj_iff.mp (by rw [hqL]; exact h1)
      rw [h2]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (by omega) (by omega) (by omega)
  have hd₁ : H.Adj b₁ (q[1]'(by omega)) := by rw [← hq0]; exact hq.1.2.2 0 (by omega)
  have hd₂ : H.Adj b₂ (q[q.length - 2]'(by omega)) := by
    have := hq.1.2.2 (q.length - 2) (by omega)
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
      (show q.length - 2 + 1 = q.length - 1 by omega) (by omega) (by omega), hqL] at this
    exact this.symm
  have hdq₁ : s(b₁, q[1]'(by omega)) ∈ trackEdges q := ⟨0, by omega, by rw [hq0]⟩
  have hdq₂ : s(b₂, q[q.length - 2]'(by omega)) ∈ trackEdges q := by
    refine ⟨q.length - 2, by omega, ?_⟩
    rw [Sym2.eq_swap,
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show q.length - 2 + 1 = q.length - 1 by omega) (by omega) (by omega), hqL]
  -- the new neighbour of each end is not an old neighbour
  have hznot₁ : ∀ y₀ : resVerts q, (resGraph H q).Adj ⟨b₁, hb₁⟩ y₀ →
      rho y₀ ≠ q'[1]'(by omega) := by
    intro y₀ hy₀ hcon
    rcases Nat.lt_or_ge q'.length 3 with hlt | hge
    · have hlen2 : q'.length = 2 := by omega
      have : q'[1]'(by omega) = rho ⟨b₂, hb₂⟩ := by
        rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q'
          (show (1 : ℕ) = q'.length - 1 by omega) (by omega) (by omega)]
        exact hq'L
      rw [this] at hcon
      rw [hext.inj hcon] at hy₀
      exact hnadj hy₀
    · exact hext.newInterior _
        (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q' 0 (by omega))
        ⟨y₀, hcon⟩
  have hznot₂ : ∀ y₀ : resVerts q, (resGraph H q).Adj ⟨b₂, hb₂⟩ y₀ →
      rho y₀ ≠ q'[q'.length - 2]'(by omega) := by
    intro y₀ hy₀ hcon
    rcases Nat.lt_or_ge q'.length 3 with hlt | hge
    · have hlen2 : q'.length = 2 := by omega
      have : q'[q'.length - 2]'(by omega) = rho ⟨b₁, hb₁⟩ := by
        rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q'
          (show q'.length - 2 = 0 by omega) (by omega) (by omega)]
        exact hq'0
      rw [this] at hcon
      rw [hext.inj hcon] at hy₀
      exact hnadj hy₀.symm
    · refine hext.newInterior _ ?_ ⟨y₀, hcon⟩
      have := Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q'
        (q'.length - 3) (by omega)
      rwa [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q'
        (show q'.length - 3 + 1 = q'.length - 2 by omega) (by omega) (by omega)] at this
  have hzadj₁ : D.Adj (rho ⟨b₁, hb₁⟩) (q'[1]'(by omega)) := by
    rw [← hq'0]; exact hext.track.1.2.2 0 (by omega)
  have hzadj₂ : D.Adj (rho ⟨b₂, hb₂⟩) (q'[q'.length - 2]'(by omega)) := by
    have := hext.track.1.2.2 (q'.length - 2) (by omega)
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q'
      (show q'.length - 2 + 1 = q'.length - 1 by omega) (by omega) (by omega), hq'L] at this
    exact this.symm
  refine ⟨Workspace.ProofLemmas.RungReplacementDegrees.branchVertex_end hext hclosed hb₁
      hd₁ hdq₁ huniq₁ hzadj₁ hznot₁ hends.1,
    Workspace.ProofLemmas.RungReplacementDegrees.branchVertex_end hext hclosed hb₂
      hd₂ hdq₂ huniq₂ hzadj₂ hznot₂ hends.2⟩

/-- **Every branch-vertex of `H` outside the interior of the deleted branch is still a
branch-vertex.** -/
theorem branchVertex_map [Fintype U] [Fintype W] [Finite Z]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {w : W} (hw : w ∉ trackInterior q) (hwb : w ∈ branchVertices H) :
    rho ⟨w, hw⟩ ∈ branchVertices D := by
  have hclosed :=
    Workspace.ProofLemmas.RungReplacementBranchFacts.edges_off_branch_avoid_interior
      hJ hsub hq hq2
  by_cases hw₁ : w = b₁
  · subst hw₁
    exact (branchVertex_ends hJ hsub hq hqf hq2 hw hb₂ hext).1
  · by_cases hw₂ : w = b₂
    · subst hw₂
      exact (branchVertex_ends hJ hsub hq hqf hq2 hb₁ hw hext).2
    · have hwq : w ∉ q := by
        intro hcon
        rcases Workspace.ProofLemmas.RungReplacementResidual.mem_track_cases hqf hq2 hcon with
          h | h | h
        · exact hw₁ h
        · exact hw₂ h
        · exact hw h
      have hnq' := Workspace.ProofLemmas.RungReplacementDegrees.rho_notMem_track
        (w₀ := ⟨w, hw⟩) hext
        (fun h => hw₁ (Subtype.ext_iff.mp h)) (fun h => hw₂ (Subtype.ext_iff.mp h))
      have hcard := Workspace.ProofLemmas.RungReplacementDegrees.ncard_neighborSet_of_notMem
        hext hclosed hwq hw hnq'
      simp only [branchVertices, Set.mem_setOf_eq] at hwb ⊢
      omega

/-- A vertex of `H` off the deleted branch that was not a branch-vertex does not become one. -/
theorem not_branchVertex_map [Fintype U] [Fintype W] [Finite Z]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {w : W} (hw : w ∉ trackInterior q) (hwq : w ∉ q) (hwb : w ∉ branchVertices H) :
    rho ⟨w, hw⟩ ∉ branchVertices D := by
  have hclosed :=
    Workspace.ProofLemmas.RungReplacementBranchFacts.edges_off_branch_avoid_interior
      hJ hsub hq hq2
  have hb₁q : b₁ ∈ q := List.mem_of_mem_head? hqf.2.1
  have hb₂q : b₂ ∈ q := List.mem_of_mem_getLast? hqf.2.2
  have hnq' := Workspace.ProofLemmas.RungReplacementDegrees.rho_notMem_track
    (w₀ := ⟨w, hw⟩) hext
    (fun h => hwq (by rw [show w = b₁ from Subtype.ext_iff.mp h]; exact hb₁q))
    (fun h => hwq (by rw [show w = b₂ from Subtype.ext_iff.mp h]; exact hb₂q))
  have hcard := Workspace.ProofLemmas.RungReplacementDegrees.ncard_neighborSet_of_notMem
    hext hclosed hwq hw hnq'
  simp only [branchVertices, Set.mem_setOf_eq] at hwb ⊢
  omega

/-- **GAP (paper 7.5, printed p. 37).**  PAPER: *"some new branch `B′`"* — the new track really
is a branch of the new graph. -/
theorem isBranch_new [Fintype U] [Fintype W] [Finite Z]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q') :
    IsBranch D q' := by
  obtain ⟨hu, hv⟩ := branchVertex_ends hJ hsub hq hqf hq2 hb₁ hb₂ hext
  exact Workspace.ProofLemmas.RungReplacementMaximality.isBranch_of_ends hext.track hext.length
    (fun x hx => Workspace.ProofLemmas.RungReplacementDegrees.not_branchVertex_new_interior
      hext hx) hu hv

/-- **GAP (paper 7.5, printed p. 37).**  PAPER: *"`N′v = Nv` for all vertices `v` of `J` except
for `b₁` and `b₂`"* — the branches of `H` other than the replaced one survive as branches.

Such a branch has no vertex in the interior of `q`
(`Workspace.ProofLemmas.RungReplacementBranchFacts.other_branch_avoids_interior`), so it is
carried into `D` vertex by vertex; only its maximality has to be re-checked, and that is
because the degrees of all of its vertices are unchanged. -/
theorem branch_survives [Fintype U] [Fintype W] [Finite Z]
    {J : SimpleGraph U} {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hq2 : 2 ≤ q.length) (hb₁ : b₁ ∉ trackInterior q) (hb₂ : b₂ ∉ trackInterior q)
    {D : SimpleGraph Z} {q' : List Z} {rho : resVerts q → Z}
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {p : List W} {u v : W} (hp : IsBranch H p) (hp2 : 2 ≤ p.length)
    (hpf : IsTrackFrom H p u v) (hpq : trackEdges p ≠ trackEdges q) :
    IsBranch D (p.map (fun w => rho (resEmb q b₁ hb₁ w))) ∧
      IsTrackFrom D (p.map (fun w => rho (resEmb q b₁ hb₁ w)))
        (rho (resEmb q b₁ hb₁ u)) (rho (resEmb q b₁ hb₁ v)) := by
  have hpin := Workspace.ProofLemmas.RungReplacementBranchFacts.other_branch_avoids_interior
    hJ hsub hq hq2 hp hp2 hpq
  have hpqe := Workspace.ProofLemmas.RungReplacementBranchFacts.trackEdges_disjoint_of_ne
    hJ hsub hq hq2 hp hp2 hpq
  have hρ : ∀ (w : W) (hw : w ∈ p), resEmb q b₁ hb₁ w = ⟨w, hpin w hw⟩ :=
    fun w hw => resEmb_of_notMem q b₁ hb₁ (hpin w hw)
  have hinjp : ∀ x ∈ p, ∀ y ∈ p,
      (fun w => rho (resEmb q b₁ hb₁ w)) x = (fun w => rho (resEmb q b₁ hb₁ w)) y → x = y := by
    intro x hx y hy hxy
    have hEq := hext.inj hxy
    rw [hρ x hx, hρ y hy] at hEq
    exact Subtype.ext_iff.mp hEq
  have htl : IsTrackList D (p.map (fun w => rho (resEmb q b₁ hb₁ w))) := by
    refine ⟨by simpa using hp.1.1, hp.1.2.1.map_on hinjp, ?_⟩
    intro i hi
    have hi' : i + 1 < p.length := by simpa using hi
    simp only [List.getElem_map]
    rw [hρ _ (List.getElem_mem _), hρ _ (List.getElem_mem _)]
    exact hext.oldAdj _ _ ⟨hp.1.2.2 i hi', hpqe _ ⟨i, hi', rfl⟩⟩
  have htf : IsTrackFrom D (p.map (fun w => rho (resEmb q b₁ hb₁ w)))
      (rho (resEmb q b₁ hb₁ u)) (rho (resEmb q b₁ hb₁ v)) := by
    refine ⟨htl, ?_, ?_⟩
    · rw [List.head?_map, hpf.2.1]; rfl
    · rw [List.getLast?_map, hpf.2.2]; rfl
  refine ⟨?_, htf⟩
  have hendsq := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub q b₁ b₂ hq hqf (by simp only [trackLength]; omega)
  have hendsp := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub p u v hp hpf (by simp only [trackLength]; omega)
  refine Workspace.ProofLemmas.RungReplacementMaximality.isBranch_of_ends htf
    (by simpa using hp2) ?_ ?_ ?_
  · intro x hx
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have hwp : w ∈ p := List.tail_subset _ (List.dropLast_subset _ hw)
    have hwb : w ∉ branchVertices H := hp.2.1 w hw
    have hwq : w ∉ q := by
      intro hcon
      rcases Workspace.ProofLemmas.RungReplacementResidual.mem_track_cases hqf hq2 hcon with
        h | h | h
      · exact hwb (h ▸ hendsq.1)
      · exact hwb (h ▸ hendsq.2)
      · exact hpin w hwp h
    rw [hρ w hwp]
    exact not_branchVertex_map hJ hsub hq hqf hq2 hb₁ hb₂ hext (hpin w hwp) hwq hwb
  · rw [hρ u (List.mem_of_mem_head? hpf.2.1)]
    exact branchVertex_map hJ hsub hq hqf hq2 hb₁ hb₂ hext _ hendsp.1
  · rw [hρ v (List.mem_of_mem_getLast? hpf.2.2)]
    exact branchVertex_map hJ hsub hq hqf hq2 hb₁ hb₂ hext _ hendsp.2

end Workspace.ProofLemmas.RungReplacementSurgeryGaps
