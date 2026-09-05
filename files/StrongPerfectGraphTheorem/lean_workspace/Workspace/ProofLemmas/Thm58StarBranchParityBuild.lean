import Workspace.ProofLemmas.Thm58StarBranchParityTrack
import Workspace.ProofLemmas.Thm58StarBranchParityEnds
import Workspace.ProofLemmas.Thm58StarBranchGeometry
import Workspace.ProofLemmas.Thm58StarStarHoles
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# Assembling the two completions of 5.8 (2)

This file turns the two host tracks of `Thm58StarBranchParityTrack.exists_side_track` into the
two paths `S₁`, `S₂` of `L(H)` and builds the connecting path

`r₂-Q-s₁`,   `Q` running back along the rung and then through `F`,

of the paper's sentence *"Let `Q` be the path between `r₂` and `s₁` with interior in
`F ∪ V(R_{uv} \ {r₁})`"*.  The output is exactly the data of
`Thm58StarBranchParity.TwoTrackCompletion`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchParityBuild

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- Rungs of two tracks with no common edge are disjoint sets of vertices of `G`. -/
theorem image_disjoint {A B : Set (Sym2 (Fin n))} (hAB : ∀ g ∈ A, g ∉ B) :
    ∀ x ∈ edgeImage φ A, x ∉ edgeImage φ B := by
  rintro x ⟨e, he, heA, rfl⟩ ⟨f, hf, hfB, hxf⟩
  have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hxf))
  exact hAB e heA (hef ▸ hfB)

/-- The only vertex of the rung of a track that lies in the star of its first end is the first
vertex of the rung. -/
theorem rung_meet_star_first {N : Fin n → Set V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {tk : List (Fin n)} {a b : Fin n} (htk : IsTrackFrom H tk a b) (htk2 : 2 ≤ tk.length)
    {x : V} (hx : x ∈ edgeImage φ (trackEdges tk)) (hxa : x ∈ N a) :
    x = firstRungVertex φ tk htk.1 htk2 := by
  obtain ⟨g, hg, hgt, rfl⟩ := hx
  rw [hstar a] at hxa
  obtain ⟨g', hg', hg'c, hxg'⟩ := hxa
  have hgg' : g = g' := congrArg Subtype.val (φ.injective (Subtype.ext hxg'))
  have hcg : a ∈ g := hgg' ▸ hg'c.2
  have := edge_eq_firstTrackEdge htk htk2 hgt hcg
  exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext this)

/-- The only vertex of the rung of a track that lies in the star of its last end is the last
vertex of the rung. -/
theorem rung_meet_star_last {N : Fin n → Set V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {tk : List (Fin n)} {a b : Fin n} (htk : IsTrackFrom H tk a b) (htk2 : 2 ≤ tk.length)
    {x : V} (hx : x ∈ edgeImage φ (trackEdges tk)) (hxb : x ∈ N b) :
    x = lastRungVertex φ tk htk.1 htk2 := by
  obtain ⟨g, hg, hgt, rfl⟩ := hx
  rw [hstar b] at hxb
  obtain ⟨g', hg', hg'c, hxg'⟩ := hxb
  have hgg' : g = g' := congrArg Subtype.val (φ.injective (Subtype.ext hxg'))
  have hcg : b ∈ g := hgg' ▸ hg'c.2
  have := edge_eq_lastTrackEdge htk htk2 hgt hcg
  exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext this)

/-- The vertex of `G` attached to the first edge of a track is the image of that edge. -/
theorem firstRungVertex_eq {tk : List (Fin n)} (htk : IsTrackList H tk) (htk2 : 2 ≤ tk.length)
    {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) (hfe : firstTrackEdge tk htk2 = e) :
    firstRungVertex φ tk htk htk2 = (φ ⟨e, he⟩ : V) :=
  congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hfe)

theorem lastRungVertex_eq {tk : List (Fin n)} (htk : IsTrackList H tk) (htk2 : 2 ≤ tk.length)
    {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) (hfe : lastTrackEdge tk htk2 = e) :
    lastRungVertex φ tk htk htk2 = (φ ⟨e, he⟩ : V) :=
  congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hfe)


/-- **The data of the last two sentences of 5.8 (2).** -/
theorem exists_completion_data (h : Context G m J n H K φ N F P p₁ p₂ c q)
    (hcq : c ∈ q) (R : List V) (r t : V)
    (hR : IsPathFrom G R r t)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hinter : N c ∩ {x : V | x ∈ R} = {r})
    (s₁ s₂ : V) (hs₁ : s₁ ∈ N c \ {r}) (hs₂ : s₂ ∈ N c \ {r})
    (ha : G.Adj p₁ s₁) (hna : ¬ G.Adj p₁ s₂) :
    ∃ (S₁ S₂ Qm : List V) (y₀ y₁ : V),
      IsPathFrom G S₁ s₁ t ∧ IsPathFrom G S₂ s₂ t ∧ IsPathFrom G Qm y₀ y₁ ∧
      IsPathFrom G (Qm ++ [s₁]) y₀ s₁ ∧
      (∀ x ∈ S₁, x ∉ Qm) ∧ (∀ x ∈ S₂, x ∉ Qm ++ [s₁]) ∧
      (∀ x ∈ S₁, ∀ y ∈ Qm, (G.Adj x y ↔ (x = t ∧ y = y₀) ∨ (x = s₁ ∧ y = y₁))) ∧
      (∀ x ∈ S₂, ∀ y ∈ Qm ++ [s₁],
        (G.Adj x y ↔ (x = t ∧ y = y₀) ∨ (x = s₂ ∧ y = s₁))) ∧
      4 ≤ S₁.length + Qm.length ∧ 4 ≤ S₂.length + (Qm ++ [s₁]).length ∧
      S₁.length % 2 = S₂.length % 2 := by
  classical
  have hstar := star_eq h
  have hJ : IsKConnected J 3 := h.ready.2.1
  have hsub : IsSubdivision J H := h.ready.2.2.1.1
  have hFK : F ⊆ Kᶜ := h.ready.2.2.2.2.1
  have hPnotK : ∀ x ∈ P, x ∉ K := by
    intro x hx
    exact hFK (by rw [← vertices h]; exact hx)
  -- orient the branch so that it starts at the star vertex
  obtain ⟨b, Q, hQb, hQfrom, hQeq, hbB⟩ := Thm58StarBranchGeometry.orient_incident h hcq
  have hQ2 : 2 ≤ Q.length := by
    have he := firstTrackEdge_mem_trackEdges (branch_two_le_length h)
    rw [← hQeq] at he
    obtain ⟨i, hi, -⟩ := he
    omega
  -- the rung of the branch and its two ends
  obtain ⟨R', r', s', hR'path, hR'set, hNc', hNb'⟩ :=
    Thm58StarBranchGeometry.rung_intersections h hQfrom hQ2
  have hR'q : {x : V | x ∈ R'} = edgeImage φ (trackEdges q) := by rw [hR'set, hQeq]
  have hsame : ∀ x : V, x ∈ R ↔ x ∈ R' := by
    intro x
    constructor
    · intro hx; exact (Set.ext_iff.mp (hRset.trans hR'q.symm) x).mp hx
    · intro hx; exact (Set.ext_iff.mp (hR'q.trans hRset.symm) x).mp hx
  have hNcR : N c ∩ {x : V | x ∈ R'} = {r'} := hNc'
  have hrr' : r = r' := by
    have h1 : N c ∩ {x : V | x ∈ R} = N c ∩ {x : V | x ∈ R'} := by
      rw [hRset, hR'q]
    rw [hinter, hNcR] at h1
    exact Set.singleton_injective h1
  subst hrr'
  have hrNc : r ∈ N c := by
    have : r ∈ ({r} : Set V) := rfl
    rw [← hNcR] at this
    exact this.1
  -- the far end of the given path is the far end of the rung
  have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
  have hR'pos : 0 < R'.length := PathBasics.path_length_pos hR'path.1
  have hR0 : R[0]'hRpos = r := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRl : R[R.length - 1]'(by omega) = t := PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  have hR'0 : R'[0]'hR'pos = r := PathBasics.getElem_zero_of_head? hR'path.2.1 hR'pos
  have hR'l : R'[R'.length - 1]'(by omega) = s' :=
    PathBasics.getElem_last_of_getLast? hR'path.2.2 hR'pos
  have hrt : r ≠ t := by
    obtain ⟨x, hx, hpx⟩ := last_outside_star h
    have hxR : x ∈ R := by
      have : x ∈ {y : V | y ∈ R} := by rw [hRset]; exact hx.1
      exact this
    have hxr : x ≠ r := fun hh => hx.2 (hh ▸ hrNc)
    intro hcon
    -- `R` would then have `r` as both ends, so `R = [r]`
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxR
    have h1 : R.length = 1 := by
      by_contra hlen
      have : (0 : ℕ) = R.length - 1 := hR.1.2.1.getElem_inj_iff.mp (by rw [hR0, hRl, hcon])
      omega
    have hi0 : i = 0 := by omega
    subst hi0
    exact hxr (hix.symm.trans hR0)
  have hts' : t = s' := by
    have := Thm58StarBranchParityEnds.end_mem_ends hR.1 hR'path.1 hRpos hR'pos hsame
      (x := t) (Or.inr hRl.symm)
    rcases this with hh | hh
    · exact absurd (hh.trans hR'0).symm hrt
    · exact hh.trans hR'l
  subst hts'
  have hNbt : N b ∩ {x : V | x ∈ R'} = {t} := hNb'
  -- the branch has at least three vertices, since its rung has two distinct ends
  have hQ3 : 3 ≤ Q.length := by
    by_contra hcon
    have hQlen : Q.length = 2 := by omega
    have hrmem : r ∈ edgeImage φ (trackEdges Q) := by
      rw [← hR'set]
      have : r ∈ ({r} : Set V) := rfl
      rw [← hNcR] at this
      exact this.2
    have htmem : t ∈ edgeImage φ (trackEdges Q) := by
      rw [← hR'set]
      have : t ∈ ({t} : Set V) := rfl
      rw [← hNbt] at this
      exact this.2
    obtain ⟨g, hg, hgQ, hrg⟩ := hrmem
    obtain ⟨g', hg', hg'Q, htg⟩ := htmem
    obtain ⟨i, hi, hgi⟩ := hgQ
    obtain ⟨i', hi', hgi'⟩ := hg'Q
    have hi0 : i = 0 := by omega
    have hi'0 : i' = 0 := by omega
    subst hi0; subst hi'0
    apply hrt
    rw [hrg, htg]
    exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext (hgi.trans hgi'.symm))
  -- the two edges of `H` at the star vertex carrying `s₁` and `s₂`
  have hs₁star : s₁ ∈ edgeImage φ (incidentEdges H c) := by rw [← hstar c]; exact hs₁.1
  have hs₂star : s₂ ∈ edgeImage φ (incidentEdges H c) := by rw [← hstar c]; exact hs₂.1
  obtain ⟨e₁, he₁, hce₁, hs₁eq⟩ := hs₁star
  obtain ⟨e₂, he₂, hce₂, hs₂eq⟩ := hs₂star
  have hs₁s₂ : s₁ ≠ s₂ := by rintro rfl; exact hna ha
  have he₁₂ : e₁ ≠ e₂ := by
    rintro rfl
    exact hs₁s₂ (hs₁eq.trans hs₂eq.symm)
  have hoverlap : N c ∩ edgeImage φ (trackEdges q) ⊆ {r} := by
    rw [← hR'q, hNcR]
  have hnotrung : ∀ x : V, x ∈ N c → x ≠ r → x ∉ edgeImage φ (trackEdges q) := by
    intro x hxc hxr hxR
    exact hxr (hoverlap ⟨hxc, hxR⟩)
  have he₁Q : e₁ ∉ trackEdges Q := by
    intro hcon
    exact hnotrung s₁ hs₁.1 hs₁.2 ⟨e₁, he₁, hQeq ▸ hcon, hs₁eq⟩
  have he₂Q : e₂ ∉ trackEdges Q := by
    intro hcon
    exact hnotrung s₂ hs₂.1 hs₂.2 ⟨e₂, he₂, hQeq ▸ hcon, hs₂eq⟩
  -- the two tracks of `H` from the star vertex to the other end of the branch
  obtain ⟨tk₁, htk₁2, htk₁, hfe₁, htk₁Q, htk₁f⟩ :=
    Thm58StarBranchParityTrack.exists_side_track hJ hsub hQb hQfrom hQ2 h.star hbB
      he₁ he₂ hce₁.2 hce₂.2 he₁₂ he₁Q he₂Q
  obtain ⟨tk₂, htk₂2, htk₂, hfe₂, htk₂Q, htk₂f⟩ :=
    Thm58StarBranchParityTrack.exists_side_track hJ hsub hQb hQfrom hQ2 h.star hbB
      he₂ he₁ hce₂.2 hce₁.2 (Ne.symm he₁₂) he₂Q he₁Q
  -- `s₁` is not in the star at the far end of the branch
  have hbe₁ : b ∉ e₁ :=
    Thm58StarBranchParityTrack.end_not_mem_edge hJ hsub hQb hQfrom hQ2 h.star hbB
      he₁ hce₁.2 he₁Q
  have hs₁Nb : s₁ ∉ N b := by
    rw [hstar b]
    rintro ⟨g, hg, hgb, hgs⟩
    have hgg : e₁ = g := congrArg Subtype.val (φ.injective (Subtype.ext (hs₁eq.symm.trans hgs)))
    exact hbe₁ (hgg ▸ hgb.2)
  -- the general dictionary: an edge off the rung meets it only in `r` or in `t`
  have hcross_rung : ∀ x : V, x ∈ K → x ∉ edgeImage φ (trackEdges q) →
      ∀ y : V, y ∈ edgeImage φ (trackEdges q) → G.Adj x y →
      (x ∈ N c ∧ y = r) ∨ (x ∈ N b ∧ y = t) := by
    intro x hxK hxR y hy hadj
    have hy' : y ∈ edgeImage φ (trackEdges Q) := by rw [hQeq]; exact hy
    have hxR' : x ∉ edgeImage φ (trackEdges Q) := by rw [hQeq]; exact hxR
    have hyR' : y ∈ {z : V | z ∈ R'} := by rw [hR'q]; exact hy
    rcases Thm58StarStarHoles.adj_rung_imp hstar hQb hQfrom hxK hxR' hy' hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, ?_⟩
      have hmem : y ∈ N c ∩ {z : V | z ∈ R'} := ⟨h2, hyR'⟩
      rw [hNcR] at hmem
      exact hmem
    · refine Or.inr ⟨h1, ?_⟩
      have hmem : y ∈ N b ∩ {z : V | z ∈ R'} := ⟨h2, hyR'⟩
      rw [hNbt] at hmem
      exact hmem
  have hs₁K : s₁ ∈ K := star_subset h c hs₁.1
  have hs₂K : s₂ ∈ K := star_subset h c hs₂.1
  have hs₁R : s₁ ∉ edgeImage φ (trackEdges q) := hnotrung s₁ hs₁.1 hs₁.2
  have hs₂R : s₂ ∉ edgeImage φ (trackEdges q) := hnotrung s₂ hs₂.1 hs₂.2
  have hs₁noR : ∀ y ∈ edgeImage φ (trackEdges q), y ≠ r → ¬ G.Adj s₁ y := by
    intro y hy hyr hadj
    rcases hcross_rung s₁ hs₁K hs₁R y hy hadj with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hyr h2
    · exact hs₁Nb h1
  -- the rungs of the two tracks
  have hA₁first : firstRungVertex φ tk₁ htk₁.1 htk₁2 = s₁ := by
    rw [firstRungVertex_eq htk₁.1 htk₁2 he₁ hfe₁]; exact hs₁eq.symm
  have hA₂first : firstRungVertex φ tk₂ htk₂.1 htk₂2 = s₂ := by
    rw [firstRungVertex_eq htk₂.1 htk₂2 he₂ hfe₂]; exact hs₂eq.symm
  have hA₁path : IsPathFrom G (trackRung φ tk₁ htk₁.1) s₁ (lastRungVertex φ tk₁ htk₁.1 htk₁2) := by
    have hp := trackRung_isPathFrom_ends φ htk₁ htk₁2
    rwa [hA₁first] at hp
  have hA₂path : IsPathFrom G (trackRung φ tk₂ htk₂.1) s₂ (lastRungVertex φ tk₂ htk₂.1 htk₂2) := by
    have hp := trackRung_isPathFrom_ends φ htk₂ htk₂2
    rwa [hA₂first] at hp
  have hA₁mem : ∀ x : V, x ∈ trackRung φ tk₁ htk₁.1 ↔ x ∈ edgeImage φ (trackEdges tk₁) :=
    fun x => mem_trackRung_iff φ htk₁.1
  have hA₂mem : ∀ x : V, x ∈ trackRung φ tk₂ htk₂.1 ↔ x ∈ edgeImage φ (trackEdges tk₂) :=
    fun x => mem_trackRung_iff φ htk₂.1
  have hA₁K : ∀ x ∈ trackRung φ tk₁ htk₁.1, x ∈ K := trackRung_subset_K φ tk₁ htk₁.1
  have hA₂K : ∀ x ∈ trackRung φ tk₂ htk₂.1, x ∈ K := trackRung_subset_K φ tk₂ htk₂.1
  have hA₁disj : ∀ x ∈ trackRung φ tk₁ htk₁.1, x ∉ edgeImage φ (trackEdges q) := by
    intro x hx hcon
    exact image_disjoint htk₁Q x ((hA₁mem x).mp hx) (by rw [hQeq]; exact hcon)
  have hA₂disj : ∀ x ∈ trackRung φ tk₂ htk₂.1, x ∉ edgeImage φ (trackEdges q) := by
    intro x hx hcon
    exact image_disjoint htk₂Q x ((hA₂mem x).mp hx) (by rw [hQeq]; exact hcon)
  have hA₁star : ∀ x ∈ trackRung φ tk₁ htk₁.1, x ∈ N c → x = s₁ := by
    intro x hx hxc
    rw [← hA₁first]
    exact rung_meet_star_first hstar htk₁ htk₁2 ((hA₁mem x).mp hx) hxc
  have hA₂star : ∀ x ∈ trackRung φ tk₂ htk₂.1, x ∈ N c → x = s₂ := by
    intro x hx hxc
    rw [← hA₂first]
    exact rung_meet_star_first hstar htk₂ htk₂2 ((hA₂mem x).mp hx) hxc
  -- the last vertex of each rung is the unique neighbour of `t` on it
  have htNb : t ∈ N b := by
    have : t ∈ ({t} : Set V) := rfl
    rw [← hNbt] at this
    exact this.1
  have htR : t ∈ edgeImage φ (trackEdges q) := by
    rw [← hR'q]
    have : t ∈ ({t} : Set V) := rfl
    rw [← hNbt] at this
    exact this.2
  have hlastNb : ∀ (tk : List (Fin n)) (htk : IsTrackFrom H tk c b) (htk2 : 2 ≤ tk.length),
      lastRungVertex φ tk htk.1 htk2 ∈ N b := by
    intro tk htk htk2
    rw [hstar b]
    exact ⟨lastTrackEdge tk htk2, lastTrackEdge_mem htk.1 htk2,
      ⟨lastTrackEdge_mem htk.1 htk2, lastTrackEdge_contains htk htk2⟩, rfl⟩
  have hlastmem : ∀ (tk : List (Fin n)) (htk : IsTrackFrom H tk c b) (htk2 : 2 ≤ tk.length),
      lastRungVertex φ tk htk.1 htk2 ∈ trackRung φ tk htk.1 :=
    fun tk htk htk2 => lastRungVertex_mem φ htk.1 htk2
  have hf₁adj : G.Adj (lastRungVertex φ tk₁ htk₁.1 htk₁2) t := by
    refine Thm58StarStarHoles.star_adj hstar b (hlastNb tk₁ htk₁ htk₁2) htNb ?_
    intro hcon
    exact hA₁disj _ (hlastmem tk₁ htk₁ htk₁2) (hcon ▸ htR)
  have hf₂adj : G.Adj (lastRungVertex φ tk₂ htk₂.1 htk₂2) t := by
    refine Thm58StarStarHoles.star_adj hstar b (hlastNb tk₂ htk₂ htk₂2) htNb ?_
    intro hcon
    exact hA₂disj _ (hlastmem tk₂ htk₂ htk₂2) (hcon ▸ htR)
  have hA₁t : ∀ x ∈ trackRung φ tk₁ htk₁.1, G.Adj x t → x = lastRungVertex φ tk₁ htk₁.1 htk₁2 := by
    intro x hx hadj
    rcases hcross_rung x (hA₁K x hx) (hA₁disj x hx) t htR hadj with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2.symm hrt
    · exact rung_meet_star_last hstar htk₁ htk₁2 ((hA₁mem x).mp hx) h1
  have hA₂t : ∀ x ∈ trackRung φ tk₂ htk₂.1, G.Adj x t → x = lastRungVertex φ tk₂ htk₂.1 htk₂2 := by
    intro x hx hadj
    rcases hcross_rung x (hA₂K x hx) (hA₂disj x hx) t htR hadj with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2.symm hrt
    · exact rung_meet_star_last hstar htk₂ htk₂2 ((hA₂mem x).mp hx) h1
  -- the two paths `S₁`, `S₂` of `L(H)`
  have hsingt : IsPathFrom G [t] t t := ⟨PathBasics.isPathList_singleton G t, rfl, rfl⟩
  have hS₁path : IsPathFrom G (trackRung φ tk₁ htk₁.1 ++ [t]) s₁ t := by
    refine PathGlue.glue_path hA₁path hsingt ?_ ?_
    · intro x hx hmem
      exact hA₁disj x hx ((List.eq_of_mem_singleton hmem) ▸ htR)
    · intro x hx y hy
      have hyt : y = t := List.eq_of_mem_singleton hy
      subst hyt
      exact ⟨fun hadj => ⟨hA₁t x hx hadj, rfl⟩, fun hh => hh.1 ▸ hf₁adj⟩
  have hS₂path : IsPathFrom G (trackRung φ tk₂ htk₂.1 ++ [t]) s₂ t := by
    refine PathGlue.glue_path hA₂path hsingt ?_ ?_
    · intro x hx hmem
      exact hA₂disj x hx ((List.eq_of_mem_singleton hmem) ▸ htR)
    · intro x hx y hy
      have hyt : y = t := List.eq_of_mem_singleton hy
      subst hyt
      exact ⟨fun hadj => ⟨hA₂t x hx hadj, rfl⟩, fun hh => hh.1 ▸ hf₂adj⟩
  -- the segment of the rung between the last attachment of `p₂` and the far end
  have hM2 : 2 ≤ R'.length := by
    by_contra hcon
    apply hrt
    rw [← hR'0, ← hR'l]
    exact SubdivisionCounting.getElem_eq_of_index_eq R' (by omega) (by omega) (by omega)
  have hM1 : R'.length - 1 < R'.length := by omega
  obtain ⟨w, hw, hpw⟩ := last_outside_star h
  have hwR' : w ∈ R' := by
    have hmem : w ∈ {z : V | z ∈ R'} := by rw [hR'q]; exact hw.1
    exact hmem
  obtain ⟨j₀, hj₀, hj₀w⟩ := List.getElem_of_mem hwR'
  have hj₀pos : 1 ≤ j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with hz | hpos
    · exfalso
      subst hz
      exact hw.2 (hj₀w ▸ hR'0 ▸ hrNc)
    · exact hpos
  obtain ⟨k, hkdef⟩ : ∃ z : ℕ,
      z = Nat.findGreatest (fun j => ∃ hj : j < R'.length, G.Adj p₂ (R'[j]'hj))
        (R'.length - 1) := ⟨_, rfl⟩
  have hPj₀ : ∃ hj : j₀ < R'.length, G.Adj p₂ (R'[j₀]'hj) := ⟨hj₀, by rw [hj₀w]; exact hpw⟩
  have hkle : k ≤ R'.length - 1 := by rw [hkdef]; exact Nat.findGreatest_le _
  have hkge : j₀ ≤ k := by rw [hkdef]; exact Nat.le_findGreatest (by omega) hPj₀
  have hkM : k < R'.length := by omega
  have hadjk : G.Adj p₂ (R'[k]'hkM) := by
    have hspec : ∃ hj : k < R'.length, G.Adj p₂ (R'[k]'hj) := by
      rw [hkdef]
      exact Nat.findGreatest_spec (P := fun i => ∃ hi : i < R'.length, G.Adj p₂ (R'[i]'hi))
        (m := j₀) (by omega) hPj₀
    obtain ⟨hjk', hh⟩ := hspec
    exact hh
  have hkmax : ∀ (j : ℕ) (hj : j < R'.length), k < j → ¬ G.Adj p₂ (R'[j]'hj) := by
    intro j hj hkj hadj
    exact Nat.findGreatest_is_greatest (P := fun i => ∃ hi : i < R'.length, G.Adj p₂ (R'[i]'hi))
      (by rw [← hkdef]; exact hkj) (by omega) ⟨hj, hadj⟩
  obtain ⟨Bfull, hBdef⟩ : ∃ z : List V, z = (R'.drop k).take (R'.length - 1 - k + 1) := ⟨_, rfl⟩
  have hBpath : IsPathFrom G Bfull (R'[k]'hkM) t := by
    rw [hBdef, ← hR'l]
    exact Thm58StarBranchParityEnds.isPathFrom_slice' hR'path.1 hkle hM1
  have hBlen : 1 ≤ Bfull.length := by
    rw [hBdef, PathBasics.length_slice R' hkle hM1]
    omega
  have hBmem : ∀ x : V, x ∈ Bfull ↔
      ∃ (j : ℕ) (hj : j < R'.length), k ≤ j ∧ j ≤ R'.length - 1 ∧ R'[j]'hj = x := by
    intro x
    rw [hBdef]
    exact PathBasics.mem_slice_iff R' hkle hM1
  have hBrung : ∀ x ∈ Bfull, x ∈ edgeImage φ (trackEdges q) := by
    intro x hx
    obtain ⟨j, hj, -, -, hjx⟩ := (hBmem x).mp hx
    have hmem : x ∈ {z : V | z ∈ R'} := hjx ▸ List.getElem_mem hj
    rw [hR'q] at hmem
    exact hmem
  have hBne_r : ∀ x ∈ Bfull, x ≠ r := by
    intro x hx hcon
    obtain ⟨j, hj, hjk, -, hjx⟩ := (hBmem x).mp hx
    have : j = 0 := hR'path.1.2.1.getElem_inj_iff.mp (by rw [hjx, hcon, hR'0])
    omega
  have hrR : r ∈ edgeImage φ (trackEdges q) := by
    rw [← hR'q]
    have hmem : r ∈ ({r} : Set V) := rfl
    rw [← hNcR] at hmem
    exact hmem.2
  have hts₁ : t ≠ s₁ := fun hh => hs₁R (hh ▸ htR)
  have hts₂ : t ≠ s₂ := fun hh => hs₂R (hh ▸ htR)
  -- the path `r₂-Q-s₁` of the paper
  obtain ⟨Ct, hCtdef⟩ : ∃ z : List V, z = Bfull.reverse ++ P.reverse := ⟨_, rfl⟩
  have hBrev : IsPathFrom G Bfull.reverse t (R'[k]'hkM) := PathBasics.isPathFrom_reverse hBpath
  have hPrev : IsPathFrom G P.reverse p₂ p₁ := PathBasics.isPathFrom_reverse (path h)
  have hPlen : 2 ≤ P.length := two_le_length h
  have hCtmem : ∀ x : V, x ∈ Ct → x ∈ Bfull ∨ x ∈ P := by
    intro x hx
    rw [hCtdef, List.mem_append, List.mem_reverse, List.mem_reverse] at hx
    exact hx
  have hCtpath : IsPathFrom G Ct t p₁ := by
    rw [hCtdef]
    refine PathGlue.glue_path hBrev hPrev ?_ ?_
    · intro x hx hmem
      rw [List.mem_reverse] at hx hmem
      exact hPnotK x hmem (image_subset (hBrung x hx))
    · intro x hx y hy
      rw [List.mem_reverse] at hx hy
      have hxR := hBrung x hx
      have hxK : x ∈ K := image_subset hxR
      have hxr : x ≠ r := hBne_r x hx
      constructor
      · intro hadj
        rcases edges_except_overlap h hoverlap y hy x hxK hxr hadj.symm with
          ⟨hy1, hx1⟩ | ⟨hy2, hx2⟩
        · exact absurd (hoverlap ⟨hx1.1, hxR⟩) hxr
        · refine ⟨?_, hy2⟩
          obtain ⟨j, hj, hjk, hjM, hjx⟩ := (hBmem x).mp hx
          have hnk : ¬ k < j := fun hlt =>
            hkmax j hj hlt (by rw [hjx, ← hy2]; exact hadj.symm)
          have hjeq : j = k := by omega
          rw [← hjx]
          exact SubdivisionCounting.getElem_eq_of_index_eq R' hjeq hj hkM
      · rintro ⟨hxk, hyp⟩
        rw [hxk, hyp]
        exact hadjk.symm
  have hCtlen : 3 ≤ Ct.length := by
    rw [hCtdef]
    simp only [List.length_append, List.length_reverse]
    omega
  have hCthead : Ct.head? = some t := hCtpath.2.1
  obtain ⟨lt, hCtl⟩ : ∃ l : List V, Ct = t :: l := by
    cases hc : Ct with
    | nil => rw [hc] at hCthead; simp at hCthead
    | cons a l' =>
      rw [hc] at hCthead
      simp only [List.head?_cons, Option.some.injEq] at hCthead
      exact ⟨l', by rw [hCthead]⟩
  have htnotin : t ∉ Ct.tail := by
    have hnd := hCtpath.1.2.1
    rw [hCtl] at hnd ⊢
    exact (List.nodup_cons.mp hnd).1
  have hCttail : ∀ x ∈ Ct.tail, x ∈ Ct ∧ x ≠ t := by
    intro x hx
    exact ⟨List.mem_of_mem_tail hx, fun hcon => htnotin (hcon ▸ hx)⟩
  have hCt0 : Ct[0]'(by omega) = t := PathBasics.getElem_zero_of_head? hCtpath.2.1 (by omega)
  obtain ⟨y₀, hy₀def⟩ : ∃ z : V, z = Ct[1]'(by omega) := ⟨_, rfl⟩
  have hy₀mem : y₀ ∈ Ct := by rw [hy₀def]; exact List.getElem_mem _
  have hy0adj : ∀ y ∈ Ct.tail, (G.Adj t y ↔ y = y₀) := by
    intro y hy
    obtain ⟨hyCt, hyt⟩ := hCttail y hy
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hyCt
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hyt (hiy.symm.trans hCt0)
    constructor
    · intro hadj
      rw [← hCt0, ← hiy] at hadj
      have hidx := (PathBasics.path_adj_iff hCtpath.1 (by omega) hi).mp hadj
      have hi1 : i = 1 := by omega
      subst hi1
      rw [hy₀def]
      exact hiy.symm
    · intro hyy
      rw [hyy, hy₀def, ← hCt0]
      exact (PathBasics.path_adj_iff hCtpath.1 (by omega) (show 1 < Ct.length by omega)).mpr
        (by omega)
  have hQmpath : IsPathFrom G Ct.tail y₀ p₁ := by
    rw [hy₀def]
    exact Thm58StarBranchParityEnds.isPathFrom_tail hCtpath (by omega)
  -- the longer completion `r₂-Q-s₁-s₂`
  have hsings : IsPathFrom G [s₁] s₁ s₁ := ⟨PathBasics.isPathList_singleton G s₁, rfl, rfl⟩
  have hs₁notCt : s₁ ∉ Ct := by
    intro hx
    rcases hCtmem s₁ hx with hb | hp
    · exact hs₁R (hBrung s₁ hb)
    · exact hPnotK s₁ hp hs₁K
  have hs₁ney₀ : s₁ ≠ y₀ := fun hh => hs₁notCt (hh ▸ hy₀mem)
  have hCt2path : IsPathFrom G (Ct ++ [s₁]) t s₁ := by
    refine PathGlue.glue_path hCtpath hsings ?_ ?_
    · intro x hx hmem
      exact hs₁notCt ((List.eq_of_mem_singleton hmem) ▸ hx)
    · intro x hx y hy
      have hyeq : y = s₁ := List.eq_of_mem_singleton hy
      subst hyeq
      constructor
      · intro hadj
        rcases hCtmem x hx with hb | hp
        · exact absurd hadj.symm (hs₁noR x (hBrung x hb) (hBne_r x hb))
        · rcases edges_except_overlap h hoverlap x hp y hs₁K hs₁.2 hadj with
            ⟨h1, -⟩ | ⟨h1, h2⟩
          · exact ⟨h1, rfl⟩
          · exact absurd h2.1 hs₁R
      · rintro ⟨hxp, -⟩
        rw [hxp]
        exact ha
  have hCt2len : (Ct ++ [s₁]).length = Ct.length + 1 := by simp
  have htailapp : (Ct ++ [s₁]).tail = Ct.tail ++ [s₁] := by rw [hCtl]; rfl
  have hlongpath : IsPathFrom G (Ct.tail ++ [s₁]) y₀ s₁ := by
    rw [← htailapp]
    have hh := Thm58StarBranchParityEnds.isPathFrom_tail hCt2path
      (show 2 ≤ (Ct ++ [s₁]).length by omega)
    have hidx : (Ct ++ [s₁])[1]'(by omega) = y₀ := by
      rw [hy₀def]
      exact List.getElem_append_left (by omega)
    rwa [hidx] at hh
  have hs₂s₁adj : G.Adj s₂ s₁ :=
    Thm58StarStarHoles.star_adj hstar c hs₂.1 hs₁.1 (Ne.symm hs₁s₂)
  refine ⟨trackRung φ tk₁ htk₁.1 ++ [t], trackRung φ tk₂ htk₂.1 ++ [t], Ct.tail, y₀, p₁,
    hS₁path, hS₂path, hQmpath, hlongpath, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `S₁` misses the middle path
    intro x hx hmem
    obtain ⟨hxCt, hxt⟩ := hCttail x hmem
    rcases List.mem_append.mp hx with hxA | hxtt
    · rcases hCtmem x hxCt with hb | hp
      · exact hA₁disj x hxA (hBrung x hb)
      · exact hPnotK x hp (hA₁K x hxA)
    · exact hxt (List.eq_of_mem_singleton hxtt)
  · -- `S₂` misses the longer middle path
    intro x hx hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨hxCt, hxt⟩ := hCttail x hm
      rcases List.mem_append.mp hx with hxA | hxtt
      · rcases hCtmem x hxCt with hb | hp
        · exact hA₂disj x hxA (hBrung x hb)
        · exact hPnotK x hp (hA₂K x hxA)
      · exact hxt (List.eq_of_mem_singleton hxtt)
    · have hxs : x = s₁ := List.eq_of_mem_singleton hm
      rcases List.mem_append.mp hx with hxA | hxtt
      · exact hs₁s₂ (hxs.symm.trans (hA₂star x hxA (hxs ▸ hs₁.1)))
      · exact hts₁ ((List.eq_of_mem_singleton hxtt).symm.trans hxs)
  · -- the edges between `S₁` and the middle path
    intro x hx y hy
    obtain ⟨hyCt, hyt⟩ := hCttail y hy
    rcases List.mem_append.mp hx with hxA | hxtt
    · have hxK := hA₁K x hxA
      have hxR := hA₁disj x hxA
      have hxnet : x ≠ t := fun hh => hxR (hh ▸ htR)
      have hxner : x ≠ r := fun hh => hxR (hh ▸ hrR)
      constructor
      · intro hadj
        rcases hCtmem y hyCt with hb | hp
        · exfalso
          rcases hcross_rung x hxK hxR y (hBrung y hb) hadj with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact hBne_r y hb h2
          · exact hyt h2
        · rcases edges_except_overlap h hoverlap y hp x hxK hxner hadj.symm with
            ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨hA₁star x hxA h2.1, h1⟩
          · exact absurd h2.1 hxR
      · rintro (⟨hh, -⟩ | ⟨hh, hyy⟩)
        · exact absurd hh hxnet
        · rw [hh, hyy]; exact ha.symm
    · have hxt : x = t := List.eq_of_mem_singleton hxtt
      subst hxt
      constructor
      · intro hadj
        exact Or.inl ⟨rfl, (hy0adj y hy).mp hadj⟩
      · rintro (⟨-, hyy⟩ | ⟨hh, -⟩)
        · exact (hy0adj y hy).mpr hyy
        · exact absurd hh hts₁
  · -- the edges between `S₂` and the longer middle path
    intro x hx y hy
    rcases List.mem_append.mp hy with hyt' | hys
    · obtain ⟨hyCt, hyt⟩ := hCttail y hyt'
      have hynes₁ : y ≠ s₁ := fun hh => hs₁notCt (hh ▸ hyCt)
      rcases List.mem_append.mp hx with hxA | hxtt
      · have hxK := hA₂K x hxA
        have hxR := hA₂disj x hxA
        have hxnet : x ≠ t := fun hh => hxR (hh ▸ htR)
        have hxner : x ≠ r := fun hh => hxR (hh ▸ hrR)
        constructor
        · intro hadj
          exfalso
          rcases hCtmem y hyCt with hb | hp
          · rcases hcross_rung x hxK hxR y (hBrung y hb) hadj with ⟨-, h2⟩ | ⟨-, h2⟩
            · exact hBne_r y hb h2
            · exact hyt h2
          · rcases edges_except_overlap h hoverlap y hp x hxK hxner hadj.symm with
              ⟨h1, h2⟩ | ⟨h1, h2⟩
            · apply hna
              rw [← hA₂star x hxA h2.1, ← h1]
              exact hadj.symm
            · exact hxR h2.1
        · rintro (⟨hh, -⟩ | ⟨-, hh⟩)
          · exact absurd hh hxnet
          · exact absurd hh hynes₁
      · have hxt : x = t := List.eq_of_mem_singleton hxtt
        subst hxt
        constructor
        · intro hadj
          exact Or.inl ⟨rfl, (hy0adj y hyt').mp hadj⟩
        · rintro (⟨-, hyy⟩ | ⟨hh, -⟩)
          · exact (hy0adj y hyt').mpr hyy
          · exact absurd hh hts₂
    · have hys₁ : y = s₁ := List.eq_of_mem_singleton hys
      subst hys₁
      rcases List.mem_append.mp hx with hxA | hxtt
      · constructor
        · intro hadj
          refine Or.inr ⟨?_, rfl⟩
          obtain ⟨g, hg, hgt, hxg⟩ := (hA₂mem x).mp hxA
          have hadj' : G.Adj (↑(φ ⟨g, hg⟩) : V) (↑(φ ⟨e₁, he₁⟩) : V) := by
            rw [← hxg, ← hs₁eq]; exact hadj
          obtain ⟨-, z, hzg, hze⟩ :=
            SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj')
          have hge₂ : g = e₂ := by
            by_contra hcon
            exact htk₂f g hgt hcon z hzg hze
          refine hxg.trans (?_ : (↑(φ ⟨g, hg⟩) : V) = s₂)
          rw [hs₂eq]
          exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hge₂)
        · rintro (⟨-, hyy⟩ | ⟨hh, -⟩)
          · exact absurd hyy hs₁ney₀
          · rw [hh]; exact hs₂s₁adj
      · have hxt : x = t := List.eq_of_mem_singleton hxtt
        subst hxt
        constructor
        · intro hadj
          exact absurd hadj.symm (hs₁noR _ htR (Ne.symm hrt))
        · rintro (⟨-, hyy⟩ | ⟨hh, -⟩)
          · exact absurd hyy hs₁ney₀
          · exact absurd hh hts₂
  · -- lengths
    have h1 : (trackRung φ tk₁ htk₁.1 ++ [t]).length = trackLength tk₁ + 1 := by
      simp [trackRung_length]
    have h2 : Ct.tail.length = Ct.length - 1 := by simp
    simp only [trackLength] at h1
    omega
  · have h1 : (trackRung φ tk₂ htk₂.1 ++ [t]).length = trackLength tk₂ + 1 := by
      simp [trackRung_length]
    have h2 : (Ct.tail ++ [s₁]).length = Ct.length - 1 + 1 := by simp
    simp only [trackLength] at h1
    omega
  · -- parity: `H` is bipartite and both tracks join the two ends of the branch
    obtain ⟨col⟩ :=
      BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite h.ready.2.2.1.2
    have hpar : Even (trackLength tk₁) ↔ Even (trackLength tk₂) :=
      (BipartiteClosedWalkEven.even_trackLength_iff col htk₁).trans
        (BipartiteClosedWalkEven.even_trackLength_iff col htk₂).symm
    have h1 : (trackRung φ tk₁ htk₁.1 ++ [t]).length = trackLength tk₁ + 1 := by
      simp [trackRung_length]
    have h2 : (trackRung φ tk₂ htk₂.1 ++ [t]).length = trackLength tk₂ + 1 := by
      simp [trackRung_length]
    rw [Nat.even_iff, Nat.even_iff] at hpar
    simp only [trackLength] at hpar h1 h2
    omega







end Workspace.ProofLemmas.Thm58StarBranchParityBuild
