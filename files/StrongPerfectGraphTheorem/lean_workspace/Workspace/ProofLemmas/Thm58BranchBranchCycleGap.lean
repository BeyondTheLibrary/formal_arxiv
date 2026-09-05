import Workspace.ProofLemmas.Thm58BranchBranchStars
import Workspace.ProofLemmas.Thm58BranchBranchCut
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.Thm58BranchBranchCycleRung
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.Thm58BranchBranchCycleHost

/-!
# The cycle of 5.8 (7) and the three paths it carries

PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the branch
between `u₁` and `v₁`, and using `u₂` and not `v₂` (since `J \ v₂` is
2-connected).  There correspond two paths in `L(H)`, say `P` and `Q`, from
`N_{u₁}` and `N_{v₁}` respectively to `N_{u₂}`, disjoint from each other, and
there is a third path `R` say from `p₁` to `N_{u₂}` via `F` and a subpath of
`R_{u₂v₂}`.  There are no edges between these paths except within the triangle
`T` formed by their ends in `N_{u₂}`."*

The cycle of `H` becomes a hole `Z` of `G` (the edges of a cycle are an induced
cycle of the line graph).  `P` and `Q` are the two arcs of `Z` obtained by
deleting one vertex of the first rung and cutting between the two vertices of
`Z` that lie in `N_{u₂}`; `Thm58BranchBranchCut.link_of_hole_cut` performs that
cut.  `Config` below records the data of the two quoted sentences, with `α`, `β`
the two vertices of `Z` in `N_{u₂}` and `t` the third vertex of the triangle.

The hole itself is available to whoever proves the two gaps below:
`Thm58BranchBranchCycleRung.isHoleList_cycleRung` turns any cycle of `H` into a
hole of `G`, with position `i` of the hole carrying edge `i` of the cycle, so
only the choice of the cycle and of its starting point is left to make.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranchCycle

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm58BranchBranch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- The data of the cycle of 5.8 (7): the hole `Z` of `G` carried by the cycle of
`H`, the two vertices `α`, `β` of `Z` in the star of the branch-vertex `u`
(consecutive on `Z`, at positions `j` and `j + 1`), the third path `R` of the
link with its end `t` in the same star, and the fact that the only edges between
`R` and the cycle are the two triangle edges at `t`. -/
structure Config (G : SimpleGraph V) (H : SimpleGraph (Fin n)) (K : Set V)
    (N : Fin n → Set V) (p₁ : V) (Z R : List V) (j : ℕ) (α β t : V) (u : Fin n) :
    Prop where
  /-- The cycle of `H` is a hole of `G`. -/
  hole : IsHoleList G Z
  /-- The hole lies in the appearance. -/
  subK : ∀ z ∈ Z, z ∈ K
  /-- The two vertices in `N u` are not the deleted first vertex of `Z`. -/
  jpos : 1 ≤ j
  /-- Both positions are inside the hole. -/
  jlt : j + 1 < Z.length
  /-- The first vertex of the cut edge. -/
  alphaZ : Z[j]? = some α
  /-- The second vertex of the cut edge. -/
  betaZ : Z[j + 1]? = some β
  /-- The cycle passes through the branch-vertex `u`. -/
  ubranch : u ∈ branchVertices H
  /-- `α` is one of the two edges of the cycle at `u`. -/
  alphaN : α ∈ N u
  /-- `β` is the other edge of the cycle at `u`. -/
  betaN : β ∈ N u
  /-- The third triangle vertex is the edge at `u` of the second branch. -/
  tN : t ∈ N u
  /-- The third path of the link. -/
  rpath : IsPathList G R
  /-- It starts at the third triangle vertex. -/
  rhead : R.head? = some t
  /-- It is disjoint from the cycle. -/
  rdisj : ∀ z ∈ R, z ∉ Z
  /-- Its only edges to the cycle are the two triangle edges. -/
  rcross : ∀ z ∈ R, ∀ zz ∈ Z, (G.Adj z zz ↔ (z = t ∧ (zz = α ∨ zz = β)))
  /-- The third path stops just before the first end of the outside path. -/
  pnot : p₁ ∉ R
  /-- The first end of the outside path sees exactly the last vertex of `R`. -/
  plast : ∃ z, R.getLast? = some z ∧ ∀ z' ∈ R, (G.Adj p₁ z' ↔ z' = z)

/-- Two distinct edges of `H` at a common vertex `u`, both on the same branch,
put `u` inside that branch, where no branch-vertex lies. -/
theorem no_two_star_edges_on_branch {q : List (Fin n)} (hq : IsBranch H q)
    {u : Fin n} (hu : u ∈ branchVertices H)
    {e f : Sym2 (Fin n)} (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q)
    (hef : e ≠ f) (hue : u ∈ e) (huf : u ∈ f) : False :=
  hq.2.1 u (Thm58BranchBranch.internal_of_two_edges hq.1.2.1 he hf hef hue huf) hu

/-- A vertex of the appearance whose edge misses `u` has at most one neighbour in
the star of `u`: two would give a triangle of `H`, which is bipartite. -/
theorem no_two_star_neighbors (hbip : H.IsBipartite)
    (hN : ∀ c : Fin n, N c =
      {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    {u : Fin n} {x y : V} (hx : x ∈ N u) (hy : y ∈ N u) (hxy : x ≠ y)
    {g : Sym2 (Fin n)} (hg : g ∈ H.edgeSet) (hu : u ∉ g)
    (hwx : G.Adj (↑(φ ⟨g, hg⟩) : V) x) (hwy : G.Adj (↑(φ ⟨g, hg⟩) : V) y) : False := by
  rw [hN u] at hx hy
  obtain ⟨e, he, ⟨-, hue⟩, rfl⟩ := hx
  obtain ⟨f, hf, ⟨-, huf⟩, rfl⟩ := hy
  have hef : e ≠ f := by
    intro hh
    exact hxy (congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hh))
  obtain ⟨-, a, hag, hae⟩ :=
    SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hwx)
  obtain ⟨-, b, hbg, hbf⟩ :=
    SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hwy)
  have hua : u ≠ a := fun hh => hu (hh ▸ hag)
  have hub : u ≠ b := fun hh => hu (hh ▸ hbg)
  have heua : e = s(u, a) := (Sym2.mem_and_mem_iff hua).mp ⟨hue, hae⟩
  have hfub : f = s(u, b) := (Sym2.mem_and_mem_iff hub).mp ⟨huf, hbf⟩
  have hab : a ≠ b := by
    intro hh
    exact hef (by rw [heua, hfub, hh])
  have hgab : g = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨hag, hbg⟩
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  have h1 : col u ≠ col a := col.valid (by
    have : s(u, a) ∈ H.edgeSet := heua ▸ he
    exact this)
  have h2 : col u ≠ col b := col.valid (by
    have : s(u, b) ∈ H.edgeSet := hfub ▸ hf
    exact this)
  have h3 : col a ≠ col b := col.valid (by
    have : s(a, b) ∈ H.edgeSet := hgab ▸ hg
    exact this)
  revert h1 h2 h3
  cases col u <;> cases col a <;> cases col b <;> simp


/-! ### From a cycle and a third track of `H` to the `Config` record

The two gaps below differ only in the choice of the cycle and of the point at which it is cut.
Everything after that choice is the same, and is done once here: given the cycle, and a track
`T` of `H` leaving it at a vertex `w` and running to an attachment of `p₂`, the hole of `G`
carried by the cycle together with the rung of `T` extended through `F` is the configuration
the paper describes.
-/

open Workspace.ProofLemmas.Thm58BranchBranchCycleRung
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.Connectivity58CycleBuild

/-- **The configuration of 5.8 (7), given the cycle and the third track.**

`cy` is the cycle of `H`, `T` the track that leaves it at `w` and ends at an attachment of the
far end `p₂` of the outside path, and `pw` is the position of `w` on the cycle.  The hole is the
list of edges of `cy`, the third path is the rung of `T` followed by the outside path run
backwards from `p₂`. -/
theorem config_of_cycle_and_track
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {cy : List (Fin n)} (hcyc : IsCycleList H cy) (h4 : 4 ≤ cy.length)
    (hq₁cy : ∀ z ∈ q₁, z ∈ cy)
    (hcyq₂ : ∀ (i : ℕ) (hi : i < cy.length), cycleEdge cy i hi ∉ trackEdges q₂)
    {T : List (Fin n)} (hT : IsTrackList H T) (hT2 : 2 ≤ T.length)
    {w : Fin n} (hTw : T.head? = some w)
    (hTcy : ∀ z ∈ T, z ∈ cy → z = w)
    (hTattach : ∃ zl, (trackRung φ T hT).getLast? = some zl ∧
      ∀ z ∈ trackRung φ T hT, (G.Adj p₂ z ↔ z = zl))
    {pw : ℕ} (hpw : cy[pw]? = some w) (hpw2 : 2 ≤ pw) :
    ∃ α β t : V, Config G H K N p₁ (cycleRung φ hcyc)
      (trackRung φ T hT ++ (P.drop 1).reverse) (pw - 1) α β t w := by
  classical
  obtain ⟨zl, hzl, hzladj⟩ := hTattach
  -- the hole
  have hZlen : (cycleRung φ hcyc).length = cy.length := cycleRung_length φ hcyc
  have hhole : IsHoleList G (cycleRung φ hcyc) := isHoleList_cycleRung φ hcyc h4
  have hpwlt : pw < cy.length := (List.getElem?_eq_some_iff.mp hpw).1
  have hcyw : cy[pw]'hpwlt = w := (List.getElem?_eq_some_iff.mp hpw).2
  have hZget : ∀ (i : ℕ) (hi : i < cy.length),
      (cycleRung φ hcyc)[i]'(by rw [hZlen]; exact hi)
        = (↑(φ ⟨cycleEdge cy i hi, cycleEdge_mem hcyc i hi⟩) : V) :=
    fun i hi => cycleRung_getElem φ hcyc i (by rw [hZlen]; exact hi) hi
  -- the track
  have hTpos : 0 < T.length := by omega
  have hT0 : T[0]'hTpos = w := by
    have := hTw
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hTpos] at this
    exact Option.some_injective _ this
  have hTnd : T.Nodup := hT.2.1
  have hTnotcy : ∀ (i : ℕ) (hi : i < T.length), i ≠ 0 → T[i]'hi ∉ cy := by
    intro i hi hi0 hmem
    have he := hTcy _ (List.getElem_mem hi) hmem
    rw [← hT0] at he
    exact hi0 (hTnd.getElem_inj_iff.mp he)
  have hRTlen : (trackRung φ T hT).length = T.length - 1 := by
    rw [trackRung_length]; rfl
  have hRTget : ∀ (i : ℕ) (hi : i + 1 < T.length),
      (trackRung φ T hT)[i]'(by rw [hRTlen]; omega)
        = (↑(φ ⟨s(T[i]'(by omega), T[i + 1]'hi), trackEdge_mem_edgeSet hT i hi⟩) : V) :=
    fun i hi => trackRung_getElem φ T hT i (by rw [hRTlen]; omega) hi _
  have hRTmem : ∀ z ∈ trackRung φ T hT, ∃ (i : ℕ) (hi : i + 1 < T.length),
      z = (↑(φ ⟨s(T[i]'(by omega), T[i + 1]'hi), trackEdge_mem_edgeSet hT i hi⟩) : V) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [hRTlen] at hi
    exact ⟨i, by omega, hRTget i (by omega)⟩
  have hZmem : ∀ z ∈ cycleRung φ hcyc, ∃ (k : ℕ) (hk : k < cy.length),
      z = (↑(φ ⟨cycleEdge cy k hk, cycleEdge_mem hcyc k hk⟩) : V) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [hZlen] at hk
    exact ⟨k, hk, hZget k hk⟩
  -- an edge of `T` has at most one end on the cycle
  have hshare : ∀ (i : ℕ) (hi : i + 1 < T.length) (k : ℕ) (hk : k < cy.length) (v : Fin n),
      v ∈ s(T[i]'(by omega), T[i + 1]'hi) → v ∈ cycleEdge cy k hk →
      i = 0 ∧ (k = pw ∨ k + 1 = pw) := by
    intro i hi k hk v hv1 hv2
    have hnxt : nxt cy k < cy.length := nxt_lt hk
    rw [cycleEdge_eq cy k hk hnxt] at hv2
    have hvcy : v ∈ cy := by
      rcases Sym2.mem_iff.mp hv2 with rfl | rfl <;> exact List.getElem_mem _
    have hi0 : i = 0 := by
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · by_contra hh
        exact hTnotcy i (by omega) hh hvcy
      · exact absurd hvcy (hTnotcy (i + 1) hi (by omega))
    subst hi0
    have hvw : v = w := by
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · exact hT0
      · exact absurd hvcy (hTnotcy 1 hi (by omega))
    subst hvw
    refine ⟨rfl, ?_⟩
    have hnd := hcyc.2.1
    rcases Sym2.mem_iff.mp hv2 with hh | hh
    · left
      exact hnd.getElem_inj_iff.mp (hh.symm.trans hcyw.symm)
    · right
      have hkk : nxt cy k = pw := hnd.getElem_inj_iff.mp (hh.symm.trans hcyw.symm)
      rw [nxt, PathGlue.succ_mod_eq hk] at hkk
      split_ifs at hkk <;> omega
  -- adjacency of two vertices of the appearance
  have hadj_iff : ∀ (e f : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet),
      (G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) ↔ (e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f)) := by
    intro e f he hf
    have hmap : G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) ↔
        H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff
    rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne, v, h1, h2⟩
      exact ⟨fun hh => hne (Subtype.ext hh), v, h1, h2⟩
    · rintro ⟨hne, v, h1, h2⟩
      exact ⟨fun hh => hne (congrArg (fun d : H.edgeSet => d.1) hh), v, h1, h2⟩
  -- the three vertices of the triangle
  have hjlt : pw - 1 < cy.length := by omega
  have hnxtj : nxt cy (pw - 1) = pw := by
    rw [nxt, show pw - 1 + 1 = pw by omega]
    exact Nat.mod_eq_of_lt hpwlt
  have hT1 : 1 < T.length := by omega
  set eα : Sym2 (Fin n) := cycleEdge cy (pw - 1) hjlt with heαdef
  set eβ : Sym2 (Fin n) := cycleEdge cy pw hpwlt with heβdef
  set eτ : Sym2 (Fin n) := s(T[0]'hTpos, T[1]'hT1) with heτdef
  have hval : cy[nxt cy (pw - 1)]'(nxt_lt hjlt) = w :=
    (SubdivisionCounting.getElem_eq_of_index_eq cy hnxtj (nxt_lt hjlt) hpwlt).trans hcyw
  have hwα : w ∈ eα := by
    rw [heαdef, cycleEdge_eq cy (pw - 1) hjlt (nxt_lt hjlt), ← hval]
    exact Sym2.mem_mk_right _ _
  have hwβ : w ∈ eβ := by
    rw [heβdef, cycleEdge_eq cy pw hpwlt (nxt_lt hpwlt), ← hcyw]
    exact Sym2.mem_mk_left _ _
  have hwτ : w ∈ eτ := by rw [heτdef, ← hT0]; exact Sym2.mem_mk_left _ _
  have hNw := h.2.2.2.1 w
  have hstar : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), w ∈ e →
      (↑(φ ⟨e, he⟩) : V) ∈ N w := by
    intro e he hwe
    rw [hNw]
    exact ⟨e, he, ⟨he, hwe⟩, rfl⟩
  -- the outside path
  have hPfrom : IsPathFrom G P p₁ p₂ := h.2.2.2.2.2.2.1
  have hPF : {x : V | x ∈ P} = F := h.2.2.2.2.2.2.2.1
  have hFK : F ⊆ Kᶜ := h.2.2.2.2.1
  have hPpos : 0 < P.length := PathBasics.path_length_pos hPfrom.1
  have hP0 : P[0]'hPpos = p₁ := PathBasics.getElem_zero_of_head? hPfrom.2.1 hPpos
  have hPl : P[P.length - 1]'(by omega) = p₂ :=
    PathBasics.getElem_last_of_getLast? hPfrom.2.2 hPpos
  have hPne : p₁ ≠ p₂ := ends_ne h
  have hP2 : 2 ≤ P.length := by
    by_contra hh
    have h1 : P.length = 1 := by omega
    apply hPne
    rw [← hP0, ← hPl]
    exact SubdivisionCounting.getElem_eq_of_index_eq P (by omega) hPpos (by omega)
  have hPnd : P.Nodup := hPfrom.1.2.1
  have hp₁F : p₁ ∈ F := by rw [← hPF]; exact PathBasics.head_mem hPfrom.2.1
  have hp₂F : p₂ ∈ F := by rw [← hPF]; exact PathBasics.getLast_mem hPfrom.2.2
  have hp₁K : p₁ ∉ K := hFK hp₁F
  have hp₂K : p₂ ∉ K := hFK hp₂F
  -- membership in the tail of the outside path
  have hdropmem : ∀ x ∈ P.drop 1, x ∈ F ∧ x ≠ p₁ := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_drop] at hi
    rw [List.getElem_drop] at hxi
    refine ⟨by rw [← hPF]; exact List.mem_iff_getElem.mpr ⟨1 + i, by omega, hxi⟩, ?_⟩
    intro hh
    have := hPnd.getElem_inj_iff (hi := (by omega : 1 + i < P.length)) (hj := hPpos)
      |>.mp (hxi.trans (hh.trans hP0.symm))
    omega
  have hp₁drop : p₁ ∉ P.drop 1 := fun hh => (hdropmem p₁ hh).2 rfl
  -- attachments of the two ends
  have hattach₁ : ∀ x ∈ F, x ≠ p₂ → ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      G.Adj x (↑(φ ⟨e, he⟩) : V) → e ∈ trackEdges q₁ :=
    fun x hxF hx2 e he hadj => hX₁ ⟨he, (φ ⟨e, he⟩).2, x, ⟨hxF, hx2⟩, hadj.symm⟩
  have hattach₂ : ∀ x ∈ F, x ≠ p₁ → ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      G.Adj x (↑(φ ⟨e, he⟩) : V) → e ∈ trackEdges q₂ :=
    fun x hxF hx1 e he hadj => hX₂ ⟨he, (φ ⟨e, he⟩).2, x, ⟨hxF, hx1⟩, hadj.symm⟩
  have hdisjq : Disjoint (trackEdges q₁) (trackEdges q₂) :=
    branches_disjoint h hq₁ hq₂ hX₁ hX₂
  -- no edge of `T` lies on the first branch
  have hTq₁ : ∀ (i : ℕ) (hi : i + 1 < T.length),
      s(T[i]'(by omega), T[i + 1]'hi) ∉ trackEdges q₁ := by
    intro i hi hmem
    obtain ⟨l, hl, hle⟩ := hmem
    have h1 : T[i + 1]'hi ∈ s(q₁[l]'(by omega), q₁[l + 1]'hl) := by
      rw [← hle]; exact Sym2.mem_mk_right _ _
    have : T[i + 1]'hi ∈ cy := by
      rcases Sym2.mem_iff.mp h1 with hh | hh <;>
        exact hh ▸ hq₁cy _ (List.getElem_mem _)
    exact hTnotcy (i + 1) hi (by omega) this
  -- no vertex of the tail of the outside path is adjacent to the hole
  have hFnotZ : ∀ x ∈ P.drop 1, ∀ zz ∈ cycleRung φ hcyc, ¬ G.Adj x zz := by
    intro x hx zz hzz hadj
    obtain ⟨k, hk, rfl⟩ := hZmem zz hzz
    obtain ⟨hxF, hxp₁⟩ := hdropmem x hx
    exact hcyq₂ k hk (hattach₂ x hxF hxp₁ _ _ hadj)
  -- the rung of `T`
  have hRTpath : IsPathList G (trackRung φ T hT) :=
    trackRung_isPathList φ T hT (by simp only [trackLength]; omega)
  have hRTsub : ∀ z ∈ trackRung φ T hT, z ∈ K := trackRung_subset_K φ T hT
  have hRTpos : 0 < (trackRung φ T hT).length := by rw [hRTlen]; omega
  have hRThead : (trackRung φ T hT).head? = some (↑(φ ⟨eτ, trackEdge_mem_edgeSet hT 0 hT1⟩) : V) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hRTpos]
    congr 1
    exact hRTget 0 hT1
  set tv : V := (↑(φ ⟨eτ, trackEdge_mem_edgeSet hT 0 hT1⟩) : V) with htvdef
  set αv : V := (↑(φ ⟨eα, cycleEdge_mem hcyc (pw - 1) hjlt⟩) : V) with hαvdef
  set βv : V := (↑(φ ⟨eβ, cycleEdge_mem hcyc pw hpwlt⟩) : V) with hβvdef
  -- an edge of `T` is never an edge of the cycle
  have hTneCe : ∀ (i : ℕ) (hi : i + 1 < T.length) (k : ℕ) (hk : k < cy.length),
      s(T[i]'(by omega), T[i + 1]'hi) ≠ cycleEdge cy k hk := by
    intro i hi k hk hcon
    have h1 : T[i + 1]'hi ∈ cycleEdge cy k hk := by rw [← hcon]; exact Sym2.mem_mk_right _ _
    rw [cycleEdge_eq cy k hk (nxt_lt hk)] at h1
    have : T[i + 1]'hi ∈ cy := by
      rcases Sym2.mem_iff.mp h1 with hh | hh <;> exact hh ▸ List.getElem_mem _
    exact hTnotcy (i + 1) hi (by omega) this
  -- the two triangle edges at `w`
  have htα : G.Adj tv αv := by
    rw [htvdef, hαvdef, hadj_iff]
    exact ⟨hTneCe 0 hT1 (pw - 1) hjlt, w, hwτ, hwα⟩
  have htβ : G.Adj tv βv := by
    rw [htvdef, hβvdef, hadj_iff]
    exact ⟨hTneCe 0 hT1 pw hpwlt, w, hwτ, hwβ⟩
  -- the tail of the outside path, reversed
  set P1 : V := P[1]'(by omega) with hP1def
  have hdrop0 : (P.drop 1)[0]'(by rw [List.length_drop]; omega) = P1 := by
    rw [List.getElem_drop]
  have hdroppath : IsPathList G (P.drop 1) := PathBasics.isPathList_drop hPfrom.1 (by omega)
  have hdrophead : (P.drop 1).head? = some P1 := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [List.length_drop]; omega),
      hdrop0]
  have hdroplast : (P.drop 1).getLast? = some p₂ := by
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by rw [List.length_drop]; omega)]
    congr 1
    rw [List.getElem_drop]
    rw [SubdivisionCounting.getElem_eq_of_index_eq P
      (show 1 + ((P.drop 1).length - 1) = P.length - 1 by rw [List.length_drop]; omega)
      (by rw [List.length_drop] at *; omega) (by omega)]
    exact hPl
  have hrev : IsPathFrom G ((P.drop 1).reverse) p₂ P1 :=
    PathBasics.isPathFrom_reverse ⟨hdroppath, hdrophead, hdroplast⟩
  have hmemrev : ∀ x ∈ (P.drop 1).reverse, x ∈ P.drop 1 := fun x hx =>
    List.mem_reverse.mp hx
  -- the third path
  have hzlmem : zl ∈ trackRung φ T hT := PathBasics.getLast_mem hzl
  have hglue : IsPathFrom G (trackRung φ T hT ++ (P.drop 1).reverse) tv P1 := by
    refine PathGlue.glue_path ⟨hRTpath, hRThead, hzl⟩ hrev ?_ ?_
    · intro x hx hx'
      exact hFK (hdropmem x (hmemrev x hx')).1 (hRTsub x hx)
    · intro x hx y hy
      have hyF := hdropmem y (hmemrev y hy)
      constructor
      · intro hadj
        have hend := adjacent_vertex_is_end h hq₁ hq₂ hX₁ hX₂ hyF.1 (hRTsub x hx) hadj.symm
        have hyp₂ : y = p₂ := by
          rcases hend with hh | hh
          · exact absurd hh hyF.2
          · exact hh
        exact ⟨(hzladj x hx).mp (hyp₂ ▸ hadj.symm), hyp₂⟩
      · rintro ⟨rfl, rfl⟩
        exact ((hzladj x hx).mpr rfl).symm
  refine ⟨αv, βv, tv, ?_⟩
  refine ⟨hhole, cycleRung_subset_K φ hcyc, by omega, by rw [hZlen]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, hglue.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem (by rw [hZlen]; omega)]
    congr 1
    exact hZget (pw - 1) hjlt
  · rw [show pw - 1 + 1 = pw by omega, List.getElem?_eq_getElem (by rw [hZlen]; omega)]
    congr 1
    exact hZget pw hpwlt
  · -- `w` is a branch-vertex
    have ha1 : H.Adj w (cy[pw - 1]'hjlt) := by
      have := hcyc.2.2 (pw - 1) hjlt (nxt_lt hjlt)
      rw [SubdivisionCounting.getElem_eq_of_index_eq cy hnxtj (nxt_lt hjlt) hpwlt, hcyw] at this
      exact this.symm
    have ha2 : H.Adj w (cy[nxt cy pw]'(nxt_lt hpwlt)) := by
      have := hcyc.2.2 pw hpwlt (nxt_lt hpwlt)
      rwa [hcyw] at this
    have ha3 : H.Adj w (T[1]'hT1) := by
      have := hT.2.2 0 hT1
      rwa [hT0] at this
    have hne12 : cy[pw - 1]'hjlt ≠ cy[nxt cy pw]'(nxt_lt hpwlt) := by
      intro hh
      have := hcyc.2.1.getElem_inj_iff (hi := hjlt) (hj := nxt_lt hpwlt) |>.mp hh
      rw [nxt, PathGlue.succ_mod_eq hpwlt] at this
      split_ifs at this <;> omega
    have hne13 : cy[pw - 1]'hjlt ≠ T[1]'hT1 := fun hh =>
      hTnotcy 1 hT1 (by omega) (hh ▸ List.getElem_mem hjlt)
    have hne23 : cy[nxt cy pw]'(nxt_lt hpwlt) ≠ T[1]'hT1 := fun hh =>
      hTnotcy 1 hT1 (by omega) (hh ▸ List.getElem_mem (nxt_lt hpwlt))
    have hsub : ({cy[pw - 1]'hjlt, cy[nxt cy pw]'(nxt_lt hpwlt), T[1]'hT1} : Set (Fin n))
        ⊆ H.neighborSet w := by
      rintro y (rfl | rfl | hy)
      · exact ha1
      · exact ha2
      · have : y = T[1]'hT1 := hy
        exact this ▸ ha3
    have hcard : ({cy[pw - 1]'hjlt, cy[nxt cy pw]'(nxt_lt hpwlt), T[1]'hT1} : Set (Fin n)).ncard
        = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hne12, hne13]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [hne23]) (Set.toFinite _), Set.ncard_singleton]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [branchVertices, Set.mem_setOf_eq]
    omega
  · exact hstar _ _ hwα
  · exact hstar _ _ hwβ
  · exact hstar _ _ hwτ
  · -- the head of the third path
    rw [List.head?_append, hRThead]
    rfl
  · -- the third path avoids the hole
    intro z hz hzZ
    rcases List.mem_append.mp hz with hz' | hz'
    · obtain ⟨i, hi, rfl⟩ := hRTmem z hz'
      obtain ⟨k, hk, hcon⟩ := hZmem _ hzZ
      exact hTneCe i hi k hk
        (congrArg (fun d : H.edgeSet => d.1) (φ.injective (Subtype.ext hcon)))
    · exact hFK (hdropmem z (hmemrev z hz')).1 (cycleRung_subset_K φ hcyc z hzZ)
  · -- the only edges to the hole are the two triangle edges
    intro z hz zz hzz
    rcases List.mem_append.mp hz with hz' | hz'
    · obtain ⟨i, hi, rfl⟩ := hRTmem z hz'
      obtain ⟨k, hk, rfl⟩ := hZmem zz hzz
      rw [hadj_iff]
      constructor
      · rintro ⟨-, v, hv1, hv2⟩
        obtain ⟨hi0, hk'⟩ := hshare i hi k hk v hv1 hv2
        subst hi0
        refine ⟨rfl, ?_⟩
        rcases hk' with rfl | hk'
        · exact Or.inr rfl
        · have : k = pw - 1 := by omega
          subst this
          exact Or.inl rfl
      · rintro ⟨h1, h2⟩
        have e1 : s(T[i]'(by omega), T[i + 1]'hi) = eτ :=
          congrArg (fun d : H.edgeSet => d.1) (φ.injective (Subtype.ext h1))
        rcases h2 with h2 | h2
        · have e2 : cycleEdge cy k hk = eα :=
            congrArg (fun d : H.edgeSet => d.1) (φ.injective (Subtype.ext h2))
          rw [e1, e2]
          exact ⟨hTneCe 0 hT1 (pw - 1) hjlt, w, hwτ, hwα⟩
        · have e2 : cycleEdge cy k hk = eβ :=
            congrArg (fun d : H.edgeSet => d.1) (φ.injective (Subtype.ext h2))
          rw [e1, e2]
          exact ⟨hTneCe 0 hT1 pw hpwlt, w, hwτ, hwβ⟩
    · constructor
      · intro hadj
        exact absurd hadj (hFnotZ z (hmemrev z hz') zz hzz)
      · rintro ⟨rfl, -⟩
        exact absurd (hRTsub _ (PathBasics.head_mem hRThead)) (hFK (hdropmem _ (hmemrev _ hz')).1)
  · -- the first end of the outside path is not on the third path
    intro hcon
    rcases List.mem_append.mp hcon with hz' | hz'
    · exact hp₁K (hRTsub p₁ hz')
    · exact hp₁drop (hmemrev p₁ hz')
  · -- the first end sees exactly the last vertex of the third path
    refine ⟨P1, hglue.2.2, ?_⟩
    intro z' hz'
    have hP1F : P1 ∈ F := by
      rw [← hPF]; exact List.mem_iff_getElem.mpr ⟨1, by omega, rfl⟩
    rcases List.mem_append.mp hz' with hz'' | hz''
    · constructor
      · intro hadj
        obtain ⟨i, hi, rfl⟩ := hRTmem z' hz''
        exact absurd (hattach₁ p₁ hp₁F hPne _ _ hadj) (hTq₁ i hi)
      · rintro rfl
        exact absurd (hRTsub _ hz'') (hFK hP1F)
    · obtain ⟨i, hi, hz'i⟩ := List.mem_iff_getElem.mp (hmemrev z' hz'')
      rw [List.length_drop] at hi
      rw [List.getElem_drop] at hz'i
      subst hz'i
      rw [← hP0]
      rw [hPfrom.1.2.2 0 (1 + i) hPpos (by omega)]
      constructor
      · intro hh
        have : i = 0 := by omega
        subst this
        exact SubdivisionCounting.getElem_eq_of_index_eq P (by omega) (by omega) (by omega)
      · intro hh
        have : (1 : ℕ) + i = 1 :=
          hPnd.getElem_inj_iff (hi := (by omega : 1 + i < P.length))
            (hj := (by omega : 1 < P.length)) |>.mp hh
        omega


/-- Two vertices of the appearance are adjacent exactly when their edges of `H` are different
and share a vertex. -/
theorem adj_iff_edges_meet (e f : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) :
    (G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) ↔ (e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f)) := by
  have hmap : G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) ↔
      H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff
  rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, h1, h2⟩
    exact ⟨fun hh => hne (Subtype.ext hh), v, h1, h2⟩
  · rintro ⟨hne, v, h1, h2⟩
    exact ⟨fun hh => hne (congrArg (fun d : H.edgeSet => d.1) hh), v, h1, h2⟩

/-- **The `Config` record for the cycle listed from `q₁[s]`.**  Position `mm` of the hole
carries the edge `q₁[s + mm]q₁[s + mm + 1]` of the first branch, and the last position of the
hole carries the edge `q₁[s - 1]q₁[s]`, the one the cut runs through.  The two vertices in the
star of the apex sit at positions `j` and `j + 1`, past every edge of the first branch. -/
theorem exists_config_rotated
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 3 ≤ q₁.length) :
    ∃ (Z R : List V) (j : ℕ) (α β t : V) (u : Fin n),
      Config G H K N p₁ Z R j α β t u ∧
      q₁.length - 2 - s ≤ j ∧
      (∀ (mm : ℕ) (hm : s + mm + 1 < q₁.length)
          (he : s(q₁[s + mm]'(by omega), q₁[s + mm + 1]'hm) ∈ H.edgeSet),
          Z[mm]? = some (↑(φ ⟨_, he⟩) : V)) ∧
      (∀ (he : s(q₁[s - 1]'(by omega), q₁[s]'(by omega)) ∈ H.edgeSet),
          Z[Z.length - 1]? = some (↑(φ ⟨_, he⟩) : V)) := by
  classical
  obtain ⟨D, hcyc, hD3, hq₁cy, hcyq₂, T, hT, u, pw, hT2, hThead, hTcy, hTattach, hpw, hpwge⟩ :=
    Workspace.ProofLemmas.Thm58BranchBranchCycleHost.exists_cycle_and_track h hq₁ hq₂ hX₁ hX₂ hs1 hs2
  have hcylen := cycleFrom_length q₁ D s
  have h4 : 4 ≤ (cycleFrom q₁ D s).length := by omega
  have hpw2 : 2 ≤ pw := by omega
  obtain ⟨α, β, t, hcfg⟩ :=
    config_of_cycle_and_track h hq₁ hq₂ hX₁ hX₂ hcyc h4 hq₁cy hcyq₂ hT hT2 hThead hTcy
      hTattach hpw hpw2
  have hZlen : (cycleRung φ hcyc).length = (cycleFrom q₁ D s).length := cycleRung_length φ hcyc
  refine ⟨cycleRung φ hcyc, _, pw - 1, α, β, t, u, hcfg, by omega, ?_, ?_⟩
  · intro mm hm he
    have hmlt : mm < (cycleFrom q₁ D s).length := by omega
    have hnxt : nxt (cycleFrom q₁ D s) mm = mm + 1 := by
      rw [nxt]; exact Nat.mod_eq_of_lt (by omega)
    have e0 : (cycleFrom q₁ D s)[mm]'hmlt = q₁[s + mm]'(by omega) :=
      cycleFrom_getElem_branch q₁ D s mm (by omega) hmlt
    have e1 : (cycleFrom q₁ D s)[nxt (cycleFrom q₁ D s) mm]'(nxt_lt hmlt)
        = q₁[s + mm + 1]'hm := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq _ hnxt (nxt_lt hmlt) (by omega),
        cycleFrom_getElem_branch q₁ D s (mm + 1) (by omega) (by omega)]
      exact SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
    have hedge : cycleEdge (cycleFrom q₁ D s) mm hmlt
        = s(q₁[s + mm]'(by omega), q₁[s + mm + 1]'hm) := by
      rw [cycleEdge_eq _ mm hmlt (nxt_lt hmlt), e0, e1]
    rw [List.getElem?_eq_getElem (by omega : mm < (cycleRung φ hcyc).length),
      cycleRung_getElem φ hcyc mm (by omega) hmlt]
    exact congrArg (fun d : H.edgeSet => some (↑(φ d) : V)) (Subtype.ext hedge)
  · intro he
    have hlast : (cycleFrom q₁ D s).length - 1 < (cycleFrom q₁ D s).length := by omega
    have hnxtl : nxt (cycleFrom q₁ D s) ((cycleFrom q₁ D s).length - 1) = 0 := by
      rw [nxt, show (cycleFrom q₁ D s).length - 1 + 1 = (cycleFrom q₁ D s).length by omega,
        Nat.mod_self]
    have e0 : (cycleFrom q₁ D s)[(cycleFrom q₁ D s).length - 1]'hlast = q₁[s - 1]'(by omega) :=
      cycleFrom_getElem_last q₁ D s hs1 (by omega) hD3 hlast
    have e1 : (cycleFrom q₁ D s)[nxt (cycleFrom q₁ D s) ((cycleFrom q₁ D s).length - 1)]'
        (nxt_lt hlast) = q₁[s]'(by omega) := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq _ hnxtl (nxt_lt hlast) (by omega),
        cycleFrom_getElem_branch q₁ D s 0 (by omega) (by omega)]
      exact SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
    have hedge : cycleEdge (cycleFrom q₁ D s) ((cycleFrom q₁ D s).length - 1) hlast
        = s(q₁[s - 1]'(by omega), q₁[s]'(by omega)) := by
      rw [cycleEdge_eq _ _ hlast (nxt_lt hlast), e0, e1]
    have hidx : (cycleRung φ hcyc).length - 1 = (cycleFrom q₁ D s).length - 1 := by omega
    rw [List.getElem?_eq_getElem
        (by omega : (cycleRung φ hcyc).length - 1 < (cycleRung φ hcyc).length),
      SubdivisionCounting.getElem_eq_of_index_eq (cycleRung φ hcyc) hidx _ (by omega),
      cycleRung_getElem φ hcyc ((cycleFrom q₁ D s).length - 1) (by omega) hlast]
    exact congrArg (fun d : H.edgeSet => some (↑(φ d) : V)) (Subtype.ext hedge)

/-- GAP — PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the
branch between `u₁` and `v₁`, and using `u₂` and not `v₂` (since `J \ v₂` is
2-connected).  There correspond two paths in `L(H)`, say `P` and `Q`, from
`N_{u₁}` and `N_{v₁}` respectively to `N_{u₂}`, disjoint from each other, and
there is a third path `R` say from `p₁` to `N_{u₂}` via `F` and a subpath of
`R_{u₂v₂}`.  There are no edges between these paths except within the triangle
`T` formed by their ends in `N_{u₂}`."*

This is the version used when a vertex `w` of the first rung is to be deleted:
the hole is listed with `w` first, and `P`, `Q` are the two arcs obtained by
`Thm58BranchBranchCut.link_of_hole_cut`.  The hypothesis on `w` says that its
edge of `H` is internal to the branch, which is what keeps `w` away from the two
cycle edges at `u₂`; `R` is listed from its end in `N_{u₂}` towards `F`, and
stops just before `p₁`. -/
theorem cycle_config_at_interior_edge
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {w : V} (hwK : w ∈ K) (hwq : (φ.symm ⟨w, hwK⟩).1 ∈ trackEdges q₁)
    (hwint : ∀ c ∈ branchVertices H, c ∉ (φ.symm ⟨w, hwK⟩).1) :
    ∃ (Z R : List V) (j : ℕ) (α β t : V) (u : Fin n),
      Config G H K N p₁ Z R j α β t u ∧ Z[0]? = some w := by
  classical
  obtain ⟨s, hs, hes⟩ := hwq
  have hJ : IsKConnected J 3 := h.2.1
  have hsub : IsSubdivision J H := h.2.2.1.1
  have hq₁2 : 2 ≤ q₁.length := by omega
  have hq₁ne : q₁ ≠ [] := hq₁.1.1
  have hq₁from : IsTrackFrom H q₁ (q₁[0]'(by omega)) (q₁[q₁.length - 1]'(by omega)) := by
    refine ⟨hq₁.1, ?_, ?_⟩
    · rw [List.head?_eq_head hq₁ne, List.head_eq_getElem]
    · rw [List.getLast?_eq_getLast hq₁ne, List.getLast_eq_getElem]
  obtain ⟨hbv₁, hbv₂⟩ := Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H hsub q₁ _ _
    hq₁ hq₁from (by simp only [trackLength]; omega)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · refine absurd ?_ (hwint _ hbv₁)
      rw [hes, Sym2.mem_iff]
      exact Or.inl (SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _)
    · exact h0
  have hs3 : s + 3 ≤ q₁.length := by
    by_contra hcon
    refine hwint _ hbv₂ ?_
    rw [hes, Sym2.mem_iff]
    exact Or.inr (SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _)
  obtain ⟨Z, R, j, α, β, t, u, hcfg, -, hfwd, -⟩ :=
    exists_config_rotated h hq₁ hq₂ hX₁ hX₂ hs1 hs3
  refine ⟨Z, R, j, α, β, t, u, hcfg, ?_⟩
  have hem : s(q₁[s + 0]'(by omega), q₁[s + 0 + 1]'(by omega)) ∈ H.edgeSet :=
    trackEdge_mem_edgeSet hq₁.1 (s + 0) (by omega)
  have hsu : (⟨_, hem⟩ : H.edgeSet) = φ.symm ⟨w, hwK⟩ := Subtype.ext hes.symm
  rw [hfwd 0 (by omega) hem, hsu, φ.apply_symm_apply]


/-- The separating configuration when the edge of `a` comes before the edge of `b` along the
first branch: cut the cycle just after the edge of `a`, so that the edge of `b` sits at position
`r - p - 1` of the hole and the edge of `a` at its last position. -/
theorem separating_aux
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    {p r : ℕ} (hp : p + 1 < q₁.length) (hr : r + 1 < q₁.length)
    (hea : (φ.symm ⟨a, haK⟩).1 = s(q₁[p]'(by omega), q₁[p + 1]'hp))
    (heb : (φ.symm ⟨b, hbK⟩).1 = s(q₁[r]'(by omega), q₁[r + 1]'hr))
    (hpr : p + 2 ≤ r) :
    ∃ (Z R : List V) (j : ℕ) (α β t : V) (u : Fin n),
      Config G H K N p₁ Z R j α β t u ∧
      ∃ i k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j + 1 ≤ k ∧ k < Z.length ∧
        (Z[i]? = some b ∧ Z[k]? = some a) := by
  classical
  obtain ⟨Z, R, j, α, β, t, u, hcfg, hj, hfwd, hlst⟩ :=
    exists_config_rotated h hq₁ hq₂ hX₁ hX₂ (s := p + 1) (by omega) (by omega)
  have hjlt := hcfg.jlt
  refine ⟨Z, R, j, α, β, t, u, hcfg, r - (p + 1), Z.length - 1, by omega, by omega,
    by omega, by omega, ?_, ?_⟩
  · have hem : s(q₁[(p + 1) + (r - (p + 1))]'(by omega),
        q₁[(p + 1) + (r - (p + 1)) + 1]'(by omega)) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet hq₁.1 _ (by omega)
    have i1 : q₁[(p + 1) + (r - (p + 1))]'(by omega) = q₁[r]'(by omega) :=
      SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
    have i2 : q₁[(p + 1) + (r - (p + 1)) + 1]'(by omega) = q₁[r + 1]'hr :=
      SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
    have hsym : s(q₁[(p + 1) + (r - (p + 1))]'(by omega),
        q₁[(p + 1) + (r - (p + 1)) + 1]'(by omega)) = (φ.symm ⟨b, hbK⟩).1 := by
      rw [heb, i1, i2]
    have hsu : (⟨_, hem⟩ : H.edgeSet) = φ.symm ⟨b, hbK⟩ := Subtype.ext hsym
    rw [hfwd (r - (p + 1)) (by omega) hem, hsu, φ.apply_symm_apply]
  · have hem : s(q₁[(p + 1) - 1]'(by omega), q₁[p + 1]'(by omega)) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet hq₁.1 ((p + 1) - 1) (by omega)
    have i1 : q₁[(p + 1) - 1]'(by omega) = q₁[p]'(by omega) :=
      SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
    have hsym : s(q₁[(p + 1) - 1]'(by omega), q₁[p + 1]'(by omega))
        = (φ.symm ⟨a, haK⟩).1 := by rw [hea, i1]
    have hsu : (⟨_, hem⟩ : H.edgeSet) = φ.symm ⟨a, haK⟩ := Subtype.ext hsym
    rw [hlst hem, hsu, φ.apply_symm_apply]

/-- GAP — PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the
branch between `u₁` and `v₁`, and using `u₂` and not `v₂` (since `J \ v₂` is
2-connected).  There correspond two paths in `L(H)`, say `P` and `Q`, from
`N_{u₁}` and `N_{v₁}` respectively to `N_{u₂}`, disjoint from each other, and
there is a third path `R` say from `p₁` to `N_{u₂}` via `F` and a subpath of
`R_{u₂v₂}`.  There are no edges between these paths except within the triangle
`T` formed by their ends in `N_{u₂}`."*

This is the version used when two nonadjacent vertices `a`, `b` of the first
rung are to be separated: the cycle is cut at a vertex of the rung lying between
them, so that `a` and `b` end up on different arcs.  Which of the two arcs
carries `a` is not determined, whence the final disjunction. -/
theorem cycle_config_separating
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    (haq : (φ.symm ⟨a, haK⟩).1 ∈ trackEdges q₁)
    (hbq : (φ.symm ⟨b, hbK⟩).1 ∈ trackEdges q₁)
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b) :
    ∃ (Z R : List V) (j : ℕ) (α β t : V) (u : Fin n),
      Config G H K N p₁ Z R j α β t u ∧
      ∃ i k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j + 1 ≤ k ∧ k < Z.length ∧
        ((Z[i]? = some a ∧ Z[k]? = some b) ∨ (Z[i]? = some b ∧ Z[k]? = some a)) := by
  classical
  obtain ⟨p, hp, hea⟩ := haq
  obtain ⟨r, hr, heb⟩ := hbq
  have hnee : φ.symm ⟨a, haK⟩ ≠ φ.symm ⟨b, hbK⟩ := by
    intro hh
    exact hab (congrArg Subtype.val (φ.symm.injective hh))
  have hnoshare : ∀ v, v ∈ (φ.symm ⟨a, haK⟩).1 → v ∈ (φ.symm ⟨b, hbK⟩).1 → False := by
    intro v h1 h2
    apply hnadj
    have hlg : H.lineGraph.Adj (φ.symm ⟨a, haK⟩) (φ.symm ⟨b, hbK⟩) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hnee, v, h1, h2⟩
    have hgg := φ.map_rel_iff.mpr hlg
    rw [φ.apply_symm_apply, φ.apply_symm_apply] at hgg
    exact hgg
  have hsep : p + 2 ≤ r ∨ r + 2 ≤ p := by
    by_contra hcon
    push_neg at hcon
    have hcases : p = r ∨ r = p + 1 ∨ p = r + 1 := by omega
    rcases hcases with hh | hh | hh
    · subst hh
      exact hnee (Subtype.ext (hea.trans heb.symm))
    · subst hh
      exact hnoshare (q₁[p + 1]'hp) (by rw [hea]; exact Sym2.mem_mk_right _ _)
        (by rw [heb]; exact Sym2.mem_mk_left _ _)
    · subst hh
      exact hnoshare (q₁[r + 1]'hr) (by rw [hea]; exact Sym2.mem_mk_left _ _)
        (by rw [heb]; exact Sym2.mem_mk_right _ _)
  rcases hsep with hh | hh
  · obtain ⟨Z, R, j, α, β, t, u, hcfg, i, k, h1, h2, h3, h4, h5, h6⟩ :=
      separating_aux h hq₁ hq₂ hX₁ hX₂ haK hbK hp hr hea heb hh
    exact ⟨Z, R, j, α, β, t, u, hcfg, i, k, h1, h2, h3, h4, Or.inr ⟨h5, h6⟩⟩
  · obtain ⟨Z, R, j, α, β, t, u, hcfg, i, k, h1, h2, h3, h4, h5, h6⟩ :=
      separating_aux h hq₁ hq₂ hX₁ hX₂ hbK haK hr hp heb hea hh
    exact ⟨Z, R, j, α, β, t, u, hcfg, i, k, h1, h2, h3, h4, Or.inl ⟨h5, h6⟩⟩

end Workspace.ProofLemmas.Thm58BranchBranchCycle
