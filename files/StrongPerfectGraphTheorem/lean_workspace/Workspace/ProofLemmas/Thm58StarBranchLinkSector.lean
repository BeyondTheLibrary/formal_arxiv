import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.PathGlue

/-!
# The third path of 5.8 (6): out of the star and along `P`

PAPER (proof of 5.8 (6), printed p. 28): *"Hence in `L(H)` there are three vertex-disjoint
paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w` … If `pₙ` has a unique neighbour
(say `r`) in `R_{v₁v₂}`, then `r` can be linked onto the triangle `T`."*

The path *"from `N_u`"* is the rung of the minimal track `S`, continued through the star at
`u = c` into the connected set `F`.  This file builds the part after the rung: the neighbour
of `p₁` in the star, if it is not already the last vertex of the rung, followed by the path
through `F`.  The two facts that make the result induced are that the only edge of `H` on the
minimal track through `c` is the last one (no chord at `c`), and that the two ends of `P` are
the only vertices of `F` with neighbours in `L(H)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchLinkSector

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- Vertices of `P` are outside the appearance. -/
theorem mem_P_not_mem_K (h : Context G m J n H K φ N F P p₁ p₂ c q) {u : V}
    (hu : u ∈ P) : u ∉ K := by
  have hF : F ⊆ Kᶜ := h.ready.2.2.2.2.1
  have : u ∈ F := by rw [← vertices h]; exact hu
  exact hF this

/-- An edge of `G` between the rung of the minimal track and `P` runs from the last vertex of
that rung to `p₁`. -/
theorem rung_adj_P (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {S₂ : List (Fin n)} {w : Fin n} (hS₂ : IsTrackFrom H S₂ w c) (hlen₂ : 2 ≤ S₂.length)
    (hS₂q : ∀ z ∈ S₂, z ∉ q) {u y : V} (hu : u ∈ P)
    (hy : y ∈ trackRung φ S₂ hS₂.1) (hadj : G.Adj y u) :
    y = lastRungVertex φ S₂ hS₂.1 hlen₂ ∧ u = p₁ := by
  classical
  obtain ⟨e, he, heS, rfl⟩ := (mem_trackRung_iff φ hS₂.1).mp hy
  have hyK : (φ ⟨e, he⟩ : V) ∈ K := (φ ⟨e, he⟩).2
  rcases edges_of_disjoint h (star_disjoint_branch h hcq) u hu _ hyK hadj.symm with hh | hh
  · refine ⟨?_, hh.1⟩
    -- the edge lies in the star at `c`, hence contains `c`, hence is the last edge
    have hstar : (φ ⟨e, he⟩ : V) ∈ edgeImage φ (incidentEdges H c) := by
      rw [← star_eq h c]; exact hh.2
    have hce : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hstar
    have := edge_eq_lastTrackEdge hS₂ hlen₂ heS hce.2
    exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext this)
  · exfalso
    have heq : e ∈ trackEdges q := (image_mem_iff (φ := φ) he).mp hh.2
    obtain ⟨i, hi, rfl⟩ := heq
    obtain ⟨j, hj, hje⟩ := heS
    have : q[i]'(by omega) ∈ S₂ := by
      have : q[i]'(by omega) ∈ s(S₂[j]'(by omega), S₂[j + 1]'hj) := by
        rw [← hje]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.mp this with hh' | hh' <;> rw [hh'] <;> exact List.getElem_mem _
    exact hS₂q _ this (List.getElem_mem _)

/-- **The third path of claim (6), after its rung**, with the sharper record of where its
vertices come from: each is a vertex of `Q₀` itself, or the star vertex prepended to it.  This
is what says that the extension misses `pₙ` when `Q₀` does. -/
theorem exists_star_extension_strong
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {S₂ : List (Fin n)} {w : Fin n} (hS₂ : IsTrackFrom H S₂ w c) (hlen₂ : 2 ≤ S₂.length)
    (hS₂q : ∀ z ∈ S₂, z ∉ q)
    (hchord : ∀ y : Fin n, y ∈ S₂ → H.Adj c y → y = S₂[S₂.length - 2]'(by omega))
    {Q₀ : List V} {yend : V} (hQ₀ : IsPathFrom G Q₀ p₁ yend) (hQ₀P : ∀ u ∈ Q₀, u ∈ P)
    (A : Set (Fin n))
    (hstar : ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) ∧ (x ∉ S₂ → x ∉ A)) :
    ∃ (Q : List V) (z : V), IsPathFrom G Q z yend ∧
      (∀ u ∈ Q, u ∉ trackRung φ S₂ hS₂.1) ∧
      (∀ u ∈ Q, ∀ y ∈ trackRung φ S₂ hS₂.1,
        (G.Adj y u ↔ (y = lastRungVertex φ S₂ hS₂.1 hlen₂ ∧ u = z))) ∧
      (∀ u ∈ Q, u ∈ Q₀ ∨ ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
          x ∉ A ∧ u = (φ ⟨s(c, x), hx⟩ : V)) ∧
      (∀ u ∈ Q₀, u ∈ Q) := by
  classical
  have hp₁Q₀ : p₁ ∈ Q₀ := PathBasics.head_mem hQ₀.2.1
  have hQ₀K : ∀ u ∈ Q₀, u ∉ K := fun u hu => mem_P_not_mem_K h (hQ₀P u hu)
  have hrungK : ∀ y ∈ trackRung φ S₂ hS₂.1, y ∈ K := trackRung_subset_K φ S₂ hS₂.1
  by_cases hcase : G.Adj p₁ (lastRungVertex φ S₂ hS₂.1 hlen₂)
  · -- the neighbour of `p₁` in the star is already the last vertex of the rung
    refine ⟨Q₀, p₁, hQ₀, ?_, ?_, fun u hu => Or.inl hu, fun u hu => hu⟩
    · exact fun u hu hmem => hQ₀K u hu (hrungK u hmem)
    · intro u hu y hy
      constructor
      · exact fun hadj => rung_adj_P h hcq hS₂ hlen₂ hS₂q (hQ₀P u hu) hy hadj
      · rintro ⟨rfl, rfl⟩
        exact hcase.symm
  · -- a genuinely new star vertex is needed
    obtain ⟨x, hx, hax, hxA⟩ := hstar
    set a : V := (φ ⟨s(c, x), hx⟩ : V) with ha
    have haK : a ∈ K := (φ ⟨s(c, x), hx⟩).2
    have hxS₂ : x ∉ S₂ := by
      intro hmem
      apply hcase
      have hxadj : H.Adj c x := (SimpleGraph.mem_edgeSet H).mp hx
      have hxe : x = S₂[S₂.length - 2]'(by omega) := hchord x hmem hxadj
      have hclast : S₂[S₂.length - 1]'(by omega) = c := by
        have hh := hS₂.2.2
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
        exact Option.some_injective _ hh
      have : s(c, x) = lastTrackEdge S₂ hlen₂ := by
        rw [hxe, ← hclast]
        simp only [lastTrackEdge]
        exact Sym2.eq_swap
      have : a = lastRungVertex φ S₂ hS₂.1 hlen₂ :=
        congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext this)
      rw [← this]
      exact hax
    have hxA' : x ∉ A := hxA hxS₂
    -- `a` sees exactly `p₁` inside `P`
    have hacross : ∀ u ∈ Q₀, (G.Adj a u ↔ u = p₁) := by
      intro u hu
      constructor
      · intro hadj
        rcases edges_of_disjoint h (star_disjoint_branch h hcq) u (hQ₀P u hu) a haK hadj.symm
          with hh | hh
        · exact hh.1
        · exact absurd hh.2 (fun hmem => Set.disjoint_left.mp (star_disjoint_branch h hcq)
            (by rw [star_eq h c]; exact ⟨s(c, x), hx, ⟨hx, Sym2.mem_mk_left _ _⟩, ha⟩) hmem)
      · rintro rfl
        exact hax.symm
    have hQ : IsPathFrom G ([a] ++ Q₀) a yend := by
      refine PathGlue.glue_path ⟨PathBasics.isPathList_singleton G a, rfl, rfl⟩ hQ₀ ?_ ?_
      · intro z hz
        rw [List.mem_singleton] at hz
        rw [hz]
        exact fun hmem => hQ₀K a hmem haK
      · intro z hz u hu
        rw [List.mem_singleton] at hz
        subst hz
        rw [hacross u hu]
        simp
    -- the new star vertex is not on the rung
    have hanotrung : a ∉ trackRung φ S₂ hS₂.1 := by
      intro hmem
      obtain ⟨e, he, heS, hae⟩ := (mem_trackRung_iff φ hS₂.1).mp hmem
      have : s(c, x) = e := congrArg Subtype.val (φ.injective (Subtype.ext hae))
      obtain ⟨j, hj, hje⟩ := heS
      apply hxS₂
      have : x ∈ s(S₂[j]'(by omega), S₂[j + 1]'hj) := by
        rw [← hje, ← this]; exact Sym2.mem_mk_right _ _
      rcases Sym2.mem_iff.mp this with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
    have halast : G.Adj (lastRungVertex φ S₂ hS₂.1 hlen₂) a := by
      apply φ.map_rel_iff.mpr
      refine ⟨fun hh => ?_, c, lastTrackEdge_contains hS₂ hlen₂, Sym2.mem_mk_left _ _⟩
      · -- the two edges are different, since `x` is not on the track
        have hlt : lastTrackEdge S₂ hlen₂ = s(c, x) := congrArg Subtype.val hh
        apply hxS₂
        have : x ∈ lastTrackEdge S₂ hlen₂ := by rw [hlt]; exact Sym2.mem_mk_right _ _
        simp only [lastTrackEdge] at this
        rcases Sym2.mem_iff.mp this with hh' | hh' <;> rw [hh'] <;> exact List.getElem_mem _
    refine ⟨[a] ++ Q₀, a, hQ, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu' | hu'
      · rw [List.mem_singleton] at hu'; subst hu'; exact hanotrung
      · exact fun hmem => hQ₀K u hu' (hrungK u hmem)
    · intro u hu y hy
      rcases List.mem_append.mp hu with hu' | hu'
      · rw [List.mem_singleton] at hu'
        subst hu'
        constructor
        · intro hadj
          refine ⟨?_, rfl⟩
          obtain ⟨e, he, heS, rfl⟩ := (mem_trackRung_iff φ hS₂.1).mp hy
          obtain ⟨hne, z, hze, hza⟩ :=
            SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
          have hz : z = c ∨ z = x := by simpa using hza
          rcases hz with rfl | rfl
          · exact congrArg (fun t : H.edgeSet => (φ t : V))
              (Subtype.ext (edge_eq_lastTrackEdge hS₂ hlen₂ heS hze))
          · exfalso
            apply hxS₂
            obtain ⟨j, hj, hje⟩ := heS
            have : z ∈ s(S₂[j]'(by omega), S₂[j + 1]'hj) := by rw [← hje]; exact hze
            rcases Sym2.mem_iff.mp this with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
        · rintro ⟨rfl, -⟩
          exact halast
      · constructor
        · intro hadj
          exfalso
          obtain ⟨hy1, hu1⟩ := rung_adj_P h hcq hS₂ hlen₂ hS₂q (hQ₀P u hu') hy hadj
          rw [hy1, hu1] at hadj
          exact hcase hadj.symm
        · rintro ⟨-, hua⟩
          exact absurd (hua ▸ haK) (hQ₀K u hu')
    · intro u hu
      rcases List.mem_append.mp hu with hu' | hu'
      · rw [List.mem_singleton] at hu'
        exact Or.inr ⟨x, hx, hxA', hu'.trans ha⟩
      · exact Or.inl hu'
    · intro u hu
      exact List.mem_append.mpr (Or.inr hu)

/-- **The third path of claim (6), after its rung.**

`Q₀` is the part of `P` that is used (all of it when the vertex to be linked is `r`, all but
`pₙ` when it is `pₙ` itself).  The result is `Q₀` preceded, when necessary, by a neighbour of
`p₁` in the star at `c`.  `A` is the set of vertices of `H` used by the other two tracks; the
star vertex chosen is required to avoid it. -/
theorem exists_star_extension
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {S₂ : List (Fin n)} {w : Fin n} (hS₂ : IsTrackFrom H S₂ w c) (hlen₂ : 2 ≤ S₂.length)
    (hS₂q : ∀ z ∈ S₂, z ∉ q)
    (hchord : ∀ y : Fin n, y ∈ S₂ → H.Adj c y → y = S₂[S₂.length - 2]'(by omega))
    {Q₀ : List V} {yend : V} (hQ₀ : IsPathFrom G Q₀ p₁ yend) (hQ₀P : ∀ u ∈ Q₀, u ∈ P)
    (A : Set (Fin n))
    (hstar : ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) ∧ (x ∉ S₂ → x ∉ A)) :
    ∃ (Q : List V) (z : V), IsPathFrom G Q z yend ∧
      (∀ u ∈ Q, u ∉ trackRung φ S₂ hS₂.1) ∧
      (∀ u ∈ Q, ∀ y ∈ trackRung φ S₂ hS₂.1,
        (G.Adj y u ↔ (y = lastRungVertex φ S₂ hS₂.1 hlen₂ ∧ u = z))) ∧
      (∀ u ∈ Q, u ∈ P ∨ ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
          x ∉ A ∧ u = (φ ⟨s(c, x), hx⟩ : V)) ∧
      (∀ u ∈ Q₀, u ∈ Q) := by
  obtain ⟨Q, z, hQ, h1, h2, h3, h4⟩ :=
    exists_star_extension_strong h hcq hS₂ hlen₂ hS₂q hchord hQ₀ hQ₀P A hstar
  exact ⟨Q, z, hQ, h1, h2, fun u hu => (h3 u hu).imp (fun hh => hQ₀P u hh) id, h4⟩


end Workspace.ProofLemmas.Thm58StarBranchLinkSector
