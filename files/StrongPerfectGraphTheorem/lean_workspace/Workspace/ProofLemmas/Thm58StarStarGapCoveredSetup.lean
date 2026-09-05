import Workspace.ProofLemmas.Thm58StarStarTracks
import Workspace.ProofLemmas.Thm58StarStarGapTracks

/-!
# The data of the last paragraph of 5.8 (4)

The final paragraph of the proof of claim (4) of 5.8 works with a fixed collection of objects:
the branch `q` between the two star vertices, its rung `R` with ends `r₁, r₂`, the common
neighbour `w` of the two star vertices, and the two singleton attachment sets `A₁ = {a₁}`,
`A₂ = {a₂}`.  This file bundles them into `Cov`, records the elementary facts about `a₁` and
`a₂`, and proves the two counting statements of the paragraph: *"the branch of `H` with ends
`v₁, v₂` has even length, and therefore `R_{v₁v₂}` has odd length, and in particular
`r₁ ≠ r₂`"*, and *"the hole `p₁-⋯-pₙ-a₂-a₁-p₁` is even, and so `n` is even"*.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapCoveredSetup

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles
open ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ w : Fin n}
  {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

/-- The hypotheses of the last paragraph of the proof of 5.8 (4), bundled.  They are exactly
the hypotheses of `Thm58StarStarGapCovered.covered_endgame`, minus the disjunction `hB`, which
that paragraph never uses. -/
structure Cov (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (F : Set V) (P : List V) (p₁ p₂ : V) (c₁ c₂ w : Fin n)
    (q : List (Fin n)) (R : List V) (r₁ r₂ : V) : Prop where
  ctx : Context G m J n H K φ N F P p₁ p₂ c₁ c₂
  branch : IsBranch H q
  from' : IsTrackFrom H q c₁ c₂
  len2 : 2 ≤ q.length
  rung : IsPathFrom G R r₁ r₂
  rungSet : {x : V | x ∈ R} = edgeImage φ (trackEdges q)
  int₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}
  int₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂}
  adjw₁ : H.Adj c₁ w
  adjw₂ : H.Adj c₂ w
  off₁ : s(c₁, w) ∉ trackEdges q
  off₂ : s(c₂, w) ∉ trackEdges q
  sing₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x = (φ ⟨s(c₁, w), adjw₁⟩ : V)
  sing₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x = (φ ⟨s(c₂, w), adjw₂⟩ : V)
  ne₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x
  ne₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x

variable (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂)

/-- PAPER: *"`Aᵢ = {aᵢ}`"* for `i = 1`: the vertex of `L(H)` given by the edge `v₁w`. -/
def Cov.a₁ (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂) : V :=
  (φ ⟨s(c₁, w), hc.adjw₁⟩ : V)

/-- PAPER: *"`Aᵢ = {aᵢ}`"* for `i = 2`: the vertex of `L(H)` given by the edge `v₂w`. -/
def Cov.a₂ (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂) : V :=
  (φ ⟨s(c₂, w), hc.adjw₂⟩ : V)

include hc

/-! ## The two star vertices, `w`, and the two attachment vertices -/

theorem stars_ne' : c₁ ≠ c₂ := stars_ne hc.ctx

theorem w_ne₁ : w ≠ c₁ := hc.adjw₁.ne'

theorem w_ne₂ : w ≠ c₂ := hc.adjw₂.ne'

theorem mem_R_iff {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    (φ ⟨e, he⟩ : V) ∈ R ↔ e ∈ trackEdges q := by
  have : ((φ ⟨e, he⟩ : V) ∈ {x : V | x ∈ R}) ↔ (φ ⟨e, he⟩ : V) ∈ edgeImage φ (trackEdges q) := by
    rw [hc.rungSet]
  rw [Set.mem_setOf_eq] at this
  rw [this, image_mem_iff he]

theorem a₁_mem_star₁ : hc.a₁ ∈ N c₁ :=
  (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₁).mpr (Sym2.mem_mk_left _ _)

theorem a₁_mem_starw : hc.a₁ ∈ N w :=
  (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₁).mpr (Sym2.mem_mk_right _ _)

theorem a₂_mem_star₂ : hc.a₂ ∈ N c₂ :=
  (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₂).mpr (Sym2.mem_mk_left _ _)

theorem a₂_mem_starw : hc.a₂ ∈ N w :=
  (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₂).mpr (Sym2.mem_mk_right _ _)

theorem a₁_mem_K : hc.a₁ ∈ K := star_subset hc.ctx c₁ (a₁_mem_star₁ hc)

theorem a₂_mem_K : hc.a₂ ∈ K := star_subset hc.ctx c₂ (a₂_mem_star₂ hc)

theorem a₁_not_mem_star₂ : hc.a₁ ∉ N c₂ := by
  intro hmem
  have hin : c₂ ∈ s(c₁, w) :=
    (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₁).mp hmem
  rcases Sym2.mem_iff.mp hin with h | h
  · exact stars_ne' hc h.symm
  · exact w_ne₂ hc h.symm

theorem a₂_not_mem_star₁ : hc.a₂ ∉ N c₁ := by
  intro hmem
  have hin : c₁ ∈ s(c₂, w) :=
    (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hc.adjw₂).mp hmem
  rcases Sym2.mem_iff.mp hin with h | h
  · exact stars_ne' hc h
  · exact w_ne₁ hc h.symm

theorem a₁_not_mem_R : hc.a₁ ∉ R := fun hmem => hc.off₁ ((mem_R_iff hc hc.adjw₁).mp hmem)

theorem a₂_not_mem_R : hc.a₂ ∉ R := fun hmem => hc.off₂ ((mem_R_iff hc hc.adjw₂).mp hmem)

theorem a_ne : hc.a₁ ≠ hc.a₂ := fun hcon => a₁_not_mem_star₂ hc (hcon ▸ a₂_mem_star₂ hc)

theorem a_adj : G.Adj hc.a₁ hc.a₂ :=
  star_adj (star_eq hc.ctx) w (a₁_mem_starw hc) (a₂_mem_starw hc) (a_ne hc)

/-- PAPER: *"`A₁ = {a₁}`"*: `p₁` is adjacent to `a₁`. -/
theorem adj_p₁_a₁ : G.Adj p₁ hc.a₁ := by
  obtain ⟨x, hx, hadj⟩ := hc.ne₁
  have hx' := hc.sing₁ x hx hadj
  rw [hx'] at hadj
  exact hadj

/-- PAPER: *"`A₂ = {a₂}`"*: `p₂` is adjacent to `a₂`. -/
theorem adj_p₂_a₂ : G.Adj p₂ hc.a₂ := by
  obtain ⟨x, hx, hadj⟩ := hc.ne₂
  have hx' := hc.sing₂ x hx hadj
  rw [hx'] at hadj
  exact hadj

theorem not_adj_p₁_a₂ : ¬ G.Adj p₁ hc.a₂ := fun hadj =>
  a₂_not_mem_star₁ hc (first_adj_mem hc.ctx (a₂_mem_K hc) hadj)

theorem not_adj_p₂_a₁ : ¬ G.Adj p₂ hc.a₁ := fun hadj =>
  a₁_not_mem_star₂ hc (last_adj_mem hc.ctx (a₁_mem_K hc) hadj)

/-! ## Parity of the branch and of the rung -/

/-- PAPER: *"Since `H` is bipartite, and there is a 2-edge track of `H` between `v₁, v₂` (via
`w`), it follows that the branch of `H` with ends `v₁, v₂` has even length."* -/
theorem even_trackLength : Even (trackLength q) := by
  obtain ⟨col⟩ :=
    BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hc.ctx.ready.2.2.1.2
  have htwo : IsTrackFrom H [c₁, w, c₂] c₁ c₂ := by
    refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
    · simp [hc.adjw₁.ne, stars_ne' hc, hc.adjw₂.ne']
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · simpa using hc.adjw₁
      · simpa using hc.adjw₂.symm
  have hlen2 : trackLength [c₁, w, c₂] = 2 := by simp [trackLength]
  have h2 : Even (trackLength [c₁, w, c₂]) := by rw [hlen2]; exact ⟨1, rfl⟩
  have hcol := (BipartiteClosedWalkEven.even_trackLength_iff col htwo).mp h2
  exact (BipartiteClosedWalkEven.even_trackLength_iff col hc.from').mpr hcol

theorem three_le_q : 3 ≤ q.length := by
  have h := even_trackLength hc
  have h2 := hc.len2
  simp only [trackLength] at h
  rcases h with ⟨k, hk⟩
  omega

/-- The rung has one vertex per edge of the branch. -/
theorem R_length : R.length = trackLength q := by
  classical
  have hq2 : 2 ≤ q.length := hc.len2
  have hpath : IsPathList G (trackRung φ q hc.branch.1) :=
    trackRung_isPathList φ q hc.branch.1 (by simp only [trackLength]; omega)
  have hset : R.toFinset = (trackRung φ q hc.branch.1).toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      have hx' : x ∈ edgeImage φ (trackEdges q) := by
        rw [← hc.rungSet]; exact hx
      obtain ⟨e, he, heq, rfl⟩ := hx'
      exact (mem_trackRung_iff φ hc.branch.1).mpr ⟨e, he, heq, rfl⟩
    · intro hx
      obtain ⟨e, he, heq, rfl⟩ := (mem_trackRung_iff φ hc.branch.1).mp hx
      have : (φ ⟨e, he⟩ : V) ∈ edgeImage φ (trackEdges q) := ⟨e, he, heq, rfl⟩
      have h2 : (φ ⟨e, he⟩ : V) ∈ {x : V | x ∈ R} := by rw [hc.rungSet]; exact this
      exact h2
  have h1 : R.toFinset.card = R.length := List.toFinset_card_of_nodup hc.rung.1.2.1
  have h2 : (trackRung φ q hc.branch.1).toFinset.card = (trackRung φ q hc.branch.1).length :=
    List.toFinset_card_of_nodup hpath.2.1
  rw [← h1, hset, h2, trackRung_length]

/-- PAPER: *"and therefore `R_{v₁v₂}` has odd length, and in particular `r₁ ≠ r₂`"*.  The
number of vertices of the rung is even, so its length as a path is odd. -/
theorem even_R_length : Even R.length := by
  rw [R_length hc]; exact even_trackLength hc

theorem two_le_R_length : 2 ≤ R.length := by
  have := three_le_q hc
  rw [R_length hc]
  simp only [trackLength]
  omega

theorem r_ne : r₁ ≠ r₂ :=
  PathBasics.isPathFrom_ends_ne hc.rung (by
    have := two_le_R_length hc
    simp only [pathLength]
    omega)

theorem r₁_mem_R : r₁ ∈ R := by
  have : r₁ ∈ N c₁ ∩ {y : V | y ∈ R} := by rw [hc.int₁]; rfl
  exact this.2

theorem r₂_mem_R : r₂ ∈ R := by
  have : r₂ ∈ N c₂ ∩ {y : V | y ∈ R} := by rw [hc.int₂]; rfl
  exact this.2

theorem r₁_mem_star₁ : r₁ ∈ N c₁ := by
  have : r₁ ∈ N c₁ ∩ {y : V | y ∈ R} := by rw [hc.int₁]; rfl
  exact this.1

theorem r₂_mem_star₂ : r₂ ∈ N c₂ := by
  have : r₂ ∈ N c₂ ∩ {y : V | y ∈ R} := by rw [hc.int₂]; rfl
  exact this.1

/-- PAPER: *"Since `r₁ ∉ N_{v₂}`"*. -/
theorem r₁_not_mem_star₂ : r₁ ∉ N c₂ := by
  intro hmem
  have : r₁ ∈ N c₂ ∩ {y : V | y ∈ R} := ⟨hmem, r₁_mem_R hc⟩
  rw [hc.int₂] at this
  exact r_ne hc this

theorem r₂_not_mem_star₁ : r₂ ∉ N c₁ := by
  intro hmem
  have : r₂ ∈ N c₁ ∩ {y : V | y ∈ R} := ⟨hmem, r₂_mem_R hc⟩
  rw [hc.int₁] at this
  exact (r_ne hc) this.symm

theorem r₁_ne_a₁ : r₁ ≠ hc.a₁ := fun hcon => a₁_not_mem_R hc (hcon ▸ r₁_mem_R hc)

/-! ## The hole through `a₁` and `a₂` -/

/-- PAPER: *"the hole `p₁-⋯-pₙ-a₂-a₁-p₁`"*: the two attachment vertices complete the outside
path to a hole. -/
theorem completion_a : Completion G K (N c₁ ∩ N c₂) p₁ p₂ [hc.a₁, hc.a₂] hc.a₁ hc.a₂ := by
  refine ⟨⟨PathBasics.isPathList_pair (a_adj hc), rfl, rfl⟩, ?_, adj_p₁_a₁ hc, adj_p₂_a₂ hc,
    ?_, ?_, ?_, a_ne hc⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact a₁_mem_K hc
    · rw [List.mem_singleton.mp hx]; exact a₂_mem_K hc
  · intro x hx hadj
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · rw [List.mem_singleton.mp hx] at hadj ⊢
      exact absurd hadj (not_adj_p₁_a₂ hc)
  · intro x hx hadj
    rcases List.mem_cons.mp hx with rfl | hx
    · exact absurd hadj (not_adj_p₂_a₁ hc)
    · exact List.mem_singleton.mp hx
  · intro x hx hmem
    rcases List.mem_cons.mp hx with rfl | hx
    · exact a₁_not_mem_star₂ hc hmem.2
    · rw [List.mem_singleton.mp hx] at hmem
      exact a₂_not_mem_star₁ hc hmem.1

/-- PAPER: *"Now the hole `p₁-⋯-pₙ-a₂-a₁-p₁` is even, and so `n` is even."* -/
theorem even_P_length : Even P.length := by
  have hhole : IsHoleList G ([hc.a₁, hc.a₂] ++ P.reverse) :=
    hole_of_completion hc.ctx (completion_a hc)
  have heven := (berge hc.ctx).1 _ hhole
  simp only [holeLength, List.length_append, List.length_reverse, List.length_cons,
    List.length_nil] at heven
  rcases heven with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

end Workspace.ProofLemmas.Thm58StarStarGapCoveredSetup
