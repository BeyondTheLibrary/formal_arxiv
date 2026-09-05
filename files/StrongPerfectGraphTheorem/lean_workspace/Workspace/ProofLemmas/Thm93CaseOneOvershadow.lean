import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.LineGraphDegree
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.Thm93CaseOneClassify
import Workspace.ProofLemmas.Thm93CaseOneAddTrack
import Workspace.ProofLemmas.AppearanceVertexTypeTransport
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision
import Workspace.ProofLemmas.EnlargementFromNonlocalColoring
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm93CaseOneBranchPair
import Workspace.ProofLemmas.TrackSlice

/-!
# The overshadowed appearance of case (1) of 9.3

PAPER (9.3, printed p. 49): *"If `R` has length 0 then statement 4 of the theorem holds, while
if `R` has length > 0 then it is even and there is an overshadowed appearance of `K₄` in `G`,
a contradiction."*

Here `R` is the path in `F` supplied by 5.8.2 (called `P` below), and the branch of `H` at hand
is a single edge `e = d₁d₂`, carrying the single vertex `x` of `L(H)`.  The path `P` attaches
to `N(d₁) \ x` at one end and to `N(d₂) \ x` at the other and nowhere else on `K \ x`, so
`L(H)` with the vertex `x` deleted and `V(P)` put in its place is again a line graph: it is
`L(H')`, where `H'` is `H` with the edge `e` subdivided into a track of length `|V(P)|`.  Since
`P` has even length, that track has odd length, so `H'` is again bipartite, and the track is a
branch of `H'` of odd length at least three.  Finally `x` itself is nonadjacent to at most one
edge of `H'` at each of `d₁, d₂` — namely to the first, respectively last, edge of the new
track — so the appearance `L(H')` is overshadowed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93CaseOneOvershadow

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The single vertex of a one-edge branch is the vertex carried by that edge. -/
theorem adj_of_short_branch {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) {N : Fin n → Set V}
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    {d₁ d₂ : Fin n} (hne : d₁ ≠ d₂) {x : V} (h₁ : x ∈ N d₁) (h₂ : x ∈ N d₂) :
    ∃ hadj : H.Adj d₁ d₂, (↑(phi ⟨s(d₁, d₂), hadj⟩) : V) = x := by
  rw [hN d₁] at h₁
  rw [hN d₂] at h₂
  obtain ⟨e, he, ⟨-, hd₁e⟩, hxe⟩ := h₁
  obtain ⟨f, hf, ⟨-, hd₂f⟩, hxf⟩ := h₂
  have hef : e = f := by
    have : phi ⟨e, he⟩ = phi ⟨f, hf⟩ := Subtype.ext (hxe.symm.trans hxf)
    exact congrArg Subtype.val (phi.injective this)
  subst hef
  have hpair : e = s(d₁, d₂) := (Sym2.mem_and_mem_iff hne).mp ⟨hd₁e, hd₂f⟩
  subst hpair
  exact ⟨he, hxe.symm⟩


/-- Adjacency in `G` between two vertices of the appearance is adjacency in `L(H)`. -/
theorem adj_iff {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) (a b : H.edgeSet) :
    G.Adj (↑(phi a) : V) (↑(phi b) : V) ↔ H.lineGraph.Adj a b :=
  ⟨fun h => phi.map_adj_iff.mp h, fun h => phi.map_adj_iff.mpr h⟩

/-- Two edges of `H` are adjacent in `L(H)` exactly when they are distinct and meet. -/
theorem lineGraph_adj_iff' {n : ℕ} {H : SimpleGraph (Fin n)} (a b : H.edgeSet) :
    H.lineGraph.Adj a b ↔ (a ≠ b ∧ ∃ w : Fin n, w ∈ (a : Sym2 (Fin n)) ∧ w ∈ (b : Sym2 (Fin n))) := by
  rw [← SimpleGraph.mem_neighborSet, LineGraphDegree.mem_lineGraph_neighborSet_iff]
  constructor
  · rintro ⟨h, w, h1, h2⟩; exact ⟨h.symm, w, h1, h2⟩
  · rintro ⟨h, w, h1, h2⟩; exact ⟨h.symm, w, h1, h2⟩

/-- Membership in the clique `N c` of the appearance, unfolded. -/
theorem mem_N_iff {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {phi : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (c : Fin n) (v : V) :
    v ∈ N c ↔ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c ∈ e ∧ v = (↑(phi ⟨e, he⟩) : V) := by
  rw [hN c]
  exact ⟨fun ⟨e, he, hinc, hv⟩ => ⟨e, he, hinc.2, hv⟩,
    fun ⟨e, he, hinc, hv⟩ => ⟨e, he, ⟨he, hinc⟩, hv⟩⟩

/-- **A vertex of `K` cannot be complete to `N c \ x` when `c` is a branch-vertex.**

`N c \ x` is the image of the at least two edges of `H` at `c` other than `d₁d₂`; a vertex of
`K` adjacent to all of them would be an edge of `H` containing two distinct neighbours of `c`,
so `H` would have a triangle. -/
theorem not_complete_of_mem_K {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) (col : H.Coloring (Fin 2)) {N : Fin n → Set V}
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    {c c' : Fin n} (hdeg : 3 ≤ (H.neighborSet c).ncard) (hcc' : H.Adj c c')
    {x : V} (hx : (↑(phi ⟨s(c, c'), hcc'⟩) : V) = x)
    {v : V} (hv : v ∈ K) (hvx : v ≠ x) (hall : ∀ w ∈ N c \ {x}, G.Adj v w) : False := by
  classical
  set f : H.edgeSet := phi.symm ⟨v, hv⟩ with hf
  have hphif : (↑(phi f) : V) = v := by rw [hf]; simp
  -- the image of an edge at `c` other than `cc'` lies in `N c \ x`
  have hmem : ∀ (g : Sym2 (Fin n)) (hg : g ∈ H.edgeSet), c ∈ g → g ≠ s(c, c') →
      (↑(phi ⟨g, hg⟩) : V) ∈ N c \ {x} := by
    intro g hg hcg hne
    refine ⟨(mem_N_iff hN c _).mpr ⟨g, hg, hcg, rfl⟩, ?_⟩
    intro hcon
    apply hne
    have : phi ⟨g, hg⟩ = phi ⟨s(c, c'), hcc'⟩ := Subtype.ext (by
      simpa using (show (↑(phi ⟨g, hg⟩) : V) = x from hcon).trans hx.symm)
    exact congrArg Subtype.val (phi.injective this)
  by_cases hcf : c ∈ (f : Sym2 (Fin n))
  · have hfne : (f : Sym2 (Fin n)) ≠ s(c, c') := by
      intro hcon
      apply hvx
      rw [← hphif, ← hx]
      exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext hcon)
    have := hall _ (hmem (f : Sym2 (Fin n)) f.2 hcf hfne)
    rw [Subtype.coe_eta, hphif] at this
    exact G.irrefl this
  · -- two neighbours of `c` other than `c'`
    have hnt : (H.neighborSet c \ {c'}).Nontrivial := by
      rw [← Set.one_lt_ncard_iff_nontrivial]
      have hmem' : c' ∈ H.neighborSet c := hcc'
      rw [Set.ncard_diff_singleton_of_mem hmem']
      omega
    obtain ⟨w₁, hw₁, w₂, hw₂, hw12⟩ := hnt
    have key : ∀ w : Fin n, w ∈ H.neighborSet c \ {c'} → w ∈ (f : Sym2 (Fin n)) := by
      intro w hw
      have hadjw : H.Adj c w := hw.1
      have hgE : s(c, w) ∈ H.edgeSet := hadjw
      have hgne : s(c, w) ≠ s(c, c') := fun hcon => hw.2 (Sym2.congr_right.mp hcon)
      have := hall _ (hmem _ hgE (by simp) hgne)
      rw [← hphif] at this
      have hl := (lineGraph_adj_iff' _ _).mp ((adj_iff phi _ _).mp this)
      obtain ⟨-, z, hz1, hz2⟩ := hl
      have : z = c ∨ z = w := by simpa using hz2
      rcases this with rfl | rfl
      · exact absurd hz1 hcf
      · exact hz1
    have hfeq : (f : Sym2 (Fin n)) = s(w₁, w₂) :=
      (Sym2.mem_and_mem_iff hw12).mp ⟨key w₁ hw₁, key w₂ hw₂⟩
    have hadj12 : H.Adj w₁ w₂ := by have := f.2; rwa [hfeq] at this
    have c1 : col c ≠ col w₁ := col.valid hw₁.1
    have c2 : col c ≠ col w₂ := col.valid hw₂.1
    have c3 : col w₁ ≠ col w₂ := col.valid hadj12
    have hfin : ∀ a b d : Fin 2, a ≠ b → a ≠ d → b ≠ d → False := by decide
    exact hfin _ _ _ c1 c2 c3


/-- Every vertex of `K` has two distinct neighbours in `K`. -/
theorem two_neighbours_in_K {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) (hdeg2 : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard)
    (v : V) (hv : v ∈ K) :
    ∃ y₁ y₂ : V, y₁ ∈ K ∧ y₂ ∈ K ∧ G.Adj v y₁ ∧ G.Adj v y₂ ∧ y₁ ≠ y₂ := by
  classical
  have hother : ∀ w z : Fin n, H.Adj w z → ∃ t : Fin n, H.Adj w t ∧ t ≠ z := by
    intro w z hwz
    have hnt : (H.neighborSet w \ {z}).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]
      have hmem' : z ∈ H.neighborSet w := hwz
      rw [Set.ncard_diff_singleton_of_mem hmem']
      have := hdeg2 w; omega
    obtain ⟨t, ht⟩ := hnt
    exact ⟨t, ht.1, ht.2⟩
  set f : H.edgeSet := phi.symm ⟨v, hv⟩ with hf
  have hphif : (↑(phi f) : V) = v := by rw [hf]; simp
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin n, (f : Sym2 (Fin n)) = s(a, b) := by
    induction (f : Sym2 (Fin n)) using Sym2.ind with
    | _ a b => exact ⟨a, b, rfl⟩
  have habE : H.Adj a b := by have := f.2; rwa [hab] at this
  obtain ⟨c, hac, hcb⟩ := hother a b habE
  obtain ⟨c', hbc', hc'a⟩ := hother b a habE.symm
  have hg₁ : s(a, c) ∈ H.edgeSet := hac
  have hg₂ : s(b, c') ∈ H.edgeSet := hbc'
  have hne₁ : (⟨s(a, c), hg₁⟩ : H.edgeSet) ≠ f := by
    intro hcon
    have : s(a, c) = s(a, b) := by rw [← hab]; exact congrArg Subtype.val hcon
    exact hcb (Sym2.congr_right.mp this)
  have hne₂ : (⟨s(b, c'), hg₂⟩ : H.edgeSet) ≠ f := by
    intro hcon
    have h' : s(b, c') = s(a, b) := by rw [← hab]; exact congrArg Subtype.val hcon
    rcases Sym2.eq_iff.mp h' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact habE.ne h1.symm
    · exact hc'a h2
  have hne₁₂ : (⟨s(a, c), hg₁⟩ : H.edgeSet) ≠ ⟨s(b, c'), hg₂⟩ := by
    intro hcon
    have h' : s(a, c) = s(b, c') := congrArg Subtype.val hcon
    rcases Sym2.eq_iff.mp h' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact habE.ne h1
    · exact hcb h2
  refine ⟨↑(phi ⟨s(a, c), hg₁⟩), ↑(phi ⟨s(b, c'), hg₂⟩), (phi _).2, (phi _).2, ?_, ?_, ?_⟩
  · rw [← hphif]
    exact (adj_iff phi _ _).mpr ((lineGraph_adj_iff' _ _).mpr
      ⟨hne₁.symm, a, by rw [hab]; simp, by simp⟩)
  · rw [← hphif]
    exact (adj_iff phi _ _).mpr ((lineGraph_adj_iff' _ _).mpr
      ⟨hne₂.symm, b, by rw [hab]; simp, by simp⟩)
  · intro hcon
    exact hne₁₂ (phi.injective (Subtype.ext hcon))

/-- **The path supplied by 5.8.2 is disjoint from the appearance.** -/
theorem path_off_appearance {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) (col : H.Coloring (Fin 2))
    (hdeg2 : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard) {N : Fin n → Set V}
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    {d₁ d₂ : Fin n} (hdeg₁ : 3 ≤ (H.neighborSet d₁).ncard)
    (hdeg₂ : 3 ≤ (H.neighborSet d₂).ncard) (hadj : H.Adj d₁ d₂)
    {x : V} (hx : (↑(phi ⟨s(d₁, d₂), hadj⟩) : V) = x)
    {P : List V} {p₁ p₂ : V} (hp : p₁ ≠ p₂)
    (hfirst : ∀ v ∈ N d₁ \ {x}, G.Adj p₁ v) (hlast : ∀ v ∈ N d₂ \ {x}, G.Adj p₂ v)
    (hno : ∀ u ∈ P, ∀ v ∈ K, v ≠ x → G.Adj u v →
      (u = p₁ ∧ v ∈ N d₁ \ {x}) ∨ (u = p₂ ∧ v ∈ N d₂ \ {x})) :
    ∀ u ∈ P, u ∉ K := by
  classical
  -- the two cliques meet exactly in `x`
  have hinter : ∀ v : V, v ∈ N d₁ → v ∈ N d₂ → v = x := by
    intro v h1 h2
    obtain ⟨g, hg, hd₁g, hvg⟩ := (mem_N_iff hN d₁ v).mp h1
    obtain ⟨g', hg', hd₂g', hvg'⟩ := (mem_N_iff hN d₂ v).mp h2
    have : g = g' := congrArg Subtype.val (phi.injective (Subtype.ext (hvg.symm.trans hvg')))
    subst this
    have : g = s(d₁, d₂) := (Sym2.mem_and_mem_iff hadj.ne).mp ⟨hd₁g, hd₂g'⟩
    subst this
    rw [hvg, ← hx]
  -- each clique has a vertex other than `x`, and `x` is adjacent to it
  have hexists : ∀ (c c' : Fin n) (hcc' : H.Adj c c'), 3 ≤ (H.neighborSet c).ncard →
      (↑(phi ⟨s(c, c'), hcc'⟩) : V) = x → ∃ v ∈ N c \ {x}, G.Adj x v := by
    intro c c' hcc' hdc hxc
    have hnt : (H.neighborSet c \ {c'}).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]
      have hmem' : c' ∈ H.neighborSet c := hcc'
      rw [Set.ncard_diff_singleton_of_mem hmem']
      omega
    obtain ⟨t, ht⟩ := hnt
    have hgE : s(c, t) ∈ H.edgeSet := ht.1
    have hgne : (⟨s(c, t), hgE⟩ : H.edgeSet) ≠ ⟨s(c, c'), hcc'⟩ := by
      intro hcon
      exact ht.2 (Sym2.congr_right.mp (congrArg Subtype.val hcon))
    refine ⟨↑(phi ⟨s(c, t), hgE⟩), ⟨(mem_N_iff hN c _).mpr ⟨_, hgE, by simp, rfl⟩, ?_⟩, ?_⟩
    · intro hcon
      exact hgne (phi.injective (Subtype.ext (by
        simpa using (show (↑(phi ⟨s(c, t), hgE⟩) : V) = x from hcon).trans hxc.symm)))
    · rw [← hxc]
      exact (adj_iff phi _ _).mpr ((lineGraph_adj_iff' _ _).mpr
        ⟨hgne.symm, c, by simp, by simp⟩)
  -- `x` itself is not on the path
  have hxP : x ∉ P := by
    intro hxmem
    obtain ⟨v₁, hv₁, hxv₁⟩ := hexists d₁ d₂ hadj hdeg₁ hx
    obtain ⟨v₂, hv₂, hxv₂⟩ := hexists d₂ d₁ hadj.symm hdeg₂ (by
      rw [← hx]
      exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext (Sym2.eq_swap)))
    have hv₁K : v₁ ∈ K := by
      obtain ⟨g, hg, -, hvg⟩ := (mem_N_iff hN d₁ v₁).mp hv₁.1
      rw [hvg]; exact (phi _).2
    have hv₂K : v₂ ∈ K := by
      obtain ⟨g, hg, -, hvg⟩ := (mem_N_iff hN d₂ v₂).mp hv₂.1
      rw [hvg]; exact (phi _).2
    have hv₁x : v₁ ≠ x := hv₁.2
    have hv₂x : v₂ ≠ x := hv₂.2
    have e₁ := hno x hxmem v₁ hv₁K hv₁x hxv₁
    have e₂ := hno x hxmem v₂ hv₂K hv₂x hxv₂
    have hx₁ : x = p₁ := by
      rcases e₁ with ⟨h, -⟩ | ⟨-, hm⟩
      · exact h
      · exact absurd (hinter v₁ hv₁.1 hm.1) hv₁x
    have hx₂ : x = p₂ := by
      rcases e₂ with ⟨-, hm⟩ | ⟨h, -⟩
      · exact absurd (hinter v₂ hm.1 hv₂.1) hv₂x
      · exact h
    exact hp (hx₁ ▸ hx₂ ▸ rfl)
  intro u hu huK
  obtain ⟨y₁, y₂, hy₁K, hy₂K, ha₁, ha₂, hy12⟩ := two_neighbours_in_K phi hdeg2 u huK
  have : ∃ y ∈ K, y ≠ x ∧ G.Adj u y := by
    by_cases h : y₁ = x
    · exact ⟨y₂, hy₂K, fun hc => hy12 (h.trans hc.symm), ha₂⟩
    · exact ⟨y₁, hy₁K, h, ha₁⟩
  obtain ⟨y, hyK, hyx, hadjy⟩ := this
  rcases hno u hu y hyK hyx hadjy with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact not_complete_of_mem_K phi col hN hdeg₁ hadj hx huK (fun hc => hxP (by rw [← hc]; exact hu)) hfirst
  · refine not_complete_of_mem_K phi col hN hdeg₂ hadj.symm ?_ huK
      (fun hc => hxP (by rw [← hc]; exact hu)) hlast
    rw [← hx]
    exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext (Sym2.eq_swap))


/-! ### Deleting the short branch from the appearance -/

/-- **Deleting one edge of `H` deletes the vertex it carries from `L(H)`.** -/
theorem deleted_iso {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) {d₁ d₂ : Fin n} (hadj : H.Adj d₁ d₂)
    {x : V} (hx : (↑(phi ⟨s(d₁, d₂), hadj⟩) : V) = x) :
    ∃ phi₀ : (H.deleteEdges {s(d₁, d₂)}).lineGraph ≃g G.induce (K \ {x}),
      ∀ (e : Sym2 (Fin n)) (he : e ∈ (H.deleteEdges {s(d₁, d₂)}).edgeSet)
        (he' : e ∈ H.edgeSet), (↑(phi₀ ⟨e, he⟩) : V) = (↑(phi ⟨e, he'⟩) : V) := by
  classical
  set H₀ : SimpleGraph (Fin n) := H.deleteEdges {s(d₁, d₂)} with hH₀
  have hsub : ∀ {e : Sym2 (Fin n)}, e ∈ H₀.edgeSet → e ∈ H.edgeSet := by
    intro e he
    rw [hH₀, SimpleGraph.edgeSet_deleteEdges] at he
    exact he.1
  have hne : ∀ {e : Sym2 (Fin n)}, e ∈ H₀.edgeSet → e ≠ s(d₁, d₂) := by
    intro e he
    rw [hH₀, SimpleGraph.edgeSet_deleteEdges] at he
    intro hcon
    exact he.2 (by rw [hcon]; rfl)
  have hvne : ∀ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet),
      (↑(phi ⟨e, hsub he⟩) : V) ≠ x := by
    intro e he hcon
    have hEq : (⟨e, hsub he⟩ : H.edgeSet) = ⟨s(d₁, d₂), hadj⟩ :=
      phi.injective (Subtype.ext (by simpa using hcon.trans hx.symm))
    exact hne he (congrArg Subtype.val hEq)
  let f : H₀.edgeSet → (K \ {x} : Set V) :=
    fun e => ⟨(↑(phi ⟨(e : Sym2 (Fin n)), hsub e.2⟩) : V),
      ⟨(phi ⟨(e : Sym2 (Fin n)), hsub e.2⟩).2, hvne _ e.2⟩⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (↑(phi ⟨(a : Sym2 (Fin n)), hsub a.2⟩) : V)
        = (↑(phi ⟨(b : Sym2 (Fin n)), hsub b.2⟩) : V) :=
      congrArg (fun t : (K \ {x} : Set V) => (t : V)) hab
    have h2 : (⟨(a : Sym2 (Fin n)), hsub a.2⟩ : H.edgeSet)
        = ⟨(b : Sym2 (Fin n)), hsub b.2⟩ := phi.injective (Subtype.ext this)
    exact Subtype.ext (congrArg (fun t : H.edgeSet => (t : Sym2 (Fin n))) h2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv, hvx⟩
    obtain ⟨g, hg⟩ := phi.surjective ⟨v, hv⟩
    have hgval : (↑(phi g) : V) = v := congrArg Subtype.val hg
    have hgne : (g : Sym2 (Fin n)) ≠ s(d₁, d₂) := by
      intro hcon
      apply hvx
      rw [← hgval, ← hx]
      exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext hcon)
    have hgmem : (g : Sym2 (Fin n)) ∈ H₀.edgeSet := by
      rw [hH₀, SimpleGraph.edgeSet_deleteEdges]
      exact ⟨g.2, by simpa using hgne⟩
    refine ⟨⟨(g : Sym2 (Fin n)), hgmem⟩, ?_⟩
    apply Subtype.ext
    show (↑(phi ⟨(g : Sym2 (Fin n)), hsub hgmem⟩) : V) = v
    rw [Subtype.coe_eta, hgval]
  refine ⟨⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩, ?_⟩
  · intro a b
    show (G.induce (K \ {x})).Adj (f a) (f b) ↔ H₀.lineGraph.Adj a b
    show G.Adj (↑(phi ⟨(a : Sym2 (Fin n)), hsub a.2⟩) : V)
        (↑(phi ⟨(b : Sym2 (Fin n)), hsub b.2⟩) : V) ↔ H₀.lineGraph.Adj a b
    rw [adj_iff phi, lineGraph_adj_iff', lineGraph_adj_iff']
    constructor
    · rintro ⟨hne', w, h1, h2⟩
      refine ⟨fun hcon => hne' (Subtype.ext ?_), w, h1, h2⟩
      exact (show (a : Sym2 (Fin n)) = (b : Sym2 (Fin n)) from congrArg Subtype.val hcon)
    · rintro ⟨hne', w, h1, h2⟩
      refine ⟨fun hcon => hne' (Subtype.ext ?_), w, h1, h2⟩
      exact (show (a : Sym2 (Fin n)) = (b : Sym2 (Fin n)) from
        congrArg (fun t : H.edgeSet => (t : Sym2 (Fin n))) hcon)
  · intro e he he'
    show (↑(phi ⟨e, hsub he⟩) : V) = (↑(phi ⟨e, he'⟩) : V)
    rfl



/-! ### The subdivision after deleting the short branch -/

/-- **Deleting a branch that is a single edge leaves a subdivision of `K₄` minus that edge.**

The track of the skeleton edge `ab` carrying the deleted edge is `[d₁, d₂]` itself, so every
other track survives untouched. -/
theorem short_branch_subData {n : ℕ} {H : SimpleGraph (Fin n)}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    {d₁ d₂ : Fin n} (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hadj : H.Adj d₁ d₂) :
    ∃ (a b : Fin 4) (ι : Fin 4 → Fin n) (T : Fin 4 → Fin 4 → List (Fin n)),
      a ≠ b ∧ ι a = d₁ ∧ ι b = d₂ ∧
      Workspace.ProofLemmas.NoCrossTrackBranch.SubData
        ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)})
        (H.deleteEdges {s(d₁, d₂)}) ι T := by
  classical
  obtain ⟨ι, T, hs⟩ := Workspace.ProofLemmas.NoCrossTrackBranch.exists_subData hsub
  have hrange : branchVertices H = Set.range ι :=
    Workspace.ProofLemmas.NoCrossTrackBranch.branch_eq_range
      Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected hs
  obtain ⟨a, ha⟩ : ∃ a, ι a = d₁ := by rw [hrange] at hd₁; exact hd₁
  obtain ⟨b, hb⟩ : ∃ b, ι b = d₂ := by rw [hrange] at hd₂; exact hd₂
  have hab : a ≠ b := by
    intro h
    exact hadj.ne (by rw [← ha, ← hb, h])
  -- the ends of an old track containing the edge `d₁d₂` are `d₁` and `d₂`
  have hkey : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
      s(d₁, d₂) ∈ trackEdges (T u v) → s(u, v) = s(a, b) := by
    intro u v huv hmem
    obtain ⟨h1, h2⟩ := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem
    have hend : ∀ z : Fin 4, ι z ∈ T u v → z = u ∨ z = v := by
      intro z hz
      have hnotint : ι z ∉ trackInterior (T u v) := fun hc => hs.new u v huv _ hc ⟨z, rfl⟩
      rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
        (hs.track u v huv).2.1 (hs.track u v huv).2.2 hz hnotint with h | h
      · exact Or.inl (hs.inj h)
      · exact Or.inr (hs.inj h)
    have hA := hend a (by rw [ha]; exact h1)
    have hB := hend b (by rw [hb]; exact h2)
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hab
  -- the track of `ab` is the single edge `d₁d₂`
  have hTab : T a b = [d₁, d₂] := by
    have hadjE : s(d₁, d₂) ∈ H.edgeSet := hadj
    rw [hs.edges] at hadjE
    simp only [Set.mem_iUnion] at hadjE
    obtain ⟨u, v, huv, hmem⟩ := hadjE
    have hsuv := hkey u v huv hmem
    have hmem' : s(d₁, d₂) ∈ trackEdges (T a b) := by
      rcases Sym2.eq_iff.mp hsuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmem
      · rw [hs.rev _ _ huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
        exact hmem
    have hABadj : (⊤ : SimpleGraph (Fin 4)).Adj a b := hab
    have htr := hs.track a b hABadj
    have hint : ∀ z : Fin n, z ∈ Set.range ι → z ∉ trackInterior (T a b) :=
      fun z hz hc => hs.new a b hABadj z hc hz
    have hlen : (T a b).length = 2 :=
      Workspace.ProofLemmas.Thm93CaseOneBranchPair.length_eq_two_of_ends_adjacent
        htr.1.2.1 (by rw [← ha]; exact List.mem_of_mem_head? htr.2.1)
        (by rw [← hb]; exact List.mem_of_getLast? htr.2.2)
        (fun hc => hint d₁ ⟨a, ha⟩ hc) (fun hc => hint d₂ ⟨b, hb⟩ hc) hmem'
    obtain ⟨p, r, hpr⟩ := List.length_eq_two.mp hlen
    have hp : p = d₁ := by
      have h := htr.2.1
      rw [hpr] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      rw [h, ha]
    have hr : r = d₂ := by
      have h := htr.2.2
      rw [hpr] at h
      simp at h
      rw [h, hb]
    rw [hpr, hp, hr]
  have hABadj : (⊤ : SimpleGraph (Fin 4)).Adj a b := hab
  -- the track of any skeleton edge equal to `ab` is that single edge
  have hTuv : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v → s(u, v) = s(a, b) →
      T u v = [d₁, d₂] ∨ T u v = [d₂, d₁] := by
    intro u v huv hsuv
    rcases Sym2.eq_iff.mp hsuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [show T u v = T a b by rw [h1, h2]]; exact hTab)
    · refine Or.inr ?_
      rw [show T u v = T b a by rw [h1, h2], hs.rev a b hABadj, hTab]
      rfl
  refine ⟨a, b, ι, T, hab, ha, hb, ?_⟩
  -- the deleted edge lies on no surviving track
  have hBle : ∀ u v : Fin 4, ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}).Adj u v →
      (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v h
    exact (SimpleGraph.deleteEdges_adj.mp h).1
  have hnotmem : ∀ u v : Fin 4, ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}).Adj u v →
      s(d₁, d₂) ∉ trackEdges (T u v) := by
    intro u v huv hmem
    have h := SimpleGraph.deleteEdges_adj.mp huv
    exact h.2 (by rw [hkey u v h.1 hmem]; rfl)
  have hedgeNe : ∀ u v : Fin 4, ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}).Adj u v →
      ∀ e ∈ trackEdges (T u v), e ≠ s(d₁, d₂) := by
    intro u v huv e he hcon
    exact hnotmem u v huv (by rw [← hcon]; exact he)
  refine ⟨hs.inj, ?_, fun u v h => hs.len u v (hBle u v h),
    fun u v h => hs.rev u v (hBle u v h),
    fun u v u' v' h h' hne => hs.disj u v u' v' (hBle u v h) (hBle u' v' h') hne,
    fun u v h => hs.new u v (hBle u v h), ?_, ?_⟩
  · -- tracks
    intro u v huv
    have htr := hs.track u v (hBle u v huv)
    refine ⟨⟨htr.1.1, htr.1.2.1, ?_⟩, htr.2.1, htr.2.2⟩
    intro i hi
    have hadji := htr.1.2.2 i hi
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hadji, by
      have : s((T u v)[i], (T u v)[i + 1]) ≠ s(d₁, d₂) :=
        hedgeNe u v huv _ ⟨i, hi, rfl⟩
      simpa using this⟩
  · -- cover
    intro t
    rcases hs.cover t with h | ⟨u, v, huv, hint⟩
    · exact Or.inl h
    · by_cases hsuv : s(u, v) = s(a, b)
      · exfalso
        rcases hTuv u v huv hsuv with h | h <;> rw [h] at hint <;>
          simp [trackInterior] at hint
      · refine Or.inr ⟨u, v, ?_, hint⟩
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using hsuv⟩
  · -- edge set
    ext e
    rw [SimpleGraph.edgeSet_deleteEdges]
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨he, hne⟩
      rw [hs.edges] at he
      simp only [Set.mem_iUnion] at he
      obtain ⟨u, v, huv, hmem⟩ := he
      by_cases hsuv : s(u, v) = s(a, b)
      · exfalso
        apply hne
        rcases hTuv u v huv hsuv with h | h <;> rw [h] at hmem <;>
          rw [Workspace.ProofLemmas.Thm93CaseOneBranchPair.trackEdges_pair] at hmem <;>
          simp only [Set.mem_singleton_iff] at hmem
        · exact hmem
        · rw [hmem, Sym2.eq_swap]
      · exact ⟨u, v, by rw [SimpleGraph.deleteEdges_adj]; exact ⟨huv, by simpa using hsuv⟩, hmem⟩
    · rintro ⟨u, v, huv, hmem⟩
      refine ⟨?_, ?_⟩
      · rw [hs.edges]
        simp only [Set.mem_iUnion]
        exact ⟨u, v, hBle u v huv, hmem⟩
      · exact hedgeNe u v huv e hmem



/-! ### Degrees in the extended host -/

section Extension

open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack

variable {W Z : Type*} {H₀ : SimpleGraph W} {D : SimpleGraph Z} {rho : W → Z}
  {qq : List Z} {c₁ c₂ : W}

/-- Adjacency in the extended host: an old edge, or an edge of the new track. -/
theorem ext_adj_iff (hext : IsBranchExtension H₀ c₁ c₂ D rho qq) (z w : Z) :
    D.Adj z w ↔ ((∃ e ∈ H₀.edgeSet, Sym2.map rho e = s(z, w)) ∨ s(z, w) ∈ trackEdges qq) := by
  constructor
  · intro h
    have hmem : s(z, w) ∈ D.edgeSet := h
    rw [hext.edges] at hmem
    rcases hmem with ⟨e, he, heq⟩ | h'
    · exact Or.inl ⟨e, he, heq⟩
    · exact Or.inr h'
  · intro h
    have : s(z, w) ∈ D.edgeSet := by
      rw [hext.edges]
      rcases h with ⟨e, he, heq⟩ | h'
      · exact Or.inl ⟨e, he, heq⟩
      · exact Or.inr h'
    exact this

/-- An internal vertex of the new track has degree at most two. -/
theorem ext_interior_degree [Finite Z] (hext : IsBranchExtension H₀ c₁ c₂ D rho qq)
    {z : Z} (hz : z ∈ trackInterior qq) : (D.neighborSet z).ncard ≤ 2 := by
  classical
  have hnd : qq.Nodup := hext.track.1.2.1
  have hzq : z ∈ qq := Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hz
  obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hzq
  have hzrange : z ∉ Set.range rho := hext.newInterior z hz
  have hsub : D.neighborSet z ⊆ {qq.getD (j + 1) z, qq.getD (j - 1) z} := by
    intro w hw
    have hadj : D.Adj z w := hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (ext_adj_iff hext z w).mp hadj with ⟨e, he, heq⟩ | ⟨i, hi, hie⟩
    · exfalso
      have hmemz : z ∈ Sym2.map rho e := by rw [heq]; exact Sym2.mem_mk_left _ _
      obtain ⟨u, -, hu⟩ := Sym2.mem_map.mp hmemz
      exact hzrange ⟨u, hu⟩
    · rcases Sym2.eq_iff.mp hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hij : j = i := hnd.getElem_inj_iff.mp (hjz.trans h1)
        left
        rw [List.getD_eq_getElem qq z (by omega), h2]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq qq
          (by omega) _ _
      · have hij : j = i + 1 := hnd.getElem_inj_iff.mp (hjz.trans h1)
        right
        rw [List.getD_eq_getElem qq z (by omega), h2]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq qq
          (by omega) _ _
  calc (D.neighborSet z).ncard
      ≤ ({qq.getD (j + 1) z, qq.getD (j - 1) z} : Set Z).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp [Set.ncard_singleton]

/-- An end of the new track keeps its old neighbours and gains a new one. -/
theorem ext_end_degree [Finite W] [Finite Z] (hext : IsBranchExtension H₀ c₁ c₂ D rho qq)
    (h2 : 2 ≤ (H₀.neighborSet c₁).ncard) (hlen : 3 ≤ qq.length) :
    3 ≤ (D.neighborSet (rho c₁)).ncard := by
  classical
  have hnt : (H₀.neighborSet c₁).Nontrivial := by
    rw [← Set.one_lt_ncard_iff_nontrivial]; omega
  obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := hnt
  have hz : qq[1]'(by omega) ∈ trackInterior qq :=
    Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem qq 0 (by omega)
  have hznew : qq[1]'(by omega) ∉ Set.range rho := hext.newInterior _ hz
  have hhead : qq[0]'(by omega) = rho c₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  have hadjnew : D.Adj (rho c₁) (qq[1]'(by omega)) := by
    have := hext.track.1.2.2 0 (by omega)
    rwa [hhead] at this
  have hsub : ({rho u₁, rho u₂, qq[1]'(by omega)} : Set Z) ⊆ D.neighborSet (rho c₁) := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact hext.oldAdj _ _ hu₁
    · exact hext.oldAdj _ _ hu₂
    · exact hadjnew
  have hcard : ({rho u₁, rho u₂, qq[1]'(by omega)} : Set Z).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨rho u₁, rho u₂, qq[1]'(by omega), fun h => h12 (hext.inj h),
      fun h => hznew ⟨u₁, h⟩, fun h => hznew ⟨u₂, h⟩, rfl⟩
  calc (3 : ℕ) = ({rho u₁, rho u₂, qq[1]'(by omega)} : Set Z).ncard := hcard.symm
    _ ≤ (D.neighborSet (rho c₁)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

end Extension



/-- The set of edges at a vertex that a fixed vertex of `G` misses transports along `θ`. -/
theorem transport_subsingleton {G : SimpleGraph V} {α β : Type*} {D : SimpleGraph α}
    {D' : SimpleGraph β} (θ : D ≃g D') {K : Set V} (psi : D.lineGraph ≃g G.induce K)
    {v : V} {c : α}
    (hc : (incidentEdges D c \
      {e : Sym2 α | ∃ he : e ∈ D.edgeSet, G.Adj v (↑(psi ⟨e, he⟩) : V)}).Subsingleton) :
    (incidentEdges D' (θ c) \
      {e : Sym2 β | ∃ he : e ∈ D'.edgeSet,
        G.Adj v (↑(((Thm75Claim2Transport.lineGraphIso θ).symm.trans psi) ⟨e, he⟩) : V)}
      ).Subsingleton := by
  classical
  have hpull : ∀ f : Sym2 β, f ∈ incidentEdges D' (θ c) →
      (f ∉ {e : Sym2 β | ∃ he : e ∈ D'.edgeSet,
        G.Adj v (↑(((Thm75Claim2Transport.lineGraphIso θ).symm.trans psi) ⟨e, he⟩) : V)}) →
      Sym2.map θ.symm f ∈ incidentEdges D c \
        {e : Sym2 α | ∃ he : e ∈ D.edgeSet, G.Adj v (↑(psi ⟨e, he⟩) : V)} := by
    intro f hf hf'
    have hfeq : Sym2.map θ (Sym2.map (⇑θ.symm) f) = f :=
      Thm75Claim2Transport.sym2_map_symm' θ f
    have hmem : Sym2.map (⇑θ.symm) f ∈ incidentEdges D c := by
      rw [← Thm75Claim2Transport.mem_incidentEdges_map θ c (Sym2.map (⇑θ.symm) f), hfeq]
      exact hf
    refine ⟨hmem, ?_⟩
    rintro ⟨he, hadj⟩
    apply hf'
    refine ⟨by rw [← hfeq]; exact Thm75Claim2Transport.map_mem_edgeSet θ _ he, ?_⟩
    have hbridge := Thm75Claim2Transport.phi_bridge θ psi (Sym2.map (⇑θ.symm) f) he
    have : (↑(((Thm75Claim2Transport.lineGraphIso θ).symm.trans psi)
        ⟨Sym2.map θ (Sym2.map (⇑θ.symm) f),
          Thm75Claim2Transport.map_mem_edgeSet θ _ he⟩) : V)
        = (↑(psi ⟨Sym2.map (⇑θ.symm) f, he⟩) : V) := hbridge
    simp only [hfeq] at this
    rw [this]
    exact hadj
  intro f hf g hg
  have h1 := hpull f hf.1 hf.2
  have h2 := hpull g hg.1 hg.2
  have := hc h1 h2
  have hf' : Sym2.map θ (Sym2.map (⇑θ.symm) f) = f := Thm75Claim2Transport.sym2_map_symm' θ f
  have hg' : Sym2.map θ (Sym2.map (⇑θ.symm) g) = g := Thm75Claim2Transport.sym2_map_symm' θ g
  rw [← hf', ← hg', this]

/-- A branch extension read from the other end. -/
theorem ext_symm {W Z : Type*} {H₀ : SimpleGraph W} {D : SimpleGraph Z} {rho : W → Z}
    {qq : List Z} {c₁ c₂ : W} (hext : IsBranchExtension H₀ c₁ c₂ D rho qq) :
    IsBranchExtension H₀ c₂ c₁ D rho qq.reverse where
  inj := hext.inj
  oldAdj := hext.oldAdj
  track := Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hext.track
  length := by simpa using hext.length
  newInterior := by
    intro z hz
    rw [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse] at hz
    exact hext.newInterior z hz
  cover := by
    intro z
    rcases hext.cover z with h | h
    · exact Or.inl h
    · exact Or.inr (by
        rw [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse]
        exact h)
  edges := by
    rw [hext.edges, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]

/-- **The deleted vertex sees all but one of the edges at an end of the new branch.**

The old edges of `D` at `c` are the edges of `H` at `c` other than `cc'`, and each of them
meets `cc'`, so the vertex `x` carried by `cc'` is adjacent in `G` to each of them.  The only
other edge of `D` at `c` is the first edge of the new track. -/
theorem miss_subsingleton {n m : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) {H₀ : SimpleGraph (Fin n)}
    (hH₀ : ∀ e : Sym2 (Fin n), e ∈ H₀.edgeSet → e ∈ H.edgeSet)
    {c c' : Fin n} (hcc' : H.Adj c c') {x : V}
    (hx : (↑(phi ⟨s(c, c'), hcc'⟩) : V) = x)
    (hnotin : s(c, c') ∉ H₀.edgeSet)
    {D : SimpleGraph (Fin n ⊕ Fin m)} {qq : List (Fin n ⊕ Fin m)} {c₂ : Fin n}
    (hext : IsBranchExtension H₀ c c₂ D Sum.inl qq)
    {K' : Set V} (psi : D.lineGraph ≃g G.induce K')
    (hcompat : ∀ (e : Sym2 (Fin n)) (he₀ : e ∈ H₀.edgeSet)
      (hd : Sym2.map (@Sum.inl (Fin n) (Fin m)) e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map (@Sum.inl (Fin n) (Fin m)) e, hd⟩) : V)
        = (↑(phi ⟨e, hH₀ e he₀⟩) : V)) :
    (incidentEdges D (Sum.inl c) \
      {f : Sym2 (Fin n ⊕ Fin m) | ∃ hf : f ∈ D.edgeSet,
        G.Adj x (↑(psi ⟨f, hf⟩) : V)}).Subsingleton := by
  classical
  have hlen2 : 2 ≤ qq.length := hext.length
  have hhead : qq[0]'(by omega) = Sum.inl c :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  refine Set.subsingleton_of_subset_singleton
    (a := s(qq[0]'(by omega), qq[1]'(by omega))) ?_
  intro f hf
  have hfD : f ∈ D.edgeSet := hf.1.1
  have hfc : Sum.inl c ∈ f := hf.1.2
  have hfE := hfD
  rw [hext.edges] at hfE
  rcases hfE with ⟨e, he, rfl⟩ | ⟨i, hi, rfl⟩
  · exfalso
    apply hf.2
    obtain ⟨u, hu, hueq⟩ := Sym2.mem_map.mp hfc
    have huc : u = c := Sum.inl_injective hueq
    subst huc
    have hene : e ≠ s(u, c') := by
      intro hcon
      exact hnotin (by rw [← hcon]; exact he)
    refine ⟨hfD, ?_⟩
    rw [hcompat e he hfD, ← hx]
    exact (adj_iff phi _ _).mpr ((lineGraph_adj_iff' _ _).mpr
      ⟨fun hcon => hene (congrArg Subtype.val hcon).symm, u, by simp, hu⟩)
  · have hi0 : i = 0 := by
      have hnd : qq.Nodup := hext.track.1.2.1
      rcases Sym2.mem_iff.mp hfc with h | h
      · exact (hnd.getElem_inj_iff.mp (h.symm.trans hhead.symm) : i = 0)
      · exfalso
        have : i + 1 = 0 := hnd.getElem_inj_iff.mp (h.symm.trans hhead.symm)
        omega
    subst hi0
    rfl


/-! ### Transporting an overshadowed appearance along an isomorphism of the host -/

/-- Overshadowing is a property of the appearance, not of the vertex type of the host. -/
theorem overshadowed_map {G : SimpleGraph V} {α β : Type*} {D : SimpleGraph α}
    {D' : SimpleGraph β} (θ : D ≃g D') {K : Set V} (psi : D.lineGraph ≃g G.induce K)
    (h : IsOvershadowedAppearance G D K psi) :
    IsOvershadowedAppearance G D' K ((Thm75Claim2Transport.lineGraphIso θ).symm.trans psi) := by
  classical
  obtain ⟨B, b₁, b₂, hbranch, htrack, hodd, hlong, v, hv₁, hv₂⟩ := h
  have hlen : trackLength (B.map θ) = trackLength B := by
    simp [trackLength]
  refine ⟨B.map θ, θ b₁, θ b₂, Thm75Claim2Transport.isBranch_map θ hbranch,
    ⟨Thm75Claim2Transport.isTrackList_map θ htrack.1, ?_, ?_⟩,
    by rwa [hlen], by rwa [hlen], v, ?_, ?_⟩
  · simp only [List.head?_map, htrack.2.1, Option.map_some]
  · simp only [List.getLast?_map, htrack.2.2, Option.map_some]
  · exact transport_subsingleton θ psi hv₁
  · exact transport_subsingleton θ psi hv₂



/-! ### The construction -/

/-- **The even attachment path of case (1) of 9.3 yields an overshadowed appearance.**

PAPER (9.3, printed p. 49): *"If `R` has length 0 then statement 4 of the theorem holds, while
if `R` has length > 0 then it is even and there is an overshadowed appearance of `K₄` in `G`,
a contradiction."* -/
theorem overshadowed (G : SimpleGraph V) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (x : V)
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hqt : IsTrackFrom H q d₁ d₂)
    (hRset : {v | v ∈ R} = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (hR₁ : N d₁ ∩ {v | v ∈ R} = {x}) (hR₂ : N d₂ ∩ {v | v ∈ R} = {x})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hne : p₁ ≠ p₂)
    (hfirst : ∀ v ∈ N d₁ \ {x}, G.Adj p₁ v)
    (hlast : ∀ v ∈ N d₂ \ {x}, G.Adj p₂ v)
    (hno : ∀ u ∈ P, ∀ v ∈ K, v ≠ x → G.Adj u v →
      (u = p₁ ∧ v ∈ N d₁ \ {x}) ∨ (u = p₂ ∧ v ∈ N d₂ \ {x}))
    (heven : Even (pathLength P)) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧
        IsOvershadowedAppearance G H' K' psi := by
  classical
  ----------------------------------------------------------------------------
  -- 1.  The branch is the single edge `d₁d₂`, carrying the single vertex `x`.
  ----------------------------------------------------------------------------
  have hxR : x ∈ ({x} : Set V) := rfl
  have hx₁ : x ∈ N d₁ := by rw [← hR₁] at hxR; exact hxR.1
  have hxRmem : x ∈ {v | v ∈ R} := by rw [← hR₁] at hxR; exact hxR.2
  have hx₂ : x ∈ N d₂ := by
    have hxR' : x ∈ ({x} : Set V) := rfl
    rw [← hR₂] at hxR'
    exact hxR'.1
  have hqedge : ∃ e ∈ trackEdges q, True := by
    rw [hRset] at hxRmem
    obtain ⟨e, -, hmem, -⟩ := hxRmem
    exact ⟨e, hmem, trivial⟩
  have hqlen : 2 ≤ q.length := by
    obtain ⟨e, ⟨i, hi, -⟩, -⟩ := hqedge
    omega
  have hdne : d₁ ≠ d₂ :=
    Workspace.ProofLemmas.Thm93CaseOneClassify.ends_ne_of_two_le_length hqt hqlen
  obtain ⟨hadj, hx⟩ := adj_of_short_branch phi hN hdne hx₁ hx₂
  ----------------------------------------------------------------------------
  -- 2.  The path avoids the appearance.
  ----------------------------------------------------------------------------
  have hdeg2 : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard := fun w =>
    Workspace.ProofLemmas.LineGraphDegree.two_le_degree_of_isSubdivision
      Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected happ.1.1 w
  have hdeg₁ : 3 ≤ (H.neighborSet d₁).ncard := hd₁
  have hdeg₂ : 3 ≤ (H.neighborSet d₂).ncard := hd₂
  obtain ⟨col2⟩ : Nonempty (H.Coloring (Fin 2)) := happ.1.2
  have hPK : ∀ u ∈ P, u ∉ K :=
    path_off_appearance phi col2 hdeg2 hN hdeg₁ hdeg₂ hadj hx hne hfirst hlast hno
  have hlenP : 2 ≤ P.length := by
    by_contra hc
    have h0 : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (show P.length = 1 by omega)
    have h1 := hP.2.1
    have h2 := hP.2.2
    rw [hz] at h1 h2
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    exact hne (by rw [← h1, ← h2])
  ----------------------------------------------------------------------------
  -- 3.  Delete the edge `d₁d₂` and the vertex `x`.
  ----------------------------------------------------------------------------
  set H₀ : SimpleGraph (Fin n) := H.deleteEdges {s(d₁, d₂)} with hH₀def
  have hH₀sub : ∀ e : Sym2 (Fin n), e ∈ H₀.edgeSet → e ∈ H.edgeSet := by
    intro e he
    rw [hH₀def, SimpleGraph.edgeSet_deleteEdges] at he
    exact he.1
  have hH₀ne : ∀ e : Sym2 (Fin n), e ∈ H₀.edgeSet → e ≠ s(d₁, d₂) := by
    intro e he hcon
    rw [hH₀def, SimpleGraph.edgeSet_deleteEdges] at he
    exact he.2 (by rw [hcon]; rfl)
  have hnotin : s(d₁, d₂) ∉ H₀.edgeSet := fun hcon => hH₀ne _ hcon rfl
  obtain ⟨phi₀, hphi₀⟩ := deleted_iso phi hadj hx
  -- the vertex of `K` carried by an edge of `H₀` is not `x`
  have hnotx : ∀ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet),
      (↑(phi ⟨e, hH₀sub e he⟩) : V) ≠ x := by
    intro e he hcon
    have hEq : (⟨e, hH₀sub e he⟩ : H.edgeSet) = ⟨s(d₁, d₂), hadj⟩ :=
      phi.injective (Subtype.ext (by simpa using hcon.trans hx.symm))
    exact hH₀ne e he (congrArg Subtype.val hEq)
  have hmemN : ∀ (c : Fin n) (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), c ∈ e →
      (↑(phi ⟨e, hH₀sub e he⟩) : V) ∈ N c \ {x} := by
    intro c e he hce
    refine ⟨?_, hnotx e he⟩
    rw [hN c]
    exact ⟨e, hH₀sub e he, ⟨hH₀sub e he, hce⟩, rfl⟩
  ----------------------------------------------------------------------------
  -- 4.  Add the path as a new track.
  ----------------------------------------------------------------------------
  have hnadj₀ : ¬ H₀.Adj d₁ d₂ := by
    intro hcon
    exact hnotin hcon
  have hPK₀ : ∀ u ∈ P, u ∉ K \ {x} := fun u hu hmem => hPK u hu hmem.1
  have h₁' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), d₁ ∈ e →
      G.Adj p₁ (↑(phi₀ ⟨e, he⟩) : V) := by
    intro e he hce
    rw [hphi₀ e he (hH₀sub e he)]
    exact hfirst _ (hmemN d₁ e he hce)
  have h₂' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), d₂ ∈ e →
      G.Adj p₂ (↑(phi₀ ⟨e, he⟩) : V) := by
    intro e he hce
    rw [hphi₀ e he (hH₀sub e he)]
    exact hlast _ (hmemN d₂ e he hce)
  have hno' : ∀ u ∈ P, ∀ y ∈ K \ {x}, G.Adj u y →
      (u = p₁ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), d₁ ∈ e ∧
        y = (↑(phi₀ ⟨e, he⟩) : V)) ∨
      (u = p₂ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), d₂ ∈ e ∧
        y = (↑(phi₀ ⟨e, he⟩) : V)) := by
    intro u hu y hy hadjuy
    have hyx : y ≠ x := hy.2
    have hcvt : ∀ (c : Fin n), y ∈ N c \ {x} →
        ∃ (e : Sym2 (Fin n)) (he : e ∈ H₀.edgeSet), c ∈ e ∧ y = (↑(phi₀ ⟨e, he⟩) : V) := by
      intro c hyc
      rw [hN c] at hyc
      obtain ⟨e, he, ⟨-, hce⟩, hval⟩ := hyc.1
      have hene : e ≠ s(d₁, d₂) := by
        intro hcon
        apply hyc.2
        rw [hval, ← hx]
        exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext hcon)
      have he₀ : e ∈ H₀.edgeSet := by
        rw [hH₀def, SimpleGraph.edgeSet_deleteEdges]
        exact ⟨he, by simpa using hene⟩
      exact ⟨e, he₀, hce, by rw [hphi₀ e he₀ he]; exact hval⟩
    rcases hno u hu y hy.1 hyx hadjuy with ⟨h, hm⟩ | ⟨h, hm⟩
    · exact Or.inl ⟨h, hcvt d₁ hm⟩
    · exact Or.inr ⟨h, hcvt d₂ hm⟩
  obtain ⟨D, qq, psi, hext, hqqlen, hcompat0⟩ :=
    Workspace.ProofLemmas.Thm93CaseOneAddTrack.addTrackCompat G H₀ (K \ {x}) phi₀
      P p₁ p₂ hP hPK₀ d₁ d₂ hdne hnadj₀ h₁' h₂' hno'
  have hcompat : ∀ (e : Sym2 (Fin n)) (he₀ : e ∈ H₀.edgeSet)
      (hd : Sym2.map (@Sum.inl (Fin n) (Fin (P.length - 1))) e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map (@Sum.inl (Fin n) (Fin (P.length - 1))) e, hd⟩) : V)
        = (↑(phi ⟨e, hH₀sub e he₀⟩) : V) := by
    intro e he₀ hd
    rw [hcompat0 e he₀ hd, hphi₀ e he₀ (hH₀sub e he₀)]
  ----------------------------------------------------------------------------
  -- 5.  `D` is again a subdivision of `K₄`: the deleted edge is a whole track.
  ----------------------------------------------------------------------------
  obtain ⟨a, b, ι, T, hab, ha, hb, hsd⟩ := short_branch_subData happ.1.1 hd₁ hd₂ hadj
  have hext' : IsBranchExtension H₀ (ι a) (ι b) D Sum.inl qq := by rw [ha, hb]; exact hext
  have hnadjB : ¬ ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}).Adj a b := by
    intro hcon
    exact (SimpleGraph.deleteEdges_adj.mp hcon).2 rfl
  have hDsub0 := Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision.add_edge
    ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}) H₀ ι T hsd a b hab hnadjB D Sum.inl qq
    hext'
  have hsup : ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge a b
      = (⊤ : SimpleGraph (Fin 4)) := by
    ext u v
    simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj,
      SimpleGraph.top_adj, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      by_cases hs : s(u, v) = s(a, b)
      · exact Or.inr ⟨Sym2.eq_iff.mp hs, h⟩
      · exact Or.inl ⟨h, hs⟩
  have hDsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) D := by rw [← hsup]; exact hDsub0
  ----------------------------------------------------------------------------
  -- 6.  `D` is bipartite: the new track is odd, and so were `d₁` and `d₂` apart.
  ----------------------------------------------------------------------------
  obtain ⟨colB⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite happ.1.2
  have hle : H₀ ≤ H := by rw [hH₀def]; exact SimpleGraph.deleteEdges_le _
  let col₀ : H₀.Coloring Bool :=
    SimpleGraph.Coloring.mk colB (fun {u v} h => colB.valid (hle h))
  have hlenqq : trackLength qq = P.length := by
    simp only [trackLength, hqqlen]
    omega
  have hPlen3 : 3 ≤ P.length := by
    rcases heven with ⟨k, hk⟩
    simp only [pathLength] at hk
    omega
  have hoddqq : ¬ Even (trackLength qq) := by
    rw [hlenqq]
    rcases heven with ⟨k, hk⟩
    simp only [pathLength] at hk
    rintro ⟨j, hj⟩
    omega
  have hpar : Even (trackLength qq) ↔ col₀ d₁ = col₀ d₂ := by
    have hcol : col₀ d₁ ≠ col₀ d₂ := colB.valid hadj
    exact ⟨fun h => absurd h hoddqq, fun h => absurd h hcol⟩
  have hbip : D.IsBipartite :=
    Workspace.ProofLemmas.EnlargementFromNonlocalColoring.bipartite_of_parity hext col₀ hpar
  ----------------------------------------------------------------------------
  -- 7.  The new track is a branch of `D` of odd length at least three.
  ----------------------------------------------------------------------------
  have hqq3 : 3 ≤ qq.length := by omega
  have hns₁ : H₀.neighborSet d₁ = H.neighborSet d₁ \ {d₂} := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_diff, Set.mem_singleton_iff, hH₀def,
      SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hc => h2 (by rw [hc])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      intro hc
      exact h2 (Sym2.congr_right.mp (by simpa using hc))
  have hns₂ : H₀.neighborSet d₂ = H.neighborSet d₂ \ {d₁} := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_diff, Set.mem_singleton_iff, hH₀def,
      SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hc => h2 (by rw [hc, Sym2.eq_swap])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      intro hc
      have hc' : s(d₂, w) = s(d₂, d₁) := by
        rw [show s(d₁, d₂) = s(d₂, d₁) from Sym2.eq_swap] at hc
        simpa using hc
      exact h2 (Sym2.congr_right.mp hc')
  have hdeg₀₁ : 2 ≤ (H₀.neighborSet d₁).ncard := by
    rw [hns₁, Set.ncard_diff_singleton_of_mem (show d₂ ∈ H.neighborSet d₁ from hadj)]
    omega
  have hdeg₀₂ : 2 ≤ (H₀.neighborSet d₂).ncard := by
    rw [hns₂, Set.ncard_diff_singleton_of_mem (show d₁ ∈ H.neighborSet d₂ from hadj.symm)]
    omega
  have hbv₁ : Sum.inl d₁ ∈ branchVertices D := ext_end_degree hext hdeg₀₁ hqq3
  have hbv₂ : Sum.inl d₂ ∈ branchVertices D :=
    ext_end_degree (ext_symm hext) hdeg₀₂ (by simpa using hqq3)
  have hint : ∀ w ∈ trackInterior qq, w ∉ branchVertices D := by
    intro w hw hcon
    have h1 : 3 ≤ (D.neighborSet w).ncard := hcon
    have h2 := ext_interior_degree hext hw
    omega
  have hbranchD : IsBranch D qq :=
    Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hext.track
      (fun h => hdne (Sum.inl_injective h)) hint hbv₁ hbv₂
  ----------------------------------------------------------------------------
  -- 8.  The deleted vertex `x` overshadows the new branch.
  ----------------------------------------------------------------------------
  have hxswap : (↑(phi ⟨s(d₂, d₁), hadj.symm⟩) : V) = x := by
    rw [← hx]
    exact congrArg (fun t : H.edgeSet => (↑(phi t) : V)) (Subtype.ext Sym2.eq_swap)
  have hnotin' : s(d₂, d₁) ∉ H₀.edgeSet := by
    rw [show s(d₂, d₁) = s(d₁, d₂) from Sym2.eq_swap]
    exact hnotin
  have hover : IsOvershadowedAppearance G D (K \ {x} ∪ {v : V | v ∈ P}) psi := by
    refine ⟨qq, Sum.inl d₁, Sum.inl d₂, hbranchD, hext.track, ?_, ?_, x, ?_, ?_⟩
    · exact Nat.not_even_iff_odd.mp hoddqq
    · rw [hlenqq]
      exact hPlen3
    · exact miss_subsingleton phi hH₀sub hadj hx hnotin hext psi hcompat
    · exact miss_subsingleton phi hH₀sub hadj.symm hxswap hnotin' (ext_symm hext) psi hcompat
  ----------------------------------------------------------------------------
  -- 9.  Move the host onto a `Fin`.
  ----------------------------------------------------------------------------
  let ee := Fintype.equivFin (Fin n ⊕ Fin (P.length - 1))
  let H' : SimpleGraph (Fin (Fintype.card (Fin n ⊕ Fin (P.length - 1)))) :=
    D.map ee.toEmbedding
  let θ : D ≃g H' := SimpleGraph.Iso.map ee D
  refine ⟨Fintype.card (Fin n ⊕ Fin (P.length - 1)), H', K \ {x} ∪ {v : V | v ∈ P},
    (Thm75Claim2Transport.lineGraphIso θ).symm.trans psi, ⟨⟨?_, ?_⟩, ?_⟩,
    overshadowed_map θ psi hover⟩
  · exact Workspace.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso θ hDsub
  · exact SimpleGraph.Colorable.of_hom θ.symm.toHom hbip
  · exact ⟨(Thm75Claim2Transport.lineGraphIso θ).symm.trans psi⟩



end Workspace.ProofLemmas.Thm93CaseOneOvershadow
