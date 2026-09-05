import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.CyclicThreeConnectedAttachments

/-!
# 5.3, Step 2: the no-cross-track branch

This module proves the **left disjunct** of `Thm53Assembly.TwoTracksYieldK33`, i.e. the three
printed sentences (`paper/proofs/5_3.md`, published p. 19)

> *"Suppose every track in `H` between `{p₁,…,p_m}` and `{q₁,…,q_n}` uses one of the edges
> `p₁q₁, p₁q_n, p_mq₁, p_mq_n`.  Then there are no edges between `P` and `Q` except the given
> four, and for every component `F` of `H \ (V(P) ∪ V(Q))`, the set of attachments of `F` in
> `V(P) ∪ V(Q)` is a subset of one of `V(P)`, `V(Q)`.  Since `H` is cyclically 3-connected, it
> follows that `H` is a subdivision of `K₄` and the theorem holds."*

`isSubdivision_k4_of_no_cross_track` is that sentence: under the hypothesis `hno` — *every*
track of `H` with one end on `P` and the other on `Q` uses one of the four cross edges —
`H` itself is a subdivision of `K₄`, with branch-vertices `p₁, p_m, q₁, q_n` and six tracks
`P`, `Q`, `p₁q₁`, `p₁q_n`, `p_mq₁`, `p_mq_n`.

Unlike the rest of §5 the conclusion is about `H` itself, not about a subgraph, so the two
*exactness* clauses of `IsSubdivision` — the cover `V(H) = V(P) ∪ V(Q)` and
`E(H) = ⋃ trackEdges` — have to be proved, not just a `SubdivisionDatum.IsK4Datum`.

## How cyclic 3-connectivity is used

The paper leaves *"Since `H` is cyclically 3-connected"* completely unargued.  It is doing two
distinct jobs, and both are isolated here as reusable lemmas.  Note throughout that `H` is
**never** 3-connected (an internal track vertex has degree `2`), so everything has to be routed
through the 3-connected `J₀` that `H` subdivides.

* `branch_rchIn_of_two`: **deleting two branch-vertices leaves all the other branch-vertices in
  one piece.**  In `J₀`-terms this deletes at most two vertices, and `IsKConnected J₀ 3` gives
  connectedness of the rest; the tracks between surviving branch-vertices are untouched because
  track interiors miss `Set.range ι`.  (This is the two-vertex companion of
  `CyclicThreeConnectedAttachments.branch_avoiding`, which deletes one.)
* `no_two_branchless`: **after deleting two branch-vertices `x`, `y` there is at most one piece
  containing no branch-vertex.**  A branch-free piece closed under adjacency is exactly the
  interior of one track `T c d`, and the two ends `ι c`, `ι d` of that track must then be `x`
  and `y`; since `J₀` is *simple* there is only one such track, so there is only one such piece.

With those two, the printed argument runs as follows, taking `x = p₁`, `y = p_m`, `z = q₁`,
`w = q_n` (all four are branch-vertices, having degree `≥ 3`):

1. `keyRA` / `keyRB`: no walk from `V(P)` to `V(Q)` can avoid `{x,y}` (resp. `{z,w}`) — its
   track would use none of the four cross edges, all of which meet `{x,y}` (resp. `{z,w}`).
2. `interior_core`: consequently the piece of `H - {x,y}` containing `p₂` contains no
   branch-vertex (else it would reach `q₁` by `branch_rchIn_of_two`), so each of its vertices
   has degree exactly `2`, so it *is* the interior of `P`.  Symmetrically for `Q`.
3. `hcross` is the printed *"there are no edges between `P` and `Q` except the given four"*: an
   internal vertex of `P` has both its neighbours on `P`.
4. `hcov` is the printed component analysis.  For `v ∉ V(P) ∪ V(Q)`: if its piece in `H - {x,y}`
   and its piece in `H - {z,w}` both contain a branch-vertex, then `v` reaches `q₁` avoiding
   `{x,y}` and reaches `p₁` avoiding `{z,w}`, and gluing those two walks gives a `P`-to-`Q`
   walk using none of the four cross edges, contradicting 1; otherwise one of the two pieces is
   branch-free and `no_two_branchless` contradicts 2.
5. The `K₄` datum is then read off directly, with `ι = ![x,y,z,w]` and the six tracks
   `T 0 1 = P`, `T 2 3 = Q`, `T i j = [ι i, ι j]` for the four cross edges.  Bipartiteness
   enters exactly once, through `DegenerateK4Tracks.track_color`: `m` and `n` are odd, so
   `p₁ p_m` and `q₁ q_n` are **not** edges, which is what pins the within-track edges down to
   consecutive pairs.

## Joining the two branches of Step 2

`hno` is stated so that the `by_cases` splitting Step 2 into its two printed halves is a single
line: its negation is the paper's *"So we may assume that there is a track `R` of `H` … from
`V(P)` to `V(Q)`, not using any of `p₁q₁, p₁q_n, p_mq₁, p_mq_n`"*, which is the hypothesis of
the cross-track branch.  The binder order matches `Thm53Assembly.TwoTracksYieldK33` exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.NoCrossTrackBranch

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {W : Type*}

/-! ### Walks confined to a set of vertices -/

/-- A `RchIn`-connection yields an honest walk of `H` all of whose vertices lie in the set. -/
theorem walk_of_rchIn {H : SimpleGraph W} {X : Set W} {a b : W} (h : RchIn H X a b) :
    ∃ p : H.Walk a b, ∀ t ∈ p.support, t ∈ X := by
  obtain ⟨ha, hb, hr⟩ := h
  obtain ⟨p⟩ := hr
  refine ⟨p.map (⟨fun z => (z : W), fun {_ _} hz => hz⟩ : (H.induce X) →g H), ?_⟩
  intro t ht
  rw [SimpleGraph.Walk.support_map] at ht
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp ht
  exact z.2

/-- A set closed under `H`-adjacency inside `X` absorbs every walk that stays in `X`. -/
theorem walk_stays {H : SimpleGraph W} {X C : Set W}
    (hcl : ∀ c ∈ C, ∀ t ∈ X, H.Adj c t → t ∈ C) :
    ∀ {a b : W} (p : H.Walk a b), (∀ t ∈ p.support, t ∈ X) → a ∈ C → b ∈ C := by
  intro a b p
  induction p with
  | nil => intro _ ha; exact ha
  | @cons u v w hadj q ih =>
      intro hp ha
      have hsub : ∀ t ∈ q.support, t ∈ X := by
        intro t ht
        exact hp t (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ ht)
      exact ih hsub (hcl u ha v (hsub v q.start_mem_support) hadj)

/-- `walk_stays`, phrased for `RchIn`. -/
theorem rchIn_closed {H : SimpleGraph W} {X C : Set W}
    (hcl : ∀ c ∈ C, ∀ t ∈ X, H.Adj c t → t ∈ C) {a b : W} (ha : a ∈ C)
    (h : RchIn H X a b) : b ∈ C := by
  obtain ⟨p, hp⟩ := walk_of_rchIn h
  exact walk_stays hcl p hp ha

/-! ### Track edges of the support of a walk -/

private theorem trackEdges_cons {α : Type*} (u : α) (l : List α) {e : Sym2 α}
    (he : e ∈ trackEdges (u :: l)) :
    (∃ h : 0 < l.length, e = s(u, l[0]'h)) ∨ e ∈ trackEdges l := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h0 : 0 < l.length := by
      have h := hi; simp only [List.length_cons] at h; omega
    exact Or.inl ⟨h0, by simp⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j + 1 < l.length := by
      have h := hi; simp only [List.length_cons] at h; omega
    exact Or.inr ⟨j, hj, by simp⟩

private theorem mem_edges_of_mem_trackEdges {H : SimpleGraph W} :
    ∀ {a b : W} (p : H.Walk a b) {e : Sym2 W}, e ∈ trackEdges p.support → e ∈ p.edges := by
  intro a b p
  induction p with
  | nil =>
      intro e he
      obtain ⟨i, hi, -⟩ := he
      rw [SimpleGraph.Walk.support_nil] at hi
      simp only [List.length_cons, List.length_nil] at hi
      omega
  | @cons u v w hadj q ih =>
      intro e he
      rw [SimpleGraph.Walk.support_cons] at he
      rcases trackEdges_cons u q.support he with ⟨h0, rfl⟩ | h
      · have hv : ∀ (h : 0 < q.support.length), q.support[0]'h = v := by
          cases q with
          | nil => intro _; rfl
          | cons hh p => intro _; rfl
        rw [hv h0, SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self
      · rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_of_mem _ (ih h)

/-- Every walk contains a track between the same two ends, using only edges of the walk. -/
theorem exists_track_of_walk [DecidableEq W] {H : SimpleGraph W} {a b : W} (p : H.Walk a b) :
    ∃ R : List W, IsTrackFrom H R a b ∧ (∀ t ∈ R, t ∈ p.support) ∧
      (∀ e ∈ trackEdges R, e ∈ p.edges) := by
  refine ⟨p.bypass.support,
    ⟨⟨p.bypass.support_ne_nil, p.bypass_isPath.support_nodup, ?_⟩, ?_, ?_⟩,
    fun t ht => p.support_bypass_subset ht,
    fun e he => p.edges_bypass_subset (mem_edges_of_mem_trackEdges p.bypass he)⟩
  · intro i hi
    exact List.isChain_iff_getElem.mp p.bypass.isChain_adj_support i hi
  · rw [List.head?_eq_some_head p.bypass.support_ne_nil]
    exact congrArg some p.bypass.head_support
  · rw [List.getLast?_eq_some_getLast p.bypass.support_ne_nil]
    exact congrArg some p.bypass.getLast_support

/-! ### The data of a subdivision, bundled -/

/-- All eight clauses of `IsSubdivision J H`, as a structure. -/
structure SubData {n : ℕ} (J : SimpleGraph (Fin n)) (H : SimpleGraph W)
    (ι : Fin n → W) (T : Fin n → Fin n → List W) : Prop where
  inj : Function.Injective ι
  track : ∀ u v : Fin n, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v)
  len : ∀ u v : Fin n, J.Adj u v → 1 ≤ trackLength (T u v)
  rev : ∀ u v : Fin n, J.Adj u v → T v u = (T u v).reverse
  disj : ∀ u v u' v' : Fin n, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
    ∀ t ∈ trackInterior (T u v), t ∉ T u' v'
  new : ∀ u v : Fin n, J.Adj u v → ∀ t ∈ trackInterior (T u v), t ∉ Set.range ι
  cover : ∀ t : W, (∃ u : Fin n, t = ι u) ∨
    ∃ u v : Fin n, J.Adj u v ∧ t ∈ trackInterior (T u v)
  edges : H.edgeSet = ⋃ (u : Fin n) (v : Fin n) (_ : J.Adj u v), trackEdges (T u v)

theorem exists_subData {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    (h : IsSubdivision J H) : ∃ ι T, SubData J H ι T := by
  obtain ⟨ι, T, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨ι, T, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- The branch-vertices of a subdivision of a 3-connected graph are the images of `ι`. -/
theorem branch_eq_range [Finite W] {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    {ι : Fin n → W} {T : Fin n → Fin n → List W} (hJ : IsKConnected J 3)
    (hS : SubData J H ι T) : branchVertices H = Set.range ι :=
  Set.Subset.antisymm
    (SubdivisionCounting.branchVertices_subset_range hS.track hS.rev hS.disj hS.cover hS.edges)
    (SubdivisionCounting.range_subset_branchVertices hS.inj hS.track hS.len hS.disj hS.new
      (SubdivisionCounting.three_le_degree_of_three_connected J hJ))

/-! ### Deleting two vertices keeps the branch-vertices together -/

private theorem branch_avoiding_two {H : SimpleGraph W} {X : Set W} {n : ℕ}
    {J : SimpleGraph (Fin n)} (hJ : IsKConnected J 3) (ι : Fin n → W) (a b : Fin n)
    (hmem : ∀ c : Fin n, c ≠ a → c ≠ b → ι c ∈ X)
    (hedge : ∀ c d : Fin n, J.Adj c d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
      RchIn H X (ι c) (ι d))
    {p q : Fin n} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    RchIn H X (ι p) (ι q) := by
  have hcard : ({a, b} : Set (Fin n)).ncard < 3 := by
    have h1 := Set.ncard_insert_le a ({b} : Set (Fin n))
    have h2 : ({b} : Set (Fin n)).ncard = 1 := Set.ncard_singleton b
    omega
  have hc : (J.induce ((({a, b} : Set (Fin n)))ᶜ)).Connected := hJ.2 _ hcard
  have hpm : p ∈ ((({a, b} : Set (Fin n)))ᶜ) := by
    intro h; rcases h with h | h
    · exact hpa h
    · exact hpb h
  have hqm : q ∈ ((({a, b} : Set (Fin n)))ᶜ) := by
    intro h; rcases h with h | h
    · exact hqa h
    · exact hqb h
  obtain ⟨wk⟩ := hc.preconnected ⟨p, hpm⟩ ⟨q, hqm⟩
  exact rchIn_of_walk (H := H) (X := X)
    (fun c : ↥((({a, b} : Set (Fin n)))ᶜ) => ι (c : Fin n))
    (fun c => hmem _ (fun h => c.2 (Or.inl h)) (fun h => c.2 (Or.inr h)))
    (fun c d hcd => hedge c.1 d.1 hcd (fun h => c.2 (Or.inl h)) (fun h => c.2 (Or.inr h))
      (fun h => d.2 (Or.inl h)) (fun h => d.2 (Or.inr h))) wk

/-- **Deleting two branch-vertices from a cyclically 3-connected graph leaves all the other
branch-vertices in one piece.**  (Deleting two *arbitrary* vertices need not, but that is not
needed: in 5.3 the deleted pair is `{p₁, p_m}`, both of degree `≥ 3`.) -/
theorem branch_rchIn_of_two [Finite W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {x y : W}
    (hxb : x ∈ branchVertices H) (hyb : y ∈ branchVertices H)
    {u v : W} (hub : u ∈ branchVertices H) (hvb : v ∈ branchVertices H)
    (huA : u ∈ ((({x, y} : Set W))ᶜ)) (hvA : v ∈ ((({x, y} : Set W))ᶜ)) :
    RchIn H ((({x, y} : Set W))ᶜ) u v := by
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  rw [hbr] at hxb hyb hub hvb
  obtain ⟨a, ha⟩ := hxb
  obtain ⟨b, hb⟩ := hyb
  obtain ⟨p, hp⟩ := hub
  obtain ⟨q, hq⟩ := hvb
  subst ha; subst hb; subst hp; subst hq
  have hmem : ∀ c : Fin n, c ≠ a → c ≠ b → ι c ∈ ((({ι a, ι b} : Set W))ᶜ) := by
    intro c hca hcb hc
    rcases hc with h | h
    · exact hca (hS.inj h)
    · exact hcb (hS.inj h)
  have hedge : ∀ c d : Fin n, J.Adj c d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
      RchIn H ((({ι a, ι b} : Set W))ᶜ) (ι c) (ι d) := by
    intro c d hcd hca hcb hda hdb
    refine rchIn_of_chain (T c d)
      (List.isChain_iff_getElem.mpr (hS.track c d hcd).1.2.2) ?_
      (List.mem_of_head? (hS.track c d hcd).2.1)
      (List.mem_of_getLast? (hS.track c d hcd).2.2)
    intro t ht hbad
    have hta : t = ι a ∨ t = ι b := hbad
    by_cases hint : t ∈ trackInterior (T c d)
    · refine hS.new c d hcd t hint ?_
      rcases hta with h | h
      · exact ⟨a, h.symm⟩
      · exact ⟨b, h.symm⟩
    · rcases SubdivisionCompose.mem_ends_of_mem (hS.track c d hcd).2.1
        (hS.track c d hcd).2.2 ht hint with h | h
      · rcases hta with h2 | h2
        · exact hca (hS.inj (h.symm.trans h2))
        · exact hcb (hS.inj (h.symm.trans h2))
      · rcases hta with h2 | h2
        · exact hda (hS.inj (h.symm.trans h2))
        · exact hdb (hS.inj (h.symm.trans h2))
  refine branch_avoiding_two hJ ι a b hmem hedge ?_ ?_ ?_ ?_
  · intro h; exact huA (Or.inl (by rw [h]))
  · intro h; exact huA (Or.inr (by rw [h]; exact rfl))
  · intro h; exact hvA (Or.inl (by rw [h]))
  · intro h; exact hvA (Or.inr (by rw [h]; exact rfl))

/-! ### At most one branch-free piece after deleting two branch-vertices -/

/-- A nonempty set with no branch-vertex which is closed under `H`-adjacency inside
`{x,y}ᶜ` is exactly the interior of one of the tracks, and that track's two ends are `x`
and `y`. -/
private theorem branchless_interior [Finite W] {H : SimpleGraph W} {n : ℕ}
    {J : SimpleGraph (Fin n)} {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hJ : IsKConnected J 3) (hS : SubData J H ι T) {x y : W}
    (hxr : x ∈ Set.range ι) (hyr : y ∈ Set.range ι) {E : Set W}
    (hEcl : ∀ c ∈ E, ∀ t ∈ ((({x, y} : Set W))ᶜ), H.Adj c t → t ∈ E)
    (hEnb : ∀ c ∈ E, c ∉ branchVertices H) (hEne : E.Nonempty) :
    ∃ c d : Fin n, J.Adj c d ∧ (∃ t, t ∈ trackInterior (T c d)) ∧
      (∀ t ∈ trackInterior (T c d), t ∈ E) ∧
      ι c ∈ (({x, y} : Set W)) ∧ ι d ∈ (({x, y} : Set W)) := by
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  obtain ⟨e₀, he₀⟩ := hEne
  have he₀r : e₀ ∉ Set.range ι := by
    intro h; exact hEnb e₀ he₀ (by rw [hbr]; exact h)
  -- the head of a track whose interior lies in `E` is `x` or `y`
  have hhead : ∀ c d : Fin n, J.Adj c d → (∀ t ∈ trackInterior (T c d), t ∈ E) →
      (∃ t, t ∈ trackInterior (T c d)) → ι c ∈ (({x, y} : Set W)) := by
    intro c d hcd hsubE hne
    obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨j, hj, -⟩ := (SubdivisionCounting.mem_trackInterior_iff _ _).mp ht₀
    have hlen3 : 2 < (T c d).length := by omega
    have h1int : (T c d)[1]'(by omega) ∈ trackInterior (T c d) := by
      have := SubdivisionCounting.mem_trackInterior_getElem (T c d) 0 (by omega)
      exact this
    have h1E : (T c d)[1]'(by omega) ∈ E := hsubE _ h1int
    have h0eq : (T c d)[0]'(by omega) = ι c :=
      SubdivisionCounting.track_head (hS.track c d hcd) (by omega)
    have hadj0 : H.Adj ((T c d)[0]'(by omega)) ((T c d)[1]'(by omega)) :=
      (hS.track c d hcd).1.2.2 0 (by omega)
    by_contra hbad
    have hmemE : ι c ∈ E := by
      refine hEcl _ h1E (ι c) hbad ?_
      rw [← h0eq]; exact hadj0.symm
    exact hEnb _ hmemE (by rw [hbr]; exact ⟨c, rfl⟩)
  rcases hS.cover e₀ with ⟨c, hc⟩ | ⟨c, d, hcd, hint⟩
  · exact absurd ⟨c, hc.symm⟩ he₀r
  have hintX : ∀ t ∈ trackInterior (T c d), t ∈ ((({x, y} : Set W))ᶜ) := by
    intro t ht hbad
    refine hS.new c d hcd t ht ?_
    rcases hbad with h | h
    · rw [h]; exact hxr
    · rw [h]; exact hyr
  have hchain : List.IsChain H.Adj (trackInterior (T c d)) :=
    ((List.isChain_iff_getElem.mpr (hS.track c d hcd).1.2.2).tail).dropLast
  have hsubE : ∀ t ∈ trackInterior (T c d), t ∈ E := by
    intro t ht
    exact rchIn_closed hEcl he₀ (rchIn_of_chain _ hchain hintX hint ht)
  refine ⟨c, d, hcd, ⟨e₀, hint⟩, hsubE, hhead c d hcd hsubE ⟨e₀, hint⟩, ?_⟩
  -- the other end, via the reversed track
  have hcd' : J.Adj d c := hcd.symm
  have hrevT : T d c = (T c d).reverse := hS.rev c d hcd
  have hsubE' : ∀ t ∈ trackInterior (T d c), t ∈ E := by
    intro t ht
    rw [hrevT] at ht
    exact hsubE t (TrackSlice.mem_trackInterior_reverse.mp ht)
  refine hhead d c hcd' hsubE' ⟨e₀, ?_⟩
  rw [hrevT]
  exact TrackSlice.mem_trackInterior_reverse.mpr hint

/-- **After deleting two branch-vertices there is at most one branch-free piece.** -/
theorem no_two_branchless [Finite W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {x y : W}
    (hxb : x ∈ branchVertices H) (hyb : y ∈ branchVertices H) {C D : Set W}
    (hCcl : ∀ c ∈ C, ∀ t ∈ ((({x, y} : Set W))ᶜ), H.Adj c t → t ∈ C)
    (hDcl : ∀ c ∈ D, ∀ t ∈ ((({x, y} : Set W))ᶜ), H.Adj c t → t ∈ D)
    (hCnb : ∀ c ∈ C, c ∉ branchVertices H) (hDnb : ∀ c ∈ D, c ∉ branchVertices H)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hCD : ∀ c ∈ C, c ∉ D) : False := by
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  have hxr : x ∈ Set.range ι := by rw [← hbr]; exact hxb
  have hyr : y ∈ Set.range ι := by rw [← hbr]; exact hyb
  obtain ⟨c, d, hcd, ⟨t₀, ht₀⟩, hCsub, hcx, hdx⟩ :=
    branchless_interior hJ hS hxr hyr hCcl hCnb hCne
  obtain ⟨c', d', hcd', ⟨t₁, ht₁⟩, hDsub, hcx', hdx'⟩ :=
    branchless_interior hJ hS hxr hyr hDcl hDnb hDne
  -- the two tracks join the same pair of branch-vertices, hence are the same track
  obtain ⟨a, hxa⟩ := hxr
  obtain ⟨b, hyb'⟩ := hyr
  have hdec : ∀ (u v : Fin n), J.Adj u v → ι u ∈ (({x, y} : Set W)) →
      ι v ∈ (({x, y} : Set W)) → (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    intro u v huv hu hv
    have hune : u ≠ v := huv.ne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with h1 | h1
    · have hua : u = a := hS.inj (by rw [h1, ← hxa])
      rcases hv with h2 | h2
      · exact absurd (hS.inj (by rw [h1, h2] : ι u = ι v)) hune
      · exact Or.inl ⟨hua, hS.inj (by rw [h2, ← hyb'])⟩
    · have hub : u = b := hS.inj (by rw [h1, ← hyb'])
      rcases hv with h2 | h2
      · exact Or.inr ⟨hub, hS.inj (by rw [h2, ← hxa])⟩
      · exact absurd (hS.inj (by rw [h1, h2] : ι u = ι v)) hune
  have hJab : J.Adj a b := by
    rcases hdec c d hcd hcx hdx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hcd
    · rw [← h2, ← h1]; exact hcd.symm
  have hTab : ∀ (u v : Fin n), ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) →
      ∀ t : W, t ∈ trackInterior (T u v) ↔ t ∈ trackInterior (T a b) := by
    intro u v h t
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hS.rev a b hJab]
      exact TrackSlice.mem_trackInterior_reverse
  have hstep1 := (hTab c d (hdec c d hcd hcx hdx) t₀).mp ht₀
  have hstep2 := (hTab c' d' (hdec c' d' hcd' hcx' hdx') t₀).mpr hstep1
  exact hCD t₀ (hCsub t₀ ht₀) (hDsub t₀ hstep2)

/-! ### The interior of one of the two tracks -/

/-- **The structural core.**  If no vertex of the track `P` reaches the branch-vertex `zz`
without passing through one of `P`'s two ends `x`, `y`, then the piece of `H - {x,y}` containing
`p₂` is exactly the interior of `P`, contains no branch-vertex, and every internal vertex of `P`
has exactly its two track-neighbours. -/
theorem interior_core [Finite W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {P : List W} (hP : 3 ≤ P.length)
    (htP : IsTrackList H P) {x y : W} (hx : P[0] = x) (hy : P[P.length - 1] = y)
    (hxb : x ∈ branchVertices H) (hyb : y ∈ branchVertices H)
    {zz : W} (hzb : zz ∈ branchVertices H) (hzP : zz ∉ P)
    (hsep : ∀ t ∈ P, ¬ RchIn H ((({x, y} : Set W))ᶜ) t zz) :
    (∀ (j : ℕ) (hj : j + 2 < P.length),
        H.neighborSet (P[j + 1]'(by omega)) = {P[j]'(by omega), P[j + 2]'hj}) ∧
    (∀ v : W, RchIn H ((({x, y} : Set W))ᶜ) (P[1]'(by omega)) v → v ∈ P) ∧
    (∀ v : W, RchIn H ((({x, y} : Set W))ᶜ) (P[1]'(by omega)) v → v ∉ branchVertices H) := by
  have hnd : P.Nodup := htP.2.1
  have hAc : ∀ (j : ℕ) (hj : j + 2 < P.length),
      (P[j + 1]'(by omega)) ∈ ((({x, y} : Set W))ᶜ) := by
    intro j hj hbad
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with h | h
    · rw [← hx] at h
      have := hnd.getElem_inj_iff.mp h
      omega
    · rw [← hy] at h
      have := hnd.getElem_inj_iff.mp h
      omega
  have hchain : List.IsChain H.Adj (trackInterior P) :=
    ((List.isChain_iff_getElem.mpr htP.2.2).tail).dropLast
  have hintX : ∀ t ∈ trackInterior P, t ∈ ((({x, y} : Set W))ᶜ) := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := (SubdivisionCounting.mem_trackInterior_iff P t).mp ht
    rw [← hjt]
    exact hAc j hj
  have h1int : (P[1]'(by omega)) ∈ trackInterior P :=
    SubdivisionCounting.mem_trackInterior_getElem P 0 (by omega)
  have hrch : ∀ (j : ℕ) (hj : j + 2 < P.length),
      RchIn H ((({x, y} : Set W))ᶜ) (P[1]'(by omega)) (P[j + 1]'(by omega)) := by
    intro j hj
    exact rchIn_of_chain (trackInterior P) hchain hintX h1int
      (SubdivisionCounting.mem_trackInterior_getElem P j hj)
  have hzA : zz ∈ ((({x, y} : Set W))ᶜ) := by
    intro hbad
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with h | h
    · exact hzP (by rw [h, ← hx]; exact List.getElem_mem _)
    · exact hzP (by rw [h, ← hy]; exact List.getElem_mem _)
  have hnb : ∀ v : W, RchIn H ((({x, y} : Set W))ᶜ) (P[1]'(by omega)) v →
      v ∉ branchVertices H := by
    intro v hv hvb
    exact hsep (P[1]'(by omega)) (List.getElem_mem _)
      (hv.trans (branch_rchIn_of_two hc3 hxb hyb hvb hzb hv.mem_right hzA))
  have hnbr : ∀ (j : ℕ) (hj : j + 2 < P.length),
      H.neighborSet (P[j + 1]'(by omega)) = {P[j]'(by omega), P[j + 2]'hj} := by
    intro j hj
    have hnb2 : (H.neighborSet (P[j + 1]'(by omega))).ncard ≤ 2 := by
      by_contra hc
      exact hnb _ (hrch j hj) (by show 3 ≤ (H.neighborSet (P[j + 1]'(by omega))).ncard; omega)
    have hne : (P[j]'(by omega)) ≠ (P[j + 2]'hj) := by
      intro hc
      have := hnd.getElem_inj_iff.mp hc
      omega
    have hsubset : ({P[j]'(by omega), P[j + 2]'hj} : Set W) ⊆
        H.neighborSet (P[j + 1]'(by omega)) := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with h | h
      · rw [h]; exact (htP.2.2 j (by omega)).symm
      · rw [h]; exact htP.2.2 (j + 1) (by omega)
    have hcard : ({P[j]'(by omega), P[j + 2]'hj} : Set W).ncard = 2 := Set.ncard_pair hne
    exact (Set.eq_of_subset_of_ncard_le hsubset (by omega) (Set.toFinite _)).symm
  refine ⟨hnbr, ?_, hnb⟩
  intro v hv
  have hcl : ∀ c ∈ {t : W | t ∈ P ∧ t ∈ ((({x, y} : Set W))ᶜ)},
      ∀ t ∈ ((({x, y} : Set W))ᶜ), H.Adj c t →
        t ∈ {t : W | t ∈ P ∧ t ∈ ((({x, y} : Set W))ᶜ)} := by
    rintro c ⟨hcP, hcA⟩ t htA hadj
    obtain ⟨i, hi, hic⟩ := List.getElem_of_mem hcP
    have hi0 : i ≠ 0 := by
      intro h
      refine hcA (Or.inl ?_)
      rw [← hic, ← hx]
      exact SubdivisionCounting.getElem_eq_of_index_eq P h hi (by omega)
    have hil : i ≠ P.length - 1 := by
      intro h
      refine hcA (Or.inr ?_)
      show c = y
      rw [← hic, ← hy]
      exact SubdivisionCounting.getElem_eq_of_index_eq P h hi (by omega)
    obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj2 : j + 2 < P.length := by omega
    have hmem : t ∈ H.neighborSet (P[j + 1]'(by omega)) := by
      have heq : (P[j + 1]'(by omega)) = c := by
        rw [← hic]
        exact SubdivisionCounting.getElem_eq_of_index_eq P hj.symm (by omega) hi
      rw [heq]; exact hadj
    rw [hnbr j hj2] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    refine ⟨?_, htA⟩
    rcases hmem with h | h
    · rw [h]; exact List.getElem_mem _
    · rw [h]; exact List.getElem_mem _
  exact (rchIn_closed hcl
    (show (P[1]'(by omega)) ∈ {t : W | t ∈ P ∧ t ∈ ((({x, y} : Set W))ᶜ)} from
      ⟨List.getElem_mem _, hintX _ h1int⟩) hv).1

/-! ### The no-cross-track branch of Step 2 of 5.3 -/

theorem isSubdivision_k4_of_no_cross_track [Finite W] {H : SimpleGraph W}
    (hbip : H.IsBipartite) (hc3 : CyclicallyThreeConnected H)
    (P Q : List W) (hP : 3 ≤ P.length) (hQ : 3 ≤ Q.length)
    (htP : IsTrackList H P) (htQ : IsTrackList H Q) (hdisj : ∀ t ∈ P, t ∉ Q)
    (hoP : Odd P.length) (hoQ : Odd Q.length)
    (e1 : H.Adj P[0] Q[0]) (e2 : H.Adj P[0] Q[Q.length - 1])
    (e3 : H.Adj P[P.length - 1] Q[0]) (e4 : H.Adj P[P.length - 1] Q[Q.length - 1])
    (hno : ∀ (R : List W) (a b : W), IsTrackFrom H R a b → a ∈ P → b ∈ Q →
      s(P[0], Q[0]) ∈ trackEdges R ∨ s(P[0], Q[Q.length - 1]) ∈ trackEdges R ∨
      s(P[P.length - 1], Q[0]) ∈ trackEdges R ∨
      s(P[P.length - 1], Q[Q.length - 1]) ∈ trackEdges R) :
    IsSubdivision (⊤ : SimpleGraph (Fin 4)) H := by
  classical
  -- Name the four ends.
  obtain ⟨x, y, z, w, hx, hy, hz, hw⟩ : ∃ x y z w : W,
      P[0] = x ∧ P[P.length - 1] = y ∧ Q[0] = z ∧ Q[Q.length - 1] = w :=
    ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩
  simp only [hx, hy, hz, hw] at e1 e2 e3 e4 hno
  have hxP : x ∈ P := by rw [← hx]; exact List.getElem_mem _
  have hyP : y ∈ P := by rw [← hy]; exact List.getElem_mem _
  have hzQ : z ∈ Q := by rw [← hz]; exact List.getElem_mem _
  have hwQ : w ∈ Q := by rw [← hw]; exact List.getElem_mem _
  have hxQ : x ∉ Q := hdisj x hxP
  have hyQ : y ∉ Q := hdisj y hyP
  have hzP : z ∉ P := fun h => hdisj z h hzQ
  have hwP : w ∉ P := fun h => hdisj w h hwQ
  have dxy : x ≠ y := by
    rw [← hx, ← hy]; intro hc; have := htP.2.1.getElem_inj_iff.mp hc; omega
  have dzw : z ≠ w := by
    rw [← hz, ← hw]; intro hc; have := htQ.2.1.getElem_inj_iff.mp hc; omega
  have dxz : x ≠ z := fun h => hzP (h ▸ hxP)
  have dxw : x ≠ w := fun h => hwP (h ▸ hxP)
  have dyz : y ≠ z := fun h => hzP (h ▸ hyP)
  have dyw : y ≠ w := fun h => hwP (h ▸ hyP)
  -- the two tracks, with named ends
  have hPhead : P.head? = some x := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < P.length), hx]
  have hPlast : P.getLast? = some y := by
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : P.length - 1 < P.length), hy]
  have hQhead : Q.head? = some z := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < Q.length), hz]
  have hQlast : Q.getLast? = some w := by
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : Q.length - 1 < Q.length), hw]
  have hPtrack : IsTrackFrom H P x y := ⟨htP, hPhead, hPlast⟩
  have hQtrack : IsTrackFrom H Q z w := ⟨htQ, hQhead, hQlast⟩
  -- the four ends are branch-vertices
  have hdeg3 : ∀ (u a b c : W), a ≠ b → a ≠ c → b ≠ c → H.Adj u a → H.Adj u b → H.Adj u c →
      u ∈ branchVertices H := by
    intro u a b c hab hac hbc ha hb hc
    show 3 ≤ (H.neighborSet u).ncard
    have hsub : ({a, b, c} : Set W) ⊆ H.neighborSet u := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with h | h | h
      · rw [h]; exact ha
      · rw [h]; exact hb
      · rw [h]; exact hc
    have hcard : ({a, b, c} : Set W).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, hac]) (Set.toFinite _), Set.ncard_pair hbc]
    calc (3 : ℕ) = ({a, b, c} : Set W).ncard := hcard.symm
      _ ≤ (H.neighborSet u).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hP1P : (P[1]'(by omega)) ∈ P := List.getElem_mem _
  have hQ1Q : (Q[1]'(by omega)) ∈ Q := List.getElem_mem _
  have hPm2 : (P[P.length - 2]'(by omega)) ∈ P := List.getElem_mem _
  have hQm2 : (Q[Q.length - 2]'(by omega)) ∈ Q := List.getElem_mem _
  have hxb : x ∈ branchVertices H := by
    refine hdeg3 x (P[1]'(by omega)) z w (fun h => hzP (h ▸ hP1P)) (fun h => hwP (h ▸ hP1P))
      dzw ?_ e1 e2
    rw [← hx]; exact htP.2.2 0 (by omega)
  have hyb : y ∈ branchVertices H := by
    refine hdeg3 y (P[P.length - 2]'(by omega)) z w (fun h => hzP (h ▸ hPm2))
      (fun h => hwP (h ▸ hPm2)) dzw ?_ e3 e4
    rw [← hy]
    have hh := htP.2.2 (P.length - 2) (by omega)
    have heq : (P[P.length - 2 + 1]'(by omega)) = (P[P.length - 1]'(by omega)) :=
      SubdivisionCounting.getElem_eq_of_index_eq P (by omega) (by omega) (by omega)
    rw [heq] at hh
    exact hh.symm
  have hzb : z ∈ branchVertices H := by
    refine hdeg3 z (Q[1]'(by omega)) x y (fun h => hxQ (h ▸ hQ1Q)) (fun h => hyQ (h ▸ hQ1Q))
      dxy ?_ e1.symm e3.symm
    rw [← hz]; exact htQ.2.2 0 (by omega)
  have hwb : w ∈ branchVertices H := by
    refine hdeg3 w (Q[Q.length - 2]'(by omega)) x y (fun h => hxQ (h ▸ hQm2))
      (fun h => hyQ (h ▸ hQm2)) dxy ?_ e2.symm e4.symm
    rw [← hw]
    have hh := htQ.2.2 (Q.length - 2) (by omega)
    have heq : (Q[Q.length - 2 + 1]'(by omega)) = (Q[Q.length - 1]'(by omega)) :=
      SubdivisionCounting.getElem_eq_of_index_eq Q (by omega) (by omega) (by omega)
    rw [heq] at hh
    exact hh.symm
  -- since `H` is bipartite and `m`, `n` are odd, the two ends of each track are non-adjacent
  obtain ⟨col⟩ := hbip
  have hnadjP : ¬ H.Adj x y := by
    intro hadj
    have h1 := DegenerateK4Tracks.track_color col htP (P.length - 1) (by omega) (by omega)
    rw [hy, hx] at h1
    have hodd : P.length % 2 = 1 := Nat.odd_iff.mp hoP
    have hb1 := (col x).isLt
    have hb2 := (col y).isLt
    exact col.valid hadj (Fin.val_injective (by omega))
  have hnadjQ : ¬ H.Adj z w := by
    intro hadj
    have h1 := DegenerateK4Tracks.track_color col htQ (Q.length - 1) (by omega) (by omega)
    rw [hw, hz] at h1
    have hodd : Q.length % 2 = 1 := Nat.odd_iff.mp hoQ
    have hb1 := (col z).isLt
    have hb2 := (col w).isLt
    exact col.valid hadj (Fin.val_injective (by omega))
  -- the no-cross-track hypothesis, in walk form
  have key : ∀ (a b : W), a ∈ P → b ∈ Q → ∀ p : H.Walk a b,
      s(x, z) ∉ p.edges → s(x, w) ∉ p.edges → s(y, z) ∉ p.edges → s(y, w) ∉ p.edges →
      False := by
    intro a b ha hb p h1 h2 h3 h4
    obtain ⟨R, hR, -, hRe⟩ := exists_track_of_walk p
    rcases hno R a b hR ha hb with h | h | h | h
    · exact h1 (hRe _ h)
    · exact h2 (hRe _ h)
    · exact h3 (hRe _ h)
    · exact h4 (hRe _ h)
  have notedge1 : ∀ (a b : W) (p : H.Walk a b) (u v : W), u ∉ p.support → s(u, v) ∉ p.edges :=
    fun _ _ p u v hu he => hu (p.fst_mem_support_of_mem_edges he)
  have notedge2 : ∀ (a b : W) (p : H.Walk a b) (u v : W), v ∉ p.support → s(u, v) ∉ p.edges :=
    fun _ _ p u v hv he => hv (p.snd_mem_support_of_mem_edges he)
  have keyRA : ∀ (a b : W), a ∈ P → b ∈ Q → ¬ RchIn H ((({x, y} : Set W))ᶜ) a b := by
    intro a b ha hb hr
    obtain ⟨p, hp⟩ := walk_of_rchIn hr
    refine key a b ha hb p (notedge1 _ _ p x z ?_) (notedge1 _ _ p x w ?_)
      (notedge1 _ _ p y z ?_) (notedge1 _ _ p y w ?_)
    · intro hc; exact hp x hc (Or.inl rfl)
    · intro hc; exact hp x hc (Or.inl rfl)
    · intro hc; exact hp y hc (Or.inr rfl)
    · intro hc; exact hp y hc (Or.inr rfl)
  have keyRB : ∀ (a b : W), a ∈ P → b ∈ Q → ¬ RchIn H ((({z, w} : Set W))ᶜ) a b := by
    intro a b ha hb hr
    obtain ⟨p, hp⟩ := walk_of_rchIn hr
    refine key a b ha hb p (notedge2 _ _ p x z ?_) (notedge2 _ _ p x w ?_)
      (notedge2 _ _ p y z ?_) (notedge2 _ _ p y w ?_)
    · intro hc; exact hp z hc (Or.inl rfl)
    · intro hc; exact hp w hc (Or.inr rfl)
    · intro hc; exact hp z hc (Or.inl rfl)
    · intro hc; exact hp w hc (Or.inr rfl)
  -- the two interiors
  obtain ⟨hnbrP, hinP, hnbP⟩ := interior_core hc3 hP htP hx hy hxb hyb hzb hzP
    (fun t ht => keyRA t z ht hzQ)
  obtain ⟨hnbrQ, hinQ, hnbQ⟩ := interior_core hc3 hQ htQ hz hw hzb hwb hxb hxQ
    (fun t ht hr => keyRB x t hxP ht hr.symm)
  have hP1A : (P[1]'(by omega)) ∈ ((({x, y} : Set W))ᶜ) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | h
    · rw [← hx] at h; have := htP.2.1.getElem_inj_iff.mp h; omega
    · rw [← hy] at h; have := htP.2.1.getElem_inj_iff.mp h; omega
  have hQ1B : (Q[1]'(by omega)) ∈ ((({z, w} : Set W))ᶜ) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | h
    · rw [← hz] at h; have := htQ.2.1.getElem_inj_iff.mp h; omega
    · rw [← hw] at h; have := htQ.2.1.getElem_inj_iff.mp h; omega
  have hzA : z ∈ ((({x, y} : Set W))ᶜ) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | h
    · exact dxz h.symm
    · exact dyz h.symm
  have hxB : x ∈ ((({z, w} : Set W))ᶜ) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | h
    · exact dxz h
    · exact dxw h
  -- **Every vertex of `H` lies on `P` or on `Q`.**
  have hcov : ∀ v : W, v ∈ P ∨ v ∈ Q := by
    intro v
    by_contra hbad
    push Not at hbad
    obtain ⟨hvP, hvQ⟩ := hbad
    have hvA : v ∈ ((({x, y} : Set W))ᶜ) := by
      intro hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with h | h
      · exact hvP (h ▸ hxP)
      · exact hvP (h ▸ hyP)
    have hvB : v ∈ ((({z, w} : Set W))ᶜ) := by
      intro hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with h | h
      · exact hvQ (h ▸ hzQ)
      · exact hvQ (h ▸ hwQ)
    by_cases hCbr : ∃ u : W, RchIn H ((({x, y} : Set W))ᶜ) v u ∧ u ∈ branchVertices H
    · by_cases hDbr : ∃ u : W, RchIn H ((({z, w} : Set W))ᶜ) v u ∧ u ∈ branchVertices H
      · obtain ⟨u, hu, hub⟩ := hCbr
        obtain ⟨u', hu', hub'⟩ := hDbr
        have hvz : RchIn H ((({x, y} : Set W))ᶜ) v z :=
          hu.trans (branch_rchIn_of_two hc3 hxb hyb hub hzb hu.mem_right hzA)
        have hvx : RchIn H ((({z, w} : Set W))ᶜ) v x :=
          hu'.trans (branch_rchIn_of_two hc3 hzb hwb hub' hxb hu'.mem_right hxB)
        obtain ⟨p₂, hp₂⟩ := walk_of_rchIn hvz
        obtain ⟨p₁, hp₁⟩ := walk_of_rchIn hvx
        have hpp : ∀ e ∈ (p₁.reverse.append p₂).edges, e ∈ p₁.edges ∨ e ∈ p₂.edges := by
          intro e he
          rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse] at he
          rcases List.mem_append.mp he with h | h
          · exact Or.inl (List.mem_reverse.mp h)
          · exact Or.inr h
        refine key x z hxP hzQ (p₁.reverse.append p₂) ?_ ?_ ?_ ?_
        · intro he
          rcases hpp _ he with h | h
          · exact hp₁ z (p₁.snd_mem_support_of_mem_edges h) (Or.inl rfl)
          · exact hp₂ x (p₂.fst_mem_support_of_mem_edges h) (Or.inl rfl)
        · intro he
          rcases hpp _ he with h | h
          · exact hp₁ w (p₁.snd_mem_support_of_mem_edges h) (Or.inr rfl)
          · exact hp₂ x (p₂.fst_mem_support_of_mem_edges h) (Or.inl rfl)
        · intro he
          rcases hpp _ he with h | h
          · exact hp₁ z (p₁.snd_mem_support_of_mem_edges h) (Or.inl rfl)
          · exact hp₂ y (p₂.fst_mem_support_of_mem_edges h) (Or.inr rfl)
        · intro he
          rcases hpp _ he with h | h
          · exact hp₁ w (p₁.snd_mem_support_of_mem_edges h) (Or.inr rfl)
          · exact hp₂ y (p₂.fst_mem_support_of_mem_edges h) (Or.inr rfl)
      · push Not at hDbr
        refine no_two_branchless hc3 hzb hwb
          (C := {t | RchIn H ((({z, w} : Set W))ᶜ) (Q[1]'(by omega)) t})
          (D := {t | RchIn H ((({z, w} : Set W))ᶜ) v t})
          (fun c hc t ht hadj => hc.trans (RchIn.of_adj hc.mem_right ht hadj))
          (fun c hc t ht hadj => hc.trans (RchIn.of_adj hc.mem_right ht hadj))
          hnbQ (fun c hc => hDbr c hc) ⟨_, RchIn.refl hQ1B⟩ ⟨v, RchIn.refl hvB⟩ ?_
        intro c hc hcD
        exact hvQ (hinQ v (hc.trans hcD.symm))
    · push Not at hCbr
      refine no_two_branchless hc3 hxb hyb
        (C := {t | RchIn H ((({x, y} : Set W))ᶜ) (P[1]'(by omega)) t})
        (D := {t | RchIn H ((({x, y} : Set W))ᶜ) v t})
        (fun c hc t ht hadj => hc.trans (RchIn.of_adj hc.mem_right ht hadj))
        (fun c hc t ht hadj => hc.trans (RchIn.of_adj hc.mem_right ht hadj))
        hnbP (fun c hc => hCbr c hc) ⟨_, RchIn.refl hP1A⟩ ⟨v, RchIn.refl hvA⟩ ?_
      intro c hc hcD
      exact hvP (hinP v (hc.trans hcD.symm))
  -- decoders for membership on the two tracks
  have hPidx : ∀ t ∈ P, t = x ∨ t = y ∨
      ∃ (j : ℕ) (hj : j + 2 < P.length), (P[j + 1]'(by omega)) = t := by
    intro t ht
    obtain ⟨i, hi, hit⟩ := List.getElem_of_mem ht
    by_cases h0 : i = 0
    · left; rw [← hit, ← hx]
      exact SubdivisionCounting.getElem_eq_of_index_eq P h0 hi (by omega)
    · by_cases hl : i = P.length - 1
      · right; left; rw [← hit, ← hy]
        exact SubdivisionCounting.getElem_eq_of_index_eq P hl hi (by omega)
      · right; right
        refine ⟨i - 1, by omega, ?_⟩
        rw [← hit]
        exact SubdivisionCounting.getElem_eq_of_index_eq P (by omega) (by omega) hi
  have hQidx : ∀ t ∈ Q, t = z ∨ t = w ∨
      ∃ (j : ℕ) (hj : j + 2 < Q.length), (Q[j + 1]'(by omega)) = t := by
    intro t ht
    obtain ⟨i, hi, hit⟩ := List.getElem_of_mem ht
    by_cases h0 : i = 0
    · left; rw [← hit, ← hz]
      exact SubdivisionCounting.getElem_eq_of_index_eq Q h0 hi (by omega)
    · by_cases hl : i = Q.length - 1
      · right; left; rw [← hit, ← hw]
        exact SubdivisionCounting.getElem_eq_of_index_eq Q hl hi (by omega)
      · right; right
        refine ⟨i - 1, by omega, ?_⟩
        rw [← hit]
        exact SubdivisionCounting.getElem_eq_of_index_eq Q (by omega) (by omega) hi
  -- **There are no edges between `P` and `Q` except the given four.**
  have hcross : ∀ a b : W, a ∈ P → b ∈ Q → H.Adj a b →
      (a = x ∨ a = y) ∧ (b = z ∨ b = w) := by
    intro a b ha hb hadj
    constructor
    · rcases hPidx a ha with h | h | ⟨j, hj, hja⟩
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hmem : b ∈ H.neighborSet (P[j + 1]'(by omega)) := by rw [hja]; exact hadj
        rw [hnbrP j hj] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · exact hdisj b (by rw [h]; exact List.getElem_mem _) hb
        · exact hdisj b (by rw [h]; exact List.getElem_mem _) hb
    · rcases hQidx b hb with h | h | ⟨j, hj, hjb⟩
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hmem : a ∈ H.neighborSet (Q[j + 1]'(by omega)) := by rw [hjb]; exact hadj.symm
        rw [hnbrQ j hj] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · exact hdisj a ha (by rw [h]; exact List.getElem_mem _)
        · exact hdisj a ha (by rw [h]; exact List.getElem_mem _)
  -- edges inside a track join consecutive vertices
  have hconsec : ∀ (R : List W) (hR3 : 3 ≤ R.length), IsTrackList H R →
      (∀ (j : ℕ) (hj : j + 2 < R.length),
        H.neighborSet (R[j + 1]'(by omega)) = {R[j]'(by omega), R[j + 2]'hj}) →
      ¬ H.Adj (R[0]'(by omega)) (R[R.length - 1]'(by omega)) →
      ∀ (i k : ℕ) (hi : i < R.length) (hk : k < R.length),
        H.Adj (R[i]'hi) (R[k]'hk) → (k = i + 1 ∨ i = k + 1) := by
    intro R hR3 htR hnbrR hnadjR i k hi hk hadj
    have hint : ∀ (a b : ℕ) (ha : a < R.length) (hb : b < R.length), 0 < a → a + 1 < R.length →
        H.Adj (R[a]'ha) (R[b]'hb) → (b + 1 = a ∨ b = a + 1) := by
      intro a b ha hb h0 h1 hab
      obtain ⟨j, hja⟩ : ∃ j, a = j + 1 := ⟨a - 1, by omega⟩
      have hj2 : j + 2 < R.length := by omega
      have hmem : (R[b]'hb) ∈ H.neighborSet (R[j + 1]'(by omega)) := by
        have heq : (R[j + 1]'(by omega)) = (R[a]'ha) :=
          SubdivisionCounting.getElem_eq_of_index_eq R hja.symm (by omega) ha
        rw [heq]; exact hab
      rw [hnbrR j hj2] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · left; have := htR.2.1.getElem_inj_iff.mp h; omega
      · right; have := htR.2.1.getElem_inj_iff.mp h; omega
    by_cases hia : 0 < i ∧ i + 1 < R.length
    · rcases hint i k hi hk hia.1 hia.2 hadj with h | h
      · right; omega
      · left; omega
    · by_cases hkb : 0 < k ∧ k + 1 < R.length
      · rcases hint k i hk hi hkb.1 hkb.2 hadj.symm with h | h
        · left; omega
        · right; omega
      · exfalso
        have hik : i ≠ k := by
          intro h
          refine H.irrefl (v := R[i]'hi) ?_
          have heq : (R[k]'hk) = (R[i]'hi) :=
            SubdivisionCounting.getElem_eq_of_index_eq R h.symm hk hi
          rw [heq] at hadj
          exact hadj
        refine hnadjR ?_
        have hi' : i = 0 ∨ i = R.length - 1 := by omega
        have hk' : k = 0 ∨ k = R.length - 1 := by omega
        rcases hi' with h1 | h1 <;> rcases hk' with h2 | h2
        · exact absurd (show i = k by omega) hik
        · have g5 : (R[i]'hi) = (R[0]'(by omega)) :=
            SubdivisionCounting.getElem_eq_of_index_eq R h1 hi (by omega)
          have g6 : (R[k]'hk) = (R[R.length - 1]'(by omega)) :=
            SubdivisionCounting.getElem_eq_of_index_eq R h2 hk (by omega)
          rw [g5, g6] at hadj; exact hadj
        · have g5 : (R[i]'hi) = (R[R.length - 1]'(by omega)) :=
            SubdivisionCounting.getElem_eq_of_index_eq R h1 hi (by omega)
          have g6 : (R[k]'hk) = (R[0]'(by omega)) :=
            SubdivisionCounting.getElem_eq_of_index_eq R h2 hk (by omega)
          rw [g5, g6] at hadj; exact hadj.symm
        · exact absurd (show i = k by omega) hik
  have hconsecP := hconsec P hP htP hnbrP (by rw [hx, hy]; exact hnadjP)
  have hconsecQ := hconsec Q hQ htQ hnbrQ (by rw [hz, hw]; exact hnadjQ)
  -- **`H` is a subdivision of `K₄` with branch-vertices `x, y, z, w`.**
  obtain ⟨ι, hι0, hι1, hι2, hι3⟩ : ∃ f : Fin 4 → W, f 0 = x ∧ f 1 = y ∧ f 2 = z ∧ f 3 = w :=
    ⟨fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w,
      by simp, by simp, by simp, by simp⟩
  obtain ⟨T, hT01, hT10, hT23, hT32, hTgen⟩ : ∃ g : Fin 4 → Fin 4 → List W,
      g 0 1 = P ∧ g 1 0 = P.reverse ∧ g 2 3 = Q ∧ g 3 2 = Q.reverse ∧
      ∀ i j : Fin 4, ¬(i = 0 ∧ j = 1) → ¬(i = 1 ∧ j = 0) → ¬(i = 2 ∧ j = 3) →
        ¬(i = 3 ∧ j = 2) → g i j = [ι i, ι j] :=
    ⟨fun i j => if i = 0 ∧ j = 1 then P else if i = 1 ∧ j = 0 then P.reverse
      else if i = 2 ∧ j = 3 then Q else if i = 3 ∧ j = 2 then Q.reverse else [ι i, ι j],
      by simp, by simp, by simp, by simp,
      by intro i j h1 h2 h3 h4; simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]⟩
  have hficases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hcases : ∀ u v : Fin 4, ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∨
      ((u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)) ∨
      (¬(u = 0 ∧ v = 1) ∧ ¬(u = 1 ∧ v = 0) ∧ ¬(u = 2 ∧ v = 3) ∧ ¬(u = 3 ∧ v = 2)) := by
    intro u v
    by_cases h1 : u = 0 ∧ v = 1
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : u = 1 ∧ v = 0
      · exact Or.inl (Or.inr h2)
      · by_cases h3 : u = 2 ∧ v = 3
        · exact Or.inr (Or.inl (Or.inl h3))
        · by_cases h4 : u = 3 ∧ v = 2
          · exact Or.inr (Or.inl (Or.inr h4))
          · exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)
  have hadjgen : ∀ u v : Fin 4, u ≠ v → ¬(u = 0 ∧ v = 1) → ¬(u = 1 ∧ v = 0) →
      ¬(u = 2 ∧ v = 3) → ¬(u = 3 ∧ v = 2) → H.Adj (ι u) (ι v) := by
    intro u v huv h1 h2 h3 h4
    rcases hficases u with rfl | rfl | rfl | rfl <;>
      rcases hficases v with rfl | rfl | rfl | rfl <;>
      simp only [hι0, hι1, hι2, hι3] <;>
      first
        | exact absurd rfl huv
        | exact absurd ⟨rfl, rfl⟩ h1
        | exact absurd ⟨rfl, rfl⟩ h2
        | exact absurd ⟨rfl, rfl⟩ h3
        | exact absurd ⟨rfl, rfl⟩ h4
        | exact e1 | exact e2 | exact e3 | exact e4
        | exact e1.symm | exact e2.symm | exact e3.symm | exact e4.symm
  have hinj : Function.Injective ι := by
    have hne : ∀ u v : Fin 4, u ≠ v → ι u ≠ ι v := by
      intro u v huv
      rcases hficases u with rfl | rfl | rfl | rfl <;>
        rcases hficases v with rfl | rfl | rfl | rfl <;>
        simp only [hι0, hι1, hι2, hι3] <;>
        first
          | exact absurd rfl huv
          | exact dxy | exact dxz | exact dxw | exact dyz | exact dyw | exact dzw
          | exact dxy.symm | exact dxz.symm | exact dxw.symm | exact dyz.symm
          | exact dyw.symm | exact dzw.symm
    intro u v h
    by_contra huv
    exact hne u v huv h
  have hpairtrack : ∀ a b : W, H.Adj a b → IsTrackFrom H [a, b] a b := by
    intro a b hab
    refine ⟨⟨by simp, by simp [hab.ne], ?_⟩, by simp, by simp⟩
    intro i hi
    have hi0 : i = 0 := by
      have h := hi; simp only [List.length_cons, List.length_nil] at h; omega
    subst hi0
    exact hab
  have hintpair : ∀ a b : W, trackInterior [a, b] = ([] : List W) := fun a b => rfl
  have hpairedge : ∀ a b : W, s(a, b) ∈ trackEdges [a, b] := fun a b => ⟨0, by simp, rfl⟩
  have hPint : ∀ t ∈ trackInterior P, t ∈ P ∧ t ≠ x ∧ t ≠ y := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := (SubdivisionCounting.mem_trackInterior_iff P t).mp ht
    refine ⟨?_, ?_, ?_⟩
    · rw [← hjt]; exact List.getElem_mem _
    · rw [← hjt, ← hx]; intro hc; have := htP.2.1.getElem_inj_iff.mp hc; omega
    · rw [← hjt, ← hy]; intro hc; have := htP.2.1.getElem_inj_iff.mp hc; omega
  have hQint : ∀ t ∈ trackInterior Q, t ∈ Q ∧ t ≠ z ∧ t ≠ w := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := (SubdivisionCounting.mem_trackInterior_iff Q t).mp ht
    refine ⟨?_, ?_, ?_⟩
    · rw [← hjt]; exact List.getElem_mem _
    · rw [← hjt, ← hz]; intro hc; have := htQ.2.1.getElem_inj_iff.mp hc; omega
    · rw [← hjt, ← hw]; intro hc; have := htQ.2.1.getElem_inj_iff.mp hc; omega
  have hPintι : ∀ t ∈ trackInterior P, ∀ i : Fin 4, t ≠ ι i := by
    intro t ht i
    obtain ⟨htP', htx, hty⟩ := hPint t ht
    rcases hficases i with rfl | rfl | rfl | rfl
    · rw [hι0]; exact htx
    · rw [hι1]; exact hty
    · rw [hι2]; intro hc; exact hzP (hc ▸ htP')
    · rw [hι3]; intro hc; exact hwP (hc ▸ htP')
  have hQintι : ∀ t ∈ trackInterior Q, ∀ i : Fin 4, t ≠ ι i := by
    intro t ht i
    obtain ⟨htQ', htz, htw⟩ := hQint t ht
    rcases hficases i with rfl | rfl | rfl | rfl
    · rw [hι0]; intro hc; exact hxQ (hc ▸ htQ')
    · rw [hι1]; intro hc; exact hyQ (hc ▸ htQ')
    · rw [hι2]; exact htz
    · rw [hι3]; exact htw
  have hPnotmem : ∀ (u' v' : Fin 4), ¬((u' = 0 ∧ v' = 1) ∨ (u' = 1 ∧ v' = 0)) →
      ∀ t ∈ trackInterior P, t ∉ T u' v' := by
    intro u' v' hnot t ht
    obtain ⟨htP', htx, hty⟩ := hPint t ht
    rcases hcases u' v' with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · exact absurd (Or.inl ⟨hu, hv⟩) hnot
    · exact absurd (Or.inr ⟨hu, hv⟩) hnot
    · subst hu; subst hv; rw [hT23]; exact hdisj t htP'
    · subst hu; subst hv; rw [hT32, List.mem_reverse]; exact hdisj t htP'
    · rw [hTgen u' v' g1 g2 g3 g4]
      intro hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h
      · exact hPintι t ht u' h
      · exact hPintι t ht v' h
  have hQnotmem : ∀ (u' v' : Fin 4), ¬((u' = 2 ∧ v' = 3) ∨ (u' = 3 ∧ v' = 2)) →
      ∀ t ∈ trackInterior Q, t ∉ T u' v' := by
    intro u' v' hnot t ht
    obtain ⟨htQ', htz, htw⟩ := hQint t ht
    rcases hcases u' v' with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv; rw [hT01]; exact fun hc => hdisj t hc htQ'
    · subst hu; subst hv; rw [hT10, List.mem_reverse]; exact fun hc => hdisj t hc htQ'
    · exact absurd (Or.inl ⟨hu, hv⟩) hnot
    · exact absurd (Or.inr ⟨hu, hv⟩) hnot
    · rw [hTgen u' v' g1 g2 g3 g4]
      intro hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h
      · exact hQintι t ht u' h
      · exact hQintι t ht v' h
  -- the eight clauses
  have htrackall : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
      IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    have huv' : u ≠ v := huv
    rcases hcases u v with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv; rw [hT01, hι0, hι1]; exact hPtrack
    · subst hu; subst hv; rw [hT10, hι0, hι1]; exact TrackSlice.isTrackFrom_reverse hPtrack
    · subst hu; subst hv; rw [hT23, hι2, hι3]; exact hQtrack
    · subst hu; subst hv; rw [hT32, hι2, hι3]; exact TrackSlice.isTrackFrom_reverse hQtrack
    · rw [hTgen u v g1 g2 g3 g4]; exact hpairtrack _ _ (hadjgen u v huv' g1 g2 g3 g4)
  have htesub : ∀ q : List W, IsTrackList H q → trackEdges q ⊆ H.edgeSet := by
    rintro q hq e ⟨i, hi, rfl⟩
    exact hq.2.2 i hi
  refine ⟨ι, T, hinj, htrackall, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every track has at least one edge
    intro u v huv
    rcases hcases u v with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv; rw [hT01]; show 1 ≤ P.length - 1; omega
    · subst hu; subst hv; rw [hT10]; show 1 ≤ P.reverse.length - 1
      rw [List.length_reverse]; omega
    · subst hu; subst hv; rw [hT23]; show 1 ≤ Q.length - 1; omega
    · subst hu; subst hv; rw [hT32]; show 1 ≤ Q.reverse.length - 1
      rw [List.length_reverse]; omega
    · rw [hTgen u v g1 g2 g3 g4]; show 1 ≤ [ι u, ι v].length - 1; simp
  · -- reversing the edge reverses the track
    intro u v huv
    rcases hcases u v with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv; rw [hT01, hT10]
    · subst hu; subst hv; rw [hT10, hT01, List.reverse_reverse]
    · subst hu; subst hv; rw [hT23, hT32]
    · subst hu; subst hv; rw [hT32, hT23, List.reverse_reverse]
    · rw [hTgen u v g1 g2 g3 g4,
        hTgen v u (fun hh => g2 ⟨hh.2, hh.1⟩) (fun hh => g1 ⟨hh.2, hh.1⟩)
          (fun hh => g4 ⟨hh.2, hh.1⟩) (fun hh => g3 ⟨hh.2, hh.1⟩)]
      rfl
  · -- the tracks are disjoint except for their ends
    intro u v u' v' huv hu'v' hne t ht
    rcases hcases u v with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv
      rw [hT01] at ht
      refine hPnotmem u' v' ?_ t ht
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · exact hne Sym2.eq_swap
    · subst hu; subst hv
      rw [hT10, TrackSlice.trackInterior_reverse, List.mem_reverse] at ht
      refine hPnotmem u' v' ?_ t ht
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne Sym2.eq_swap
      · exact hne rfl
    · subst hu; subst hv
      rw [hT23] at ht
      refine hQnotmem u' v' ?_ t ht
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · exact hne Sym2.eq_swap
    · subst hu; subst hv
      rw [hT32, TrackSlice.trackInterior_reverse, List.mem_reverse] at ht
      refine hQnotmem u' v' ?_ t ht
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne Sym2.eq_swap
      · exact hne rfl
    · rw [hTgen u v g1 g2 g3 g4, hintpair] at ht
      simp at ht
  · -- no internal vertex of a track is a branch-vertex
    intro u v huv t ht hrange
    obtain ⟨i, hi⟩ := hrange
    rcases hcases u v with (⟨hu, hv⟩ | ⟨hu, hv⟩) | (⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨g1, g2, g3, g4⟩
    · subst hu; subst hv; rw [hT01] at ht; exact hPintι t ht i hi.symm
    · subst hu; subst hv
      rw [hT10, TrackSlice.trackInterior_reverse, List.mem_reverse] at ht
      exact hPintι t ht i hi.symm
    · subst hu; subst hv; rw [hT23] at ht; exact hQintι t ht i hi.symm
    · subst hu; subst hv
      rw [hT32, TrackSlice.trackInterior_reverse, List.mem_reverse] at ht
      exact hQintι t ht i hi.symm
    · rw [hTgen u v g1 g2 g3 g4, hintpair] at ht; simp at ht
  · -- the six tracks cover every vertex
    intro t
    rcases hcov t with htP' | htQ'
    · rcases hPidx t htP' with h | h | ⟨j, hj, hjt⟩
      · exact Or.inl ⟨0, by rw [hι0]; exact h⟩
      · exact Or.inl ⟨1, by rw [hι1]; exact h⟩
      · refine Or.inr ⟨0, 1, by decide, ?_⟩
        rw [hT01, ← hjt]
        exact SubdivisionCounting.mem_trackInterior_getElem P j hj
    · rcases hQidx t htQ' with h | h | ⟨j, hj, hjt⟩
      · exact Or.inl ⟨2, by rw [hι2]; exact h⟩
      · exact Or.inl ⟨3, by rw [hι3]; exact h⟩
      · refine Or.inr ⟨2, 3, by decide, ?_⟩
        rw [hT23, ← hjt]
        exact SubdivisionCounting.mem_trackInterior_getElem Q j hj
  · -- the six tracks carry exactly the edges of `H`
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      constructor
      · intro hab'
        have hab : H.Adj a b := hab'
        simp only [Set.mem_iUnion]
        rcases hcov a with haP | haQ
        · rcases hcov b with hbP | hbQ
          · obtain ⟨i, hi, hia⟩ := List.getElem_of_mem haP
            obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hbP
            refine ⟨0, 1, by decide, ?_⟩
            rw [hT01]
            rcases hconsecP i k hi hk (by rw [hia, hkb]; exact hab) with h | h
            · have hb' : b = (P[i + 1]'(by omega)) := by
                rw [← hkb]
                exact SubdivisionCounting.getElem_eq_of_index_eq P h (by omega) (by omega)
              exact ⟨i, by omega, by rw [← hia, hb']⟩
            · have ha' : a = (P[k + 1]'(by omega)) := by
                rw [← hia]
                exact SubdivisionCounting.getElem_eq_of_index_eq P h (by omega) (by omega)
              exact ⟨k, by omega, by rw [ha', ← hkb]; exact Sym2.eq_swap⟩
          · obtain ⟨ha', hb'⟩ := hcross a b haP hbQ hab
            rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
            · exact ⟨0, 2, by decide, by
                rw [hTgen 0 2 (by decide) (by decide) (by decide) (by decide), hι0, hι2]
                exact hpairedge _ _⟩
            · exact ⟨0, 3, by decide, by
                rw [hTgen 0 3 (by decide) (by decide) (by decide) (by decide), hι0, hι3]
                exact hpairedge _ _⟩
            · exact ⟨1, 2, by decide, by
                rw [hTgen 1 2 (by decide) (by decide) (by decide) (by decide), hι1, hι2]
                exact hpairedge _ _⟩
            · exact ⟨1, 3, by decide, by
                rw [hTgen 1 3 (by decide) (by decide) (by decide) (by decide), hι1, hι3]
                exact hpairedge _ _⟩
        · rcases hcov b with hbP | hbQ
          · obtain ⟨hb', ha'⟩ := hcross b a hbP haQ hab.symm
            rcases hb' with rfl | rfl <;> rcases ha' with rfl | rfl
            · exact ⟨0, 2, by decide, by
                rw [hTgen 0 2 (by decide) (by decide) (by decide) (by decide), hι0, hι2,
                  Sym2.eq_swap]
                exact hpairedge _ _⟩
            · exact ⟨0, 3, by decide, by
                rw [hTgen 0 3 (by decide) (by decide) (by decide) (by decide), hι0, hι3,
                  Sym2.eq_swap]
                exact hpairedge _ _⟩
            · exact ⟨1, 2, by decide, by
                rw [hTgen 1 2 (by decide) (by decide) (by decide) (by decide), hι1, hι2,
                  Sym2.eq_swap]
                exact hpairedge _ _⟩
            · exact ⟨1, 3, by decide, by
                rw [hTgen 1 3 (by decide) (by decide) (by decide) (by decide), hι1, hι3,
                  Sym2.eq_swap]
                exact hpairedge _ _⟩
          · obtain ⟨i, hi, hia⟩ := List.getElem_of_mem haQ
            obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hbQ
            refine ⟨2, 3, by decide, ?_⟩
            rw [hT23]
            rcases hconsecQ i k hi hk (by rw [hia, hkb]; exact hab) with h | h
            · have hb' : b = (Q[i + 1]'(by omega)) := by
                rw [← hkb]
                exact SubdivisionCounting.getElem_eq_of_index_eq Q h (by omega) (by omega)
              exact ⟨i, by omega, by rw [← hia, hb']⟩
            · have ha' : a = (Q[k + 1]'(by omega)) := by
                rw [← hia]
                exact SubdivisionCounting.getElem_eq_of_index_eq Q h (by omega) (by omega)
              exact ⟨k, by omega, by rw [ha', ← hkb]; exact Sym2.eq_swap⟩
      · intro he
        simp only [Set.mem_iUnion] at he
        obtain ⟨u, v, huv, hmem⟩ := he
        exact htesub _ (htrackall u v huv).1 hmem

end Workspace.ProofLemmas.NoCrossTrackBranch
