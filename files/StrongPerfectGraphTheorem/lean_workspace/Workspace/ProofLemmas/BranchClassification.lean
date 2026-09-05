import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# The branches of a subdivision are exactly its subdividing tracks

PAPER (printed pp. 19–20): *"the effect of repeatedly subdividing edges is to replace each edge
of `J` by a track joining the same pair of vertices, where these tracks are disjoint except for
their ends"*, together with *"a branch of `H` means a maximal track `P` in `H` such that no
internal vertex of `P` is a branch-vertex"*.

The paper uses without comment the resulting identification — *"the branches of `H` are in 1-1
correspondence with the edges of `J`"* (printed p. 20) — every time it speaks of "the branch of
`H` between `u` and `v`" (5.7, 5.8, 6.1, 9.2, 9.3, …).  `Tracks.IsBranch` is the intrinsic
definition (maximal track without interior branch-vertices), so the identification has to be
proved.  That is what this module does, in the direction the proofs need: **every branch of `H`
has the same edge set as one of the subdividing tracks `T u v`**.

The argument is the obvious one.  Two consecutive edges of a branch `q` lie on the same track
`T u v`: otherwise the vertex between them lies on two different tracks, hence — the tracks
being disjoint except at their ends — is an *end* of its track, i.e. lies in the range of `ι`,
i.e. is a branch-vertex; but it is an interior vertex of `q`, contradiction.  So the whole of
`q` lies inside a single `T u v`, and maximality of `q` upgrades the inclusion of edge sets to
an equality.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.BranchClassification

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {U W : Type*}

/-- Both ends of an edge of a track are vertices of that track. -/
theorem mem_of_mem_trackEdges {t : List W} {a b : W} (h : s(a, b) ∈ trackEdges t) :
    a ∈ t ∧ b ∈ t := by
  obtain ⟨i, hi, hie⟩ := h
  rcases Sym2.eq_iff.mp hie with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
  · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩

/-- Every vertex of a track with at least two vertices is an end of one of its edges. -/
theorem exists_edge_of_mem {t : List W} (h2 : 2 ≤ t.length) {w : W} (hw : w ∈ t) :
    ∃ i : ℕ, ∃ hi : i + 1 < t.length, w = t[i]'(by omega) ∨ w = t[i + 1]'hi := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
  by_cases hlast : k + 1 < t.length
  · exact ⟨k, hlast, Or.inl (SubdivisionCounting.getElem_eq_of_index_eq t rfl _ _)⟩
  · have hk' : k = t.length - 1 := by omega
    refine ⟨k - 1, by omega, Or.inr ?_⟩
    exact SubdivisionCounting.getElem_eq_of_index_eq t (by omega) _ _

/-- **Every branch of a subdivision is one of the subdividing tracks.**

The hypotheses are the eight conjuncts of `Tracks.IsSubdivision J H` for the data `(ι, T)`,
together with the minimum-degree hypothesis `hdeg` that makes `Set.range ι` the set of
branch-vertices of `H` (it holds for every 3-connected `J`, in particular for `K₄`). -/
theorem exists_trackEdges_eq_of_isBranch [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) :
    ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (T u v) := by
  obtain ⟨hqtrack, hqint, hqmax⟩ := hq
  -- `branchVertices H = Set.range ι`
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  -- interior vertices of a subdividing track are not branch-vertices
  have hTint : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ branchVertices H :=
    fun u v huv w hw hb => hnew u v huv w hw (hbv₂ hb)
  -- every edge of `q` lies on some subdividing track
  have hedge : ∀ (i : ℕ) (hi : i + 1 < q.length),
      ∃ u v : U, J.Adj u v ∧ s(q[i]'(by omega), q[i + 1]'hi) ∈ trackEdges (T u v) := by
    intro i hi
    have hadj : H.Adj (q[i]'(by omega)) (q[i + 1]'hi) := hqtrack.2.2 i hi
    have hmem : s(q[i]'(by omega), q[i + 1]'hi) ∈ H.edgeSet := hadj
    rw [hedges] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, v, huv, hmem⟩ := hmem
    exact ⟨u, v, huv, hmem⟩
  obtain ⟨u₀, v₀, hu₀v₀, h0⟩ := hedge 0 (by omega)
  -- all edges of `q` lie on the *same* track `T u₀ v₀`
  have hall : ∀ (i : ℕ) (hi : i + 1 < q.length),
      s(q[i]'(by omega), q[i + 1]'hi) ∈ trackEdges (T u₀ v₀) := by
    intro i
    induction i with
    | zero => intro hi; exact h0
    | succ k ih =>
      intro hi
      have hk : k + 1 < q.length := by omega
      have hprev := ih hk
      obtain ⟨u, v, huv, hcur⟩ := hedge (k + 1) hi
      by_cases hsame : s(u, v) = s(u₀, v₀)
      · -- the two tracks are literally the same list, up to reversal
        rcases Sym2.eq_iff.mp hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcur
        · rw [hrev v u (huv.symm)] at hcur
          rwa [SubdivisionCounting.trackEdges_reverse] at hcur
      · exfalso
        -- the vertex between the two edges lies on both tracks
        have hmem₀ : q[k + 1]'hk ∈ T u₀ v₀ := (mem_of_mem_trackEdges hprev).2
        have hmem₁ : q[k + 1]'hk ∈ T u v := by
          have := (mem_of_mem_trackEdges hcur).1
          simpa using this
        have hnotint : q[k + 1]'hk ∉ trackInterior (T u₀ v₀) := fun hc =>
          hdisjint u₀ v₀ u v hu₀v₀ huv (Ne.symm hsame) _ hc hmem₁
        have hlen0 : 0 < (T u₀ v₀).length := by
          have := hlen u₀ v₀ hu₀v₀
          simp only [trackLength] at this
          omega
        have hends := DegenerateK4Tracks.mem_ends_of_notMem_interior hmem₀ hnotint hlen0
        have hrange : q[k + 1]'hk ∈ Set.range ι := by
          rcases hends with he | he
          · rw [he, SubdivisionCounting.track_head (htrack u₀ v₀ hu₀v₀) hlen0]
            exact ⟨u₀, rfl⟩
          · rw [he, DegenerateK4Tracks.track_getLast (htrack u₀ v₀ hu₀v₀) hlen0]
            exact ⟨v₀, rfl⟩
        exact hqint _ (SubdivisionCounting.mem_trackInterior_getElem q k (by omega))
          (hbv₁ hrange)
  -- hence `E(q) ⊆ E(T u₀ v₀)`
  have hsubE : trackEdges q ⊆ trackEdges (T u₀ v₀) := by
    rintro e ⟨i, hi, rfl⟩
    exact hall i hi
  -- and `V(q) ⊆ V(T u₀ v₀)`
  have hsubV : ∀ w ∈ q, w ∈ T u₀ v₀ := by
    intro w hw
    obtain ⟨i, hi, hcase⟩ := exists_edge_of_mem hq2 hw
    have := mem_of_mem_trackEdges (hall i hi)
    rcases hcase with rfl | rfl
    · exact this.1
    · exact this.2
  -- maximality of the branch upgrades the inclusion to an equality
  refine ⟨u₀, v₀, hu₀v₀, ?_⟩
  exact (hqmax (T u₀ v₀) (htrack u₀ v₀ hu₀v₀).1 (hTint u₀ v₀ hu₀v₀) hsubE hsubV).symm

/-- **A branch, together with the naming of its ends.**

Refines `exists_trackEdges_eq_of_isBranch` by identifying the two ends of the branch with the
two ends `ι u`, `ι v` of the subdividing track.  This is what turns 5.7/5.8/6.1's *"the branch
of `H` between `b₁` and `b₂`"* into a concrete track. -/
theorem exists_trackEdges_eq_and_ends [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) {d₁ d₂ : W}
    (hqe : IsTrackFrom H q d₁ d₂)
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H) :
    ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (T u v) ∧
      ((d₁ = ι u ∧ d₂ = ι v) ∨ (d₁ = ι v ∧ d₂ = ι u)) := by
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  obtain ⟨u, v, huv, hEq⟩ :=
    exists_trackEdges_eq_of_isBranch hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hq hq2
  have hlen0 : 0 < (T u v).length := by
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  have hhead : (T u v)[0]'hlen0 = ι u := SubdivisionCounting.track_head (htrack u v huv) hlen0
  have hlast : (T u v)[(T u v).length - 1]'(by omega) = ι v :=
    DegenerateK4Tracks.track_getLast (htrack u v huv) hlen0
  -- both ends of `q` lie on `T u v` and are branch-vertices, hence are its ends
  have key : ∀ d : W, d ∈ q → d ∈ branchVertices H → d = ι u ∨ d = ι v := by
    intro d hd hdb
    have hdT : d ∈ T u v := by
      obtain ⟨i, hi, hcase⟩ := exists_edge_of_mem hq2 hd
      have hmem : s(q[i]'(by omega), q[i + 1]'hi) ∈ trackEdges (T u v) := by
        rw [← hEq]; exact ⟨i, hi, rfl⟩
      have := mem_of_mem_trackEdges hmem
      rcases hcase with rfl | rfl
      · exact this.1
      · exact this.2
    have hnotint : d ∉ trackInterior (T u v) := fun hc =>
      hnew u v huv d hc (hbv₂ hdb)
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hdT hnotint hlen0 with he | he
    · exact Or.inl (by rw [he, hhead])
    · exact Or.inr (by rw [he, hlast])
  have hq0 : q[0]'(by omega) = d₁ := SubdivisionCounting.track_head hqe (by omega)
  have hqL : q[q.length - 1]'(by omega) = d₂ :=
    DegenerateK4Tracks.track_getLast hqe (by omega)
  have hd₁q : d₁ ∈ q := hq0 ▸ List.getElem_mem _
  have hd₂q : d₂ ∈ q := hqL ▸ List.getElem_mem _
  have hne : d₁ ≠ d₂ := by
    intro hcon
    have hnd : q.Nodup := hqe.1.2.1
    rw [← hq0, ← hqL] at hcon
    have := (List.Nodup.getElem_inj_iff hnd).mp hcon
    omega
  have huvne : ι u ≠ ι v := fun hcon => (huv.ne) (hι hcon)
  refine ⟨u, v, huv, hEq, ?_⟩
  rcases key d₁ hd₁q hd₁ with h₁ | h₁ <;> rcases key d₂ hd₂q hd₂ with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (h₁.trans h₂.symm) hne

/-- **A branch is determined by its two ends.**

Two branches of `H` with the same pair of ends (both of them branch-vertices) are the same
subgraph.  The paper uses this silently whenever it writes *"the branch of `H` between `u` and
`v`"* and then identifies it with a previously named track. -/
theorem trackEdges_eq_of_same_ends [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard)
    {q q' : List W} {d₁ d₂ d₁' d₂' : W}
    (hq : IsBranch H q) (hq2 : 2 ≤ q.length) (hqe : IsTrackFrom H q d₁ d₂)
    (hq' : IsBranch H q') (hq2' : 2 ≤ q'.length) (hqe' : IsTrackFrom H q' d₁' d₂')
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hmatch : (d₁' = d₁ ∧ d₂' = d₂) ∨ (d₁' = d₂ ∧ d₂' = d₁)) :
    trackEdges q = trackEdges q' := by
  have hd₁' : d₁' ∈ branchVertices H := by rcases hmatch with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    assumption
  have hd₂' : d₂' ∈ branchVertices H := by rcases hmatch with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;>
    assumption
  obtain ⟨u, v, huv, hE, hends⟩ :=
    exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisjint hnew hcover hedges hdeg
      hq hq2 hqe hd₁ hd₂
  obtain ⟨u', v', huv', hE', hends'⟩ :=
    exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisjint hnew hcover hedges hdeg
      hq' hq2' hqe' hd₁' hd₂'
  -- `T u v` and `T u' v'` are the same track, up to reversal
  have hTeq : trackEdges (T u v) = trackEdges (T u' v') := by
    have hswap : ∀ a b : U, J.Adj a b → trackEdges (T b a) = trackEdges (T a b) := by
      intro a b hab
      rw [hrev a b hab, SubdivisionCounting.trackEdges_reverse]
    -- match up the four labels through `ι`'s injectivity
    have hpair : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
      rcases hmatch with ⟨hm₁, hm₂⟩ | ⟨hm₁, hm₂⟩ <;>
        rcases hends with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases hends' with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
      · exact Or.inl ⟨hι (f₁.symm.trans (hm₁.trans e₁)), hι (f₂.symm.trans (hm₂.trans e₂))⟩
      · exact Or.inr ⟨hι (f₂.symm.trans (hm₂.trans e₂)), hι (f₁.symm.trans (hm₁.trans e₁))⟩
      · exact Or.inr ⟨hι (f₁.symm.trans (hm₁.trans e₁)), hι (f₂.symm.trans (hm₂.trans e₂))⟩
      · exact Or.inl ⟨hι (f₂.symm.trans (hm₂.trans e₂)), hι (f₁.symm.trans (hm₁.trans e₁))⟩
      · exact Or.inr ⟨hι (f₁.symm.trans (hm₁.trans e₂)), hι (f₂.symm.trans (hm₂.trans e₁))⟩
      · exact Or.inl ⟨hι (f₂.symm.trans (hm₂.trans e₁)), hι (f₁.symm.trans (hm₁.trans e₂))⟩
      · exact Or.inl ⟨hι (f₁.symm.trans (hm₁.trans e₂)), hι (f₂.symm.trans (hm₂.trans e₁))⟩
      · exact Or.inr ⟨hι (f₂.symm.trans (hm₂.trans e₁)), hι (f₁.symm.trans (hm₁.trans e₂))⟩
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hswap u' v' huv'
  rw [hE, hTeq, ← hE']

end Workspace.ProofLemmas.BranchClassification
