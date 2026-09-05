import Workspace.ProofLemmas.Thm57Claim2ConnCore
import Workspace.ProofLemmas.Thm55Connectivity

/-! # The two routes around the window in 5.7 (2)

PAPER (printed p. 23): *"Choose a branch-vertex `b` … and choose three paths `P₁,P₂,P₃`
between `b` and `c₁,c₂,a` respectively, pairwise disjoint except for `b`."*

We do not build the three paths.  What the parity calculation uses is only their two unions:
a track `R` from `c₁` to `c₂` missing `a`, and a track `S` from `c₁` to `a` missing `c₂`, both
avoiding the window and the two edges at `a`.  In the subdivision picture `c₁ = ι c`,
`c₂ = ι d` and `a = ι z`, and the two tracks are lifted from walks of `J` given by 5.5's
elementary connectivity lemmas: a walk from `c` to `d` in `J` with the vertex `z` and the edge
`cd` deleted, and a walk from `c` to `z` in `J` with the vertex `d` and the edge `cz` deleted.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Routes

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch
open Workspace.ProofLemmas.Thm57Claim2ConnCore
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

section Data

variable {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W} {ι : Fin n → W}
  {T : Fin n → Fin n → List W}

/-- An edge of `J` between two branch-vertices lies on no other subdividing track. -/
theorem edge_not_mem_other_track (hS : SubData J H ι T)
    {p q x y : Fin n} (hpq : J.Adj p q) (hxy : J.Adj x y) (hne : s(x, y) ≠ s(p, q)) :
    s(ι p, ι q) ∉ trackEdges (T x y) := by
  intro hmem
  have hp : ι p ∈ T x y :=
    Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem |>.1
  have hq : ι q ∈ T x y :=
    Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem |>.2
  have hends : ∀ {w : Fin n}, ι w ∈ T x y → ι w = ι x ∨ ι w = ι y := by
    intro w hw
    refine Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (hS.track x y hxy).2.1 (hS.track x y hxy).2.2 hw ?_
    intro hint
    exact hS.new x y hxy _ hint ⟨w, rfl⟩
  have h1 := hends hp
  have h2 := hends hq
  apply hne
  have hpq' : ι p ≠ ι q := fun h => hpq.ne (hS.inj h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hpq'
  · exact Sym2.eq_iff.mpr (Or.inl ⟨(hS.inj h1).symm, (hS.inj h2).symm⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨(hS.inj h2).symm, (hS.inj h1).symm⟩)
  · exact absurd (h1.trans h2.symm) hpq'

/-- A branch-vertex on a track is one of its two ends. -/
theorem branch_end_of_mem (hS : SubData J H ι T) {x y w : Fin n} (hxy : J.Adj x y)
    (hw : ι w ∈ T x y) : w = x ∨ w = y := by
  have h := Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
    (hS.track x y hxy).2.1 (hS.track x y hxy).2.2 hw
    (fun hint => hS.new x y hxy _ hint ⟨w, rfl⟩)
  rcases h with h | h
  · exact Or.inl (hS.inj h)
  · exact Or.inr (hS.inj h)

variable (hJ : IsKConnected J 3) (hS : SubData J H ι T)

section Branch

variable {B : List W} (hB : IsBranch H B) (hL : 2 ≤ B.length)
  {c d : Fin n} (hcd : J.Adj c d)
  (hc : ι c = B[0]'(by omega)) (hd : ι d = B[B.length - 1]'(by omega))
  (hE : trackEdges (T c d) = trackEdges B)

include hJ hS hB hL hcd hc hd hE

/-- The interior of the branch is the interior of the track carrying it. -/
theorem interior_subset_track : ∀ w ∈ trackInterior B, w ∈ trackInterior (T c d) := by
  intro w hw
  have hwB : w ∈ B :=
    ((List.dropLast_sublist _).trans (List.tail_sublist B)).subset hw
  have hwT : w ∈ T c d := mem_of_trackEdges_eq hL hE.symm hwB
  have hfrom : IsTrackFrom H B (B[0]'(by omega)) (B[B.length - 1]'(by omega)) :=
    Workspace.ProofLemmas.Thm57Claim2Structure.branch_from_ends hB hL
  have hout := Workspace.ProofLemmas.Thm57Claim2DeletedWindow.ends_outside hfrom
  by_contra hcon
  rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
    (hS.track c d hcd).2.1 (hS.track c d hcd).2.2 hwT hcon with h | h
  · exact hout.1 (by rw [← hc, ← h]; exact hw)
  · exact hout.2 (by rw [← hd, ← h]; exact hw)

/-- Vertices of a different subdividing track stay outside the branch's interior. -/
theorem mem_track_not_interior {x y : Fin n} (hxy : J.Adj x y) (hne : s(x, y) ≠ s(c, d))
    {w : W} (hw : w ∈ T x y) : w ∉ trackInterior B := by
  intro hint
  exact hS.disj c d x y hcd hxy (Ne.symm hne) w
    (interior_subset_track hJ hS hB hL hcd hc hd hE w hint) hw

end Branch

end Data


/-! ### A track of the graph with some edges deleted -/

theorem isTrackList_of_deleteEdges {G : SimpleGraph W} {F : Set (Sym2 W)} {q : List W}
    (hq : IsTrackList (G.deleteEdges F) q) :
    IsTrackList G q ∧ ∀ e ∈ trackEdges q, e ∉ F := by
  refine ⟨⟨hq.1, hq.2.1, fun i h => (SimpleGraph.deleteEdges_adj.mp (hq.2.2 i h)).1⟩, ?_⟩
  rintro e ⟨i, hi, rfl⟩
  exact (SimpleGraph.deleteEdges_adj.mp (hq.2.2 i hi)).2

/-! ### The two routes -/

section Routes

variable {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W} {ι : Fin n → W}
  {T : Fin n → Fin n → List W} {B : List W} {c d z : Fin n}

/-- **The route from `c₁` to `c₂` avoiding `a`.** -/
theorem exists_route_cd (hJ : IsKConnected J 3) (hS : SubData J H ι T)
    (hB : IsBranch H B) (hL : 2 ≤ B.length) (hcd : J.Adj c d)
    (hc : ι c = B[0]'(by omega)) (hd : ι d = B[B.length - 1]'(by omega))
    (hE : trackEdges (T c d) = trackEdges B) (hzc : z ≠ c) (hzd : z ≠ d) :
    ∃ R : List W, IsTrackFrom H R (ι c) (ι d) ∧
      (∀ w ∈ R, w ∉ trackInterior B) ∧ ι z ∉ R := by
  classical
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  set X : Set W := {w : W | w ∉ trackInterior B ∧ w ≠ ι z} with hXdef
  have hmemX : ∀ x : Fin n, x ≠ z → ι x ∈ X := by
    intro x hx
    refine ⟨fun hint => hB.2.1 _ hint (by rw [hbr]; exact ⟨x, rfl⟩), ?_⟩
    intro h
    exact hx (hS.inj h)
  have hedgeX : ∀ x y : Fin n, x ≠ z → y ≠ z → J.Adj x y → s(x, y) ≠ s(c, d) →
      RchIn H X (ι x) (ι y) := by
    intro x y hx hy hxy hne
    refine rchIn_of_chain (T x y) (List.isChain_iff_getElem.mpr (hS.track x y hxy).1.2.2) ?_
      (List.mem_of_head? (hS.track x y hxy).2.1)
      (List.mem_of_getLast? (hS.track x y hxy).2.2)
    intro t ht
    refine ⟨mem_track_not_interior hJ hS hB hL hcd hc hd hE hxy hne ht, ?_⟩
    intro htz
    rcases branch_end_of_mem hS hxy (htz ▸ ht) with h | h
    · exact hx h.symm
    · exact hy h.symm
  have hcz' : c ≠ z := fun h => hzc h.symm
  have hdz' : d ≠ z := fun h => hzd h.symm
  let c' : ↥(({z} : Set (Fin n))ᶜ) := ⟨c, by simpa using hcz'⟩
  let d' : ↥(({z} : Set (Fin n))ᶜ) := ⟨d, by simpa using hdz'⟩
  have hKconn :=
    Workspace.ProofLemmas.Thm55Connectivity.connected_induce_compl_singleton_delete_edge
      hJ z c' d'
  obtain ⟨p⟩ := hKconn.preconnected c' d'
  have hrch : RchIn H X (ι c) (ι d) := by
    refine rchIn_of_walk (fun x : ↥(({z} : Set (Fin n))ᶜ) => ι (x : Fin n)) ?_ ?_ p
    · intro x
      exact hmemX x x.2
    · intro x y hxy
      rw [SimpleGraph.deleteEdges_adj] at hxy
      refine hedgeX _ _ x.2 y.2 hxy.1 ?_
      intro heq
      refine hxy.2 ?_
      simp only [Set.mem_singleton_iff]
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
  obtain ⟨q, hq⟩ := walk_of_rchIn hrch
  obtain ⟨R, hR, hRsub, -⟩ := exists_track_of_walk q
  exact ⟨R, hR, fun w hw => (hq _ (hRsub _ hw)).1,
    fun hmem => ((hq _ (hRsub _ hmem)).2) rfl⟩

/-- **The route from `c₁` to `a` avoiding `c₂` and the edge `c₁a`.** -/
theorem exists_route_cz (hJ : IsKConnected J 3) (hS : SubData J H ι T)
    (hB : IsBranch H B) (hL : 2 ≤ B.length) (hcd : J.Adj c d) (hcz : J.Adj c z)
    (hc : ι c = B[0]'(by omega)) (hd : ι d = B[B.length - 1]'(by omega))
    (hE : trackEdges (T c d) = trackEdges B) (hzd : z ≠ d) :
    ∃ S : List W, IsTrackFrom H S (ι c) (ι z) ∧
      (∀ w ∈ S, w ∉ trackInterior B) ∧ ι d ∉ S ∧ s(ι c, ι z) ∉ trackEdges S := by
  classical
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  set H₀ : SimpleGraph W := H.deleteEdges {s(ι c, ι z)} with hH₀
  set X : Set W := {w : W | w ∉ trackInterior B ∧ w ≠ ι d} with hXdef
  have hmemX : ∀ x : Fin n, x ≠ d → ι x ∈ X := by
    intro x hx
    refine ⟨fun hint => hB.2.1 _ hint (by rw [hbr]; exact ⟨x, rfl⟩), ?_⟩
    intro h
    exact hx (hS.inj h)
  have hedgeX : ∀ x y : Fin n, x ≠ d → y ≠ d → J.Adj x y → s(x, y) ≠ s(c, z) →
      RchIn H₀ X (ι x) (ι y) := by
    intro x y hx hy hxy hne
    have hnotcd : s(x, y) ≠ s(c, d) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hy h2
      · exact hx h1
    have hchain : List.IsChain H₀.Adj (T x y) := by
      refine List.isChain_iff_getElem.mpr ?_
      intro i hi
      refine SimpleGraph.deleteEdges_adj.mpr ⟨(hS.track x y hxy).1.2.2 i hi, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      exact edge_not_mem_other_track hS hcz hxy hne (heq ▸ ⟨i, hi, rfl⟩)
    refine rchIn_of_chain (T x y) hchain ?_
      (List.mem_of_head? (hS.track x y hxy).2.1)
      (List.mem_of_getLast? (hS.track x y hxy).2.2)
    intro t ht
    refine ⟨mem_track_not_interior hJ hS hB hL hcd hc hd hE hxy hnotcd ht, ?_⟩
    intro htd
    rcases branch_end_of_mem hS hxy (htd ▸ ht) with h | h
    · exact hx h.symm
    · exact hy h.symm
  have hcd' : c ≠ d := hcd.ne
  let c' : ↥(({d} : Set (Fin n))ᶜ) := ⟨c, by simpa using hcd'⟩
  let z' : ↥(({d} : Set (Fin n))ᶜ) := ⟨z, by simpa using hzd⟩
  have hKconn :=
    Workspace.ProofLemmas.Thm55Connectivity.connected_induce_compl_singleton_delete_edge
      hJ d c' z'
  obtain ⟨p⟩ := hKconn.preconnected c' z'
  have hrch : RchIn H₀ X (ι c) (ι z) := by
    refine rchIn_of_walk (fun x : ↥(({d} : Set (Fin n))ᶜ) => ι (x : Fin n)) ?_ ?_ p
    · intro x
      exact hmemX x x.2
    · intro x y hxy
      rw [SimpleGraph.deleteEdges_adj] at hxy
      refine hedgeX _ _ x.2 y.2 hxy.1 ?_
      intro heq
      refine hxy.2 ?_
      simp only [Set.mem_singleton_iff]
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
  obtain ⟨q, hq⟩ := walk_of_rchIn hrch
  obtain ⟨S, hSt, hSsub, -⟩ := exists_track_of_walk q
  obtain ⟨hlist, hnoedge⟩ := isTrackList_of_deleteEdges hSt.1
  refine ⟨S, ⟨hlist, hSt.2.1, hSt.2.2⟩, fun w hw => (hq _ (hSsub _ hw)).1,
    fun hmem => ((hq _ (hSsub _ hmem)).2) rfl, ?_⟩
  intro hedge
  exact hnoedge _ hedge rfl

end Routes

/-! ### The window is the whole branch -/

section Forcing

variable {H : SimpleGraph W} {B : List W}

/-- Every neighbour of an internal vertex of a branch is one of its two neighbours on the
branch. -/
theorem neighbor_of_internal (hB : IsBranch H B) {k : ℕ} (hk0 : 0 < k) (hk : k + 1 < B.length)
    {w : W} (hadj : H.Adj (B[k]'(by omega)) w) :
    w = B[k - 1]'(by omega) ∨ w = B[k + 1]'hk := by
  obtain ⟨l, hl, hel⟩ :=
    Workspace.ProofLemmas.Thm57Claim2Structure.incidentEdges_internal_subset hB hk0 hk
      ⟨hadj, Sym2.mem_mk_left _ _⟩
  rcases Sym2.eq_iff.mp hel with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hkl : k = l := hB.1.2.1.getElem_inj_iff.mp h1
    exact Or.inr (h2.trans (getElem_eq_of_index_eq B (show l + 1 = k + 1 by omega) _ _))
  · have hkl : k = l + 1 := hB.1.2.1.getElem_inj_iff.mp h1
    exact Or.inl (h2.trans (getElem_eq_of_index_eq B (show l = k - 1 by omega) _ _))

/-- The two ends of a branch with at least two edges are nonadjacent. -/
theorem ends_not_adj (hc3 : CyclicallyThreeConnected H) (hB : IsBranch H B)
    (hL : 3 ≤ B.length) :
    ¬ H.Adj (B[0]'(by omega)) (B[B.length - 1]'(by omega)) := by
  obtain ⟨n, J, hJ, hsubdiv⟩ := hc3
  exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H hsubdiv B _ _ hB
    (Workspace.ProofLemmas.Thm57Claim2Structure.branch_from_ends hB (by omega))
    (by unfold trackLength; omega)).2.2.2

/-- An edge of the branch inside the window is an edge of the window. -/
theorem slice_edge (B : List W) {i j k : ℕ} (hj : j < B.length) (hik : i ≤ k) (hkj : k < j) :
    s(B[k]'(by omega), B[k + 1]'(by omega)) ∈ trackEdges (slice B i j) := by
  have hlen := length_slice B hj (show i ≤ j by omega)
  refine ⟨k - i, by omega, ?_⟩
  rw [getElem_slice B (by omega) (show i + (k - i) < B.length by omega),
    getElem_slice B (by omega)
      (show i + (k - i + 1) < B.length by omega),
    getElem_eq_of_index_eq B (show i + (k - i) = k by omega) _ _,
    getElem_eq_of_index_eq B (show i + (k - i + 1) = k + 1 by omega) _ _]

/-- **The window of 5.7 (2) with a common neighbour is a whole branch.**

PAPER (printed p. 23): *"and so `C = B` and `c₁,c₂` are branch-vertices"*. -/
theorem window_is_whole_branch (hc3 : CyclicallyThreeConnected H) (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hlen : 3 ≤ (slice B i j).length) {a : W}
    (hadj₁ : H.Adj (B[i]'(by omega)) a) (hadj₂ : H.Adj (B[j]'hj) a)
    (hout₁ : s(B[i]'(by omega), a) ∉ trackEdges (slice B i j))
    (hout₂ : s(B[j]'hj, a) ∉ trackEdges (slice B i j)) :
    i = 0 ∧ j = B.length - 1 ∧ a ∉ B := by
  have hlen' := length_slice B hj (show i ≤ j by omega)
  have hji : i + 2 ≤ j := by omega
  have hnd := hB.1.2.1
  have hi0 : i = 0 := by
    by_contra hi0
    have hiint : 0 < i := by omega
    rcases neighbor_of_internal hB hiint (by omega) hadj₁ with hai | hai
    · -- `a = B[i-1]`
      rcases Nat.lt_or_ge j (B.length - 1) with hjlt | hjge
      · -- `B[j]` is internal, so `a` is one of its neighbours
        rcases neighbor_of_internal hB (show 0 < j by omega) (by omega) hadj₂ with h | h
        · have := hnd.getElem_inj_iff.mp (hai.symm.trans h)
          omega
        · have := hnd.getElem_inj_iff.mp (hai.symm.trans h)
          omega
      · -- `j = B.length - 1`
        have hjeq : j = B.length - 1 := by omega
        rcases Nat.lt_or_ge 0 (i - 1) with him | him
        · -- `B[i-1]` is internal too
          have hadj₂' : H.Adj (B[i - 1]'(by omega)) (B[j]'hj) := by
            rw [← hai]; exact hadj₂.symm
          rcases neighbor_of_internal hB him (by omega) hadj₂' with h | h
          · have := hnd.getElem_inj_iff.mp h.symm
            omega
          · have := hnd.getElem_inj_iff.mp h.symm
            omega
        · -- `a = B[0]`, so the two ends of `B` are adjacent
          refine ends_not_adj hc3 hB (by omega) ?_
          have hthis := hadj₂.symm
          rw [hai, getElem_eq_of_index_eq B (show i - 1 = 0 by omega) (by omega)
            (by omega)] at hthis
          rw [getElem_eq_of_index_eq B hjeq.symm (by omega) hj]
          exact hthis
    · -- `a = B[i+1]`, an edge of the window
      exact hout₁ (by rw [hai]; exact slice_edge B hj (le_refl i) (by omega))
  subst hi0
  have hjL : j = B.length - 1 := by
    by_contra hjL
    have hjlt : j + 1 < B.length := by omega
    rcases neighbor_of_internal hB (show 0 < j by omega) hjlt hadj₂ with haj | haj
    · refine hout₂ ?_
      have hk : s(B[j - 1]'(by omega), B[j - 1 + 1]'(by omega)) ∈ trackEdges (slice B 0 j) :=
        slice_edge B hj (Nat.zero_le _) (by omega)
      rw [getElem_eq_of_index_eq B (show j - 1 + 1 = j by omega) (by omega) hj] at hk
      rw [haj, Sym2.eq_swap]
      exact hk
    · -- `a = B[j+1]`
      rcases Nat.lt_or_ge (j + 1) (B.length - 1) with hlt | hge
      · have hadj₁' : H.Adj (B[j + 1]'hjlt) (B[0]'(by omega)) := by
          rw [← haj]; exact hadj₁.symm
        rcases neighbor_of_internal hB (by omega) (by omega) hadj₁' with h | h
        · have := hnd.getElem_inj_iff.mp h.symm
          omega
        · have := hnd.getElem_inj_iff.mp h.symm
          omega
      · refine ends_not_adj hc3 hB (by omega) ?_
        have h0 : B[j + 1]'hjlt = B[B.length - 1]'(by omega) :=
          getElem_eq_of_index_eq B (by omega) _ _
        rw [← h0, ← haj]
        exact hadj₁
  refine ⟨rfl, hjL, ?_⟩
  intro haB
  obtain ⟨k, hk, hka⟩ := List.getElem_of_mem haB
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact hadj₁.ne' (by rw [← hka, getElem_eq_of_index_eq B hk0 _ _])
  rcases Nat.lt_or_ge k (B.length - 1) with hklt | hkge
  · -- `a` is internal to `B`
    have h1 : H.Adj (B[k]'hk) (B[0]'(by omega)) := by rw [hka]; exact hadj₁.symm
    have h2 : H.Adj (B[k]'hk) (B[j]'hj) := by rw [hka]; exact hadj₂.symm
    have e1 : k = 1 := by
      rcases neighbor_of_internal hB hk0 (by omega) h1 with h | h
      · have := hnd.getElem_inj_iff.mp h.symm
        omega
      · have := hnd.getElem_inj_iff.mp h.symm
        omega
    have e2 : k + 1 = j := by
      rcases neighbor_of_internal hB hk0 (by omega) h2 with h | h
      · have := hnd.getElem_inj_iff.mp h.symm
        omega
      · have := hnd.getElem_inj_iff.mp h.symm
        omega
    -- then `B` has three vertices and the edge `B[0]a` lies in the window
    refine hout₁ ?_
    have : a = B[0 + 1]'(by omega) := by
      rw [← hka]; exact getElem_eq_of_index_eq B (by omega) _ _
    rw [this]
    exact slice_edge B hj (le_refl 0) (by omega)
  · have : k = j := by omega
    exact hadj₂.ne' (by rw [← hka, getElem_eq_of_index_eq B this _ _])

end Forcing

/-! ### Assembling the two routes -/

section Assembly

variable {H : SimpleGraph W}

/-- A track between two distinct ends which does not use the edge joining them has at least
three vertices. -/
theorem three_le_length {q : List W} {x y : W} (hq : IsTrackFrom H q x y)
    (hxy : x ≠ y) (hmiss : s(x, y) ∉ trackEdges q) : 3 ≤ q.length := by
  have hpos : 0 < q.length := List.length_pos_of_ne_nil hq.1.1
  have hhead : q[0]'hpos = x := track_head hq hpos
  have hlast : q[q.length - 1]'(by omega) = y := by
    have h := hq.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  by_contra hcon
  rcases (show q.length = 1 ∨ q.length = 2 by omega) with h1 | h1
  · refine hxy ?_
    rw [← hhead, ← hlast]
    exact getElem_eq_of_index_eq q (show 0 = q.length - 1 by omega) hpos (by omega)
  · refine hmiss ⟨0, by omega, ?_⟩
    have e1 : q[0 + 1]'(by omega) = y := by
      rw [getElem_eq_of_index_eq q (show 0 + 1 = q.length - 1 by omega) (by omega) (by omega)]
      exact hlast
    rw [hhead, e1]

/-- Both ends of an edge of a track are vertices of it. -/
theorem ends_mem_of_mem_trackEdges {q : List W} {e : Sym2 W} (he : e ∈ trackEdges q)
    {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨k, hk, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

/-- An edge of a track avoiding the interior of the branch `B` is not an edge of `B`. -/
theorem not_mem_trackEdges_branch {q B : List W} (hL : 3 ≤ B.length)
    (hqB : ∀ w ∈ q, w ∉ trackInterior B) {e : Sym2 W} (he : e ∈ trackEdges q) :
    e ∉ trackEdges B := by
  intro heB
  obtain ⟨m, hm, hme⟩ := heB
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact hqB _ (ends_mem_of_mem_trackEdges he (by rw [hme]; exact Sym2.mem_mk_right _ _))
      (mem_trackInterior_getElem B 0 (by omega))
  · refine hqB _ (ends_mem_of_mem_trackEdges he (by rw [hme]; exact Sym2.mem_mk_left _ _)) ?_
    have := mem_trackInterior_getElem B (m - 1) (by omega)
    rwa [getElem_eq_of_index_eq B (show m - 1 + 1 = m by omega) (by omega) (by omega)] at this

end Assembly

/-- Every edge of a track is an edge of the graph. -/
theorem adj_of_mem_trackEdges {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    {x y : W} (he : s(x, y) ∈ trackEdges q) : H.Adj x y := by
  obtain ⟨k, hk, hke⟩ := he
  have hadj := hq.2.2 k hk
  rcases Sym2.eq_iff.mp hke with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hadj
  · rw [h1, h2]; exact hadj.symm

/-- Any two subdividing tracks carrying the same edge of `H` between branch-vertices are the
same edge of `J`. -/
theorem adj_of_branch_adj {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W} {ι : Fin n → W}
    {T : Fin n → Fin n → List W} (hS : SubData J H ι T) {x y : Fin n} (hxy : x ≠ y)
    (hadj : H.Adj (ι x) (ι y)) : J.Adj x y := by
  have he : s(ι x, ι y) ∈ H.edgeSet := hadj
  rw [hS.edges] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨p, q, hpq, hmem⟩ := he
  have h1 := branch_end_of_mem hS hpq
    (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem).1
  have h2 := branch_end_of_mem hS hpq
    (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem).2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hxy
  · rw [h1, h2]; exact hpq
  · rw [h1, h2]; exact hpq.symm
  · exact absurd (h1.trans h2.symm) hxy

/-- **The two routes of 5.7 (2).**

PAPER (printed p. 23): the track `R` through `P₁, P₂` and the track `S` through `P₁, P₃`. -/
theorem common_neighbor_routes_core (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hlen : 3 ≤ (slice B i j).length) {a : W}
    (hadj₁ : H.Adj (B[i]'(by omega)) a) (hadj₂ : H.Adj (B[j]'hj) a)
    (hout₁ : s(B[i]'(by omega), a) ∉ trackEdges (slice B i j))
    (hout₂ : s(B[j]'hj, a) ∉ trackEdges (slice B i j)) :
    ∃ R S : List W,
      IsTrackFrom H R (B[i]'(by omega)) (B[j]'hj) ∧ IsTrackFrom H S (B[i]'(by omega)) a ∧
      3 ≤ R.length ∧ 3 ≤ S.length ∧ a ∉ R ∧ (B[j]'hj) ∉ S ∧
      (∀ w ∈ R, w ∈ slice B i j → w = B[i]'(by omega) ∨ w = B[j]'hj) ∧
      (∀ w ∈ S, w ∈ slice B i j → w = B[i]'(by omega)) ∧
      Disjoint (trackEdges R ∪ trackEdges S)
        (trackEdges (slice B i j) ∪ {s(B[i]'(by omega), a), s(B[j]'hj, a)}) := by
  classical
  obtain ⟨hi0, hjL, haB⟩ := window_is_whole_branch hc3 hB hij hj hlen hadj₁ hadj₂ hout₁ hout₂
  subst hi0
  subst hjL
  have hlen' := length_slice B hj (show 0 ≤ B.length - 1 by omega)
  have hL3 : 3 ≤ B.length := by omega
  have hCB : slice B 0 (B.length - 1) = B := by
    simp only [slice, List.drop_zero, Nat.sub_zero]
    rw [show B.length - 1 + 1 = B.length by omega, List.take_length]
  rw [hCB] at hout₁ hout₂ ⊢
  have hnadj := ends_not_adj hc3 hB hL3
  have hfromB : IsTrackFrom H B (B[0]'(by omega)) (B[B.length - 1]'(by omega)) :=
    Workspace.ProofLemmas.Thm57Claim2Structure.branch_from_ends hB (by omega)
  obtain ⟨n, J, hJ, hsubdiv⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsubdiv
  have hdeg := Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hbr : branchVertices H = Set.range ι := branch_eq_range hJ hS
  have hbv := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsubdiv B _ _ hB hfromB (by unfold trackLength; omega)
  obtain ⟨u, v, huv, hEuv, hendsuv⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hS.inj hS.track hS.len hS.rev hS.disj hS.new hS.cover hS.edges hdeg hB (by omega)
      hfromB hbv.1 hbv.2
  obtain ⟨c, d, hcd, hc, hd, hE⟩ : ∃ c d : Fin n, J.Adj c d ∧ ι c = B[0]'(by omega) ∧
      ι d = B[B.length - 1]'(by omega) ∧ trackEdges (T c d) = trackEdges B := by
    rcases hendsuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨u, v, huv, h1.symm, h2.symm, hEuv.symm⟩
    · refine ⟨v, u, huv.symm, h1.symm, h2.symm, ?_⟩
      rw [hS.rev u v huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
      exact hEuv.symm
  -- `a` is a branch-vertex
  have harange : a ∈ Set.range ι := by
    by_contra hcon
    obtain ⟨e, f, hef, haint⟩ : ∃ e f : Fin n, J.Adj e f ∧ a ∈ trackInterior (T e f) := by
      rcases hS.cover a with ⟨u', hu'⟩ | h
      · exact absurd ⟨u', hu'.symm⟩ hcon
      · exact h
    have hTL : 2 ≤ (T e f).length := by
      have := hS.len e f hef
      unfold trackLength at this
      omega
    have hkey : ∀ {x : W}, H.Adj x a → x ∈ T e f := by
      intro x hx
      have hxe : s(x, a) ∈ H.edgeSet := hx
      rw [hS.edges] at hxe
      simp only [Set.mem_iUnion] at hxe
      obtain ⟨p, q, hpq, hmem⟩ := hxe
      have hap : a ∈ T p q :=
        (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem).2
      have hxp : x ∈ T p q :=
        (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hmem).1
      have hsame : s(p, q) = s(e, f) := by
        by_contra hne
        exact hS.disj e f p q hef hpq (Ne.symm hne) a haint hap
      rcases Sym2.eq_iff.mp hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hxp; exact hxp
      · rw [h1, h2, hS.rev e f hef] at hxp
        exact List.mem_reverse.mp hxp
    have hce : ι c ∈ T e f := hkey (by rw [hc]; exact hadj₁)
    have hde : ι d ∈ T e f := hkey (by rw [hd]; exact hadj₂)
    have h1 := branch_end_of_mem hS hef hce
    have h2 := branch_end_of_mem hS hef hde
    have hsame2 : s(c, d) = s(e, f) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hcd.ne
      · rw [h1, h2]
      · rw [h1, h2]; exact Sym2.eq_swap
      · exact absurd (h1.trans h2.symm) hcd.ne
    have hEef : trackEdges (T e f) = trackEdges B := by
      rw [trackEdges_eq_of_sym2_eq hS.rev hcd hsame2]
      exact hE
    refine haB (mem_of_trackEdges_eq hTL hEef ?_)
    exact ((List.dropLast_sublist _).trans (List.tail_sublist _)).subset haint
  obtain ⟨z, hz⟩ := harange
  have hzc : z ≠ c := by
    intro h
    exact haB (by rw [← hz, h, hc]; exact List.getElem_mem _)
  have hzd : z ≠ d := by
    intro h
    exact haB (by rw [← hz, h, hd]; exact List.getElem_mem _)
  have hcz : J.Adj c z := by
    refine adj_of_branch_adj hS (fun h => hzc h.symm) ?_
    rw [hc, hz]
    exact hadj₁
  obtain ⟨Rt, hRt, hRint, hRz⟩ :=
    exists_route_cd hJ hS hB (by omega) hcd hc hd hE hzc hzd
  obtain ⟨St, hSt, hSint, hSd, hSedge⟩ :=
    exists_route_cz hJ hS hB (by omega) hcd hcz hc hd hE hzd
  simp only [hc, hd] at hRt hSt hSd hSedge
  simp only [hz] at hRt hRz hSt hSd hSedge
  -- a few consequences
  have hends : ∀ {q : List W}, (∀ w ∈ q, w ∉ trackInterior B) → ∀ w ∈ q, w ∈ B →
      w = B[0]'(by omega) ∨ w = B[B.length - 1]'(by omega) := by
    intro q hq w hw hwB
    exact Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem hfromB.2.1 hfromB.2.2 hwB
      (hq w hw)
  have hne0 : B[0]'(by omega) ≠ B[B.length - 1]'(by omega) := by
    intro h
    exact absurd (hB.1.2.1.getElem_inj_iff.mp h) (by omega)
  have hnea : B[0]'(by omega) ≠ a := by
    intro h
    exact haB (by rw [← h]; exact List.getElem_mem _)
  refine ⟨Rt, St, hRt, hSt, ?_, ?_, hRz, hSd, hends hRint, ?_, ?_⟩
  · refine three_le_length hRt hne0 ?_
    intro hmem
    exact hnadj (adj_of_mem_trackEdges hRt.1 hmem)
  · exact three_le_length hSt hnea hSedge
  · intro w hw hwB
    rcases hends hSint w hw hwB with h | h
    · exact h
    · exact absurd (h ▸ hw) hSd
  · refine Set.disjoint_left.mpr ?_
    intro e he hbad
    have hpair : e ∈ trackEdges B ∨ e = s(B[0]'(by omega), a) ∨
        e = s(B[B.length - 1]'(by omega), a) := by
      rcases hbad with h | h
      · exact Or.inl h
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        exact Or.inr h
    rcases he with he | he
    · rcases hpair with h | h | h
      · exact not_mem_trackEdges_branch hL3 hRint he h
      · exact hRz (ends_mem_of_mem_trackEdges he (by rw [h]; exact Sym2.mem_mk_right _ _))
      · exact hRz (ends_mem_of_mem_trackEdges he (by rw [h]; exact Sym2.mem_mk_right _ _))
    · rcases hpair with h | h | h
      · exact not_mem_trackEdges_branch hL3 hSint he h
      · exact hSedge (h ▸ he)
      · exact hSd (ends_mem_of_mem_trackEdges he (by rw [h]; exact Sym2.mem_mk_left _ _))


end Workspace.ProofLemmas.Thm57Claim2Routes
