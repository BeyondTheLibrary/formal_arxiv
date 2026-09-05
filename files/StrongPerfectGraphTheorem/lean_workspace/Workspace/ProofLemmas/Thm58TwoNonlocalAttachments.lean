import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58TwoNonlocalAttachments

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- A bipartite graph has no triangle. -/
private theorem no_triangle {W : Type*} {H : SimpleGraph W} (hbip : H.IsBipartite)
    {a b c : W} (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c) : False := by
  obtain ⟨f⟩ := hbip
  have h1 := f.valid hab
  have h2 := f.valid hbc
  have h3 := f.valid hac
  revert h1 h2 h3
  generalize f a = A
  generalize f b = B
  generalize f c = C
  revert A B C
  decide

theorem thm58TwoNonlocalAttachments {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotlocal : ¬ LocalForLineGraph H X) :
    ∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ LocalForLineGraph H {x₁, x₂} := by
  classical
  obtain ⟨m, J, hJ, ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hc3
  -- ## Basic dictionary between `H` and its subdivision data
  have hdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard := fun u =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  -- every subdividing track is a branch
  have hTint : ∀ u v : Fin m, J.Adj u v → ∀ w ∈ trackInterior (T u v),
      w ∉ branchVertices H := fun u v huv w hw hb => hnew u v huv w hw (hbv₂ hb)
  have hTbranch : ∀ u v : Fin m, J.Adj u v → IsBranch H (T u v) := by
    intro u v huv
    exact Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
      (fun h => huv.ne (hι h)) (hTint u v huv) (hbv₁ ⟨u, rfl⟩) (hbv₁ ⟨v, rfl⟩)
  -- every edge lies on a subdividing track
  have hedgeTrack : ∀ e ∈ H.edgeSet, ∃ u v : Fin m, J.Adj u v ∧ e ∈ trackEdges (T u v) := by
    intro e he
    rw [hedges] at he
    simp only [Set.mem_iUnion] at he
    obtain ⟨u, v, huv, h⟩ := he
    exact ⟨u, v, huv, h⟩
  -- tracks attached to the same edge of `J` have the same edge set
  have htrackEq : ∀ u v u' v' : Fin m, J.Adj u v → J.Adj u' v' → s(u, v) = s(u', v') →
      trackEdges (T u v) = trackEdges (T u' v') := by
    intro u v u' v' _ hu'v' hs
    rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hrev u' v' hu'v']
      exact SubdivisionCounting.trackEdges_reverse _
  -- ... and a common edge forces that
  have htrackUniq : ∀ u v u' v' : Fin m, J.Adj u v → J.Adj u' v' → ∀ e : Sym2 W,
      e ∈ trackEdges (T u v) → e ∈ trackEdges (T u' v') →
      trackEdges (T u v) = trackEdges (T u' v') := by
    intro u v u' v' huv hu'v' e he he'
    exact htrackEq u v u' v' huv hu'v'
      (SubdivisionCounting.trackEdges_disjoint hι htrack hlen hdisjint u v u' v' huv hu'v' e he he')
  -- a branch-vertex lying on an edge of a track is an end of that track
  have hBVend : ∀ u v : Fin m, J.Adj u v → ∀ e ∈ trackEdges (T u v), ∀ c ∈ e,
      c ∈ branchVertices H → c = ι u ∨ c = ι v := by
    intro u v huv e he c hce hcb
    obtain ⟨d, rfl⟩ := Sym2.mem_iff_exists.mp hce
    have hmem := (BranchClassification.mem_of_mem_trackEdges he).1
    have hint : c ∉ trackInterior (T u v) := fun hh => hnew u v huv c hh (hbv₂ hcb)
    exact SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1 (htrack u v huv).2.2 hmem hint
  -- two distinct branch-vertices on a single track are its two ends
  have hendPair : ∀ (a b : W) (u' v' : Fin m), J.Adj u' v' → ∀ e f : Sym2 W,
      e ∈ trackEdges (T u' v') → f ∈ trackEdges (T u' v') → a ∈ e → b ∈ f →
      a ∈ branchVertices H → b ∈ branchVertices H → a ≠ b →
      (a = ι u' ∧ b = ι v') ∨ (a = ι v' ∧ b = ι u') := by
    intro a b u' v' h e f he hf hae hbf hab' hbb' hne
    rcases hBVend u' v' h e he a hae hab' with h1 | h1 <;>
      rcases hBVend u' v' h f hf b hbf hbb' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  -- the track carrying two prescribed branch-vertices is determined
  have hendTrack2 : ∀ (a b : W) (p₀ q₀ u' v' : Fin m), J.Adj p₀ q₀ → J.Adj u' v' →
      a = ι p₀ → b = ι q₀ → ∀ e f : Sym2 W,
      e ∈ trackEdges (T u' v') → f ∈ trackEdges (T u' v') → a ∈ e → b ∈ f →
      trackEdges (T u' v') = trackEdges (T p₀ q₀) := by
    intro a b p₀ q₀ u' v' hpq huv hap hbq e f he hf hae hbf
    have hne : a ≠ b := by rw [hap, hbq]; exact fun h => hpq.ne (hι h)
    have hab : a ∈ branchVertices H := by rw [hap]; exact hbv₁ ⟨p₀, rfl⟩
    have hbb : b ∈ branchVertices H := by rw [hbq]; exact hbv₁ ⟨q₀, rfl⟩
    rcases hendPair a b u' v' huv e f he hf hae hbf hab hbb hne with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine htrackEq u' v' p₀ q₀ huv hpq ?_
      rw [hι (hap.symm.trans e1), hι (hbq.symm.trans e2)]
    · refine htrackEq u' v' p₀ q₀ huv hpq ?_
      rw [hι (hap.symm.trans e1), hι (hbq.symm.trans e2)]
      exact Sym2.eq_swap
  -- ## The criterion for a two-element set to be non-local
  have hcrit : ∀ x y : Sym2 W,
      (∀ c ∈ branchVertices H, ¬ (c ∈ x ∧ c ∈ y)) →
      (∀ u v : Fin m, J.Adj u v →
        ¬ (x ∈ trackEdges (T u v) ∧ y ∈ trackEdges (T u v))) →
      ¬ LocalForLineGraph H ({x, y} : Set (Sym2 W)) := by
    intro x y h1 h2 hloc
    rcases hloc with ⟨c, hc, hsub⟩ | ⟨q, hq, hsub⟩
    · exact h1 c hc ⟨(hsub (Set.mem_insert _ _)).2,
        (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2⟩
    · have hx : x ∈ trackEdges q := hsub (Set.mem_insert _ _)
      have hy : y ∈ trackEdges q := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hq2 : 2 ≤ q.length := by obtain ⟨i, hi, -⟩ := hx; omega
      obtain ⟨u, v, huv, heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
        hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hq hq2
      rw [heq] at hx hy
      exact h2 u v huv ⟨hx, hy⟩
  -- ## The two consequences of `X` not being local
  have hA : ∀ c ∈ branchVertices H, ∃ e ∈ X, c ∉ e := by
    intro c hc
    by_contra hcon
    refine hnotlocal (Or.inl ⟨c, hc, fun e he => ⟨hXE he, ?_⟩⟩)
    by_contra hce
    exact hcon ⟨e, he, hce⟩
  have hB : ∀ u v : Fin m, J.Adj u v → ∃ e ∈ X, e ∉ trackEdges (T u v) := by
    intro u v huv
    by_contra hcon
    refine hnotlocal (Or.inr ⟨T u v, hTbranch u v huv, fun e he => ?_⟩)
    by_contra hce
    exact hcon ⟨e, he, hce⟩
  have hXne : X.Nonempty := by
    rcases Set.eq_empty_or_nonempty X with rfl | h
    · exfalso
      have h4 : 3 < m := by have := hJ.1; simpa using this
      exact hnotlocal (Or.inl ⟨ι ⟨0, by omega⟩, hbv₁ ⟨_, rfl⟩, by simp⟩)
    · exact h
  -- ## Case A: some edge of `X` has no branch-vertex end
  by_cases hcaseA : ∃ x ∈ X, ∀ c ∈ x, c ∉ branchVertices H
  · obtain ⟨x₁, hx₁X, hx₁nb⟩ := hcaseA
    obtain ⟨u, v, huv, hx₁T⟩ := hedgeTrack x₁ (hXE hx₁X)
    obtain ⟨x₂, hx₂X, hx₂T⟩ := hB u v huv
    refine ⟨x₁, hx₁X, x₂, hx₂X, hcrit x₁ x₂ ?_ ?_⟩
    · rintro c hc ⟨hc1, -⟩
      exact hx₁nb c hc1 hc
    · rintro u' v' hu'v' ⟨h1, h2⟩
      exact hx₂T (htrackUniq u' v' u v hu'v' huv x₁ h1 hx₁T ▸ h2)
  -- ## Case B: every edge of `X` is incident with a branch-vertex
  · have hbvend : ∀ x ∈ X, ∃ c ∈ x, c ∈ branchVertices H := by
      intro x hx
      by_contra hcon
      exact hcaseA ⟨x, hx, fun c hcx hcb => hcon ⟨c, hcx, hcb⟩⟩
    obtain ⟨x₁, hx₁X⟩ := hXne
    obtain ⟨b₁, hb₁x, hb₁bv⟩ := hbvend x₁ hx₁X
    obtain ⟨d, hx₁eq⟩ := Sym2.mem_iff_exists.mp hb₁x
    have hdx : d ∈ x₁ := by rw [hx₁eq]; exact Sym2.mem_mk_right b₁ d
    have hadj : H.Adj b₁ d := by
      have hh := hXE hx₁X
      rw [hx₁eq] at hh
      rwa [SimpleGraph.mem_edgeSet] at hh
    have hbd : b₁ ≠ d := hadj.ne
    obtain ⟨u, v, huv, hx₁T⟩ := hedgeTrack x₁ (hXE hx₁X)
    by_cases hd : d ∈ branchVertices H
    -- ### Case B-ii: both ends of `x₁` are branch-vertices
    · obtain ⟨p₀, q₀, hpq, hb₁p, hdq, hx₁Tp⟩ :
          ∃ p₀ q₀ : Fin m, J.Adj p₀ q₀ ∧ b₁ = ι p₀ ∧ d = ι q₀ ∧ x₁ ∈ trackEdges (T p₀ q₀) := by
        rcases hendPair b₁ d u v huv x₁ x₁ hx₁T hx₁T hb₁x hdx hb₁bv hd hbd with
          ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨u, v, huv, e1, e2, hx₁T⟩
        · refine ⟨v, u, huv.symm, e1, e2, ?_⟩
          rw [htrackEq v u u v huv.symm huv Sym2.eq_swap]
          exact hx₁T
      -- the branch of `x₁` is the single edge `b₁ d`
      obtain ⟨i, hi, hie⟩ := id hx₁Tp
      have hbvi : (T p₀ q₀)[i]'(by omega) ∈ branchVertices H ∧
          (T p₀ q₀)[i + 1]'hi ∈ branchVertices H := by
        have h' : s(b₁, d) = s((T p₀ q₀)[i]'(by omega), (T p₀ q₀)[i + 1]'hi) := by
          rw [← hx₁eq]; exact hie
        rcases Sym2.eq_iff.mp h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨e1 ▸ hb₁bv, e2 ▸ hd⟩
        · exact ⟨e2 ▸ hd, e1 ▸ hb₁bv⟩
      have hlen2 : (T p₀ q₀).length = 2 :=
        SubdivisionCounting.track_edge_len_two (T p₀ q₀) i hi
          (fun hh => hnew p₀ q₀ hpq _ hh (hbv₂ hbvi.1))
          (fun hh => hnew p₀ q₀ hpq _ hh (hbv₂ hbvi.2))
      have hi0 : i = 0 := by omega
      subst hi0
      have hsingle : ∀ f ∈ trackEdges (T p₀ q₀), f = x₁ := by
        rintro f ⟨j, hj, hje⟩
        have hj0 : j = 0 := by omega
        subst hj0
        exact hje.trans hie.symm
      obtain ⟨x₂, hx₂X, hx₂b₁⟩ := hA b₁ hb₁bv
      obtain ⟨x₃, hx₃X, hx₃d⟩ := hA d hd
      by_cases hloc12 : LocalForLineGraph H ({x₁, x₂} : Set (Sym2 W))
      swap
      · exact ⟨x₁, hx₁X, x₂, hx₂X, hloc12⟩
      by_cases hloc13 : LocalForLineGraph H ({x₁, x₃} : Set (Sym2 W))
      swap
      · exact ⟨x₁, hx₁X, x₃, hx₃X, hloc13⟩
      -- from locality of the two pairs: `d ∈ x₂` and `b₁ ∈ x₃`
      have hdx₂ : d ∈ x₂ := by
        rcases hloc12 with ⟨c, hcbv, hsub⟩ | ⟨qq, hqq, hsub⟩
        · have h1 : c ∈ x₁ := (hsub (Set.mem_insert _ _)).2
          have h2 : c ∈ x₂ := (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2
          rw [hx₁eq] at h1
          rcases Sym2.mem_iff.mp h1 with h | h
          · exact absurd (h ▸ h2) hx₂b₁
          · exact h ▸ h2
        · exfalso
          have h1 : x₁ ∈ trackEdges qq := hsub (Set.mem_insert _ _)
          have h2 : x₂ ∈ trackEdges qq := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hq2 : 2 ≤ qq.length := by obtain ⟨k, hk, -⟩ := h1; omega
          obtain ⟨a', b', hab', heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
            hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hqq hq2
          rw [heq] at h1 h2
          have := htrackUniq a' b' p₀ q₀ hab' hpq x₁ h1 hx₁Tp
          exact hx₂b₁ (hsingle x₂ (this ▸ h2) ▸ hb₁x)
      have hb₁x₃ : b₁ ∈ x₃ := by
        rcases hloc13 with ⟨c, hcbv, hsub⟩ | ⟨qq, hqq, hsub⟩
        · have h1 : c ∈ x₁ := (hsub (Set.mem_insert _ _)).2
          have h2 : c ∈ x₃ := (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2
          rw [hx₁eq] at h1
          rcases Sym2.mem_iff.mp h1 with h | h
          · exact h ▸ h2
          · exact absurd (h ▸ h2) hx₃d
        · exfalso
          have h1 : x₁ ∈ trackEdges qq := hsub (Set.mem_insert _ _)
          have h2 : x₃ ∈ trackEdges qq := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hq2 : 2 ≤ qq.length := by obtain ⟨k, hk, -⟩ := h1; omega
          obtain ⟨a', b', hab', heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
            hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hqq hq2
          rw [heq] at h1 h2
          have := htrackUniq a' b' p₀ q₀ hab' hpq x₁ h1 hx₁Tp
          exact hx₃d (hsingle x₃ (this ▸ h2) ▸ hdx)
      refine ⟨x₂, hx₂X, x₃, hx₃X, ?_⟩
      rintro (⟨c, hcbv, hsub⟩ | ⟨qq, hqq, hsub⟩)
      · -- a common branch-vertex end produces a triangle `b₁ d c`
        have h1 : c ∈ x₂ := (hsub (Set.mem_insert _ _)).2
        have h2 : c ∈ x₃ := (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2
        have hcb₁ : c ≠ b₁ := fun h => hx₂b₁ (h ▸ h1)
        have hcd : c ≠ d := fun h => hx₃d (h ▸ h2)
        obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hdx₂
        rw [hw] at h1
        have hcw : c = w := by
          rcases Sym2.mem_iff.mp h1 with h | h
          exacts [absurd h hcd, h]
        have hadj2 : H.Adj d c := by
          have hh := hXE hx₂X
          rw [hw, ← hcw] at hh
          rwa [SimpleGraph.mem_edgeSet] at hh
        obtain ⟨w', hw'⟩ := Sym2.mem_iff_exists.mp hb₁x₃
        rw [hw'] at h2
        have hcw' : c = w' := by
          rcases Sym2.mem_iff.mp h2 with h | h
          exacts [absurd h hcb₁, h]
        have hadj3 : H.Adj b₁ c := by
          have hh := hXE hx₃X
          rw [hw', ← hcw'] at hh
          rwa [SimpleGraph.mem_edgeSet] at hh
        exact no_triangle hbip hadj hadj2 hadj3
      · -- a common track would put `x₂` on the branch of `x₁`
        have h1 : x₂ ∈ trackEdges qq := hsub (Set.mem_insert _ _)
        have h2 : x₃ ∈ trackEdges qq := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        have hq2 : 2 ≤ qq.length := by obtain ⟨k, hk, -⟩ := h1; omega
        obtain ⟨a', b', hab', heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
          hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hqq hq2
        rw [heq] at h1 h2
        have hEq1 : trackEdges (T a' b') = trackEdges (T q₀ p₀) :=
          hendTrack2 d b₁ q₀ p₀ a' b' hpq.symm hab' hdq hb₁p x₂ x₃ h1 h2 hdx₂ hb₁x₃
        have hEq2 : trackEdges (T q₀ p₀) = trackEdges (T p₀ q₀) :=
          htrackEq q₀ p₀ p₀ q₀ hpq.symm hpq Sym2.eq_swap
        exact hx₂b₁ (hsingle x₂ (hEq2 ▸ hEq1 ▸ h1) ▸ hb₁x)
    -- ### Case B-i: exactly one end of `x₁` is a branch-vertex
    · have hS1 : ∀ c ∈ x₁, c ∈ branchVertices H → c = b₁ := by
        intro c hc hcb
        rw [hx₁eq] at hc
        rcases Sym2.mem_iff.mp hc with h | h
        · exact h
        · exact absurd (h ▸ hcb) hd
      obtain ⟨p₀, q₀, hpq, hb₁p, hx₁Tp⟩ :
          ∃ p₀ q₀ : Fin m, J.Adj p₀ q₀ ∧ b₁ = ι p₀ ∧ x₁ ∈ trackEdges (T p₀ q₀) := by
        rcases hBVend u v huv x₁ hx₁T b₁ hb₁x hb₁bv with h | h
        · exact ⟨u, v, huv, h, hx₁T⟩
        · refine ⟨v, u, huv.symm, h, ?_⟩
          rw [htrackEq v u u v huv.symm huv Sym2.eq_swap]
          exact hx₁T
      obtain ⟨x₂, hx₂X, hx₂b₁⟩ := hA b₁ hb₁bv
      by_cases hx₂T : x₂ ∈ trackEdges (T p₀ q₀)
      swap
      · refine ⟨x₁, hx₁X, x₂, hx₂X, hcrit x₁ x₂ ?_ ?_⟩
        · rintro c hc ⟨hc1, hc2⟩
          exact hx₂b₁ (hS1 c hc1 hc ▸ hc2)
        · rintro u' v' hu'v' ⟨h1, h2⟩
          exact hx₂T (htrackUniq u' v' p₀ q₀ hu'v' hpq x₁ h1 hx₁Tp ▸ h2)
      -- `x₂` lies on the same branch, so its branch-vertex end is the far end `ι q₀`
      have hS2 : ∀ c ∈ x₂, c ∈ branchVertices H → c = ι q₀ := by
        intro c hc hcb
        rcases hBVend p₀ q₀ hpq x₂ hx₂T c hc hcb with h | h
        · exact absurd (show b₁ ∈ x₂ by rw [hb₁p, ← h]; exact hc) hx₂b₁
        · exact h
      obtain ⟨x₃, hx₃X, hx₃T⟩ := hB p₀ q₀ hpq
      by_cases hloc13 : LocalForLineGraph H ({x₁, x₃} : Set (Sym2 W))
      swap
      · exact ⟨x₁, hx₁X, x₃, hx₃X, hloc13⟩
      by_cases hloc23 : LocalForLineGraph H ({x₂, x₃} : Set (Sym2 W))
      swap
      · exact ⟨x₂, hx₂X, x₃, hx₃X, hloc23⟩
      exfalso
      have hb₁x₃ : b₁ ∈ x₃ := by
        rcases hloc13 with ⟨c, hcbv, hsub⟩ | ⟨qq, hqq, hsub⟩
        · have h1 : c ∈ x₁ := (hsub (Set.mem_insert _ _)).2
          have h2 : c ∈ x₃ := (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2
          exact hS1 c h1 hcbv ▸ h2
        · exfalso
          have h1 : x₁ ∈ trackEdges qq := hsub (Set.mem_insert _ _)
          have h2 : x₃ ∈ trackEdges qq := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hq2 : 2 ≤ qq.length := by obtain ⟨k, hk, -⟩ := h1; omega
          obtain ⟨a', b', hab', heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
            hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hqq hq2
          rw [heq] at h1 h2
          exact hx₃T (htrackUniq a' b' p₀ q₀ hab' hpq x₁ h1 hx₁Tp ▸ h2)
      have hq₀x₃ : ι q₀ ∈ x₃ := by
        rcases hloc23 with ⟨c, hcbv, hsub⟩ | ⟨qq, hqq, hsub⟩
        · have h1 : c ∈ x₂ := (hsub (Set.mem_insert _ _)).2
          have h2 : c ∈ x₃ := (hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2
          exact hS2 c h1 hcbv ▸ h2
        · exfalso
          have h1 : x₂ ∈ trackEdges qq := hsub (Set.mem_insert _ _)
          have h2 : x₃ ∈ trackEdges qq := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hq2 : 2 ≤ qq.length := by obtain ⟨k, hk, -⟩ := h1; omega
          obtain ⟨a', b', hab', heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
            hι htrack hlen hrev hdisjint hnew hcover hedges hdeg hqq hq2
          rw [heq] at h1 h2
          exact hx₃T (htrackUniq a' b' p₀ q₀ hab' hpq x₂ h1 hx₂T ▸ h2)
      -- then `x₃` joins the two ends of the branch, so it lies on that branch
      obtain ⟨a'', b'', hab'', hx₃T'⟩ := hedgeTrack x₃ (hXE hx₃X)
      have hEq := hendTrack2 b₁ (ι q₀) p₀ q₀ a'' b'' hpq hab'' hb₁p rfl x₃ x₃
        hx₃T' hx₃T' hb₁x₃ hq₀x₃
      exact hx₃T (hEq ▸ hx₃T')

end Workspace.ProofLemmas.Thm58TwoNonlocalAttachments
