import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# The elementary König step in 5.7 (1)

The proof of 5.7 (1) only needs the following special case of König's theorem: a nonempty
pairwise-meeting set of edges in a triangle-free graph has a common end.  This file also
records the subdivision fact used after choosing that common end.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim1Konig

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-- A bipartite graph contains no triangle. -/
theorem no_triangle {H : SimpleGraph W} (hbip : H.IsBipartite) {a b c : W}
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c) : False := by
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

/-- Two edges which are not disjoint have a common end. -/
theorem exists_common_end {e f : Sym2 W} (h : ¬ DisjointEdges e f) :
    ∃ w : W, w ∈ e ∧ w ∈ f := by
  classical
  by_contra hno
  apply h
  intro w hw
  exact hno ⟨w, hw⟩

/-- The special case of König's theorem used in the printed proof of 5.7 (1). -/
theorem exists_common_vertex {H : SimpleGraph W} (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet) (hX : X.Nonempty)
    (hmeet : ∀ e ∈ X, ∀ f ∈ X, ¬ DisjointEdges e f) :
    ∃ v : W, ∀ e ∈ X, v ∈ e := by
  classical
  obtain ⟨e₀, he₀⟩ := hX
  induction e₀ using Sym2.ind with
  | _ a b =>
      by_cases ha : ∀ e ∈ X, a ∈ e
      · exact ⟨a, ha⟩
      · push Not at ha
        obtain ⟨f, hfX, haf⟩ := ha
        obtain ⟨w, hwab, hwf⟩ := exists_common_end (hmeet s(a, b) he₀ f hfX)
        have hwb : w = b := by
          rcases Sym2.mem_iff.mp hwab with hwa | hwb
          · exact absurd (hwa ▸ hwf) haf
          · exact hwb
        have hbf : b ∈ f := hwb ▸ hwf
        obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp hbf
        subst f
        have hac : a ≠ c := by
          intro h
          subst c
          exact haf (by simp)
        refine ⟨b, ?_⟩
        intro g hgX
        by_contra hbg
        obtain ⟨x, hxab, hxg⟩ := exists_common_end (hmeet s(a, b) he₀ g hgX)
        have hxa : x = a := by
          rcases Sym2.mem_iff.mp hxab with hxa | hxb
          · exact hxa
          · exact absurd (hxb ▸ hxg) hbg
        have hag : a ∈ g := hxa ▸ hxg
        obtain ⟨y, hybc, hyg⟩ := exists_common_end (hmeet s(b, c) hfX g hgX)
        have hyc : y = c := by
          rcases Sym2.mem_iff.mp hybc with hyb | hyc
          · exact absurd (hyb ▸ hyg) hbg
          · exact hyc
        have hcg : c ∈ g := hyc ▸ hyg
        have hg : g = s(a, c) := (Sym2.mem_and_mem_iff hac).mp ⟨hag, hcg⟩
        have hab : H.Adj a b := by simpa using hXE he₀
        have hbc : H.Adj b c := by simpa using hXE hfX
        have hac' : H.Adj a c := by simpa [hg] using hXE hgX
        exact no_triangle hbip hab hbc hac'

/-- If a vertex is internal to one subdividing track, every edge at that vertex lies on that
track. -/
theorem incidentEdges_subset_trackEdges {U : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {T : U → U → List W}
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' →
      s(u, v) ≠ s(u', v') → ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    {u v : U} (huv : J.Adj u v) {w : W} (hw : w ∈ trackInterior (T u v)) :
    incidentEdges H w ⊆ trackEdges (T u v) := by
  intro e he
  have heH : e ∈ H.edgeSet := he.1
  have hwe : w ∈ e := he.2
  rw [hedges] at heH
  simp only [Set.mem_iUnion] at heH
  obtain ⟨u', v', hu'v', heT⟩ := heH
  by_cases hs : s(u, v) = s(u', v')
  · rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heT
    · rw [hrev u v huv, SubdivisionCounting.trackEdges_reverse] at heT
      exact heT
  · exfalso
    have hwT : w ∈ T u' v' := by
      obtain ⟨i, hi, hie⟩ := heT
      rw [hie] at hwe
      rcases Sym2.mem_iff.mp hwe with h | h
      · exact h ▸ List.getElem_mem _
      · exact h ▸ List.getElem_mem _
    exact hdisjint u v u' v' huv hu'v' hs w hw hwT

end Workspace.ProofLemmas.Thm57Claim1Konig
