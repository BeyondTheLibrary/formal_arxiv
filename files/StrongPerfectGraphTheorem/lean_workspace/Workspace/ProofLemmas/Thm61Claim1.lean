import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Claim1Core
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-!
# 6.1, claim (1)

PAPER (proof of 6.1, printed p. 29):

> *"(1) If the branch-vertices of `H` form a 4-cycle `C` and `X` consists of at most three edges
> of `C`, then the theorem holds.*
>
> *For in this case `H` has only four branch-vertices and `J = K₄`.  Let the edges of `C` be
> `a, b, c, d` in order, and let `p, q, r, s` be edges of `H \ {a,b,c,d}` such that the sets of
> edges incident with branch-vertices of `H` are `{a,b,p}`, `{b,c,q}`, `{c,d,r}` and `{d,a,s}`.
> Since every branch-vertex is incident with at least one edge in `X`, we may assume that
> `X = {b,d}` or `{b,c,d}`.  Since `a, p ∉ X`, it follows that one is in `X₁` and the other in
> `X₂`, say `a ∈ X₁` and `p ∈ X₂`.  Similarly, since `a, s ∉ X` it follows that `s ∈ X₂`.  Let
> `P` be the path in `L(H)` between `p, r` whose vertex set is the edge-set of the branch of `H`
> containing `p, r`, and choose `Q` containing `q, s` similarly.  Thus `P` is odd, and so is `Q`.
> If they both have length 1 then `H` has 6 vertices and the fourth outcome of the theorem
> holds.  We may therefore assume that `P` has length `≥ 3`.  The path `b-p-P-r-d` is odd and
> has length `≥ 5`; its ends are `Y`-complete and its internal vertices are not, so by 2.1, `Y`
> contains a leap.  Hence there exist nonadjacent `y, y' ∈ Y` such that `y-r-P-p-y'` is a path
> in `G`.  Since `p ∈ X₂` and `y` is nonadjacent to `p` it follows that `y = y₂`; and since
> `s ∈ X₂` and `y ≠ y'`, it follows that `y'` is adjacent to `s`.  Now `y-r-P-p-y'` is an odd
> path, and it cannot be completed to an odd hole, so `y, y'` have no common neighbour in `Q`.
> But `b-q-Q-s-d` is an odd path; its ends are `{y,y'}`-complete, and its internal vertices are
> not, so by 2.1, `y, y'` form a leap for this path, that is, `y-q-Q-s-y'` is a path of `G`.
> (Note that this holds even if `b-q-Q-s-d` has length 3, since the anticonnected set in
> question has cardinality 2.)  Since `y'` is major and nonadjacent to `q` it follows that `y'`
> is adjacent to `c`, and similarly `y` is adjacent to `a`.  But then the fifth outcome of the
> theorem holds.  This proves (1)."*

Claim (1) is used in **both** halves of the proof of 6.1 — at the end of claim (6) (odd case)
and in the closing paragraph (even case) — so it is stated once here, with no hypothesis on the
parity of `Q`.

*"The branch-vertices of `H` form a 4-cycle `C`"* is encoded exactly as in the fifth outcome of
6.1 itself: four distinct vertices `v₁, v₂, v₃, v₄` which are cyclically adjacent in `H` and
which are **precisely** the branch-vertices of `H`.  *"`X` consists of at most three edges of
`C`"* is `X ⊆ E(C)` together with `X.ncard ≤ 3`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Workspace.ProofLemmas.Thm61Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Claim1Geometry
open Workspace.ProofLemmas.Thm61Claim1Core

/-- **6.1(1)** *"If the branch-vertices of `H` form a 4-cycle `C` and `X` consists of at most
three edges of `C`, then the theorem holds."* -/
theorem thm_6_1_claim_1
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    -- *"the branch-vertices of `H` form a 4-cycle `C`"*
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n)))
    (hc₁ : H.Adj w₁ w₂) (hc₂ : H.Adj w₂ w₃) (hc₃ : H.Adj w₃ w₄) (hc₄ : H.Adj w₄ w₁)
    -- *"`X` consists of at most three edges of `C`"*
    (hXC : completeEdges G H K φ Y ⊆
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} : Set (Sym2 (Fin n))))
    (hXcard : (completeEdges G H K φ Y).ncard ≤ 3) :
    Thm61Concl G m J n H K φ Y := by
  classical
  obtain ⟨hJiso, hsub4⟩ := source_is_k4 m J hJ H hsub.1 w₁ w₂ w₃ w₄ hnd hbv
  let X := completeEdges G H K φ Y
  let a := s(w₁, w₂)
  let b := s(w₂, w₃)
  let c := s(w₃, w₄)
  let d := s(w₄, w₁)
  change X.ncard ≤ 3 at hXcard
  have h12 : w₁ ≠ w₂ := by rintro rfl; simp at hnd
  have h13 : w₁ ≠ w₃ := by rintro rfl; simp at hnd
  have h14 : w₁ ≠ w₄ := by rintro rfl; simp at hnd
  have h23 : w₂ ≠ w₃ := by rintro rfl; simp at hnd
  have h24 : w₂ ≠ w₄ := by rintro rfl; simp at hnd
  have h34 : w₃ ≠ w₄ := by rintro rfl; simp at hnd
  have hAt : ∀ w ∈ branchVertices H,
      ∃ e : Sym2 (Fin n), e ∈ incidentEdges H w ∧ e ∈ X := by
    intro w hw
    exact Thm61EvenEndgameHelpers.exists_complete_incident G n H K φ Y hmin
      y₁ y₂ Q hQ hQY hy w hw
  have hw1 : a ∈ X ∨ d ∈ X := by
    obtain ⟨e, heI, heX⟩ := hAt w₁ (by rw [hbv]; simp)
    have heC := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
    rcases heC with h | h | h | h
    · left; simpa [a] using (h ▸ heX)
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h12, h13, Ne.symm h12, Ne.symm h13] at hm
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h13, h14, Ne.symm h13, Ne.symm h14] at hm
    · right; simpa [d] using (h ▸ heX)
  have hw2 : a ∈ X ∨ b ∈ X := by
    obtain ⟨e, heI, heX⟩ := hAt w₂ (by rw [hbv]; simp)
    have heC := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
    rcases heC with h | h | h | h
    · left; simpa [a] using (h ▸ heX)
    · right; simpa [b] using (h ▸ heX)
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h23, h24, Ne.symm h23, Ne.symm h24] at hm
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h12, h24, Ne.symm h12, Ne.symm h24] at hm
  have hw3 : b ∈ X ∨ c ∈ X := by
    obtain ⟨e, heI, heX⟩ := hAt w₃ (by rw [hbv]; simp)
    have heC := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
    rcases heC with h | h | h | h
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h13, h23, Ne.symm h13, Ne.symm h23] at hm
    · left; simpa [b] using (h ▸ heX)
    · right; simpa [c] using (h ▸ heX)
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h13, h34, Ne.symm h13, Ne.symm h34] at hm
  have hw4 : c ∈ X ∨ d ∈ X := by
    obtain ⟨e, heI, heX⟩ := hAt w₄ (by rw [hbv]; simp)
    have heC := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
    rcases heC with h | h | h | h
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h14, h24, Ne.symm h14, Ne.symm h24] at hm
    · subst e
      have hm := heI.2
      simp [Sym2.mem_iff, h24, h34, Ne.symm h24, Ne.symm h34] at hm
    · left; simpa [c] using (h ▸ heX)
    · right; simpa [d] using (h ▸ heX)
  have hcycleCard : ({a, b, c, d} : Set (Sym2 (Fin n))).ncard = 4 := by
    have hab : a ≠ b := by
      intro h
      have : w₁ ∈ b := h ▸ (by simp [a])
      simpa [b, Sym2.mem_iff, h12, h13, Ne.symm h12, Ne.symm h13] using this
    have hac : a ≠ c := by
      intro h
      have : w₁ ∈ c := h ▸ (by simp [a])
      simpa [c, Sym2.mem_iff, h13, h14, Ne.symm h13, Ne.symm h14] using this
    have had : a ≠ d := by
      intro h
      have : w₂ ∈ d := h ▸ (by simp [a])
      simpa [d, Sym2.mem_iff, h12, h24, Ne.symm h12, Ne.symm h24] using this
    have hbc : b ≠ c := by
      intro h
      have : w₂ ∈ c := h ▸ (by simp [b])
      simpa [c, Sym2.mem_iff, h23, h24, Ne.symm h23, Ne.symm h24] using this
    have hbd : b ≠ d := by
      intro h
      have : w₂ ∈ d := h ▸ (by simp [b])
      simpa [d, Sym2.mem_iff, h12, h24, Ne.symm h12, Ne.symm h24] using this
    have hcd : c ≠ d := by
      intro h
      have : w₃ ∈ d := h ▸ (by simp [c])
      simpa [d, Sym2.mem_iff, h13, h34, Ne.symm h13, Ne.symm h34] using this
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_insert_of_notMem (by simp [hcd]), Set.ncard_singleton]
  have hmissing : a ∉ X ∨ b ∉ X ∨ c ∉ X ∨ d ∉ X := by
    by_contra h
    push Not at h
    have hsubC : ({a, b, c, d} : Set (Sym2 (Fin n))) ⊆ X := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2
    have hle := Set.ncard_le_ncard hsubC (Set.toFinite X)
    rw [hcycleCard] at hle
    omega
  rcases hmissing with ha | hb | hc | hd
  · have hb' : b ∈ X := hw2.resolve_left ha
    have hd' : d ∈ X := hw1.resolve_left ha
    exact canonical_case G hG m J n H K φ Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
      hJiso hsub4 hsub.2 w₁ w₂ w₃ w₄ hnd hbv hc₁ hc₂ hc₃ hc₄ hXC ha hb' hd'
  · have ha' : a ∈ X := hw2.resolve_right hb
    have hc' : c ∈ X := hw3.resolve_left hb
    have hnd' : [w₂, w₃, w₄, w₁].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hnd ⊢
      aesop
    have hbv' : branchVertices H = ({w₂, w₃, w₄, w₁} : Set (Fin n)) := by
      rw [hbv]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    have hset :
        ({s(w₂, w₃), s(w₃, w₄), s(w₄, w₁), s(w₁, w₂)} :
          Set (Sym2 (Fin n))) = ({a, b, c, d} : Set (Sym2 (Fin n))) := by
      ext e
      simp only [a, b, c, d, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    apply canonical_case G hG m J n H K φ Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
      hJiso hsub4 hsub.2 w₂ w₃ w₄ w₁ hnd' hbv' hc₂ hc₃ hc₄ hc₁
    · rw [hset]
      simpa [a, b, c, d] using hXC
    · exact hb
    · exact hc'
    · exact ha'
  · have hb' : b ∈ X := hw3.resolve_right hc
    have hd' : d ∈ X := hw4.resolve_left hc
    have hnd' : [w₃, w₄, w₁, w₂].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hnd ⊢
      aesop
    have hbv' : branchVertices H = ({w₃, w₄, w₁, w₂} : Set (Fin n)) := by
      rw [hbv]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    have hset :
        ({s(w₃, w₄), s(w₄, w₁), s(w₁, w₂), s(w₂, w₃)} :
          Set (Sym2 (Fin n))) = ({a, b, c, d} : Set (Sym2 (Fin n))) := by
      ext e
      simp only [a, b, c, d, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    apply canonical_case G hG m J n H K φ Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
      hJiso hsub4 hsub.2 w₃ w₄ w₁ w₂ hnd' hbv' hc₃ hc₄ hc₁ hc₂
    · rw [hset]
      simpa [a, b, c, d] using hXC
    · exact hc
    · exact hd'
    · exact hb'
  · have hc' : c ∈ X := hw4.resolve_right hd
    have ha' : a ∈ X := hw1.resolve_right hd
    have hnd' : [w₄, w₁, w₂, w₃].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hnd ⊢
      aesop
    have hbv' : branchVertices H = ({w₄, w₁, w₂, w₃} : Set (Fin n)) := by
      rw [hbv]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    have hset :
        ({s(w₄, w₁), s(w₁, w₂), s(w₂, w₃), s(w₃, w₄)} :
          Set (Sym2 (Fin n))) = ({a, b, c, d} : Set (Sym2 (Fin n))) := by
      ext e
      simp only [a, b, c, d, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    apply canonical_case G hG m J n H K φ Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
      hJiso hsub4 hsub.2 w₄ w₁ w₂ w₃ hnd' hbv' hc₄ hc₁ hc₂ hc₃
    · rw [hset]
      simpa [a, b, c, d] using hXC
    · exact hd
    · exact ha'
    · exact hc'

end Workspace.ProofLemmas.Thm61Claim1
