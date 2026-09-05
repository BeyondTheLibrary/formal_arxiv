import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose

/-!
# The ends of a branch of a subdivision are branch-vertices, and are nonadjacent

PAPER (proof of 7.5, claim (1), printed p. 35): *"… and they have length `≥ 3` since `c₁, c₂` are
nonadjacent (for they are the ends of a branch of length `> 1`.)"*
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75BranchEnds

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-! ### List end lemmas -/

private theorem head_getElem {α : Type*} {l : List α} {a : α} (h : l.head? = some a)
    (h0 : 0 < l.length) : l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

private theorem last_getElem {α : Type*} {l : List α} {b : α} (h : l.getLast? = some b)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = b := by
  have hne : l ≠ [] := by intro hc; subst hc; simp at h0
  have h1 : l.getLast? = some (l.getLast hne) := List.getLast?_eq_some_getLast hne
  rw [h] at h1
  have h2 : b = l.getLast hne := Option.some_injective _ h1
  rw [h2]
  exact (List.getLast_eq_getElem hne).symm

/-! ### Elementary track facts -/

section TrackFacts

variable {W : Type*}

private theorem mem_of_mem_trackEdges {q : List W} {e : Sym2 W} (he : e ∈ trackEdges q)
    {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

/-- A vertex of a `Nodup` track lying on **two different** edges of the track is an internal
vertex of it.  (Contrapositive: an end of a track lies on exactly one of its edges.) -/
private theorem mem_trackInterior_of_two_edges {q : List W} (hnd : q.Nodup)
    {e f : Sym2 W} (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q) (hef : e ≠ f)
    {w : W} (hwe : w ∈ e) (hwf : w ∈ f) : w ∈ trackInterior q := by
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  rw [SubdivisionCounting.mem_trackInterior_iff]
  rcases Sym2.mem_iff.mp hwe with h1 | h1 <;> rcases Sym2.mem_iff.mp hwf with h2 | h2
  · exfalso
    have hij : i = j := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    subst hij
    exact hef rfl
  · -- `w = q[i] = q[j+1]`, so `w` sits at the internal position `j + 1`
    have hij : i = j + 1 := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    exact ⟨j, by omega, h2.symm⟩
  · have hij : i + 1 = j := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    exact ⟨i, by omega, h1.symm⟩
  · exfalso
    have h : i + 1 = j + 1 := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    have hij : i = j := by omega
    subst hij
    exact hef rfl

/-- A track on two vertices has exactly one edge. -/
private theorem trackEdges_of_length_two {q : List W} (h2 : q.length = 2) {e : Sym2 W}
    (he : e ∈ trackEdges q) : e = s(q[0]'(by omega), q[1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  rw [h2] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  rfl

end TrackFacts

/-! ### Subdivision facts -/

section SubdivisionFacts

variable {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

private theorem mem_trackInterior_of_not_range
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    {u v : U} (huv : J.Adj u v) {w : W} (hw : w ∈ T u v) (hnr : w ∉ Set.range ι) :
    w ∈ trackInterior (T u v) := by
  by_contra hcon
  rcases SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1
    (htrack u v huv).2.2 hw hcon with h | h
  · exact hnr ⟨u, h.symm⟩
  · exact hnr ⟨v, h.symm⟩

private theorem trackEdges_eq_of_sym2_eq
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    {u v u' v' : U} (huv : J.Adj u v) (h : s(u, v) = s(u', v')) :
    trackEdges (T u' v') = trackEdges (T u v) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [hrev _ _ huv, SubdivisionCounting.trackEdges_reverse]

/-- PAPER (printed pp. 19–20, used silently throughout §§5–8): **a branch of a subdivision `H`
of `J` is one of the tracks that the subdivision attaches to the edges of `J`.**

The argument is the paper's: consecutive edges of the branch share an internal vertex of the
branch, which is not a branch-vertex, hence not a vertex of `J`, hence internal to whichever
track of the subdivision carries it — so the two tracks coincide.  All the edges of the branch
therefore lie on a single track, and maximality of the branch makes the two equal. -/
private theorem exists_track_of_branch
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hrange : Set.range ι ⊆ branchVertices H) (hbrsub : branchVertices H ⊆ Set.range ι)
    {B : List W} (hbranch : IsBranch H B) (hBlen : 2 ≤ B.length) :
    ∃ u v : U, J.Adj u v ∧ trackEdges (T u v) = trackEdges B ∧ ∀ w ∈ B, w ∈ T u v := by
  classical
  have hlab : ∀ (i : ℕ) (hi : i + 1 < B.length),
      ∃ u v : U, J.Adj u v ∧ s(B[i]'(by omega), B[i + 1]'hi) ∈ trackEdges (T u v) := by
    intro i hi
    have hmem : s(B[i]'(by omega), B[i + 1]'hi) ∈ H.edgeSet := hbranch.1.2.2 i hi
    rw [hedges] at hmem
    simpa using hmem
  obtain ⟨u₀, v₀, huv₀, he₀⟩ := hlab 0 (by omega)
  have hall : ∀ (i : ℕ) (hi : i + 1 < B.length),
      s(B[i]'(by omega), B[i + 1]'hi) ∈ trackEdges (T u₀ v₀) := by
    intro i
    induction i with
    | zero => intro hi; exact he₀
    | succ n ih =>
      intro hi
      have hn : n + 1 < B.length := by omega
      have hprev := ih hn
      obtain ⟨u, v, huv, he⟩ := hlab (n + 1) hi
      have hwint : B[n + 1]'hn ∈ trackInterior B :=
        SubdivisionCounting.mem_trackInterior_getElem B n (by omega)
      have hwnb : B[n + 1]'hn ∉ branchVertices H := hbranch.2.1 _ hwint
      have hwnr : B[n + 1]'hn ∉ Set.range ι := fun hc => hwnb (hrange hc)
      have hw₀ : B[n + 1]'hn ∈ T u₀ v₀ := mem_of_mem_trackEdges hprev (by simp)
      have hw₁ : B[n + 1]'hn ∈ T u v := mem_of_mem_trackEdges he (by simp)
      have hi₀ : B[n + 1]'hn ∈ trackInterior (T u₀ v₀) :=
        mem_trackInterior_of_not_range htrack huv₀ hw₀ hwnr
      have hsame : s(u₀, v₀) = s(u, v) := by
        by_contra hcon
        exact hdisj u₀ v₀ u v huv₀ huv hcon _ hi₀ hw₁
      rw [trackEdges_eq_of_sym2_eq hrev huv₀ hsame] at he
      exact he
  have hsubE : trackEdges B ⊆ trackEdges (T u₀ v₀) := by
    rintro e ⟨i, hi, rfl⟩
    exact hall i hi
  have hsubV : ∀ w ∈ B, w ∈ T u₀ v₀ := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    by_cases hlast : i + 1 < B.length
    · exact mem_of_mem_trackEdges (hall i hlast) (by simp)
    · have hi' : i = B.length - 1 := by omega
      subst hi'
      refine mem_of_mem_trackEdges (hall (B.length - 2) (by omega)) ?_
      have hidx : B.length - 2 + 1 = B.length - 1 := by omega
      rw [SubdivisionCounting.getElem_eq_of_index_eq B hidx (by omega) (by omega)]
      simp
  have hTint : ∀ w ∈ trackInterior (T u₀ v₀), w ∉ branchVertices H := fun w hw hcon =>
    hnew u₀ v₀ huv₀ w hw (hbrsub hcon)
  exact ⟨u₀, v₀, huv₀,
    hbranch.2.2 (T u₀ v₀) (htrack u₀ v₀ huv₀).1 hTint hsubE hsubV, hsubV⟩

end SubdivisionFacts

/-- The two named ends of any nontrivial branch of a subdivision of a 3-connected graph are
branch-vertices.  This is the endpoint part of `thm75BranchEnds`, without the stronger
length-two hypothesis needed there to prove that the ends are nonadjacent. -/
theorem branchEnds_mem_branchVertices {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hlen : 1 ≤ trackLength B) :
    c₁ ∈ branchVertices H ∧ c₂ ∈ branchVertices H := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen1, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen1 hdisj hnew hdeg
  have hbrsub : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hL : 2 ≤ B.length := by
    simp only [trackLength] at hlen
    omega
  have hnd : B.Nodup := hbranch.1.2.1
  have hB0 : B[0]'(by omega) = c₁ := head_getElem hfrom.2.1 (by omega)
  have hBl : B[B.length - 1]'(by omega) = c₂ := last_getElem hfrom.2.2 (by omega)
  have hc1B : c₁ ∈ B := List.mem_of_mem_head? hfrom.2.1
  have hc2B : c₂ ∈ B := List.mem_of_mem_getLast? hfrom.2.2
  obtain ⟨u, v, huv, hTB, hsubV⟩ :=
    exists_track_of_branch htrack hrev hdisj hnew hedges hrange hbrsub hbranch hL
  have key : ∀ c ∈ B, c ∉ trackInterior B → c ∈ branchVertices H := by
    intro c hcB hcint
    by_contra hcon
    have hnr : c ∉ Set.range ι := fun hc => hcon (hrange hc)
    have hint : c ∈ trackInterior (T u v) :=
      mem_trackInterior_of_not_range htrack huv (hsubV c hcB) hnr
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff (T u v) c).mp hint
    have hndT : (T u v).Nodup := (htrack u v huv).1.2.1
    have he1 : s((T u v)[j]'(by omega), (T u v)[j + 1]'(by omega)) ∈ trackEdges (T u v) :=
      ⟨j, by omega, rfl⟩
    have he2 : s((T u v)[j + 1]'(by omega), (T u v)[j + 2]'(by omega)) ∈
        trackEdges (T u v) := ⟨j + 1, by omega, rfl⟩
    have hdist : s((T u v)[j]'(by omega), (T u v)[j + 1]'(by omega)) ≠
        s((T u v)[j + 1]'(by omega), (T u v)[j + 2]'(by omega)) := by
      intro hcon2
      rcases Sym2.eq_iff.mp hcon2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · have : j = j + 1 := (hndT.getElem_inj_iff).mp h1
        omega
      · have : j = j + 2 := (hndT.getElem_inj_iff).mp h1
        omega
    refine hcint (mem_trackInterior_of_two_edges hnd (hTB ▸ he1) (hTB ▸ he2) hdist ?_ ?_)
    · exact Sym2.mem_iff.mpr (Or.inr hjc.symm)
    · exact Sym2.mem_iff.mpr (Or.inl hjc.symm)
  have hc1int : c₁ ∉ trackInterior B := by
    intro hcon
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff B c₁).mp hcon
    have h0 : j + 1 = 0 := (hnd.getElem_inj_iff).mp (by rw [hjc, hB0])
    omega
  have hc2int : c₂ ∉ trackInterior B := by
    intro hcon
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff B c₂).mp hcon
    have h0 : j + 1 = B.length - 1 := (hnd.getElem_inj_iff).mp (by rw [hjc, hBl])
    omega
  exact ⟨key c₁ hc1B hc1int, key c₂ hc2B hc2int⟩

/-- The two ends of a branch of length `≥ 2` of a subdivision of a 3-connected graph are distinct
branch-vertices, and are nonadjacent. -/
theorem thm75BranchEnds {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂) (hlen : 2 ≤ trackLength B) :
    c₁ ≠ c₂ ∧ c₁ ∈ branchVertices H ∧ c₂ ∈ branchVertices H ∧ ¬ H.Adj c₁ c₂ := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen1, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen1 hdisj hnew hdeg
  have hbrsub : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hL : 3 ≤ B.length := by
    simp only [trackLength] at hlen; omega
  have hnd : B.Nodup := hbranch.1.2.1
  have hB0 : B[0]'(by omega) = c₁ := head_getElem hfrom.2.1 (by omega)
  have hBl : B[B.length - 1]'(by omega) = c₂ := last_getElem hfrom.2.2 (by omega)
  have hc1B : c₁ ∈ B := List.mem_of_mem_head? hfrom.2.1
  have hc2B : c₂ ∈ B := List.mem_of_mem_getLast? hfrom.2.2
  -- (a) the two ends are distinct
  have hne : c₁ ≠ c₂ := by
    intro hcon
    have h0 : (0 : ℕ) = B.length - 1 :=
      (hnd.getElem_inj_iff).mp (by rw [hB0, hBl, hcon])
    omega
  -- the branch is one of the subdivision's tracks
  obtain ⟨u, v, huv, hTB, hsubV⟩ :=
    exists_track_of_branch htrack hrev hdisj hnew hedges hrange hbrsub hbranch (by omega)
  -- (b) a vertex of `B` which is not internal to `B` is a branch-vertex: otherwise it is a new
  -- vertex of the subdivision, hence internal to `T u v`, hence on two edges of
  -- `trackEdges (T u v) = trackEdges B`, hence internal to `B`.
  have key : ∀ c ∈ B, c ∉ trackInterior B → c ∈ branchVertices H := by
    intro c hcB hcint
    by_contra hcon
    have hnr : c ∉ Set.range ι := fun hc => hcon (hrange hc)
    have hint : c ∈ trackInterior (T u v) :=
      mem_trackInterior_of_not_range htrack huv (hsubV c hcB) hnr
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff (T u v) c).mp hint
    have hndT : (T u v).Nodup := (htrack u v huv).1.2.1
    have he1 : s((T u v)[j]'(by omega), (T u v)[j + 1]'(by omega)) ∈ trackEdges (T u v) :=
      ⟨j, by omega, rfl⟩
    have he2 : s((T u v)[j + 1]'(by omega), (T u v)[j + 2]'(by omega)) ∈ trackEdges (T u v) :=
      ⟨j + 1, by omega, rfl⟩
    have hdist : s((T u v)[j]'(by omega), (T u v)[j + 1]'(by omega)) ≠
        s((T u v)[j + 1]'(by omega), (T u v)[j + 2]'(by omega)) := by
      intro hcon2
      rcases Sym2.eq_iff.mp hcon2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · have : j = j + 1 := (hndT.getElem_inj_iff).mp h1
        omega
      · have : j = j + 2 := (hndT.getElem_inj_iff).mp h1
        omega
    refine hcint (mem_trackInterior_of_two_edges hnd (hTB ▸ he1) (hTB ▸ he2) hdist ?_ ?_)
    · exact Sym2.mem_iff.mpr (Or.inr hjc.symm)
    · exact Sym2.mem_iff.mpr (Or.inl hjc.symm)
  have hc1int : c₁ ∉ trackInterior B := by
    intro hcon
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff B c₁).mp hcon
    have h0 : j + 1 = 0 := (hnd.getElem_inj_iff).mp (by rw [hjc, hB0])
    omega
  have hc2int : c₂ ∉ trackInterior B := by
    intro hcon
    obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff B c₂).mp hcon
    have h0 : j + 1 = B.length - 1 := (hnd.getElem_inj_iff).mp (by rw [hjc, hBl])
    omega
  have hc1 : c₁ ∈ branchVertices H := key c₁ hc1B hc1int
  have hc2 : c₂ ∈ branchVertices H := key c₂ hc2B hc2int
  refine ⟨hne, hc1, hc2, ?_⟩
  -- (c) the two ends are nonadjacent: the edge `c₁c₂` would be a whole track of the subdivision
  -- joining the same two vertices of `J` as the branch, i.e. a parallel edge of `J`.
  intro hadj
  obtain ⟨a, ha⟩ := hbrsub hc1
  obtain ⟨b, hb⟩ := hbrsub hc2
  have hmem : s(c₁, c₂) ∈ H.edgeSet := hadj
  rw [hedges] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨u', v', hu'v', hme⟩ := hmem
  obtain ⟨i, hi, hie⟩ := hme
  have hends : ∀ w : W, w = c₁ ∨ w = c₂ → w ∉ trackInterior (T u' v') := by
    rintro w (rfl | rfl) hcon
    · exact hnew u' v' hu'v' _ hcon ⟨a, ha⟩
    · exact hnew u' v' hu'v' _ hcon ⟨b, hb⟩
  have hpair : ((T u' v')[i]'(by omega) = c₁ ∧ (T u' v')[i + 1]'hi = c₂) ∨
      ((T u' v')[i]'(by omega) = c₂ ∧ (T u' v')[i + 1]'hi = c₁) := by
    rcases Sym2.eq_iff.mp hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  have hlen2 : (T u' v').length = 2 := by
    refine SubdivisionCounting.track_edge_len_two _ i hi ?_ ?_
    · rcases hpair with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hends _ (Or.inl h1)
      · exact hends _ (Or.inr h1)
    · rcases hpair with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hends _ (Or.inr h2)
      · exact hends _ (Or.inl h2)
  have hix : i = 0 := by omega
  have hT'0 : (T u' v')[i]'(by omega) = ι u' := by
    rw [SubdivisionCounting.getElem_eq_of_index_eq (T u' v') hix (by omega) (by omega)]
    exact SubdivisionCounting.track_head (htrack u' v' hu'v') (by omega)
  have hT'1 : (T u' v')[i + 1]'hi = ι v' := by
    rw [SubdivisionCounting.getElem_eq_of_index_eq (T u' v') (show i + 1 = 1 by omega) hi
      (by omega)]
    exact SubdivisionCounting.track_last (htrack u' v' hu'v') hlen2
  -- `{c₁, c₂} = {ι u', ι v'}`
  have hsym' : s(ι u', ι v') = s(c₁, c₂) := by
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hT'0, ← hT'1, h1, h2]
    · rw [← hT'0, ← hT'1, h1, h2, Sym2.eq_swap]
  -- `{c₁, c₂}` is also the pair of ends of `T u v`
  have hc1e : c₁ = ι u ∨ c₁ = ι v :=
    SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1 (htrack u v huv).2.2
      (hsubV c₁ hc1B) (fun hcon => hnew u v huv c₁ hcon ⟨a, ha⟩)
  have hc2e : c₂ = ι u ∨ c₂ = ι v :=
    SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1 (htrack u v huv).2.2
      (hsubV c₂ hc2B) (fun hcon => hnew u v huv c₂ hcon ⟨b, hb⟩)
  have hsym : s(ι u, ι v) = s(c₁, c₂) := by
    rcases hc1e with h1 | h1 <;> rcases hc2e with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
    · exact absurd (h1.trans h2.symm) hne
  -- so `u'v'` and `uv` are the same edge of `J`
  have hJedge : s(u, v) = s(u', v') := by
    have h : s(ι u, ι v) = s(ι u', ι v') := hsym.trans hsym'.symm
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hι h1, hι h2]
    · rw [hι h1, hι h2, Sym2.eq_swap]
  have hTT : trackEdges (T u' v') = trackEdges B :=
    (trackEdges_eq_of_sym2_eq hrev huv hJedge).trans hTB
  -- but `B` has at least two edges, while `T u' v'` has exactly one
  have hEa : s(B[0]'(by omega), B[1]'(by omega)) ∈ trackEdges B := ⟨0, by omega, rfl⟩
  have hEb : s(B[1]'(by omega), B[2]'(by omega)) ∈ trackEdges B := ⟨1, by omega, rfl⟩
  have ha' := trackEdges_of_length_two hlen2 (hTT ▸ hEa)
  have hb' := trackEdges_of_length_two hlen2 (hTT ▸ hEb)
  have habeq : s(B[0]'(by omega), B[1]'(by omega)) = s(B[1]'(by omega), B[2]'(by omega)) :=
    ha'.trans hb'.symm
  rcases Sym2.eq_iff.mp habeq with ⟨h1, -⟩ | ⟨h1, -⟩
  · have : (0 : ℕ) = 1 := (hnd.getElem_inj_iff).mp h1
    omega
  · have : (0 : ℕ) = 2 := (hnd.getElem_inj_iff).mp h1
    omega

end Workspace.ProofLemmas.Thm75BranchEnds
