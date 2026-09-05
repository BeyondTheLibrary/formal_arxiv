import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.Thm57Claim4Basics

/-!
# 5.7 (4), last paragraph: building the track `P₄` and finishing

PAPER (printed p. 25):

> *"Choose a minimal track in `S` between `s` and the interior of `P₃`; then it can be extended
> via a subpath of `P₃` and via `sv` to become a track `P₄` in `H`, of length `≥ 2`, from `v` to
> `b₃`, using none of `a₁, b₁, a₃`, and with only its first edge in `X`.  But then the tracks
> `b₁-a₁-P₁-b₃`, `P₄`, and the one-edge track made by `x₃`, violate (3)."*

The statement below is that sentence with the names made abstract, so that it can be used on
either side of the symmetry `a ↔ b`, `i ↔ j`: `γ` is the paper's `b₃`, `γ'` its `a₃`, `u` its
`a₁`, `u'` its `b₁`, `P` the track `P₁` and `P3` the track `P₃`.  `S` is the paper's `S`; the
hypotheses record that `S` avoids `P`, that `P3` runs from `γ'` to `γ` through `S`, and that the
new vertex `v` is on none of them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4EndgameOutside

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Basics
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*}

/-- The paper's final three tracks `u'-u-P-γ`, `P₄` and `γγ'`, all out of `γ`. -/
theorem caseVOutP
    (H : SimpleGraph W) (X : Set (Sym2 W))
    (hclaim3 :
      ¬ ∃ (c a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
          (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
        IsTrackFrom H P₁ c a₁ ∧ IsTrackFrom H P₂ c a₂ ∧ IsTrackFrom H P₃ c a₃ ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = c) ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = c) ∧
        (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = c) ∧
        (∃ e ∈ trackEdges P₁, e ∈ X) ∧
        (∃ e ∈ trackEdges P₂, e ∈ X) ∧
        (∃ e ∈ trackEdges P₃, e ∈ X) ∧
        ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
         (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)))
    {P P3 : List W} {S : Set W} {u γ u' γ' s v : W}
    (hP : IsTrackFrom (H.deleteEdges X) P u γ)
    (hP3 : IsTrackFrom (H.deleteEdges X) P3 γ' γ)
    (hSconn : ConnectedSet (H.deleteEdges X) S)
    (hsS : s ∈ S)
    (hPS : ∀ z ∈ P, z ∉ S)
    (hP3S : ∀ z ∈ P3, z = γ ∨ z = γ' ∨ z ∈ S)
    (hex : ∃ z ∈ P3, z ∈ S)
    (hγS : γ ∉ S) (hγ'S : γ' ∉ S)
    (hu'P : u' ∉ P) (hu'S : u' ∉ S) (hu'γ : u' ≠ γ) (hu'γ' : u' ≠ γ')
    (hvP : v ∉ P) (hvS : v ∉ S) (hvγ : v ≠ γ) (hvγ' : v ≠ γ') (hvu' : v ≠ u')
    (hγ'P : γ' ∉ P) (huγ : u ≠ γ)
    (hXu : s(u, u') ∈ X) (hXγ : s(γ, γ') ∈ X) (hXsv : s(s, v) ∈ X)
    (hadju : H.Adj u u') (hadjγ : H.Adj γ γ') (hadjs : H.Adj s v) :
    False := by
  classical
  -- *"Choose a minimal track in `S` between `s` and the interior of `P₃`."*
  obtain ⟨a, ha, p, hp, R, hR, hRS, -, hRclean⟩ :=
    Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack (H.deleteEdges X) S {s}
      {z | z ∈ P3 ∧ z ∈ S} hSconn ⟨s, rfl⟩
      (by obtain ⟨z, hz1, hz2⟩ := hex; exact ⟨z, hz1, hz2⟩)
      (Set.singleton_subset_iff.mpr hsS) (fun z hz => hz.2)
  have has : a = s := ha
  rw [has] at hR
  obtain ⟨hpP3, hpS⟩ := hp
  -- where `p` sits on `P3`
  have hP3ne : 0 < P3.length := List.length_pos_of_ne_nil hP3.1.1
  have hP30 : P3[0]'hP3ne = γ' := getElem_zero_of_head? hP3.2.1 hP3ne
  have hP3l : P3[P3.length - 1]'(by omega) = γ := getElem_last_of_getLast? hP3.2.2 hP3ne
  obtain ⟨n, hn, hpn⟩ := List.mem_iff_getElem.mp hpP3
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hpγ' : p = γ' := by
        rw [← hpn, ← hP30]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 h hn hP3ne
      exact hγ'S (hpγ' ▸ hpS)
    · exact h
  have hnl : n < P3.length - 1 := by
    rcases lt_or_eq_of_le (show n ≤ P3.length - 1 by omega) with h | h
    · exact h
    · exfalso
      have hpγ : p = γ := by
        rw [← hpn, ← hP3l]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 h hn (by omega)
      exact hγS (hpγ ▸ hpS)
  -- the piece of `P3` from `p` to `γ`
  have hSuf : IsTrackFrom (H.deleteEdges X) (slice P3 n (P3.length - 1)) p γ := by
    have h := isTrackFrom_slice (i := n) (j := P3.length - 1) hP3.1
      (show P3.length - 1 < P3.length by omega) (by omega)
    rw [hP3l, hpn] at h
    exact h
  have hSufP3 : ∀ z ∈ slice P3 n (P3.length - 1), z ∈ P3 := fun z hz => mem_of_mem_slice hz
  have hSufr : IsTrackFrom (H.deleteEdges X) (slice P3 n (P3.length - 1)).reverse γ p :=
    isTrackFrom_reverse hSuf
  have hRr : IsTrackFrom (H.deleteEdges X) R.reverse p s := isTrackFrom_reverse hR
  have hcommon : ∀ z : W, z ∈ (slice P3 n (P3.length - 1)).reverse → z ∈ R.reverse → z = p := by
    intro z h1 h2
    exact hRclean z (List.mem_reverse.mp h2)
      ⟨hSufP3 z (List.mem_reverse.mp h1), hRS z (List.mem_reverse.mp h2)⟩
  obtain ⟨hW, hWmem⟩ :=
    Workspace.ProofLemmas.TrackGlueAtCommonEndpoint (H.deleteEdges X)
      (slice P3 n (P3.length - 1)).reverse R.reverse γ p s hSufr hRr hcommon
  set Wk : List W := (slice P3 n (P3.length - 1)).reverse ++ R.reverse.tail with hWkdef
  -- `Wk` is a track from `γ` to `s`
  have hWne : 0 < Wk.length := List.length_pos_of_ne_nil hW.1.1
  have hW0 : Wk[0]'hWne = γ := getElem_zero_of_head? hW.2.1 hWne
  have hWl : Wk[Wk.length - 1]'(by omega) = s := getElem_last_of_getLast? hW.2.2 hWne
  have hγs : γ ≠ s := fun h => hγS (h ▸ hsS)
  have hWlen : 2 ≤ Wk.length := by
    by_contra hc
    have h1 : Wk.length = 1 := by omega
    apply hγs
    rw [← hW0, ← hWl]
    exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Wk
      (by omega) hWne (by omega))
  -- `v` is on none of the pieces
  have hvW : v ∉ Wk := by
    intro hz
    rcases hWmem v hz with h | h
    · rcases hP3S v (hSufP3 v (List.mem_reverse.mp h)) with h' | h' | h'
      · exact hvγ h'
      · exact hvγ' h'
      · exact hvS h'
    · exact hvS (hRS v (List.mem_reverse.mp h))
  have hu'W : u' ∉ Wk := by
    intro hz
    rcases hWmem u' hz with h | h
    · rcases hP3S u' (hSufP3 u' (List.mem_reverse.mp h)) with h' | h' | h'
      · exact hu'γ h'
      · exact hu'γ' h'
      · exact hu'S h'
    · exact hu'S (hRS u' (List.mem_reverse.mp h))
  have hγ'W : γ' ∉ Wk := by
    intro hz
    rcases hWmem γ' hz with h | h
    · obtain ⟨k, hk, hnk, -, hkγ'⟩ :=
        (mem_slice_iff (show P3.length - 1 < P3.length by omega) (by omega)).mp
          (List.mem_reverse.mp h)
      have hk0 : k = 0 := by
        have heq : P3[k]'hk = P3[0]'hP3ne := by rw [hkγ', hP30]
        exact (List.Nodup.getElem_inj_iff hP3.1.2.1).mp heq
      omega
    · exact hγ'S (hRS γ' (List.mem_reverse.mp h))
  -- the three tracks out of `γ`
  have hPr : IsTrackFrom (H.deleteEdges X) P.reverse γ u := isTrackFrom_reverse hP
  have hu'Pr : u' ∉ P.reverse := fun h => hu'P (List.mem_reverse.mp h)
  have hT2 : IsTrackFrom H (P.reverse ++ [u']) γ u' :=
    isTrackFrom_concat (isTrackFrom_of_delete hPr) hadju hu'Pr
  have hT3 : IsTrackFrom H (Wk ++ [v]) γ v :=
    isTrackFrom_concat (isTrackFrom_of_delete hW) hadjs hvW
  have hT1 : IsTrackFrom H ([γ, γ'] : List W) γ γ' := by
    refine ⟨⟨by simp, by simp [hadjγ.ne], ?_⟩, by simp, by simp⟩
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using hadjγ
  -- lengths
  have hPlen : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  have hP0 : P[0]'hPlen = u := getElem_zero_of_head? hP.2.1 hPlen
  have hPl : P[P.length - 1]'(by omega) = γ := getElem_last_of_getLast? hP.2.2 hPlen
  have hPlen2 : 2 ≤ P.length := by
    by_contra hc
    have h1 : P.length = 1 := by omega
    apply huγ
    rw [← hP0, ← hPl]
    exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P
      (by omega) hPlen (by omega))
  have hlen2 : 2 ≤ (P.reverse ++ [u']).length := by
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]; omega
  have hlen3 : 2 ≤ (Wk ++ [v]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hlen1 : 2 ≤ ([γ, γ'] : List W).length := by simp
  -- the marked edges on the three tracks
  have hE2 : s(u, u') ∈ trackEdges (P.reverse ++ [u']) := by
    have hlast := getElem_last_of_getLast? hPr.2.2 (by simp only [List.length_reverse]; omega)
    have h := last_edge_mem_concat (by simp only [List.length_reverse]; omega : 0 < P.reverse.length) u'
    rwa [hlast] at h
  have hE3 : s(s, v) ∈ trackEdges (Wk ++ [v]) := by
    have h := last_edge_mem_concat (by omega : 0 < Wk.length) v
    rwa [hWl] at h
  have hE1 : s(γ, γ') ∈ trackEdges ([γ, γ'] : List W) := ⟨0, by simp, by simp⟩
  -- the first edges
  have hF2 : s((P.reverse ++ [u'])[0]'(by omega), (P.reverse ++ [u'])[1]'(by omega)) ∉ X := by
    rw [first_edge_concat (by simp only [List.length_reverse]; omega : 2 ≤ P.reverse.length)]
    exact edge_not_mem_of_delete hPr.1 (by simp only [List.length_reverse]; omega)
  have hF3 : s((Wk ++ [v])[0]'(by omega), (Wk ++ [v])[1]'(by omega)) ∉ X := by
    rw [first_edge_concat (by omega : 2 ≤ Wk.length)]
    exact edge_not_mem_of_delete hW.1 (by omega)
  -- pairwise disjointness away from `γ`
  have hd23 : ∀ z : W, z ∈ P.reverse ++ [u'] → z ∈ Wk ++ [v] → z = γ := by
    intro z h2 h3
    rcases mem_concat_iff.mp h2 with h2 | h2 <;> rcases mem_concat_iff.mp h3 with h3 | h3
    · have hzP : z ∈ P := List.mem_reverse.mp h2
      rcases hWmem z h3 with h | h
      · rcases hP3S z (hSufP3 z (List.mem_reverse.mp h)) with h' | h' | h'
        · exact h'
        · exact absurd (h' ▸ hzP) hγ'P
        · exact absurd h' (hPS z hzP)
      · exact absurd (hRS z (List.mem_reverse.mp h)) (hPS z hzP)
    · exact absurd (h3 ▸ List.mem_reverse.mp h2) hvP
    · exact absurd (h2 ▸ h3) hu'W
    · exact absurd (h2.symm.trans h3) (Ne.symm hvu')
  have hd21 : ∀ z : W, z ∈ P.reverse ++ [u'] → z ∈ ([γ, γ'] : List W) → z = γ := by
    intro z h2 h1
    rcases List.mem_pair.mp h1 with rfl | rfl
    · rfl
    · rcases mem_concat_iff.mp h2 with h2 | h2
      · exact absurd (List.mem_reverse.mp h2) hγ'P
      · exact absurd h2.symm hu'γ'
  have hd31 : ∀ z : W, z ∈ Wk ++ [v] → z ∈ ([γ, γ'] : List W) → z = γ := by
    intro z h3 h1
    rcases List.mem_pair.mp h1 with rfl | rfl
    · rfl
    · rcases mem_concat_iff.mp h3 with h3 | h3
      · exact absurd h3 hγ'W
      · exact absurd h3.symm hvγ'
  exact hclaim3 ⟨γ, u', v, γ',
    P.reverse ++ [u'], Wk ++ [v], [γ, γ'],
    hlen2, hlen3, hlen1, hT2, hT3, hT1, hd23, hd21, hd31,
    ⟨_, hE2, hXu⟩, ⟨_, hE3, hXsv⟩, ⟨_, hE1, hXγ⟩, Or.inl ⟨hF2, hF3⟩⟩

end Workspace.ProofLemmas.Thm57Claim4EndgameOutside
