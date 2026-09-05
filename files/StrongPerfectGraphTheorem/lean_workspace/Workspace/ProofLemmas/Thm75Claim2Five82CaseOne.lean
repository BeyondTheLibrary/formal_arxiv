import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary
import Workspace.ProofLemmas.Thm75Claim2Five82Splice
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps
import Workspace.ProofLemmas.RungReplacementLabelled

/-!
# Case 1 of 5.8.2 when the replaced branch is the distinguished branch

PAPER (proof of 7.5, claim (2), printed p. 37): *"In case 1, let `R′` be the (unique) path from
`p₁` to `s₂` in `(V(P) ∪ V(Rb₁b₂)) \ {s₁}` … So if in `L(H)` we replace `Rb₁b₂` by `R′` we
obtain another appearance of `J` in `G`, say `L(H′)`."*

This module carries out that replacement when `Bb₁b₂` is the distinguished branch `Bc₁c₂`, and
records what the new appearance looks like: the clique at `c₁` exchanges the old rung end `r₁`
for `p₁`, the clique at `c₂` is unchanged (the replacement path ends at the old `r₂`), and the
new distinguished rung is the replacement path itself, which meets the old appearance only
inside the old rung and meets `F` at `p₁`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseOne

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance
open Workspace.ProofLemmas.RungReplacementLabelled

/-- **The outcome of the case-1 replacement on the distinguished branch.**

The hypotheses are the appearance, its distinguished odd branch `Bc₁c₂` with rung `R` and rung
ends `r₁, r₂`, the path `P` of the connected set (which avoids the appearance), and the case-1
attachment pattern.  The conclusion names the new appearance, its two endpoint cliques, the
7.4 relation between the old and the new clique at `c₁`, and where the new rung sits. -/
theorem case_one_outcome {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List (Fin m)) (c₁ c₂ : Fin m) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (R : List V) (hRs : {x : V | x ∈ R} = rungSet G H K φ B)
    (r₁ r₂ : V)
    (hr₁ : NSet G H K φ c₁ ∩ {x : V | x ∈ R} = {r₁})
    (hr₂ : NSet G H K φ c₂ ∩ {x : V | x ∈ R} = {r₂})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (hcase : (∀ x ∈ NSet G H K φ c₁ \ {r₁}, G.Adj p₁ x) ∧
      (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
        (x = p₁ ∧ y ∈ NSet G H K φ c₁ \ {r₁}) ∨
        (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) :
    ∃ a : BranchAppearance G J,
      a.leftClique = (NSet G H K φ c₁ \ {r₁}) ∪ {p₁} ∧
      a.rightClique = NSet G H K φ c₂ ∧
      SingleCliqueSwap G (NSet G H K φ c₁) (NSet G H K φ c₂) a.leftClique ∧
      K \ {x : V | x ∈ R} ⊆ a.K ∧
      a.rung ∩ K ⊆ {x : V | x ∈ R} ∧
      p₁ ∈ a.rung := by
  classical
  -- the canonical oriented rung of the distinguished branch
  have h2 : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
  obtain ⟨-, hb₁, hb₂, -⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂
      hbranch hfrom (by omega)
  set Q : List V := trackRung φ B hbranch.1 with hQdef
  have hQset : {x : V | x ∈ Q} = {x : V | x ∈ R} := by
    rw [hRs]
    ext x
    exact mem_trackRung_iff φ hbranch.1
  have hQrung : {x : V | x ∈ Q} = rungSet G H K φ B := by rw [hQset, hRs]
  have hQK : ∀ x ∈ Q, x ∈ K := trackRung_subset_K φ B hbranch.1
  have hr₁Q : NSet G H K φ c₁ ∩ {x : V | x ∈ Q} = {r₁} := by rw [hQset]; exact hr₁
  have hr₂Q : NSet G H K φ c₂ ∩ {x : V | x ∈ Q} = {r₂} := by rw [hQset]; exact hr₂
  -- the ends of the canonical rung are `r₁` and `r₂`
  have hfirst : firstRungVertex φ B hbranch.1 h2 = r₁ := by
    have hmem : firstRungVertex φ B hbranch.1 h2 ∈ NSet G H K φ c₁ ∩ {x : V | x ∈ Q} :=
      ⟨by
        refine ⟨firstTrackEdge B h2, firstTrackEdge_mem hbranch.1 h2, ?_, rfl⟩
        exact ⟨firstTrackEdge_mem hbranch.1 h2, firstTrackEdge_contains hfrom h2⟩,
        firstRungVertex_mem φ hbranch.1 h2⟩
    rw [hr₁Q] at hmem
    exact hmem
  have hlast : lastRungVertex φ B hbranch.1 h2 = r₂ := by
    have hmem : lastRungVertex φ B hbranch.1 h2 ∈ NSet G H K φ c₂ ∩ {x : V | x ∈ Q} :=
      ⟨by
        refine ⟨lastTrackEdge B h2, lastTrackEdge_mem hbranch.1 h2, ?_, rfl⟩
        exact ⟨lastTrackEdge_mem hbranch.1 h2, lastTrackEdge_contains hfrom h2⟩,
        lastRungVertex_mem φ hbranch.1 h2⟩
    rw [hr₂Q] at hmem
    exact hmem
  have hQfrom : IsPathFrom G Q r₁ r₂ := by
    have := trackRung_isPathFrom_ends φ hfrom h2
    rwa [hfirst, hlast] at this
  -- the boundary dictionary of the old rung
  have hbdry : ∀ x ∈ Q, ∀ y ∈ K, y ∉ Q →
      (G.Adj x y ↔ (x = r₁ ∧ y ∈ NSet G H K φ c₁) ∨ (x = r₂ ∧ y ∈ NSet G H K φ c₂)) := by
    intro x hx y hyK hyQ
    have := Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary.rung_boundary
      φ hbranch hfrom h2 (x := x) (y := y) hx hyK hyQ
    rwa [hfirst, hlast] at this
  -- the splice
  obtain ⟨R', hR'from, hR'disj, hp₁R', hr₂R', hR'bdry⟩ :=
    Workspace.ProofLemmas.Thm75Claim2Five82Splice.case_one_splice
      (G := G) K (NSet G H K φ c₁) (NSet G H K φ c₂) Q r₁ r₂ hQfrom hQK hr₁Q hbdry
      P p₁ p₂ hP hPK hcase.1 (by
        obtain ⟨x, hx, hadj⟩ := hcase.2.1
        exact ⟨x, ⟨by rw [hQset]; exact hx.1, hx.2⟩, hadj⟩)
      (fun x hx y hy hyr hadj => by
        rcases hcase.2.2 x hx y hy hyr hadj with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by rw [hQset]; exact h.2.1, h.2.2⟩)
  -- the two ends of the replacement path are distinct, because `p₁` is outside the appearance
  have hp₁K : p₁ ∉ K := hPK p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP).1
  have hr₂K : r₂ ∈ K := hQK r₂ (Workspace.ProofLemmas.PathBasics.getLast_mem hQfrom.2.2)
  have hne : p₁ ≠ r₂ := fun hc => hp₁K (hc ▸ hr₂K)
  -- parity, and hence the length of the new branch
  have hQeven : Even (pathLength Q) := by
    rw [hQdef, trackRung_pathLength]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hpar : Even (pathLength R') ↔ Even (pathLength Q) :=
    Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.case_one_parity
      G hG J hJ H K φ happ B c₁ c₂ hb₁ hb₂ hbranch hfrom h2 r₁ r₂ hr₁Q hr₂Q
      R' p₁ r₂ hR'from hne hR'disj hR'bdry
  have hR'even : Even (pathLength R') := hpar.mpr hQeven
  have hR'len : 2 ≤ pathLength R' := by
    have h1 : 1 ≤ pathLength R' := by
      rcases Nat.eq_zero_or_pos (pathLength R') with h0 | hpos
      · exfalso
        have hlen1 : R'.length = 1 := by
          have := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hR'from.1
          omega
        obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hlen1
        have hh := hR'from.2.1
        have hl := hR'from.2.2
        rw [hu] at hh hl
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
        exact hne (hh.symm.trans hl)
      · exact hpos
    obtain ⟨k, hk⟩ := hR'even
    omega
  -- the replacement
  obtain ⟨res⟩ := Workspace.ProofLemmas.RungReplacementLabelled.rungReplacement
    G J hJ H K φ happ B c₁ c₂ hb₁ hb₂ hbranch hfrom Q hQfrom.1 hQrung r₁ r₂ hr₁Q hr₂Q
    R' p₁ r₂ hR'from hR'disj hR'bdry hpar
  have hr₂N : r₂ ∈ NSet G H K φ c₂ := by
    have : r₂ ∈ NSet G H K φ c₂ ∩ {x : V | x ∈ Q} := by rw [hr₂Q]; rfl
    exact this.1
  refine ⟨{ m := res.m
            H := res.H'
            K := res.K'
            φ := res.φ'
            happ := res.happ
            B := res.q'
            c₁ := res.ι c₁
            c₂ := res.ι c₂
            hbranch := res.hq'
            hfrom := res.hq'from
            hodd := ?_
            hlen := ?_ }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [res.hq'len]; exact hR'even.add_one
  · rw [res.hq'len]; omega
  · show NSet G res.H' res.K' res.φ' (res.ι c₁) = _
    rw [res.hleft]
  · show NSet G res.H' res.K' res.φ' (res.ι c₂) = _
    rw [res.hright]
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact (show x = r₂ from hx) ▸ hr₂N
    · intro hx
      by_cases hxr : x = r₂
      · exact Or.inr hxr
      · exact Or.inl ⟨hx, hxr⟩
  · have hleft : NSet G res.H' res.K' res.φ' (res.ι c₁) = (NSet G H K φ c₁ \ {r₁}) ∪ {p₁} :=
      res.hleft
    show SingleCliqueSwap G _ _ (NSet G res.H' res.K' res.φ' (res.ι c₁))
    rw [hleft]
    exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.case_one_single_clique_swap
      G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen r₁ r₂ p₁ hr₁Q hr₂Q hp₁K
      R' hR'from hR'disj hR'bdry hR'even hR'len
  · rintro x ⟨hxK, hxR⟩
    show x ∈ res.K'
    rw [res.hK']
    refine Or.inl ⟨hxK, ?_⟩
    intro hcon
    exact hxR (by rw [← hQset]; exact hcon)
  · rintro x ⟨hxrung, hxK⟩
    have hx' : x ∈ R' := by
      have hx0 : x ∈ rungSet G res.H' res.K' res.φ' res.q' := hxrung
      rw [res.hrung'] at hx0
      exact hx0
    show x ∈ {y : V | y ∈ R}
    rw [← hQset]
    exact hR'disj x hx' hxK
  · show p₁ ∈ rungSet G res.H' res.K' res.φ' res.q'
    rw [res.hrung']
    exact hp₁R'

end Workspace.ProofLemmas.Thm75Claim2Five82CaseOne
