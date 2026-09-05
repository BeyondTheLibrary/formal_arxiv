import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary
import Workspace.ProofLemmas.Thm75Claim2Five82Splice
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps
import Workspace.ProofLemmas.RungReplacementLabelled
import Workspace.ProofLemmas.RungReplacementRungLength

/-!
# 5.8.2 when the replaced branch is not the distinguished branch

PAPER (proof of 7.5, claim (2), printed p. 37): *"Now suppose that `b₁b₂` and `c₁c₂` are
different edges of `J`.  Then `Bc₁c₂` is still a branch of `H′`, and we claim that every
`y ∈ Y` is `Bc₁c₂`-dominant with respect to `L(H′)` … Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that
`Rb₁b₂` is incident with at most one of `c₁, c₂`, so these two prisms are related as in 7.4."*

The replacement is performed on the branch `Bb₁b₂`, in whichever of the four cases of 5.8 (2)
applies, and the distinguished branch survives with the same rung.  Its two endpoint cliques are
unchanged unless the replaced branch is incident with one of `c₁, c₂`, and it cannot be incident
with both: two branches with the same pair of ends are the same branch.  When one of them does
change, it loses one rung end and gains one end of the replacement path, which lies outside the
old appearance, so the change is a `SingleCliqueSwap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82OtherBranch

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance
open Workspace.ProofLemmas.Thm75Claim2Five82Splice
open Workspace.ProofLemmas.RungReplacementLabelled

/-- **A branch is determined, as an unordered pair of ends, by its edge set.**

An end of a branch is a branch-vertex, while no internal vertex of a branch is one.  So an end
of one branch that lies on another branch with the same edges must be an end of that one too. -/
theorem sym2_ends_eq_of_trackEdges_eq {W : Type*} {H : SimpleGraph W}
    {q q' : List W} {d₁ d₂ d₁' d₂' : W}
    (hq : IsBranch H q) (hqe : IsTrackFrom H q d₁ d₂) (hq2 : 2 ≤ q.length)
    (hqe' : IsTrackFrom H q' d₁' d₂') (hq2' : 2 ≤ q'.length)
    (hd₁' : d₁' ∈ branchVertices H) (hd₂' : d₂' ∈ branchVertices H)
    (heq : trackEdges q = trackEdges q') :
    s(d₁, d₂) = s(d₁', d₂') := by
  have hq0 : q[0]'(by omega) = d₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hqe (by omega)
  have hqL : q[q.length - 1]'(by omega) = d₂ :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hqe (by omega)
  have hq'0 : q'[0]'(by omega) = d₁' :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hqe' (by omega)
  have hq'L : q'[q'.length - 1]'(by omega) = d₂' :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hqe' (by omega)
  have hmem : ∀ d : W, (d = d₁' ∨ d = d₂') → d ∈ q := by
    intro d hd
    have hedge : ∃ e ∈ trackEdges q', d ∈ e := by
      rcases hd with rfl | rfl
      · exact ⟨s(q'[0]'(by omega), q'[0 + 1]'(by omega)), ⟨0, by omega, rfl⟩,
          by rw [show q'[0]'(by omega) = d from hq'0]; exact Sym2.mem_mk_left _ _⟩
      · refine ⟨s(q'[q'.length - 2]'(by omega), q'[q'.length - 2 + 1]'(by omega)),
          ⟨q'.length - 2, by omega, rfl⟩, ?_⟩
        have hidx : q'[q'.length - 2 + 1]'(by omega) = q'[q'.length - 1]'(by omega) :=
          Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q' (by omega)
            (by omega) (by omega)
        rw [hidx, hq'L]
        exact Sym2.mem_mk_right _ _
    obtain ⟨e, he, hde⟩ := hedge
    rw [← heq] at he
    obtain ⟨i, hi, rfl⟩ := he
    rcases Sym2.mem_iff.mp hde with rfl | rfl
    · exact List.getElem_mem _
    · exact List.getElem_mem _
  have hends : ∀ d : W, (d = d₁' ∨ d = d₂') → d ∈ branchVertices H → d = d₁ ∨ d = d₂ := by
    intro d hd hdb
    have hnot : d ∉ trackInterior q := fun hc => hq.2.1 d hc hdb
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
      (hmem d hd) hnot (by omega) with h | h
    · exact Or.inl (by rw [h, hq0])
    · exact Or.inr (by rw [h, hqL])
  have hne' : d₁' ≠ d₂' := by
    intro hcon
    rw [← hq'0, ← hq'L] at hcon
    have := (List.Nodup.getElem_inj_iff hqe'.1.2.1).mp hcon
    omega
  rcases hends d₁' (Or.inl rfl) hd₁' with h₁ | h₁ <;>
    rcases hends d₂' (Or.inr rfl) hd₂' with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne'
  · rw [h₁, h₂]
  · rw [h₁, h₂]; exact Sym2.eq_swap
  · exact absurd (h₁.trans h₂.symm) hne'

/-- **The outcome of the replacement when the replaced branch is not the distinguished one.**

The distinguished branch survives with the same rung, at most one of its two endpoint cliques
changes, and the new appearance contains the first vertex `p₁` of the connected set's path. -/
theorem other_branch_outcome {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List (Fin m)) (c₁ c₂ : Fin m) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (q : List (Fin m)) (b₁ b₂ : Fin m)
    (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hendsne : s(b₁, b₂) ≠ s(c₁, c₂))
    (R : List V) (hR : IsPathList G R) (hRs : {x : V | x ∈ R} = rungSet G H K φ q)
    (r₁ r₂ : V)
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (hcases :
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂}) ∨
          (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
        (Even (pathLength P) ↔ Even (pathLength R))) ∨
      (p₁ = p₂ ∧
        (∀ x ∈ (NSet G H K φ b₁ ∪ NSet G H K φ b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
        (∀ y ∈ K, G.Adj p₁ y →
          y ∈ NSet G H K φ b₁ ∪ NSet G H K φ b₂ ∪ {z : V | z ∈ R}) ∧
        Even (pathLength R)) ∨
      (r₁ = r₂ ∧ (∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})) ∧
        Even (pathLength P))) :
    ∃ a : BranchAppearance G J,
      (a.leftClique ∪ a.rightClique) ∩ K ⊆ NSet G H K φ c₁ ∪ NSet G H K φ c₂ ∧
      OneCliqueReplacement G (NSet G H K φ c₁) (NSet G H K φ c₂) a.leftClique a.rightClique ∧
      a.rung = rungSet G H K φ B ∧ rungSet G H K φ B ⊆ a.K ∧ p₁ ∈ a.K := by
  classical
  have hp₁P : p₁ ∈ P := (isPathFrom_ends_mem hP).1
  have hp₂P : p₂ ∈ P := (isPathFrom_ends_mem hP).2
  have hp₁K : p₁ ∉ K := hPK p₁ hp₁P
  have hp₂K : p₂ ∉ K := hPK p₂ hp₂P
  have hr₁mem : r₁ ∈ NSet G H K φ b₁ ∩ {x : V | x ∈ R} := by rw [hr₁]; rfl
  have hr₂mem : r₂ ∈ NSet G H K φ b₂ ∩ {x : V | x ∈ R} := by rw [hr₂]; rfl
  have hqlen2 : 2 ≤ q.length := by
    have hmem : r₁ ∈ rungSet G H K φ q := hRs ▸ hr₁mem.2
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := hmem
    omega
  have hBlen2 : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
  obtain ⟨hcne, hc₁b, hc₂b, -⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂
      hbranch hfrom (by omega)
  have hdiff : trackEdges q ≠ trackEdges B := fun hc =>
    hendsne (sym2_ends_eq_of_trackEdges_eq hq hqf hqlen2 hfrom hBlen2 hc₁b hc₂b hc)
  -- the canonical oriented rung of the replaced branch
  set Q : List V := trackRung φ q hq.1 with hQdef
  have hQset : {x : V | x ∈ Q} = {x : V | x ∈ R} := by
    rw [hRs]; ext x; exact mem_trackRung_iff φ hq.1
  have hQrung : {x : V | x ∈ Q} = rungSet G H K φ q := by rw [hQset, hRs]
  have hQK : ∀ x ∈ Q, x ∈ K := trackRung_subset_K φ q hq.1
  have hr₁Q : NSet G H K φ b₁ ∩ {x : V | x ∈ Q} = {r₁} := by rw [hQset]; exact hr₁
  have hr₂Q : NSet G H K φ b₂ ∩ {x : V | x ∈ Q} = {r₂} := by rw [hQset]; exact hr₂
  have hfirst : firstRungVertex φ q hq.1 hqlen2 = r₁ := by
    have hmem : firstRungVertex φ q hq.1 hqlen2 ∈ NSet G H K φ b₁ ∩ {x : V | x ∈ Q} :=
      ⟨by
        refine ⟨firstTrackEdge q hqlen2, firstTrackEdge_mem hq.1 hqlen2, ?_, rfl⟩
        exact ⟨firstTrackEdge_mem hq.1 hqlen2, firstTrackEdge_contains hqf hqlen2⟩,
        firstRungVertex_mem φ hq.1 hqlen2⟩
    rw [hr₁Q] at hmem
    exact hmem
  have hlast : lastRungVertex φ q hq.1 hqlen2 = r₂ := by
    have hmem : lastRungVertex φ q hq.1 hqlen2 ∈ NSet G H K φ b₂ ∩ {x : V | x ∈ Q} :=
      ⟨by
        refine ⟨lastTrackEdge q hqlen2, lastTrackEdge_mem hq.1 hqlen2, ?_, rfl⟩
        exact ⟨lastTrackEdge_mem hq.1 hqlen2, lastTrackEdge_contains hqf hqlen2⟩,
        lastRungVertex_mem φ hq.1 hqlen2⟩
    rw [hr₂Q] at hmem
    exact hmem
  have hQfrom : IsPathFrom G Q r₁ r₂ := by
    have h := trackRung_isPathFrom_ends φ hqf hqlen2
    rwa [hfirst, hlast] at h
  have hbdry : ∀ x ∈ Q, ∀ y ∈ K, y ∉ Q →
      (G.Adj x y ↔ (x = r₁ ∧ y ∈ NSet G H K φ b₁) ∨ (x = r₂ ∧ y ∈ NSet G H K φ b₂)) := by
    intro x hx y hyK hyQ
    have h := Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary.rung_boundary
      φ hq hqf hqlen2 (x := x) (y := y) hx hyK hyQ
    rwa [hfirst, hlast] at h
  have hQlen : pathLength Q = pathLength R := by
    have h := Workspace.ProofLemmas.RungReplacementRungLength.rung_length_eq_trackLength
      φ q hq.1 (by simp only [trackLength]; omega) R hR hRs
    have h2 : Q.length = trackLength q := by rw [hQdef, trackRung_length]
    simp only [pathLength]
    omega
  -- the replacement input, uniformly over the four cases
  obtain ⟨R', s₂, hR'from, hR'disj, hR'bdry, hpar, hp₁R', hs₂⟩ :
      ∃ (R' : List V) (s₂ : V), IsPathFrom G R' p₁ s₂ ∧
        (∀ x ∈ R', x ∈ K → x ∈ Q) ∧
        (∀ x ∈ R', ∀ y ∈ K, y ∉ Q →
          (G.Adj x y ↔ (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
            (x = s₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂}))) ∧
        (Even (pathLength R') ↔ Even (pathLength Q)) ∧
        p₁ ∈ R' ∧ (s₂ ∉ K ∨ s₂ = r₂) := by
    rcases hcases with hc | hc | hc | hc
    · obtain ⟨R', h1, h2, h3, -, h5⟩ :=
        case_one_splice (G := G) K (NSet G H K φ b₁) (NSet G H K φ b₂) Q r₁ r₂
          hQfrom hQK hr₁Q hbdry P p₁ p₂ hP hPK hc.1
          (by
            obtain ⟨x, hx, hadj⟩ := hc.2.1
            exact ⟨x, ⟨by rw [hQset]; exact hx.1, hx.2⟩, hadj⟩)
          (fun x hx y hy hyr hadj => by
            rcases hc.2.2 x hx y hy hyr hadj with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h.1, by rw [hQset]; exact h.2.1, h.2.2⟩)
      refine ⟨R', r₂, h1, h2, h5, ?_, h3, Or.inr rfl⟩
      exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.case_one_parity
        G hG J hJ H K φ happ q b₁ b₂ hb₁ hb₂ hq hqf hqlen2 r₁ r₂ hr₁Q hr₂Q
        R' p₁ r₂ h1 (fun hcon => hp₁K (hcon ▸ hQK r₂ (getLast_mem hQfrom.2.2))) h2 h5
    · obtain ⟨hd, hb⟩ :=
        input_case_two (G := G) K (NSet G H K φ b₁) (NSet G H K φ b₂) Q r₁ r₂ hQfrom
          P p₁ p₂ hPK hc.1 hc.2.1 hc.2.2.1
      refine ⟨P, p₂, hP, hd, hb, ?_, hp₁P, Or.inl hp₂K⟩
      rw [hQlen]; exact hc.2.2.2
    · have hP' : IsPathFrom G P p₁ p₁ := by
        have h := hP; rw [← hc.1] at h; exact h
      obtain ⟨hPeq, hd, hb⟩ :=
        input_case_three (G := G) K (NSet G H K φ b₁) (NSet G H K φ b₂) Q r₁ r₂ hQfrom
          P p₁ hP' hPK hc.2.1
          (fun y hy hadj => by
            have h := hc.2.2.1 y hy hadj
            rw [← hQset] at h
            exact h)
      refine ⟨P, p₁, hP', hd, hb, ?_, hp₁P, Or.inl hp₁K⟩
      have hQeven : Even (pathLength Q) := by rw [hQlen]; exact hc.2.2.2
      have hPeven : Even (pathLength P) := by rw [hPeq]; exact ⟨0, rfl⟩
      exact iff_of_true hPeven hQeven
    · obtain ⟨hQeven, hd, hb⟩ :=
        input_case_four (G := G) K (NSet G H K φ b₁) (NSet G H K φ b₂) Q r₁ r₂ hQfrom hc.1
          P p₁ p₂ hPK hc.2.1 hc.2.2.1 hc.2.2.2.1
      exact ⟨P, p₂, hP, hd, hb, iff_of_true hc.2.2.2.2 hQeven, hp₁P, Or.inl hp₂K⟩
  -- the replacement
  obtain ⟨res⟩ := Workspace.ProofLemmas.RungReplacementLabelled.rungReplacement
    G J hJ H K φ happ q b₁ b₂ hb₁ hb₂ hq hqf Q hQfrom.1 hQrung r₁ r₂ hr₁Q hr₂Q
    R' p₁ s₂ hR'from hR'disj hR'bdry hpar
  obtain ⟨hBb, hBf, hBr⟩ := res.hbranches B c₁ c₂ hbranch hfrom (fun hc => hdiff hc.symm)
  have hlenmap : trackLength (B.map res.ι) = trackLength B := by
    simp only [trackLength, List.length_map]
  have hL1 : NSet G res.H' res.K' res.φ' (res.ι b₁) = (NSet G H K φ b₁ \ {r₁}) ∪ {p₁} :=
    res.hleft
  have hL2 : NSet G res.H' res.K' res.φ' (res.ι b₂) = (NSet G H K φ b₂ \ {r₂}) ∪ {s₂} :=
    res.hright
  -- every new clique meets `K` inside the corresponding old clique
  have hc₁int : c₁ ∉ trackInterior q := fun hc => hq.2.1 c₁ hc hc₁b
  have hc₂int : c₂ ∉ trackInterior q := fun hc => hq.2.1 c₂ hc hc₂b
  have hclq : ∀ c : Fin m, c ∉ trackInterior q →
      NSet G res.H' res.K' res.φ' (res.ι c) ∩ K ⊆ NSet G H K φ c := by
    intro c hcint x hx
    by_cases h1 : c = b₁
    · subst h1
      rw [hL1] at hx
      rcases hx.1 with h | h
      · exact h.1
      · exact absurd hx.2 ((show x = p₁ from h) ▸ hp₁K)
    · by_cases h2 : c = b₂
      · subst h2
        rw [hL2] at hx
        rcases hx.1 with h | h
        · exact h.1
        · have hxs : x = s₂ := h
          rcases hs₂ with hout | heq
          · exact absurd hx.2 (hxs ▸ hout)
          · rw [hxs, heq]; exact hr₂mem.1
      · rw [res.hother c hcint h1 h2] at hx; exact hx.1
  -- the reversed distinguished branch, for the two cases where `c₂` is the shared end
  have hbranchR : IsBranch H B.reverse :=
    Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse hbranch
  have hfromR : IsTrackFrom H B.reverse c₂ c₁ :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom
  have hlenR : trackLength B.reverse = trackLength B := by
    simp only [trackLength, List.length_reverse]
  have hdiffR : trackEdges q ≠ trackEdges B.reverse := by
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]; exact hdiff
  refine ⟨{ m := res.m
            H := res.H'
            K := res.K'
            φ := res.φ'
            happ := res.happ
            B := B.map res.ι
            c₁ := res.ι c₁
            c₂ := res.ι c₂
            hbranch := hBb
            hfrom := hBf
            hodd := by rw [hlenmap]; exact hodd
            hlen := by rw [hlenmap]; exact hlen }, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hxK⟩
    rcases hx with hx | hx
    · exact Or.inl (hclq c₁ hc₁int ⟨hx, hxK⟩)
    · exact Or.inr (hclq c₂ hc₂int ⟨hx, hxK⟩)
  · show OneCliqueReplacement G (NSet G H K φ c₁) (NSet G H K φ c₂)
      (NSet G res.H' res.K' res.φ' (res.ι c₁)) (NSet G res.H' res.K' res.φ' (res.ι c₂))
    have hnb : ¬ (c₁ = b₁ ∧ c₂ = b₂) := fun h => hendsne (by rw [h.1, h.2])
    have hnb' : ¬ (c₁ = b₂ ∧ c₂ = b₁) := fun h => hendsne (by rw [h.1, h.2]; exact Sym2.eq_swap)
    by_cases h11 : c₁ = b₁
    · have h21 : c₂ ≠ b₁ := fun hc => hcne (h11.trans hc.symm)
      have h22 : c₂ ≠ b₂ := fun hc => hnb ⟨h11, hc⟩
      refine Or.inr (Or.inl ⟨res.hother c₂ hc₂int h21 h22, ?_⟩)
      rw [show NSet G res.H' res.K' res.φ' (res.ι c₁) = (NSet G H K φ c₁ \ {r₁}) ∪ {p₁} by
        rw [h11]; exact hL1]
      exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.shared_end_single_clique_swap
        G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen q b₁ b₂ hq hqf hdiff
        Q hQfrom.1 hQrung r₁ r₂ p₁ s₂ hr₁Q hr₂Q R' hR'from hR'disj hR'bdry hpar
        r₁ p₁ hp₁K (Or.inl ⟨h11, rfl, rfl⟩)
    · by_cases h12 : c₁ = b₂
      · have h21 : c₂ ≠ b₂ := fun hc => hcne (h12.trans hc.symm)
        have h22 : c₂ ≠ b₁ := fun hc => hnb' ⟨h12, hc⟩
        rcases hs₂ with hout | heq
        · refine Or.inr (Or.inl ⟨res.hother c₂ hc₂int h22 h21, ?_⟩)
          rw [show NSet G res.H' res.K' res.φ' (res.ι c₁) = (NSet G H K φ c₁ \ {r₂}) ∪ {s₂} by
            rw [h12]; exact hL2]
          exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.shared_end_single_clique_swap
            G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen q b₁ b₂ hq hqf hdiff
            Q hQfrom.1 hQrung r₁ r₂ p₁ s₂ hr₁Q hr₂Q R' hR'from hR'disj hR'bdry hpar
            r₂ s₂ hout (Or.inr ⟨h12, rfl, rfl⟩)
        · refine Or.inl ⟨?_, res.hother c₂ hc₂int h22 h21⟩
          rw [show NSet G res.H' res.K' res.φ' (res.ι c₁) = (NSet G H K φ c₁ \ {r₂}) ∪ {s₂} by
            rw [h12]; exact hL2]
          rw [heq]
          ext x
          constructor
          · rintro (h | h)
            · exact h.1
            · rw [show x = r₂ from h, h12]; exact hr₂mem.1
          · intro hx
            by_cases hxr : x = r₂
            · exact Or.inr hxr
            · exact Or.inl ⟨hx, hxr⟩
      · by_cases h21 : c₂ = b₁
        · refine Or.inr (Or.inr ⟨res.hother c₁ hc₁int h11 h12, ?_⟩)
          rw [show NSet G res.H' res.K' res.φ' (res.ι c₂) = (NSet G H K φ c₂ \ {r₁}) ∪ {p₁} by
            rw [h21]; exact hL1]
          exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.shared_end_single_clique_swap
            G hG J hJ H K φ happ B.reverse c₂ c₁ hbranchR hfromR (by rw [hlenR]; exact hodd)
            (by rw [hlenR]; exact hlen) q b₁ b₂ hq hqf hdiffR
            Q hQfrom.1 hQrung r₁ r₂ p₁ s₂ hr₁Q hr₂Q R' hR'from hR'disj hR'bdry hpar
            r₁ p₁ hp₁K (Or.inl ⟨h21, rfl, rfl⟩)
        · by_cases h22 : c₂ = b₂
          · rcases hs₂ with hout | heq
            · refine Or.inr (Or.inr ⟨res.hother c₁ hc₁int h11 h12, ?_⟩)
              rw [show NSet G res.H' res.K' res.φ' (res.ι c₂) = (NSet G H K φ c₂ \ {r₂}) ∪ {s₂} by
                rw [h22]; exact hL2]
              exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps.shared_end_single_clique_swap
                G hG J hJ H K φ happ B.reverse c₂ c₁ hbranchR hfromR (by rw [hlenR]; exact hodd)
                (by rw [hlenR]; exact hlen) q b₁ b₂ hq hqf hdiffR
                Q hQfrom.1 hQrung r₁ r₂ p₁ s₂ hr₁Q hr₂Q R' hR'from hR'disj hR'bdry hpar
                r₂ s₂ hout (Or.inr ⟨h22, rfl, rfl⟩)
            · refine Or.inl ⟨res.hother c₁ hc₁int h11 h12, ?_⟩
              rw [show NSet G res.H' res.K' res.φ' (res.ι c₂) = (NSet G H K φ c₂ \ {r₂}) ∪ {s₂} by
                rw [h22]; exact hL2]
              rw [heq]
              ext x
              constructor
              · rintro (h | h)
                · exact h.1
                · rw [show x = r₂ from h, h22]; exact hr₂mem.1
              · intro hx
                by_cases hxr : x = r₂
                · exact Or.inr hxr
                · exact Or.inl ⟨hx, hxr⟩
          · exact Or.inl ⟨res.hother c₁ hc₁int h11 h12, res.hother c₂ hc₂int h21 h22⟩
  · show rungSet G res.H' res.K' res.φ' (B.map res.ι) = rungSet G H K φ B
    exact hBr
  · rw [← hBr]
    rintro x ⟨e, he, -, rfl⟩
    exact (res.φ' ⟨e, he⟩).property
  · show p₁ ∈ res.K'
    rw [res.hK']
    exact Or.inr hp₁R'

end Workspace.ProofLemmas.Thm75Claim2Five82OtherBranch
