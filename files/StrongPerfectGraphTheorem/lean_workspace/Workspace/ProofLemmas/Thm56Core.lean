import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm56Basics

/-!
# 5.6 — the path argument

This follows the proof on printed pp. 21–22.  The endpoint sets below are the paper's
`X₁,Y₁,X₂,Y₂`.  We first build its track `P`.  If `P` does not already give one of the
two outcomes, we build the minimal endpoint-clean track `Q` and join the needed slice of `P`
to `Q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm56Core

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm56Basics

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem mem_endpoint_union_of_adj {H : SimpleGraph W} {c z : W}
    {A B : Set (Sym2 W)} (hpart : A ∪ B = incidentEdges H c) (hcz : H.Adj c z) :
    z ∈ endsAt c A ∪ endsAt c B := by
  have hi : s(c, z) ∈ incidentEdges H c := ⟨by
    rw [SimpleGraph.mem_edgeSet]
    exact hcz, by simp⟩
  have hu : s(c, z) ∈ A ∪ B := by rw [hpart]; exact hi
  exact hu

private theorem center_not_mem_endpoint_clean_track {H : SimpleGraph W} {c p q : W}
    {A B : Set (Sym2 W)} {P : List W}
    (hpart : A ∪ B = incidentEdges H c) (hP : IsTrackFrom H P p q)
    (hpc : p ≠ c) (hqc : q ≠ c)
    (hclean : ∀ z ∈ P, z ∈ endsAt c A ∪ endsAt c B → z = q) : c ∉ P := by
  intro hcP
  obtain ⟨i, hi, hic⟩ := List.mem_iff_getElem.mp hcP
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  have hi0 : i ≠ 0 := by
    intro h
    have hp0 := Workspace.ProofLemmas.Thm61Claim1Helpers.head_getElem hP.2.1 hpos
    exact hpc (hp0.symm.trans (by simpa [h] using hic))
  have hilast : i ≠ P.length - 1 := by
    intro h
    have hlast := Workspace.ProofLemmas.Thm61Claim1Helpers.last_getElem hP.2.2 hpos
    exact hqc (hlast.symm.trans (by simpa [h] using hic))
  have hprev := hP.1.2.2 (i - 1) (by omega)
  have hnext := hP.1.2.2 i (by omega)
  have hprevAdj : H.Adj c (P[i - 1]'(by omega)) := by
    have heq : P[i]'(by omega) = c := by simpa using hic
    have hstep : P[i - 1 + 1]'(by omega) = P[i]'(by omega) :=
      Workspace.ProofLemmas.Thm61Claim1Helpers.geq P (by omega) _ _
    rw [hstep, heq] at hprev
    exact hprev.symm
  have hnextAdj : H.Adj c (P[i + 1]'(by omega)) := by
    have heq : P[i]'(by omega) = c := by simpa using hic
    rw [heq] at hnext
    exact hnext
  have hprevEnd := mem_endpoint_union_of_adj hpart hprevAdj
  have hnextEnd := mem_endpoint_union_of_adj hpart hnextAdj
  have hpq := hclean _ (List.getElem_mem _) hprevEnd
  have hnq := hclean _ (List.getElem_mem _) hnextEnd
  have heq : P[i - 1]'(by omega) = P[i + 1]'(by omega) := hpq.trans hnq.symm
  have hidx := hP.1.2.1.getElem_inj_iff.mp heq
  omega

private theorem endpoint_union_not_subsingleton {H : SimpleGraph W} {c₁ c₂ : W}
    {A₁ B₁ A₂ B₂ : Set (Sym2 W)}
    (hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁)
    (hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂)
    (hA₁ : A₁.Nonempty)
    (hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e) :
    ¬ (endsAt c₁ A₁ ∪ endsAt c₂ A₂).Subsingleton := by
  intro hsub
  obtain ⟨x, hx⟩ := endpoints_nonempty hpart₁ hA₁
  apply hnocover
  refine ⟨x, ?_⟩
  intro e he
  rcases he with he | he
  · obtain ⟨z, hz, rfl⟩ := exists_endpoint_of_mem hpart₁ he
    have hzx := hsub (Or.inl hz) (Or.inl hx)
    simp [hzx]
  · obtain ⟨z, hz, rfl⟩ := exists_endpoint_of_mem hpart₂ he
    have hzx := hsub (Or.inr hz) (Or.inl hx)
    simp [hzx]

private theorem choose_left_not_cover_right {X₁ X₂ : Set W}
    (hX₁ : X₁.Nonempty) (hX₂ : X₂.Nonempty) (
      hlarge : ¬ (X₁ ∪ X₂).Subsingleton) :
    ∃ x ∈ X₁, ¬ X₂ ⊆ {x} := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hX₁
  obtain ⟨b, hb⟩ := hX₂
  have hba : b = a := Set.mem_singleton_iff.mp (h a ha hb)
  apply hlarge
  intro x hx y hy
  have hxa : x = a := by
    rcases hx with hx | hx
    · exact (Set.mem_singleton_iff.mp (h x hx hb)).symm.trans hba
    · exact Set.mem_singleton_iff.mp (h a ha hx)
  have hya : y = a := by
    rcases hy with hy | hy
    · exact (Set.mem_singleton_iff.mp (h y hy hb)).symm.trans hba
    · exact Set.mem_singleton_iff.mp (h a ha hy)
  exact hxa.trans hya.symm

private theorem choose_opposite {X₁ X₂ : Set W} {q : W}
    (hX₁ : X₁.Nonempty) (hX₂ : X₂.Nonempty)
    (hlarge : ¬ (X₁ ∪ X₂).Subsingleton) (hq : q ∈ X₁ ∪ X₂) :
    (q ∈ X₁ ∧ ∃ x ∈ X₂, x ≠ q) ∨ (q ∈ X₂ ∧ ∃ x ∈ X₁, x ≠ q) := by
  by_cases hq₁ : q ∈ X₁
  · by_cases hother : ∃ x ∈ X₂, x ≠ q
    · exact Or.inl ⟨hq₁, hother⟩
    · right
      push Not at hother
      obtain ⟨z, hz⟩ := hX₂
      have hzq : z = q := hother z hz
      refine ⟨hzq ▸ hz, ?_⟩
      by_contra hnone
      push Not at hnone
      apply hlarge
      intro a ha b hb
      have haq : a = q := by
        rcases ha with ha | ha
        · exact hnone a ha
        · exact hother a ha
      have hbq : b = q := by
        rcases hb with hb | hb
        · exact hnone b hb
        · exact hother b hb
      exact haq.trans hbq.symm
  · right
    have hq₂ : q ∈ X₂ := hq.resolve_left hq₁
    refine ⟨hq₂, ?_⟩
    obtain ⟨x, hx⟩ := hX₁
    exact ⟨x, hx, fun h => hq₁ (h ▸ hx)⟩

private theorem glue_to_last {H : SimpleGraph W} {P Q : List W} {p last q r : W}
    (hP : IsTrackFrom H P p last) (hQ : IsTrackFrom H Q q r) (hrP : r ∈ P)
    (hcleanQ : ∀ z ∈ Q, z ∈ P → z = r) :
    ∃ R : List W, IsTrackFrom H R q last ∧ ∀ z ∈ R, z ∈ Q ∨ z ∈ P := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hrP
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  let S := Workspace.ProofLemmas.TrackSlice.slice P i (P.length - 1)
  have hS : IsTrackFrom H S r last := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice hP.1
      (show P.length - 1 < P.length by omega) (show i ≤ P.length - 1 by omega)
    have hlast := Workspace.ProofLemmas.Thm61Claim1Helpers.last_getElem hP.2.2 hpos
    simpa only [S, hir, hlast] using hs
  have hcommon : ∀ z : W, z ∈ Q → z ∈ S → z = r := by
    intro z hzQ hzS
    exact hcleanQ z hzQ (Workspace.ProofLemmas.TrackSlice.mem_of_mem_slice hzS)
  let R := Q ++ S.tail
  have hglue := Workspace.ProofLemmas.TrackGlueAtCommonEndpoint H Q S q r last hQ hS hcommon
  refine ⟨R, hglue.1, ?_⟩
  intro z hz
  rcases hglue.2 z hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (Workspace.ProofLemmas.TrackSlice.mem_of_mem_slice hz)

private theorem glue_from_first {H : SimpleGraph W} {P Q : List W} {first last q r : W}
    (hP : IsTrackFrom H P first last) (hQ : IsTrackFrom H Q q r) (hrP : r ∈ P)
    (hcleanQ : ∀ z ∈ Q, z ∈ P → z = r) :
    ∃ R : List W, IsTrackFrom H R first q ∧ ∀ z ∈ R, z ∈ P ∨ z ∈ Q := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hrP
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  let S := Workspace.ProofLemmas.TrackSlice.slice P 0 i
  have hS : IsTrackFrom H S first r := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice hP.1 hi (Nat.zero_le i)
    have hfirst := Workspace.ProofLemmas.Thm61Claim1Helpers.head_getElem hP.2.1 hpos
    simpa only [S, hfirst, hir] using hs
  have hQr : IsTrackFrom H Q.reverse r q :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hQ
  have hcommon : ∀ z : W, z ∈ S → z ∈ Q.reverse → z = r := by
    intro z hzS hzQ
    apply hcleanQ z
    · simpa using hzQ
    · exact Workspace.ProofLemmas.TrackSlice.mem_of_mem_slice hzS
  let R := S ++ Q.reverse.tail
  have hglue := Workspace.ProofLemmas.TrackGlueAtCommonEndpoint H S Q.reverse first r q
    hS hQr hcommon
  refine ⟨R, hglue.1, ?_⟩
  intro z hz
  rcases hglue.2 z hz with hz | hz
  · exact Or.inl (Workspace.ProofLemmas.TrackSlice.mem_of_mem_slice hz)
  · exact Or.inr (by simpa using hz)

private theorem reverse_suffix {H : SimpleGraph W} {P : List W} {first last r : W}
    (hP : IsTrackFrom H P first last) (hrP : r ∈ P) :
    ∃ R : List W, IsTrackFrom H R last r ∧ ∀ z ∈ R, z ∈ P := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hrP
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  let S := Workspace.ProofLemmas.TrackSlice.slice P i (P.length - 1)
  have hS : IsTrackFrom H S r last := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice hP.1
      (show P.length - 1 < P.length by omega) (show i ≤ P.length - 1 by omega)
    have hlast := Workspace.ProofLemmas.Thm61Claim1Helpers.last_getElem hP.2.2 hpos
    simpa only [S, hir, hlast] using hs
  refine ⟨S.reverse, Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hS, ?_⟩
  intro z hz
  apply Workspace.ProofLemmas.TrackSlice.mem_of_mem_slice (R := P)
  simpa using hz

/-- The path argument of 5.6 when `B₁` is the nonempty `B`-part. -/
theorem core_of_B₁_nonempty (H : SimpleGraph W) (c₁ c₂ : W)
    (hnadj : ¬ H.Adj c₁ c₂)
    (hconn : ConnectedSet H (({c₁, c₂} : Set W)ᶜ))
    (A₁ B₁ A₂ B₂ : Set (Sym2 W))
    (hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁) (hdisj₁ : Disjoint A₁ B₁)
    (hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂) (hdisj₂ : Disjoint A₂ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty)
    (hAconn : ∀ e ∈ A₁ ∪ A₂, ∀ u v : W, e = s(u, v) →
      ConnectedSet H (({u, v} : Set W)ᶜ))
    (hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e) :
    Outcome H c₁ c₂ A₁ B₁ A₂ ∨ Outcome H c₂ c₁ A₂ B₂ A₁ := by
  let X₁ := endsAt c₁ A₁
  let Y₁ := endsAt c₁ B₁
  let X₂ := endsAt c₂ A₂
  let Y₂ := endsAt c₂ B₂
  have hpart₁' : B₁ ∪ A₁ = incidentEdges H c₁ := by rw [Set.union_comm, hpart₁]
  have hpart₂' : B₂ ∪ A₂ = incidentEdges H c₂ := by rw [Set.union_comm, hpart₂]
  have hX₁ : X₁.Nonempty := by simpa [X₁] using endpoints_nonempty hpart₁ hA₁
  have hY₁ : Y₁.Nonempty := by simpa [Y₁] using endpoints_nonempty hpart₁' hB₁
  have hX₂ : X₂.Nonempty := by simpa [X₂] using endpoints_nonempty hpart₂ hA₂
  have hcne : c₁ ≠ c₂ := by
    intro hcc
    apply hnocover
    refine ⟨c₁, ?_⟩
    intro e he
    rcases he with he | he
    · exact (part_subset_incident hpart₁ he).2
    · have := (part_subset_incident hpart₂ he).2
      simpa [hcc] using this
  have hlarge : ¬ (X₁ ∪ X₂).Subsingleton := by
    simpa [X₁, X₂] using
      endpoint_union_not_subsingleton hpart₁ hpart₂ hA₁ hnocover
  obtain ⟨x₁, hx₁, hnotcover⟩ := choose_left_not_cover_right hX₁ hX₂ hlarge
  obtain ⟨x₂zero, hx₂zero, hx₂zeronot⟩ := Set.not_subset.mp hnotcover
  have hx₂zerone : x₂zero ≠ x₁ := by simpa using hx₂zeronot
  let Z₂ : Set W := (X₂ ∪ Y₂) ∩ ({c₁, x₁} : Set W)ᶜ
  have hY₁sub : Y₁ ⊆ ({c₁, x₁} : Set W)ᶜ := by
    intro z hz hzbad
    rcases hzbad with hzc | hzx
    · have hzneq : z ≠ c₁ := by
        apply ne_center_of_mem_endpoints hpart₁'
        simpa [Y₁] using hz
      exact hzneq hzc
    · apply Set.disjoint_left.mp hdisj₁ (show s(c₁, x₁) ∈ A₁ by exact hx₁)
      have hzB : s(c₁, z) ∈ B₁ := hz
      rw [hzx] at hzB
      exact hzB
  have hZ₂ : Z₂.Nonempty := by
    refine ⟨x₂zero, Or.inl hx₂zero, ?_⟩
    intro hbad
    rcases hbad with hc | hx
    · apply hnadj
      have hadj := adj_of_mem_endpoints hpart₂ (show x₂zero ∈ endsAt c₂ A₂ by exact hx₂zero)
      rw [hc] at hadj
      exact hadj.symm
    · exact hx₂zerone hx
  have hZ₂sub : Z₂ ⊆ ({c₁, x₁} : Set W)ᶜ := fun _ hz => hz.2
  have hconnP : ConnectedSet H (({c₁, x₁} : Set W)ᶜ) :=
    hAconn (s(c₁, x₁)) (Or.inl hx₁) c₁ x₁ rfl
  obtain ⟨p₁, hp₁Y, pₙ, hpₙZ, P, hP, hPS, hPcleanY, hPcleanZ⟩ :=
    ConnectedSetHasEndpointCleanTrack H (({c₁, x₁} : Set W)ᶜ) Y₁ Z₂
      hconnP hY₁ hZ₂ hY₁sub hZ₂sub
  have hp₁ne : p₁ ≠ c₂ := by
    intro h
    apply hnadj
    have hadj := adj_of_mem_endpoints hpart₁' (show p₁ ∈ endsAt c₁ B₁ by exact hp₁Y)
    rwa [h] at hadj
  have hpₙne : pₙ ≠ c₂ := by
    intro h
    rcases hpₙZ.1 with hpₙX | hpₙY
    · exact (ne_center_of_mem_endpoints hpart₂
        (show pₙ ∈ endsAt c₂ A₂ by exact hpₙX)) h
    · exact (ne_center_of_mem_endpoints hpart₂'
        (show pₙ ∈ endsAt c₂ B₂ by exact hpₙY)) h
  have hc₂P : c₂ ∉ P := by
    apply center_not_mem_endpoint_clean_track hpart₂ hP hp₁ne hpₙne
    intro z hzP hzEnd
    apply hPcleanZ z hzP
    exact ⟨hzEnd, hPS z hzP⟩
  by_cases hpₙX₂ : pₙ ∈ X₂
  · left
    apply assemble_first_alternative hP
    · intro h; exact hPS c₁ h (Or.inl rfl)
    · exact hc₂P
    · intro h; exact hPS x₁ h (Or.inr rfl)
    · exact hcne
    · exact hnadj
    · exact (adj_of_mem_endpoints hpart₁ (show x₁ ∈ endsAt c₁ A₁ by exact hx₁)).symm
    · exact adj_of_mem_endpoints hpart₁' (show p₁ ∈ endsAt c₁ B₁ by exact hp₁Y)
    · exact (adj_of_mem_endpoints hpart₂
        (show pₙ ∈ endsAt c₂ A₂ by exact hpₙX₂)).symm
    · simpa only [Sym2.eq_swap] using hx₁
    · exact hp₁Y
    · simpa only [Sym2.eq_swap] using hpₙX₂
  have hpₙY₂ : pₙ ∈ Y₂ := hpₙZ.1.resolve_left hpₙX₂
  by_cases hPX₁ : ∃ r ∈ P, r ∈ X₁
  · obtain ⟨r, hrP, hrX₁⟩ := hPX₁
    obtain ⟨x₂, hx₂⟩ := hX₂
    have hx₂P : x₂ ∉ P := by
      intro hxP
      have hxZ : x₂ ∈ Z₂ := ⟨Or.inl hx₂, hPS x₂ hxP⟩
      have heq := hPcleanZ x₂ hxP hxZ
      exact hpₙX₂ (heq ▸ hx₂)
    obtain ⟨R, hR, hRP⟩ := reverse_suffix hP hrP
    right
    apply assemble_first_alternative hR
    · exact fun h => hc₂P (hRP c₂ h)
    · intro h; exact hPS c₁ (hRP c₁ h) (Or.inl rfl)
    · exact fun h => hx₂P (hRP x₂ h)
    · exact hcne.symm
    · exact fun h => hnadj h.symm
    · exact (adj_of_mem_endpoints hpart₂ (show x₂ ∈ endsAt c₂ A₂ by exact hx₂)).symm
    · exact adj_of_mem_endpoints hpart₂' (show pₙ ∈ endsAt c₂ B₂ by exact hpₙY₂)
    · exact (adj_of_mem_endpoints hpart₁ (show r ∈ endsAt c₁ A₁ by exact hrX₁)).symm
    · simpa only [Sym2.eq_swap] using hx₂
    · exact hpₙY₂
    · simpa only [Sym2.eq_swap] using hrX₁
  have hPavoidX : ∀ z ∈ P, z ∉ X₁ ∪ X₂ := by
    intro z hzP hzX
    rcases hzX with hzX₁ | hzX₂
    · exact hPX₁ ⟨z, hzP, hzX₁⟩
    · have hzZ : z ∈ Z₂ := ⟨Or.inl hzX₂, hPS z hzP⟩
      have heq := hPcleanZ z hzP hzZ
      exact hpₙX₂ (heq ▸ hzX₂)
  let VP : Set W := {z | z ∈ P}
  have hVP : VP.Nonempty := by
    exact ⟨p₁, List.mem_of_head? hP.2.1⟩
  have hXsub : X₁ ∪ X₂ ⊆ ({c₁, c₂} : Set W)ᶜ := by
    intro z hz hzbad
    rcases hz with hzX₁ | hzX₂
    · rcases hzbad with hzc₁ | hzc₂
      · exact (ne_center_of_mem_endpoints hpart₁
          (show z ∈ endsAt c₁ A₁ by exact hzX₁)) hzc₁
      · apply hnadj
        have hadj := adj_of_mem_endpoints hpart₁
          (show z ∈ endsAt c₁ A₁ by exact hzX₁)
        rwa [hzc₂] at hadj
    · rcases hzbad with hzc₁ | hzc₂
      · apply hnadj
        have hadj := adj_of_mem_endpoints hpart₂
          (show z ∈ endsAt c₂ A₂ by exact hzX₂)
        rw [hzc₁] at hadj
        exact hadj.symm
      · exact (ne_center_of_mem_endpoints hpart₂
          (show z ∈ endsAt c₂ A₂ by exact hzX₂)) hzc₂
  have hVPsub : VP ⊆ ({c₁, c₂} : Set W)ᶜ := by
    intro z hz hzbad
    rcases hzbad with hzc₁ | hzc₂
    · exact hPS z hz (Or.inl hzc₁)
    · exact hc₂P (hzc₂ ▸ hz)
  obtain ⟨q, hqX, r, hrP, Q, hQ, hQS, hQcleanX, hQcleanP⟩ :=
    ConnectedSetHasEndpointCleanTrack H (({c₁, c₂} : Set W)ᶜ) (X₁ ∪ X₂) VP
      hconn (hX₁.mono Set.subset_union_left) hVP hXsub hVPsub
  have hQmeet : ∀ z ∈ Q, z ∈ P → z = r := by
    intro z hzQ hzP
    exact hQcleanP z hzQ hzP
  rcases choose_opposite hX₁ hX₂ hlarge hqX with
      ⟨hqX₁, x₂, hx₂, hxq⟩ | ⟨hqX₂, x₁', hx₁', hxq⟩
  · obtain ⟨R, hR, hRmem⟩ := glue_to_last hP hQ hrP hQmeet
    have hx₂R : x₂ ∉ R := by
      intro hxR
      rcases hRmem x₂ hxR with hxQ | hxP
      · exact hxq (hQcleanX x₂ hxQ (Or.inr hx₂))
      · exact hPavoidX x₂ hxP (Or.inr hx₂)
    have hc₂R : c₂ ∉ R := by
      intro hcR
      rcases hRmem c₂ hcR with hcQ | hcP
      · exact hQS c₂ hcQ (Or.inr rfl)
      · exact hc₂P hcP
    have hc₁R : c₁ ∉ R := by
      intro hcR
      rcases hRmem c₁ hcR with hcQ | hcP
      · exact hQS c₁ hcQ (Or.inl rfl)
      · exact hPS c₁ hcP (Or.inl rfl)
    right
    have hRrev := Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hR
    apply assemble_first_alternative hRrev
    · simpa using hc₂R
    · simpa using hc₁R
    · simpa using hx₂R
    · exact hcne.symm
    · exact fun h => hnadj h.symm
    · exact (adj_of_mem_endpoints hpart₂ (show x₂ ∈ endsAt c₂ A₂ by exact hx₂)).symm
    · exact adj_of_mem_endpoints hpart₂' (show pₙ ∈ endsAt c₂ B₂ by exact hpₙY₂)
    · exact (adj_of_mem_endpoints hpart₁ (show q ∈ endsAt c₁ A₁ by exact hqX₁)).symm
    · simpa only [Sym2.eq_swap] using hx₂
    · exact hpₙY₂
    · simpa only [Sym2.eq_swap] using hqX₁
  · obtain ⟨R, hR, hRmem⟩ := glue_from_first hP hQ hrP hQmeet
    have hx₁R : x₁' ∉ R := by
      intro hxR
      rcases hRmem x₁' hxR with hxP | hxQ
      · exact hPavoidX x₁' hxP (Or.inl hx₁')
      · exact hxq (hQcleanX x₁' hxQ (Or.inl hx₁'))
    have hc₁R : c₁ ∉ R := by
      intro hcR
      rcases hRmem c₁ hcR with hcP | hcQ
      · exact hPS c₁ hcP (Or.inl rfl)
      · exact hQS c₁ hcQ (Or.inl rfl)
    have hc₂R : c₂ ∉ R := by
      intro hcR
      rcases hRmem c₂ hcR with hcP | hcQ
      · exact hc₂P hcP
      · exact hQS c₂ hcQ (Or.inr rfl)
    left
    apply assemble_first_alternative hR
    · exact hc₁R
    · exact hc₂R
    · exact hx₁R
    · exact hcne
    · exact hnadj
    · exact (adj_of_mem_endpoints hpart₁
        (show x₁' ∈ endsAt c₁ A₁ by exact hx₁')).symm
    · exact adj_of_mem_endpoints hpart₁' (show p₁ ∈ endsAt c₁ B₁ by exact hp₁Y)
    · exact (adj_of_mem_endpoints hpart₂ (show q ∈ endsAt c₂ A₂ by exact hqX₂)).symm
    · simpa only [Sym2.eq_swap] using hx₁'
    · exact hp₁Y
    · simpa only [Sym2.eq_swap] using hqX₂

/-- The full path argument, using symmetry when `B₂` rather than `B₁` is known to be
nonempty. -/
theorem conclusion (H : SimpleGraph W) (c₁ c₂ : W)
    (hnadj : ¬ H.Adj c₁ c₂)
    (hconn : ConnectedSet H (({c₁, c₂} : Set W)ᶜ))
    (A₁ B₁ A₂ B₂ : Set (Sym2 W))
    (hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁) (hdisj₁ : Disjoint A₁ B₁)
    (hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂) (hdisj₂ : Disjoint A₂ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB : B₁.Nonempty ∨ B₂.Nonempty)
    (hAconn : ∀ e ∈ A₁ ∪ A₂, ∀ u v : W, e = s(u, v) →
      ConnectedSet H (({u, v} : Set W)ᶜ))
    (hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e) :
    Outcome H c₁ c₂ A₁ B₁ A₂ ∨ Outcome H c₂ c₁ A₂ B₂ A₁ := by
  rcases hB with hB₁ | hB₂
  · exact core_of_B₁_nonempty H c₁ c₂ hnadj hconn A₁ B₁ A₂ B₂ hpart₁ hdisj₁
      hpart₂ hdisj₂ hA₁ hA₂ hB₁ hAconn hnocover
  · have hconn' : ConnectedSet H (({c₂, c₁} : Set W)ᶜ) := by
      simpa [Set.pair_comm] using hconn
    have hAconn' : ∀ e ∈ A₂ ∪ A₁, ∀ u v : W, e = s(u, v) →
        ConnectedSet H (({u, v} : Set W)ᶜ) := by
      intro e he u v huv
      exact hAconn e (by simpa [Set.union_comm] using he) u v huv
    have hnocover' : ¬ ∃ w : W, ∀ e ∈ A₂ ∪ A₁, w ∈ e := by
      simpa [Set.union_comm] using hnocover
    rcases core_of_B₁_nonempty H c₂ c₁ (fun h => hnadj h.symm) hconn'
      A₂ B₂ A₁ B₁ hpart₂ hdisj₂ hpart₁ hdisj₁ hA₂ hA₁ hB₂
      hAconn' hnocover' with h | h
    · exact Or.inr h
    · exact Or.inl h

end Workspace.ProofLemmas.Thm56Core
