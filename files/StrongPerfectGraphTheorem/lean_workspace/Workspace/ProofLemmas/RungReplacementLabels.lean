import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.RungReplacementAddTrack

/-!
# Reading the cliques of a graph with one track added

This is Lemma 6/7 of the rung-replacement plan for 7.5 (printed p. 37):

> PAPER: *"For each `v ∈ V(J)` let `N′v` be the clique in `L(H′)` formed by the edges in
> `δ_H′(v)`.  So `N′v = Nv` for all vertices `v` of `J` except for `b₁` and `b₂`.  Let `R′` be
> between `r′₁` and `r′₂`, where `r′ᵢ ∈ N′_{bᵢ}`."*

Everything here is stated for an abstract `IsBranchExtension` together with the two edge-label
equations of `Workspace.ProofLemmas.RungReplacementAddTrack.addTrackLabelled`: an old edge
keeps the vertex of `G` it had, and the `i`-th edge of the new track is labelled by the `i`-th
vertex of the path `P`.

The four conclusions are the arithmetic of the paper's sentence:

* the rung of the new track is exactly `V(P)`;
* the clique at the first end gains `P`'s first vertex, and nothing else;
* the clique at the second end gains `P`'s last vertex, and nothing else;
* every other old clique is unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.RungReplacementLabels

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.RungReplacementAddTrack

variable {V W Z : Type*} {G : SimpleGraph V} {H₀ : SimpleGraph W} {K₀ : Set V}
  {φ₀ : H₀.lineGraph ≃g G.induce K₀} {D : SimpleGraph Z} {rho : W → Z} {q' : List Z}
  {K' : Set V} {psi : D.lineGraph ≃g G.induce K'} {P : List V} {c₁ c₂ : W}

/-- Every edge of the extended graph is either an old edge or an edge of the new track. -/
theorem edge_cases (hext : IsBranchExtension H₀ c₁ c₂ D rho q') {e : Sym2 Z}
    (he : e ∈ D.edgeSet) :
    (∃ (e₀ : Sym2 W), e₀ ∈ H₀.edgeSet ∧ e = Sym2.map rho e₀) ∨
      (∃ i, ∃ hi : i + 1 < q'.length, e = s(q'[i]'(by omega), q'[i + 1]'hi)) := by
  have := hext.edges ▸ he
  rcases this with ⟨e₀, he₀, heq⟩ | ⟨i, hi, heq⟩
  · exact Or.inl ⟨e₀, he₀, heq.symm⟩
  · exact Or.inr ⟨i, hi, heq⟩

/-- An old edge, seen in the extended graph. -/
theorem old_mem_edgeSet (hext : IsBranchExtension H₀ c₁ c₂ D rho q') {e₀ : Sym2 W}
    (he₀ : e₀ ∈ H₀.edgeSet) : Sym2.map rho e₀ ∈ D.edgeSet := by
  rw [hext.edges]
  exact Or.inl ⟨e₀, he₀, rfl⟩

/-- An edge of the new track, seen in the extended graph. -/
theorem new_mem_edgeSet (hext : IsBranchExtension H₀ c₁ c₂ D rho q') (i : ℕ)
    (hi : i + 1 < q'.length) : s(q'[i]'(by omega), q'[i + 1]'hi) ∈ D.edgeSet := by
  rw [hext.edges]
  exact Or.inr ⟨i, hi, rfl⟩

/-- **Where an old vertex can sit on the new track.**  Only the two ends of the new track are
images of old vertices, and each occurs once. -/
theorem index_of_rho (hext : IsBranchExtension H₀ c₁ c₂ D rho q') (c : W) (j : ℕ)
    (hj : j < q'.length) (hjc : q'[j]'hj = rho c) :
    (j = 0 ∧ c = c₁) ∨ (j = q'.length - 1 ∧ c = c₂) := by
  have hlen := hext.length
  have hnd : q'.Nodup := hext.track.1.2.1
  have h0 : q'[0]'(by omega) = rho c₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  have hL : q'[q'.length - 1]'(by omega) = rho c₂ := by
    have h' := hext.track.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact Or.inl ⟨rfl, hext.inj (by rw [← h0, hjc])⟩
  · rcases Nat.lt_or_ge j (q'.length - 1) with hlt | hge
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hint : q'[k + 1]'hj ∈ trackInterior q' :=
        Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q' k (by omega)
      exact hext.newInterior _ (hjc ▸ hint) ⟨c, rfl⟩
    · have hjeq : j = q'.length - 1 := by omega
      subst hjeq
      exact Or.inr ⟨rfl, hext.inj (by rw [← hL, hjc])⟩

/-- **The rung of the new track is the vertex set of `P`.** -/
theorem rung_new (hext : IsBranchExtension H₀ c₁ c₂ D rho q')
    (hqlen : q'.length = P.length + 1)
    (hnew : ∀ (i : ℕ) (hi : i + 1 < q'.length) (hiP : i < P.length)
      (he : s(q'[i]'(by omega), q'[i + 1]'hi) ∈ D.edgeSet),
      (↑(psi ⟨s(q'[i]'(by omega), q'[i + 1]'hi), he⟩) : V) = P[i]'hiP) :
    {x : V | ∃ (e : Sym2 Z) (he : e ∈ D.edgeSet), e ∈ trackEdges q' ∧
        x = (↑(psi ⟨e, he⟩) : V)} = {x : V | x ∈ P} := by
  ext x
  constructor
  · rintro ⟨e, he, ⟨i, hi, rfl⟩, rfl⟩
    have hiP : i < P.length := by omega
    rw [hnew i hi hiP he]
    exact List.getElem_mem _
  · intro hx
    obtain ⟨i, hiP, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi : i + 1 < q'.length := by omega
    refine ⟨s(q'[i]'(by omega), q'[i + 1]'hi), new_mem_edgeSet hext i hi, ⟨i, hi, rfl⟩, ?_⟩
    exact (hnew i hi hiP _).symm

/-- **The rung of an old track is unchanged.** -/
theorem rung_old (hext : IsBranchExtension H₀ c₁ c₂ D rho q')
    (hold : ∀ (e : Sym2 W) (he : e ∈ H₀.edgeSet) (he' : Sym2.map rho e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map rho e, he'⟩) : V) = (↑(φ₀ ⟨e, he⟩) : V))
    (p : List W) (hp : ∀ (i : ℕ) (hi : i + 1 < p.length),
      s(p[i]'(by omega), p[i + 1]'hi) ∈ H₀.edgeSet) :
    {x : V | ∃ (e : Sym2 Z) (he : e ∈ D.edgeSet), e ∈ trackEdges (p.map rho) ∧
        x = (↑(psi ⟨e, he⟩) : V)}
      = {x : V | ∃ (e : Sym2 W) (he : e ∈ H₀.edgeSet), e ∈ trackEdges p ∧
        x = (↑(φ₀ ⟨e, he⟩) : V)} := by
  ext x
  constructor
  · rintro ⟨e, he, hem, rfl⟩
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at hem
    obtain ⟨e₀, he₀m, rfl⟩ := hem
    obtain ⟨i, hi, rfl⟩ := he₀m
    exact ⟨_, hp i hi, ⟨i, hi, rfl⟩, (hold _ (hp i hi) he).symm ▸ rfl⟩
  · rintro ⟨e₀, he₀, hem, rfl⟩
    refine ⟨Sym2.map rho e₀, old_mem_edgeSet hext he₀, ?_, (hold e₀ he₀ _).symm⟩
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
    exact ⟨e₀, hem, rfl⟩

/-! ### The three clique equations -/

/-- **The clique at a vertex other than the two ends is unchanged.** -/
theorem nset_other (hext : IsBranchExtension H₀ c₁ c₂ D rho q')
    (hold : ∀ (e : Sym2 W) (he : e ∈ H₀.edgeSet) (he' : Sym2.map rho e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map rho e, he'⟩) : V) = (↑(φ₀ ⟨e, he⟩) : V))
    (c : W) (hc₁ : c ≠ c₁) (hc₂ : c ≠ c₂) :
    NSet G D K' psi (rho c) = NSet G H₀ K₀ φ₀ c := by
  ext x
  constructor
  · rintro ⟨e, he, ⟨-, hce⟩, rfl⟩
    rcases edge_cases hext he with ⟨e₀, he₀, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨w, hw, hwe⟩ := Sym2.mem_map.mp hce
      have : w = c := hext.inj hwe
      subst this
      exact ⟨e₀, he₀, ⟨he₀, hw⟩, hold e₀ he₀ he⟩
    · exfalso
      have hlen := hext.length
      rcases Sym2.mem_iff.mp hce with h | h
      · rcases index_of_rho hext c i (by omega) h.symm with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hc₁ rfl
        · exact hc₂ rfl
      · rcases index_of_rho hext c (i + 1) hi h.symm with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hc₁ rfl
        · exact hc₂ rfl
  · rintro ⟨e₀, he₀, ⟨-, hce⟩, rfl⟩
    exact ⟨Sym2.map rho e₀, old_mem_edgeSet hext he₀,
      ⟨old_mem_edgeSet hext he₀, Sym2.mem_map.mpr ⟨c, hce, rfl⟩⟩, (hold e₀ he₀ _).symm⟩

/-- **The clique at the first end gains the first vertex of `P`, and nothing else.** -/
theorem nset_left (hext : IsBranchExtension H₀ c₁ c₂ D rho q')
    (hqlen : q'.length = P.length + 1) (hPlen : 0 < P.length)
    (hold : ∀ (e : Sym2 W) (he : e ∈ H₀.edgeSet) (he' : Sym2.map rho e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map rho e, he'⟩) : V) = (↑(φ₀ ⟨e, he⟩) : V))
    (hnew : ∀ (i : ℕ) (hi : i + 1 < q'.length) (hiP : i < P.length)
      (he : s(q'[i]'(by omega), q'[i + 1]'hi) ∈ D.edgeSet),
      (↑(psi ⟨s(q'[i]'(by omega), q'[i + 1]'hi), he⟩) : V) = P[i]'hiP) :
    NSet G D K' psi (rho c₁) = NSet G H₀ K₀ φ₀ c₁ ∪ {P[0]'hPlen} := by
  have hlen := hext.length
  have hnd : q'.Nodup := hext.track.1.2.1
  have h0 : q'[0]'(by omega) = rho c₁ :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hext.track (by omega)
  ext x
  constructor
  · rintro ⟨e, he, ⟨-, hce⟩, rfl⟩
    rcases edge_cases hext he with ⟨e₀, he₀, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨w, hw, hwe⟩ := Sym2.mem_map.mp hce
      have : w = c₁ := hext.inj hwe
      subst this
      exact Or.inl ⟨e₀, he₀, ⟨he₀, hw⟩, hold e₀ he₀ he⟩
    · refine Or.inr ?_
      have hi0 : i = 0 := by
        rcases Sym2.mem_iff.mp hce with h | h
        · rcases index_of_rho hext c₁ i (by omega) h.symm with ⟨h', -⟩ | ⟨h', -⟩
          · exact h'
          · exfalso
            have : q'[i]'(by omega) = q'[0]'(by omega) := h.symm.trans h0.symm
            have := hnd.getElem_inj_iff.mp this
            omega
        · exfalso
          rcases index_of_rho hext c₁ (i + 1) hi h.symm with ⟨h', -⟩ | ⟨h', -⟩
          · omega
          · have : q'[i + 1]'hi = q'[0]'(by omega) := h.symm.trans h0.symm
            have := hnd.getElem_inj_iff.mp this
            omega
      subst hi0
      rw [hnew 0 hi hPlen he]
      rfl
  · rintro (⟨e₀, he₀, ⟨-, hce⟩, rfl⟩ | hx)
    · exact ⟨Sym2.map rho e₀, old_mem_edgeSet hext he₀,
        ⟨old_mem_edgeSet hext he₀, Sym2.mem_map.mpr ⟨c₁, hce, rfl⟩⟩, (hold e₀ he₀ _).symm⟩
    · have hi : 0 + 1 < q'.length := by omega
      refine ⟨s(q'[0]'(by omega), q'[0 + 1]'hi), new_mem_edgeSet hext 0 hi,
        ⟨new_mem_edgeSet hext 0 hi, ?_⟩, ?_⟩
      · rw [← h0]; simp
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, hnew 0 hi hPlen _]

/-- **The clique at the second end gains the last vertex of `P`, and nothing else.** -/
theorem nset_right (hext : IsBranchExtension H₀ c₁ c₂ D rho q')
    (hqlen : q'.length = P.length + 1) (hPlen : 0 < P.length)
    (hold : ∀ (e : Sym2 W) (he : e ∈ H₀.edgeSet) (he' : Sym2.map rho e ∈ D.edgeSet),
      (↑(psi ⟨Sym2.map rho e, he'⟩) : V) = (↑(φ₀ ⟨e, he⟩) : V))
    (hnew : ∀ (i : ℕ) (hi : i + 1 < q'.length) (hiP : i < P.length)
      (he : s(q'[i]'(by omega), q'[i + 1]'hi) ∈ D.edgeSet),
      (↑(psi ⟨s(q'[i]'(by omega), q'[i + 1]'hi), he⟩) : V) = P[i]'hiP) :
    NSet G D K' psi (rho c₂) = NSet G H₀ K₀ φ₀ c₂ ∪ {P[P.length - 1]'(by omega)} := by
  have hlen := hext.length
  have hnd : q'.Nodup := hext.track.1.2.1
  have hL : q'[q'.length - 1]'(by omega) = rho c₂ := by
    have h' := hext.track.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  ext x
  constructor
  · rintro ⟨e, he, ⟨-, hce⟩, rfl⟩
    rcases edge_cases hext he with ⟨e₀, he₀, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨w, hw, hwe⟩ := Sym2.mem_map.mp hce
      have : w = c₂ := hext.inj hwe
      subst this
      exact Or.inl ⟨e₀, he₀, ⟨he₀, hw⟩, hold e₀ he₀ he⟩
    · refine Or.inr ?_
      have hi0 : i = P.length - 1 := by
        rcases Sym2.mem_iff.mp hce with h | h
        · exfalso
          rcases index_of_rho hext c₂ i (by omega) h.symm with ⟨h', -⟩ | ⟨h', -⟩
          · have : q'[i]'(by omega) = q'[q'.length - 1]'(by omega) := h.symm.trans hL.symm
            have := hnd.getElem_inj_iff.mp this
            omega
          · omega
        · rcases index_of_rho hext c₂ (i + 1) hi h.symm with ⟨h', -⟩ | ⟨h', -⟩
          · exfalso; omega
          · omega
      subst hi0
      rw [hnew _ hi (by omega) he]
      rfl
  · rintro (⟨e₀, he₀, ⟨-, hce⟩, rfl⟩ | hx)
    · exact ⟨Sym2.map rho e₀, old_mem_edgeSet hext he₀,
        ⟨old_mem_edgeSet hext he₀, Sym2.mem_map.mpr ⟨c₂, hce, rfl⟩⟩, (hold e₀ he₀ _).symm⟩
    · have hi : (P.length - 1) + 1 < q'.length := by omega
      refine ⟨s(q'[P.length - 1]'(by omega), q'[(P.length - 1) + 1]'hi),
        new_mem_edgeSet hext _ hi, ⟨new_mem_edgeSet hext _ hi, ?_⟩, ?_⟩
      · have hidx : (P.length - 1) + 1 = q'.length - 1 := by omega
        have hrc : q'[(P.length - 1) + 1]'hi = rho c₂ := by
          rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q' hidx hi
            (by omega)]
          exact hL
        rw [← hrc]
        simp
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, hnew (P.length - 1) hi (by omega) _]

end Workspace.ProofLemmas.RungReplacementLabels
