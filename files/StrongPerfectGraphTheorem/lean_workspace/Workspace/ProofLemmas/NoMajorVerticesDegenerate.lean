import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.NoMajorVerticesGraphShape
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm83MixedRungs
import Workspace.ProofLemmas.Thm86ClaimTwo

/-!
# The degeneracy step in 8.6, claim (1)

This module isolates the line-graph counting sentence in the first claim of the proof of 8.6.
It is separate from the separator and component bookkeeping in the main proof.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoMajorVerticesDegenerate

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- PAPER (proof of 8.6, printed p. 45): *"Since `X ∩ V(L(H₀))` saturates `L(H₀)`, it
follows that for every vertex `w` of `J` different from `b₁,b₂`, `w` has at most one
neighbour in `J` different from `b₁,b₂`, and `w` is adjacent in `J` to both `b₁` and
`b₂`, and all `wb₁`- and `wb₂`-rungs have length zero. Since `J` is 3-connected it
follows that `J = K₄`, and `L(H₀)` is degenerate."* -/
theorem saturation_inside_two_ends_forces_degenerate
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N)
    (X : Set V) (hsat : SaturatesStripSystem J S N X)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (n : ℕ) (H₀ : SimpleGraph (Fin n)) (R : U → U → List V)
    (hforms : FormsLineGraph G J S N R H₀)
    (hinside :
      X ∩ (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) ⊆ N b₁ ∪ N b₂) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ DegenerateAppearance J H₀ := by
  classical
  have hbne : b₁ ≠ b₂ := hb₁b₂.ne
  let K : Set V := ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}
  have hbad : ∀ w p : U, w ≠ b₁ → w ≠ b₂ → p ≠ b₁ → p ≠ b₂ →
      J.Adj w p → ¬ stripSystemNuv S N w p ⊆ X := by
    intro w p hwb₁ hwb₂ hpb₁ hpb₂ hwp hgood
    obtain ⟨-, s, t, hpath, hRsub, hsN, htN⟩ := hforms.1 w p hwp
    have hsR : s ∈ R w p := List.mem_of_mem_head? hpath.2.1
    have hsNw : s ∈ N w := (hsN s hsR).mpr rfl
    have hsX : s ∈ X := hgood ⟨hsNw, hRsub s hsR⟩
    have hsK : s ∈ K := by
      simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨w, p, hwp, hsR⟩
    have hsEnds : s ∈ N b₁ ∪ N b₂ := hinside ⟨hsX, by simpa [K] using hsK⟩
    rcases hsEnds with hs₁ | hs₂
    · have : s ∈ S w p ∩ N b₁ := ⟨hRsub s hsR, hs₁⟩
      rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty
        hSN hwp (Ne.symm hwb₁) (Ne.symm hpb₁)] at this
      exact this
    · have : s ∈ S w p ∩ N b₂ := ⟨hRsub s hsR, hs₂⟩
      rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty
        hSN hwp (Ne.symm hwb₂) (Ne.symm hpb₂)] at this
      exact this
  have hout : ∀ w : U, w ≠ b₁ → w ≠ b₂ →
      {p : U | J.Adj w p ∧ p ≠ b₁ ∧ p ≠ b₂}.Subsingleton := by
    intro w hwb₁ hwb₂ p hp q hq
    exact hsat w ⟨hp.1, hbad w p hwb₁ hwb₂ hp.2.1 hp.2.2 hp.1⟩
      ⟨hq.1, hbad w q hwb₁ hwb₂ hq.2.1 hq.2.2 hq.1⟩
  have hends : ∀ w : U, w ≠ b₁ → w ≠ b₂ → J.Adj w b₁ ∧ J.Adj w b₂ := by
    intro w hwb₁ hwb₂
    have hdegw : 3 ≤ (J.neighborSet w).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ w
    obtain ⟨p, hwp, hpb₁, hpb₂⟩ :=
      Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdegw b₁ b₂
    have hpout : p ∈ {q : U | J.Adj w q ∧ q ≠ b₁ ∧ q ≠ b₂} :=
      ⟨hwp, hpb₁, hpb₂⟩
    have hwb₁adj : J.Adj w b₁ := by
      by_contra hnot
      have hsub : J.neighborSet w ⊆ ({b₂, p} : Set U) := by
        intro q hwq
        by_cases hqb₂ : q = b₂
        · exact Or.inl hqb₂
        have hqb₁ : q ≠ b₁ := by
          intro hqb₁
          exact hnot (hqb₁ ▸ hwq)
        have hqp := hout w hwb₁ hwb₂
          ⟨hwq, hqb₁, hqb₂⟩ hpout
        exact Or.inr hqp
      have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hpairs : ({b₂, p} : Set U).ncard ≤ 2 := by
        have := Set.ncard_insert_le b₂ ({p} : Set U)
        rw [Set.ncard_singleton] at this
        exact this
      omega
    have hwb₂adj : J.Adj w b₂ := by
      by_contra hnot
      have hsub : J.neighborSet w ⊆ ({b₁, p} : Set U) := by
        intro q hwq
        by_cases hqb₁ : q = b₁
        · exact Or.inl hqb₁
        have hqb₂ : q ≠ b₂ := by
          intro hqb₂
          exact hnot (hqb₂ ▸ hwq)
        have hqp := hout w hwb₁ hwb₂
          ⟨hwq, hqb₁, hqb₂⟩ hpout
        exact Or.inr hqp
      have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hpairs : ({b₁, p} : Set U).ncard ≤ 2 := by
        have := Set.ncard_insert_le b₁ ({p} : Set U)
        rw [Set.ncard_singleton] at this
        exact this
      omega
    exact ⟨hwb₁adj, hwb₂adj⟩
  have hzero₁ : ∀ w : U, w ≠ b₁ → w ≠ b₂ → pathLength (R w b₁) = 0 := by
    intro w hwb₁ hwb₂
    have hdegw : 3 ≤ (J.neighborSet w).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ w
    obtain ⟨p, hwp, hpb₁, hpb₂⟩ :=
      Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdegw b₁ b₂
    have hgood₁ : stripSystemNuv S N w b₁ ⊆ X := by
      by_contra hnot
      have heq := hsat w
        ⟨hwp, hbad w p hwb₁ hwb₂ hpb₁ hpb₂ hwp⟩
        ⟨(hends w hwb₁ hwb₂).1, hnot⟩
      exact hpb₁ heq
    obtain ⟨-, s, t, hpath, hRsub, hsN, htN⟩ :=
      hforms.1 w b₁ (hends w hwb₁ hwb₂).1
    have hsR : s ∈ R w b₁ := List.mem_of_mem_head? hpath.2.1
    have hsNw : s ∈ N w := (hsN s hsR).mpr rfl
    have hsX : s ∈ X := hgood₁ ⟨hsNw, hRsub s hsR⟩
    have hsK : s ∈ K := by
      simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨w, b₁, (hends w hwb₁ hwb₂).1, hsR⟩
    have hsNb₁ : s ∈ N b₁ := by
      rcases hinside ⟨hsX, by simpa [K] using hsK⟩ with hs₁ | hs₂
      · exact hs₁
      · have : s ∈ S w b₁ ∩ N b₂ := ⟨hRsub s hsR, hs₂⟩
        rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty hSN
          (hends w hwb₁ hwb₂).1 (Ne.symm hwb₂) hbne.symm] at this
        exact this.elim
    have hst : s = t := (htN s hsR).mp hsNb₁
    have hpos : 0 < (R w b₁).length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos hpath.1
    have hfirst := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hpath.2.1 hpos
    have hlast := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hpath.2.2 hpos
    have helem : (R w b₁)[0]'hpos = (R w b₁)[(R w b₁).length - 1]'(by omega) :=
      hfirst.trans (hst.trans hlast.symm)
    have hind : 0 = (R w b₁).length - 1 := hpath.1.2.1.getElem_inj_iff.mp helem
    simp only [pathLength]
    omega
  have hzero₂ : ∀ w : U, w ≠ b₁ → w ≠ b₂ → pathLength (R w b₂) = 0 := by
    intro w hwb₁ hwb₂
    have hdegw : 3 ≤ (J.neighborSet w).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ w
    obtain ⟨p, hwp, hpb₁, hpb₂⟩ :=
      Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdegw b₁ b₂
    have hgood₂ : stripSystemNuv S N w b₂ ⊆ X := by
      by_contra hnot
      have heq := hsat w
        ⟨hwp, hbad w p hwb₁ hwb₂ hpb₁ hpb₂ hwp⟩
        ⟨(hends w hwb₁ hwb₂).2, hnot⟩
      exact hpb₂ heq
    obtain ⟨-, s, t, hpath, hRsub, hsN, htN⟩ :=
      hforms.1 w b₂ (hends w hwb₁ hwb₂).2
    have hsR : s ∈ R w b₂ := List.mem_of_mem_head? hpath.2.1
    have hsNw : s ∈ N w := (hsN s hsR).mpr rfl
    have hsX : s ∈ X := hgood₂ ⟨hsNw, hRsub s hsR⟩
    have hsK : s ∈ K := by
      simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨w, b₂, (hends w hwb₁ hwb₂).2, hsR⟩
    have hsNb₂ : s ∈ N b₂ := by
      rcases hinside ⟨hsX, by simpa [K] using hsK⟩ with hs₁ | hs₂
      · have : s ∈ S w b₂ ∩ N b₁ := ⟨hRsub s hsR, hs₁⟩
        rw [Workspace.ProofLemmas.StripSystemBasics.strip_inter_N_eq_empty hSN
          (hends w hwb₁ hwb₂).2 (Ne.symm hwb₁) hbne] at this
        exact this.elim
      · exact hs₂
    have hst : s = t := (htN s hsR).mp hsNb₂
    have hpos : 0 < (R w b₂).length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos hpath.1
    have hfirst := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hpath.2.1 hpos
    have hlast := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hpath.2.2 hpos
    have helem : (R w b₂)[0]'hpos = (R w b₂)[(R w b₂).length - 1]'(by omega) :=
      hfirst.trans (hst.trans hlast.symm)
    have hind : 0 = (R w b₂).length - 1 := hpath.1.2.1.getElem_inj_iff.mp helem
    simp only [pathLength]
    omega
  have hK₄ := Workspace.ProofLemmas.NoMajorVerticesGraphShape.k4_of_two_hubs
    J hJ b₁ b₂ hb₁b₂ hends hout
  have hdeg₁ : 3 ≤ (J.neighborSet b₁).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ b₁
  obtain ⟨c, hcb₁, hcb₁ne, hcb₂ne⟩ :=
    Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdeg₁ b₁ b₂
  have hdegc : 3 ≤ (J.neighborSet c).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ c
  obtain ⟨d, hcd, hdb₁, hdb₂⟩ :=
    Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdegc b₁ b₂
  have hcdne : c ≠ d := hcd.ne
  obtain ⟨ι, B, hιinj, hrange, hbranch, hdict, -⟩ :=
    Workspace.ProofLemmas.Thm83MixedRungs.dict G J hJ S N hSN H₀ R hforms
  have hab : H₀.Adj (ι b₁) (ι c) :=
    (Workspace.ProofLemmas.Thm83MixedRungs.zero_rung_to_adj hbranch hdict hcb₁.symm
      (hzero₁ c hcb₁ne hcb₂ne)).symm
  have hbc : H₀.Adj (ι c) (ι b₂) :=
    Workspace.ProofLemmas.Thm83MixedRungs.zero_rung_to_adj hbranch hdict
      (hends c hcb₁ne hcb₂ne).2 (hzero₂ c hcb₁ne hcb₂ne)
  have hcdH : H₀.Adj (ι b₂) (ι d) :=
    (Workspace.ProofLemmas.Thm83MixedRungs.zero_rung_to_adj hbranch hdict
      (hends d hdb₁ hdb₂).2 (hzero₂ d hdb₁ hdb₂)).symm
  have hda : H₀.Adj (ι d) (ι b₁) :=
    Workspace.ProofLemmas.Thm83MixedRungs.zero_rung_to_adj hbranch hdict
      (hends d hdb₁ hdb₂).1 (hzero₁ d hdb₁ hdb₂)
  have hnodup : [ι b₁, ι c, ι b₂, ι d].Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, by simp⟩⟩⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact hcb₁ne (hιinj h.symm)
      · exact hbne (hιinj h)
      · exact hdb₁ (hιinj h.symm)
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact hcb₂ne (hιinj h)
      · exact hcdne (hιinj h)
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact hdb₂ (hιinj h.symm)
  have hcard4 : Fintype.card U = 4 := by
    obtain ⟨e⟩ := hK₄
    simpa using Fintype.card_congr e.toEquiv
  have hfourcard : ({b₁, c, b₂, d} : Set U).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hcb₁ne, hbne, Ne.symm hdb₁]),
      Set.ncard_insert_of_notMem (by simp [hcb₂ne, hcdne]),
      Set.ncard_insert_of_notMem (by simp [Ne.symm hdb₂]), Set.ncard_singleton]
  have hfour : ({b₁, c, b₂, d} : Set U) = Set.univ := by
    rw [Set.eq_univ_iff_ncard, Nat.card_eq_fintype_card, hcard4]
    exact hfourcard
  have hbr : branchVertices H₀ ⊆ ({ι b₁, ι c, ι b₂, ι d} : Set (Fin n)) := by
    intro z hz
    rw [← hrange] at hz
    obtain ⟨w, rfl⟩ := hz
    have hw : w ∈ ({b₁, c, b₂, d} : Set U) := by rw [hfour]; exact Set.mem_univ w
    rcases hw with hw | hw | hw | hw
    · exact Or.inl (congrArg ι hw)
    · exact Or.inr (Or.inl (congrArg ι hw))
    · exact Or.inr (Or.inr (Or.inl (congrArg ι hw)))
    · exact Or.inr (Or.inr (Or.inr (congrArg ι hw)))
  exact ⟨hK₄, Or.inl ⟨hK₄, ⟨ι b₁, ι c, ι b₂, ι d,
    hnodup, hab, hbc, hcdH, hda, hbr⟩⟩⟩

end Workspace.ProofLemmas.NoMajorVerticesDegenerate
