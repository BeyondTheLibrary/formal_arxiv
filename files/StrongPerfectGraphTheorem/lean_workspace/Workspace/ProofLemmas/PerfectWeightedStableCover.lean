import Workspace.ProofLemmas.OccurrenceIndexedCliqueReplicationPerfect

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A perfect finite graph admits an exact weighted stable-set cover whose
number of labels is the largest total demand carried by a clique. -/
theorem PerfectWeightedStableCover
    {W : Type*} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) (w : W → ℕ) (hL : SPGT.IsPerfect L) :
    let cliqueWeights : Finset ℕ :=
      (@Finset.filter (Finset W)
        (fun Q ↦ L.IsClique (Q : Set W))
        (fun _ ↦ Classical.propDecidable _)
        Finset.univ.powerset).image (fun Q ↦ ∑ z ∈ Q, w z)
    let hnonempty : cliqueWeights.Nonempty := by
      refine ⟨0, ?_⟩
      simp only [cliqueWeights, Finset.mem_image]
      refine ⟨∅, ?_, by simp⟩
      simp
    let omega_w : ℕ := cliqueWeights.max' hnonempty
    ∃ S : Fin omega_w → Set W,
      (∀ i, Set.Pairwise (S i) (fun x y ↦ ¬ L.Adj x y)) ∧
      ∀ z, {i | z ∈ S i}.ncard = w z := by
  classical
  let cliqueWeights : Finset ℕ :=
    (@Finset.filter (Finset W)
      (fun Q ↦ L.IsClique (Q : Set W))
      (fun _ ↦ Classical.propDecidable _)
      Finset.univ.powerset).image (fun Q ↦ ∑ z ∈ Q, w z)
  let hnonempty : cliqueWeights.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [cliqueWeights, Finset.mem_image]
    refine ⟨∅, ?_, by simp⟩
    simp
  let omega_w : ℕ := cliqueWeights.max' hnonempty
  change ∃ S : Fin omega_w → Set W,
    (∀ i, Set.Pairwise (S i) (fun x y ↦ ¬ L.Adj x y)) ∧
    ∀ z, {i | z ∈ S i}.ncard = w z
  have hweight_le (z : W) : w z ≤ omega_w := by
    apply Finset.le_max' cliqueWeights (w z)
    refine Finset.mem_image.mpr ⟨{z}, ?_, by simp⟩
    simp
  by_cases homega : omega_w = 0
  · let S : Fin omega_w → Set W := fun _ ↦ ∅
    refine ⟨S, ?_, ?_⟩
    · intro i
      simp [S]
    · intro z
      have hwz : w z = 0 :=
        Nat.eq_zero_of_le_zero (homega ▸ hweight_le z)
      simp [S, hwz]
  · have homega_pos : 0 < omega_w := Nat.pos_of_ne_zero homega
    let A : Fin omega_w → Set W := fun i ↦ {z | i.val < w z}
    let Omega := {p : Fin omega_w × W // p.2 ∈ A p.1}
    let proj : Omega → W := fun p ↦ p.1.2
    let LOmega : SimpleGraph Omega :=
      { Adj := fun x y ↦ x ≠ y ∧
          (proj x = proj y ∨ L.Adj (proj x) (proj y))
        symm := by
          intro x y h
          exact ⟨h.1.symm, h.2.elim (fun hxy ↦ Or.inl hxy.symm)
            (fun hxy ↦ Or.inr hxy.symm)⟩
        loopless := by
          refine ⟨?_⟩
          intro x h
          exact h.1 rfl }
    have hLOmega : SPGT.IsPerfect LOmega := by
      simpa [A, Omega, proj, LOmega] using
        (OccurrenceIndexedCliqueReplicationPerfect L omega_w homega_pos A hL)
    obtain ⟨R, hR⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := LOmega)
    let Q : Finset W := R.image proj
    have hQclique : L.IsClique (Q : Set W) := by
      rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      simp only [Q, Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun e ↦ hxy (congrArg proj e)
      exact (hR.1 (by simpa using ha) (by simpa using hb) hab).2.resolve_left hxy
    have hRcard_le_weight : R.card ≤ ∑ z ∈ Q, w z := by
      let Source := {x : Omega // x ∈ R}
      let Target := Sigma fun z : {z : W // z ∈ Q} ↦ Fin (w z)
      let f : Source → Target := fun x ↦
        ⟨⟨proj x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩,
          ⟨x.1.1.1.val, by simpa [A, proj] using x.1.2⟩⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext (congrArg (fun q : Target ↦ q.2.val) hxy)
        · exact congrArg (fun q : Target ↦ q.1.1) hxy
      calc
        R.card = Fintype.card Source := by simp [Source]
        _ ≤ Fintype.card Target := Fintype.card_le_of_injective f hf
        _ = ∑ z ∈ Q, w z := by
          simpa [Target] using (Finset.sum_attach Q (fun z ↦ w z))
    have hQweight_mem : (∑ z ∈ Q, w z) ∈ cliqueWeights := by
      refine Finset.mem_image.mpr ⟨Q, ?_, rfl⟩
      simpa [cliqueWeights] using hQclique
    have hcliqueNum_le : LOmega.cliqueNum ≤ omega_w := by
      rw [← hR.2]
      exact hRcard_le_weight.trans
        (Finset.le_max' cliqueWeights (∑ z ∈ Q, w z) hQweight_mem)
    have hcolorable_cliqueNum : LOmega.Colorable LOmega.cliqueNum := by
      have heq := hLOmega Set.univ
      rw [IsoTransport.chromaticNumber_iso (SimpleGraph.induceUnivIso LOmega),
        IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso LOmega)] at heq
      rw [← SimpleGraph.chromaticNumber_le_iff_colorable, heq]
    obtain ⟨color⟩ := SimpleGraph.Colorable.mono hcliqueNum_le hcolorable_cliqueNum
    let S : Fin omega_w → Set W := fun c ↦
      {z | ∃ x : Omega, proj x = z ∧ color x = c}
    refine ⟨S, ?_, ?_⟩
    · intro c x hx y hy hxy
      rintro hxyAdj
      obtain ⟨a, ha, hac⟩ := hx
      obtain ⟨b, hb, hbc⟩ := hy
      have hab : a ≠ b := by
        intro e
        exact hxy (ha ▸ hb ▸ congrArg proj e)
      have hadj : L.Adj (proj a) (proj b) := by
        simpa only [ha, hb] using hxyAdj
      exact color.valid ⟨hab, Or.inr hadj⟩ (hac.trans hbc.symm)
    · intro z
      let Iz := {i : Fin omega_w // i.val < w z}
      let occ : Iz → Omega := fun i ↦ ⟨(i.1, z), by simpa [A] using i.2⟩
      let f : Iz → Fin omega_w := fun i ↦ color (occ i)
      have hf : Function.Injective f := by
        intro i j hij
        have hocc : occ i = occ j := by
          by_contra hne
          exact color.valid ⟨hne, Or.inl rfl⟩ hij
        apply Subtype.ext
        exact Fin.ext (congrArg (fun x : Omega ↦ x.1.1.val) hocc)
      have hrange : Set.range f = {c | z ∈ S c} := by
        ext c
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨occ i, rfl, rfl⟩
        · rintro ⟨x, hxz, hxc⟩
          let i : Iz := ⟨x.1.1, by simpa [Iz, A, proj, hxz] using x.2⟩
          have hoccix : occ i = x := by
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · exact hxz.symm
          refine ⟨i, ?_⟩
          change color (occ i) = c
          rw [hoccix]
          exact hxc
      rw [← hrange, Set.ncard_range_of_injective hf]
      let e : Iz ≃ Fin (w z) :=
        { toFun := fun i ↦ ⟨i.val, i.2⟩
          invFun := fun i ↦
            ⟨⟨i.val, i.isLt.trans_le (hweight_le z)⟩, i.isLt⟩
          left_inv := by
            intro i
            apply Subtype.ext
            apply Fin.ext
            rfl
          right_inv := by
            intro i
            apply Fin.ext
            rfl }
      simpa using Nat.card_congr e

end Workspace.ProofLemmas

