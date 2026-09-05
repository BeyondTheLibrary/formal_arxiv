import Workspace.ProofLemmas.OccurrenceIndexedCliqueReplicationPerfect
import Workspace.ProofLemmas.CliqueNumOfInducedSet

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- Every nonempty finite perfect graph has a clique meeting every maximum
independent set. -/
theorem PerfectGraphMaximumStableSetHittingClique
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph W) (hH : IsPerfect H) :
    ∃ C : Finset W,
      H.IsClique (↑C : Set W) ∧
        ∀ A : Finset W,
          H.IsIndepSet (↑A : Set W) →
            A.card = Hᶜ.cliqueNum →
              ∃ x : W, x ∈ C ∧ x ∈ A := by
  classical
  let alpha : ℕ := Hᶜ.cliqueNum
  let maxStables : Finset (Finset W) := H.indepSetFinset alpha
  have hmaxStables_nonempty : maxStables.Nonempty := by
    obtain ⟨A, hA⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := H)
    refine ⟨A, ?_⟩
    change A ∈ H.indepSetFinset alpha
    rw [SimpleGraph.mem_indepSetFinset_iff]
    refine ⟨hA.isIndepSet, ?_⟩
    simpa [alpha, SimpleGraph.cliqueNum_compl] using hA.card_eq
  let MaxStable := {A : Finset W // A ∈ maxStables}
  let k : ℕ := Fintype.card MaxStable
  have hk : 0 < k := by
    change 0 < Fintype.card MaxStable
    exact Fintype.card_pos_iff.mpr ⟨⟨hmaxStables_nonempty.choose,
      hmaxStables_nonempty.choose_spec⟩⟩
  let enum : Fin k ≃ MaxStable :=
    (Fintype.equivFinOfCardEq (by rfl : Fintype.card MaxStable = k)).symm
  let sets : Fin k → Set W := fun i => (enum i : Finset W)
  have hsets (i : Fin k) :
      H.IsIndepSet (sets i) ∧ (sets i).ncard = alpha := by
    have hi := (SimpleGraph.mem_indepSetFinset_iff).mp (enum i).property
    exact ⟨hi.1, by simpa [sets] using hi.2⟩
  let Omega := {p : Fin k × W // p.2 ∈ sets p.1}
  let proj : Omega → W := fun p => p.1.2
  let HOmega : SimpleGraph Omega :=
    { Adj := fun x y => x ≠ y ∧ (proj x = proj y ∨ H.Adj (proj x) (proj y))
      symm := by
        intro x y h
        exact ⟨h.1.symm, h.2.elim (fun hxy => Or.inl hxy.symm)
          (fun hxy => Or.inr hxy.symm)⟩
      loopless := by
        refine ⟨?_⟩
        intro x h
        exact h.1 rfl }
  have hHOmega : IsPerfect HOmega := by
    simpa [Omega, proj, HOmega] using
      (OccurrenceIndexedCliqueReplicationPerfect H k hk sets hH)
  let indexColor : HOmega.Coloring (Fin k) :=
    SimpleGraph.Coloring.mk (fun x : Omega => x.1.1) (by
      intro x y hxy hindex
      have hxi : proj x ∈ sets x.1.1 := by
        simpa [proj] using x.property
      have hyi : proj y ∈ sets x.1.1 := by
        simpa [proj, hindex] using y.property
      have hstable := (SimpleGraph.isIndepSet_iff H).mp (hsets x.1.1).1
      rcases hxy.2 with hproj | hadj
      · apply hxy.1
        apply Subtype.ext
        apply Prod.ext hindex
        exact hproj
      · exact (hstable hxi hyi (fun h => hxy.1 (Subtype.ext (Prod.ext hindex h)))) hadj)
  have hcolorable_k : HOmega.Colorable k := by
    simpa using indexColor.colorable
  have stable_card_le (S : Finset Omega)
      (hS : HOmega.IsIndepSet (↑S : Set Omega)) : S.card ≤ alpha := by
    have hinj : Set.InjOn proj (↑S : Set Omega) := by
      intro x hx y hy hproj
      by_contra hxy
      have hadj : HOmega.Adj x y := ⟨hxy, Or.inl hproj⟩
      exact ((SimpleGraph.isIndepSet_iff HOmega).mp hS hx hy hxy) hadj
    let P : Finset W := S.image proj
    have hPcard : P.card = S.card := by
      exact Finset.card_image_of_injOn hinj
    have hPstable : H.IsIndepSet (↑P : Set W) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro u hu v hv huv
      simp only [P, Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hv
      have hxy : x ≠ y := fun h => huv (congrArg proj h)
      intro hadj
      have hadjOmega : HOmega.Adj x y := ⟨hxy, Or.inr hadj⟩
      exact ((SimpleGraph.isIndepSet_iff HOmega).mp hS
        (by simpa using hx) (by simpa using hy) hxy) hadjOmega
    calc
      S.card = P.card := hPcard.symm
      _ ≤ H.indepNum := hPstable.card_le_indepNum
      _ = alpha := by simp [alpha, SimpleGraph.cliqueNum_compl]
  let omegaEquiv : Omega ≃ Sigma fun i : Fin k => {w : W // w ∈ sets i} :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; cases x; rfl }
  have hOmega_card : Fintype.card Omega = k * alpha := by
    rw [Fintype.card_congr omegaEquiv, Fintype.card_sigma]
    have hfiberCard : ∀ i : Fin k,
        Fintype.card {w : W // w ∈ sets i} = alpha := by
      intro i
      have hi := (SimpleGraph.mem_indepSetFinset_iff).mp (enum i).property
      simpa only [sets, Finset.mem_coe, Fintype.card_coe] using hi.2
    simp_rw [hfiberCard]
    simp
  let r : ℕ := HOmega.cliqueNum
  have hcolorable_r : HOmega.Colorable r :=
    CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect HOmega hHOmega
  obtain ⟨colorR⟩ := hcolorable_r
  have hcard_by_color :
      Fintype.card Omega =
        ∑ j : Fin r, (Finset.univ.filter fun x : Omega => colorR x = j).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset Omega)) (t := (Finset.univ : Finset (Fin r)))
      (f := fun x : Omega => colorR x) (by intro x hx; simp))
  have hfiber (j : Fin r) :
      (Finset.univ.filter fun x : Omega => colorR x = j).card ≤ alpha := by
    apply stable_card_le
    simpa [SimpleGraph.Coloring.colorClass] using colorR.isIndepSet_colorClass j
  have hmul_le : k * alpha ≤ r * alpha := by
    rw [← hOmega_card, hcard_by_color]
    calc
      (∑ j : Fin r, (Finset.univ.filter fun x : Omega => colorR x = j).card)
          ≤ ∑ _j : Fin r, alpha := Finset.sum_le_sum fun j _ => hfiber j
      _ = r * alpha := by simp
  have halpha : 0 < alpha := by
    let w : W := Classical.choice inferInstance
    have hs : H.IsIndepSet (↑({w} : Finset W) : Set W) := by
      rw [SimpleGraph.isIndepSet_iff]
      simp
    have hle : 1 ≤ H.indepNum := by
      simpa using hs.card_le_indepNum
    simpa [alpha, SimpleGraph.cliqueNum_compl] using hle
  have hk_le_r : k ≤ r := Nat.le_of_mul_le_mul_right hmul_le halpha
  obtain ⟨Q, hQ⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := HOmega)
  have hr_le_k : r ≤ k := by
    calc
      r = Q.card := by simpa [r] using hQ.2.symm
      _ ≤ k := by
        have hle : Q.card ≤ Fintype.card (Fin k) :=
          hQ.1.card_le_of_coloring indexColor
        simpa using hle
  have hrk : r = k := Nat.le_antisymm hr_le_k hk_le_r
  have hQcard : Q.card = k := by simpa [r, hrk] using hQ.2
  let C : Finset W := Q.image proj
  refine ⟨C, ?_, ?_⟩
  · rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    simp only [C, Finset.mem_coe, Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    have hxy : x ≠ y := fun h => huv (congrArg proj h)
    have hadjOmega := hQ.1 (by simpa using hx) (by simpa using hy) hxy
    exact hadjOmega.2.resolve_left huv
  · intro A hA hAcard
    have hAmem : A ∈ maxStables := by
      change A ∈ H.indepSetFinset alpha
      rw [SimpleGraph.mem_indepSetFinset_iff]
      exact ⟨hA, by simpa [alpha] using hAcard⟩
    let a : MaxStable := ⟨A, hAmem⟩
    obtain ⟨i, hi⟩ := enum.surjective a
    have hsurj : Set.SurjOn (fun x : Omega => x.1.1) (↑Q : Set Omega) Set.univ := by
      apply indexColor.surjOn_of_card_le_isClique hQ.1
      simpa using hQcard.symm.le
    obtain ⟨q, hqQ, hqi⟩ := hsurj (Set.mem_univ i)
    refine ⟨proj q, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, hqQ, rfl⟩
    · have hqset : proj q ∈ sets i := by
        simpa [proj, hqi] using q.property
      simpa [sets, hi, a] using hqset

end Workspace.ProofLemmas

