import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem UnramifiedProPTowerFields :
    ∀ (F : Type*) [Field F] [NumberField F]
      (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
      IsClosed (N : Set (galUr 3 F)) →
        letI := hNnorm
        Infinite (galUr 3 F ⧸ N) →
          TopFinitelyGenerated (galUr 3 F ⧸ N) →
            IsProP 3 (galUr 3 F ⧸ N) →
              ∀ (H : ℕ → Subgroup (galUr 3 F)),
                (∀ j, (H j).Normal) →
                  (∀ j, IsOpen ((H j : Set (galUr 3 F)))) →
                    (∀ j, N ≤ H j) →
                      H 0 = ⊤ →
                        StrictAnti H →
                          (∀ j, 0 < (H j).index) →
                            Filter.Tendsto (fun j => (H j).index)
                                Filter.atTop Filter.atTop →
                              ∃ Fj : ℕ → IntermediateField F (AlgebraicClosure F),
                                (∀ j, Fj j =
                                    IntermediateField.map
                                      (IntermediateField.val (maxUnramifiedProPExt 3 F))
                                      (fixedFieldOf 3 F (H j))) ∧
                                  Fj 0 = ⊥ ∧ StrictMono Fj ∧
                                    Filter.Tendsto (fun j => Module.finrank ℚ ↥(Fj j))
                                      Filter.atTop Filter.atTop := by
  intro F _ _ N hNnorm hNclosed hNinf hNtfg hNprop H hHnorm hHopen hHN hH0 hSA hHpos hHtend
  -- Unpack the correspondence axiom, part (a): degree formula, injectivity, inclusion-reversal.
  obtain ⟨hGal, hInj, hRev, _hChain⟩ := UnramifiedProPTowerCorrespondence F
  -- The ambient embedding `ι : F^{ur,3} ↪ AlgebraicClosure F`.
  set ι := IntermediateField.val (maxUnramifiedProPExt 3 F) with hι
  -- The tower of fields.
  refine ⟨fun j => IntermediateField.map ι (fixedFieldOf 3 F (H j)), fun j => rfl, ?_, ?_, ?_⟩
  · -- Base layer: Fj 0 = ⊥.
    show IntermediateField.map ι (fixedFieldOf 3 F (H 0)) = ⊥
    have hbot : fixedFieldOf 3 F (H 0) = ⊥ := by
      rw [← IntermediateField.finrank_eq_one_iff]
      rw [(hGal (H 0) (hHnorm 0) (hHopen 0)).2.2.1, hH0, Subgroup.index_top]
    rw [hbot, IntermediateField.map_bot]
  · -- Strict monotonicity.
    refine strictMono_nat_of_lt_succ (fun j => ?_)
    have hlt : H (j + 1) < H j := hSA (Nat.lt_succ_self j)
    have hfle : fixedFieldOf 3 F (H j) ≤ fixedFieldOf 3 F (H (j + 1)) :=
      hRev (H (j + 1)) (H j) (hHnorm _) (hHopen _) (hHnorm _) (hHopen _) hlt.le
    have hfne : fixedFieldOf 3 F (H j) ≠ fixedFieldOf 3 F (H (j + 1)) := by
      intro heq
      exact hlt.ne' (hInj (H j) (H (j + 1)) (hHnorm _) (hHopen _) (hHnorm _) (hHopen _) heq)
    have hflt : fixedFieldOf 3 F (H j) < fixedFieldOf 3 F (H (j + 1)) :=
      lt_of_le_of_ne hfle hfne
    show IntermediateField.map ι (fixedFieldOf 3 F (H j)) <
        IntermediateField.map ι (fixedFieldOf 3 F (H (j + 1)))
    refine lt_of_le_of_ne (IntermediateField.map_mono ι hflt.le) ?_
    intro heq
    exact hfne (IntermediateField.map_injective ι heq)
  · -- Degrees diverge.
    have hdeg : ∀ j, Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
        = Module.finrank ℚ F * (H j).index := by
      intro j
      haveI hfd : FiniteDimensional F ↥(fixedFieldOf 3 F (H j)) :=
        (hGal (H j) (hHnorm j) (hHopen j)).2.1
      have hidx : Module.finrank F ↥(fixedFieldOf 3 F (H j)) = (H j).index :=
        (hGal (H j) (hHnorm j) (hHopen j)).2.2.1
      have hmapeq : Module.finrank F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
          = Module.finrank F ↥(fixedFieldOf 3 F (H j)) :=
        ((fixedFieldOf 3 F (H j)).equivMap ι).toLinearEquiv.finrank_eq.symm
      haveI : FiniteDimensional F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))) :=
        ((fixedFieldOf 3 F (H j)).equivMap ι).toLinearEquiv.finiteDimensional
      have htower : Module.finrank ℚ F
          * Module.finrank F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
          = Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))) :=
        Module.finrank_mul_finrank ℚ F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
      rw [← htower, hmapeq, hidx]
    have hkey : (fun j => Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))))
        = (fun j => Module.finrank ℚ F * (H j).index) := funext hdeg
    rw [hkey]
    have hc : 0 < Module.finrank ℚ F := Module.finrank_pos
    exact Filter.tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left _ hc) hHtend
