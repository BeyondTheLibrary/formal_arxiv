import Mathlib

set_option maxHeartbeats 800000

theorem ResidueMapSurjectiveOfInertiaDegOne {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] (h : Ideal.inertiaDeg p P = 1) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap R S)) := by
  letI hFp : Field (R ⧸ p) := Ideal.Quotient.field p
  letI hFP : Field (S ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Free (R ⧸ p) (S ⧸ P) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap p P]; exact h
  have hbij : Function.Bijective (algebraMap (R ⧸ p) (S ⧸ P)) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfr
  intro z
  obtain ⟨y, hy⟩ := hbij.2 z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r, ?_⟩
  rw [RingHom.comp_apply, ← Ideal.Quotient.algebraMap_mk_of_liesOver P p r, hy]
