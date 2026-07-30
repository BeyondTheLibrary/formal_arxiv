import Mathlib

set_option maxHeartbeats 800000

/-- **Multiplicity is transported by a ring automorphism (property-5 core for `ConjugatePairIndexing`).** -/
theorem MultiplicityTransportConjAut {A : Type*} [CommRing A] {F : Type*}
    [EquivLike F A A] [RingEquivClass F A A] (e : F) (p I : Ideal A) :
    multiplicity (Ideal.map e p) (Ideal.map e I) = multiplicity p I := by
  let g : Ideal A ≃* Ideal A :=
    { toFun := Ideal.map e
      invFun := Ideal.comap e
      left_inv := fun J => Ideal.comap_map_of_bijective e (EquivLike.bijective e)
      right_inv := fun J => Ideal.map_comap_of_surjective e (EquivLike.surjective e) J
      map_mul' := fun J K => Ideal.map_mul e J K }
  exact multiplicity_map_eq g (a := p) (b := I)
