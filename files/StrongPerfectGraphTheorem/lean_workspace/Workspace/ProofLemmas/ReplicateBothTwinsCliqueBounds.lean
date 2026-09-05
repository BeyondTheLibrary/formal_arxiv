import Workspace.Types.Replication

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Replication.SPGT

/-- Clique-number bounds and maximum-clique twin containment for an induced
subgraph of a replicated graph containing both twins. -/
theorem ReplicateBothTwinsCliqueBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X : Set (V ⊕ Unit))
    (hv : Sum.inl v ∈ X) (hw : Sum.inr () ∈ X) :
    let A : Set V := {a : V | Sum.inl a ∈ X}
    let H0 : SimpleGraph A := G.induce A
    let H : SimpleGraph X := (replicateVertex G v).induce X
    H0.cliqueNum ≤ H.cliqueNum ∧
      H.cliqueNum ≤ H0.cliqueNum + 1 ∧
        (H.cliqueNum = H0.cliqueNum + 1 →
          ∀ Q : Finset X, H.IsClique (↑Q : Set X) →
            Q.card = H.cliqueNum →
              (⟨Sum.inl v, hv⟩ : X) ∈ Q ∧ (⟨Sum.inr (), hw⟩ : X) ∈ Q) := by
  classical
  let A : Set V := {a : V | Sum.inl a ∈ X}
  let H0 : SimpleGraph A := G.induce A
  let H : SimpleGraph X := (replicateVertex G v).induce X
  let f : X → A := fun x =>
    match h : x.1 with
    | Sum.inl a => ⟨a, by simpa [h] using x.2⟩
    | Sum.inr _ => ⟨v, hv⟩
  let old : A ↪ X :=
    ⟨fun a => ⟨Sum.inl a.1, a.2⟩, by
      intro a b hab
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hab))⟩
  let wX : X := ⟨Sum.inr (), hw⟩
  let vX : X := ⟨Sum.inl v, hv⟩
  change H0.cliqueNum ≤ H.cliqueNum ∧
    H.cliqueNum ≤ H0.cliqueNum + 1 ∧
      (H.cliqueNum = H0.cliqueNum + 1 →
        ∀ Q : Finset X, H.IsClique (↑Q : Set X) → Q.card = H.cliqueNum →
          vX ∈ Q ∧ wX ∈ Q)

  have image_clique (Q : Finset X) (hQ : H.IsClique (↑Q : Set X)) :
      H0.IsClique (↑(Q.image f) : Set A) := by
    rintro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hpq : p ≠ q := fun h => hxy (congrArg f h)
    have hadj := hQ (by simpa using hp) (by simpa using hq) hpq
    change (replicateVertex G v).Adj p.1 q.1 at hadj
    rcases p with ⟨p, hpX⟩
    rcases q with ⟨q, hqX⟩
    rcases p with a | u <;> rcases q with b | z
    · change G.Adj a b at hadj
      exact hadj
    · change a = v ∨ G.Adj a v at hadj
      change G.Adj a v
      rcases hadj with rfl | hav
      · exact (hxy rfl).elim
      · exact hav
    · change b = v ∨ G.Adj b v at hadj
      change G.Adj v b
      rcases hadj with rfl | hbv
      · exact (hxy rfl).elim
      · exact hbv.symm
    · exact hadj.elim

  have erase_inj (Q : Finset X) : Set.InjOn f (↑(Q.erase wX) : Set X) := by
    intro p hp q hq heq
    have hpne : p ≠ wX := Finset.ne_of_mem_erase hp
    have hqne : q ≠ wX := Finset.ne_of_mem_erase hq
    rcases p with ⟨p, hpX⟩
    rcases q with ⟨q, hqX⟩
    rcases p with a | u <;> rcases q with b | z
    · apply Subtype.ext
      have hab : (⟨a, hpX⟩ : A) = ⟨b, hqX⟩ := by simpa [f] using heq
      exact congrArg Sum.inl (congrArg Subtype.val hab)
    · exfalso
      apply hqne
      apply Subtype.ext
      cases z
      rfl
    · exfalso
      apply hpne
      apply Subtype.ext
      cases u
      rfl
    · apply Subtype.ext
      cases u
      cases z
      rfl

  have card_le_image_add_one (Q : Finset X) : Q.card ≤ (Q.image f).card + 1 := by
    have hi := Finset.card_image_of_injOn (erase_inj Q)
    have hsub : (Q.erase wX).image f ⊆ Q.image f :=
      Finset.image_mono f (Finset.erase_subset _ _)
    have hcard := Finset.card_le_card hsub
    by_cases hwQ : wX ∈ Q
    · have herase := Finset.card_erase_add_one hwQ
      omega
    · have heqcard : Q.card = (Q.image f).card := by
        simpa [Finset.erase_eq_of_notMem hwQ] using hi.symm
      omega

  have lower : H0.cliqueNum ≤ H.cliqueNum := by
    obtain ⟨K, hK⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := H0)
    let K' : Finset X := K.map old
    have hK' : H.IsClique (↑K' : Set X) := by
      rintro x hx y hy hxy
      simp only [K', Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      change G.Adj a.1 b.1
      exact hK.1 (by simpa using ha) (by simpa using hb) (fun hab => hxy (congrArg old hab))
    have hle := SimpleGraph.IsClique.card_le_cliqueNum (tc := hK')
    simpa [K', hK.2] using hle

  refine ⟨lower, ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := H)
    have himage := image_clique Q hQ.1
    have himage_le := SimpleGraph.IsClique.card_le_cliqueNum (tc := himage)
    have hcard := card_le_image_add_one Q
    have hQcard := hQ.2
    omega
  · intro hEq Q hQ hQcard
    have himage := image_clique Q hQ
    have himage_le := SimpleGraph.IsClique.card_le_cliqueNum (tc := himage)
    by_contra hboth
    rw [not_and_or] at hboth
    have hinj : Set.InjOn f (↑Q : Set X) := by
      intro p hp q hq heq
      rcases p with ⟨p, hpX⟩
      rcases q with ⟨q, hqX⟩
      rcases p with a | u <;> rcases q with b | z
      · apply Subtype.ext
        have hab : (⟨a, hpX⟩ : A) = ⟨b, hqX⟩ := by simpa [f] using heq
        exact congrArg Sum.inl (congrArg Subtype.val hab)
      · have hav : a = v := by
          have : (⟨a, hpX⟩ : A) = ⟨v, hv⟩ := by simpa [f] using heq
          exact congrArg Subtype.val this
        subst a
        exfalso
        rcases hboth with hvnot | hwnot
        · exact hvnot (by simpa [vX] using hp)
        · exact hwnot (by simpa [wX] using hq)
      · have hbv : b = v := by
          have : (⟨v, hv⟩ : A) = ⟨b, hqX⟩ := by simpa [f] using heq
          exact (congrArg Subtype.val this).symm
        subst b
        exfalso
        rcases hboth with hvnot | hwnot
        · exact hvnot (by simpa [vX] using hq)
        · exact hwnot (by simpa [wX] using hp)
      · apply Subtype.ext
        cases u
        cases z
        rfl
    have hcard_image := Finset.card_image_of_injOn hinj
    omega

end Workspace.ProofLemmas
